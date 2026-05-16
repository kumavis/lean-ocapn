/* OcapnLean — WebSocket FFI shim.
 *
 * Pairs `libwslay` (RFC 6455 frame state machine, masking, fragment
 * reassembly) with a small in-house HTTP/1.1 upgrade-handshake and
 * a blocking POSIX socket driver. Lean sees a tiny synchronous
 * surface — open client / accept server / send-one-message /
 * recv-one-message / close — never the wslay callback model.
 *
 * Why this shape:
 *   - wslay deliberately doesn't ship the HTTP upgrade. We bring our
 *     own (SHA-1 + base64 + `Sec-WebSocket-Accept` mechanics).
 *   - wslay's `wslay_event_*` API is callback-driven. We adapt it
 *     to a blocking synchronous model by pumping `wslay_event_recv`
 *     in a small loop until our `on_msg_recv_callback` records a
 *     completed message, and `wslay_event_send` after every queue
 *     of an outbound message.
 *   - Sockets are plain POSIX (not libuv). WS connections are
 *     point-to-point and we already use blocking I/O elsewhere; no
 *     need to involve the libuv event loop.
 */

/* POSIX feature-test macros must come before any system header,
 * so that getaddrinfo/freeaddrinfo/gai_strerror, strerror, strncasecmp,
 * etc. are all visible. */
#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L
#endif
#ifndef _DEFAULT_SOURCE
#define _DEFAULT_SOURCE 1
#endif

#include <lean/lean.h>
#include <wslay/wslay.h>

#include <arpa/inet.h>
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <netdb.h>
#include <netinet/in.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <unistd.h>

/* ----------------------------- error helpers ---------------------------- */

static lean_obj_res mk_user_error_str(const char *prefix, const char *detail) {
  char buf[512];
  snprintf(buf, sizeof(buf), "%s: %s", prefix, detail);
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

static lean_obj_res mk_user_errno(const char *prefix) {
  return mk_user_error_str(prefix, strerror(errno));
}

/* ------------------------------- SHA-1 ---------------------------------- *
 * Public-domain implementation by Steve Reid; trimmed to what we need.    *
 * Used only for the WebSocket handshake `Sec-WebSocket-Accept` header.    *
 * Not a cryptographic boundary — pure anti-confusion check per RFC 6455.  */

typedef struct {
  uint32_t state[5];
  uint32_t count[2];
  uint8_t  buffer[64];
} sha1_ctx;

#define rol(v, n) (((v) << (n)) | ((v) >> (32 - (n))))

static void sha1_transform(uint32_t state[5], const uint8_t buf[64]) {
  uint32_t a, b, c, d, e, w[80];
  for (int i = 0; i < 16; i++) {
    w[i] = ((uint32_t)buf[i * 4 + 0] << 24) | ((uint32_t)buf[i * 4 + 1] << 16)
         | ((uint32_t)buf[i * 4 + 2] << 8 ) | ((uint32_t)buf[i * 4 + 3]);
  }
  for (int i = 16; i < 80; i++) w[i] = rol(w[i-3] ^ w[i-8] ^ w[i-14] ^ w[i-16], 1);
  a = state[0]; b = state[1]; c = state[2]; d = state[3]; e = state[4];
  for (int i = 0; i < 80; i++) {
    uint32_t f, k;
    if (i < 20)      { f = (b & c) | ((~b) & d);             k = 0x5A827999; }
    else if (i < 40) { f = b ^ c ^ d;                        k = 0x6ED9EBA1; }
    else if (i < 60) { f = (b & c) | (b & d) | (c & d);      k = 0x8F1BBCDC; }
    else             { f = b ^ c ^ d;                        k = 0xCA62C1D6; }
    uint32_t t = rol(a, 5) + f + e + k + w[i];
    e = d; d = c; c = rol(b, 30); b = a; a = t;
  }
  state[0] += a; state[1] += b; state[2] += c; state[3] += d; state[4] += e;
}

static void sha1_init(sha1_ctx *c) {
  c->state[0] = 0x67452301; c->state[1] = 0xEFCDAB89; c->state[2] = 0x98BADCFE;
  c->state[3] = 0x10325476; c->state[4] = 0xC3D2E1F0;
  c->count[0] = c->count[1] = 0;
}

static void sha1_update(sha1_ctx *c, const uint8_t *data, size_t len) {
  uint32_t j = (c->count[0] >> 3) & 63;
  if ((c->count[0] += (uint32_t)len << 3) < ((uint32_t)len << 3)) c->count[1]++;
  c->count[1] += (uint32_t)(len >> 29);
  size_t i;
  if (j + len > 63) {
    i = 64 - j;
    memcpy(&c->buffer[j], data, i);
    sha1_transform(c->state, c->buffer);
    for (; i + 63 < len; i += 64) sha1_transform(c->state, &data[i]);
    j = 0;
  } else i = 0;
  memcpy(&c->buffer[j], &data[i], len - i);
}

static void sha1_final(sha1_ctx *c, uint8_t digest[20]) {
  uint8_t finalcount[8];
  for (int i = 0; i < 8; i++)
    finalcount[i] = (uint8_t)((c->count[(i < 4 ? 1 : 0)] >> ((3 - (i & 3)) * 8)) & 0xff);
  uint8_t pad = 0x80;
  sha1_update(c, &pad, 1);
  uint8_t zero = 0;
  while ((c->count[0] & 504) != 448) sha1_update(c, &zero, 1);
  sha1_update(c, finalcount, 8);
  for (int i = 0; i < 20; i++)
    digest[i] = (uint8_t)((c->state[i >> 2] >> ((3 - (i & 3)) * 8)) & 0xff);
}

static void sha1(const uint8_t *data, size_t len, uint8_t out[20]) {
  sha1_ctx c;
  sha1_init(&c);
  sha1_update(&c, data, len);
  sha1_final(&c, out);
}

/* ----------------------------- base64 ----------------------------------- */

static const char B64_ALPHA[] =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/* Encode `in_len` bytes into the caller's `out` buffer. Caller ensures
 * `out` has at least `4*((in_len+2)/3) + 1` bytes including '\0'. */
static void base64_encode(const uint8_t *in, size_t in_len, char *out) {
  size_t i = 0, o = 0;
  while (i + 3 <= in_len) {
    uint32_t v = ((uint32_t)in[i] << 16) | ((uint32_t)in[i+1] << 8) | in[i+2];
    out[o++] = B64_ALPHA[(v >> 18) & 0x3f];
    out[o++] = B64_ALPHA[(v >> 12) & 0x3f];
    out[o++] = B64_ALPHA[(v >>  6) & 0x3f];
    out[o++] = B64_ALPHA[ v        & 0x3f];
    i += 3;
  }
  if (i < in_len) {
    uint32_t v = (uint32_t)in[i] << 16;
    if (i + 1 < in_len) v |= (uint32_t)in[i+1] << 8;
    out[o++] = B64_ALPHA[(v >> 18) & 0x3f];
    out[o++] = B64_ALPHA[(v >> 12) & 0x3f];
    out[o++] = (i + 1 < in_len) ? B64_ALPHA[(v >> 6) & 0x3f] : '=';
    out[o++] = '=';
  }
  out[o] = '\0';
}

/* ------------------------ WebSocket key plumbing ------------------------ */

#define WS_GUID "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

static void compute_accept(const char *client_key, char accept_out[32]) {
  /* Concatenate client_key with the magic GUID, SHA-1, base64-encode. */
  char concat[256];
  size_t kl = strlen(client_key);
  size_t gl = strlen(WS_GUID);
  if (kl + gl >= sizeof(concat)) { accept_out[0] = '\0'; return; }
  memcpy(concat, client_key, kl);
  memcpy(concat + kl, WS_GUID, gl);
  uint8_t digest[20];
  sha1((const uint8_t *)concat, kl + gl, digest);
  base64_encode(digest, 20, accept_out);
}

/* Generate a random 16-byte client key and base64-encode it (no '\0'
 * trailing in the output; produces exactly 24 base64 chars + '\0'). */
static void generate_client_key(char key_out[28]) {
  uint8_t raw[16];
  /* /dev/urandom is plenty for an anti-confusion handshake nonce. */
  int fd = open("/dev/urandom", O_RDONLY);
  if (fd < 0) {
    /* Worst case: fall back to time-based pseudo-random. The
     * handshake is not a security boundary so collisions just mean
     * cosmetic ugliness; in practice /dev/urandom always succeeds. */
    for (int i = 0; i < 16; i++) raw[i] = (uint8_t)(rand() & 0xff);
  } else {
    ssize_t n = read(fd, raw, 16);
    close(fd);
    if (n != 16) for (int i = 0; i < 16; i++) raw[i] = (uint8_t)(rand() & 0xff);
  }
  base64_encode(raw, 16, key_out);
}

/* ----------------------- HTTP handshake (blocking) ---------------------- */

/* Read until '\r\n\r\n' or EOF; returns -1 on error. Caps at `cap`. */
static ssize_t read_http_headers(int fd, char *buf, size_t cap) {
  size_t total = 0;
  while (total + 1 < cap) {
    ssize_t n = read(fd, buf + total, 1);
    if (n < 0) {
      if (errno == EINTR) continue;
      return -1;
    }
    if (n == 0) return -1;  /* EOF mid-headers */
    total += (size_t)n;
    if (total >= 4 && memcmp(buf + total - 4, "\r\n\r\n", 4) == 0) {
      buf[total] = '\0';
      return (ssize_t)total;
    }
  }
  return -1;  /* headers too big */
}

/* Write all `len` bytes. Returns 0 on success, -1 on error. */
static int write_all(int fd, const char *buf, size_t len) {
  size_t sent = 0;
  while (sent < len) {
    ssize_t n = write(fd, buf + sent, len - sent);
    if (n < 0) {
      if (errno == EINTR) continue;
      return -1;
    }
    sent += (size_t)n;
  }
  return 0;
}

/* Case-insensitive header value lookup. Writes value into `out` (up to
 * `out_len`); returns 1 on found, 0 on missing. */
static int header_get(const char *headers, const char *name,
                      char *out, size_t out_len) {
  size_t name_len = strlen(name);
  const char *p = headers;
  while ((p = strchr(p, '\n'))) {
    p++;
    if (strncasecmp(p, name, name_len) == 0 && p[name_len] == ':') {
      p += name_len + 1;
      while (*p == ' ' || *p == '\t') p++;
      const char *end = strstr(p, "\r\n");
      if (!end) return 0;
      size_t l = (size_t)(end - p);
      if (l >= out_len) l = out_len - 1;
      memcpy(out, p, l);
      out[l] = '\0';
      return 1;
    }
  }
  return 0;
}

/* Client-side handshake. Returns 0 on success. */
static int ws_client_handshake(int fd, const char *host, uint16_t port,
                               const char *path) {
  char key[28];
  generate_client_key(key);

  char req[1024];
  int n = snprintf(req, sizeof(req),
                   "GET %s HTTP/1.1\r\n"
                   "Host: %s:%u\r\n"
                   "Upgrade: websocket\r\n"
                   "Connection: Upgrade\r\n"
                   "Sec-WebSocket-Key: %s\r\n"
                   "Sec-WebSocket-Version: 13\r\n"
                   "\r\n",
                   path, host, (unsigned)port, key);
  if (n <= 0 || (size_t)n >= sizeof(req)) return -1;
  if (write_all(fd, req, (size_t)n) < 0) return -1;

  char resp[2048];
  if (read_http_headers(fd, resp, sizeof(resp)) < 0) return -1;

  /* Expect "HTTP/1.1 101 ..." */
  if (strncmp(resp, "HTTP/1.1 101", 12) != 0 &&
      strncmp(resp, "HTTP/1.0 101", 12) != 0) return -2;

  char accept_actual[256];
  if (!header_get(resp, "Sec-WebSocket-Accept", accept_actual, sizeof(accept_actual)))
    return -3;
  char accept_expected[32];
  compute_accept(key, accept_expected);
  if (strcmp(accept_actual, accept_expected) != 0) return -4;
  return 0;
}

/* Server-side handshake. Returns 0 on success. */
static int ws_server_handshake(int fd) {
  char req[2048];
  if (read_http_headers(fd, req, sizeof(req)) < 0) return -1;
  if (strncmp(req, "GET ", 4) != 0) return -2;
  char key[256];
  if (!header_get(req, "Sec-WebSocket-Key", key, sizeof(key))) return -3;
  char accept_str[32];
  compute_accept(key, accept_str);
  char resp[512];
  int n = snprintf(resp, sizeof(resp),
                   "HTTP/1.1 101 Switching Protocols\r\n"
                   "Upgrade: websocket\r\n"
                   "Connection: Upgrade\r\n"
                   "Sec-WebSocket-Accept: %s\r\n"
                   "\r\n",
                   accept_str);
  if (n <= 0 || (size_t)n >= sizeof(resp)) return -4;
  if (write_all(fd, resp, (size_t)n) < 0) return -5;
  return 0;
}

/* ---------------------------- wslay glue -------------------------------- */

struct ws_conn {
  int                          fd;
  wslay_event_context_ptr      ctx;
  bool                         is_client;
  /* Single-shot message hand-off from wslay's recv-callback to our
   * blocking recv loop. */
  bool                         msg_ready;
  uint8_t                      msg_opcode;
  uint8_t                     *msg_payload;
  size_t                       msg_len;
  bool                         msg_alloc_error;
  bool                         eof_seen;
};

static ssize_t ws_recv_cb(wslay_event_context_ptr ctx, uint8_t *buf, size_t len,
                          int flags, void *user_data) {
  (void)flags;
  struct ws_conn *c = (struct ws_conn *)user_data;
  /* wslay_event_recv's internal loop keeps processing until it gets
   * WANT_READ or an error. If a complete message has already arrived
   * during this call (msg_ready set), we want to *stop* — otherwise
   * a blocking recv() on a quiet socket would hang forever. Returning
   * WSLAY_ERR_WANT_READ here breaks wslay's loop cleanly without
   * setting the error flag, so our outer loop can deliver the
   * pending message. */
  if (c->msg_ready) {
    wslay_event_set_error(ctx, WSLAY_ERR_WOULDBLOCK);
    return -1;
  }
  while (true) {
    ssize_t n = recv(c->fd, buf, len, 0);
    if (n < 0) {
      if (errno == EINTR) continue;
      wslay_event_set_error(ctx, WSLAY_ERR_CALLBACK_FAILURE);
      return -1;
    }
    if (n == 0) {
      c->eof_seen = true;
      wslay_event_set_error(ctx, WSLAY_ERR_CALLBACK_FAILURE);
      return -1;
    }
    return n;
  }
}

static ssize_t ws_send_cb(wslay_event_context_ptr ctx, const uint8_t *buf,
                          size_t len, int flags, void *user_data) {
  (void)flags;
  struct ws_conn *c = (struct ws_conn *)user_data;
  while (true) {
    ssize_t n = send(c->fd, buf, len, 0);
    if (n < 0) {
      if (errno == EINTR) continue;
      wslay_event_set_error(ctx, WSLAY_ERR_CALLBACK_FAILURE);
      return -1;
    }
    return n;
  }
}

static int ws_genmask_cb(wslay_event_context_ptr ctx, uint8_t *buf, size_t len,
                         void *user_data) {
  (void)ctx;
  (void)user_data;
  int fd = open("/dev/urandom", O_RDONLY);
  if (fd >= 0) {
    ssize_t n = read(fd, buf, len);
    close(fd);
    if (n == (ssize_t)len) return 0;
  }
  /* Fallback — not a security boundary, masking is anti-confusion only. */
  for (size_t i = 0; i < len; i++) buf[i] = (uint8_t)(rand() & 0xff);
  return 0;
}

static void ws_on_msg_recv(wslay_event_context_ptr ctx,
                           const struct wslay_event_on_msg_recv_arg *arg,
                           void *user_data) {
  (void)ctx;
  struct ws_conn *c = (struct ws_conn *)user_data;
  /* Ignore control opcodes (close handled below). */
  if (arg->opcode == WSLAY_CONNECTION_CLOSE) {
    c->eof_seen = true;
    return;
  }
  if (arg->opcode == WSLAY_PING || arg->opcode == WSLAY_PONG) {
    /* wslay auto-replies to pings; nothing to do here. */
    return;
  }
  uint8_t *copy = (uint8_t *)malloc(arg->msg_length);
  if (!copy) { c->msg_alloc_error = true; return; }
  memcpy(copy, arg->msg, arg->msg_length);
  /* If multiple messages arrive in a single recv pump, replace the
   * pending one. In practice OCapN messages alternate with our own
   * sends, so this is fine; if the peer pipelines more than one
   * frame before we recv, we'd lose the earlier one. We accept that
   * for now — Lean callers `recvMessage?` once between sends. */
  free(c->msg_payload);
  c->msg_payload = copy;
  c->msg_len     = arg->msg_length;
  c->msg_opcode  = arg->opcode;
  c->msg_ready   = true;
}

static int init_wslay(struct ws_conn *c) {
  struct wslay_event_callbacks cbs = {
    .recv_callback           = ws_recv_cb,
    .send_callback           = ws_send_cb,
    .genmask_callback        = ws_genmask_cb,
    .on_frame_recv_start_callback = NULL,
    .on_frame_recv_chunk_callback = NULL,
    .on_frame_recv_end_callback   = NULL,
    .on_msg_recv_callback         = ws_on_msg_recv,
  };
  int r = c->is_client
        ? wslay_event_context_client_init(&c->ctx, &cbs, c)
        : wslay_event_context_server_init(&c->ctx, &cbs, c);
  return r;
}

static struct ws_conn *new_conn(int fd, bool is_client) {
  struct ws_conn *c = (struct ws_conn *)calloc(1, sizeof(*c));
  if (!c) return NULL;
  c->fd = fd;
  c->is_client = is_client;
  if (init_wslay(c) != 0) { free(c); return NULL; }
  return c;
}

static void free_conn(struct ws_conn *c) {
  if (!c) return;
  if (c->ctx) wslay_event_context_free(c->ctx);
  if (c->fd >= 0) close(c->fd);
  free(c->msg_payload);
  free(c);
}

/* ---------------- Lean external-object class for ws_conn ---------------- */

static lean_external_class *ws_conn_class = NULL;

static void ws_conn_finalize(void *p) { free_conn((struct ws_conn *)p); }
static void ws_conn_foreach(void *p, b_lean_obj_arg fn) {
  (void)p; (void)fn;
}

static lean_external_class *get_ws_conn_class(void) {
  if (!ws_conn_class) {
    ws_conn_class = lean_register_external_class(ws_conn_finalize, ws_conn_foreach);
  }
  return ws_conn_class;
}

static lean_obj_res wrap_conn(struct ws_conn *c) {
  return lean_alloc_external(get_ws_conn_class(), c);
}

static struct ws_conn *unwrap_conn(b_lean_obj_arg handle) {
  return (struct ws_conn *)lean_get_external_data(handle);
}

/* ----------------------- public Lean entry points ----------------------- */

/* `wsClientConnect (host : @& String) (port : UInt16) (path : @& String)
 *   : IO Conn` */
LEAN_EXPORT lean_obj_res
ocapnlean_ws_client_connect(b_lean_obj_arg host_obj, uint16_t port,
                            b_lean_obj_arg path_obj, lean_obj_arg /*io*/) {
  const char *host = lean_string_cstr(host_obj);
  const char *path = lean_string_cstr(path_obj);

  struct addrinfo hints = {0}, *res = NULL;
  hints.ai_family = AF_INET;
  hints.ai_socktype = SOCK_STREAM;
  char port_str[8];
  snprintf(port_str, sizeof(port_str), "%u", (unsigned)port);
  int err = getaddrinfo(host, port_str, &hints, &res);
  if (err != 0) return mk_user_error_str("ws_client_connect: getaddrinfo", gai_strerror(err));

  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) {
    freeaddrinfo(res);
    return mk_user_errno("ws_client_connect: socket");
  }
  if (connect(fd, res->ai_addr, res->ai_addrlen) < 0) {
    int saved = errno;
    close(fd);
    freeaddrinfo(res);
    errno = saved;
    return mk_user_errno("ws_client_connect: connect");
  }
  freeaddrinfo(res);

  int rc = ws_client_handshake(fd, host, port, path);
  if (rc != 0) {
    close(fd);
    char msg[64];
    snprintf(msg, sizeof(msg), "client handshake failed (code %d)", rc);
    return mk_user_error_str("ws_client_connect", msg);
  }

  struct ws_conn *c = new_conn(fd, /*is_client=*/true);
  if (!c) { close(fd); return mk_user_error_str("ws_client_connect", "alloc"); }
  return lean_io_result_mk_ok(wrap_conn(c));
}

/* `wsListen (bindAddr : @& String) (port : UInt16) (backlog : UInt32)
 *   : IO UInt32` */
LEAN_EXPORT lean_obj_res
ocapnlean_ws_listen(b_lean_obj_arg bind_obj, uint16_t port, uint32_t backlog,
                    lean_obj_arg /*io*/) {
  const char *bind_str = lean_string_cstr(bind_obj);
  int lfd = socket(AF_INET, SOCK_STREAM, 0);
  if (lfd < 0) return mk_user_errno("ws_listen: socket");
  int yes = 1;
  setsockopt(lfd, SOL_SOCKET, SO_REUSEADDR, &yes, sizeof(yes));
  struct sockaddr_in addr = {0};
  addr.sin_family = AF_INET;
  addr.sin_port = htons(port);
  if (inet_pton(AF_INET, bind_str, &addr.sin_addr) != 1) {
    close(lfd);
    return mk_user_error_str("ws_listen", "bind address must be IPv4 dotted-decimal");
  }
  if (bind(lfd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
    int saved = errno; close(lfd); errno = saved;
    return mk_user_errno("ws_listen: bind");
  }
  if (listen(lfd, (int)backlog) < 0) {
    int saved = errno; close(lfd); errno = saved;
    return mk_user_errno("ws_listen: listen");
  }
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)lfd));
}

/* `wsAccept (listenFd : UInt32) : IO Conn` */
LEAN_EXPORT lean_obj_res
ocapnlean_ws_accept(uint32_t listen_fd, lean_obj_arg /*io*/) {
  int cfd = accept((int)listen_fd, NULL, NULL);
  if (cfd < 0) return mk_user_errno("ws_accept: accept");
  int rc = ws_server_handshake(cfd);
  if (rc != 0) {
    close(cfd);
    char msg[64];
    snprintf(msg, sizeof(msg), "server handshake failed (code %d)", rc);
    return mk_user_error_str("ws_accept", msg);
  }
  struct ws_conn *c = new_conn(cfd, /*is_client=*/false);
  if (!c) { close(cfd); return mk_user_error_str("ws_accept", "alloc"); }
  return lean_io_result_mk_ok(wrap_conn(c));
}

/* `wsSend (handle : Conn) (bytes : @& ByteArray) (opcode : UInt8) : IO Unit` */
LEAN_EXPORT lean_obj_res
ocapnlean_ws_send(b_lean_obj_arg handle, b_lean_obj_arg bytes, uint8_t opcode,
                  lean_obj_arg /*io*/) {
  struct ws_conn *c = unwrap_conn(handle);
  struct wslay_event_msg msg = {
    .opcode    = opcode,
    .msg       = lean_sarray_cptr(bytes),
    .msg_length = lean_sarray_size(bytes),
  };
  int qrc = wslay_event_queue_msg(c->ctx, &msg);
  if (qrc != 0) return mk_user_error_str("ws_send", "wslay_event_queue_msg failed");
  while (wslay_event_want_write(c->ctx)) {
    int srx = wslay_event_send(c->ctx);
    if (srx != 0) return mk_user_error_str("ws_send", "wslay_event_send failed");
  }
  return lean_io_result_mk_ok(lean_box(0));
}

/* `wsRecv (handle : Conn) : IO (Option ByteArray)`
 *   `none` on clean close (peer sent a CLOSE frame or socket EOF).
 *   Skips control frames; only binary/text messages are surfaced.   */
LEAN_EXPORT lean_obj_res
ocapnlean_ws_recv(b_lean_obj_arg handle, lean_obj_arg /*io*/) {
  struct ws_conn *c = unwrap_conn(handle);
  if (c->msg_ready) goto deliver;
  while (wslay_event_want_read(c->ctx) && !c->msg_ready && !c->eof_seen) {
    int rc = wslay_event_recv(c->ctx);
    if (c->msg_alloc_error) return mk_user_error_str("ws_recv", "out of memory");
    /* WSLAY_ERR_WOULDBLOCK is returned by our recv_cb once a message has
     * already arrived during this call — it's our signal to stop pumping
     * the wslay loop, not a real error. The msg_ready check at the top of
     * the next iteration will see the pending message and break out. */
    if (rc != 0 && rc != WSLAY_ERR_WOULDBLOCK
        && !c->msg_ready && !c->eof_seen) {
      return mk_user_error_str("ws_recv", "wslay_event_recv failed");
    }
  }
  if (!c->msg_ready) {
    /* Clean close. */
    lean_object *none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }
deliver: {
    lean_obj_res ba = lean_alloc_sarray(1, c->msg_len, c->msg_len);
    if (c->msg_len > 0) memcpy(lean_sarray_cptr(ba), c->msg_payload, c->msg_len);
    free(c->msg_payload);
    c->msg_payload = NULL;
    c->msg_len = 0;
    c->msg_ready = false;
    lean_obj_res some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, ba);
    return lean_io_result_mk_ok(some);
  }
}

/* `wsClose (handle : Conn) : IO Unit` */
LEAN_EXPORT lean_obj_res
ocapnlean_ws_close(b_lean_obj_arg handle, lean_obj_arg /*io*/) {
  struct ws_conn *c = unwrap_conn(handle);
  /* Best-effort CLOSE frame; ignore errors. */
  if (c->ctx) {
    wslay_event_queue_close(c->ctx, WSLAY_CODE_NORMAL_CLOSURE, NULL, 0);
    while (wslay_event_want_write(c->ctx)) {
      if (wslay_event_send(c->ctx) != 0) break;
    }
  }
  /* Don't free the conn here — finaliser does that on Lean GC. We
   * just shut the write side so the peer sees EOF promptly. */
  if (c->fd >= 0) shutdown(c->fd, SHUT_WR);
  return lean_io_result_mk_ok(lean_box(0));
}
