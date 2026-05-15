/* OcapnLean — Unix Domain Socket FFI shim.
 *
 * Minimal AF_UNIX socket primitives so Lean can speak Goblins's
 * `testuds` netlayer (and any other UDS-backed OCapN peer). The
 * Lean wrappers in OcapnLean.Netlayer.Uds expose these as IO
 * actions and wrap raw fds in the standard `Netlayer` interface.
 *
 * All blocking calls use the kernel's default semantics (no
 * non-blocking flags). That is fine for our use because each
 * connection is driven on a dedicated Lean task (`IO.asTask
 * (prio := .dedicated)`), the same pattern used for the TCP
 * netlayer.
 */

#include <lean/lean.h>

#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/un.h>
#include <unistd.h>

static lean_obj_res mk_user_errno(const char *prefix) {
  char buf[512];
  snprintf(buf, sizeof(buf), "%s: %s", prefix, strerror(errno));
  lean_object *msg = lean_mk_string(buf);
  return lean_io_result_mk_error(lean_mk_io_user_error(msg));
}

static void fill_sun(struct sockaddr_un *addr, const char *path) {
  memset(addr, 0, sizeof(*addr));
  addr->sun_family = AF_UNIX;
  strncpy(addr->sun_path, path, sizeof(addr->sun_path) - 1);
}

/* `udsConnect (path : @& String) : IO UInt32` */
LEAN_EXPORT lean_obj_res
ocapnlean_uds_connect(b_lean_obj_arg path_obj, lean_obj_arg /* io */) {
  const char *path = lean_string_cstr(path_obj);
  int fd = socket(AF_UNIX, SOCK_STREAM, 0);
  if (fd < 0) return mk_user_errno("uds_connect: socket");
  struct sockaddr_un addr;
  fill_sun(&addr, path);
  if (connect(fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
    int saved = errno;
    close(fd);
    errno = saved;
    return mk_user_errno("uds_connect: connect");
  }
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/* `udsListen (path : @& String) (backlog : UInt32) : IO UInt32` */
LEAN_EXPORT lean_obj_res
ocapnlean_uds_listen(b_lean_obj_arg path_obj, uint32_t backlog,
                     lean_obj_arg /* io */) {
  const char *path = lean_string_cstr(path_obj);
  /* Best-effort unlink to clear any stale file from a prior run. */
  unlink(path);
  int fd = socket(AF_UNIX, SOCK_STREAM, 0);
  if (fd < 0) return mk_user_errno("uds_listen: socket");
  struct sockaddr_un addr;
  fill_sun(&addr, path);
  if (bind(fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
    int saved = errno;
    close(fd);
    errno = saved;
    return mk_user_errno("uds_listen: bind");
  }
  if (listen(fd, (int)backlog) < 0) {
    int saved = errno;
    close(fd);
    errno = saved;
    return mk_user_errno("uds_listen: listen");
  }
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/* `udsAccept (listenFd : UInt32) : IO UInt32` */
LEAN_EXPORT lean_obj_res
ocapnlean_uds_accept(uint32_t listen_fd, lean_obj_arg /* io */) {
  int conn = accept((int)listen_fd, NULL, NULL);
  if (conn < 0) return mk_user_errno("uds_accept: accept");
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)conn));
}

/* `udsRead (fd : UInt32) (maxBytes : USize) : IO (Option ByteArray)`
 * Returns `none` on clean EOF, raises on error. */
LEAN_EXPORT lean_obj_res
ocapnlean_uds_read(uint32_t fd, size_t max_bytes, lean_obj_arg /* io */) {
  if (max_bytes == 0) max_bytes = 4096;
  uint8_t *buf = (uint8_t *)malloc(max_bytes);
  if (!buf) return mk_user_errno("uds_read: malloc");
  ssize_t n;
  do { n = read((int)fd, buf, max_bytes); }
  while (n < 0 && errno == EINTR);
  if (n < 0) { free(buf); return mk_user_errno("uds_read: read"); }
  if (n == 0) {
    free(buf);
    /* EOF: return `none`. */
    lean_obj_res none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }
  lean_obj_res ba = lean_alloc_sarray(1, (size_t)n, (size_t)n);
  memcpy(lean_sarray_cptr(ba), buf, (size_t)n);
  free(buf);
  /* Some : ByteArray */
  lean_obj_res some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, ba);
  return lean_io_result_mk_ok(some);
}

/* `udsWrite (fd : UInt32) (bytes : @& ByteArray) : IO Unit`
 * Loops until all bytes are sent or an error occurs. */
LEAN_EXPORT lean_obj_res
ocapnlean_uds_write(uint32_t fd, b_lean_obj_arg bytes,
                    lean_obj_arg /* io */) {
  const size_t total = lean_sarray_size(bytes);
  const uint8_t *p = lean_sarray_cptr(bytes);
  size_t sent = 0;
  while (sent < total) {
    ssize_t n;
    do { n = write((int)fd, p + sent, total - sent); }
    while (n < 0 && errno == EINTR);
    if (n < 0) return mk_user_errno("uds_write: write");
    sent += (size_t)n;
  }
  return lean_io_result_mk_ok(lean_box(0));
}

/* `udsClose (fd : UInt32) : IO Unit` */
LEAN_EXPORT lean_obj_res
ocapnlean_uds_close(uint32_t fd, lean_obj_arg /* io */) {
  close((int)fd);
  return lean_io_result_mk_ok(lean_box(0));
}

/* `udsUnlink (path : @& String) : IO Unit` */
LEAN_EXPORT lean_obj_res
ocapnlean_uds_unlink(b_lean_obj_arg path_obj, lean_obj_arg /* io */) {
  const char *path = lean_string_cstr(path_obj);
  unlink(path);  /* ignore errors; ENOENT is fine */
  return lean_io_result_mk_ok(lean_box(0));
}
