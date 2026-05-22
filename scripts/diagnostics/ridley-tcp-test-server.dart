// Ridley dobjects interop probe used by ocapn-lean.
//
// Spins up a `tcp-testing-only` netlayer using Ridley's own
// `TCPTestingNetLayer`, listens on the requested port, accepts one
// inbound connection, and drives `activate()`. This exercises:
//
//   1. Ridley's netstring de-framer on our outbound op:start-session.
//   2. Ridley's Syrup decoder on the de-framed body.
//   3. Ridley's CapTP version check.
//   4. Ridley's signature verification of our acceptable-location.
//   5. Ridley's reciprocal op:start-session, written back through
//      its own netstring framer for our client to read.
//
// Setup (one-time, inside the Ridley submodule):
//
//   cd projects/ridley-dobjects
//   dart pub get
//   echo /path/to/libsodium.so > test/utils/libsodium_path.txt
//   cp ../../scripts/diagnostics/ridley-tcp-test-server.dart .
//
// Run:
//
//   dart run ridley-tcp-test-server.dart --port 22047
//
// Then in another shell:
//
//   lake exe client-vs-external -- --port 22047 \
//     --frame netstring --captp-version 0.1 --hints false \
//     --handshake-only
//
// Verified working 2026-05-16 against the Ridley submodule snapshot
// at projects/ridley-dobjects (CapTP version 0.1, dart 3.11.4,
// libsodium 1.0.21).

import 'dart:async';
import 'dart:io';
import 'dart:ffi';
import 'package:d_objects/src/net_layers/tcp_testing_net_layer/tcp_testing_net_layer.dart';
import 'package:sodium/sodium.dart';

Future<void> main(List<String> args) async {
  int port = 22047;
  for (var i = 0; i + 1 < args.length; i++) {
    if (args[i] == '--port') port = int.parse(args[i + 1]);
  }

  final libsodiumPath =
      (await File('test/utils/libsodium_path.txt').readAsString()).trim();
  final sodium = await SodiumInit.init(() => DynamicLibrary.open(libsodiumPath));

  final netLayer = TCPTestingNetLayer(sodium: sodium);
  // Bind 127.0.0.1 explicitly — `localhost` may resolve to ::1 first
  // and Lean's `Tcp.connect` is currently IPv4-only.
  await netLayer.init(
    designator: 'ocapn-lean-interop-probe',
    address: InternetAddress.loopbackIPv4,
    port: port,
  );
  print('[ridley-probe] tcp-testing-only listening on '
      '${netLayer.ourLocator.hints['host']}:${netLayer.ourLocator.hints['port']}');

  try {
    final authConn = await netLayer.incomingConnections.first
        .timeout(Duration(seconds: 15));
    print('[ridley-probe] incomingConnections yielded AuthenticatedConnection '
        '(theirLocator=${authConn.theirLocator})');

    final activated =
        await authConn.activate().timeout(Duration(seconds: 5));
    print('[ridley-probe] activate() resolved '
        '(ours=${activated.ourLocator}, theirs=${activated.theirLocator})');
    print('PASS: framing + handshake interop verified end-to-end');
  } on TimeoutException {
    print('[ridley-probe] timeout — incomingConnections never yielded.');
    print('  CommonNetLayer._handleStartSessionOp rejected the inbound');
    print('  message (and silently sent op:abort back). Likely causes:');
    print('    - missing --frame netstring on the Lean side');
    print('    - missing --captp-version 0.1 (Ridley uses 0.1, not 1.0)');
    print('    - missing --hints false (Ridley re-encodes empty');
    print('      hints as false during sig verification — see');
    print('      INTEROP.md Disagreement 3)');
    exitCode = 1;
  } catch (e, st) {
    print('[ridley-probe] FAIL: $e');
    print(st);
    exitCode = 1;
  } finally {
    await netLayer.close();
  }
}
