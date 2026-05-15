import Lake
open Lake DSL System

package «ocapn-lean»

require veil from git "https://github.com/verse-lab/veil.git" @ "main"

/-! ## libsodium paths

The C shim in `c/crypto.c` links against libsodium. We hard-code the
two nix-store paths used on this development machine; on a different
host, set `LIBSODIUM_INCLUDE` and `LIBSODIUM_LIB` env vars before
running `lake build` (or edit the constants below). A future
improvement would be to probe via `pkg-config`. -/

def libsodium.defaultIncludeDir : String :=
  "/nix/store/zyk5r62rh170h3zff7ffg4jky943il62-libsodium-1.0.21-unstable-2026-03-29-dev/include"

def libsodium.defaultLibDir : String :=
  -- 64-bit build paired with the -dev headers above; the sibling
  -- `1hbn13…` path is the 32-bit i386 build and would fail to link.
  "/nix/store/z4yz8jy4hipl0mvyj8dy77s5brajzviv-libsodium-1.0.21-unstable-2026-03-29/lib"

def libsodium.includeDir : IO String := do
  match ← IO.getEnv "LIBSODIUM_INCLUDE" with
  | some s => pure s
  | none   => pure libsodium.defaultIncludeDir

input_file cryptoShimSrc where
  path := "c" / "crypto.c"
  text := true

input_file udsShimSrc where
  path := "c" / "uds.c"
  text := true

/-- libsodium link args, used wherever the FFI shim is pulled in.

The `--allow-shlib-undefined` is needed because libsodium references
GLIBC_2.33 symbols (e.g. `fstat`) which the Lean toolchain's bundled
glibc (≤2.26) doesn't export. The dynamic loader picks the system's
glibc 2.42 at runtime, which has them. -/
def sodiumLinkArgs : Array String := #[
  s!"-L{libsodium.defaultLibDir}",
  s!"-Wl,-rpath,{libsodium.defaultLibDir}",
  "-lsodium",
  "-Wl,--allow-shlib-undefined"
]

/-- Build the C shim into a static archive (`libocapnLeanShim.a`).
This is what executables and other static consumers link against. -/
extern_lib libocapnLeanShim pkg := do
  let cryptoO := pkg.buildDir / "c" / "crypto.o"
  let udsO    := pkg.buildDir / "c" / "uds.o"
  let aFile := pkg.staticLibDir / nameToStaticLib "ocapnLeanShim"
  let cryptoSrcJob ← cryptoShimSrc.fetch
  let udsSrcJob ← udsShimSrc.fetch
  let incDir ← libsodium.includeDir
  let cryptoFlags := #[
    "-std=c11",
    "-fPIC",
    "-O2",
    "-Wall",
    "-I", (← getLeanIncludeDir).toString,
    "-I", incDir
  ]
  let udsFlags := #[
    "-std=c11",
    "-fPIC",
    "-O2",
    "-Wall",
    "-I", (← getLeanIncludeDir).toString
  ]
  let cryptoOJob ← buildO cryptoO cryptoSrcJob cryptoFlags
  let udsOJob ← buildO udsO udsSrcJob udsFlags
  buildStaticLib aFile #[cryptoOJob, udsOJob]

/-- FFI-only lib. -/
@[default_target]
lean_lib OcapnLeanCrypto where
  srcDir := "."
  roots := #[`OcapnLean.Crypto]
  precompileModules := true
  moreLinkArgs := sodiumLinkArgs

/-- Precompiled UDS FFI lib. Same trick as OcapnLeanCrypto: the
extern symbols live in the shared `libocapnLeanShim` static archive
(`c/uds.c`), and `precompileModules` makes Lake link them into the
downstream binaries. -/
@[default_target]
lean_lib OcapnLeanUds where
  srcDir := "."
  roots := #[`OcapnLean.Uds]
  precompileModules := true

/-- Main library — every `OcapnLean.*` module except `Crypto`,
which lives in the precompiled `OcapnLeanCrypto` lib above. -/
@[default_target]
lean_lib OcapnLean where
  srcDir := "."
  roots := #[
    `OcapnLean,
    `OcapnLean.Model,
    `OcapnLean.Syrup,
    `OcapnLean.Server,
    `OcapnLean.Netlayer,
    `OcapnLean.Netlayer.Tcp,
    `OcapnLean.Netlayer.Uds,
    `OcapnLean.Syrup.Extended,
    `OcapnLean.Captp.Messages,
    `OcapnLean.Captp.Spec,
    `OcapnLean.Captp.Twoparty,
    `OcapnLean.Captp.CrossedHellos,
    `OcapnLean.Captp.Gc,
    `OcapnLean.Captp.NoForgery,
    `OcapnLean.Captp.Threeparty,
    `OcapnLean.Captp.Impl,
    `OcapnLean.Captp.Refinement,
    `OcapnLean.Captp.RefinementExtended,
    `OcapnLean.Captp.Run,
    `OcapnLean.Captp.Bootstrap,
    `OcapnLean.Captp.Session,
    `OcapnLean.Captp.Client,
    `OcapnLean.Test.Interop
  ]

/-- The executable doesn't need to mention the shim explicitly — the
`extern_lib libocapnLeanShim` above is auto-linked into anything that
transitively imports `OcapnLean.Crypto` (here, via `OcapnLean.Server →
… → OcapnLean.Captp.Session → OcapnLean.Crypto`). We only need to
pass through the libsodium link args. -/
@[default_target]
lean_exe «ocapn-server» where
  root := `OcapnLean.Server
  moreLinkArgs := sodiumLinkArgs

/-! ## Smoke tests packaged as executables

Lake's per-module dynlibs don't pick up the extern_lib on Linux
(`linkDeps := Platform.isWindows` in `buildLeanSharedLib`), which
means `lake env lean --run scripts/foo.lean` can't resolve our
`@[extern]` symbols. Wrapping the smoke scripts as `lean_exe`
targets bypasses that — the extern_lib is statically linked into
the executable at build time. Run with `lake exe <name>`. -/

lean_exe «crypto-smoke» where
  root := `scripts.CryptoSmoke
  srcDir := "."
  moreLinkArgs := sodiumLinkArgs

lean_exe «session-handshake-smoke» where
  root := `scripts.SessionHandshakeSmoke
  srcDir := "."
  moreLinkArgs := sodiumLinkArgs

lean_exe «enlivener-smoke» where
  root := `scripts.EnlivenerSmoke
  srcDir := "."
  moreLinkArgs := sodiumLinkArgs

lean_exe «client-smoke» where
  root := `scripts.ClientSmoke
  srcDir := "."
  moreLinkArgs := sodiumLinkArgs

lean_exe «client-vs-external» where
  root := `scripts.ClientVsExternal
  srcDir := "."
  moreLinkArgs := sodiumLinkArgs

lean_exe «uds-smoke» where
  root := `scripts.UdsSmoke
  srcDir := "."
  moreLinkArgs := sodiumLinkArgs
