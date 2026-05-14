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

/-- Build `c/crypto.c` to an `.o` linked into the Crypto FFI lib. -/
target cryptoShim pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "crypto.o"
  let srcJob ← cryptoShimSrc.fetch
  let incDir ← libsodium.includeDir
  let flags := #[
    "-std=c11",
    "-fPIC",
    "-O2",
    "-Wall",
    "-I", (← getLeanIncludeDir).toString,
    "-I", incDir
  ]
  buildO oFile srcJob flags

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

/-- FFI-only lib. Precompiled so the `.o` is linked into a shared
object that both the executable and the interpreter can dlopen.
Isolated from the rest of `OcapnLean.*` to keep the precompile cost
small (only this single module is native-compiled). -/
@[default_target]
lean_lib OcapnLeanCrypto where
  srcDir := "."
  roots := #[`OcapnLean.Crypto]
  precompileModules := true
  moreLinkObjs := #[cryptoShim]
  moreLinkArgs := sodiumLinkArgs

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
    `OcapnLean.Captp.Run,
    `OcapnLean.Captp.Bootstrap,
    `OcapnLean.Captp.Session,
    `OcapnLean.Test.Interop
  ]

/-- Path the cryptoShim target writes its .o to. Lake doesn't surface a
nicer accessor here, so we hardcode it; the value matches the target
defined above. -/
def cryptoShimOPath : String :=
  ".lake/build/c/crypto.o"

/-- `lean_exe` doesn't have a `moreLinkObjs` field, but plain object
paths in `moreLinkArgs` are accepted by the linker — so we slip
crypto.o in that way. -/
@[default_target]
lean_exe «ocapn-server» where
  root := `OcapnLean.Server
  needs := #[cryptoShim]
  moreLinkArgs := #[cryptoShimOPath] ++ sodiumLinkArgs
