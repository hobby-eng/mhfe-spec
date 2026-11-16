#!/usr/bin/env python3
"""Builds the extraction harness of mhfe_core in ../harness.

The harness is a crate whose sources are the crate's own files, reached through symbolic links,
except two: src/feistel.rs and src/cipher.rs, which are written here from the originals by the
exact replacements listed in DYN_TO_GENERIC. They change types only: a `&mut dyn Trait` parameter
or field becomes a generic one, which Aeneas can translate. The hash crates blake2, hmac and sha2
are replaced by shim crates of the same API whose functions Charon keeps opaque; their Lean models
state what the real crates compute.

Every replacement must match exactly as often as listed, so that a change of the original
sources stops the script instead of producing another program. MANIFEST.txt records the commit
of mhfe_core and the SHA-256 of every file the harness reads.
"""

import hashlib
import os
import shutil
import subprocess
import sys

# The workspace holds mhfe_spec and the mhfe_core checkout; MHFE_WORKSPACE overrides it.
WORKSPACE = os.environ.get("MHFE_WORKSPACE") or os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))))))
CRATE = os.path.join(WORKSPACE, "mhfe_core")
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(HERE, "harness")

# (file, old, new, count): the only changes to the crate's sources.
DYN_TO_GENERIC = [
    ("src/feistel.rs",
     "pub(crate) struct Permutation<'a> {\n    pub(crate) engine: &'a mut dyn Argon2Engine,",
     "pub(crate) struct Permutation<'a, E: Argon2Engine> {\n    pub(crate) engine: &'a mut E,", 1),
    ("src/feistel.rs", "impl Permutation<'_> {", "impl<E: Argon2Engine> Permutation<'_, E> {", 1),
    ("src/feistel.rs", "on_round: &mut dyn FnMut(u32) -> ControlFlow<()>,",
     "on_round: &mut impl FnMut(u32) -> ControlFlow<()>,", 2),
    ("src/cipher.rs", "on_round: &mut dyn FnMut(u32, u32) -> ControlFlow<()>,",
     "on_round: &mut impl FnMut(u32, u32) -> ControlFlow<()>,", 2),
    ("src/cipher.rs", "on_unchecked: &mut dyn FnMut(&Phrase) -> ControlFlow<()>,",
     "on_unchecked: &mut impl FnMut(&Phrase) -> ControlFlow<()>,", 1),
    ("src/cipher.rs", "    ) -> Permutation<'a> {", "    ) -> Permutation<'a, E> {", 1),
]

# Files reached through links: everything the library build reads but the two rewritten files.
LINKED = ["build.rs", "vendor", "src/lib.rs", "src/engine.rs", "src/engine", "src/error.rs",
          "src/nfkd.rs", "src/os.rs", "src/os", "src/packing.rs", "src/password.rs",
          "src/password_check.rs", "src/phrase.rs", "src/protect.rs", "src/recovery.rs",
          "src/repair.rs", "src/repair", "src/stack.rs", "src/suite.rs", "src/test_support.rs",
          "src/wallet_check.rs"]

CARGO_TOML = """[package]
name = "mhfe-core"
version = "0.2.0"
edition = "2024"
publish = false
build = "build.rs"

[lib]
path = "src/lib.rs"

[dependencies]
bip39 = { version = "3", default-features = false, features = ["zeroize"] }
blake2 = { path = "shims/blake2", package = "shim-blake2" }
hmac = { path = "shims/hmac", package = "shim-hmac" }
sha2 = { path = "shims/sha2", package = "shim-sha2" }
unicode-normalization = { version = ">=0.1.26, <0.1.27", default-features = false }
zeroize = "1.9"

[target.'cfg(not(target_arch = "wasm32"))'.dependencies]
argon2 = { version = "=0.6.0", default-features = false, features = ["parallel"] }
rayon = "1.12"

[target.'cfg(unix)'.dependencies]
libc = "0.2.191"

[workspace]
"""

SHIMS = {
    "sha2": ("shim-sha2", "", """//! SHA-256 with the API that mhfe_core calls. The functions are opaque to the extraction:
//! the Lean model says what they compute. The bodies are never run.
#![allow(unused_variables, clippy::all)]

/// The output of SHA-256.
pub type Output = [u8; 32];

/// Imported by the crate for `new`, `chain_update`, `finalize` and `digest`.
pub trait Digest {}

/// SHA-256 over the bytes given so far.
pub struct Sha256 {
    _state: (),
}

impl Digest for Sha256 {}

impl Sha256 {
    pub fn new() -> Self {
        unimplemented!()
    }
    pub fn chain_update<T: AsRef<[u8]>>(self, data: T) -> Self {
        unimplemented!()
    }
    pub fn finalize(self) -> Output {
        unimplemented!()
    }
    pub fn digest<T: AsRef<[u8]>>(data: T) -> Output {
        unimplemented!()
    }
}
"""),
    "blake2": ("shim-blake2", "", """//! BLAKE2b with the API that mhfe_core calls. The functions are opaque to the extraction.
#![allow(unused_variables, clippy::all)]

use core::marker::PhantomData;

pub mod digest {
    pub mod consts {
        /// The output length of 32 bytes.
        pub struct U32;
    }
}

/// BLAKE2b with an output length of `N` bytes (only `U32` is used), over the bytes given so far.
pub struct Blake2b<N> {
    _n: PhantomData<N>,
}

impl<N> Blake2b<N> {
    pub fn new() -> Self {
        unimplemented!()
    }
    pub fn chain_update<T: AsRef<[u8]>>(self, data: T) -> Self {
        unimplemented!()
    }
    pub fn finalize(self) -> [u8; 32] {
        unimplemented!()
    }
}
"""),
    "hmac": ("shim-hmac", 'sha2 = { path = "../sha2", package = "shim-sha2" }\n',
             """//! HMAC with the API that mhfe_core calls. The functions are opaque to the extraction.
#![allow(unused_variables, clippy::all)]

use core::marker::PhantomData;

/// Imported by the crate for `update` and `finalize`.
pub trait Mac {}

/// Keyed construction from a key of one block.
pub trait KeyInit: Sized {
    fn new(key: &[u8; 64]) -> Self;
}

/// HMAC over the hash `D` (only SHA-256 is used), keyed, over the bytes given so far.
pub struct Hmac<D> {
    _d: PhantomData<D>,
}

/// The tag.
pub struct CtOutput {
    _bytes: (),
}

impl CtOutput {
    pub fn into_bytes(self) -> [u8; 32] {
        unimplemented!()
    }
}

impl<D> Mac for Hmac<D> {}

impl<D> KeyInit for Hmac<D> {
    fn new(key: &[u8; 64]) -> Self {
        unimplemented!()
    }
}

impl<D> Hmac<D> {
    pub fn update(&mut self, data: &[u8]) {
        unimplemented!()
    }
    pub fn finalize(self) -> CtOutput {
        unimplemented!()
    }
}
"""),
}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        h.update(f.read())
    return h.hexdigest()


def files_under(path):
    if os.path.isdir(path):
        for root, _, names in os.walk(path):
            for name in sorted(names):
                yield os.path.join(root, name)
    else:
        yield path


def main():
    commit = subprocess.check_output(["git", "-C", CRATE, "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(["git", "-C", CRATE, "status", "--porcelain", "--", "src",
                                     "build.rs", "vendor"], text=True).strip()
    if dirty:
        sys.exit("mhfe_core has local changes in its sources:\n" + dirty)
    if os.path.exists(OUT):
        shutil.rmtree(OUT)
    os.makedirs(os.path.join(OUT, "src"))
    for rel in LINKED:
        os.symlink(os.path.join(CRATE, rel), os.path.join(OUT, rel))
    rewritten = {}
    for rel, old, new, count in DYN_TO_GENERIC:
        text = rewritten.get(rel)
        if text is None:
            with open(os.path.join(CRATE, rel)) as f:
                text = f.read()
        found = text.count(old)
        if found != count:
            sys.exit(f"{rel}: expected {count} occurrence(s) of {old!r}, found {found}")
        rewritten[rel] = text.replace(old, new)
    for rel, text in rewritten.items():
        with open(os.path.join(OUT, rel), "w") as f:
            f.write(text)
    with open(os.path.join(OUT, "Cargo.toml"), "w") as f:
        f.write(CARGO_TOML)
    shutil.copy(os.path.join(CRATE, "Cargo.lock"), os.path.join(OUT, "Cargo.lock"))
    for name, (package, deps, source) in SHIMS.items():
        root = os.path.join(OUT, "shims", name)
        os.makedirs(os.path.join(root, "src"))
        with open(os.path.join(root, "Cargo.toml"), "w") as f:
            f.write(f'[package]\nname = "{package}"\nversion = "0.0.0"\nedition = "2024"\n'
                    f'publish = false\n\n[lib]\nname = "{name}"\n\n[dependencies]\n{deps}')
        with open(os.path.join(root, "src", "lib.rs"), "w") as f:
            f.write(source)
    lines = [f"mhfe_core commit {commit}", "", "Read through links (SHA-256, path):"]
    for rel in LINKED:
        for path in files_under(os.path.join(CRATE, rel)):
            lines.append(f"{sha256(path)}  {os.path.relpath(path, CRATE)}")
    lines += ["", "Rewritten (SHA-256 of the original, of the rewrite, path):"]
    for rel in rewritten:
        lines.append(f"{sha256(os.path.join(CRATE, rel))}  {sha256(os.path.join(OUT, rel))}  {rel}")
    with open(os.path.join(OUT, "MANIFEST.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    for rel in rewritten:
        # Labels instead of file times: the diff then depends on the sources alone.
        labels = ["--label", "mhfe_core/" + rel, "--label", "harness/" + rel]
        diff = subprocess.run(["diff", "-u", *labels, os.path.join(CRATE, rel), os.path.join(OUT, rel)],
                              capture_output=True, text=True).stdout
        with open(os.path.join(OUT, rel.replace("/", "_") + ".diff"), "w") as f:
            f.write(diff.replace(CRATE, "mhfe_core").replace(OUT, "harness"))
    print(f"harness written for mhfe_core {commit[:7]}")


if __name__ == "__main__":
    main()
