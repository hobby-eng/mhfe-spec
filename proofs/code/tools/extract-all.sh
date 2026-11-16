#!/usr/bin/env bash
# The extraction of record: every module the cipher uses, with the items Aeneas cannot translate
# kept opaque. Each opaque item of mhfe_core gets a Lean definition in MhfeCore/Assumptions/,
# written from its Rust source and compared with it line by line (see README.md).
here=$(cd "$(dirname "$0")/.." && pwd)
starts="--start-from mhfe_core::feistel --start-from mhfe_core::packing --start-from mhfe_core::suite --start-from mhfe_core::recovery --start-from mhfe_core::cipher --start-from mhfe_core::wallet_check --start-from 'mhfe_core::password::_::as_bytes'"
# Not translatable by Aeneas build-2b9e3ea (reasons in README.md):
untranslatable="--opaque 'mhfe_core::feistel::_::parts' --opaque 'mhfe_core::feistel::_::round' --opaque 'mhfe_core::feistel::_::forward' --opaque 'mhfe_core::feistel::_::inverse' --opaque mhfe_core::recovery::lengths"
# Outside the proof: the operating system, the stack clearing, the hash functions, BIP39 and NFKD,
# and the formatting of values.
outside="--opaque mhfe_core::os --opaque mhfe_core::engine::native --opaque mhfe_core::stack::overwrite --opaque sha2 --opaque blake2 --opaque hmac --opaque mhfe_core::phrase --opaque mhfe_core::nfkd --opaque bip39 --opaque '{impl core::fmt::Debug for _}' --opaque '{impl core::fmt::Display for _}'"
X_CHARON="$starts --inline-anon-consts $untranslatable $outside" exec "$here/tools/extract.sh"
