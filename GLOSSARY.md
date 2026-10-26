# MHFE

The language of Memory-Hard Feistel Encryption: how an original seed phrase is encrypted under a
password into a container phrase and recovered from it.

## Language

<!-- Each term, its definition and its Avoid list stay on lines of their own, as the glossary format
has them, so the formatter leaves this section unwrapped. -->
<!-- prettier-ignore-start -->

### Phrases and backups

**Original seed phrase**:
The wallet's own BIP39 phrase that MHFE encrypts; the specification's formulas call it the source.
_Avoid_: the original (alone)

**Container**:
The encrypted result of MHFE for one original seed phrase, password and settings: itself an ordinary, checksum-valid BIP39 phrase.
_Avoid_: ciphertext, encrypted mnemonic, encrypted phrase

**Container phrase**:
The written words that hold an MHFE-encrypted original seed phrase: 24 in suite 3, as many as the original seed phrase in suite 4.
_Avoid_: plate, seed plate

**Backup**:
The paper or metal medium that holds a container phrase.

**Metal backup**:
The physical metal medium that a container phrase is written on, when such a medium is meant.
_Avoid_: plate

**Reading**:
A phrase that recovery derives from the recovered state for one word count.

### Suites and settings

**Suite**:
A frozen set of parameters, named by its suite identifier, that fixes how a container is made and read.

**Same-length container**:
A suite 4 container, which has as many words as its original seed phrase.
_Avoid_: length-preserving container

**PIM**:
The pass multiplier, from 0 to 1023, that lengthens every round; 0 by default.
_Avoid_: iterations

**Memory level**:
The setting, from 0 to 21, that fixes the memory of every round, from 2 GiB at level 0 to 3 TiB at level 21.
_Avoid_: memory cost

### Recovery

**Stated length**:
The word count of the original seed phrase that the user gives at recovery.

**Detected length**:
A word count whose verifier matches the recovered state.

**Verifier**:
The bits that a suite 3 container of a 12- to 21-word original seed phrase carries to recognise the right password and length; they do not identify the wallet.

**Built-in check**:
The comparison of a reading with its verifier.

**Wallet-identity reference**:
Independent data that identifies a wallet: a known receiving address with its coin, network, address type and derivation path, or its master key fingerprint.

**Creation check**:
The recovery that creation runs on a new container, every round computed afresh, before the container counts as verified.
_Avoid_: check at creation, round-trip check

**Rehearsal**:
A full recovery from the finished backup, made before the container is relied on, that reports "matches", "does not match" or "not verified", and, besides that result, only facts that reveal no word of the mnemonic.

**Re-encryption**:
Encrypting a recovered original seed phrase again under another password, suite or settings, after the phrase is confirmed.

### Optional profiles

**Wallet check**:
The optional check that a new 24-word original seed phrase, with its BIP39 passphrase, is chosen to pass, so that recovery can recognise a wrong password.
_Avoid_: source check, seed check

**Repair words**:
Extra BIP39 words computed from a finished container that let an application restore unreadable or miscopied container words without the password.

**Repair card**:
The separate card that carries the repair words of one container.

**Password check word**:
The sixth word of a generated password, computed from the first five, that catches typing errors before any Argon2id work.

### Deniability

**Decoy password**:
A password other than the real one that the owner discloses for a container; it recovers a valid but different phrase, the decoy phrase.

**Decoy wallet**:
The wallet of a decoy phrase.

**Hidden wallet**:
A wallet that the owner derives from a genuine wallet's container with a second password, so that the disclosed password opens the genuine wallet.

<!-- prettier-ignore-end -->
