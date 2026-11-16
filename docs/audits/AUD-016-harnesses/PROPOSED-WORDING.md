# Proposed trial-disclosure wording

These are review proposals for AUD-016. They have **not** been applied to the specification.
They preserve the sequential `2^-120` term and do not claim formal verification of workers,
general expected trial count, capped generation with disclosure, or physical timing behavior.

## A.6: qualify the general disclosure claim

In the paragraph **The number of trials**, add a condition specific to that disclosure claim:

> For this disclosure claim, any coins used to select or schedule trials must also be sampled
> jointly independently of the secrets, the functions and the underlying sequence of entropy
> draws. Selection and scheduling may use the trial order, the pass/fail outcomes and these coins,
> but no other information about the secrets, functions or trial values.

Keep the existing independent-noise condition on disclosed duration. This addition belongs to the
revealed-trial extension; it need not strengthen the earlier rule with hidden trials. Do not demand
that scheduling coins remain independent after conditioning on stopping or on the transcript.
Independence is a condition on their initial sampling, before their use in the rule.

Without that clarification, a fair bit equal to a binary password meets the literal condition
“coins independent of the trial values”: it can choose whether to stop at the first or second
pass. The source remains uniform on the passing set, but the disclosed number of PASS outcomes
identifies the password. The checked sequential implementations use the first pass and do not
permit this secret-dependent selection.

## Specification README: elapsed generation time

Replace the sentence beginning “An implementation MAY show the number of trials” with:

> An implementation MAY show the number of trials while it draws, and the elapsed generation time
> if, for fixed public settings, that time is a function only of the revealed pass/fail outcomes
> and of randomness jointly independent of the password, the passphrase, the functions and the
> trial values.

The count is the length of the outcome sequence. The condition excludes **additional** hidden
inputs to timing; it does not assert that the duration is unconditionally independent of the
secrets/functions, since the permitted outcomes already depend weakly on them. For a progress
trace the analogous restriction applies to every emitted timing observation and its outcome prefix.

## DESIGN-NOTES: Theorem 5 summary

Replace the sentence beginning “Revealing their outcomes and number” with:

> Revealing their outcomes and number, with a duration that depends only on these and on coins
> jointly independent of the secrets, the functions and the trial values, adds `2^-120` to the
> bound for the sequential rule (`2^-136·n` in general; see the selection rule in A.6).

## DESIGN-NOTES: assumption 4

Replace its final sentence with:

> The selection rule of A.6 shows the cost of revealing the wallet-check profile's trial outcomes,
> their number and a duration that depends only on these and on coins jointly independent of the
> secrets, the functions and the trial values.

## Consistency and application checks

Use the same full independence list, or a link to A.6, in the EasyCrypt README's duration sentence.
Other short specification references may link to A.6 instead of duplicating its conditions.
The two DESIGN-NOTES summaries currently saying “only on these” are restrictive deterministic
shorthands; adding independent coins aligns their expressiveness. The README's exclusion of only
trial value/passphrase is the substantive permission that needs tightening.

These edits do not establish that measured BIP39/PBKDF2 or OS time satisfies the condition. For a
verified sequential disclosure claim, showing the trial count does not by itself justify showing
arbitrary wall-clock time. A bounded search exposing its attempts remains outside the final formal
endpoints audited here. Check requirement identifiers, changelog wording and document consistency
when an authorized specification edit is applied; do not renumber existing identifiers.
