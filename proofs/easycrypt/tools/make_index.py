# Writes INDEX.md: each result of the text with the formal statements that state it, at file:line.
# Usage: python3 -I tools/make_index.py (from the development root).
import re, os, glob
ROWS = [
 ("Lemma 1 (consistency)", "invpermK permK"),
 ("Lemma 2 (uniformity)", "lemma2"),
 ("Lemma 3 (one input, two rounds); network form", "lemma3 enc_uniform"),
 ("Theorem 1 (random oracle; any fixed functions)", "theorem1 theorem1_fixed"),
 ("Theorem 2 (abstract; Instances.ec realizes it for suite 3 at 12 to 24 words and suite 4 at 12 to 21 words)", "theorem2"),
 ("Corollary: simulating a prepared disclosure", "simulation"),
 ("Lemma G1", "G1"),
 ("Γ2 and inequality (1)", "upto_bad ineq1 lazy_gamma2"),
 ("Lemma G2", "G2"),
 ("Lemma G3", "G3"),
 ("Lemma G4", "G4"),
 ("Lemma G5", "G5"),
 ("Theorem 3 (and its assembly in Γ2)", "theorem3 gamma2"),
 ("Corollary G6", "G6"),
 ("Corollary G7 (the adversary submits its Argon2id queries in batches; a batch of any queries reduces to this by answering its Argon2id queries first)", "G7"),
 ("Proposition G8 (sum and top forms, budget)", "G8 G8_top G8_budget"),
 ("G8 and Theorem 3 bracket the best adversary", "G8_bracket G8_upper"),
 ("Remark G9 (Pr[Perm_w(x) = x] = 2^-256; refusal for every play on Γ0)", "G9 refusal"),
 ("Corollary G10 (Ω(E); checksum-aware form)", "G10 G10_derived"),
 ("G10, matching attack (sum and top forms, budget)", "G10_match G10_top G10_budget"),
 ("A 24-word source without wallet data: Pr[win] <= p_1", "G0_p1"),
 ("δ_X, the pair lemma", "pair_coll mu_coll deltaX"),
 ("Games Δ0, Δ1_j", "Delta0 Delta1"),
 ("Lemma K1", "K1"),
 ("Lemma K2 (order, distinct points, Cross)", "K2_order K2_distinct K2_cross"),
 ("Lemma K3", "K3"),
 ("Lemma K4", "K4"),
 ("Inequality (2), for the monitored chains: the right-hand side includes Early, which the text charges one step later", "averaging"),
 ("Fractional top T(x): the largest weighted sum, between top(floor x) and top(ceil x)", "ftop ftop_max ftop_attained ftop_top"),
 ("Theorem 4 (both inequalities)", "theorem4 theorem4_coarse"),
 ("Remark G9 for Theorem 4 (refusal for every play on Δ0)", "refusalK"),
 ("δ_K, the pair lemma for a known pair (one wrong candidate is accepted with chance at most δ_K)", "pairK deltaK"),
 ("Proposition K5 (sum and top forms, budget)", "K5 K5_top K5_budget"),
 ("K5 and Theorem 4 bracket the best adversary", "K5_bracket K5_upper"),
 ("top2 and Lemma W1", "top2 W1"),
 ("Θ0: the sequential rule of the specification, a covered rule", "SeqU SeqU_pass SeqU_ll"),
 ("Selection rule: a covered rule gives the distribution of the specification's rule", "selection_eq"),
 ("Selection rule: against the rule cut off after 2^80 trials", "selection selection_bound seq_cutoff"),
 ("Selection rule: a rule that stops at a limit and reports a failure keeps the bounds of Theorem 5 (a) and (b)", "theorem5_seed_capped theorem5_pair_capped capped_up"),
 ("Lemma W2 (every covered rule; the cut rule with W2's own constant)", "W2 W2_cut deltacut_le"),
 ("Lemma W3", "W3"),
 ("Lemmas W2 and W3 together, from Θ0 with the cut rule to Θ1", "theta01 theta01_out"),
 ("Lemma W4", "W4"),
 ("Refusal in Θ0", "setup_refused"),
 ("Theorem 5 (every covered rule)", "theorem5_seed theorem5_pair"),
 ("Theorem 5 for the cut rule without refusal", "theorem5_seed_cut theorem5_pair_cut"),
 ("Transfer from the cut rule to every covered rule", "rule_up rule_lo"),
 ("Reading for independent uniform secrets (the exact value, and the upper bound that part (a) uses)", "top2_uniform_eq top2_uniform top2_le"),
 ("A known passphrase: top2(m, n) = top(min(m, n)) and part (b)", "top2_known theorem5_pair_known"),
 ("One cost budget: the main term as a bound valid on every run, where the text writes an expectation; and its reading for uniform secrets, as in the text", "theorem5_cost theorem5_cost_uniform cost_uniform"),
 ("Corollary W5 (every covered rule; cut rule)", "W5 W5_cut"),
 ("The number of trials: E|p_U - 2^-16| <= 2^-136 over the random S and T (with its slack, 2^-136 - 2^-154)", "E_pU E_pU_tight"),
 ("The number of trials: one uniform number per trial decides its outcome with p_U and with 2^-16; the two runs of the cut sequential rule differ with probability at most 2^16 E|p_U - 2^-16|", "cc_upto cc_bad"),
 ("The number of trials: with 2^-16 the outcomes are independent of the selected value, and the adversary can draw them itself (the reduction BO)", "fake_side seq_disclosure BO"),
 ("The number of trials: the sequential rule of the specification against the rule cut off after 2^80 trials", "uncut seqU_disclosure"),
 ("The number of trials: every response after a refusal wins at most as often as one that always wins (the seed, the pair or the phrase from the refused container)", "disc_game disc_game5 RwSeed_win RwPair_win setup_seed"),
 ("The number of trials: Theorem 5 (a) and (b) and Corollary W5 hold with 2^-120 added for the sequential rule (w workers and the general 2^-136 n are not stated)", "theorem5_seed_trials theorem5_pair_trials W5_trials"),
 ("Corollary W6 (seed, pair, phrase)", "W6_seed W6_pair W6_phrase"),
 ("Proposition W7 (seed and pair games, top2 forms, budget, Ω queries after a pass)", "W7_seed W7_pair W7_top2 W7_budget W7_passes"),
 ("W7 and Theorem 5 bracket the best attack on the seed", "W7_bracket W7_upper_cut"),
]
files = sorted(glob.glob("src/*.ec"))
defs = {}
pat = re.compile(r"^(?:local\s+)?(lemma|equiv|module|op)\s+([A-Za-z0-9_']+)")
for f in files:
    for n, line in enumerate(open(f), 1):
        m = pat.match(line)
        if m and not line.startswith("local"):
            defs.setdefault(m.group(2), []).append((f, n, m.group(1)))
out = ["# Index: the results of the text and their formal statements", "",
       "Generated by `tools/make_index.py` from `src/`; line numbers refer to the files as they are. A row names the",
       "statements of a result in the model of `SCOPE.md`. Where a statement is narrower or weaker than the sentence of",
       "the text, the row says so; `README.md` lists every such place (\"Where the formal statements differ from the",
       "text\").", "",
       "| Text | Formal statement | Where |", "| --- | --- | --- |"]
missing = []
for text, names in ROWS:
    locs = []
    for nm in names.split():
        if nm not in defs:
            missing.append(nm); continue
        f, n, kind = defs[nm][0]
        locs.append((nm, f"{f}:{n}"))
    out.append("| %s | %s | %s |" % (text, ", ".join("`%s`" % a for a, _ in locs), ", ".join(b for _, b in locs)))
open("INDEX.md", "w").write("\n".join(out) + "\n")
print("missing:", missing)
