(* A 24-word source with an unknown BIP39 passphrase (DESIGN-NOTES A.6): passphrases, seeds, the
   functions S, T and Omega, pair masses and Lemma W1, the selection interface and the games Θ0, Θ0',
   Θ1 and Θ2. ENT = 256, so the state is the entropy and G does not enter. *)
require import AllCore List Distr DBool DProd FMap IntDiv StdBigop StdOrder Xreal.
require import Suite3 Chain Collision.
require (*--*) BitWord FinType PROM.
import W128 StdBigop.Bigreal.BRA RealOrder.

(* ---- Passphrases, seeds, the check digest and the wallet data ------------------------------- *)
type pp.                                   (* normalized BIP39 passphrases, a finite set *)
clone FinType.FinType as PpT with type t <- pp.
op dQ : pp distr.
axiom dQ_ll : is_lossless dQ.

clone BitWord as W512 with op n <- 512 proof gt0_n by done.     (* BIP39 seeds *)
clone BitWord as W16 with op n <- 16 proof gt0_n by done.       (* the first 16 bits of T *)
clone BitWord as W240 with op n <- 240 proof gt0_n by done.     (* the other 240 bits of T *)
const lambda : { int | 0 < lambda } as gt0_lambda.
clone BitWord as WL with op n <- lambda proof gt0_n by exact gt0_lambda.   (* Omega(seed) *)

type seed = W512.word.
type data = WL.word.
op zero16 : W16.word = W16.zerow.
op dseed : seed distr = W512.DWord.dunifin.
op dct : (W16.word * W240.word) distr = W16.DWord.dunifin `*` W240.DWord.dunifin.
op ddata : data distr = WL.DWord.dunifin.

clone import PROM.FullRO as RS with
  type in_t <- state * pp, type out_t <- seed, op dout <- (fun _ => dseed),
  type d_in_t <- unit, type d_out_t <- bool.
clone import PROM.FullRO as RT with
  type in_t <- seed, type out_t <- W16.word * W240.word, op dout <- (fun _ => dct),
  type d_in_t <- unit, type d_out_t <- bool.
clone import PROM.FullRO as RW with
  type in_t <- seed, type out_t <- data, op dout <- (fun _ => ddata).

lemma dseed_ll : is_lossless dseed by exact W512.DWord.dunifin_ll.
lemma ddata_ll : is_lossless ddata by exact WL.DWord.dunifin_ll.
lemma dct_ll : is_lossless dct.
proof. by rewrite /dct; apply/dprod_ll; rewrite W16.DWord.dunifin_ll W240.DWord.dunifin_ll. qed.
lemma dseed1 (x : seed) : mu1 dseed x = inv (2%r ^ 512).
proof. by rewrite /dseed W512.DWord.dunifin1E W512.word_card /=; smt(RField.fromintXn). qed.
lemma e512_gt0 : 0%r < inv (2%r ^ 512) by smt(RealOrder.expr_gt0 RealOrder.invr_gt0).
lemma ddata1 (x : data) : mu1 ddata x = inv (2%r ^ lambda).
proof. by rewrite /ddata WL.DWord.dunifin1E WL.word_card; smt(RField.fromintXn gt0_lambda). qed.

(* S and T as whole functions, for the selection rules. *)
op sp_enum : (state * pp) list =
  allpairs (fun (x : state) (q : pp) => (x, q))
    (allpairs (fun (a b : W128.word) => (a, b)) W128.words W128.words) PpT.enum.

lemma sp_enum_uniq : uniq sp_enum.
proof.
apply allpairs_uniq; [| exact PpT.enum_uniq | smt()].
by apply allpairs_uniq; [exact W128.enum_uniq | exact W128.enum_uniq | smt()].
qed.

lemma sp_enumP (c : state * pp) : c \in sp_enum.
proof.
case: c => [[a b] q]; rewrite allpairsP; exists ((a, b), q) => /=.
by rewrite PpT.enumP allpairsP /=; exists (a, b); rewrite !W128.enumP.
qed.

clone FinType.FinType as SPT with type t = state * pp, op enum = sp_enum proof enum_spec.
realize enum_spec. proof. by move=> c; rewrite count_uniq_mem 1:sp_enum_uniq sp_enumP. qed.
clone FinType.FinType as SeedT with type t = seed, op enum = W512.words proof enum_spec.
realize enum_spec. proof. exact W512.enum_spec. qed.

clone RS.FinEager as RSE with theory FinFrom <- SPT.
clone RT.FinEager as RTE with theory FinFrom <- SeedT.

(* ---- Oracles ---------------------------------------------------------------------------------- *)
module type OraclesP = {
  proc a(p : pw, s : W128.word) : W256.word
  proc b(i : ridx, r : W128.word) : W128.word
  proc h(k : W256.word, i : ridx, r : W128.word) : W128.word
  proc s(e : state, q : pp) : seed
  proc t(d : seed) : W16.word * W240.word
  proc w(d : seed) : data
}.

(* The adversary receives Y and omega* and outputs a string sigma and a pair of a password and a
   passphrase. *)
module type AdvP (O : OraclesP) = {
  proc guess(y : state, om : data) : seed * (pw * pp)
}.

module CountP (O : OraclesP) = {
  var cs, ct, cw : int
  proc init() = { Count(O).init(); cs <- 0; ct <- 0; cw <- 0; }
  proc a = Count(O).a
  proc b = Count(O).b
  proc h = Count(O).h
  proc s(e : state, q : pp) = { var d; cs <- cs + 1; d <@ O.s(e, q); return d; }
  proc t(d : seed) = { var c; ct <- ct + 1; c <@ O.t(d); return c; }
  proc w(d : seed) = { var o; cw <- cw + 1; o <@ O.w(d); return o; }
}.

module IP : OraclesP = {
  proc a = Ideal.a
  proc b = Ideal.b
  proc h = Ideal.h
  proc s(e : state, q : pp) = { var d; d <@ RS.RO.get(e, q); return d; }
  proc t(d : seed) = { var c; c <@ RT.RO.get(d); return c; }
  proc w(d : seed) = { var o; o <@ RW.RO.get(d); return o; }
}.

(* ---- Pair masses ------------------------------------------------------------------------------ *)
(* Passphrases v_1, v_2, ... by decreasing probability and s_j = Pr[Q = v_j] (0 past the last one). *)
op rankedQ : pp list = sort (fun (u v : pp) => mu1 dQ v <= mu1 dQ u) PpT.enum.
op sr (j : int) : real = if 1 <= j <= size rankedQ then mu1 dQ (nth witness rankedQ (j - 1)) else 0%r.
op s1 : real = sr 1.

(* top2(m, n): the sum of the n largest products p_i s_j over index pairs with i <= m, or of all of
   them if there are fewer. *)
op top2 (m n : int) : real =
  big predT idfun (take n (sort (fun (a b : real) => b <= a)
    (allpairs (fun i j => pr i * sr j) (iota_ 1 m) (iota_ 1 (size rankedQ))))).

op mass2 (ps : (pw * pp) list) : real = big predT (fun (x : pw * pp) => mu1 dP x.`1 * mu1 dQ x.`2) ps.

(* ---- The sum of the n largest values bounds the sum of any n of them ------------------------ *)
lemma count_mono (p q : 'a -> bool) (s : 'a list) : (forall x, x \in s => p x => q x) => count p s <= count q s.
proof.
elim: s => //= x s ih h.
have := ih _; 1: by move=> y hy; apply h; right.
by have := h x; rewrite /b2i; smt().
qed.

(* In a list sorted downwards, a value reached by i + 1 entries is at most the entry at i. *)
lemma sorted_count (S : real list) v i : sorted (fun (a b : real) => b <= a) S => 0 <= i < size S =>
  i + 1 <= count (fun x => v <= x) S => v <= nth 0%r S i.
proof.
move=> hs hi hc; case: (v <= nth 0%r S i) => // /ltrNge hlt.
have hmono : forall k, i <= k < size S => nth 0%r S k <= nth 0%r S i.
- by move=> k hk; apply (sorted_nth (fun (a b : real) => b <= a) S 0%r i k) => //; smt().
have : count (fun x => v <= x) S <= i.
- rewrite -(mkseq_nth 0%r S) /mkseq count_map.
  apply (IntOrder.ler_trans (count (fun t => t < i) (iota_ 0 (size S)))).
  + by apply count_mono => t /mem_iota ht /= hv; case: (t < i) => // /IntOrder.lerNgt hti; have := hmono t _; smt().
  rewrite -size_filter; apply (IntOrder.ler_trans (size (iota_ 0 i))); 2: smt(size_iota).
  apply uniq_leq_size; 1: by apply filter_uniq; apply iota_uniq.
  by move=> t; rewrite mem_filter !mem_iota /#.
smt().
qed.

(* The entries of any uniq sub-list of P, through a nonnegative f, weigh at most the size-many
   largest values of map f P. *)
lemma top_sum (f : 'a -> real) (I P : 'a list) n : uniq I => (forall x, x \in I => x \in P) =>
  size I <= n => (forall x, x \in P => 0%r <= f x) =>
  big predT f I <= big predT idfun (take n (sort (fun (a b : real) => b <= a) (map f P))).
proof.
move=> hu hsub hn hpos.
pose X := sort (fun (a b : real) => b <= a) (map f I).
pose S := sort (fun (a b : real) => b <= a) (map f P).
have hsX : sorted (fun (a b : real) => b <= a) X by apply sort_sorted; smt().
have hsS : sorted (fun (a b : real) => b <= a) S by apply sort_sorted; smt().
have hIP : size I <= size P.
- have := uniq_leq_size I (undup P) hu _; 1: by move=> x hx; rewrite mem_undup; apply hsub.
  smt(size_undup).
have hcnt : forall (v : real), count (fun x => v <= x) (map f I) <= count (fun x => v <= x) (map f P).
- move=> v; rewrite !count_map -!size_filter.
  apply (IntOrder.ler_trans (size (undup (filter (preim f (fun x => v <= x)) P)))); 2: exact (size_undup _).
  apply uniq_leq_size; 1: by apply filter_uniq.
  by move=> x; rewrite mem_undup !mem_filter => -[-> /hsub ->].
(* entry by entry, X is below S *)
have hle : forall i, 0 <= i < size I => nth 0%r X i <= nth 0%r S i.
- move=> i hi; apply sorted_count => //; 1: by rewrite /S size_sort size_map; smt().
  have /perm_eqP hSP := perm_sort (fun (a b : real) => b <= a) (map f P).
  rewrite /S hSP.
  apply (IntOrder.ler_trans (count (fun x => nth 0%r X i <= x) (map f I))); 2: exact hcnt.
  have /perm_eqP hXI := perm_sort (fun (a b : real) => b <= a) (map f I).
  rewrite -hXI -/X.
  have hsz : size X = size I by rewrite /X size_sort size_map.
  have hv : forall t, 0 <= t <= i => nth 0%r X i <= nth 0%r X t.
  + by move=> t ht; apply (sorted_nth (fun (a b : real) => b <= a) X 0%r t i); smt().
  pose v := nth 0%r X i.
  rewrite -(mkseq_nth 0%r X) /mkseq count_map.
  apply (IntOrder.ler_trans (count (fun t => t <= i) (iota_ 0 (size X)))).
  + rewrite -size_filter; apply (IntOrder.ler_trans (size (iota_ 0 (i + 1)))); 1: smt(size_iota).
    apply uniq_leq_size; 1: by apply iota_uniq.
    by move=> t; rewrite mem_filter !mem_iota /X size_sort size_map /#.
  apply count_mono => t /mem_iota ht /= hti.
  by rewrite /preim /v; apply hv; smt().
have -> : big predT f I = big predT idfun X.
- by rewrite /X (eq_big_perm _ _ _ _ (perm_sort _ _)) big_map.
rewrite (big_nth 0%r) /X size_sort size_map -/X.
apply (ler_trans (bigi predT (fun i => nth 0%r S i) 0 (size I))).
- by apply Bigreal.ler_sum_seq => i /mem_range hi _ /=; apply hle.
rewrite (big_nth 0%r _ _ (take n S)) size_take; 1: smt(size_ge0).
have hS0 : forall i, 0 <= i => 0%r <= nth 0%r S i.
- move=> i hi; case: (i < size S) => his; 2: by rewrite nth_default; smt().
  have : nth 0%r S i \in map f P by rewrite -(mem_sort (fun (a b : real) => b <= a)); apply mem_nth.
  by move/mapP => [x [hx ->]]; apply hpos.
rewrite (_ : (if n < size S then n else size S) = min n (size S)) 1:/#.
apply (ler_trans (bigi predT (fun i => nth 0%r S i) 0 (min n (size S)))).
- have hsz : size S = size P by rewrite /S size_sort size_map.
  rewrite (big_cat_int (size I) 0 (min n (size S))); 1,2: by rewrite ?hsz; smt(size_ge0).
  by rewrite ler_addl; apply Bigreal.sumr_ge0_seq => i /mem_range hi _ /=; apply hS0; smt(size_ge0).
by apply lerr_eq; apply eq_big_int => i hi /=; rewrite nth_take //; smt().
qed.

lemma sorted_map ['a 'b] (f : 'a -> 'b) (e : 'b -> 'b -> bool) (s : 'a list) :
  sorted (fun x y => e (f x) (f y)) s => sorted e (map f s).
proof. by case: s => //= x s; elim: s x => //= y s ih x [-> /ih]. qed.

(* Conversely, the n largest values of map f P are the values of at most n elements of P. *)
lemma top_sum_ex (f : 'a -> real) (P : 'a list) n : uniq P => 0 <= n =>
  exists I, uniq I /\ (forall x, x \in I => x \in P) /\ size I <= n /\
    big predT idfun (take n (sort (fun (a b : real) => b <= a) (map f P))) = big predT f I.
proof.
move=> hu hn; pose X := sort (fun x y => f y <= f x) P.
exists (take n X); split; 1: by apply uniq_take; rewrite /X sort_uniq.
split; 1: by move=> x /mem_take; rewrite /X mem_sort.
split; 1: by rewrite size_take //; smt().
have -> : sort (fun (a b : real) => b <= a) (map f P) = map f X.
- apply (eq_sorted (fun (a b : real) => b <= a)); 1,2: smt().
  + by apply sort_sorted; smt().
  + by apply sorted_map; apply sort_sorted; smt().
  apply (perm_eq_trans (map f P)); 1: exact perm_sort.
  by rewrite perm_eq_sym; apply perm_eq_map; exact perm_sort.
by rewrite -map_take big_map.
qed.

(* The k-th of distinct passwords sorted by decreasing probability has probability at most p_(k+1). *)
lemma pr_sorted (U : pw list) k : uniq U => sorted (fun (u w : pw) => mu1 dP w <= mu1 dP u) U =>
  0 <= k < size U => mu1 dP (nth witness U k) <= pr (k + 1).
proof.
move=> hu hs hk; case: (mu1 dP (nth witness U k) <= pr (k + 1)) => // /ltrNge hlt.
have hfirst : forall t, 0 <= t <= k => mu1 dP (nth witness U k) <= mu1 dP (nth witness U t).
- by move=> t ht; apply (sorted_nth (fun (u w : pw) => mu1 dP w <= mu1 dP u) U witness t k) => //; smt().
have hidx : forall t, 0 <= t <= k => index (nth witness U t) ranked < k.
- move=> t ht; case: (index (nth witness U t) ranked < k) => // /IntOrder.lerNgt hge.
  have := pr_mono (k + 1) (index (nth witness U t) ranked + 1) _; 1: smt().
  by rewrite pr_index; have := hfirst t ht; smt().
have := uniq_leq_size (map (fun t => index (nth witness U t) ranked) (iota_ 0 (k + 1))) (iota_ 0 k) _ _.
- rewrite map_inj_in_uniq ?iota_uniq // => i j /mem_iota hi /mem_iota hj /= heq.
  have e : nth witness U i = nth witness U j.
  + by rewrite -(nth_index witness (nth witness U i) ranked) ?rankedP // heq nth_index // rankedP.
  case: (i = j) => // hne; move/(nth_uniqP U) : hu => h.
  by have := h i j _ _ hne; smt().
- by move=> x /mapP [t [/mem_iota ht ->]]; rewrite mem_iota; smt(index_ge0).
by rewrite size_map !size_iota; smt().
qed.

lemma sr_index (v : pp) : sr (index v rankedQ + 1) = mu1 dQ v.
proof.
have hv : v \in rankedQ by rewrite /rankedQ mem_sort PpT.enumP.
rewrite /sr (_ : 1 <= index v rankedQ + 1 <= size rankedQ) /=; 1: smt(index_ge0 index_mem).
by rewrite nth_index.
qed.

lemma allpairs_mapE ['a 'b 'c] (f : 'a -> 'b -> 'c) s t :
  allpairs f s t = map (fun (x : 'a * 'b) => f x.`1 x.`2) (allpairs (fun a b => (a, b)) s t).
proof. by elim: s => [|x s ih]; rewrite ?allpairs0l // !allpairs_consl ih map_cat -map_comp. qed.

(* Lemma W1. *)
lemma W1 (ps : (pw * pp) list) (m n : int) :
  uniq ps => size ps <= n => size (undup (map fst ps)) <= m => mass2 ps <= top2 m n.
proof.
move=> hu hn hm.
pose U := sort (fun (u w : pw) => mu1 dP w <= mu1 dP u) (undup (map fst ps)).
have hUu : uniq U by rewrite /U sort_uniq undup_uniq.
have hUs : sorted (fun (u w : pw) => mu1 dP w <= mu1 dP u) U by apply sort_sorted; smt().
have hUm : forall (x : pw * pp), x \in ps => x.`1 \in U.
- by move=> x hx; rewrite /U mem_sort mem_undup mapP; exists x.
pose I := map (fun (x : pw * pp) => (index x.`1 U + 1, index x.`2 rankedQ + 1)) ps.
pose P := allpairs (fun i j => (i, j)) (iota_ 1 m) (iota_ 1 (size rankedQ)).
have -> : top2 m n = big predT idfun (take n (sort (fun (a b : real) => b <= a)
                       (map (fun (y : int * int) => pr y.`1 * sr y.`2) P))).
- by rewrite /top2 /P allpairs_mapE.
apply (ler_trans (big predT (fun (y : int * int) => pr y.`1 * sr y.`2) I)).
- rewrite /mass2 /I big_map; apply Bigreal.ler_sum_seq => x hx _; rewrite /(\o) /= sr_index.
  have h1 : mu1 dP x.`1 <= pr (index x.`1 U + 1).
  + have := pr_sorted U (index x.`1 U) hUu hUs _; 1: smt(index_ge0 index_mem).
    by rewrite nth_index // hUm.
  by apply ler_wpmul2r; [apply ge0_mu | exact h1].
apply top_sum.
- rewrite map_inj_in_uniq // => x y hx hy /= [h1 h2].
  have e1 : x.`1 = y.`1 by rewrite -(nth_index witness x.`1 U) 1:hUm // -(nth_index witness y.`1 U) 1:hUm // /#.
  have hq : forall (v : pp), v \in rankedQ by move=> v; rewrite /rankedQ mem_sort PpT.enumP.
  have e2 : x.`2 = y.`2 by rewrite -(nth_index witness x.`2 rankedQ) 1:hq -(nth_index witness y.`2 rankedQ) 1:hq /#.
  by rewrite (pairS x) (pairS y) e1 e2.
- move=> y /mapP [x [hx ->]]; rewrite /P allpairsP; exists (index x.`1 U + 1, index x.`2 rankedQ + 1) => /=.
  rewrite !mem_iota; have := hUm x hx; have : x.`2 \in rankedQ by rewrite /rankedQ mem_sort PpT.enumP.
  smt(index_ge0 index_mem size_sort size_undup).
- by rewrite /I size_map.
by move=> y _ /=; apply mulr_ge0; [apply pr_ge0 | rewrite /sr; smt(ge0_mu)].
qed.

(* ---- The generation of the source ------------------------------------------------------------ *)
(* A selection rule sees only the order of the trials and their outcomes, and selects one by its
   index; it may use its own coins. *)
module type TRIALS = { proc trial() : bool }.
module type RULE (T : TRIALS) = { proc select() : int }.

(* A trial: a uniform e, checked through S and T at the passphrase q. *)
module Trials = {
  var q    : pp
  var vals : state list
  var outs : bool list
  proc trial() : bool = {
    var e, d, c;
    e <$ dstate;
    d <@ RS.RO.get(e, q);
    c <@ RT.RO.get(d);
    vals <- rcons vals e;
    outs <- rcons outs (c.`1 = zero16);
    return c.`1 = zero16;
  }
}.

(* The sequential rule of the specification: repeat until a trial passes. A run past ntr = 2^80
   trials, which the text gives any outcome (Lemma W2), stops at its last trial. *)
op ntr : int = 2 ^ 80.

module Seq (T : TRIALS) = {
  proc select() : int = {
    var ok, i;
    ok <- false;
    i <- -1;
    while (!ok /\ i + 1 < ntr) { ok <@ T.trial(); i <- i + 1; }
    return i;
  }
}.

(* The secrets: the password, the passphrase, the entropy E and seed* = S(E, Q). *)
module Gen = {
  var p  : pw
  var q  : pp
  var e  : state
  var sd : seed
}.

(* Θ0: the source is generated by the rule, Y = Perm_P(E) and omega* = Omega(seed* ). *)
module Setup0P (Rl : RULE) = {
  proc run() : state * data = {
    var i, y, om;
    R.RO.init(); RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Trials.q <- Gen.q; Trials.vals <- []; Trials.outs <- [];
    i <@ Rl(Trials).select();
    Gen.e <- nth witness Trials.vals i;
    Gen.sd <@ RS.RO.get(Gen.e, Gen.q);
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    return (y, om);
  }
}.

(* Θ0': E, seed* and the rest eta* of the check value are uniform and programmed. *)
module Setup0P' = {
  proc run() : state * data = {
    var et, y, om;
    R.RO.init(); RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Gen.e <$ dstate;
    Gen.sd <$ dseed;
    et <$ W240.DWord.dunifin;
    RS.RO.set((Gen.e, Gen.q), Gen.sd);
    RT.RO.set(Gen.sd, (zero16, et));
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    return (y, om);
  }
}.

(* Θ1: Y, omega* and seed* are uniform; S, T, Omega are programmed at e* = Inv_P(Y) and seed*. *)
module Setup1P = {
  proc run() : state * data = {
    var y, om, et;
    R.RO.init(); RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    y <$ dstate;
    om <$ ddata;
    Gen.sd <$ dseed;
    Gen.e <@ Net(Ideal).dec(Gen.p, y);
    RS.RO.set((Gen.e, Gen.q), Gen.sd);
    et <$ W240.DWord.dunifin;
    RT.RO.set(Gen.sd, (zero16, et));
    RW.RO.set(Gen.sd, om);
    return (y, om);
  }
}.

(* Θ2: nothing is programmed; seed* and omega* are independent and uniform. *)
module Setup2P = {
  proc run() : state * data = {
    var y, om;
    R.RO.init(); RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    y <$ dstate;
    om <$ ddata;
    Gen.sd <$ dseed;
    Gen.e <@ Net(Ideal).dec(Gen.p, y);
    return (y, om);
  }
}.

(* Θ1 for an ordinary source (Corollary W6): as Θ1 without the programmed check value. *)
module Setup1O = {
  proc run() : state * data = {
    var y, om;
    R.RO.init(); RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    y <$ dstate;
    om <$ ddata;
    Gen.sd <$ dseed;
    Gen.e <@ Net(Ideal).dec(Gen.p, y);
    RS.RO.set((Gen.e, Gen.q), Gen.sd);
    RW.RO.set(Gen.sd, om);
    return (y, om);
  }
}.

module type SETUPP = { proc run() : state * data }.

(* The game on a challenger, without refusal. It returns the adversary's output; the seed game is
   won if sigma = seed*, the pair game if the output pair is (P, Q). *)
module GameP (S : SETUPP) (A : AdvP) = {
  proc main() : seed * (pw * pp) = {
    var y, om, out;
    (y, om) <@ S.run();
    CountP(IP).init();
    out <@ A(CountP(IP)).guess(y, om);
    return out;
  }
}.

(* With the creation refusal of Remark G9: if Y = E the continuation is arbitrary. *)
module type AFTERP = { proc run(p : pw, q : pp, y : state) : seed * (pw * pp) }.

module GamePR (S : SETUPP) (A : AdvP) (Rf : AFTERP) = {
  proc main() : seed * (pw * pp) = {
    var y, om, out;
    (y, om) <@ S.run();
    if (y = Gen.e) {
      out <@ Rf.run(Gen.p, Gen.q, y);
    } else {
      CountP(IP).init();
      out <@ A(CountP(IP)).guess(y, om);
    }
    return out;
  }
}.

(* ---- Lemmas W2 and W3: the adversary's view and the secrets --------------------------------- *)
(* A two-phase adversary: it runs, then judges with the secrets; the judge may still read A, B, H
   and Omega, so its result can be any event of the secrets, those functions and the view. *)
module type ADVJ (O : OraclesP) = {
  proc run(y : state, om : data) : unit
  proc judge(p : pw, q : pp, e : state, sd : seed) : bool { O.a, O.b, O.h, O.w }
}.

module Judged (S : SETUPP) (J : ADVJ) = {
  proc main() : bool = {
    var y, om, b;
    (y, om) <@ S.run();
    CountP(IP).init();
    J(CountP(IP)).run(y, om);
    b <@ J(CountP(IP)).judge(Gen.p, Gen.q, Gen.e, Gen.sd);
    return b;
  }
}.
