(* Lemma W2 (the generation by rejection against one programmed point), Lemma W3 (Θ0' and Θ1)
   and the creation refusal of Θ0 (DESIGN-NOTES A.6). *)
require import AllCore List Distr DBool DProd FMap IntDiv StdBigop StdOrder Xreal.
require import Suite3 Chain Collision Passphrase.
require (*--*) BitWord FinType PROM.
import W128 StdBigop.Bigreal.BRA RealOrder.

(* ---- The cutoff of the sequential rule ------------------------------------------------------ *)
lemma bernoulli (x : real) (n : int) : 0%r <= x => 0 <= n => 1%r + n%r * x <= (1%r + x) ^ n.
proof.
move=> hx; elim: n => [|n hn ih]; 1: by rewrite RField.expr0.
rewrite RField.exprS //.
have h1 : 0%r <= 1%r + x by smt().
have h2 : (1%r + x) * (1%r + n%r * x) <= (1%r + x) * (1%r + x) ^ n by apply ler_wpmul2l.
have h3 : 0%r <= n%r * x * x by apply mulr_ge0; [apply mulr_ge0; smt() | exact hx].
smt().
qed.

lemma half_pow (k : int) : 0 <= k => (1%r - inv (2%r ^ k)) ^ (2 ^ k) <= inv 2%r.
proof.
move=> hk; pose p := inv (2%r ^ k).
have hp0 : 0%r < p by rewrite /p invr_gt0 expr_gt0.
have hp1 : p <= 1%r by rewrite /p invr_le1; smt(expr_gt0 exprn_ege1).
have hb := bernoulli p (2 ^ k) _ _; [smt() | by apply IntOrder.expr_ge0 | ].
have h2c : (2 ^ k)%r = 2%r ^ k by smt(RField.fromintXn).
have hn : (2 ^ k)%r * p = 1%r by rewrite /p h2c RField.mulrV //; smt(expr_gt0).
have h2 : (1%r - p) ^ (2 ^ k) * (1%r + p) ^ (2 ^ k) <= 1%r.
- rewrite -RField.exprMn; 1: by apply IntOrder.expr_ge0.
  by apply exprn_ile1; [apply IntOrder.expr_ge0 | split; smt()].
have h4 : 0%r <= (1%r - p) ^ (2 ^ k) by apply expr_ge0; smt().
have h3 : 2%r <= (1%r + p) ^ (2 ^ k) by smt().
have h5 : (1%r - p) ^ (2 ^ k) * 2%r <= (1%r - p) ^ (2 ^ k) * (1%r + p) ^ (2 ^ k) by apply ler_wpmul2l.
smt().
qed.

lemma inv16_le1 : inv (2%r ^ 16) <= 1%r.
proof. by rewrite invr_le1; [smt(expr_gt0) | smt(expr_gt0) | apply exprn_ege1]. qed.

lemma pow2_8 : 2 ^ 8 = 256.
proof. by rewrite (_ : 8 = 2 * (2 * 2)) // !Ring.IntID.exprM !Ring.IntID.expr2. qed.

lemma pow2_64_ge : 256 <= 2 ^ 64.
proof. by rewrite -pow2_8; apply IntOrder.ler_weexpn2l. qed.

(* Past ntr = 2^80 trials the rule is cut off; that happens with probability below 2^-256. *)
lemma pcut_bound : (1%r - inv (2%r ^ 16)) ^ ntr <= inv (2%r ^ 256).
proof.
have -> : ntr = 2 ^ 16 * 2 ^ 64 by rewrite /ntr -Ring.IntID.exprD_nneg.
rewrite RField.exprM.
apply (ler_trans ((inv 2%r) ^ (2 ^ 64))).
- apply ler_pexp; 1: by apply IntOrder.expr_ge0.
  by split; [apply expr_ge0; smt(inv16_le1) | move=> _; apply (half_pow 16)].
apply (ler_trans ((inv 2%r) ^ 256)).
- by apply ler_wiexpn2l; [smt() | smt(pow2_64_ge)].
by rewrite RField.exprVn.
qed.

lemma pcut17 : (1%r - inv (2%r ^ 17)) ^ ntr <= inv (2%r ^ 256).
proof.
have -> : ntr = 2 ^ 17 * 2 ^ 63 by rewrite /ntr -Ring.IntID.exprD_nneg.
rewrite RField.exprM.
apply (ler_trans ((inv 2%r) ^ (2 ^ 63))).
- apply ler_pexp; 1: by apply IntOrder.expr_ge0.
  split; 2: by move=> _; apply (half_pow 17).
  by apply expr_ge0; rewrite subr_ge0 invr_le1; smt(expr_gt0 exprn_ege1).
apply (ler_trans ((inv 2%r) ^ 256)).
- apply ler_wiexpn2l; 1: smt().
  by split => // _; rewrite -pow2_8; apply IntOrder.ler_weexpn2l.
by rewrite RField.exprVn.
qed.

(* ---- The potential of the trial loop ---------------------------------------------------------- *)
op pk : real = inv (2%r ^ 16).
op Kc (kS qT : int) : real = (1 + kS)%r * inv (2%r ^ 256) + (1 + qT)%r * inv (2%r ^ 512).

lemma pk_gt0 : 0%r < pk by rewrite /pk invr_gt0 expr_gt0.
lemma pk_lt1 : pk < 1%r.
proof.
have h16 : 2%r <= 2%r ^ 16 by rewrite -{1}RField.expr1; apply ler_weexpn2l.
by rewrite /pk invr_lt1; smt(expr_gt0).
qed.

lemma Kc_ge0 kS qT : 0 <= kS => 0 <= qT => 0%r <= Kc kS qT.
proof. by move=> hk hq; rewrite /Kc; smt(expr_gt0 invr_gt0). qed.

(* Before the trial with index i + 1, with ok the outcome of the last trial: the expected number of
   rejected trials, times K, plus the probability of the cutoff. *)
op phiL (K : real) (ok : bool) (i : int) : real =
  if ok then i%r * K
  else if i + 1 < ntr then (i + 1)%r * K + (1%r - pk) / pk * K + (1%r - pk) ^ (ntr - (i + 1))
  else 1%r + i%r * K.

lemma ntr_gt0 : 0 < ntr by rewrite /ntr; apply IntOrder.expr_gt0.

lemma phiL_ge0 K ok i : 0%r <= K => -1 <= i => (ok => 0 <= i) => 0%r <= phiL K ok i.
proof.
move=> hK hi hok; rewrite /phiL; have h0 := pk_gt0; have h1 := pk_lt1; have hn0 := ntr_gt0.
case: ok hok => [hi0 | _] /=; 1: by apply mulr_ge0 => //; smt().
case: (i + 1 < ntr) => hn /=.
- have : 0%r <= (1%r - pk) ^ (ntr - (i + 1)) by apply expr_ge0; smt().
  have : 0%r <= (1%r - pk) / pk * K by apply mulr_ge0; [apply divr_ge0; smt() | exact hK].
  have : 0%r <= (i + 1)%r * K by apply mulr_ge0; smt().
  smt().
have : 0%r <= i%r * K by apply mulr_ge0; smt().
smt().
qed.

lemma phiL_mono K i : 0%r <= K => -1 <= i => i + 1 < ntr => phiL K true (i + 1) <= phiL K false (i + 1).
proof.
move=> hK hi hn; rewrite /phiL /=; have h0 := pk_gt0; have h1 := pk_lt1.
case: (i + 1 + 1 < ntr) => hn2 /=.
- have : 0%r <= (1%r - pk) ^ (ntr - (i + 1 + 1)) by apply expr_ge0; smt().
  have : 0%r <= (1%r - pk) / pk * K by apply mulr_ge0; [apply divr_ge0; smt() | exact hK].
  rewrite !fromintD; smt().
smt().
qed.

(* One trial: it passes with probability pk. *)
lemma phiL_step K i : 0%r <= K => -1 <= i => i + 1 < ntr =>
  pk * phiL K true (i + 1) + (1%r - pk) * phiL K false (i + 1) <= phiL K false i.
proof.
move=> hK hi hn; have h0 := pk_gt0; have h1 := pk_lt1.
rewrite /phiL /= hn /=.
case: (i + 2 < ntr) => hn2 /=.
- rewrite (_ : ntr - (i + 1) = (ntr - (i + 2)) + 1) 1:/# RField.exprS 1:/#.
  apply lerr_eq; rewrite !fromintD; field; smt().
have hn1 : ntr - (i + 1) = 1 by smt().
rewrite hn1 RField.expr1.
have : 0%r <= (1%r - pk) / pk * K by apply mulr_ge0; [apply divr_ge0; smt() | exact hK].
rewrite !fromintD; smt().
qed.

(* A two-valued expectation. *)
lemma Ep_two ['a] (d : 'a distr) (Q : 'a -> bool) (A B : real) : is_lossless d => 0%r <= A <= B =>
  Ep d (fun x => (if Q x then A else B)%xr) = (mu d Q * A + (1%r - mu d Q) * B)%xr.
proof.
move=> hd [hA hAB].
rewrite (eq_Ep _ _ (fun x => (A + (B - A) * b2r (!Q x))%xr)) => [x _ /= | ].
- by case: (Q x) => _ /=; smt().
rewrite (Ep_cbs d A (B - A) (fun x => !Q x)) // 1:/#.
have -> : mu d (fun x => !Q x) = 1%r - mu d Q by rewrite mu_not hd.
by have -> : A + (B - A) * (1%r - mu d Q) = mu d Q * A + (1%r - mu d Q) * B by ring.
qed.

lemma dW16_zero : mu W16.DWord.dunifin (fun r => r = zero16) = pk.
proof.
have -> : (fun r => r = zero16) = pred1 zero16 by apply fun_ext => r; rewrite /pred1.
by rewrite W16.DWord.dunifin1E W16.word_card /pk /=; smt(RField.fromintXn).
qed.

(* The rejected trials: all but the last. *)
op rejS (es : state list) (q : pp) : (state * pp) list = map (fun e => (e, q)) (take (size es - 1) es).
op rejT (r1s : seed list) : seed list = take (size r1s - 1) r1s.

(* Bad of the reduced game: a collision of the passing trial, the cutoff, or a query of the adversary
   at a rejected trial point. *)
op badB (bad : bool) (es : state list) (r1s : seed list) (q : pp) (ls : (state * pp) list) (lt : seed list) =
  bad \/ has (fun x => x \in rejS es q) ls \/ has (fun x => x \in rejT r1s) lt.

(* The same event read from the trial values by index. *)
op badI (es : state list) (r1s : seed list) (e : state) (sd : seed) (q : pp) (ls : (state * pp) list)
        (lt : seed list) (n : int) =
  exists k, 0 <= k < n /\
    (nth witness es k = e \/ nth witness r1s k = sd \/ (nth witness es k, q) \in ls \/ nth witness r1s k \in lt).

lemma take_rcons_size (s : 'a list) x : take (size s) (rcons s x) = s.
proof. by rewrite -cats1 take_size_cat. qed.

lemma has_rcons (p : 'a -> bool) s x : has p (rcons s x) <=> has p s \/ p x.
proof. by rewrite -cats1 has_cat /=. qed.

lemma mu_const_true ['a] (d : 'a distr) (b : bool) : is_lossless d => b => mu d (fun _ => b) = 1%r.
proof. by move=> hd hb; rewrite hb; apply hd. qed.

lemma mem_take_last (s : 'a list) x : x \in s => x \in take (size s - 1) s \/ x = last witness s.
proof.
elim/last_ind: s => // s y _; rewrite mem_rcons size_rcons /= last_rcons take_rcons_size.
by case=> [-> | h]; [right | left].
qed.

lemma mem_take_nth (s : 'a list) n x : 0 <= n <= size s =>
  (x \in take n s) <=> exists k, 0 <= k < n /\ nth witness s k = x.
proof.
move=> hn; split.
- move=> hx; exists (index x (take n s)).
  have hi : index x (take n s) < size (take n s) by rewrite index_mem.
  have hs : size (take n s) = n by rewrite size_take; smt().
  split; 1: smt(index_ge0).
  by rewrite -(nth_take witness n) 1,2:/# nth_index.
move=> [k [hk <-]]; rewrite -(nth_take witness n) 1,2:/#.
by apply mem_nth; rewrite size_take; smt().
qed.

lemma badB_badI bad es r1s q ls lt (n : int) :
  0 <= n => size es = n + 1 => size r1s = n + 1 =>
  badB (bad \/ last witness es \in take n es \/ last witness r1s \in take n r1s) es r1s q ls lt =
  (bad \/ badI es r1s (last witness es) (last witness r1s) q ls lt n).
proof.
move=> hn hes hr1; rewrite /badB /rejS /rejT hes hr1 /= /badI eq_iff.
have hle1 : 0 <= n <= size es by smt().
have hle2 : 0 <= n <= size r1s by smt().
split.
- case=> [[hb | [he | hr]] | [/List.hasP [x [hx /mapP [e [he hxe]]]] | /List.hasP [x [hx hr]]]]; 1: by left.
  + move/(mem_take_nth es n _ hle1): he => [k [hk he]]; right; exists k; smt().
  + move/(mem_take_nth r1s n _ hle2): hr => [k [hk hr]]; right; exists k; smt().
  + move/(mem_take_nth es n _ hle1): he => [k [hk he]]; right; exists k; smt().
  move/(mem_take_nth r1s n _ hle2): hr => [k [hk hr]]; right; exists k; smt().
case=> [hb | [k [hk [he | [hr | [hs | ht]]]]]]; 1: by left; left.
- by left; right; left; apply (mem_take_nth es n _ hle1); exists k.
- by left; right; right; apply (mem_take_nth r1s n _ hle2); exists k.
- right; left; apply/List.hasP; exists (nth witness es k, q); split => //.
  by apply/mapP; exists (nth witness es k); split => //; apply (mem_take_nth es n _ hle1); exists k.
right; right; apply/List.hasP; exists (nth witness r1s k); split => //.
by apply (mem_take_nth r1s n _ hle2); exists k.
qed.

op deltagen (kS qT : int) : real = 2%r ^ 18 * (kS + 1)%r / 2%r ^ 256 + 2%r ^ 18 * qT%r / 2%r ^ 512.

lemma deltagen_mono (k k' t t' : int) : k <= k' => t <= t' => deltagen k t <= deltagen k' t'.
proof.
move=> hk ht; rewrite /deltagen; apply ler_add; (apply ler_wpmul2r; 1: smt(expr_gt0 invr_gt0));
  by apply ler_wpmul2l; [smt(expr_gt0) | smt()].
qed.

(* The distance that the proof of Lemma W2 gives for the rule cut off after ntr trials; it leaves
   room below delta_gen for the transfer to every covered rule (Selection.ec). *)
op deltacut (kS qT : int) : real = 2%r * (2%r ^ 16 * Kc kS qT + inv (2%r ^ 256)).

lemma deltacut_le (kS qT : int) : 0 <= kS => 0 <= qT =>
  deltacut kS qT + 2%r * inv (2%r ^ 256) <= deltagen kS qT.
proof.
move=> hkS hqT; rewrite /deltacut /Kc /deltagen.
pose a := inv (2%r ^ 256); pose b := inv (2%r ^ 512); pose c := 2%r ^ 16.
have ha : 0%r <= a by rewrite /a; smt(expr_gt0 invr_gt0).
have hb0 : 0%r <= b by rewrite /b; smt(expr_gt0 invr_gt0).
have hc4 : 4%r <= c.
- by rewrite /c (_ : 4%r = 2%r ^ 2) 1:RField.expr2 //; apply ler_weexpn2l.
have e18 : 2%r ^ 18 = 4%r * c.
- by rewrite /c (_ : 18 = 2 + 16) // RField.exprD_nneg // RField.expr2; smt().
have hab : 2%r * c * b <= a.
- have -> : 2%r * c * b = inv (2%r ^ 495).
  + rewrite /b /c (_ : 512 = 17 + 495) // RField.exprD_nneg // RField.invfM.
    by rewrite (_ : 17 = 1 + 16) // RField.exprD_nneg // RField.expr1; field; smt(expr_gt0).
  by rewrite /a lef_pinv; [smt(expr_gt0) | smt(expr_gt0) | apply ler_weexpn2l].
have p1 : 0%r <= c * kS%r * a by apply mulr_ge0; [apply mulr_ge0; smt() | exact ha].
have p2 : 0%r <= c * qT%r * b by apply mulr_ge0; [apply mulr_ge0; smt() | exact hb0].
have p3 : 4%r * a <= c * a by apply ler_wpmul2r.
rewrite e18; smt().
qed.

(* The tables of the real game agree with the reduced game's off the rejected points. *)
op agree (m1 m2 : ('a, 'b) fmap) (rej : 'a list) = forall x, !(x \in rej) => m1.[x] = m2.[x].

(* The invariant of the trial loops while no bad event happened. *)
op invT (q : pp) (ms : (state * pp, seed) fmap) (mt : (seed, W16.word * W240.word) fmap)
        (es : state list) (r1s : seed list) (ok1 : bool) =
  (forall x, x \in ms => x.`2 = q /\ x.`1 \in es) /\
  (forall x, x \in mt => x \in r1s) /\
  (forall x, x \in ms => oget ms.[x] \in mt) /\
  (!ok1 => forall x, x \in mt => (oget mt.[x]).`1 <> zero16).

(* One real trial while no trial has passed: the tables grow by the fresh points only, and the real
   check agrees with the ideal one unless the passing trial repeats a point. *)
lemma invT_step q (ms : (state * pp, seed) fmap) (mt : (seed, W16.word * W240.word) fmap) es r1s e r1 r21 r22 :
  invT q ms mt es r1s false =>
  let ms' = if (e, q) \notin ms then ms.[(e, q) <- r1] else ms in
  let mt' = if oget ms'.[(e, q)] \notin mt then mt.[oget ms'.[(e, q)] <- (r21, r22)] else mt in
  let ok' = (oget mt'.[oget ms'.[(e, q)]]).`1 = zero16 in
  invT q ms' mt' (rcons es e) (rcons r1s r1) ok' /\
  (!(r21 = zero16 /\ (e \in es \/ r1 \in r1s)) => ok' = (r21 = zero16)) /\
  (r21 = zero16 /\ !(e \in es \/ r1 \in r1s) => ms'.[(e, q)] = Some r1 /\ mt'.[r1] = Some (r21, r22)).
proof.
move=> [hS [hT [hST hF]]] /=.
have hF' := hF _; 1: by [].
case: ((e, q) \in ms) => hes /=.
- have hd : oget ms.[(e, q)] \in mt by apply hST.
  have he : e \in es by have := hS _ hes.
  have hc := hF' _ hd.
  rewrite hd /= /invT; split; 2: smt().
  do !split; 1,2: smt(mem_rcons).
  + exact hST.
  by move=> _; exact hF'.
rewrite get_set_sameE /=.
case: (r1 \in mt) => hr /=.
- have hc := hF' _ hr; have hr1 : r1 \in r1s by apply hT.
  rewrite /invT; split; 2: smt().
  do !split.
  + by move=> x; rewrite mem_set => -[hx | ->]; smt(mem_rcons).
  + smt(mem_rcons).
  + by move=> x; rewrite mem_set get_setE => -[hx | ->] /=; smt().
  by move=> _; exact hF'.
rewrite /invT !get_set_sameE /=.
do !split.
- by move=> x; rewrite mem_set => -[hx | ->]; smt(mem_rcons).
- by move=> x; rewrite mem_set => -[hx | ->]; smt(mem_rcons).
- by move=> x; rewrite !mem_set !get_setE => -[hx | ->] /=; smt().
move=> hnp x; rewrite mem_set get_setE => -[hx | ->] /=; smt().
qed.

section W2.
declare op kS : int.
declare op qT : int.
declare module J <: ADVJ {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                          -Gen, -Trials, -Count, -CountP}.
declare axiom J_bounded (O <: OraclesP {-Count, -CountP, -J}) :
  hoare [J(CountP(O)).run :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    CountP.cs <= kS /\ CountP.ct <= qT].
(* The judge sees only A, B, H and W, so its termination needs only theirs. *)
declare axiom J_ll (O <: OraclesP {-J}) :
  (islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
   islossless O.w => islossless J(O).run) /\
  (islossless O.a => islossless O.b => islossless O.h => islossless O.w => islossless J(O).judge).

(* ---- Step 1: the real generation with ghost copies of its samples ------------------------------ *)
local module RSs = {
  var l1 : seed
  proc get(x : state * pp) : seed = {
    var r;
    r <$ dseed;
    l1 <- r;
    if (x \notin RS.RO.m) RS.RO.m.[x] <- r;
    return oget RS.RO.m.[x];
  }
}.

local module RTs = {
  var l21 : W16.word
  proc get(x : seed) : W16.word * W240.word = {
    var r21, r22;
    r21 <$ W16.DWord.dunifin;
    r22 <$ W240.DWord.dunifin;
    l21 <- r21;
    if (x \notin RT.RO.m) RT.RO.m.[x] <- (r21, r22);
    return oget RT.RO.m.[x];
  }
}.

local clone DProd.ProdSampling as PSc with type t1 <- W16.word, type t2 <- W240.word.

local equiv rs_eq : RS.RO.get ~ RSs.get : ={arg, RS.RO.m} ==> ={res, RS.RO.m}.
proof. by proc; auto. qed.

local equiv rt_eq : RT.RO.get ~ RTs.get : ={arg, RT.RO.m} ==> ={res, RT.RO.m}.
proof.
proc; outline {2} [1 .. 2] ~ PSc.S.sample2.
rewrite equiv[{2} 1 -PSc.sample_sample2].
by inline PSc.S.sample; auto => />; smt().
qed.

(* bad: the ideal check of a trial passes while its point repeats an earlier one. *)
local module R0T = {
  var bad : bool
  var es : state list
  var r1s : seed list
  proc trial() : bool = {
    var e, d, c;
    e <$ dstate;
    d <@ RSs.get(e, Trials.q);
    c <@ RTs.get(d);
    Trials.vals <- rcons Trials.vals e;
    Trials.outs <- rcons Trials.outs (c.`1 = zero16);
    bad <- bad \/ (RTs.l21 = zero16 /\ (e \in es \/ RSs.l1 \in r1s));
    es <- rcons es e;
    r1s <- rcons r1s RSs.l1;
    return c.`1 = zero16;
  }
}.

local equiv trial_eq : Trials.trial ~ R0T.trial :
  ={Trials.q, Trials.vals, Trials.outs, RS.RO.m, RT.RO.m} ==>
  ={res, Trials.q, Trials.vals, Trials.outs, RS.RO.m, RT.RO.m}.
proof. by proc; wp; call rt_eq; call rs_eq; auto. qed.

local module R0 = {
  proc main() : bool = {
    var isel, y, om, b;
    R.RO.init(); RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Trials.q <- Gen.q; Trials.vals <- []; Trials.outs <- [];
    R0T.bad <- false; R0T.es <- []; R0T.r1s <- [];
    isel <@ Seq(R0T).select();
    Gen.e <- nth witness Trials.vals isel;
    Gen.sd <@ RS.RO.get(Gen.e, Gen.q);
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    CountP(IP).init();
    J(CountP(IP)).run(y, om);
    b <@ J(CountP(IP)).judge(Gen.p, Gen.q, Gen.e, Gen.sd);
    return b;
  }
}.

local equiv real_R0 : Judged(Setup0P(Seq), J).main ~ R0.main : ={glob J} ==> ={res}.
proof.
proc; inline Setup0P(Seq).run.
call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); 1..4: by sim.
call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); 1..6: by sim.
inline CountP(IP).init Count(IP).init; wp.
call (_ : ={RW.RO.m}); 1: by sim.
call (_ : ={R.RO.m}); 1: by sim.
call (_ : ={RS.RO.m}); 1: by sim.
wp; call (_ : ={Trials.q, Trials.vals, Trials.outs, RS.RO.m, RT.RO.m}).
- by while (={ok, i, Trials.q, Trials.vals, Trials.outs, RS.RO.m, RT.RO.m}); [wp; call trial_eq | auto].
by inline *; auto.
qed.

(* ---- Step 2: the ideal control; only the passing trial is programmed -------------------------- *)
local module LogP = {
  var ls : (state * pp) list
  var lt : seed list
}.

(* The oracles of the reduced games record the adversary's S and T points. *)
local module IPL : OraclesP = {
  proc a = Ideal.a
  proc b = Ideal.b
  proc h = Ideal.h
  proc s(e : state, q : pp) = { var d; LogP.ls <- rcons LogP.ls (e, q); d <@ RS.RO.get(e, q); return d; }
  proc t(d : seed) = { var c; LogP.lt <- rcons LogP.lt d; c <@ RT.RO.get(d); return c; }
  proc w = IP.w
}.

local module G2 = {
  var bad : bool
  var es : state list
  var r1s : seed list
  var c2 : W16.word * W240.word
  proc main() : bool = {
    var ok, i, e, r1, r21, r22, y, om, b;
    R.RO.init(); RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    bad <- false; es <- []; r1s <- [];
    ok <- false; i <- -1;
    while (!ok /\ i + 1 < ntr) {
      e <$ dstate;
      r1 <$ dseed;
      r21 <$ W16.DWord.dunifin;
      r22 <$ W240.DWord.dunifin;
      bad <- bad \/ (r21 = zero16 /\ (e \in es \/ r1 \in r1s));
      es <- rcons es e;
      r1s <- rcons r1s r1;
      c2 <- (r21, r22);
      ok <- r21 = zero16;
      i <- i + 1;
    }
    bad <- bad \/ !ok;
    Gen.e <- last witness es;
    Gen.sd <- last witness r1s;
    RS.RO.m <- empty.[(Gen.e, Gen.q) <- Gen.sd];
    RT.RO.m <- empty.[Gen.sd <- c2];
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    LogP.ls <- []; LogP.lt <- [];
    CountP(IPL).init();
    J(CountP(IPL)).run(y, om);
    b <@ J(CountP(IPL)).judge(Gen.p, Gen.q, Gen.e, Gen.sd);
    return b;
  }
}.

local lemma ip_ll : islossless CountP(IP).a /\ islossless CountP(IP).b /\ islossless CountP(IP).h /\
  islossless CountP(IP).s /\ islossless CountP(IP).t /\ islossless CountP(IP).w.
proof. by do !split; proc; inline *; auto; smt(dans_ll dseed_ll dct_ll ddata_ll). qed.

local lemma ipl_ll : islossless CountP(IPL).a /\ islossless CountP(IPL).b /\ islossless CountP(IPL).h /\
  islossless CountP(IPL).s /\ islossless CountP(IPL).t /\ islossless CountP(IPL).w.
proof. by do !split; proc; inline *; auto; smt(dans_ll dseed_ll dct_ll ddata_ll). qed.

local lemma JP_ll : islossless J(CountP(IP)).run /\ islossless J(CountP(IP)).judge.
proof.
have [ha [hb [hh [hs [ht hw]]]]] := ip_ll; have [hr hj] := J_ll (CountP(IP)).
by split; [apply hr | apply hj].
qed.

local lemma JL_ll : islossless J(CountP(IPL)).run /\ islossless J(CountP(IPL)).judge.
proof.
have [ha [hb [hh [hs [ht hw]]]]] := ipl_ll; have [hr hj] := J_ll (CountP(IPL)).
by split; [apply hr | apply hj].
qed.

local lemma rs_ll : islossless RS.RO.get by proc; auto; smt(dseed_ll).
local lemma rw_ll : islossless RW.RO.get by proc; auto; smt(ddata_ll).
local lemma enc_ll : islossless Net(Ideal).enc.
proof. by proc; while true (12 - i); [move=> z; wp; inline *; auto; smt(dans_ll) | auto => /#]. qed.


(* ---- Step 3: the rejected values, read only after the adversary ------------------------------- *)
local clone PROM.FullRO as VE with
  type in_t <- int, type out_t <- state, op dout <- (fun _ => dstate),
  type d_in_t <- unit, type d_out_t <- bool * bool.
local clone PROM.FullRO as VR with
  type in_t <- int, type out_t <- seed, op dout <- (fun _ => dseed),
  type d_in_t <- unit, type d_out_t <- bool * bool.
local clone PROM.FullRO as VC with
  type in_t <- int, type out_t <- W240.word, op dout <- (fun _ => W240.DWord.dunifin),
  type d_in_t <- unit, type d_out_t <- bool * bool.

(* Trial k draws E_k from E, its seed from Rr and the last 240 check bits from Cc. *)
local module DG (E : VE.RO) (Rr : VR.RO) (Cc : VC.RO) = {
  var ok : bool
  var i : int
  proc distinguish(u : unit) : bool * bool = {
    var r21, c22, y, om, b, j, bad, ej, rj;
    E.init(); Rr.init(); Cc.init();
    R.RO.init(); RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    ok <- false; i <- -1;
    while (!ok /\ i + 1 < ntr) {
      E.sample(i + 1);
      Rr.sample(i + 1);
      r21 <$ W16.DWord.dunifin;
      Cc.sample(i + 1);
      ok <- r21 = zero16;
      i <- i + 1;
    }
    Gen.e <@ E.get(i);
    Gen.sd <@ Rr.get(i);
    c22 <@ Cc.get(i);
    RS.RO.m <- empty.[(Gen.e, Gen.q) <- Gen.sd];
    RT.RO.m <- empty.[Gen.sd <- (r21, c22)];
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    LogP.ls <- []; LogP.lt <- [];
    CountP(IPL).init();
    J(CountP(IPL)).run(y, om);
    b <@ J(CountP(IPL)).judge(Gen.p, Gen.q, Gen.e, Gen.sd);
    bad <- !ok;
    j <- 0;
    while (j < i) {
      ej <@ E.get(j);
      rj <@ Rr.get(j);
      bad <- bad \/ ej = Gen.e \/ rj = Gen.sd \/ (ej, Gen.q) \in LogP.ls \/ rj \in LogP.lt;
      j <- j + 1;
    }
    return (b, bad);
  }
}.

local module DE (E : VE.RO) = DG(E, VR.RO, VC.RO).
local module DR (Rr : VR.RO) = DG(VE.LRO, Rr, VC.RO).
local module DC (Cc : VC.RO) = DG(VE.LRO, VR.LRO, Cc).

(* The three tables can be sampled lazily. *)
local lemma DG_lazy &m (P : bool * bool -> bool) :
  Pr[DG(VE.RO, VR.RO, VC.RO).distinguish() @ &m : P res] =
  Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : P res].
proof.
have e1 : Pr[DG(VE.RO, VR.RO, VC.RO).distinguish() @ &m : P res] =
          Pr[DG(VE.LRO, VR.RO, VC.RO).distinguish() @ &m : P res].
- have hll : forall (x : int), is_lossless dstate by move=> _; exact dstate_ll.
  by byequiv (VE.FullEager.RO_LRO_D DE hll).
have e2 : Pr[DG(VE.LRO, VR.RO, VC.RO).distinguish() @ &m : P res] =
          Pr[DG(VE.LRO, VR.LRO, VC.RO).distinguish() @ &m : P res].
- have hll : forall (x : int), is_lossless dseed by move=> _; exact dseed_ll.
  by byequiv (VR.FullEager.RO_LRO_D DR hll).
have e3 : Pr[DG(VE.LRO, VR.LRO, VC.RO).distinguish() @ &m : P res] =
          Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : P res].
- have hll : forall (x : int), is_lossless W240.DWord.dunifin by move=> _; exact W240.DWord.dunifin_ll.
  by byequiv (VC.FullEager.RO_LRO_D DC hll).
by rewrite e1 e2 e3.
qed.

(* ---- Step 4: the lazy game and Θ0' agree unless bad ------------------------------------------ *)
local equiv DGL_T0 : DG(VE.LRO, VR.LRO, VC.LRO).distinguish ~ Judged(Setup0P', J).main :
  ={glob J} ==> !res{1}.`2 => res{1}.`1 = res{2}.
proof.
proc; inline Setup0P'.run.
seq 9 6 : (={glob J, Gen.p, Gen.q, R.RO.m, RW.RO.m} /\ RS.RO.m{2} = empty /\ RT.RO.m{2} = empty /\
           VE.RO.m{1} = empty /\ VR.RO.m{1} = empty /\ VC.RO.m{1} = empty); 1: by inline *; auto.
seq 3 0 : (#pre /\ 0 <= DG.i{1} /\ DG.ok{1} = (r21{1} = zero16)).
- while{1} (-1 <= DG.i{1} /\ (0 <= DG.i{1} => DG.ok{1} = (r21{1} = zero16)) /\ (DG.i{1} = -1 => !DG.ok{1}) /\
            VE.RO.m{1} = empty /\ VR.RO.m{1} = empty /\ VC.RO.m{1} = empty) (ntr - DG.i{1}).
  + move=> _ z; inline *; auto => />; smt(W16.DWord.dunifin_ll).
  by auto => />; smt(ntr_gt0).
seq 5 5 : (={glob J, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RW.RO.m, RS.RO.m} /\
           (DG.ok{1} => ={RT.RO.m}) /\ 0 <= DG.i{1} /\
           (forall k, 0 <= k < DG.i{1} => k \notin VE.RO.m{1} /\ k \notin VR.RO.m{1})).
- by inline *; auto => />; smt(mem_set mem_empty get_set_sameE).
case (DG.ok{1}).
- while{1} (true) (DG.i{1} - j{1}).
  + move=> _ z; inline *; auto => />; smt(dstate_ll dseed_ll).
  wp; call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); 1..4: by proc; inline *; auto.
  call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); 1..6: by proc; inline *; auto.
  inline CountP(IPL).init CountP(IP).init Count(IPL).init Count(IP).init; wp.
  call (_ : ={RW.RO.m}); 1: by sim.
  call (_ : ={R.RO.m}); 1: by sim.
  by auto => />; smt().
conseq (_ : !DG.ok{1} ==> bad{1}) => //.
while{1} (bad{1}) (DG.i{1} - j{1}).
- move=> _ z; inline *; auto => />; smt(dstate_ll dseed_ll).
have [jr jj] := JL_ll; have [jr' jj'] := JP_ll.
wp; call{1} jj; call{2} jj'; call{1} jr; call{2} jr'.
inline CountP(IPL).init CountP(IP).init Count(IPL).init Count(IP).init; wp.
call{1} rw_ll; call{2} rw_ll; call{1} enc_ll; call{2} enc_ll.
by auto => /> /#.
qed.

(* ---- Step 5: the probability of bad in the lazy game ----------------------------------------- *)
local lemma mu_hitS (E : state) (q : pp) (ls : (state * pp) list) :
  mu dstate (fun r => r = E \/ (r, q) \in ls) <= (1 + size ls)%r * inv (2%r ^ 256).
proof.
apply (ler_trans (mu dstate (mem (E :: map fst ls)))).
- by apply mu_le => r _ /= [-> | h]; [left | right; apply/mapP; exists (r, q)].
apply (ler_trans _ _ _ (mu_mem_le_mu1 dstate (E :: map fst ls) (inv (2%r ^ 256)) _)).
- by move=> x; rewrite dstate1_256.
by rewrite /= size_map; smt().
qed.

local lemma mu_hitT (sd : seed) (lt : seed list) :
  mu dseed (fun r => r = sd \/ r \in lt) <= (1 + size lt)%r * inv (2%r ^ 512).
proof.
apply (ler_trans (mu dseed (mem (sd :: lt)))); 1: by apply mu_le => r _ /=.
apply (ler_trans _ _ _ (mu_mem_le_mu1 dseed (sd :: lt) (inv (2%r ^ 512)) _)).
- by move=> x; rewrite dseed1.
by rewrite /=; smt().
qed.

local lemma DGL_bad_e : 0 <= kS => 0 <= qT =>
  ehoare [DG(VE.LRO, VR.LRO, VC.LRO).distinguish :
    (phiL (Kc kS qT) false (-1))%xr ==> (res.`2 /\ size LogP.ls <= kS /\ size LogP.lt <= qT)%xr].
proof.
move=> hkS hqT; have hK := Kc_ge0 kS qT hkS hqT; proc.
seq 24 : ((0 <= DG.i /\ forall k, 0 <= k < DG.i => k \notin VE.RO.m /\ k \notin VR.RO.m) `|`
          (b2r (!DG.ok) + DG.i%r * Kc kS qT)%xr); last first.
(* the check of the rejected trials *)
while ((0 <= j <= DG.i /\ forall k, j <= k < DG.i => k \notin VE.RO.m /\ k \notin VR.RO.m) `|`
       (if size LogP.ls <= kS /\ size LogP.lt <= qT then b2r bad + (DG.i - j)%r * Kc kS qT else 0%r)%xr).
- move=> &hr; apply xle_cxr_r => hj; apply xle_cxr_r => -[[hj0 hji] _].
  have -> : j{hr} = DG.i{hr} by smt().
  by apply xr_ble; smt().
- inline *; auto => &hr /=; apply xle_cxr_r => -[hj [[hj0 hji] hfr]].
  have [hE hR] := hfr j{hr} _; 1: smt().
  rewrite hE /=.
  rewrite (eq_Ep _ _ (fun r => Ep dseed (fun r0 =>
             (if size LogP.ls{hr} <= kS /\ size LogP.lt{hr} <= qT then
                b2r (bad{hr} \/ r = Gen.e{hr} \/ r0 = Gen.sd{hr} \/ (r, Gen.q{hr}) \in LogP.ls{hr} \/
                     r0 \in LogP.lt{hr}) + (DG.i{hr} - (j{hr} + 1))%r * Kc kS qT
              else 0%r)%xr))) => [r _ /= | ].
  + apply eq_Ep => r0 _ /=; rewrite hR /= !get_set_sameE /=.
    rewrite (_ : (0 <= j{hr} + 1 <= DG.i{hr} /\ forall k, j{hr} + 1 <= k < DG.i{hr} =>
                  k \notin VE.RO.m{hr}.[j{hr} <- r] /\ k \notin VR.RO.m{hr}.[j{hr} <- r0])) //.
    by split; [smt() | move=> k hk; rewrite !mem_set; smt()].
  case: (size LogP.ls{hr} <= kS /\ size LogP.lt{hr} <= qT) => hsz /=; last first.
  + by rewrite (eq_Ep _ _ (fun _ => 0%xr)) => [r _ /= | ]; [rewrite EpC dseed_ll | rewrite EpC dstate_ll].
  case: (bad{hr}) => hb /=.
  + rewrite (eq_Ep _ _ (fun _ => (1%r + (DG.i{hr} - (j{hr} + 1))%r * Kc kS qT)%xr)) => [r _ /= | ].
    * by rewrite EpC dseed_ll smul1m.
    rewrite EpC dstate_ll smul1m; apply xr_le.
    have -> : (DG.i{hr} - j{hr})%r * Kc kS qT = (DG.i{hr} - (j{hr} + 1))%r * Kc kS qT + Kc kS qT.
    + by rewrite !fromintB fromintD; ring.
    smt().
  apply (xle_trans (Ep dstate (fun r => (b2r (r = Gen.e{hr} \/ (r, Gen.q{hr}) \in LogP.ls{hr}) +
            (1 + size LogP.lt{hr})%r * inv (2%r ^ 512) + (DG.i{hr} - (j{hr} + 1))%r * Kc kS qT)%xr))).
  + apply le_Ep => r _ /=.
    apply (xle_trans (Ep dseed (fun r0 => (b2r (r = Gen.e{hr} \/ (r, Gen.q{hr}) \in LogP.ls{hr}) +
              (DG.i{hr} - (j{hr} + 1))%r * Kc kS qT + b2r (r0 = Gen.sd{hr} \/ r0 \in LogP.lt{hr}))%xr))).
    * by apply le_Ep => r0 _ /=; rewrite /(%pos); smt(Kc_ge0).
    rewrite (Ep_cb dseed _ (fun r0 => r0 = Gen.sd{hr} \/ r0 \in LogP.lt{hr}) dseed_ll).
    + have : 0%r <= (DG.i{hr} - (j{hr} + 1))%r * Kc kS qT by apply mulr_ge0; smt().
      smt(b2r_ge0).
    by apply xr_le; have := mu_hitT Gen.sd{hr} LogP.lt{hr}; smt().
  rewrite (eq_Ep _ _ (fun r => ((1 + size LogP.lt{hr})%r * inv (2%r ^ 512) + (DG.i{hr} - (j{hr} + 1))%r * Kc kS qT +
                                1%r * b2r (r = Gen.e{hr} \/ (r, Gen.q{hr}) \in LogP.ls{hr}))%xr)) => [r _ /= | ].
  + by congr; ring.
  rewrite (Ep_cbs dstate _ 1%r (fun r1 => r1 = Gen.e{hr} \/ (r1, Gen.q{hr}) \in LogP.ls{hr}) dstate_ll) //.
  + have : 0%r <= (DG.i{hr} - (j{hr} + 1))%r * Kc kS qT by apply mulr_ge0; smt().
    smt(size_ge0 expr_gt0 invr_gt0).
  apply xr_le; have := mu_hitS Gen.e{hr} Gen.q{hr} LogP.ls{hr}.
  have -> : (DG.i{hr} - j{hr})%r * Kc kS qT = (DG.i{hr} - (j{hr} + 1))%r * Kc kS qT + Kc kS qT.
  + by rewrite !fromintB fromintD; ring.
  have h1 : (1 + size LogP.lt{hr})%r * inv (2%r ^ 512) <= (1 + qT)%r * inv (2%r ^ 512).
  + by apply ler_wpmul2r; smt(expr_gt0 invr_gt0).
  have h2 : (1 + size LogP.ls{hr})%r * inv (2%r ^ 256) <= (1 + kS)%r * inv (2%r ^ 256).
  + by apply ler_wpmul2r; smt(expr_gt0 invr_gt0).
  rewrite /Kc; smt().
wp; skip => &hr; apply xle_cxr => -[hi hfr]; split; 1: smt().
apply xr_le; have : 0%r <= DG.i{hr}%r * Kc kS qT by apply mulr_ge0; smt().
smt(b2r_ge0).
(* the adversary: the potential does not move *)
call (_ : (0 <= DG.i /\ forall k, 0 <= k < DG.i => k \notin VE.RO.m /\ k \notin VR.RO.m) `|`
          (b2r (!DG.ok) + DG.i%r * Kc kS qT)%xr).
- by proc; inline *; auto => &hr /=; rewrite ?if_same EpC dans_ll smul1m.
- by proc; inline *; auto => &hr /=; rewrite ?if_same EpC dans_ll smul1m.
- by proc; inline *; auto => &hr /=; rewrite ?if_same EpC dans_ll smul1m.
- by proc; inline *; auto => &hr /=; rewrite ?if_same EpC ddata_ll smul1m.
call (_ : (0 <= DG.i /\ forall k, 0 <= k < DG.i => k \notin VE.RO.m /\ k \notin VR.RO.m) `|`
          (b2r (!DG.ok) + DG.i%r * Kc kS qT)%xr).
- by proc; inline *; auto => &hr /=; rewrite ?if_same EpC dans_ll smul1m.
- by proc; inline *; auto => &hr /=; rewrite ?if_same EpC dans_ll smul1m.
- by proc; inline *; auto => &hr /=; rewrite ?if_same EpC dans_ll smul1m.
- by proc; inline *; auto => &hr /=; rewrite ?if_same EpC dseed_ll smul1m.
- by proc; inline *; auto => &hr /=; rewrite ?if_same EpC dct_ll smul1m.
- by proc; inline *; auto => &hr /=; rewrite ?if_same EpC ddata_ll smul1m.
inline CountP(IPL).init Count(IPL).init; wp.
(* the encryption and Omega read only A, B, H and Omega *)
call (_ : (0 <= DG.i /\ forall k, 0 <= k < DG.i => k \notin VE.RO.m /\ k \notin VR.RO.m) `|`
          (b2r (!DG.ok) + DG.i%r * Kc kS qT)%xr).
- by inline *; auto => &hr /=; rewrite ?if_same EpC ddata_ll smul1m.
call (_ : (0 <= DG.i /\ forall k, 0 <= k < DG.i => k \notin VE.RO.m /\ k \notin VR.RO.m) `|`
          (b2r (!DG.ok) + DG.i%r * Kc kS qT)%xr).
- while ((0 <= DG.i /\ forall k, 0 <= k < DG.i => k \notin VE.RO.m /\ k \notin VR.RO.m) `|`
               (b2r (!DG.ok) + DG.i%r * Kc kS qT)%xr).
  + by move=> &hr; apply xle_cxr_r => _; apply xlexx.
  + by inline *; auto => &hr /=; do 3! (rewrite ?if_same EpC dans_ll smul1m); apply xle_cxr_r => -[_ h]; apply (xle_cxr_l _ _ _ h); apply xlexx.
  by auto.
(* the passing trial *)
inline *; auto.
(* the trials *)
while ((-1 <= DG.i /\ (DG.ok => 0 <= DG.i) /\ (DG.i = -1 => !DG.ok) /\ VE.RO.m = empty /\ VR.RO.m = empty) `|`
       (phiL (Kc kS qT) DG.ok DG.i)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[hi [hok [hi1 [hE hR]]]].
  have hi0 : 0 <= DG.i{hr} by smt(ntr_gt0).
  rewrite hE hR !mem_empty /=.
  rewrite (eq_Ep _ _ (fun _ => (phiL (Kc kS qT) DG.ok{hr} DG.i{hr})%xr)) => [e _ /= | ].
  + rewrite (eq_Ep _ _ (fun _ => (phiL (Kc kS qT) DG.ok{hr} DG.i{hr})%xr)) => [sd _ /= | ].
    * rewrite (eq_Ep _ _ (fun _ => (phiL (Kc kS qT) DG.ok{hr} DG.i{hr})%xr)) => [c _ /= | ].
      - have -> : (0 <= DG.i{hr} /\ forall k, 0 <= k < DG.i{hr} =>
                   k \notin empty.[DG.i{hr} <- e] /\ k \notin empty.[DG.i{hr} <- sd]) = true.
        + by rewrite eqT; split => // k hk; rewrite !mem_set !mem_empty /#.
        by rewrite /(`|`) /= /phiL; case: (DG.ok{hr}) => hk /=; smt().
      by rewrite EpC W240.DWord.dunifin_ll smul1m.
    by rewrite EpC dseed_ll smul1m.
  by rewrite EpC dstate_ll smul1m.
- inline *; auto => &hr /=; apply xle_cxr_r => -[[hok hn] [hi [hok0 [hi1 [hE hR]]]]].
  rewrite hok /= hE hR /=.
  rewrite (eq_Ep _ _ (fun r21 => (if r21 = zero16 then phiL (Kc kS qT) true (DG.i{hr} + 1)
                                  else phiL (Kc kS qT) false (DG.i{hr} + 1))%xr)) => [r _ /= | ].
  + by case: (r = zero16) => _ /=; smt().
  rewrite (Ep_two _ (fun r21 => r21 = zero16)) ?W16.DWord.dunifin_ll; 1: split.
  + by apply phiL_ge0; smt().
  + by move=> _; apply phiL_mono; smt().
  by rewrite dW16_zero; apply xr_le; apply phiL_step => //; smt().
by inline *; auto => &hr /=; rewrite ?EpC ?dP_ll ?dQ_ll ?smul1m.
qed.

(* The adversary stays within its budgets of S and T queries. *)
local lemma DGL_budget : hoare [DG(VE.LRO, VR.LRO, VC.LRO).distinguish : true ==>
  size LogP.ls <= kS /\ size LogP.lt <= qT].
proof.
proc; while (size LogP.ls <= kS /\ size LogP.lt <= qT); 1: by inline *; auto.
wp; call (_ : size LogP.ls <= kS /\ size LogP.lt <= qT); 1..4: by proc; inline *; auto.
call (_ : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 /\
          LogP.ls = [] /\ LogP.lt = [] ==>
          size LogP.ls <= kS /\ size LogP.lt <= qT).
- conseq (_ : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
             CountP.cs <= kS /\ CountP.ct <= qT)
         (_ : size LogP.ls = CountP.cs /\ size LogP.lt = CountP.ct ==>
              size LogP.ls = CountP.cs /\ size LogP.lt = CountP.ct) => //.
  + by proc (size LogP.ls = CountP.cs /\ size LogP.lt = CountP.ct) => //;
      proc; inline *; auto => />; smt(size_rcons).
  exact (J_bounded IPL).
by inline CountP(IPL).init Count(IPL).init; wp; conseq (_ : _ ==> true).
qed.

local lemma DGL_bad &m : 0 <= kS => 0 <= qT =>
  Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : res.`2] <= phiL (Kc kS qT) false (-1).
proof.
move=> hkS hqT.
have h1 : Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : !(size LogP.ls <= kS /\ size LogP.lt <= qT)] = 0%r.
- by byphoare => //; hoare; conseq DGL_budget.
have h2 : Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : res.`2 /\ size LogP.ls <= kS /\ size LogP.lt <= qT] <=
          phiL (Kc kS qT) false (-1).
- byehoare (_ : (phiL (Kc kS qT) false (-1))%xr ==> _) => //; 1: exact (DGL_bad_e hkS hqT).
  by apply phiL_ge0 => //; apply Kc_ge0.
have h3 : Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : res.`2] <=
          Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : res.`2 /\ size LogP.ls <= kS /\ size LogP.lt <= qT] +
          Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : !(size LogP.ls <= kS /\ size LogP.lt <= qT)].
- rewrite Pr[mu_split (size LogP.ls <= kS /\ size LogP.lt <= qT)].
  have : Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : res.`2 /\ !(size LogP.ls <= kS /\ size LogP.lt <= qT)] <=
         Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : !(size LogP.ls <= kS /\ size LogP.lt <= qT)].
  + by rewrite Pr[mu_sub] => // /#.
  smt().
smt().
qed.

(* ---- Step 2': the reduced game and the lazy game ---------------------------------------------- *)
local equiv G2_DG : G2.main ~ DG(VE.RO, VR.RO, VC.RO).distinguish : ={glob J} ==>
  res{1} = res{2}.`1 /\ badB G2.bad{1} G2.es{1} G2.r1s{1} Gen.q{1} LogP.ls{1} LogP.lt{1} = res{2}.`2.
proof.
proc.
seq 11 11 : (={glob J, Gen.p, Gen.q, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m} /\ ok{1} = DG.ok{2} /\ i{1} = DG.i{2} /\
             !ok{1} /\ i{1} = -1 /\ G2.es{1} = [] /\ G2.r1s{1} = [] /\ !G2.bad{1} /\
             VE.RO.m{2} = empty /\ VR.RO.m{2} = empty /\ VC.RO.m{2} = empty); 1: by inline *; auto.
seq 1 1 : (={glob J, Gen.p, Gen.q, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m} /\ ok{1} = DG.ok{2} /\ i{1} = DG.i{2} /\
           0 <= i{1} /\ size G2.es{1} = i{1} + 1 /\ size G2.r1s{1} = i{1} + 1 /\
           (forall k, 0 <= k <= i{1} => VE.RO.m{2}.[k] = Some (nth witness G2.es{1} k)) /\
           (forall k, 0 <= k <= i{1} => VR.RO.m{2}.[k] = Some (nth witness G2.r1s{1} k)) /\
           VC.RO.m{2}.[i{1}] = Some G2.c2{1}.`2 /\ r21{2} = G2.c2{1}.`1 /\ ok{1} = (G2.c2{1}.`1 = zero16) /\
           G2.bad{1} = (ok{1} /\ (last witness G2.es{1} \in take i{1} G2.es{1} \/
                                  last witness G2.r1s{1} \in take i{1} G2.r1s{1}))).
- while (={glob J, Gen.p, Gen.q, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m} /\ ok{1} = DG.ok{2} /\ i{1} = DG.i{2} /\
         -1 <= i{1} /\ size G2.es{1} = i{1} + 1 /\ size G2.r1s{1} = i{1} + 1 /\
         (forall k, 0 <= k <= i{1} => VE.RO.m{2}.[k] = Some (nth witness G2.es{1} k)) /\
         (forall k, 0 <= k <= i{1} => VR.RO.m{2}.[k] = Some (nth witness G2.r1s{1} k)) /\
         (forall k, i{1} < k => k \notin VE.RO.m{2} /\ k \notin VR.RO.m{2} /\ k \notin VC.RO.m{2}) /\
         (0 <= i{1} => VC.RO.m{2}.[i{1}] = Some G2.c2{1}.`2 /\ r21{2} = G2.c2{1}.`1 /\
                       ok{1} = (G2.c2{1}.`1 = zero16)) /\
         (i{1} = -1 => !ok{1}) /\
         G2.bad{1} = (ok{1} /\ (last witness G2.es{1} \in take i{1} G2.es{1} \/
                                last witness G2.r1s{1} \in take i{1} G2.r1s{1}))).
  + inline *; auto => /> &1 &2 hi hes hr1 hE hR hfr hC hi1 hok hn e _.
    have [hE1 [hR1 hC1]] := hfr (DG.i{2} + 1) _; 1: smt().
    rewrite hE1 /= => r1 _; rewrite hR1 /= => r21 _ r22 _; rewrite hC1 /=.
    have t1 : take (DG.i{2} + 1) (rcons G2.es{1} e) = G2.es{1} by rewrite -hes take_rcons_size.
    have t2 : take (DG.i{2} + 1) (rcons G2.r1s{1} r1) = G2.r1s{1} by rewrite -hr1 take_rcons_size.
    rewrite !last_rcons t1 t2.
    split; 1: smt().
    split; 1: smt(size_rcons).
    split; 1: smt(size_rcons).
    split.
    * move=> k hk0 hk; rewrite get_setE; case: (k = DG.i{2} + 1) => hk1; 1: by rewrite nth_rcons /#.
      by rewrite nth_rcons (_ : k < size G2.es{1}) 1:/# /=; apply hE; smt().
    split.
    * move=> k hk0 hk; rewrite get_setE; case: (k = DG.i{2} + 1) => hk1; 1: by rewrite nth_rcons /#.
      by rewrite nth_rcons (_ : k < size G2.r1s{1}) 1:/# /=; apply hR; smt().
    split; 1: by move=> k hk; rewrite !mem_set; smt().
    split; 1: by rewrite get_set_sameE.
    smt().
  by auto => />; smt(ntr_gt0 mem_empty).
(* the passing trial *)
seq 5 5 : (={glob J, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m} /\ i{1} = DG.i{2} /\
           0 <= i{1} /\ size G2.es{1} = i{1} + 1 /\ size G2.r1s{1} = i{1} + 1 /\
           Gen.e{1} = last witness G2.es{1} /\ Gen.sd{1} = last witness G2.r1s{1} /\
           (forall k, 0 <= k <= i{1} => VE.RO.m{2}.[k] = Some (nth witness G2.es{1} k)) /\
           (forall k, 0 <= k <= i{1} => VR.RO.m{2}.[k] = Some (nth witness G2.r1s{1} k)) /\
           G2.bad{1} = (!DG.ok{2} \/ last witness G2.es{1} \in take i{1} G2.es{1} \/
                        last witness G2.r1s{1} \in take i{1} G2.r1s{1})).
- inline *; wp; rnd{2}; wp; rnd{2}; wp; rnd{2}; auto => /> &1 &2 hi hes hr1 hE hR hC r2 _.
  have hEi : DG.i{2} \in VE.RO.m{2} by rewrite domE (hE DG.i{2}) 1:/#.
  have hRi : DG.i{2} \in VR.RO.m{2} by rewrite domE (hR DG.i{2}) 1:/#.
  have hCi : DG.i{2} \in VC.RO.m{2} by rewrite domE hC.
  have le : last witness G2.es{1} = nth witness G2.es{1} DG.i{2}.
  + by rewrite -(nth_last witness) hes; congr; ring.
  have lr : last witness G2.r1s{1} = nth witness G2.r1s{1} DG.i{2}.
  + by rewrite -(nth_last witness) hr1; congr; ring.
  rewrite hEi /= => r00 _; rewrite hRi /= => r10 _; rewrite hCi /=.
  rewrite (hE DG.i{2}) 1:/# (hR DG.i{2}) 1:/# hC /= le lr /= -pairS /=.
  smt().
(* the adversary *)
seq 7 7 : (={glob J, Gen.p, Gen.q, Gen.e, Gen.sd, LogP.ls, LogP.lt, b} /\ i{1} = DG.i{2} /\
           0 <= i{1} /\ size G2.es{1} = i{1} + 1 /\ size G2.r1s{1} = i{1} + 1 /\
           Gen.e{1} = last witness G2.es{1} /\ Gen.sd{1} = last witness G2.r1s{1} /\
           (forall k, 0 <= k <= i{1} => VE.RO.m{2}.[k] = Some (nth witness G2.es{1} k)) /\
           (forall k, 0 <= k <= i{1} => VR.RO.m{2}.[k] = Some (nth witness G2.r1s{1} k)) /\
           G2.bad{1} = (!DG.ok{2} \/ last witness G2.es{1} \in take i{1} G2.es{1} \/
                        last witness G2.r1s{1} \in take i{1} G2.r1s{1})).
- call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, LogP.ls, LogP.lt}); 1..4: by sim.
  call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, LogP.ls, LogP.lt, Count.ca, Count.cb, Count.ch,
              CountP.cs, CountP.ct, CountP.cw}); 1..6: by sim.
  inline CountP(IPL).init Count(IPL).init; wp.
  call (_ : ={RW.RO.m}); 1: by sim.
  by call (_ : ={R.RO.m}); [sim | auto].
(* the check of the rejected trials *)
wp; while{2} (0 <= j{2} <= DG.i{2} /\
              (forall k, 0 <= k <= DG.i{2} => VE.RO.m{2}.[k] = Some (nth witness G2.es{1} k)) /\
              (forall k, 0 <= k <= DG.i{2} => VR.RO.m{2}.[k] = Some (nth witness G2.r1s{1} k)) /\
              bad{2} = (!DG.ok{2} \/ badI G2.es{1} G2.r1s{1} Gen.e{2} Gen.sd{2} Gen.q{2} LogP.ls{2} LogP.lt{2} j{2}))
             (DG.i{2} - j{2}).
- move=> &1 z; inline *; auto => /> &2 hj0 _ hE hR hj.
  have hEj : j{2} \in VE.RO.m{2} by rewrite domE (hE j{2}) 1:/#.
  have hRj : j{2} \in VR.RO.m{2} by rewrite domE (hR j{2}) 1:/#.
  split; 1: smt(dstate_ll).
  move=> _ v _ _; rewrite hEj /=; split; 1: smt(dseed_ll).
  move=> _ v0 _; rewrite hRj /= (hE j{2}) 1:/# (hR j{2}) 1:/# /=.
  split; 2: smt().
  split; 1: smt().
  rewrite /badI eq_iff; split.
  + case=> [[h | [k [hk hk']]] | h]; 1: by left.
    * by right; exists k; smt().
    by right; exists j{2}; smt().
  case=> [h | [k [hk hk']]]; 1: by left; left.
  case: (k = j{2}) => hkj; 1: by right; smt().
  by left; right; exists k; smt().
auto => /> &1 &2 hi hes hr1 hE hR; split; 1: by rewrite /badI; smt().
move=> mE mR j; split; 1: smt().
move=> hj hj0 hji _ _; have -> : j = DG.i{2} by smt().
by rewrite (badB_badI (!DG.ok{2}) G2.es{1} G2.r1s{1} Gen.q{2} LogP.ls{2} LogP.lt{2} DG.i{2}).
qed.

(* ---- Step 2: the real generation and the reduced game agree unless bad ---------------------- *)


local equiv R0_G2 : R0.main ~ G2.main :
  ={glob J} ==> !badB G2.bad{2} G2.es{2} G2.r1s{2} Gen.q{2} LogP.ls{2} LogP.lt{2} => ={res}.
proof.
proc; inline Seq(R0T).select R0T.trial RSs.get RTs.get.
splitwhile{1} 15 : !R0T.bad.
splitwhile{2} 12 : !G2.bad.
seq 15 12 : (={glob J, Gen.p, Gen.q, R.RO.m, RW.RO.m, i} /\ Trials.q{1} = Gen.q{1} /\
             R0T.bad{1} = G2.bad{2} /\ R0T.es{1} = G2.es{2} /\ R0T.r1s{1} = G2.r1s{2} /\
             Trials.vals{1} = G2.es{2} /\ -1 <= i{2} /\ size G2.es{2} = i{2} + 1 /\ size G2.r1s{2} = i{2} + 1 /\
             (!G2.bad{2} => ok{1} = ok{2}) /\ (i{2} = -1 => !ok{2}) /\
             invT Gen.q{1} RS.RO.m{1} RT.RO.m{1} G2.es{2} G2.r1s{2} ok{1} /\
             (0 <= i{2} => ok{2} = (G2.c2{2}.`1 = zero16)) /\
             (ok{2} /\ !G2.bad{2} =>
                RS.RO.m{1}.[(last witness G2.es{2}, Gen.q{1})] = Some (last witness G2.r1s{2}) /\
                RT.RO.m{1}.[last witness G2.r1s{2}] = Some G2.c2{2} /\
                !(last witness G2.es{2} \in take i{2} G2.es{2}) /\
                !(last witness G2.r1s{2} \in take i{2} G2.r1s{2})) /\
             !((!ok{2} /\ i{2} + 1 < ntr) /\ !G2.bad{2})).
- while (={glob J, Gen.p, Gen.q, R.RO.m, RW.RO.m, i} /\ Trials.q{1} = Gen.q{1} /\
         R0T.bad{1} = G2.bad{2} /\ R0T.es{1} = G2.es{2} /\ R0T.r1s{1} = G2.r1s{2} /\
         Trials.vals{1} = G2.es{2} /\ -1 <= i{2} /\ size G2.es{2} = i{2} + 1 /\ size G2.r1s{2} = i{2} + 1 /\
         (!G2.bad{2} => ok{1} = ok{2}) /\ (i{2} = -1 => !ok{2}) /\
         invT Gen.q{1} RS.RO.m{1} RT.RO.m{1} G2.es{2} G2.r1s{2} ok{1} /\
         (0 <= i{2} => ok{2} = (G2.c2{2}.`1 = zero16)) /\
         (ok{2} /\ !G2.bad{2} =>
            RS.RO.m{1}.[(last witness G2.es{2}, Gen.q{1})] = Some (last witness G2.r1s{2}) /\
            RT.RO.m{1}.[last witness G2.r1s{2}] = Some G2.c2{2} /\
            !(last witness G2.es{2} \in take i{2} G2.es{2}) /\
            !(last witness G2.r1s{2} \in take i{2} G2.r1s{2}))).
  + wp; rnd; rnd; wp; rnd; wp; rnd; skip => /> &1 &2 hi hes hr1 hok hi1 hS hT hST hF hc hpr hok1 hn hb hok2 e _ r1 _.
    have hF0 := hF hok1.
    have t1 : take (i{2} + 1) (rcons G2.es{2} e) = G2.es{2} by rewrite -hes take_rcons_size.
    have t2 : take (i{2} + 1) (rcons G2.r1s{2} r1) = G2.r1s{2} by rewrite -hr1 take_rcons_size.
    rewrite !last_rcons t1 t2.
    case: ((e, Gen.q{2}) \in RS.RO.m{1}) => hA /=.
    * have hd := hST _ hA; have [_ /= he] := hS _ hA; have hc0 := hF0 _ hd.
      move=> r21 _ r22 _; rewrite hd /= he /=.
      split; 2: by move=> _ _; exact hc0.
      split; 1: smt().
      split; 1: smt(size_rcons).
      split; 1: smt(size_rcons).
      split; 1: smt().
      split; 1: smt().
      split; 1: by move=> x1 hx1; rewrite mem_rcons /=; smt().
      split; 1: by move=> x1 hx1; rewrite mem_rcons /=; smt().
      by move=> _; exact hF0.
    move=> r21 _ r22 _; rewrite get_set_sameE /=.
    case: (r1 \in RT.RO.m{1}) => hB /=.
    * have hr : r1 \in G2.r1s{2} by apply hT.
      have hc0 := hF0 _ hB.
      split; 2: smt().
      split; 1: smt().
      split; 1: smt(size_rcons).
      split; 1: smt(size_rcons).
      split; 1: smt().
      split; 1: smt().
      split; 2: smt().
      split; 1: by move=> x1; rewrite mem_set mem_rcons /= => -[hx | ->] /=; smt().
      split; 1: by move=> x1 hx1; rewrite mem_rcons /=; smt().
      split; 1: by move=> x1; rewrite mem_set get_setE => -[hx | ->] /=; smt().
      by move=> _; exact hF0.
    split; 2: smt(get_set_sameE).
    split; 1: smt().
    split; 1: smt(size_rcons).
    split; 1: smt(size_rcons).
    split; 1: smt(get_set_sameE).
    split; 1: smt().
    split; 2: smt(get_set_sameE).
    split; 1: by move=> x1; rewrite mem_set mem_rcons /= => -[hx | ->] /=; smt().
    split; 1: by move=> x1; rewrite mem_set mem_rcons /= => -[hx | ->] /=; smt().
    split; 1: by move=> x1; rewrite !mem_set get_setE => -[hx | ->] /=; smt().
    by rewrite get_set_sameE /= => hr21 x1; rewrite mem_set get_setE => -[hx | ->] /=; smt().
  by inline *; auto => />; smt(mem_empty).
(* the remaining trials of a bad run, and the cutoff *)
seq 1 2 : (G2.bad{2} \/
           (={glob J, Gen.p, Gen.q, R.RO.m, RW.RO.m, i} /\ Trials.q{1} = Gen.q{1} /\
            Trials.vals{1} = G2.es{2} /\ 0 <= i{2} /\ size G2.es{2} = i{2} + 1 /\ size G2.r1s{2} = i{2} + 1 /\
            ok{1} /\ ok{2} /\ invT Gen.q{1} RS.RO.m{1} RT.RO.m{1} G2.es{2} G2.r1s{2} ok{1} /\
            RS.RO.m{1}.[(last witness G2.es{2}, Gen.q{1})] = Some (last witness G2.r1s{2}) /\
            RT.RO.m{1}.[last witness G2.r1s{2}] = Some G2.c2{2} /\
            !(last witness G2.es{2} \in take i{2} G2.es{2}) /\ !(last witness G2.r1s{2} \in take i{2} G2.r1s{2}))).
- case: (G2.bad{2}).
  + wp; while{2} (G2.bad{2}) (ntr - i{2}).
    * by move=> _ z; auto => />; smt(dstate_ll dseed_ll W16.DWord.dunifin_ll W240.DWord.dunifin_ll).
    while{1} (true) (ntr - i{1}).
    * move=> _ z; wp; rnd; rnd; wp; rnd; wp; rnd; skip => /> &hr _ _.
      do 4! (apply mu_const_true; 1: smt(dstate_ll dseed_ll W16.DWord.dunifin_ll W240.DWord.dunifin_ll)).
      smt().
    by auto => />; smt().
  rcondf{1} 1; 1: by auto => /> /#.
  rcondf{2} 1; 1: by auto => /> /#.
  by wp; skip => /> &1 &2; smt().
case: (G2.bad{2}).
- conseq (_ : G2.bad{2} ==> G2.bad{2}) => //; 1: by move=> &1 &2 hb; rewrite /badB hb.
  have [jr jj] := JP_ll; have [jr' jj'] := JL_ll.
  call{1} jj; call{2} jj'; call{1} jr; call{2} jr'.
  inline CountP(IP).init Count(IP).init CountP(IPL).init Count(IPL).init; wp.
  call{1} rw_ll; call{2} rw_ll; call{1} enc_ll; call{2} enc_ll; call{1} rs_ll.
  by auto.
(* a good run: the passing trial is programmed in both games *)
seq 3 4 : (={glob J, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RW.RO.m} /\ !G2.bad{2} /\
           agree RS.RO.m{1} RS.RO.m{2} (rejS G2.es{2} Gen.q{2}) /\
           agree RT.RO.m{1} RT.RO.m{2} (rejT G2.r1s{2})).
- inline RS.RO.get; wp; rnd{1}; auto => /> &1 &2 + hnb; rewrite hnb /=.
  move=> [#] -> -> -> -> -> -> hTq -> hi0 hes hr1 hok1 hok2 hinv hSl hTl hne hnr r _.
  have hl : nth witness G2.es{2} i{2} = last witness G2.es{2}.
  + by rewrite -(nth_last witness) hes; congr; ring.
  have hin : (last witness G2.es{2}, Gen.q{2}) \in RS.RO.m{1} by rewrite domE hSl.
  rewrite hl hin /= hSl /=.
  have [hS1 [hT1 _]] := hinv.
  split.
  + move=> x hx; rewrite get_setE emptyE.
    case: (x = (last witness G2.es{2}, Gen.q{2})) => [-> | hxn] /=; 1: exact hSl.
    case: (x \in RS.RO.m{1}) => hxm; last by smt(domE).
    have [hx2 hx1] := hS1 x hxm.
    case: (mem_take_last G2.es{2} x.`1 hx1) => [ht | hlx]; 2: smt().
    have : x \in rejS G2.es{2} Gen.q{2}; 2: smt().
    by rewrite /rejS; apply/mapP; exists x.`1; smt().
  move=> x hx; rewrite get_setE emptyE.
  case: (x = last witness G2.r1s{2}) => [-> | hxn] /=; 1: exact hTl.
  case: (x \in RT.RO.m{1}) => hxm; last by smt(domE).
  case: (mem_take_last G2.r1s{2} x (hT1 x hxm)) => [ht | hlx]; 2: smt().
  by move: hx; rewrite /rejT ht.
seq 2 2 : (#pre /\ ={y, om}).
- call (_ : ={RW.RO.m}); 1: by sim.
  by call (_ : ={R.RO.m}); [sim | auto].
inline CountP(IP).init Count(IP).init CountP(IPL).init Count(IPL).init; wp.
call (_ : badB G2.bad G2.es G2.r1s Gen.q LogP.ls LogP.lt,
          ={Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct,
            CountP.cw} /\
          agree RS.RO.m{1} RS.RO.m{2} (rejS G2.es{2} Gen.q{2}) /\ agree RT.RO.m{1} RT.RO.m{2} (rejT G2.r1s{2})).
- by move=> O; have [_ h] := J_ll O.
- by proc; inline *; auto => />.
- by move=> &2 _; have [h _] := ip_ll.
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />.
- by move=> &2 _; have [_ [h _]] := ip_ll.
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />.
- by move=> &2 _; have [_ [_ [h _]]] := ip_ll.
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />.
- by move=> &2 _; have [_ [_ [_ [_ [_ h]]]]] := ip_ll.
- by move=> &1; proc; inline *; auto => />; smt(ddata_ll).
call (_ : badB G2.bad G2.es G2.r1s Gen.q LogP.ls LogP.lt,
          ={Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct,
            CountP.cw} /\
          agree RS.RO.m{1} RS.RO.m{2} (rejS G2.es{2} Gen.q{2}) /\ agree RT.RO.m{1} RT.RO.m{2} (rejT G2.r1s{2})).
- by move=> O; have [h _] := J_ll O.
- by proc; inline *; auto => />.
- by move=> &2 _; have [h _] := ip_ll.
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />.
- by move=> &2 _; have [_ [h _]] := ip_ll.
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />.
- by move=> &2 _; have [_ [_ [h _]]] := ip_ll.
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- proc; inline *; auto => /> &1 &2 hnb hag hagT r _.
  have heq : !badB G2.bad{2} G2.es{2} G2.r1s{2} Gen.q{2} (rcons LogP.ls{2} (e{2}, q{2})) LogP.lt{2} =>
             RS.RO.m{1}.[e{2}, q{2}] = RS.RO.m{2}.[e{2}, q{2}].
  + by rewrite /badB has_rcons => hb'; apply hag; smt().
  split => hn2; split => hn1 hb'; have := heq hb'.
  + move=> _; rewrite !get_set_sameE /= /agree => y hy.
    by rewrite !get_setE; case: (y = (e{2}, q{2})) => // _; apply hag.
  + smt(domE).
  + smt(domE).
  by move=> ->.
- by move=> &2 _; have [_ [_ [_ [h _]]]] := ip_ll.
- by move=> &1; proc; inline *; auto => />; smt(dseed_ll has_rcons).
- proc; inline *; auto => /> &1 &2 hnb hag hagT r _.
  have heq : !badB G2.bad{2} G2.es{2} G2.r1s{2} Gen.q{2} LogP.ls{2} (rcons LogP.lt{2} d{2}) =>
             RT.RO.m{1}.[d{2}] = RT.RO.m{2}.[d{2}].
  + by rewrite /badB has_rcons => hb'; apply hagT; smt().
  split => hn2; split => hn1 hb'; have := heq hb'.
  + move=> _; rewrite !get_set_sameE /= /agree => y hy.
    by rewrite !get_setE; case: (y = d{2}) => // _; apply hagT.
  + smt(domE).
  + smt(domE).
  by move=> ->.
- by move=> &2 _; have [_ [_ [_ [_ [h _]]]]] := ip_ll.
- by move=> &1; proc; inline *; auto => />; smt(dct_ll has_rcons).
- by proc; inline *; auto => />.
- by move=> &2 _; have [_ [_ [_ [_ [_ h]]]]] := ip_ll.
- by move=> &1; proc; inline *; auto => />; smt(ddata_ll).
by auto => />; smt().
qed.

local equiv T0_DGL : Judged(Setup0P', J).main ~ DG(VE.LRO, VR.LRO, VC.LRO).distinguish :
  ={glob J} ==> !res{2}.`2 => res{1} = res{2}.`1.
proof. by symmetry; conseq DGL_T0 => /#. qed.

local equiv G2_R0 : G2.main ~ R0.main :
  ={glob J} ==> !badB G2.bad{1} G2.es{1} G2.r1s{1} Gen.q{1} LogP.ls{1} LogP.lt{1} => ={res}.
proof. by symmetry; conseq R0_G2 => /#. qed.

(* Lemma W2 for the sequential rule cut off after ntr trials: the generation by rejection and one
   programmed point differ by at most deltacut. Selection.ec states it for every covered rule. *)
lemma W2_cut &m : 0 <= kS => 0 <= qT =>
  `| Pr[Judged(Setup0P(Seq), J).main() @ &m : res] - Pr[Judged(Setup0P', J).main() @ &m : res] |
    <= deltacut kS qT.
proof.
move=> hkS hqT.
pose B := Pr[G2.main() @ &m : badB G2.bad G2.es G2.r1s Gen.q LogP.ls LogP.lt].
have e0 : Pr[Judged(Setup0P(Seq), J).main() @ &m : res] = Pr[R0.main() @ &m : res] by byequiv real_R0.
have h1 : Pr[R0.main() @ &m : res] <= Pr[G2.main() @ &m : res] + B.
- apply (ler_trans (Pr[G2.main() @ &m : res \/ badB G2.bad G2.es G2.r1s Gen.q LogP.ls LogP.lt])).
  + by byequiv R0_G2 => // /#.
  by rewrite Pr[mu_or] /B; smt(mu_bounded).
have h2 : Pr[G2.main() @ &m : res] <= Pr[R0.main() @ &m : res] + B.
- rewrite Pr[mu_split (badB G2.bad G2.es G2.r1s Gen.q LogP.ls LogP.lt)].
  have : Pr[G2.main() @ &m : res /\ !badB G2.bad G2.es G2.r1s Gen.q LogP.ls LogP.lt] <= Pr[R0.main() @ &m : res].
  + by byequiv G2_R0 => // /#.
  have : Pr[G2.main() @ &m : res /\ badB G2.bad G2.es G2.r1s Gen.q LogP.ls LogP.lt] <= B.
  + by rewrite /B Pr[mu_sub] => // /#.
  smt().
have e1 : Pr[G2.main() @ &m : res] = Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : res.`1].
- rewrite -(DG_lazy &m (fun (r : bool * bool) => r.`1)).
  by byequiv G2_DG => // /#.
have e2 : B = Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : res.`2].
- rewrite /B -(DG_lazy &m (fun (r : bool * bool) => r.`2)).
  by byequiv G2_DG => // /#.
have h3 : Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : res.`1] <=
          Pr[Judged(Setup0P', J).main() @ &m : res] + Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : res.`2].
- apply (ler_trans (Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : res.`2 \/ (res.`1 /\ !res.`2)])).
  + by rewrite Pr[mu_sub] => // /#.
  rewrite Pr[mu_or]; have : Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : res.`1 /\ !res.`2] <=
                            Pr[Judged(Setup0P', J).main() @ &m : res].
  + by byequiv DGL_T0 => // /#.
  smt(mu_bounded).
have h4 : Pr[Judged(Setup0P', J).main() @ &m : res] <=
          Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : res.`1] + Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : res.`2].
- apply (ler_trans (Pr[DG(VE.LRO, VR.LRO, VC.LRO).distinguish() @ &m : res.`1 \/ res.`2])).
  + by byequiv T0_DGL => // /#.
  by rewrite Pr[mu_or]; smt(mu_bounded).
have hb := DGL_bad &m hkS hqT.
have hc : phiL (Kc kS qT) false (-1) <= 2%r ^ 16 * Kc kS qT + inv (2%r ^ 256).
- rewrite /phiL /= ntr_gt0 /=.
  have e : (1%r - pk) * Kc kS qT / pk = (2%r ^ 16 - 1%r) * Kc kS qT by rewrite /pk; field; smt(expr_gt0).
  have := pcut_bound; have := Kc_ge0 kS qT hkS hqT; rewrite -/pk e => *.
  smt().
rewrite /deltacut; smt().
qed.
end section W2.

(* A continuation that sees everything: Y, omega*, the secrets and all the functions. *)
module type CONT (O : OraclesP) = {
  proc run(y : state, om : data, p : pw, q : pp, e : state, sd : seed) : bool
}.

module GenGame (S : SETUPP) (D : CONT) = {
  proc main() : bool = {
    var y, om, b;
    (y, om) <@ S.run();
    b <@ D(IP).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd);
    return b;
  }
}.

section W3.
declare module D <: CONT {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RT.RO, -RW.RO, -Gen}.

local module IPG (G : R.RO) : OraclesP = {
  proc a = Orc(G).a
  proc b = Orc(G).b
  proc h = Orc(G).h
  proc s = IP.s
  proc t = IP.t
  proc w = IP.w
}.

(* Θ0' and Θ1 as programs on the oracle of A, B, H. *)
local module V0 (G : R.RO) = {
  proc distinguish() : bool = {
    var et, y, om, b;
    RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Gen.e <$ dstate;
    Gen.sd <$ dseed;
    et <$ W240.DWord.dunifin;
    RS.RO.set((Gen.e, Gen.q), Gen.sd);
    RT.RO.set(Gen.sd, (zero16, et));
    y <@ Net(Orc(G)).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    b <@ D(IPG(G)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd);
    return b;
  }
}.

local module V1 (G : R.RO) = {
  proc distinguish() : bool = {
    var y, om, et, b;
    RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    y <$ dstate;
    om <$ ddata;
    Gen.sd <$ dseed;
    Gen.e <@ Net(Orc(G)).dec(Gen.p, y);
    RS.RO.set((Gen.e, Gen.q), Gen.sd);
    et <$ W240.DWord.dunifin;
    RT.RO.set(Gen.sd, (zero16, et));
    RW.RO.set(Gen.sd, om);
    b <@ D(IPG(G)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd);
    return b;
  }
}.

local equiv G0_V0 : GenGame(Setup0P', D).main ~ R.MainD(V0, R.RO).distinguish : ={glob D} ==> ={res, glob D}.
proof. by proc; inline *; sim. qed.

local equiv G1_V1 : GenGame(Setup1P, D).main ~ R.MainD(V1, R.RO).distinguish : ={glob D} ==> ={res, glob D}.
proof. by proc; inline *; sim. qed.

(* With A, B, H a whole function, (E, Y = Perm_P(E)) and (Inv_P(Y), Y) correspond one to one. *)
local equiv core3 : R.MainD(V0, RE.FunRO).distinguish ~ R.MainD(V1, RE.FunRO).distinguish :
  ={glob D} ==> ={res, glob D}.
proof.
proc; inline V0(RE.FunRO).distinguish V1(RE.FunRO).distinguish.
seq 7 7 : (={glob D, RE.FunRO.f, RS.RO.m, RT.RO.m, RW.RO.m, Gen.p, Gen.q} /\ RW.RO.m{1} = empty).
- by inline *; auto.
swap{2} 2 1; swap{2} 6 -3.
seq 3 3 : (={glob D, RE.FunRO.f, RS.RO.m, RT.RO.m, RW.RO.m, Gen.p, Gen.q, Gen.sd, et} /\ RW.RO.m{1} = empty /\
           y{2} = perm RE.FunRO.f{1} Gen.p{1} Gen.e{1}).
- rnd; rnd; rnd (fun e => perm RE.FunRO.f{1} Gen.p{1} e) (fun y => invperm RE.FunRO.f{1} Gen.p{1} y).
  by auto => /> &2; split => [y _ | _ e _]; [rewrite permK | rewrite invpermK].
swap{2} 1 3.
seq 0 1 : (#pre /\ Gen.e{2} = invperm RE.FunRO.f{2} Gen.p{2} y{2}).
- by exlim Gen.p{2}, y{2} => p0 y0; call{2} (dec_fun_ph p0 y0); auto.
seq 2 2 : (={glob D, RE.FunRO.f, RS.RO.m, RT.RO.m, RW.RO.m, Gen.p, Gen.q, Gen.sd, Gen.e} /\
           RW.RO.m{1} = empty /\ y{2} = perm RE.FunRO.f{1} Gen.p{1} Gen.e{1}).
- by inline *; auto => /> &1 &2; rewrite invpermK.
seq 1 0 : (#pre /\ y{1} = y{2}).
- by exlim Gen.p{1}, Gen.e{1} => p0 e0; call{1} (enc_fun_ph p0 e0); auto.
seq 1 2 : (={glob D, RE.FunRO.f, RS.RO.m, RT.RO.m, RW.RO.m, Gen.p, Gen.q, Gen.sd, Gen.e, y, om}).
- inline *; rcondt{1} 3; 1: by auto => />; smt(mem_empty).
  by auto => />; smt(get_set_sameE).
wp; call (_ : ={RE.FunRO.f, RS.RO.m, RT.RO.m, RW.RO.m}); 1..6: by proc; inline *; auto.
by auto.
qed.

(* Lemma W3: (P, Q, A, B, H, Y, S, T, Omega, omega*, E, seed* ) agree in Θ0' and Θ1, with E = e*. *)
lemma W3 : equiv [GenGame(Setup0P', D).main ~ GenGame(Setup1P, D).main : ={glob D} ==> ={res, glob D}].
proof.
transitivity R.MainD(V0, R.RO).distinguish (={glob D} ==> ={res, glob D}) (={glob D} ==> ={res, glob D}) => //.
- by move=> &1 &2 h; exists (glob D){1}.
- exact G0_V0.
transitivity R.MainD(V0, RE.FunRO).distinguish
  (={glob D} ==> ={res, glob D}) (={glob D} ==> ={res, glob D}) => //.
- by move=> &1 &2 h; exists (glob D){1}.
- transitivity R.MainD(V0, R.RO).distinguish (={glob D} ==> ={res, glob D})
    (={glob V0, arg} ==> ={res, glob V0}) => //.
  + by move=> &1 &2 h; exists (glob D){2} Gen.e{2} Gen.p{2} Gen.q{2} Gen.sd{2} RS.RO.m{2} RT.RO.m{2} RW.RO.m{2} arg{2}.
  + by proc; inline *; sim.
  exact (RO_FunRO V0).
transitivity R.MainD(V1, RE.FunRO).distinguish (={glob D} ==> ={res, glob D}) (={glob D} ==> ={res, glob D}) => //.
- by move=> &1 &2 h; exists (glob D){1}.
- exact core3.
transitivity R.MainD(V1, R.RO).distinguish (={glob D} ==> ={res, glob D}) (={glob D} ==> ={res, glob D}) => //.
- by move=> &1 &2 h; exists (glob D){1}.
- transitivity R.MainD(V1, R.RO).distinguish (={glob V1, arg} ==> ={res, glob V1})
    (={glob D} ==> ={res, glob D}) => //.
  + by move=> &1 &2 h; exists (glob D){1} Gen.e{1} Gen.p{1} Gen.q{1} Gen.sd{1} RS.RO.m{1} RT.RO.m{1} RW.RO.m{1} arg{1}.
  + by symmetry; conseq (RO_FunRO V1).
  by proc; inline *; sim.
by symmetry; conseq G1_V1.
qed.
end section W3.

(* ---- Lemmas W2 and W3 together: from Θ0 with the cut rule to Θ1 ------------------------------ *)
(* A judge as a continuation. *)
module JC (J : ADVJ) (O : OraclesP) = {
  proc run(y : state, om : data, p : pw, q : pp, e : state, sd : seed) : bool = {
    var b;
    CountP(O).init();
    J(CountP(O)).run(y, om);
    b <@ J(CountP(O)).judge(p, q, e, sd);
    return b;
  }
}.

section W23.
declare op kS : int.
declare op qT : int.
declare module J <: ADVJ {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO,
                          -RW.RO, -Gen, -Trials, -Count, -CountP}.
declare axiom J_bounded (O <: OraclesP {-Count, -CountP, -J}) :
  hoare [J(CountP(O)).run :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    CountP.cs <= kS /\ CountP.ct <= qT].
declare axiom J_ll (O <: OraclesP {-J}) :
  (islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
   islossless O.w => islossless J(O).run) /\
  (islossless O.a => islossless O.b => islossless O.h => islossless O.w => islossless J(O).judge).

lemma theta01 &m : 0 <= kS => 0 <= qT =>
  `| Pr[Judged(Setup0P(Seq), J).main() @ &m : res] - Pr[Judged(Setup1P, J).main() @ &m : res] |
    <= deltacut kS qT.
proof.
move=> hkS hqT; have := W2_cut kS qT J J_bounded J_ll &m hkS hqT.
have -> // : Pr[Judged(Setup0P', J).main() @ &m : res] = Pr[Judged(Setup1P, J).main() @ &m : res].
have -> : Pr[Judged(Setup0P', J).main() @ &m : res] = Pr[GenGame(Setup0P', JC(J)).main() @ &m : res].
- byequiv => //; proc; inline JC(J, IP).run; wp.
  call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct, CountP.cw}); 1..4: by sim.
  call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct, CountP.cw}); 1..6: by sim.
  inline CountP(IP).init Count(IP).init; wp.
  by call (_ : true ==> ={res, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); [sim | auto].
have -> : Pr[Judged(Setup1P, J).main() @ &m : res] = Pr[GenGame(Setup1P, JC(J)).main() @ &m : res].
- byequiv => //; proc; inline JC(J, IP).run; wp.
  call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct, CountP.cw}); 1..4: by sim.
  call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct, CountP.cw}); 1..6: by sim.
  inline CountP(IP).init Count(IP).init; wp.
  by call (_ : true ==> ={res, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); [sim | auto].
by byequiv (W3 (JC(J))).
qed.
end section W23.

(* The same for an event of the adversary's output and the secrets. *)
section Theta01Out.
declare op kS : int.
declare op qT : int.
declare op E : seed * (pw * pp) -> pw -> pp -> state -> seed -> bool.
declare module A <: AdvP {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO,
                          -RW.RO, -Gen, -Trials, -Count, -CountP}.
declare axiom A_bounded (O <: OraclesP {-Count, -CountP, -A}) :
  hoare [A(CountP(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    CountP.cs <= kS /\ CountP.ct <= qT].
declare axiom A_ll (O <: OraclesP {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless A(O).guess.

local module JE (O : OraclesP) = {
  var out : seed * (pw * pp)
  proc run(y : state, om : data) : unit = { out <@ A(O).guess(y, om); }
  proc judge(p : pw, q : pp, e : state, sd : seed) : bool = { return E out p q e sd; }
}.

lemma theta01_out &m : 0 <= kS => 0 <= qT =>
  `| Pr[GameP(Setup0P(Seq), A).main() @ &m : E res Gen.p Gen.q Gen.e Gen.sd] -
     Pr[GameP(Setup1P, A).main() @ &m : E res Gen.p Gen.q Gen.e Gen.sd] | <= deltacut kS qT.
proof.
move=> hkS hqT; have := theta01 kS qT JE _ _ &m hkS hqT.
- by move=> O; proc; call (A_bounded O); auto.
- move=> O; split; 2: by move=> *; proc; auto.
  by move=> ha hb hh hs ht hw; proc; call (A_ll O ha hb hh hs ht hw); auto.
have -> : Pr[Judged(Setup0P(Seq), JE).main() @ &m : res] =
          Pr[GameP(Setup0P(Seq), A).main() @ &m : E res Gen.p Gen.q Gen.e Gen.sd].
- byequiv => //; proc; inline JE(CountP(IP)).run JE(CountP(IP)).judge; wp.
  call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct, CountP.cw}); 1..6: by sim.
  inline CountP(IP).init Count(IP).init; wp.
  by call (_ : true ==> ={res, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); [sim | auto].
have -> // : Pr[Judged(Setup1P, JE).main() @ &m : res] =
             Pr[GameP(Setup1P, A).main() @ &m : E res Gen.p Gen.q Gen.e Gen.sd].
byequiv => //; proc; inline JE(CountP(IP)).run JE(CountP(IP)).judge; wp.
call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct, CountP.cw}); 1..6: by sim.
inline CountP(IP).init Count(IP).init; wp.
by call (_ : true ==> ={res, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); [sim | auto].
qed.
end section Theta01Out.

lemma rw_get_ll : islossless RW.RO.get by proc; auto; smt(ddata_ll).
lemma rs_get_ll : islossless RS.RO.get by proc; auto; smt(dseed_ll).

(* The creation refusal: Y = E has chance 2^-256 over H, which the generation does not use. *)
module T5 = {
  proc main() : bool = {
    var i, y;
    R.RO.init(); RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Trials.q <- Gen.q; Trials.vals <- []; Trials.outs <- [];
    i <@ Seq(Trials).select();
    Gen.e <- nth witness Trials.vals i;
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    return y = Gen.e;
  }
}.

lemma T5_pr &m : Pr[T5.main() @ &m : res] <= inv (2%r ^ 256).
proof.
byphoare => //; proc.
seq 11 : true 1%r (inv (2%r ^ 256)) 0%r 0%r (R.RO.m = empty) => //.
- wp; call (_ : R.RO.m = empty).
  + by while (R.RO.m = empty); [inline *; auto | auto].
  by inline *; auto.
exlim Gen.p, Gen.e => p0 x0.
have := enc_uniform_ph p0 x0 x0; rewrite dstate1_256 => h.
call (_ : arg = (p0, x0) /\ (forall c, c \in R.RO.m => isA c \/ isB c) ==> res = x0).
- bypr => &m0; split; 1: smt(expr_gt0 invr_gt0).
  move=> hpre; have -> // : Pr[Net(Ideal).enc(p{m0}, x{m0}) @ &m0 : res = x0] = inv (2%r ^ 256).
  by byphoare h => //; smt().
by auto => />; smt(mem_empty).
qed.

(* The chance of a refused creation in Θ0. *)
lemma setup_refused &m : Pr[Setup0P(Seq).run() @ &m : res.`1 = Gen.e] <= inv (2%r ^ 256).
proof.
have <- : Pr[T5.main() @ &m : res] = Pr[Setup0P(Seq).run() @ &m : res.`1 = Gen.e]; 2: exact T5_pr.
byequiv => //; proc; call{2} rw_get_ll.
call (_ : ={R.RO.m}); 1: by sim.
call{2} rs_get_ll.
by conseq (_ : _ ==> ={Gen.p, Gen.e, R.RO.m}) => //; sim.
qed.
