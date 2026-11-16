(* The lazy game Θ2 of A.6: the chains of the passwords from Y, the collision event Coll_P, the
   potentials of the seed and collision bounds, and the pair set Z (DESIGN-NOTES A.6). *)
require import AllCore List Distr DBool DProd FMap IntDiv StdBigop StdOrder Xreal.
require import Suite3 Chain Collision Passphrase Generation.
import W128 StdBigop.Bigreal.BRA RealOrder.

(* ---- The lazy Θ2 for the chain lemmas ------------------------------------------------------- *)
module WithP (O : ABHB) : OraclesP = {
  var sq : (state * pp) list
  var tq, wq : seed list
  proc a = O.a
  proc b = O.b
  proc h = O.h
  proc s(e : state, q : pp) = {
    var d; sq <- rcons sq (e, q); CountP.cs <- CountP.cs + 1; d <@ RS.RO.get(e, q); return d;
  }
  proc t(d : seed) = { var c; tq <- rcons tq d; CountP.ct <- CountP.ct + 1; c <@ RT.RO.get(d); return c; }
  proc w(d : seed) = { var o; wq <- rcons wq d; CountP.cw <- CountP.cw + 1; o <@ RW.RO.get(d); return o; }
}.

module AP (A : AdvP) (O : ABHB) = {
  var out : seed * (pw * pp)
  proc run(y : state) : unit = {
    var om, o;
    RS.RO.init(); RT.RO.init(); RW.RO.init();
    WithP.sq <- []; WithP.tq <- []; WithP.wq <- [];
    CountP.cs <- 0; CountP.ct <- 0; CountP.cw <- 0;
    om <$ ddata;
    o <@ A(WithP(O)).guess(y, om);
    out <- o;
  }
}.

(* P is drawn first and not used during the run; Q and seed* are drawn after it. *)
module Theta2L (A : AdvP) = {
  proc main() : state = {
    var xs;
    xs <@ ChainGame(AP(A)).main();
    Gen.q <$ dQ;
    Gen.sd <$ dseed;
    return xs;
  }
}.

(* Bad: a query of S at (e*, Q), or of T or Omega at seed*. *)
op badP (e : state) (q : pp) (sd : seed) (sq : (state * pp) list) (tq wq : seed list) =
  (e, q) \in sq \/ sd \in tq \/ sd \in wq.

(* epsC: the error terms of Theorem 5 for the cut rule without refusal; epsW adds delta_gen and the
   refusal term 2^-256, as in the text. *)
op epsC (kA kS qB qH qT qW : int) : real =
  (s1 * kS%r + qB%r + (1%r + 12%r * p1) * kA%r + 66%r) / 2%r ^ 128 + (qH%r + kA%r) / 2%r ^ 256
  + (qT%r + qW%r) / 2%r ^ 512.
op epsW (kA kS qB qH qT qW : int) : real = epsC kA kS qB qH qT qW + deltagen kS qT + inv (2%r ^ 256).

(* ---- Theorem 5 -------------------------------------------------------------------------------- *)
(* ---- The seed query without the last chain point (event N) ----------------------------------- *)
lemma sr_ge0 (j : int) : 0%r <= sr j.
proof. by rewrite /sr; case: (1 <= j <= size rankedQ) => _ //; apply ge0_mu. qed.

lemma sr_mono (i j : int) : 1 <= i <= j => sr j <= sr i.
proof.
move=> hij; case: (j <= size rankedQ) => hj; last by rewrite {1}/sr; smt(sr_ge0).
rewrite /sr (_ : 1 <= j <= size rankedQ) 1:/# (_ : 1 <= i <= size rankedQ) 1:/# /=.
apply (sorted_nth (fun (u w : pp) => mu1 dQ w <= mu1 dQ u) rankedQ witness (i - 1) (j - 1)).
- smt().
- smt().
- by apply sort_sorted => u w /=; smt().
smt().
qed.

lemma mu1_s1 (v : pp) : mu1 dQ v <= s1.
proof. by rewrite -sr_index /s1; apply sr_mono; smt(index_ge0). qed.

lemma s1_ge0 : 0%r <= s1 by rewrite /s1; apply sr_ge0.

(* The chance that the passphrase completes a logged S query at the state x. *)
op wS (sq : (state * pp) list) (x : state) : real = mu dQ (fun q => (x, q) \in sq).

(* With a uniform first half, a state hits a logged S query with the real passphrase with chance at
   most s_1 * 2^-128 per query. *)
lemma Ep_wS (sq : (state * pp) list) (a b : W128.word) :
  Ep W128.DWord.dunifin (fun x => (wS sq (a +^ x, b))%xr) <= (s1 * (size sq)%r * e128)%xr.
proof.
have -> : Ep W128.DWord.dunifin (fun x => (wS sq (a +^ x, b))%xr) =
          Ep (W128.DWord.dunifin `*` dQ) (fun (z : W128.word * pp) => (((a +^ z.`1, b), z.`2) \in sq)%xr).
- rewrite dprod_dlet Ep_dlet; apply eq_Ep => x _ /=.
  rewrite Ep_dlet /wS -Ep_mu; apply eq_Ep => q _ /=.
  by rewrite Ep_dunit.
rewrite Ep_mu; apply xle_rle; split; 1: by apply ge0_mu.
move=> _; pose L := map (fun (e : state * pp) => (e.`1.`1 +^ a, e.`2))
                        (filter (fun (e : state * pp) => e.`1.`2 = b) sq).
apply (ler_trans (mu (W128.DWord.dunifin `*` dQ) (mem L))).
- apply mu_le => -[x q] _ /= h; rewrite /L mapP; exists ((a +^ x, b), q).
  by rewrite mem_filter h /= (xorC a x) -xorA xorK xor0.
apply (ler_trans ((size L)%r * (e128 * s1))).
- apply mu_mem_le_mu1 => -[x q]; rewrite dprod1E dhalf1 -/e128.
  by apply ler_wpmul2l; [smt(e128_gt0) | apply mu1_s1].
have hL : size L <= size sq by rewrite /L size_map size_filter count_size.
rewrite (_ : s1 * (size sq)%r * e128 = (size sq)%r * (e128 * s1)) 1:/#.
by apply ler_wpmul2r; [smt(e128_gt0 s1_ge0) | smt()].
qed.

(* For a chain without Early: complete, it scores W of its end state if the adversary did not query
   its last point; before that, the fresh mask of the last round is still to come. *)
op psiW (W : state -> real) (B : real) (log : (point * int) list) (st : cst) : real =
  if st.`early then 0%r
  else if st.`fin then (if last witness st.`chain \in map fst log then 0%r else W st.`xs)
  else B * e128.

(* A fresh answer at the last point of the chain keeps the potential in expectation. *)
lemma Ep_psiW (W : state -> real) B log (m : (point, ans) fmap) p st c :
  (forall x, 0%r <= W x) => 0%r <= B =>
  (forall a b, Ep W128.DWord.dunifin (fun x => (W (a +^ x, b))%xr) <= (B * e128)%xr) =>
  Ep dans (fun r => (psiW W B log (cstep true p st c true r [] m.[c <- r]))%xr) <= (psiW W B log st)%xr.
proof.
move=> hW hB hE.
case: (!st.`early /\ !st.`fin /\ last witness st.`chain = c) => [[hea [hfin hl]] | hno]; last first.
- rewrite (eq_Ep _ _ (fun _ => (psiW W B log st)%xr)) => [r _ /= | ]; 2: by rewrite EpC dans_ll smul1m.
  case: (st.`early) => hea; 1: by rewrite /psiW hea (early_mono _ _ _ _ _ _ _ _ hea).
  by rewrite /cstep (_ : !(true /\ !st.`fin /\ last witness st.`chain = c)) 1:/#.
case: (!isA c /\ !isB c /\ !(0 < st.`ri)) => [[hA [hBc hri]] | hmore].
- (* the last answer: L_0 = R_1 + M_0 with a fresh mask M_0 *)
  apply (xle_trans (Ep dans (fun r => (W (st.`oth +^ mask_of r, st.`cur))%xr))).
  + apply le_Ep => r _ /=; apply le_pos.
    rewrite /cstep hfin hl /= hBc hA /= hri /= /psiW /= hea.
    by case: (last witness st.`chain \in map fst log) => _ //=; apply hW.
  have := Ep_dmap dans mask_of (fun x => (W (st.`oth +^ x, st.`cur))%xr).
  rewrite dans_mask /= => <-.
  by rewrite /psiW hea hfin /=; apply hE.
(* another point of the chain is defined *)
apply (xle_trans (Ep dans (fun _ => (psiW W B log st)%xr))); 2: by rewrite EpC dans_ll smul1m.
apply le_Ep => r _ /=; apply le_pos.
rewrite /cstep hfin hl /= /psiW hea hfin /= /push /=.
by case: (isB c) => hBc /=; [|case: (isA c) => hA /=]; smt(e128_gt0).
qed.

(* After the run, while the budget of S holds. *)
op phiS (kS : int) (sq : (state * pp) list) (log : (point * int) list) (st : cst) : real =
  if size sq <= kS then psiW (wS sq) (s1 * (size sq)%r) log st else 0%r.

lemma phiS_ge0 kS sq log st : 0%r <= phiS kS sq log st.
proof. by rewrite /phiS /psiW /wS; smt(ge0_mu e128_gt0 s1_ge0 size_ge0). qed.

(* After the run a query keeps the potential: only the real chain's step moves it. *)
lemma query_gS kS :
  ehoare [Mon.query : (!Mon.inrun /\ pend = []) `|` (phiS kS WithP.sq Mon.log (Bwd.sts Bwd.p))%xr ==>
                      (!Mon.inrun) `|` (phiS kS WithP.sq Mon.log (Bwd.sts Bwd.p))%xr].
proof.
proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hp]; rewrite hi hp /= ?if_same.
case: (c{hr} \in R.RO.m{hr}) => hc /=.
- rewrite (eq_Ep _ _ (fun _ => (phiS kS WithP.sq{hr} Mon.log{hr} (Bwd.sts{hr} Bwd.p{hr}))%xr)).
  + by move=> r _ /=; rewrite /cstep.
  by rewrite EpC dans_ll smul1m.
rewrite /phiS; case: (size WithP.sq{hr} <= kS) => hq /=; last by rewrite EpC dans_ll smul1m.
rewrite (eq_Ep _ _ (fun r => (psiW (wS WithP.sq{hr}) (s1 * (size WithP.sq{hr})%r) Mon.log{hr}
           (cstep true Bwd.p{hr} (Bwd.sts{hr} Bwd.p{hr}) c{hr} true r [] R.RO.m{hr}.[c{hr} <- r]))%xr)).
- by move=> r _ /=; rewrite get_set_sameE oget_some.
apply Ep_psiW.
- by move=> x; apply ge0_mu.
- by apply mulr_ge0; [apply s1_ge0 | smt(size_ge0)].
by move=> a b; apply Ep_wS.
qed.

lemma mon_b_gS kS : ehoare [Mon.b :
  (!Mon.inrun) `|` (phiS kS WithP.sq Mon.log (Bwd.sts Bwd.p))%xr ==>
  (!Mon.inrun) `|` (phiS kS WithP.sq Mon.log (Bwd.sts Bwd.p))%xr].
proof. by proc; call (query_gS kS); auto. qed.

lemma mon_a_gS kS : ehoare [Mon.a :
  (!Mon.inrun) `|` (phiS kS WithP.sq Mon.log (Bwd.sts Bwd.p))%xr ==>
  (!Mon.inrun) `|` (phiS kS WithP.sq Mon.log (Bwd.sts Bwd.p))%xr].
proof. by proc; call (query_gS kS); auto. qed.

lemma mon_h_gS kS : ehoare [Mon.h :
  (!Mon.inrun) `|` (phiS kS WithP.sq Mon.log (Bwd.sts Bwd.p))%xr ==>
  (!Mon.inrun) `|` (phiS kS WithP.sq Mon.log (Bwd.sts Bwd.p))%xr].
proof. by proc; call (query_gS kS); auto. qed.

lemma dec_gS kS : ehoare [Net(Mon).dec :
  (!Mon.inrun) `|` (phiS kS WithP.sq Mon.log (Bwd.sts Bwd.p))%xr ==>
  (!Mon.inrun) `|` (phiS kS WithP.sq Mon.log (Bwd.sts Bwd.p))%xr].
proof.
proc; while ((!Mon.inrun) `|` (phiS kS WithP.sq Mon.log (Bwd.sts Bwd.p))%xr).
- by move=> &hr; apply xle_cxr_r.
- conseq (_ : ((!Mon.inrun) `|` (phiS kS WithP.sq Mon.log (Bwd.sts Bwd.p))%xr) ==> _).
  + by move=> &hr; apply xle_cxr_r.
  + by move=> &hr; apply xle_cxr_r.
  wp; call (mon_h_gS kS); call (mon_a_gS kS); call (mon_b_gS kS); skip => &hr; apply xlexx.
by auto.
qed.

(* After the decryption the potential covers the seed query without the last point. *)
lemma postS kS sq log (st : cst) (x : state) :
  (if !st.`early /\ !(last witness st.`chain \in map fst log) /\ size sq <= kS /\ st.`fin /\ x = st.`xs
   then wS sq x else 0%r)%xr <= (phiS kS sq log st)%xr.
proof.
case: (!st.`early /\ !(last witness st.`chain \in map fst log) /\ size sq <= kS /\ st.`fin /\ x = st.`xs)
  => [[hea [hl [hq [hfin hx]]]] | _] /=.
- by rewrite /phiS hq /psiW hea hfin /= hl /= hx.
by rewrite /(%pos); smt(phiS_ge0).
qed.

(* At the end of the run the potential is within its bound: a complete chain ends with a point that
   the adversary queried. *)
lemma run_endS kS sq log (st : cst) : 0 <= kS => (st.`fin => last witness st.`chain \in map fst log) =>
  phiS kS sq log st <= s1 * kS%r * e128.
proof.
move=> hkS hf; rewrite /phiS; case: (size sq <= kS) => hq /=; 2: smt(s1_ge0 e128_gt0).
rewrite /psiW; case: (st.`early) => _ /=; 1: smt(s1_ge0 e128_gt0).
case: (st.`fin) => hfin /=; 1: by rewrite (hf hfin) /=; smt(s1_ge0 e128_gt0).
apply ler_wpmul2r; 1: smt(e128_gt0).
by apply ler_wpmul2l; [exact s1_ge0 | smt()].
qed.

(* The last two samplings of Θ2 turn the event into the weight of the end state. *)
lemma Ep_wS_end (sq : (state * pp) list) (x : state) (C : bool) :
  Ep dQ (fun q => Ep dseed (fun (_ : seed) => ((x, q) \in sq /\ C)%xr)) <= (if C then wS sq x else 0%r)%xr.
proof.
rewrite (eq_Ep _ _ (fun q => (((x, q) \in sq) /\ C)%xr)) => [q _ /= | ]; 1: by rewrite EpC dseed_ll smul1m.
rewrite Ep_mu; apply xle_rle; split; 1: by apply ge0_mu.
move=> _; case: C => _ /=; 2: by rewrite mu0_false.
by rewrite /wS lerr.
qed.

(* During the run the guard and a constant potential are kept. *)
lemma query_k (k : real) : ehoare [Mon.query :
  (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` k%xr ==> (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` k%xr].
proof.
proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hf]; rewrite hi /=.
apply (xle_trans (Ep dans (fun _ => k%xr))); 2: by rewrite EpC dans_ll smul1m.
apply le_Ep => r _ /=; case: (c{hr} \in R.RO.m{hr}) => hc /=; apply xle_cxr_l => //;
  exact (fin_logged_step _ _ _ _ _ _ _ _ hf).
qed.

lemma countb_a_k (k : real) : ehoare [CountB(Mon).a :
  (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` k%xr ==> (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` k%xr].
proof. by proc; inline Count(Mon).a Mon.a; wp; call (query_k k); auto. qed.

lemma count_b_k (k : real) : ehoare [Count(Mon).b :
  (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` k%xr ==> (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` k%xr].
proof. by proc; inline Mon.b; wp; call (query_k k); auto. qed.

lemma count_h_k (k : real) : ehoare [Count(Mon).h :
  (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` k%xr ==> (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` k%xr].
proof. by proc; inline Mon.h; wp; call (query_k k); auto. qed.

(* ---- The chains of all passwords, read from a table ------------------------------------------- *)
(* The backward chain of u from Y as the bookkeeping builds it from the table m alone. *)
op chain_of (m : (point, ans) fmap) (u : pw) (y : state) : cst = iter 36 (adv true u m) (cbwd y).

lemma adv_stop bwd p (m : (point, ans) fmap) st : stopped m st => adv bwd p m st = st.
proof. by rewrite /adv => ->. qed.

lemma iter_stop bwd p (m : (point, ans) fmap) st0 n : 0 <= n => stopped m (iter n (adv bwd p m) st0) =>
  forall j, 0 <= j => iter (n + j) (adv bwd p m) st0 = iter n (adv bwd p m) st0.
proof.
move=> hn hs j; elim: j => [|j hj ih]; 1: by [].
by rewrite (_ : n + (j + 1) = (n + j) + 1) 1:/# iterS 1:/# ih adv_stop.
qed.

lemma pos_le (c : point) : 0 <= pos c <= 2 by case: c.

lemma shape_adv p (m : (point, ans) fmap) st : shape true p st => shape true p (adv true p m st).
proof. by rewrite /adv; case: (stopped m st) => // _; apply shape_cstep. qed.

lemma shape_iter p (m : (point, ans) fmap) y n : 0 <= n => shape true p (iter n (adv true p m) (cbwd y)).
proof.
elim: n => [|n hn ih]; 1: by rewrite iter0 //; apply shape_bwd.
by rewrite iterS // shape_adv.
qed.

(* Every step that is not stopped adds a point or completes the chain. *)
op meas (st : cst) : int = size st.`chain + b2i st.`fin.

lemma meas_adv p (m : (point, ans) fmap) st : !stopped m st => meas (adv true p m st) = meas st + 1.
proof.
rewrite /stopped negb_or => -[hfin hl]; rewrite /adv /stopped hfin hl /= /cstep hfin /=.
rewrite /meas /push hfin /b2i /=.
case: (isB (last witness st.`chain)) => _ /=; 1: by rewrite size_rcons.
case: (isA (last witness st.`chain)) => _ /=; 1: by rewrite size_rcons.
by case: (0 < st.`ri) => _ /=; rewrite ?size_rcons.
qed.

lemma meas_le p st : shape true p st => meas st <= 37.
proof. by rewrite /meas /shape /ndone /b2i; smt(pos_le). qed.

lemma meas_iter p m y n : 0 <= n =>
  (forall k, 0 <= k < n => !stopped m (iter k (adv true p m) (cbwd y))) =>
  meas (iter n (adv true p m) (cbwd y)) = n + 1.
proof.
elim: n => [|n hn ih] htr; 1: by rewrite iter0 // /meas /cbwd /b2i.
have hs : !stopped m (iter n (adv true p m) (cbwd y)) by apply htr; smt().
by rewrite iterS // meas_adv // ih // => k hk; apply htr; smt().
qed.

(* A chain read from a table stops within 36 steps. *)
lemma iter_bound p m y n : 0 <= n =>
  (forall k, 0 <= k < n => !stopped m (iter k (adv true p m) (cbwd y))) => n <= 36.
proof.
move=> hn htr; have := meas_iter p m y n hn htr.
by have := meas_le p _ (shape_iter p m y n hn); smt().
qed.

(* Without Early, the bookkeeping is the chain read from the table. *)
lemma determined_chain p (m : (point, ans) fmap) y st :
  determined true p m (cbwd y) st => strip st = strip (chain_of m p y).
proof.
move=> [n [hn [hst [htr hstop]]]].
have hn36 := iter_bound p m y n hn htr.
have hs : stopped m (iter n (adv true p m) (cbwd y)) by rewrite -stopped_strip -hst stopped_strip.
by rewrite /chain_of (_ : 36 = n + (36 - n)) 1:/# (iter_stop _ _ _ _ _ hn hs (36 - n)) 1:/#.
qed.

(* The chain only grows. *)
lemma adv_prefix p (m : (point, ans) fmap) st : exists s, (adv true p m st).`chain = st.`chain ++ s.
proof.
rewrite /adv; case: (stopped m st) => _; 1: by exists []; rewrite cats0.
case: (cstep_cases true p st (last witness st.`chain) true (oget m.[last witness st.`chain]) [] m)
  => [[_ ->] | [_ [_ [_ [[q [-> _]] | [-> _]]]]]].
- by exists []; rewrite cats0.
- by exists [q]; rewrite cats1.
by exists []; rewrite cats0.
qed.

lemma iter_prefix p (m : (point, ans) fmap) y k n : 0 <= k <= n =>
  exists s, (iter n (adv true p m) (cbwd y)).`chain = (iter k (adv true p m) (cbwd y)).`chain ++ s.
proof.
move=> [hk hkn].
have h : forall j, 0 <= j => exists s,
  (iter (k + j) (adv true p m) (cbwd y)).`chain = (iter k (adv true p m) (cbwd y)).`chain ++ s.
- elim=> [|j hj [s hs]]; 1: by exists []; rewrite cats0.
  rewrite (_ : k + (j + 1) = (k + j) + 1) 1:/# iterS 1:/#.
  have [t ht] := adv_prefix p m (iter (k + j) (adv true p m) (cbwd y)).
  by exists (s ++ t); rewrite ht hs catA.
have [s hs] := h (n - k) _; 1: smt().
by exists s; move: hs; rewrite (_ : k + (n - k) = n) 1:/#.
qed.

(* One step reads only the last point. *)
lemma adv_agree2 p (m1 m2 : (point, ans) fmap) st :
  (st.`fin \/ (last witness st.`chain \in m1 /\ m2.[last witness st.`chain] = m1.[last witness st.`chain])) =>
  strip (adv true p m1 st) = strip (adv true p m2 st).
proof.
move=> [hf | [hl he]]; 1: by rewrite /adv /stopped hf.
have hl2 : last witness st.`chain \in m2 by rewrite domE he -domE.
rewrite /adv /stopped hl hl2 /= he.
by case: (st.`fin) => // _; apply strip_cstep_tab.
qed.

(* Two tables that agree on every point the chain reads give the same chain, Early aside. *)
lemma chain_of_agree p (m m' : (point, ans) fmap) y :
  (forall x, x \in m => m'.[x] = m.[x]) =>
  (chain_of m' p y).`fin => all (fun c => c \in m) (chain_of m' p y).`chain =>
  strip (chain_of m p y) = strip (chain_of m' p y).
proof.
move=> hagr hfin hall.
have h : forall n, 0 <= n => n <= 36 =>
  strip (iter n (adv true p m) (cbwd y)) = strip (iter n (adv true p m') (cbwd y)).
- elim=> [_ | n hn ih hn36]; 1: by rewrite !iter0.
  rewrite !iterS // adv_strip ih 1:/# -adv_strip; apply adv_agree2.
  case: ((iter n (adv true p m') (cbwd y)).`fin) => [// | _]; right.
  have [s hs] := iter_prefix p m' y n 36 _; 1: smt().
  have hl : last witness (iter n (adv true p m') (cbwd y)).`chain \in m.
  + move: hall; rewrite allP /chain_of hs => /(_ (last witness (iter n (adv true p m') (cbwd y)).`chain)).
    apply; rewrite mem_cat; left; apply last_mem.
    by have [_ [hne _]] := shape_iter p m' y n hn.
  by split => //; apply hagr.
by rewrite /chain_of h.
qed.

(* In a chain read from a table, an H point follows the A point whose answer is its key. *)
op keyH (c : point) : W256.word = with c = PA _ => witness with c = PB _ => witness with c = PH x => x.`1.

op keyinv (m : (point, ans) fmap) (p : pw) (ch : point list) =
  forall j, 1 <= j < size ch => !isA (nth witness ch j) => !isB (nth witness ch j) =>
    (exists s, nth witness ch (j - 1) = PA (p, s)) /\
    keyH (nth witness ch j) = key_of (oget m.[nth witness ch (j - 1)]).

lemma keyinv_rcons m p (ch : point list) q : keyinv m p ch => ch <> [] =>
  (!isA q => !isB q =>
   (exists s, last witness ch = PA (p, s)) /\ keyH q = key_of (oget m.[last witness ch])) =>
  keyinv m p (rcons ch q).
proof.
move=> hk hne hq j; rewrite size_rcons => -[hj1 hj].
case: (j < size ch) => hjs.
- by rewrite !nth_rcons hjs (_ : j - 1 < size ch) 1:/# /=; apply hk.
have -> : j = size ch by smt().
by rewrite !nth_rcons /= (_ : size ch - 1 < size ch) 1:/# /= nth_last.
qed.

lemma keyinv_adv p (m : (point, ans) fmap) st : shape true p st => keyinv m p st.`chain =>
  keyinv m p (adv true p m st).`chain.
proof.
move=> hsh hk; rewrite /adv; case: (stopped m st) => hs //.
move: hs; rewrite /stopped negb_or => -[hfin hlm].
have [_ [hne [_ [_ [hall _]]]]] := hsh.
rewrite /cstep hfin /=.
case: (isB (last witness st.`chain)) => hB /=.
- by rewrite /push /=; apply keyinv_rcons => //; rewrite /isA.
case: (isA (last witness st.`chain)) => hA /=.
- rewrite /push /=; apply keyinv_rcons => // _ _; split; 2: done.
  move: (hall); rewrite allP => /(_ (last witness st.`chain) (last_mem _ hne)) /(_ hA).
  by case: (last witness st.`chain) => // -[q s] /= ->; exists s.
case: (0 < st.`ri) => hri /=; 2: by [].
by rewrite /push /=; apply keyinv_rcons => //; rewrite /isB.
qed.

lemma iter_keyH p (m : (point, ans) fmap) y n : 0 <= n =>
  forall j, 1 <= j < size (iter n (adv true p m) (cbwd y)).`chain =>
    let ch = (iter n (adv true p m) (cbwd y)).`chain in
    !isA (nth witness ch j) => !isB (nth witness ch j) =>
    (exists s, nth witness ch (j - 1) = PA (p, s)) /\
    keyH (nth witness ch j) = key_of (oget m.[nth witness ch (j - 1)]).
proof.
move=> hn; have h : keyinv m p (iter n (adv true p m) (cbwd y)).`chain.
- elim: n hn => [|n hn ih]; 1: by rewrite iter0 // /cbwd /keyinv /= => j /#.
  by rewrite iterS //; apply keyinv_adv => //; apply shape_iter.
exact h.
qed.

(* Coll_P: another password u has its whole chain queried no later than the chain of P and inverts Y
   to the same state. The moments are the adversary's calls. *)
op coll (m : (point, ans) fmap) (log : (point * int) list) (p : pw) (y : state) =
  exists u, u <> p /\
    (chain_of m u y).`fin /\ (chain_of m p y).`fin /\
    all (fun c => c \in map fst log) (chain_of m u y).`chain /\
    all (fun c => c \in map fst log) (chain_of m p y).`chain /\
    (exists c, c \in (chain_of m p y).`chain /\
               all (fun c' => bnof log c' <= bnof log c) (chain_of m u y).`chain) /\
    (chain_of m u y).`xs = (chain_of m p y).`xs.

(* Two tables that agree on the chain read in the first, complete one give the same chain. *)
lemma chain_of_same p (m1 m2 : (point, ans) fmap) y :
  (chain_of m1 p y).`fin =>
  (forall x, x \in (chain_of m1 p y).`chain => x \in m1 /\ m2.[x] = m1.[x]) =>
  strip (chain_of m1 p y) = strip (chain_of m2 p y).
proof.
move=> hfin hagr.
have h : forall n, 0 <= n => n <= 36 =>
  strip (iter n (adv true p m1) (cbwd y)) = strip (iter n (adv true p m2) (cbwd y)).
- elim=> [_ | n hn ih hn36]; 1: by rewrite !iter0.
  rewrite !iterS // (adv_strip _ _ m2) -ih 1:/# -(adv_strip _ _ m2); apply adv_agree2.
  case: ((iter n (adv true p m1) (cbwd y)).`fin) => [// | _]; right.
  have [s hs] := iter_prefix p m1 y n 36 _; 1: smt().
  apply hagr; rewrite /chain_of hs mem_cat; left; apply last_mem.
  by have [_ [hne _]] := shape_iter p m1 y n hn.
by rewrite /chain_of h.
qed.

(* ---- Lemma W4 ---------------------------------------------------------------------------------- *)
(* The two events behind Coll_P for the chain st of w. col1: the chain of another password, queried
   completely before the last point of st, inverts to the same first half. col2: the key K_0 at the
   A point c_35 of st equals the key of another queried A point. *)
op col1 (m : (point, ans) fmap) (log : (point * int) list) (w : pw) (y : state) (st : cst) =
  last witness st.`chain \in map fst log /\
  exists u, u <> w /\ (chain_of m u y).`fin /\
    all (fun c => c \in map fst log /\ bnof log c < bnof log (last witness st.`chain)) (chain_of m u y).`chain /\
    (chain_of m u y).`xs.`1 = st.`xs.`1.

op col2 (m : (point, ans) fmap) (log : (point * int) list) (st : cst) =
  exists a, a \in map fst log /\ isA a /\ a <> nth witness st.`chain 34 /\
    key_of (oget m.[a]) = key_of (oget m.[nth witness st.`chain 34]).

(* The risk left for the chain of w: a later last mask, and a later or present key K_0. *)
op psiC (kA ca : int) (m : (point, ans) fmap) (log : (point * int) list) (w : pw) (y : state) (st : cst) : real =
  if st.`early then 0%r
  else (if st.`fin then b2r (col1 m log w y st) else kA%r * e128)
     + (if 36 <= size st.`chain then b2r (col2 m log st) + (kA - ca)%r * e256 else kA%r * e256).

op phiC (kA ca : int) (inrun : bool) (m : (point, ans) fmap) (log : (point * int) list) (y : state)
        (sts : pw -> cst) : real =
  if inrun /\ ca <= kA then Bigreal.BRA.big predT (fun w => mu1 dP w * psiC kA ca m log w y (sts w)) PwT.enum
  else 0%r.

lemma psiC_ge0 kA ca m log w y st : 0 <= kA => ca <= kA => 0%r <= psiC kA ca m log w y st.
proof. by move=> hk0 hca; rewrite /psiC; smt(e128_gt0 e256_gt0). qed.

(* The first halves of the inverted states of the chains completed and queried before. *)
op done1 (m : (point, ans) fmap) (log : (point * int) list) (w : pw) (y : state) : W128.word list =
  map (fun u => (chain_of m u y).`xs.`1)
    (filter (fun u => u <> w /\ (chain_of m u y).`fin /\ all (fun c => c \in map fst log) (chain_of m u y).`chain)
       PwT.enum).

(* The keys of the queried A points. *)
op keysA (m : (point, ans) fmap) (log : (point * int) list) : W256.word list =
  map (fun a => key_of (oget m.[a])) (filter isA (map fst log)).

op apw (c : point) : pw = with c = PA x => x.`1 with c = PB _ => witness with c = PH _ => witness.

(* A complete chain read from a table carries A points of its password. *)
lemma chain_of_A m u y : (chain_of m u y).`fin => exists a, a \in (chain_of m u y).`chain /\ isA a /\ apw a = u.
proof.
move=> hfin; have hsh := shape_iter u m y 36 _; 1: by [].
have [_ [hne [_ [hcnt [hall [hf _]]]]]] := hsh; have [hn hp] := hf hfin.
have : has isA (chain_of m u y).`chain by rewrite has_count -/(chain_of _ _ _) hcnt hn hp /b2i.
move=> /List.hasP [a [ha hA]]; exists a; rewrite ha hA /=.
by move/allP: hall => /(_ a ha hA); case: a ha hA.
qed.

lemma done1_size m log w y : size (done1 m log w y) <= count isA (map fst log).
proof.
rewrite /done1 size_map.
apply (IntOrder.ler_trans (size (undup (map apw (filter isA (map fst log)))))); last first.
- by rewrite -size_filter; apply (IntOrder.ler_trans _ _ _ (size_undup _)); rewrite size_map.
apply uniq_leq_size; 1: by apply filter_uniq; exact PwT.enum_uniq.
move=> u; rewrite mem_filter mem_undup => -[[_ [hfin hall]] _].
have [a [ha [hA hu]]] := chain_of_A m u y hfin.
by rewrite mapP; exists a; rewrite mem_filter hA /= -hu /=; move/allP: hall; apply.
qed.

(* A log with the same points and the same first moments leaves both events. *)
lemma col_same_log (m : (point, ans) fmap) log log' w y st :
  (forall x, x \in map fst log' <=> x \in map fst log) =>
  (forall x, x \in map fst log => bnof log' x = bnof log x) =>
  col1 m log' w y st = col1 m log w y st /\ col2 m log' st = col2 m log st.
proof.
move=> hmem hbn; split; 2: by rewrite /col2; apply eq_iff; split => -[a ha]; exists a; smt().
rewrite /col1; apply eq_iff; split => -[hl [u [hu [hf [ha hx]]]]];
  (split; 1: smt()); exists u; rewrite hu hf hx /=; move: ha; rewrite !allP => ha c hc;
  have := ha c hc; smt().
qed.

(* A fresh query at a point outside the chains leaves a complete chain's col1 unchanged. *)
lemma col1_fresh (m : (point, ans) fmap) log bn w y st c r :
  (forall x, x \in m <=> x \in map fst log) => all (fun (e : point * int) => e.`2 <= bn) log =>
  c \notin m => last witness st.`chain \in map fst log =>
  col1 m.[c <- r] (rcons log (c, bn + 1)) w y st = col1 m log w y st.
proof.
move=> hml hbn cm hl.
have hcl : !(c \in map fst log) by rewrite -hml.
have hb : forall x, x \in map fst log => bnof (rcons log (c, bn + 1)) x = bnof log x.
- by move=> x hx; rewrite bnof_rcons hx.
have hlb : bnof log (last witness st.`chain) <= bn by apply (bnof_le _ _ _ hl hbn).
have hagr : forall x, x \in map fst log => x \in m /\ m.[c <- r].[x] = m.[x].
- move=> x hx; have hxm : x \in m by rewrite hml.
  by rewrite hxm /=; smt(get_set_neqE).
rewrite /col1; apply eq_iff; split => -[hl' [u [hu [hf [ha hx]]]]]; split => //.
- have hin : forall x, x \in (chain_of m.[c <- r] u y).`chain => x \in map fst log.
  + move=> x hxc; move/allP: ha => /(_ x hxc) /= [hxl hlt]; move: hxl; rewrite map_rcons mem_rcons /=.
    case=> // hxc'; move: hlt; rewrite hxc' (hb _ hl) bnof_rcons hcl /=; smt().
  have he := chain_of_same u m.[c <- r] m y hf _.
  + move=> x hxc; have [hxm hxe] := hagr x (hin x hxc).
    by rewrite mem_set hxm /= hxe.
  have [ec [ef [_ [_ [_ ex]]]]] := strip_eq _ _ he.
  exists u; rewrite hu -ef hf -ex hx /= -ec.
  apply/allP => x hxc; have hxl := hin x hxc; move/allP: ha => /(_ x hxc) /= [_].
  by rewrite (hb _ hxl) (hb _ hl) hxl.
- by rewrite map_rcons mem_rcons /= hl'.
have he := chain_of_same u m m.[c <- r] y hf _.
- by move=> x hxc; move/allP: ha => /(_ x hxc) /= [hxl _]; apply hagr.
have [ec [ef [_ [_ [_ ex]]]]] := strip_eq _ _ he.
exists u; rewrite hu -ef hf -ex hx /= -ec.
apply/allP => x hxc; move/allP: ha => /(_ x hxc) /= [hxl hlt].
by rewrite map_rcons mem_rcons /= hxl /= (hb _ hxl) (hb _ hl').
qed.

(* The last answer of the chain of w: col1 needs the fresh first half among done1. *)
lemma col1_final (m : (point, ans) fmap) log bn w y (st : cst) c r :
  (forall x, x \in m <=> x \in map fst log) => all (fun (e : point * int) => e.`2 <= bn) log =>
  c \notin m => last witness st.`chain = c =>
  col1 m.[c <- r] (rcons log (c, bn + 1)) w y st => st.`xs.`1 \in done1 m log w y.
proof.
move=> hml hbn cm hl [_ [u [hu [hf [ha hx]]]]].
have hcl : !(c \in map fst log) by rewrite -hml.
have hlb : bnof (rcons log (c, bn + 1)) c = bn + 1 by rewrite bnof_rcons hcl.
have hin : forall x, x \in (chain_of m.[c <- r] u y).`chain => x \in map fst log.
- move=> x hxc; move/allP: ha => /(_ x hxc) /= [hxl hlt]; move: hxl; rewrite map_rcons mem_rcons /=.
  case=> // hxc'; move: hlt; rewrite hxc' hl hlb /=; smt().
have he := chain_of_same u m.[c <- r] m y hf _.
- move=> x hxc; have hxm : x \in m by rewrite hml; apply hin.
  by rewrite mem_set hxm /=; smt(get_set_neqE).
have [ec [ef [_ [_ [_ ex]]]]] := strip_eq _ _ he.
rewrite /done1 mapP; exists u; rewrite mem_filter PwT.enumP /= hu -ef hf -ex hx /=.
by apply/allP => x hxc; apply hin; rewrite ec.
qed.

(* A query that is not a fresh A point leaves col2 of a chain whose c_35 is answered. *)
lemma col2_nonA (m : (point, ans) fmap) log b st c r :
  (forall x, x \in m <=> x \in map fst log) => nth witness st.`chain 34 \in m =>
  (c \in m \/ !isA c) =>
  col2 (if c \in m then m else m.[c <- r]) (rcons log (c, b)) st => col2 m log st.
proof.
move=> hml h34 hc [a [ha [hA [hne he]]]]; exists a.
have hlm : forall x, x \in map fst log => x \in m by move=> x; rewrite hml.
have hal : a \in map fst log.
- move: ha; rewrite map_rcons mem_rcons /= => -[hac | //].
  case: hc => [hcm | hnA]; 1: by rewrite -hml hac.
  by move: hA; rewrite hac => /#.
rewrite hal hA hne /=; move: he; case: (c \in m) => hcm //=.
have hac : a <> c by smt().
have h34c : nth witness st.`chain 34 <> c by smt().
by rewrite !get_set_neqE.
qed.

(* A fresh A query: col2 of a chain whose c_35 is answered needs its key to be K_0. *)
lemma col2_freshA (m : (point, ans) fmap) log b st c r :
  (forall x, x \in map fst log => x \in m) => nth witness st.`chain 34 \in m => c \notin m =>
  col2 m.[c <- r] (rcons log (c, b)) st =>
  col2 m log st \/ key_of r = key_of (oget m.[nth witness st.`chain 34]).
proof.
move=> hlm h34 cm [a [ha [hA [hne he]]]].
have h34c : nth witness st.`chain 34 <> c by smt().
case: (a = c) => hac.
- by right; move: he; rewrite hac get_set_sameE get_set_neqE.
left; exists a; have hal : a \in map fst log by move: ha; rewrite map_rcons mem_rcons /= hac.
by rewrite hal hA hne /=; move: he; rewrite !get_set_neqE // => hac'; move: (hlm _ hal); rewrite hac' cm.
qed.

(* The answer at c_35: col2 of the new chain needs the fresh key among the queried keys. *)
lemma col2_c35 (m : (point, ans) fmap) log log' (st : cst) c r :
  (forall x, x \in map fst log => x \in m) => c \notin m => nth witness st.`chain 34 = c =>
  (forall a, a \in map fst log' => a = c \/ a \in map fst log) =>
  col2 m.[c <- r] log' st => key_of r \in keysA m log.
proof.
move=> hlm cm h34 hlog [a [ha [hA [hne he]]]].
have hal : a \in map fst log by have := hlog a ha; rewrite -h34 hne.
have hac : a <> c by rewrite -h34.
move: he; rewrite h34 get_set_sameE get_set_neqE // /= => <-.
by rewrite /keysA mapP; exists a; rewrite mem_filter hA hal.
qed.


lemma Ep_cb_le ['a] (d : 'a distr) (F : 'a -> real) (C : real) (Q : 'a -> bool) (B : real) :
  is_lossless d => 0%r <= C => (forall x, F x <= C + b2r (Q x)) => C + mu d Q <= B =>
  Ep d (fun x => (F x)%xr) <= B%xr.
proof.
move=> hd hC hF hB.
apply (xle_trans (Ep d (fun x => (C + b2r (Q x))%xr))).
- by apply le_Ep => x _ /=; apply le_pos; apply hF.
rewrite (Ep_cb d C Q hd hC); apply xle_rle; split; 2: by [].
by apply addr_ge0; [exact hC | apply ge0_mu].
qed.

(* One query of the adversary's run, for the chain of one password. *)
lemma Ep_C_w kA ca (m : (point, ans) fmap) log bn y w (st : cst) c : 0 <= kA =>
  shape true w st => (forall x, x \in m <=> x \in map fst log) =>
  all (fun (e : point * int) => e.`2 <= bn) log => count isA (map fst log) <= ca =>
  (st.`fin => last witness st.`chain \in map fst log) =>
  (!st.`early => forall t, 0 <= t < size st.`chain - 1 => nth witness st.`chain t \in m) =>
  ca + b2i (isA c) <= kA =>
  Ep dans (fun r => (psiC kA (ca + b2i (isA c)) (if c \in m then m else m.[c <- r]) (rcons log (c, bn + 1)) w y
                       (cstep true w st c (c \notin m) (if c \in m then oget m.[c] else r) []
                          (if c \in m then m else m.[c <- r])))%xr)
  <= (psiC kA ca m log w y st)%xr.
proof.
move=> hk0 hsh hml hbn hca hfl hans hk.
have hlm : forall x, x \in map fst log => x \in m by move=> x; rewrite hml.
have he128 := e128_gt0; have he256 := e256_gt0.
have [hri [hne [hsz [hcnt [hall [hf hlr]]]]]] := hsh.
case: (c \in m) => cm /=.
- (* a repeated point: no chain moves, the log gains a point it has *)
  have hcl : c \in map fst log by rewrite -hml.
  have [e1 e2] := col_same_log m log (rcons log (c, bn + 1)) w y st _ _.
  + by move=> x; rewrite map_rcons mem_rcons /= /#.
  + by move=> x hx; rewrite bnof_rcons hx.
  apply (Ep_cb_le _ _ (psiC kA (ca + b2i (isA c)) m (rcons log (c, bn + 1)) w y st) pred0) => //.
  + exact dans_ll.
  + by apply psiC_ge0.
  rewrite mu0 /= /psiC e1 e2; case: (st.`early) => //= _.
  by rewrite /b2i; case: (isA c) => _ /=; smt().
(* a fresh point *)
case: (st.`early) => hea.
- apply (Ep_cb_le _ _ 0%r pred0) => //; 1: exact dans_ll.
  + by move=> r /=; rewrite /psiC (early_mono _ _ _ _ _ _ _ _ hea).
  by rewrite mu0 /psiC hea.
have hcl : !(c \in map fst log) by rewrite -hml.
have h34 : 36 <= size st.`chain => nth witness st.`chain 34 \in m.
- by move=> h36; apply (hans hea 34); smt().
case: (!st.`fin /\ last witness st.`chain = c) => [[hfin hl] | hno]; last first.
- (* the chain does not move; col2 may gain the fresh key of an A query *)
  pose C := (if st.`fin then b2r (col1 m log w y st) else kA%r * e128)
          + (if 36 <= size st.`chain then b2r (col2 m log st) + (kA - (ca + b2i (isA c)))%r * e256
             else kA%r * e256).
  apply (Ep_cb_le _ _ C (fun r => 36 <= size st.`chain /\ isA c /\
                                  key_of r = key_of (oget m.[nth witness st.`chain 34]))) => //.
  + exact dans_ll.
  + by rewrite /C; smt().
  + move=> r /=; have -> : cstep true w st c true r [] m.[c <- r] = st by rewrite /cstep /#.
    rewrite /psiC hea /= /C.
    have -> : (if st.`fin then b2r (col1 m.[c <- r] (rcons log (c, bn + 1)) w y st) else kA%r * e128) =
              (if st.`fin then b2r (col1 m log w y st) else kA%r * e128).
    * by case: (st.`fin) => // hfi; rewrite (col1_fresh m log bn w y st c r hml hbn cm (hfl hfi)).
    case: (36 <= size st.`chain) => h36 /=; last by smt().
    case: (isA c) => hA /=.
    * have := col2_freshA m log (bn + 1) st c r hlm (h34 h36) cm.
      by case: (col2 m.[c <- r] (rcons log (c, bn + 1)) st) => /= _; smt().
    have := col2_nonA m log (bn + 1) st c r hml (h34 h36) _; 1: by right.
    by rewrite cm /=; case: (col2 m.[c <- r] (rcons log (c, bn + 1)) st) => /= _; smt().
  rewrite /C /psiC hea /=; case: (36 <= size st.`chain) => h36 /=; last by rewrite mu0_false; smt().
  case: (isA c) => hA /=; last by rewrite mu0_false; smt().
  rewrite (dans_key (fun k => k = key_of (oget m.[nth witness st.`chain 34]))) /= dkey1 -/e256 /b2i /=; smt().
(* the chain of w moves: c is its last point, answered fresh *)
rewrite /psiC hea hfin /=.
case: (isB c) => hB.
- (* a B point: the next point is the A point of the round *)
  apply (Ep_cb_le _ _ (kA%r * e128 + kA%r * e256) pred0) => //; 1: exact dans_ll; 1: smt().
  + move=> r /=; rewrite /cstep hfin hl /= hB /= /push /= size_rcons.
    have hpos : pos (last witness st.`chain) = 0 by rewrite hl; apply posB.
    by move: hsz; rewrite hpos /ndone /=; smt().
  have hpos : pos (last witness st.`chain) = 0 by rewrite hl; apply posB.
  by rewrite mu0 (_ : !(36 <= size st.`chain)) /=; smt().
case: (isA c) => hA.
- have hpos : pos (last witness st.`chain) = 1 by rewrite hl; apply posA.
  case: (st.`ri = 0) => hri0.
  + (* the A point c_35: its key K_0 is fresh *)
    apply (Ep_cb_le _ _ (kA%r * e128 + (kA - (ca + 1))%r * e256) (fun r => key_of r \in keysA m log)) => //.
    * exact dans_ll.
    * smt().
    * move=> r /=; rewrite /cstep hfin hl /= hB hA /= /push /= size_rcons hea /=.
      have h34' : nth witness (rcons st.`chain (PH (key_of r, rd st.`ri, st.`cur))) 34 = c.
      - by rewrite nth_rcons (_ : 34 < size st.`chain) /=; 1: smt(); rewrite -hl -(nth_last witness); smt().
      have hc35 : forall (st' : cst), nth witness st'.`chain 34 = c =>
                    col2 m.[c <- r] (rcons log (c, bn + 1)) st' => key_of r \in keysA m log.
      - move=> st' h; apply (col2_c35 m log (rcons log (c, bn + 1)) st' c r hlm cm h).
        by move=> a; rewrite map_rcons mem_rcons /=.
      by move: hsz; rewrite /ndone /b2i /=; smt().
    rewrite (dans_key (fun k => k \in keysA m log)) /= (_ : !(36 <= size st.`chain)) /=; 1: smt().
    have : mu W256.DWord.dunifin (mem (keysA m log)) <= (size (keysA m log))%r * e256.
    * by apply mu_mem_le_mu1 => k; rewrite dkey1.
    have : size (keysA m log) <= count isA (map fst log) by rewrite /keysA size_map size_filter.
    move=> hs hmu.
    have : (size (keysA m log))%r * e256 <= (ca + 1)%r * e256.
    * by apply ler_wpmul2r; [smt(e256_gt0) | rewrite le_fromint; smt()].
    smt().
  (* an earlier A point *)
  apply (Ep_cb_le _ _ (kA%r * e128 + kA%r * e256) pred0) => //; 1: exact dans_ll; 1: smt().
  + move=> r /=; rewrite /cstep hfin hl /= hB hA /= /push /= size_rcons.
    by move: hsz; rewrite hpos /ndone /=; smt().
  by rewrite mu0 (_ : !(36 <= size st.`chain)) /=; smt().
have hpos : pos (last witness st.`chain) = 2 by rewrite hl; apply posH.
case: (0 < st.`ri) => hri0.
- (* an H point of an earlier round *)
  apply (Ep_cb_le _ _ (kA%r * e128 + kA%r * e256) pred0) => //; 1: exact dans_ll; 1: smt().
  + move=> r /=; rewrite /cstep hfin hl /= hB hA /= hri0 /= /push /= size_rcons.
    by move: hsz; rewrite hpos /ndone /=; smt().
  by rewrite mu0 (_ : !(36 <= size st.`chain)) /=; smt().
(* c_36: the last mask; col1 needs L_0 among the earlier completed chains *)
have h36 : 36 <= size st.`chain by smt().
apply (Ep_cb_le _ _ (b2r (col2 m log st) + (kA - ca)%r * e256)
                    (fun r => st.`oth +^ mask_of r \in done1 m log w y)) => //.
- exact dans_ll.
- by smt().
- move=> r /=; rewrite /cstep hfin hl /= hB hA /= hri0 /= h36 /= /b2i /=.
  have hc1 := col1_final m log bn w y {| st with fin = true; xs = (st.`oth +^ mask_of r, st.`cur) |} c r
                hml hbn cm hl.
  have hc2 := col2_nonA m log (bn + 1) {| st with fin = true; xs = (st.`oth +^ mask_of r, st.`cur) |} c r hml
                (h34 h36) _; 1: by right.
  move: hc1 hc2; rewrite cm /=.
  case: (col1 m.[c <- r] (rcons log (c, bn + 1)) w y {| st with fin = true; xs = (st.`oth +^ mask_of r, st.`cur) |});
  case: (col2 m.[c <- r] (rcons log (c, bn + 1)) {| st with fin = true; xs = (st.`oth +^ mask_of r, st.`cur) |});
  rewrite /=; smt().
rewrite h36 /= (dans_maskE (fun x => st.`oth +^ x \in done1 m log w y)) (dhalf_shift _ (mem (done1 m log w y))).
have : mu W128.DWord.dunifin (mem (done1 m log w y)) <= (size (done1 m log w y))%r * e128.
- by apply mu_mem_le_mu1 => x; rewrite dhalf1.
have := done1_size m log w y.
move=> hds hmu.
have : (size (done1 m log w y))%r * e128 <= kA%r * e128.
- by apply ler_wpmul2r; [smt(e128_gt0) | rewrite le_fromint; smt()].
smt().
qed.

(* ---- The run: all passwords at once ------------------------------------------------------------ *)
(* What the run keeps: the chains' shapes, the table holds exactly the logged points, the batch
   numbers, the A count, complete chains end with a logged point, and the answered points. *)
op gC (m : (point, ans) fmap) (log : (point * int) list) (bn ca : int) (sts : pw -> cst) =
  (forall w, shape true w (sts w)) /\
  (forall x, x \in m <=> x \in map fst log) /\
  all (fun (e : point * int) => e.`2 <= bn) log /\
  count isA (map fst log) <= ca /\
  fin_logged log sts /\
  (forall w, !(sts w).`early => forall t, 0 <= t < size (sts w).`chain - 1 => nth witness (sts w).`chain t \in m).

(* The answered points stay answered. *)
lemma ans_step w (st : cst) c fresh r (m m' : (point, ans) fmap) :
  (forall x, x \in m => x \in m') => (fresh => c \in m') =>
  (!st.`early => forall t, 0 <= t < size st.`chain - 1 => nth witness st.`chain t \in m) =>
  let st' = cstep true w st c fresh r [] m' in
  !st'.`early => forall t, 0 <= t < size st'.`chain - 1 => nth witness st'.`chain t \in m'.
proof.
move=> hmm hc hans /=; case: (cstep_cases true w st c fresh r [] m') => [[_ ->] | [hfr [_ [hl hcs]]]].
- by move=> hea t ht; apply hmm; apply hans.
case: hcs => [[q [hch [hea' _]]] | [hch [hea' _]]].
- rewrite hch hea' size_rcons => hne t ht; rewrite nth_rcons (_ : t < size st.`chain) /=; 1: smt().
  case: (t < size st.`chain - 1) => htl; 1: by apply hmm; apply hans => //; smt().
  by rewrite (_ : t = size st.`chain - 1) 1:/# nth_last hl; apply hc.
by rewrite hch hea' => hne t ht; apply hmm; apply hans.
qed.

lemma gC_step (m : (point, ans) fmap) log bn ca sts c r :
  gC m log bn ca sts =>
  let m' = if c \in m then m else m.[c <- r] in
  gC m' (rcons log (c, bn + 1)) (bn + 1) (ca + b2i (isA c))
     (fun w => cstep true w (sts w) c (c \notin m) (if c \in m then oget m.[c] else r) [] m').
proof.
move=> [hsh [hml [hbn [hcnt [hfl hans]]]]] /=.
have hmm : forall x, x \in m => x \in (if c \in m then m else m.[c <- r]) by move=> x; case: (c \in m) => //; rewrite mem_set => _ ->.
do! split.
- by move=> w /=; apply shape_cstep; apply hsh.
- move=> x; rewrite map_rcons mem_rcons /=; case: (c \in m) => hc /=; 1: smt().
  by rewrite mem_set; smt().
- by rewrite all_rcons1 /=; move: hbn; rewrite !allP => h e he /=; have := h e he; smt().
- by rewrite map_rcons count_rcons1 /=; smt().
- exact (fin_logged_step _ _ _ _ _ _ _ _ hfl).
move=> w; have hc : c \notin m => c \in (if c \in m then m else m.[c <- r]).
- by case: (c \in m) => //; rewrite mem_set.
have /= h := ans_step w (sts w) c (c \notin m) (if c \in m then oget m.[c] else r) m
               (if c \in m then m else m.[c <- r]) hmm hc (hans w).
exact h.
qed.

lemma Ep_C_run1 kA ca ca' (m : (point, ans) fmap) log bn y sts c : 0 <= kA =>
  gC m log bn ca sts => ca' = ca + b2i (isA c) =>
  Ep dans (fun r =>
    if c \notin m then
      (gC m.[c <- r] (rcons log (c, bn + 1)) (bn + 1) ca'
          (fun w => cstep true w (sts w) c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r])) `|`
      (phiC kA ca' true m.[c <- r] (rcons log (c, bn + 1)) y
          (fun w => cstep true w (sts w) c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r]))%xr
    else
      (gC m (rcons log (c, bn + 1)) (bn + 1) ca' (fun w => cstep true w (sts w) c (c \notin m) (oget m.[c]) [] m)) `|`
      (phiC kA ca' true m (rcons log (c, bn + 1)) y (fun w => cstep true w (sts w) c (c \notin m) (oget m.[c]) [] m))%xr)
  <= (phiC kA ca true m log y sts)%xr.
proof.
move=> hk0 hg ->; have [hsh [hml [hbn [hcnt [hfl hans]]]]] := hg.
rewrite (eq_Ep _ _ (fun r => (phiC kA (ca + b2i (isA c)) true (if c \in m then m else m.[c <- r]) (rcons log (c, bn + 1)) y
            (fun w => cstep true w (sts w) c (c \notin m) (if c \in m then oget m.[c] else r) []
                        (if c \in m then m else m.[c <- r])))%xr)) => [r _ /= | ].
- have := gC_step m log bn ca sts c r hg; rewrite /=.
  by case: (c \in m) => hc /= hg'; rewrite ?get_set_sameE ?oget_some /= hg'.
rewrite /phiC /=; case: (ca + b2i (isA c) <= kA) => hk /=; last by rewrite EpC dans_ll smul1m; smt().
have hca : ca <= kA by smt(b2i_ge0).
rewrite hca /=; rewrite -(RField.addr0 (Bigreal.BRA.big _ _ _)).
rewrite (eq_Ep _ _ (fun r => (Bigreal.BRA.big predT (fun w => mu1 dP w *
            psiC kA (ca + b2i (isA c)) (if c \in m then m else m.[c <- r]) (rcons log (c, bn + 1)) w y
              (cstep true w (sts w) c (c \notin m) (if c \in m then oget m.[c] else r) []
                 (if c \in m then m else m.[c <- r]))) PwT.enum + 0%r)%xr)) => [r _ /= // | ].
apply (Ep_sum_le dans (fun w r => psiC kA (ca + b2i (isA c)) (if c \in m then m else m.[c <- r]) (rcons log (c, bn + 1)) w y
              (cstep true w (sts w) c (c \notin m) (if c \in m then oget m.[c] else r) []
                 (if c \in m then m else m.[c <- r])))
                         (fun w => psiC kA ca m log w y (sts w)) 0%r PwT.enum) => //.
- exact dans_ll.
- by move=> w r; apply psiC_ge0.
- by move=> w; apply psiC_ge0.
move=> w; apply (Ep_C_w kA ca m log bn y w (sts w) c hk0 (hsh w) hml hbn hcnt _ (hans w) hk).
by apply hfl.
qed.

lemma countb_a_C kA : 0 <= kA => ehoare [CountB(Mon).a :
  (Mon.inrun /\ gC R.RO.m Mon.log Mon.bn Count.ca Bwd.sts) `|`
  (phiC kA Count.ca Mon.inrun R.RO.m Mon.log Bwd.y Bwd.sts)%xr ==>
  (Mon.inrun /\ gC R.RO.m Mon.log Mon.bn Count.ca Bwd.sts) `|`
  (phiC kA Count.ca Mon.inrun R.RO.m Mon.log Bwd.y Bwd.sts)%xr].
proof.
move=> hk0; proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hg]; rewrite hi /=.
by apply (Ep_C_run1 _ _ _ _ _ _ _ _ _ hk0 hg); rewrite /b2i.
qed.

lemma count_b_C kA : 0 <= kA => ehoare [Count(Mon).b :
  (Mon.inrun /\ gC R.RO.m Mon.log Mon.bn Count.ca Bwd.sts) `|`
  (phiC kA Count.ca Mon.inrun R.RO.m Mon.log Bwd.y Bwd.sts)%xr ==>
  (Mon.inrun /\ gC R.RO.m Mon.log Mon.bn Count.ca Bwd.sts) `|`
  (phiC kA Count.ca Mon.inrun R.RO.m Mon.log Bwd.y Bwd.sts)%xr].
proof.
move=> hk0; proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hg]; rewrite hi /=.
by apply (Ep_C_run1 _ _ _ _ _ _ _ _ _ hk0 hg); rewrite /b2i.
qed.

lemma count_h_C kA : 0 <= kA => ehoare [Count(Mon).h :
  (Mon.inrun /\ gC R.RO.m Mon.log Mon.bn Count.ca Bwd.sts) `|`
  (phiC kA Count.ca Mon.inrun R.RO.m Mon.log Bwd.y Bwd.sts)%xr ==>
  (Mon.inrun /\ gC R.RO.m Mon.log Mon.bn Count.ca Bwd.sts) `|`
  (phiC kA Count.ca Mon.inrun R.RO.m Mon.log Bwd.y Bwd.sts)%xr].
proof.
move=> hk0; proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hg]; rewrite hi /=.
by apply (Ep_C_run1 _ _ _ _ _ _ _ _ _ hk0 hg); rewrite /b2i.
qed.

(* ---- The decryption: the real chain only -------------------------------------------------------- *)
op phiDC (kA ca : int) (m : (point, ans) fmap) (log : (point * int) list) (y : state) (p : pw) (st : cst) : real =
  if ca <= kA then psiC kA ca m log p y st else 0%r.

op gD (m : (point, ans) fmap) (log : (point * int) list) (ca : int) (p : pw) (st : cst) =
  shape true p st /\ (forall x, x \in map fst log => x \in m) /\ count isA (map fst log) <= ca /\
  (!st.`early => forall t, 0 <= t < size st.`chain - 1 => nth witness st.`chain t \in m).

(* A new point outside the logged ones changes neither event. *)
lemma col1_ext (m : (point, ans) fmap) log w y st c r :
  (forall x, x \in map fst log => x \in m) => c \notin m =>
  col1 m.[c <- r] log w y st = col1 m log w y st.
proof.
move=> hlm cm.
have hagr : forall x, x \in map fst log => x \in m /\ m.[c <- r].[x] = m.[x].
- move=> x hx; have hxm := hlm x hx.
  by rewrite hxm /=; smt(get_set_neqE).
rewrite /col1; apply eq_iff; split => -[hl [u [hu [hfu [hau hx]]]]]; (split; 1: by []); exists u; rewrite hu /=.
- have he := chain_of_same u m.[c <- r] m y hfu _.
  + move=> x hxc; move/allP: hau => /(_ x hxc) /= [hxl _]; have [hxm hxe] := hagr x hxl.
    by rewrite mem_set hxm /= hxe.
  have [ec [ef [_ [_ [_ ex]]]]] := strip_eq _ _ he.
  by rewrite -ef hfu -ex hx -ec /=.
have he := chain_of_same u m m.[c <- r] y hfu _.
- by move=> x hxc; move/allP: hau => /(_ x hxc) /= [hxl _]; apply hagr.
have [ec [ef [_ [_ [_ ex]]]]] := strip_eq _ _ he.
by rewrite -ef hfu -ex hx -ec /=.
qed.

lemma col2_ext (m : (point, ans) fmap) log st c r :
  (forall x, x \in map fst log => x \in m) => c \notin m => nth witness st.`chain 34 \in m =>
  col2 m.[c <- r] log st = col2 m log st.
proof.
move=> hlm cm h34.
have hne : forall x, x \in m => x <> c by smt().
have hn34 := hne _ h34.
rewrite /col2; apply eq_iff; split => -[a [ha [hA [hna he]]]]; exists a; have hac := hne a (hlm a ha).
- by move: he; rewrite !get_set_neqE // => he; do !split.
by rewrite !get_set_neqE //; do !split.
qed.

(* One query of the decryption. *)
lemma b2r_le (a b : bool) : (a => b) => b2r a <= b2r b.
proof. by rewrite /#. qed.

lemma Ep_DC_1 kA ca (m : (point, ans) fmap) log y p (st : cst) c : 0 <= kA =>
  gD m log ca p st =>
  Ep dans (fun r => (phiDC kA ca (if c \in m then m else m.[c <- r]) log y p
                       (cstep true p st c (c \notin m) (if c \in m then oget m.[c] else r) []
                          (if c \in m then m else m.[c <- r])))%xr)
  <= (phiDC kA ca m log y p st)%xr.
proof.
move=> hk0 [hsh [hlm [hca hans]]].
have he128 := e128_gt0; have he256 := e256_gt0.
rewrite /phiDC; case: (ca <= kA) => hk /=; last by rewrite EpC dans_ll smul1m.
have [hri [hne [hsz [hcnt [hall [hf hlr]]]]]] := hsh.
case: (c \in m) => cm /=.
- by rewrite (eq_Ep _ _ (fun _ => (psiC kA ca m log p y st)%xr)) => [r _ /= | ]; [rewrite /cstep | rewrite EpC dans_ll smul1m].
case: (st.`early) => hea.
- apply (Ep_cb_le _ _ 0%r pred0) => //; 1: exact dans_ll.
  + by move=> r /=; rewrite /psiC (early_mono _ _ _ _ _ _ _ _ hea).
  by rewrite mu0 /psiC hea.
have h34 : 36 <= size st.`chain => nth witness st.`chain 34 \in m.
- by move=> h36; apply (hans hea 34); smt().
case: (!st.`fin /\ last witness st.`chain = c) => [[hfin hl] | hno]; last first.
- (* the chain does not move: both events are unchanged *)
  have hid : forall r, cstep true p st c true r [] m.[c <- r] = st by move=> r; rewrite /cstep /#.
  rewrite (eq_Ep _ _ (fun _ => (psiC kA ca m log p y st)%xr)) => [r _ /= | ]; 2: by rewrite EpC dans_ll smul1m.
  rewrite hid /psiC hea /= (col1_ext m log p y st c r hlm cm).
  by case: (36 <= size st.`chain) => h36 //=; rewrite (col2_ext m log st c r hlm cm (h34 h36)).
(* the real chain moves *)
rewrite /psiC hea hfin /=.
case: (isB c) => hB.
- apply (Ep_cb_le _ _ (kA%r * e128 + kA%r * e256) pred0) => //; 1: exact dans_ll; 1: smt().
  + move=> r /=; rewrite /cstep hfin hl /= hB /= /push /= size_rcons.
    have hpos : pos (last witness st.`chain) = 0 by rewrite hl; apply posB.
    by move: hsz; rewrite hpos /ndone /=; smt().
  have hpos : pos (last witness st.`chain) = 0 by rewrite hl; apply posB.
  by rewrite mu0 (_ : !(36 <= size st.`chain)) /=; smt().
case: (isA c) => hA.
- have hpos : pos (last witness st.`chain) = 1 by rewrite hl; apply posA.
  case: (st.`ri = 0) => hri0.
  + (* c_35 answered by the decryption: its key may meet a queried key *)
    apply (Ep_cb_le _ _ (kA%r * e128 + (kA - ca)%r * e256) (fun r => key_of r \in keysA m log)) => //.
    * exact dans_ll.
    * smt().
    * move=> r /=; rewrite /cstep hfin hl /= hB hA /= /push /= size_rcons hea /=.
      have h34' : nth witness (rcons st.`chain (PH (key_of r, rd st.`ri, st.`cur))) 34 = c.
      - by rewrite nth_rcons (_ : 34 < size st.`chain) /=; 1: smt(); rewrite -hl -(nth_last witness); smt().
      have hc35 : forall (st' : cst), nth witness st'.`chain 34 = c =>
                    col2 m.[c <- r] log st' => key_of r \in keysA m log.
      - move=> st' h; apply (col2_c35 m log log st' c r hlm cm h).
        by move=> a ha; right.
      have hcol : col2 m.[c <- r] log {| st with chain = rcons st.`chain (PH (key_of r, rd st.`ri, st.`cur));
                                                early = PH (key_of r, rd st.`ri, st.`cur) \in m.[c <- r] |} =>
                  key_of r \in keysA m log.
      - by apply hc35.
      move: hsz; rewrite /ndone /= => hsz.
      rewrite (_ : 36 <= size st.`chain + 1) 1:/# /=.
      case: (PH (key_of r, rd st.`ri, st.`cur) \in m.[c <- r]) => hin /=; 1: smt(b2r_ge0).
      by move: hcol; rewrite hin /= => /b2r_le; rewrite hfin /=; smt().
    rewrite (dans_key (fun k => k \in keysA m log)) /= (_ : !(36 <= size st.`chain)) /=; 1: smt().
    have : mu W256.DWord.dunifin (mem (keysA m log)) <= (size (keysA m log))%r * e256.
    * by apply mu_mem_le_mu1 => k; rewrite dkey1.
    have : size (keysA m log) <= count isA (map fst log) by rewrite /keysA size_map size_filter.
    move=> h1 h2; have h3 : (size (keysA m log))%r * e256 <= ca%r * e256 by apply ler_wpmul2r; smt().
    have : kA%r * e256 = (kA - ca)%r * e256 + ca%r * e256 by rewrite fromintB; ring.
    smt().
  apply (Ep_cb_le _ _ (kA%r * e128 + kA%r * e256) pred0) => //; 1: exact dans_ll; 1: smt().
  + move=> r /=; rewrite /cstep hfin hl /= hB hA /= /push /= size_rcons.
    by move: hsz; rewrite hpos /ndone /=; smt().
  by rewrite mu0 (_ : !(36 <= size st.`chain)) /=; smt().
have hpos : pos (last witness st.`chain) = 2 by rewrite hl; apply posH.
case: (0 < st.`ri) => hri0.
- apply (Ep_cb_le _ _ (kA%r * e128 + kA%r * e256) pred0) => //; 1: exact dans_ll; 1: smt().
  + move=> r /=; rewrite /cstep hfin hl /= hB hA /= hri0 /= /push /= size_rcons.
    by move: hsz; rewrite hpos /ndone /=; smt().
  by rewrite mu0 (_ : !(36 <= size st.`chain)) /=; smt().
(* c_36 answered by the decryption: not logged, so col1 fails; col2 is unchanged *)
have h36 : 36 <= size st.`chain by smt().
apply (Ep_cb_le _ _ (b2r (col2 m log st) + (kA - ca)%r * e256) pred0) => //.
- exact dans_ll.
- by smt().
- move=> r /=; rewrite /cstep hfin hl /= hB hA /= hri0 /= h36 /=.
  have -> : col1 m.[c <- r] log p y {| st with fin = true; xs = (st.`oth +^ mask_of r, st.`cur) |} = false.
  + by rewrite /col1 /= hl neqF; apply/negP => -[hcl _]; move: (hlm c hcl); rewrite cm.
  have -> : col2 m.[c <- r] log {| st with fin = true; xs = (st.`oth +^ mask_of r, st.`cur) |} = col2 m log st.
  + by rewrite -(col2_ext m log st c r hlm cm (h34 h36)) /col2.
  by rewrite /=; smt().
by rewrite mu0 /=; smt().
qed.

lemma Ep_DC_run kA ca (m : (point, ans) fmap) log y p (st : cst) c : 0 <= kA =>
  gD m log ca p st =>
  Ep dans (fun r => if c \notin m then
      gD m.[c <- r] log ca p (cstep true p st c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r]) `|`
      (phiDC kA ca m.[c <- r] log y p (cstep true p st c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r]))%xr
    else
      gD m log ca p (cstep true p st c (c \notin m) (oget m.[c]) [] m) `|`
      (phiDC kA ca m log y p (cstep true p st c (c \notin m) (oget m.[c]) [] m))%xr)
  <= (phiDC kA ca m log y p st)%xr.
proof.
move=> hk0 hg; have [hsh [hlm [hca hans]]] := hg.
rewrite (eq_Ep _ _ (fun r => (phiDC kA ca (if c \in m then m else m.[c <- r]) log y p
            (cstep true p st c (c \notin m) (if c \in m then oget m.[c] else r) []
               (if c \in m then m else m.[c <- r])))%xr)) => [r _ /= | ].
- have hmm : forall x, x \in m => x \in (if c \in m then m else m.[c <- r]).
  + by move=> x; case: (c \in m) => //; rewrite mem_set => _ ->.
  have hg' : gD (if c \in m then m else m.[c <- r]) log ca p
               (cstep true p st c (c \notin m) (if c \in m then oget m.[c] else r) [] (if c \in m then m else m.[c <- r])).
  + split; 1: by apply shape_cstep.
    split; 1: by move=> x hx; apply hmm; apply hlm.
    split; 1: exact hca.
    have := ans_step p st c (c \notin m) (if c \in m then oget m.[c] else r) m
              (if c \in m then m else m.[c <- r]) hmm _ hans.
    * by case: (c \in m) => //; rewrite mem_set.
    by move=> /=.
  by move: hg'; case: (c \in m) => hc /= hg'; rewrite ?get_set_sameE ?oget_some hg'.
exact (Ep_DC_1 kA ca m log y p st c hk0 hg).
qed.

lemma mon_b_DC kA : 0 <= kA => ehoare [Mon.b :
  (!Mon.inrun /\ gD R.RO.m Mon.log Count.ca Bwd.p (Bwd.sts Bwd.p)) `|`
  (phiDC kA Count.ca R.RO.m Mon.log Bwd.y Bwd.p (Bwd.sts Bwd.p))%xr ==>
  (!Mon.inrun /\ gD R.RO.m Mon.log Count.ca Bwd.p (Bwd.sts Bwd.p)) `|`
  (phiDC kA Count.ca R.RO.m Mon.log Bwd.y Bwd.p (Bwd.sts Bwd.p))%xr].
proof.
move=> hk0; proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hg]; rewrite hi /= ?if_same.
exact (Ep_DC_run _ _ _ _ _ _ _ _ hk0 hg).
qed.

lemma mon_a_DC kA : 0 <= kA => ehoare [Mon.a :
  (!Mon.inrun /\ gD R.RO.m Mon.log Count.ca Bwd.p (Bwd.sts Bwd.p)) `|`
  (phiDC kA Count.ca R.RO.m Mon.log Bwd.y Bwd.p (Bwd.sts Bwd.p))%xr ==>
  (!Mon.inrun /\ gD R.RO.m Mon.log Count.ca Bwd.p (Bwd.sts Bwd.p)) `|`
  (phiDC kA Count.ca R.RO.m Mon.log Bwd.y Bwd.p (Bwd.sts Bwd.p))%xr].
proof.
move=> hk0; proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hg]; rewrite hi /= ?if_same.
exact (Ep_DC_run _ _ _ _ _ _ _ _ hk0 hg).
qed.

lemma mon_h_DC kA : 0 <= kA => ehoare [Mon.h :
  (!Mon.inrun /\ gD R.RO.m Mon.log Count.ca Bwd.p (Bwd.sts Bwd.p)) `|`
  (phiDC kA Count.ca R.RO.m Mon.log Bwd.y Bwd.p (Bwd.sts Bwd.p))%xr ==>
  (!Mon.inrun /\ gD R.RO.m Mon.log Count.ca Bwd.p (Bwd.sts Bwd.p)) `|`
  (phiDC kA Count.ca R.RO.m Mon.log Bwd.y Bwd.p (Bwd.sts Bwd.p))%xr].
proof.
move=> hk0; proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hg]; rewrite hi /= ?if_same.
exact (Ep_DC_run _ _ _ _ _ _ _ _ hk0 hg).
qed.

lemma dec_C kA : 0 <= kA => ehoare [Net(Mon).dec :
  (!Mon.inrun /\ gD R.RO.m Mon.log Count.ca Bwd.p (Bwd.sts Bwd.p)) `|`
  (phiDC kA Count.ca R.RO.m Mon.log Bwd.y Bwd.p (Bwd.sts Bwd.p))%xr ==>
  (!Mon.inrun /\ gD R.RO.m Mon.log Count.ca Bwd.p (Bwd.sts Bwd.p)) `|`
  (phiDC kA Count.ca R.RO.m Mon.log Bwd.y Bwd.p (Bwd.sts Bwd.p))%xr].
proof.
move=> hk0; proc; while ((!Mon.inrun /\ gD R.RO.m Mon.log Count.ca Bwd.p (Bwd.sts Bwd.p)) `|`
             (phiDC kA Count.ca R.RO.m Mon.log Bwd.y Bwd.p (Bwd.sts Bwd.p))%xr).
- by move=> &hr; apply xle_cxr_r.
- conseq (_ : ((!Mon.inrun /\ gD R.RO.m Mon.log Count.ca Bwd.p (Bwd.sts Bwd.p)) `|`
               (phiDC kA Count.ca R.RO.m Mon.log Bwd.y Bwd.p (Bwd.sts Bwd.p))%xr) ==> _).
  + by move=> &hr; apply xle_cxr_r.
  + by move=> &hr; apply xle_cxr_r.
  wp; call (mon_h_DC kA hk0); call (mon_a_DC kA hk0); call (mon_b_DC kA hk0); skip => &hr; apply xlexx.
by auto.
qed.

(* Drawing P after the run: the potential of the run is the expected potential of the real chain. *)
lemma run_decC kA ca (m : (point, ans) fmap) log bn y (sts : pw -> cst) (inrun : bool) : 0 <= kA =>
  Ep dP (fun p => (!false /\ gD m log ca p (sts p)) `|` (phiDC kA ca m log y p (sts p))%xr) <=
  (inrun /\ gC m log bn ca sts) `|` (phiC kA ca inrun m log y sts)%xr.
proof.
move=> hk0; apply xle_cxr_r => -[hi hg]; have [hsh [hml [hbn [hcnt [hfl hans]]]]] := hg.
rewrite (eq_Ep _ _ (fun p => (phiDC kA ca m log y p (sts p))%xr)) => [p _ /= | ].
- have -> // : gD m log ca p (sts p) = true.
  rewrite eqT; split; 1: by apply hsh.
  split; 1: by move=> x; rewrite hml.
  by split; [exact hcnt | apply hans].
rewrite (Ep_fin PwT.enum) ?PwT.enum_uniq; 1: by move=> p _; apply PwT.enumP.
have hd : forall p, 0%r <= phiDC kA ca m log y p (sts p).
- by move=> p; rewrite /phiDC; case: (ca <= kA) => // hk; apply psiC_ge0.
rewrite (BXA.eq_bigr _ _ (fun p => (mu1 dP p * phiDC kA ca m log y p (sts p))%xr)).
- by move=> p _ /=; rewrite -(of_realM _ _ (ge0_mu dP (pred1 p)) (hd p)).
rewrite bigXR; 1: by move=> p _; have := hd p; have := ge0_mu dP (pred1 p); smt().
apply xle_rle; split; 1: by apply Bigreal.sumr_ge0 => p _ /=; have := hd p; have := ge0_mu dP (pred1 p); smt().
rewrite /phiC /phiDC hi /=; case: (ca <= kA) => hk /=; last by rewrite Bigreal.BRA.big1_eq.
smt().
qed.

(* After the decryption the potential covers both events for the real chain. *)
lemma postC kA ca m log y p (st : cst) : 0 <= kA => shape true p st =>
  ((col1 m log p y st \/ col2 m log st) /\ !st.`early /\ st.`fin /\ ca <= kA)%xr <= (phiDC kA ca m log y p st)%xr.
proof.
move=> hk0 hsh; have [hri [hne [hsz [hcnt [hall [hf hlr]]]]]] := hsh.
case: ((col1 m log p y st \/ col2 m log st) /\ !st.`early /\ st.`fin /\ ca <= kA) => [[hc [hea [hfin hk]]] | _].
- have [hn hp] := hf hfin.
  have h36 : 36 <= size st.`chain by rewrite hsz hn hp.
  rewrite /phiDC hk /psiC hea hfin h36; apply rp_le.
  by case: hc => hc; rewrite hc /=; smt(e256_gt0).
apply rp_le; rewrite /=.
by rewrite /phiDC; case: (ca <= kA) => // hk; apply psiC_ge0.
qed.

(* ---- From Coll_P to the two events ---------------------------------------------------------- *)
(* In an ordered chain whose points were all queried, the last one was queried last. *)
lemma ordered_last log (ch : point list) : ch <> [] => ordered log ch =>
  all (fun c => c \in map fst log) ch => forall c, c \in ch => bnof log c <= bnof log (last witness ch).
proof.
move=> hne hord hall.
have h : forall k, 0 <= k => k < size ch => bnof log (nth witness ch (size ch - 1 - k)) <= bnof log (last witness ch).
- elim=> [_ | k hk ih hks]; 1: by rewrite (_ : size ch - 1 - 0 = size ch - 1) 1:/# nth_last.
  have := hord (size ch - 1 - k) _ _; 1: smt().
  + by move/allP: hall; apply; apply mem_nth; smt().
  rewrite (_ : size ch - 1 - k - 1 = size ch - 1 - (k + 1)) 1:/# => -[_ hlt].
  by have := ih _; smt().
move=> c hc; have := h (size ch - 1 - index c ch) _ _; 1,2: smt(index_ge0 index_mem).
by rewrite (_ : size ch - 1 - (size ch - 1 - index c ch) = index c ch) 1:/# nth_index.
qed.

(* With one logged query per call, the first moments of two logged points tell them apart. *)
lemma bnof_inj log x y : uniq (map snd log) => x \in map fst log => y \in map fst log =>
  bnof log x = bnof log y => x = y.
proof.
rewrite /bnof => hu hx hy he.
have hix : 0 <= index x (map fst log) < size log by rewrite index_ge0 -(size_map fst) index_mem.
have hiy : 0 <= index y (map fst log) < size log by rewrite index_ge0 -(size_map fst) index_mem.
have hi : index x (map fst log) = index y (map fst log).
- case: (index x (map fst log) = index y (map fst log)) => // hne.
  move/nth_uniqP: hu => /(_ (index x (map fst log)) (index y (map fst log)) _ _ hne); 1,2: by rewrite size_map.
  by rewrite !(nth_map witness) // he.
by rewrite -(nth_index witness x (map fst log)) // -(nth_index witness y (map fst log)) // hi.
qed.

(* Coll_P without Early_P, with the last point of the chain of P queried, is col1 or col2. *)
lemma coll_split (m : (point, ans) fmap) log p y (st : cst) :
  uniq (map snd log) => !st.`early => st.`fin => ordered log st.`chain =>
  strip st = strip (chain_of m p y) => shape true p st =>
  coll m log p y => last witness st.`chain \in map fst log =>
  col1 m log p y st \/ col2 m log st.
proof.
move=> hu hea hfin hord hdet hsh [u [hu' [hfu [hfp [hau [hap [[c [hc hle]] hx]]]]]]] hl.
have [ec [ef [_ [_ [_ ex]]]]] := strip_eq _ _ hdet.
have [_ [hne [hsz [_ [_ [hf _]]]]]] := hsh; have [hn hp] := hf hfin.
have h36 : size st.`chain = 36 by rewrite hsz hn hp.
have hallp : all (fun c => c \in map fst log) st.`chain by rewrite ec.
have hmax : forall c', c' \in (chain_of m u y).`chain => bnof log c' <= bnof log (last witness st.`chain).
- move=> c' hc'; have := ordered_last log st.`chain hne hord hallp c _; 1: by rewrite ec.
  by move/allP: hle => /(_ c' hc') /=; smt().
case: (all (fun c' => bnof log c' < bnof log (last witness st.`chain)) (chain_of m u y).`chain) => hlt.
- left; split => //; exists u; rewrite hu' hfu /= hx -ex /=.
  by apply/allP => c' hc'; move/allP: hau => /(_ c' hc') /= ->; move/allP: hlt => /(_ c' hc').
(* the last point of the chain of P is a point of the chain of u *)
right.
have [c' [hc' heq]] : exists c', c' \in (chain_of m u y).`chain /\ c' = last witness st.`chain.
- move: hlt; rewrite -has_predC => /List.hasP [c' [hc' /= hge]]; exists c'; rewrite hc' /=.
  apply (bnof_inj log) => //; 1: by move/allP: hau; apply.
  by have := hmax c' hc'; smt().
have hlast := last_mem st.`chain hne.
have hH : !isA (last witness st.`chain) /\ !isB (last witness st.`chain).
- by have := hp; case: (last witness st.`chain).
(* in the chain of u, c' follows an A point of u whose key is its key *)
pose j := index c' (chain_of m u y).`chain.
have hj : 0 <= j < size (chain_of m u y).`chain by rewrite index_ge0 index_mem.
have [hHA hHB] := hH.
have hj1 : 1 <= j.
- case: (j = 0) => hj0; 2: smt().
  have [s hs] := iter_prefix u m y 0 36 _; 1: smt().
  have : nth witness (chain_of m u y).`chain j = c' by rewrite nth_index.
  rewrite hj0 /chain_of hs iter0 // /cbwd /=.
  by apply/negP => hc'0; move: hHB; rewrite -heq -hc'0.
have := iter_keyH u m y 36 _ j _; 1: by []; 1: by rewrite -/(chain_of m u y); smt().
rewrite /= -/(chain_of m u y) (nth_index witness c' _ hc') heq => /(_ hHA hHB) -[[s hs] hku].
(* in the chain of P, the last point follows c_35 *)
have := iter_keyH p m y 36 _ 35 _; 1: by []; 1: by rewrite -/(chain_of m p y) -ec h36.
rewrite /= -/(chain_of m p y) -ec (_ : 35 = size st.`chain - 1) 1:/# nth_last.
move=> /(_ hHA hHB) -[[s0 hs0] hkp].
exists (nth witness (chain_of m u y).`chain (j - 1)); split.
- by move/allP: hau; apply; apply mem_nth; smt().
rewrite hs /= hs0 /=; split; 1: smt().
by rewrite -hs -hs0 -hku -hkp.
qed.


(* ---- The pairs that the seed queries assign to passwords --------------------------------------- *)
lemma head_in (s : 'a list) : s <> [] => head witness s \in s by case: s.

(* Sorting reads the order only on the elements of the list. *)
lemma insert_eq_in (e1 e2 : 'a -> 'a -> bool) x s :
  (forall b, b \in s => e1 x b = e2 x b) => InsertSort.insert e1 x s = InsertSort.insert e2 x s.
proof. by elim: s => //= y s ih h; rewrite h // ih // => b hb; apply h; rewrite hb. qed.

lemma sort_eq_in (e1 e2 : 'a -> 'a -> bool) s :
  (forall a b, a \in s => b \in s => e1 a b = e2 a b) => sort e1 s = sort e2 s.
proof.
rewrite !sortE; elim: s => //= x s ih h.
rewrite ih; 1: by move=> a b ha hb; apply h; rewrite ?ha ?hb.
apply insert_eq_in => b hb; apply h => //.
by move: hb; rewrite (perm_eq_mem _ _ (InsertSort.perm_sort e2 s)) => ->.
qed.
(* The first moment at which every point of a chain was queried. *)
op mxb (s0 : int) (log : (point * int) list) (ch : point list) : int = foldr (fun c n => max n (bnof log c)) s0 ch.
op taub (log : (point * int) list) (ch : point list) : int = mxb (bnof log (head witness ch)) log ch.

lemma mxb_ge s0 log ch c : c \in ch => bnof log c <= mxb s0 log ch.
proof. by elim: ch => //= c' ch ih [-> | /ih]; smt(). qed.

lemma mxb_attained s0 log ch : mxb s0 log ch = s0 \/ exists c, c \in ch /\ mxb s0 log ch = bnof log c.
proof.
rewrite /mxb; elim: ch => //= c ch [-> | [c' [hc' ->]]]; 1: smt().
by case: (bnof log c' <= bnof log c) => h; [right; exists c | right; exists c']; smt().
qed.

lemma taub_ge log ch c : c \in ch => bnof log c <= taub log ch.
proof. by apply mxb_ge. qed.

lemma taub_attained log ch : ch <> [] => exists c, c \in ch /\ taub log ch = bnof log c.
proof.
move=> hne; rewrite /taub; case: (mxb_attained (bnof log (head witness ch)) log ch) => [h | //].
by exists (head witness ch); rewrite head_in // h.
qed.

(* Without Early, if the last point of the chain was queried, so were all of them. *)
lemma ordered_all log (chain : point list) : chain <> [] => ordered log chain =>
  last witness chain \in map fst log => all (fun c => c \in map fst log) chain.
proof.
move=> hne; rewrite /ordered => hord hl.
have h : forall k, 0 <= k => k < size chain => nth witness chain (size chain - 1 - k) \in map fst log.
- elim=> [_ | k ge0k ih hk]; 1: by rewrite (_ : size chain - 1 - 0 = size chain - 1) 1:/# nth_last.
  have [+ _] := hord (size chain - 1 - k) _ (ih _); 1,2: smt().
  by rewrite (_ : size chain - 1 - k - 1 = size chain - 1 - (k + 1)) 1:/#.
apply/allP => x hx; have := h (size chain - 1 - index x chain) _ _; 1,2: smt(index_ge0 index_mem).
by rewrite (_ : size chain - 1 - (size chain - 1 - index x chain) = index x chain) 1:/# (nth_index witness x chain hx).
qed.

(* The candidates whose chains, read from the table, are complete and queried. *)
op Uset (m : (point, ans) fmap) (log : (point * int) list) (y : state) : pw list =
  filter (fun u => u \in cands log /\ (chain_of m u y).`fin /\
                   all (fun c => c \in map fst log) (chain_of m u y).`chain) PwT.enum.

(* u(e): among them, the one inverting Y to e with the least first moment, then the least rank. *)
op lexle (a b : int * int) = a.`1 < b.`1 \/ (a.`1 = b.`1 /\ a.`2 <= b.`2).
op keyu (m : (point, ans) fmap) (log : (point * int) list) (y : state) (u : pw) : int * int =
  (taub log (chain_of m u y).`chain, index u ranked).

op uof (m : (point, ans) fmap) (log : (point * int) list) (y : state) (e : state) : pw option =
  let U = filter (fun u => (chain_of m u y).`xs = e) (Uset m log y) in
  if U = [] then None else Some (head witness (sort (fun u v => lexle (keyu m log y u) (keyu m log y v)) U)).

(* Z: the pairs (u(e), v) for the S queries (e, v). *)
op Zset (m : (point, ans) fmap) (log : (point * int) list) (y : state) (sq : (state * pp) list) : (pw * pp) list =
  undup (pmap (fun (ev : state * pp) => omap (fun u => (u, ev.`2)) (uof m log y ev.`1)) sq).

lemma uof_mem m log y e u : uof m log y e = Some u =>
  u \in Uset m log y /\ (chain_of m u y).`xs = e.
proof.
rewrite /uof /=; case: (filter (fun u => (chain_of m u y).`xs = e) (Uset m log y) = []) => // hne /= <-.
have : head witness (sort (fun u v => lexle (keyu m log y u) (keyu m log y v))
                       (filter (fun u => (chain_of m u y).`xs = e) (Uset m log y)))
       \in filter (fun u => (chain_of m u y).`xs = e) (Uset m log y).
- by rewrite -(mem_sort (fun u v => lexle (keyu m log y u) (keyu m log y v))); apply head_in; rewrite -size_eq0 size_sort size_eq0.
by rewrite mem_filter => -[-> ->].
qed.

(* The head of the sorted candidates is below every one of them. *)
lemma uof_least m log y e u : uof m log y e = Some u =>
  forall v, v \in Uset m log y => (chain_of m v y).`xs = e => lexle (keyu m log y u) (keyu m log y v).
proof.
rewrite /uof /=; case: (filter (fun u => (chain_of m u y).`xs = e) (Uset m log y) = []) => // hne /= <- v hv hx.
pose U := filter (fun u => (chain_of m u y).`xs = e) (Uset m log y).
pose r := fun u v => lexle (keyu m log y u) (keyu m log y v).
have hs : sorted r (sort r U) by apply sort_sorted => a b; rewrite /r /lexle; smt().
have hvs : v \in sort r U by rewrite mem_sort /U mem_filter /= hv hx.
have := sorted_nth r (sort r U) witness 0 (index v (sort r U)) _ _ hs _.
- by move=> a b c; rewrite /r /lexle; smt().
- by move=> a; rewrite /r /lexle.
- by rewrite index_ge0 index_mem hvs.
by rewrite nth_index // nth0_head.
qed.

lemma size_pmap_le ['a 'b] (f : 'a -> 'b option) s : size (pmap f s) <= size s.
proof. by elim: s => //= x s ih; case: (f x) => /=; smt(). qed.

lemma Zset_props m log y sq :
  uniq (Zset m log y sq) /\ size (Zset m log y sq) <= size sq /\
  forall z, z \in Zset m log y sq => z.`1 \in cands log.
proof.
split; 1: by apply undup_uniq.
split.
- by apply (IntOrder.ler_trans _ _ _ (size_undup _)); apply size_pmap_le.
move=> z; rewrite /Zset mem_undup pmapP => -[ev [_]] /=.
case _: (uof m log y ev.`1) => // u hu /= -> /=.
by have [+ _] := uof_mem _ _ _ _ _ hu; rewrite /Uset mem_filter => -[[-> _] _].
qed.

(* Lemma W1 for Z: at most kS pairs with passwords in C'. *)
lemma Zset_mass m log y sq kA kS : count isA (map fst log) <= kA => size sq <= kS =>
  mass2 (Zset m log y sq) <= top2 (kA %/ 12) kS.
proof.
move=> hk hs; have [hu [hsz hc]] := Zset_props m log y sq.
apply W1 => //; 1: smt().
apply (IntOrder.ler_trans (size (cands log))).
- by apply uniq_leq_size; [apply undup_uniq | move=> u; rewrite mem_undup mapP => -[z [hz ->]]; apply hc].
have := cands_size log; rewrite lez_divRL //; smt().
qed.

(* On Bad_S without Early_P and N, and without Coll_P, the pair (P, Q) lies in Z. *)
lemma Z_incl (m : (point, ans) fmap) log p y (st : cst) sq q :
  !st.`early => st.`fin => strip st = strip (chain_of m p y) => ordered log st.`chain =>
  st.`chain <> [] => (comp st.`chain log => 12 <= count (isApw p) (undup (map fst log))) =>
  last witness st.`chain \in map fst log => (st.`xs, q) \in sq => !coll m log p y =>
  (p, q) \in Zset m log y sq.
proof.
move=> hea hfin hdet hord hne hcomp hl hsq hnc.
have [ec [ef [_ [_ [_ ex]]]]] := strip_eq _ _ hdet.
have hall := ordered_all log st.`chain hne hord hl.
have hcp : p \in cands log.
- rewrite /cands mem_filter PwT.enumP /=; apply hcomp.
  by rewrite /comp; apply/allP => x; rewrite mem_filter => -[_ hx]; move/allP: hall; apply.
have hpU : p \in Uset m log y by rewrite /Uset mem_filter /= PwT.enumP hcp -ef hfin -ec hall.
have [u hu] : exists u, uof m log y st.`xs = Some u.
- rewrite /uof /=; case: (filter (fun u => (chain_of m u y).`xs = st.`xs) (Uset m log y) = []) => hU /=.
  + have : p \in filter (fun u => (chain_of m u y).`xs = st.`xs) (Uset m log y).
    * by rewrite mem_filter /= hpU -ex.
    by rewrite hU.
  by exists (head witness (sort (fun u v => lexle (keyu m log y u) (keyu m log y v))
                             (filter (fun u => (chain_of m u y).`xs = st.`xs) (Uset m log y)))).
have [huU hux] := uof_mem _ _ _ _ _ hu.
have hle := uof_least _ _ _ _ _ hu p hpU _; 1: by rewrite -ex.
have hup : u = p.
- case: (u = p) => // hne'; move/negP: hnc => hnc'; apply hnc'; rewrite /coll.
  move: huU; rewrite /Uset mem_filter /= => -[[_ [hfu hau]] _].
  exists u; rewrite hne' hfu hau /= -ef hfin -ec hall /= -ex hux /=.
  have [c [hc hcm]] := taub_attained log st.`chain hne.
  exists c; rewrite hc /=; apply/allP => c' hc'.
  have := taub_ge log (chain_of m u y).`chain c' hc'.
  by move: hle; rewrite /keyu /lexle -ec; smt().
rewrite /Zset mem_undup pmapP; exists (st.`xs, q); rewrite hsq /=.
by rewrite hu /= hup.
qed.

(* The decryption only adds points outside the queried chains: Z is a function of the run. *)
lemma Uset_ext (m m' : (point, ans) fmap) log y : (forall x, x \in m => m'.[x] = m.[x]) =>
  (forall x, x \in map fst log => x \in m) =>
  Uset m' log y = Uset m log y /\
  forall u, u \in Uset m log y => strip (chain_of m' u y) = strip (chain_of m u y).
proof.
move=> hagr hlm.
have hfw : forall u, (chain_of m u y).`fin => all (fun c => c \in map fst log) (chain_of m u y).`chain =>
                     strip (chain_of m' u y) = strip (chain_of m u y).
- move=> u hf ha; rewrite (chain_of_same u m m' y hf _) //.
  by move=> x hx; move/allP: ha => /(_ x hx) /= /hlm hxm; rewrite hxm /= hagr.
have hbw : forall u, (chain_of m' u y).`fin => all (fun c => c \in map fst log) (chain_of m' u y).`chain =>
                     strip (chain_of m' u y) = strip (chain_of m u y).
- move=> u hf ha; rewrite -(chain_of_same u m' m y hf _) //.
  move=> x hx; move/allP: ha => /(_ x hx) /= /hlm hxm.
  by have := hagr _ hxm; smt(domE).
split.
- apply List.eq_in_filter => u _ /=; case: (u \in cands log) => //= _; split => -[hf ha].
  + have [ec [ef _]] := strip_eq _ _ (hbw u hf ha); by rewrite -ef hf -ec ha.
  have [ec [ef _]] := strip_eq _ _ (hfw u hf ha); by rewrite ef hf ec ha.
by move=> u; rewrite /Uset mem_filter => -[[_ [hf ha]] _]; apply hfw.
qed.

lemma Zset_ext (m m' : (point, ans) fmap) log y sq : (forall x, x \in m => m'.[x] = m.[x]) =>
  (forall x, x \in map fst log => x \in m) => Zset m' log y sq = Zset m log y sq.
proof.
move=> hagr hlm; have [hU hs] := Uset_ext m m' log y hagr hlm.
have huof : forall e, uof m' log y e = uof m log y e.
- move=> e; rewrite /uof /= hU.
  have -> : filter (fun u => (chain_of m' u y).`xs = e) (Uset m log y) =
            filter (fun u => (chain_of m u y).`xs = e) (Uset m log y).
  + by apply List.eq_in_filter => u hu /=; have [_ [_ [_ [_ [_ ->]]]]] := strip_eq _ _ (hs u hu).
  case: (filter (fun u => (chain_of m u y).`xs = e) (Uset m log y) = []) => //= _.
  rewrite (sort_eq_in (fun u v => lexle (keyu m' log y u) (keyu m' log y v))
                      (fun u v => lexle (keyu m log y u) (keyu m log y v))) //.
  move=> a b /List.mem_filter [_ ha] /List.mem_filter [_ hb].
  by rewrite /= /keyu; have [-> _] := strip_eq _ _ (hs a ha); have [-> _] := strip_eq _ _ (hs b hb).
by rewrite /Zset; congr; apply eq_in_pmap => ev _ /=; rewrite huof.
qed.

lemma top2_ge0 m n : 0%r <= top2 m n.
proof.
rewrite /top2; apply Bigreal.sumr_ge0_seq => x hx _; move: hx => /mem_take; rewrite mem_sort allpairsP => -[[i j] [_ ->]].
by apply mulr_ge0; [apply pr_ge0 | apply sr_ge0].
qed.

(* After the run, P and Q are drawn independently: Pr[(P, Q) in S] is the mass of S. *)
lemma Ep_Z (S : (pw * pp) list) (C : bool) (b : real) : (C => mass2 (undup S) <= b) => 0%r <= b =>
  Ep dP (fun p => Ep dQ (fun q => (((p, q) \in S) /\ C)%xr)) <= b%xr.
proof.
move=> hb hb0.
have -> : Ep dP (fun p => Ep dQ (fun q => (((p, q) \in S) /\ C)%xr)) =
          Ep (dP `*` dQ) (fun (z : pw * pp) => ((z \in S) /\ C)%xr).
- rewrite dprod_dlet Ep_dlet; apply eq_Ep => p _ /=.
  rewrite Ep_dlet; apply eq_Ep => q _ /=.
  by rewrite Ep_dunit.
rewrite Ep_mu; apply xle_rle; split; 1: by apply ge0_mu.
move=> _; case: C hb => [hb | _] /=; last by rewrite mu0_false.
move: hb => /= hb.
have -> : mem S = mem (undup S) by apply fun_ext => z; rewrite mem_undup.
rewrite mu_mem_uniq ?undup_uniq; apply (ler_trans _ _ _ _ hb); rewrite /mass2; apply lerr_eq.
by apply eq_bigr => z _ /=; case: z => p q; rewrite dprod1E.
qed.

(* The mass of Z with one more pair. *)
lemma mass2_cons z S : mass2 (undup (z :: S)) <= mu1 dP z.`1 * mu1 dQ z.`2 + mass2 (undup S).
proof.
rewrite /=; case: (z \in S) => hz /=.
- by have := mulr_ge0 (mu1 dP z.`1) (mu1 dQ z.`2) (ge0_mu _ _) (ge0_mu _ _); smt().
by rewrite /mass2 big_cons /predT /=.
qed.
