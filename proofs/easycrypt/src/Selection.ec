(* The cutoff of the sequential rule and the selection rules that Theorem 5 covers
   (DESIGN-NOTES A.6, "Selection rule"). *)
require import AllCore List Distr DBool DProd FMap IntDiv StdBigop StdOrder Xreal.
require import Suite3 Chain Collision Passphrase Generation.
require (*--*) PROM.
import W128 StdBigop.Bigreal.BRA RealOrder.

(* ---- Selection rules ------------------------------------------------------------------------- *)
(* Any source of trials, with its outcomes recorded in Trials.outs. *)
module Rec (T : TRIALS) = {
  proc trial() : bool = { var b; b <@ T.trial(); Trials.outs <- rcons Trials.outs b; return b; }
}.

(* Given S, T and the passphrase: whether a value passes, and the value of a trial given its outcome
   (made total for any outcome, as a distribution indexed by the trial). *)
op pass (fS : state * pp -> seed) (fT : seed -> W16.word * W240.word) (q : pp) (e : state) : bool =
  (fT (fS (e, q))).`1 = zero16.

op dval (fS : state * pp -> seed) (fT : seed -> W16.word * W240.word) (q : pp) (b : bool) : state distr =
  if b then dcond dstate (pass fS fT q) else dcond dstate (predC (pass fS fT q)).

op dtrial (x : int * bool * ((state * pp -> seed) * (seed -> W16.word * W240.word) * pp)) : state distr =
  if 0%r < mu dstate (fun e => pass x.`3.`1 x.`3.`2 x.`3.`3 e = x.`2)
  then dval x.`3.`1 x.`3.`2 x.`3.`3 x.`2 else dstate.

lemma dtrial_ll x : is_lossless (dtrial x).
proof.
rewrite /dtrial /dval; case: (0%r < mu dstate (fun e => pass x.`3.`1 x.`3.`2 x.`3.`3 e = x.`2)) => h /=.
- by case: (x.`2) h => h /=; apply dcond_ll; apply (ltr_le_trans _ _ _ h); apply/lerr_eq/mu_eq => e /#.
exact dstate_ll.
qed.

(* An outcome drawn with the pass probability has positive probability. *)
lemma dtrial_dval fS fT q j b : b \in Biased.dbiased (mu dstate (pass fS fT q)) =>
  dtrial (j, b, (fS, fT, q)) = dval fS fT q b.
proof.
rewrite supportP Biased.dbiased1E /dtrial /= Biased.clamp_id; 1: smt(ge0_mu le1_mu).
case: b => hb /=.
- have -> : mu dstate (fun e => pass fS fT q e = true) = mu dstate (pass fS fT q) by apply mu_eq => e /#.
  smt(ge0_mu).
have -> : mu dstate (fun e => pass fS fT q e = false) = mu dstate (predC (pass fS fT q)).
- by apply mu_eq => e /#.
rewrite mu_not; have := dstate_ll; rewrite /is_lossless => ->.
smt(ge0_mu le1_mu).
qed.

lemma dval_pass fS fT q b e : e \in dval fS fT q b => pass fS fT q e = b.
proof. by rewrite /dval; case: b => _; rewrite dcond_supp /#. qed.

(* The sequential rule selects its last trial. *)
lemma seq_last (T <: TRIALS {-Trials}) :
  hoare [Seq(Rec(T)).select : Trials.outs = [] ==>
           res = size Trials.outs - 1 /\ 1 <= size Trials.outs].
proof.
proc; while (i = size Trials.outs - 1 /\ (ok => 0 <= i)).
- by inline Rec(T).trial; wp; call (_ : true); auto => />; smt(size_rcons size_ge0).
by auto => />; smt(ntr_gt0).
qed.

(* The values of the trials kept by index and outcome. *)
op vvinv (m : (int * bool * ((state * pp -> seed) * (seed -> W16.word * W240.word) * pp), state) fmap)
         (outs : bool list) (vals : state list)
         (f3 : (state * pp -> seed) * (seed -> W16.word * W240.word) * pp) =
  size vals = size outs /\
  (forall x, x \in m => 0 <= x.`1 < size outs) /\
  (forall j, 0 <= j < size outs => m.[(j, nth false outs j, f3)] = Some (nth witness vals j)).

lemma vvinv_step m outs vals f3 b e : vvinv m outs vals f3 =>
  (size outs, b, f3) \notin m /\ vvinv m.[(size outs, b, f3) <- e] (rcons outs b) (rcons vals e) f3.
proof.
move=> [hs [hk hv]]; split; 1: by apply/negP => /hk /#.
rewrite /vvinv !size_rcons hs /=; split.
- by move=> x; rewrite mem_set => -[/hk | ->] /=; smt(size_ge0).
move=> j hj; rewrite get_setE !nth_rcons hs.
case: (j < size outs) => hlt.
- by rewrite (_ : (j, nth false outs j, f3) <> (size outs, b, f3)) 1:/# /=; apply hv => /#.
by have -> /= : j = size outs by smt().
qed.

(* ---- The cutoff of the sequential rule: below 2^-256 ---- *)
op qk : real = inv (2%r ^ 17).

lemma ntr_small : ntr%r * inv (2%r ^ 256) + ntr%r * inv (2%r ^ 512) <= qk.
proof.
have hn : ntr%r = 2%r ^ 80 by rewrite /ntr; smt(RField.fromintXn).
have e1 : 2%r ^ 80 * inv (2%r ^ 256) = inv (2%r ^ 176).
- by rewrite (_ : 256 = 80 + 176) // RField.exprD_nneg //; field; smt(expr_gt0).
have e2 : 2%r ^ 80 * inv (2%r ^ 512) = inv (2%r ^ 432).
- by rewrite (_ : 512 = 80 + 432) // RField.exprD_nneg //; field; smt(expr_gt0).
have e3 : inv (2%r ^ 17) = 2%r * inv (2%r ^ 18).
- by rewrite (_ : 18 = 1 + 17) // RField.exprD_nneg // RField.expr1; field; smt(expr_gt0).
have l1 : inv (2%r ^ 176) <= inv (2%r ^ 18).
- by rewrite lef_pinv; [smt(expr_gt0) | smt(expr_gt0) | apply ler_weexpn2l].
have l2 : inv (2%r ^ 432) <= inv (2%r ^ 18).
- by rewrite lef_pinv; [smt(expr_gt0) | smt(expr_gt0) | apply ler_weexpn2l].
by rewrite /qk hn e1 e2 e3; smt().
qed.

(* One trial fails with probability at most 1 - 2^-17 while the tables hold at most 2^80 values. *)
lemma trial_fail (mS : (state * pp, seed) fmap) (mT : (seed, W16.word * W240.word) fmap) (q : pp) (C : real) :
  0%r <= C => fsize mS <= ntr => fsize mT <= ntr =>
  Ep dstate (fun e => Ep dseed (fun r => Ep dct (fun (r0 : W16.word * W240.word) =>
    (C * b2r ((e, q) \in mS) + C * b2r (r \in mT) + C * b2r (r0.`1 <> zero16))%xr)))
  <= (C * (1%r - qk))%xr.
proof.
move=> hC hS hT.
have hA : mu dstate (fun e => (e, q) \in mS) <= ntr%r * inv (2%r ^ 256).
- apply (ler_trans (mu dstate (mem (map fst (FSet.elems (fdom mS)))))).
  + by apply mu_le => e _ /= h; apply/mapP; exists (e, q); rewrite -FSet.memE mem_fdom.
  apply (ler_trans _ _ _ (mu_mem_le_mu1 dstate _ (inv (2%r ^ 256)) _)); 1: by move=> x; rewrite dstate1_256.
  by rewrite size_map -FSet.cardE; apply ler_wpmul2r; smt(expr_gt0 invr_gt0).
have hB : mu dseed (fun r => r \in mT) <= ntr%r * inv (2%r ^ 512).
- apply (ler_trans (mu dseed (mem (FSet.elems (fdom mT))))); 1: by apply mu_le => d _ /= h; rewrite -FSet.memE mem_fdom.
  apply (ler_trans _ _ _ (mu_mem_le_mu1 dseed _ (inv (2%r ^ 512)) _)); 1: by move=> x; rewrite dseed1.
  by rewrite -FSet.cardE; apply ler_wpmul2r; smt(expr_gt0 invr_gt0).
have hc : mu dct (fun r0 : W16.word * W240.word => r0.`1 <> zero16) = 1%r - pk.
- rewrite /dct (dprodEl W16.DWord.dunifin W240.DWord.dunifin (fun r => r <> zero16)) W240.DWord.dunifin_ll.
  by rewrite (mu_not _ (fun r => r = zero16)) W16.DWord.dunifin_ll dW16_zero.
have hb : forall b, 0%r <= C * b2r b by move=> b; apply mulr_ge0 => //; apply b2r_ge0.
have hpk : pk = 2%r * qk.
- by rewrite /pk /qk (_ : 17 = 1 + 16) // RField.exprD_nneg // RField.expr1; field; smt(expr_gt0).
rewrite (eq_Ep _ _ (fun e => Ep dseed (fun r => ((C * b2r ((e, q) \in mS) + C * b2r (r \in mT)) +
                      C * (1%r - pk))%xr))) => [e _ /= | ].
- apply eq_Ep => r _ /=.
  rewrite (Ep_cbs dct _ C (fun (r0 : W16.word * W240.word) => r0.`1 <> zero16) dct_ll) //; 1: smt().
  by rewrite hc.
rewrite (eq_Ep _ _ (fun e => ((C * b2r ((e, q) \in mS) + C * (1%r - pk)) + C * mu dseed (fun r => r \in mT))%xr))
  => [e _ /= | ].
- rewrite (eq_Ep _ _ (fun r => ((C * b2r ((e, q) \in mS) + C * (1%r - pk)) + C * b2r (r \in mT))%xr))
    => [r _ /= | ]; 1: by congr; ring.
  by rewrite (Ep_cbs dseed _ C (fun r => r \in mT) dseed_ll) //; smt(pk_lt1).
rewrite (eq_Ep _ _ (fun e => ((C * (1%r - pk) + C * mu dseed (fun r => r \in mT)) + C * b2r ((e, q) \in mS))%xr))
  => [e _ /= | ]; 1: by congr; ring.
rewrite (Ep_cbs dstate _ C (fun e => (e, q) \in mS) dstate_ll) //; 1: smt(pk_lt1 ge0_mu).
have hn := ntr_small; apply xr_le; rewrite -!RField.mulrDr; apply ler_wpmul2l => //.
move: hA hB hn; rewrite hpk; pose a := mu dseed _; pose b := mu dstate _; smt().
qed.

(* The sequential selection alone, and its potential: 0 after a pass, otherwise the chance that
   every remaining trial fails if each fails with probability at most 1 - 2^-17. *)
module SeqRun = {
  proc main() : int = {
    var i;
    RS.RO.init(); RT.RO.init();
    Gen.q <$ dQ;
    Trials.q <- Gen.q; Trials.vals <- []; Trials.outs <- [];
    i <@ Seq(Trials).select();
    return i;
  }
}.

op phiQ (ok : bool) (i : int) : real = if ok then 0%r else (1%r - qk) ^ (ntr - (i + 1)).

lemma seqrun_e : ehoare [SeqRun.main : (phiQ false (-1))%xr ==> (!last false Trials.outs)%xr].
proof.
proc; inline Seq(Trials).select; wp.
while ((-1 <= i0 /\ i0 + 1 <= ntr /\ ok = last false Trials.outs /\
        fsize RS.RO.m <= i0 + 1 /\ fsize RT.RO.m <= i0 + 1) `|` (phiQ ok i0)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[hi [hn [hok _]]].
  apply xr_ble; rewrite /phiQ -hok; case: (ok{hr}) hc => [_ | hc] //=.
  by rewrite (_ : ntr - (i0{hr} + 1) = 0) 1:/# RField.expr0.
- inline *; auto => &hr /=; apply xle_cxr_r => -[[hok hn] [hi [hn' [hl [hS hT]]]]].
  pose C := (1%r - qk) ^ (ntr - (i0{hr} + 2)).
  have hq : 0%r <= qk <= 1%r by rewrite /qk; smt(expr_gt0 invr_gt0 invr_le1 exprn_ege1).
  have hC : 0%r <= C by apply expr_ge0; smt().
  have hb : forall b, 0%r <= C * b2r b by move=> b; apply mulr_ge0 => //; apply b2r_ge0.
  apply (xle_trans (Ep dstate (fun e => Ep dseed (fun r => Ep dct (fun (r0 : W16.word * W240.word) =>
           (C * b2r ((e, Trials.q{hr}) \in RS.RO.m{hr}) + C * b2r (r \in RT.RO.m{hr}) +
            C * b2r (r0.`1 <> zero16))%xr))))).
  + apply le_Ep => e _ /=; apply le_Ep => r _ /=.
    case: ((e, Trials.q{hr}) \in RS.RO.m{hr}) => he /=; apply le_Ep => r0 _ /=.
    * case: (oget RS.RO.m{hr}.[e, Trials.q{hr}] \in RT.RO.m{hr}) => hd /=;
        (apply xle_cxr_l; [rewrite last_rcons ?fsize_set /=; smt() |
                           apply xr_le; rewrite /phiQ ?get_set_sameE; smt(b2r_ge0)]).
    rewrite get_set_sameE /=; case: (r \in RT.RO.m{hr}) => hd /=;
      (apply xle_cxr_l; [rewrite last_rcons ?fsize_set /=; smt() |
                         apply xr_le; rewrite /phiQ ?get_set_sameE; smt(b2r_ge0)]).
  apply (xle_trans _ _ _ (trial_fail RS.RO.m{hr} RT.RO.m{hr} Trials.q{hr} C hC _ _)); 1,2: smt().
  by apply xr_le; rewrite /phiQ hok /= (_ : ntr - (i0{hr} + 1) = ntr - (i0{hr} + 2) + 1) 1:/# RField.exprS; smt().
have h0 : 0 <= ntr by smt(ntr_gt0).
inline *; auto => &hr /=; rewrite !fsize_empty h0 /=.
by rewrite /= EpC dQ_ll smul1m.
qed.

(* The cutoff of the sequential rule in Θ0. *)
lemma seq_cutoff &m : Pr[Setup0P(Seq).run() @ &m : !last false Trials.outs] <= inv (2%r ^ 256).
proof.
have -> : Pr[Setup0P(Seq).run() @ &m : !last false Trials.outs] = Pr[SeqRun.main() @ &m : !last false Trials.outs].
- byequiv => //; proc; inline RW.RO.get RS.RO.get.
  wp; rnd{1}; wp; call{1} (_ : true ==> true).
  + by proc; while true (12 - i); [move=> z; wp; inline *; auto; smt(dans_ll) | auto => /#].
  wp; rnd{1}; wp; call (_ : ={RS.RO.m, RT.RO.m, Trials.q, Trials.vals, Trials.outs}); 1: by sim.
  by inline *; wp; rnd; rnd{1}; auto => />; smt(dP_ll dseed_ll ddata_ll).
have h1 : Pr[SeqRun.main() @ &m : !last false Trials.outs] <= phiQ false (-1).
- byehoare (_ : (phiQ false (-1))%xr ==> _) => //; 1: exact seqrun_e.
  by rewrite /phiQ /=; apply expr_ge0; rewrite /qk; smt(expr_gt0 invr_gt0 invr_le1 exprn_ege1).
have h2 : phiQ false (-1) <= inv (2%r ^ 256) by rewrite /phiQ /= /qk; exact pcut17.
smt().
qed.

(* The sequential rule of the specification without a cutoff: the generation of the text's Θ0. *)
module SeqU (T : TRIALS) = {
  proc select() : int = {
    var ok, i;
    ok <- false;
    i <- -1;
    while (!ok) { ok <@ T.trial(); i <- i + 1; }
    return i;
  }
}.

(* It is a covered rule: it selects a passing trial, and it stops with probability 1 when every trial
   passes with the same positive probability. *)
lemma SeqU_pass (T <: TRIALS {-Trials}) :
  hoare [SeqU(Rec(T)).select : Trials.outs = [] ==> 0 <= res < size Trials.outs /\ nth false Trials.outs res].
proof.
proc; while (size Trials.outs = i + 1 /\ ok = nth false Trials.outs i).
- inline Rec(T).trial; wp; call (_ : true); auto => /> &hr hs _ b.
  by rewrite size_rcons nth_rcons hs /=.
by auto => />; smt(nth_neg nth_default).
qed.

lemma SeqU_ll (T <: TRIALS) (P : glob T -> bool) (b : real) :
  0%r < b => phoare [T.trial : P (glob T) ==> P (glob T) /\ res] = b =>
  phoare [T.trial : P (glob T) ==> P (glob T)] = 1%r =>
  phoare [SeqU(T).select : P (glob T) ==> true] = 1%r.
proof.
move=> hb hpass hll; proc; sp; conseq (_ : P (glob T) ==> true) => //.
while (P (glob T)) (b2i (!ok)) 1 b => //; 1: smt().
- move=> ih; seq 2 : (P (glob T)) 1%r 1%r 0%r 0%r => //; 1: by wp; call hll; auto.
  by hoare; wp; call (_ : P (glob T) ==> P (glob T)); [conseq hll | auto].
- by wp; call hll; auto.
split => [/# | z]; conseq (_ : P (glob T) /\ !ok /\ b2i (!ok) = z ==> !ok = false) => [/# |].
by wp; call (_ : P (glob T) ==> P (glob T) /\ res); [conseq hpass | auto]; smt().
qed.

section Selection.
declare module Rl <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                           -Trials, -Gen}.
declare module D <: CONT {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                          -RTE.FunRO, -RW.RO, -Trials, -Gen, -Rl}.

(* The rule selects a passing trial by the outcomes alone, whatever the source of the trials; it stops
   with probability 1 whenever the source keeps a state in which every trial passes with the same
   positive probability; the continuation halts. *)
declare axiom Rl_pass (T <: TRIALS {-Rl, -Trials}) :
  hoare [Rl(Rec(T)).select : Trials.outs = [] ==>
           0 <= res < size Trials.outs /\ nth false Trials.outs res].
declare axiom Rl_ll (T <: TRIALS {-Rl}) (P : glob T -> bool) (b : real) :
  0%r < b => phoare [T.trial : P (glob T) ==> P (glob T) /\ res] = b =>
  phoare [T.trial : P (glob T) ==> P (glob T)] = 1%r =>
  phoare [Rl(T).select : P (glob T) ==> true] = 1%r.
declare axiom D_ll (O <: OraclesP {-D}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless D(O).run.

(* ---- S and T as whole functions ---- *)
local module TrG (GS : RS.RO) (GT : RT.RO) = {
  proc trial() : bool = {
    var e, d, c;
    e <$ dstate;
    d <@ GS.get(e, Trials.q);
    c <@ GT.get(d);
    Trials.vals <- rcons Trials.vals e;
    Trials.outs <- rcons Trials.outs (c.`1 = zero16);
    return c.`1 = zero16;
  }
}.

local module IPST (GS : RS.RO) (GT : RT.RO) : OraclesP = {
  proc a = Ideal.a
  proc b = Ideal.b
  proc h = Ideal.h
  proc s(e : state, q : pp) = { var d; d <@ GS.get(e, q); return d; }
  proc t(d : seed) = { var c; c <@ GT.get(d); return c; }
  proc w = IP.w
}.

local module GG (Ru : RULE) (GS : RS.RO) (GT : RT.RO) = {
  proc main() : bool = {
    var i, y, om, b;
    R.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Trials.q <- Gen.q; Trials.vals <- []; Trials.outs <- [];
    i <@ Ru(TrG(GS, GT)).select();
    Gen.e <- nth witness Trials.vals i;
    Gen.sd <@ GS.get(Gen.e, Gen.q);
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    b <@ D(IPST(GS, GT)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd);
    return b;
  }
}.

local module DSd (Ru : RULE) (GS : RS.RO) = {
  proc distinguish() : bool = { var b; RT.RO.init(); b <@ GG(Ru, GS, RT.RO).main(); return b; }
}.

local module DTd (Ru : RULE) (GT : RT.RO) = {
  proc distinguish() : bool = { var b; RSE.FunRO.init(); b <@ GG(Ru, RSE.FunRO, GT).main(); return b; }
}.

local lemma to_eager (Ru <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                               -Trials, -Gen, -D}) (E : bool -> bool list -> bool) &m :
  Pr[GenGame(Setup0P(Ru), D).main() @ &m : E res Trials.outs] =
  Pr[RT.MainD(DTd(Ru), RTE.FunRO).distinguish() @ &m : E res Trials.outs].
proof.
have -> : Pr[GenGame(Setup0P(Ru), D).main() @ &m : E res Trials.outs] =
          Pr[RS.MainD(DSd(Ru), RS.RO).distinguish() @ &m : E res Trials.outs].
- byequiv (_ : ={glob D, glob Ru} ==> ={res, Trials.outs}) => //; proc; inline Setup0P(Ru).run DSd(Ru, RS.RO).distinguish GG(Ru, RS.RO, RT.RO).main; wp.
  call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); 1..6: by sim.
  wp; call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
  call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
  call (_ : ={arg, RS.RO.m} ==> ={res, RS.RO.m}); 1: by sim.
  wp; call (_ : ={RS.RO.m, RT.RO.m, Trials.q, Trials.vals, Trials.outs}); 1: by sim.
  by inline *; auto.
have -> : Pr[RS.MainD(DSd(Ru), RS.RO).distinguish() @ &m : E res Trials.outs] =
          Pr[RS.MainD(DSd(Ru), RSE.FunRO).distinguish() @ &m : E res Trials.outs].
- byequiv (_ : ={glob DSd(Ru), arg} ==> ={res, glob DSd(Ru)}) => //.
  transitivity RS.MainD(DSd(Ru), RSE.FinRO).distinguish
    (={glob DSd(Ru), arg} ==> ={res, glob DSd(Ru)}) (={glob DSd(Ru), arg} ==> ={res, glob DSd(Ru)}) => //.
  + by move=> &1 &2 h; exists (glob D){1} (glob Ru){1} Gen.e{1} Gen.p{1} Gen.q{1} Gen.sd{1} Trials.outs{1}
      Trials.q{1} Trials.vals{1} RT.RO.m{1} RW.RO.m{1} R.RO.m{1} arg{1}.
  + by apply (RSE.RO_FinRO_D _ (DSd(Ru))) => _; exact dseed_ll.
  by apply (RSE.FinRO_FunRO_D _ (DSd(Ru))) => _; exact dseed_ll.
have -> : Pr[RS.MainD(DSd(Ru), RSE.FunRO).distinguish() @ &m : E res Trials.outs] =
          Pr[RT.MainD(DTd(Ru), RT.RO).distinguish() @ &m : E res Trials.outs].
- by byequiv (_ : ={glob D, glob Ru} ==> ={res, Trials.outs}) => //; proc; inline *; sim; auto.
byequiv (_ : ={glob DTd(Ru), arg} ==> ={res, glob DTd(Ru)}) => //.
transitivity RT.MainD(DTd(Ru), RTE.FinRO).distinguish
  (={glob DTd(Ru), arg} ==> ={res, glob DTd(Ru)}) (={glob DTd(Ru), arg} ==> ={res, glob DTd(Ru)}) => //.
- by move=> &1 &2 h; exists (glob D){1} (glob Ru){1} Gen.e{1} Gen.p{1} Gen.q{1} Gen.sd{1} Trials.outs{1}
    Trials.q{1} Trials.vals{1} RSE.FunRO.f{1} RW.RO.m{1} R.RO.m{1} arg{1}.
- by apply (RTE.RO_FinRO_D _ (DTd(Ru))) => _; exact dct_ll.
by apply (RTE.FinRO_FunRO_D _ (DTd(Ru))) => _; exact dct_ll.
qed.

(* ---- A trial as an outcome first, then a value given the outcome ---- *)
local module TrS = {
  proc trial() : bool = {
    var b, e;
    b <$ Biased.dbiased (mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q));
    e <$ dval RSE.FunRO.f RTE.FunRO.f Trials.q b;
    Trials.vals <- rcons Trials.vals e;
    Trials.outs <- rcons Trials.outs (pass RSE.FunRO.f RTE.FunRO.f Trials.q e);
    return pass RSE.FunRO.f RTE.FunRO.f Trials.q e;
  }
}.

local clone DProd.DLetSampling as SD with type t <- bool, type u <- state.

local equiv trial_split : TrG(RSE.FunRO, RTE.FunRO).trial ~ TrS.trial :
  ={Trials.q, Trials.vals, Trials.outs, RSE.FunRO.f, RTE.FunRO.f} ==>
  ={res, Trials.q, Trials.vals, Trials.outs, RSE.FunRO.f, RTE.FunRO.f}.
proof.
proc; inline *.
outline {2} [1 .. 2] by { e <@ SD.SampleDep.sample(Biased.dbiased (mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)),
                                                   dval RSE.FunRO.f RTE.FunRO.f Trials.q); }.
rewrite equiv[{2} 1 SD.SampleDepDLet].
inline *; wp; rnd; auto => /> &2.
by rewrite /dval -(Biased.marginal_sampling_pred dstate _ dstate_ll).
qed.

local module GES (Ru : RULE) = {
  proc main() : bool = {
    var i, y, om, b;
    RTE.FunRO.init(); RSE.FunRO.init(); R.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Trials.q <- Gen.q; Trials.vals <- []; Trials.outs <- [];
    i <@ Ru(TrS).select();
    Gen.e <- nth witness Trials.vals i;
    Gen.sd <@ RSE.FunRO.get(Gen.e, Gen.q);
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    b <@ D(IPST(RSE.FunRO, RTE.FunRO)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd);
    return b;
  }
}.

local lemma to_split (Ru <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                                  -Trials, -Gen, -D}) (E : bool -> bool list -> bool) &m :
  Pr[RT.MainD(DTd(Ru), RTE.FunRO).distinguish() @ &m : E res Trials.outs] =
  Pr[GES(Ru).main() @ &m : E res Trials.outs].
proof.
byequiv (_ : ={glob D, glob Ru} ==> ={res, Trials.outs}) => //; proc.
inline DTd(Ru, RTE.FunRO).distinguish GG(Ru, RSE.FunRO, RTE.FunRO).main; wp.
call (_ : ={R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f}); 1..6: by sim.
wp; call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
call (_ : ={arg, RSE.FunRO.f} ==> ={res, RSE.FunRO.f}); 1: by sim.
wp; call (_ : ={Trials.q, Trials.vals, Trials.outs, RSE.FunRO.f, RTE.FunRO.f}); 1: by conseq trial_split.
by inline *; auto.
qed.

(* ---- The values of the trials, drawn only when read ---- *)
local module TB = {
  var p : real
  proc trial() : bool = { var b; b <$ Biased.dbiased p; return b; }
}.

local module Sv = { var i : int }.

local clone PROM.FullRO as VV with
  type in_t <- int * bool * ((state * pp -> seed) * (seed -> W16.word * W240.word) * pp),
  type out_t <- state, op dout <- dtrial, type d_in_t <- unit, type d_out_t <- bool.

local module TrV (V : VV.RO) = {
  proc trial() : bool = {
    var b;
    b <@ TB.trial();
    V.sample((size Trials.outs, b, (RSE.FunRO.f, RTE.FunRO.f, Trials.q)));
    Trials.outs <- rcons Trials.outs b;
    return b;
  }
}.

local module GVd (Ru : RULE) (V : VV.RO) = {
  proc distinguish() : bool = {
    var y, om, b;
    RTE.FunRO.init(); RSE.FunRO.init(); R.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Trials.q <- Gen.q; Trials.vals <- []; Trials.outs <- [];
    TB.p <- mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q);
    Sv.i <@ Ru(TrV(V)).select();
    Gen.e <- witness;
    if (0 <= Sv.i < size Trials.outs) {
      Gen.e <@ V.get((Sv.i, nth false Trials.outs Sv.i, (RSE.FunRO.f, RTE.FunRO.f, Trials.q)));
    }
    Gen.sd <@ RSE.FunRO.get(Gen.e, Gen.q);
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    b <@ D(IPST(RSE.FunRO, RTE.FunRO)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd);
    return b;
  }
}.

local lemma to_vv (Ru <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                               -Trials, -Gen, -D, -TB, -Sv, -VV.RO, -VV.FRO}) (E : bool -> bool list -> bool) &m :
  Pr[GES(Ru).main() @ &m : E res Trials.outs] = Pr[VV.MainD(GVd(Ru), VV.RO).distinguish() @ &m : E res Trials.outs].
proof.
byequiv (_ : ={glob D, glob Ru} ==> ={res, Trials.outs}) => //; proc.
inline GVd(Ru, VV.RO).distinguish; wp.
call (_ : ={R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f}); 1..6: by sim.
wp; call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
call (_ : ={arg, RSE.FunRO.f} ==> ={res, RSE.FunRO.f}); 1: by sim.
conseq (_ : _ ==> ={glob D, Gen.p, Gen.q, Gen.e, R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f, Trials.outs}) => />.
seq 10 13 : (={glob D, Gen.p, Gen.q, R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f, Trials.q, Trials.outs} /\
             i{1} = Sv.i{2} /\
             vvinv VV.RO.m{2} Trials.outs{2} Trials.vals{1} (RSE.FunRO.f{2}, RTE.FunRO.f{2}, Trials.q{2})).
- call (_ : ={RSE.FunRO.f, RTE.FunRO.f, Trials.q, Trials.outs} /\
            TB.p{2} = mu dstate (pass RSE.FunRO.f{2} RTE.FunRO.f{2} Trials.q{2}) /\
            vvinv VV.RO.m{2} Trials.outs{2} Trials.vals{1} (RSE.FunRO.f{2}, RTE.FunRO.f{2}, Trials.q{2})).
  + proc; inline TB.trial VV.RO.sample VV.RO.get; wp.
    rnd; wp; rnd; auto => /> &1 &2 hs hk hv b hb.
    rewrite (dtrial_dval _ _ _ _ _ hb) /= => e he.
    have := vvinv_step VV.RO.m{2} Trials.outs{2} Trials.vals{1} (RSE.FunRO.f{2}, RTE.FunRO.f{2}, Trials.q{2})
              b e _; 1: by [].
    by rewrite (dval_pass _ _ _ _ _ he) /vvinv /=; smt().
  by inline *; auto => />; smt(mem_empty).
sp; if{2}.
- inline{2} VV.RO.get; rcondf{2} 3; 1: by auto => /> /#.
  by wp; rnd{2}; auto => />; smt(dtrial_ll).
by auto => />; smt(nth_default nth_neg).
qed.

local module FR (Ru : RULE) = {
  proc main() : bool = {
    var y, om, b;
    RTE.FunRO.init(); RSE.FunRO.init(); R.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Trials.q <- Gen.q; Trials.outs <- [];
    TB.p <- mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q);
    Sv.i <@ Ru(Rec(TB)).select();
    Gen.e <- witness;
    if (0 <= Sv.i < size Trials.outs) {
      Gen.e <$ dtrial (Sv.i, nth false Trials.outs Sv.i, (RSE.FunRO.f, RTE.FunRO.f, Trials.q));
    }
    Gen.sd <@ RSE.FunRO.get(Gen.e, Gen.q);
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    b <@ D(IPST(RSE.FunRO, RTE.FunRO)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd);
    return b;
  }
}.

local lemma chain (Ru <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                               -Trials, -Gen, -D, -TB, -Sv, -VV.RO, -VV.FRO}) (E : bool -> bool list -> bool) &m :
  Pr[GenGame(Setup0P(Ru), D).main() @ &m : E res Trials.outs] = Pr[FR(Ru).main() @ &m : E res Trials.outs].
proof.
rewrite (to_eager Ru E &m) (to_split Ru E &m) (to_vv Ru E &m).
have -> : Pr[VV.MainD(GVd(Ru), VV.RO).distinguish() @ &m : E res Trials.outs] =
          Pr[VV.MainD(GVd(Ru), VV.LRO).distinguish() @ &m : E res Trials.outs].
- by byequiv (VV.FullEager.RO_LRO (GVd(Ru)) dtrial_ll) => //.
byequiv (_ : ={glob D, glob Ru} ==> ={res, Trials.outs}) => //; proc.
inline GVd(Ru, VV.LRO).distinguish; wp.
call (_ : ={R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f}); 1..6: by sim.
wp; call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
call (_ : ={arg, RSE.FunRO.f} ==> ={res, RSE.FunRO.f}); 1: by sim.
seq 13 10 : (={glob D, Gen.p, Gen.q, R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f, Trials.q, Trials.outs, Sv.i} /\
             VV.RO.m{1} = empty).
- call (_ : ={TB.p, Trials.outs} /\ VV.RO.m{1} = empty); 1: by proc; inline *; auto.
  by inline *; auto.
by sp; if => //; inline *; auto => />; smt(mem_empty get_set_sameE).
qed.

(* ---- The rule against the sequential one ---- *)
local module Pre = {
  proc main() : bool = {
    var y, om, b;
    RTE.FunRO.init(); RSE.FunRO.init(); R.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Trials.q <- Gen.q;
    Gen.e <$ dtrial (0, true, (RSE.FunRO.f, RTE.FunRO.f, Trials.q));
    Gen.sd <@ RSE.FunRO.get(Gen.e, Gen.q);
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    b <@ D(IPST(RSE.FunRO, RTE.FunRO)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd);
    return b;
  }
}.

local module Kv = { var b, ok : bool }.

(* The selection moved after the run: it reads only S, T and the passphrase. *)
local module K (Ru : RULE) = {
  proc main() : bool = {
    Kv.b <@ Pre.main();
    Trials.outs <- [];
    TB.p <- mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q);
    Sv.i <@ Ru(Rec(TB)).select();
    Kv.ok <- 0 <= Sv.i < size Trials.outs /\ nth false Trials.outs Sv.i;
    return Kv.b /\ Kv.ok;
  }
}.

local lemma enc_lls : islossless Net(Ideal).enc.
proof. by proc; while true (12 - i); [move=> z; wp; inline *; auto; smt(dans_ll) | auto => /#]. qed.

local lemma Dll : islossless D(IPST(RSE.FunRO, RTE.FunRO)).run.
proof. by apply (D_ll (IPST(RSE.FunRO, RTE.FunRO))); proc; inline *; auto => />; smt(dans_ll ddata_ll). qed.

local equiv fr_k (Ru <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                               -Trials, -Gen, -D, -TB, -Sv, -Kv}) :
  FR(Ru).main ~ K(Ru).main : ={glob D, glob Ru} ==>
  ={Trials.outs} /\ (0 <= Sv.i < size Trials.outs /\ nth false Trials.outs Sv.i){1} = Kv.ok{2} /\
  ((0 <= Sv.i < size Trials.outs /\ nth false Trials.outs Sv.i){1} => res{1} = Kv.b{2}).
proof.
proc; inline Pre.main; swap{2} [14 .. 16] -6.
seq 10 10 : (={glob D, Gen.p, Gen.q, Trials.q, Trials.outs, Sv.i, RSE.FunRO.f, RTE.FunRO.f, R.RO.m, RW.RO.m}).
- by call (_ : ={TB.p, Trials.outs}); [sim | inline *; auto].
case (0 <= Sv.i{1} < size Trials.outs{1} /\ nth false Trials.outs{1} Sv.i{1}).
- rcondt{1} 2; 1: by auto => /#.
  wp; call (_ : ={R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f}); 1..6: by sim.
  wp; call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
  call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
  call (_ : ={arg, RSE.FunRO.f} ==> ={res, RSE.FunRO.f}); 1: by sim.
  by wp; rnd; wp; skip => /> &1 &2 h0 h1 h2; rewrite /dtrial /= h2.
wp; call{1} Dll; call{2} Dll; call{1} rw_get_ll; call{2} rw_get_ll; call{1} enc_lls; call{2} enc_lls.
call{1} (_ : true ==> true); 1: by proc; auto.
call{2} (_ : true ==> true); 1: by proc; auto.
rnd{2}; sp; if{1}; [rnd{1} |]; auto => />; smt(dtrial_ll).
qed.

(* Through the selection after the run: the rule stops and selects a pass exactly when some value
   passes; the sequential rule may stop at its cutoff. *)
local lemma sel_cov (Ru <: RULE {-TB, -Trials}) :
  hoare [Ru(Rec(TB)).select : Trials.outs = [] ==> 0 <= res < size Trials.outs /\ nth false Trials.outs res] =>
  (forall (P : glob Rec(TB) -> bool) (b : real),
     0%r < b => phoare [Rec(TB).trial : P (glob Rec(TB)) ==> P (glob Rec(TB)) /\ res] = b =>
     phoare [Rec(TB).trial : P (glob Rec(TB)) ==> P (glob Rec(TB))] = 1%r =>
     phoare [Ru(Rec(TB)).select : P (glob Rec(TB)) ==> true] = 1%r) =>
  forall (p0 : real), phoare [Ru(Rec(TB)).select : TB.p = p0 /\ Trials.outs = [] /\ 0%r < p0 <= 1%r ==>
                                0 <= res < size Trials.outs /\ nth false Trials.outs res] = 1%r.
proof.
move=> hpass hll p0; case (0%r < p0 <= 1%r) => hp; 2: by exfalso; smt().
conseq (_ : TB.p = p0 ==> true) hpass => //.
apply (hll (fun (g : glob Rec(TB)) => g.`1 = p0) p0) => //; 1: smt().
- proc; inline TB.trial; wp; rnd (fun b => b); auto => />.
  by rewrite Biased.dbiasedE /= Biased.clamp_id /#.
by proc; inline TB.trial; auto => />; exact Biased.dbiased_ll.
qed.

local lemma sel0 (Ru <: RULE {-TB, -Trials}) :
  hoare [Ru(Rec(TB)).select : TB.p = 0%r /\ Trials.outs = [] ==> !nth false Trials.outs res].
proof.
conseq (_ : TB.p = 0%r /\ all (fun x => !x) Trials.outs ==> all (fun x => !x) Trials.outs) => //.
- move=> &hr _ r outs hall; case: (0 <= r < size outs) => hr; 2: smt(nth_default nth_neg).
  by move: hall; rewrite allP => /(_ (nth false outs r) (mem_nth false outs r hr)).
proc (TB.p = 0%r /\ all (fun x => !x) Trials.outs) => //.
by proc; inline TB.trial; auto => /> &hr hall b; rewrite Biased.dbiased0 supp_dunit => ->; rewrite -cats1 all_cat hall.
qed.

local lemma k_cov (Ru <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                               -Trials, -Gen, -D, -TB, -Sv, -Kv}) :
  (forall (p0 : real), phoare [Ru(Rec(TB)).select : TB.p = p0 /\ Trials.outs = [] /\ 0%r < p0 <= 1%r ==>
                                0 <= res < size Trials.outs /\ nth false Trials.outs res] = 1%r) =>
  forall &m, Pr[K(Ru).main() @ &m : Kv.b /\ Kv.ok] =
  Pr[Pre.main() @ &m : res /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)].
proof.
move=> hsel &m.
byphoare (_ : (glob K(Ru)) = (glob K(Ru)){m} ==> Kv.b /\ Kv.ok) => //; proc.
seq 1 : (Kv.b /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q))
  (Pr[Pre.main() @ &m : res /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)]) 1%r
  (Pr[Pre.main() @ &m : !(res /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q))]) 0%r => //.
- call (_ : (glob Pre) = (glob Pre){m} ==> res /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)).
  + bypr => &m0; split => [| h]; 1: smt(mu_bounded).
    by byequiv (_ : ={glob Pre} ==> ={res, RSE.FunRO.f, RTE.FunRO.f, Trials.q}) => //; sim.
  by auto.
- wp; exlim (mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)) => p0.
  by call (hsel p0); auto => />; smt(le1_mu).
hoare; wp; case Kv.b.
- by call (sel0 Ru); auto => />; smt(ge0_mu).
by call (_ : true); [proc; inline *; auto | auto => />].
qed.

local lemma seq_ll : islossless Seq(Rec(TB)).select.
proof.
proc; while true (ntr - (i + 1)); 2: by auto => /#.
by move=> z; wp; inline *; auto => />; smt(Biased.dbiased_ll).
qed.

local lemma seq_sel (p0 : real) :
  phoare [Seq(Rec(TB)).select : TB.p = p0 /\ Trials.outs = [] ==>
            (p0 = 0%r => !nth false Trials.outs res) /\ res = size Trials.outs - 1 /\
            1 <= size Trials.outs] = 1%r.
proof.
conseq seq_ll (_ : TB.p = p0 /\ Trials.outs = [] ==>
                   (p0 = 0%r => !nth false Trials.outs res) /\ res = size Trials.outs - 1 /\
                   1 <= size Trials.outs) => //.
case (p0 = 0%r) => h0.
- by conseq (sel0 Seq) (seq_last TB) => /> /#.
by conseq (seq_last TB) => /> /#.
qed.

local lemma k_seq &m :
  Pr[K(Seq).main() @ &m : Kv.b /\ Kv.ok] <=
    Pr[Pre.main() @ &m : res /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)] /\
  Pr[Pre.main() @ &m : res /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)] <=
    Pr[K(Seq).main() @ &m : Kv.b /\ Kv.ok] + Pr[K(Seq).main() @ &m : !Kv.ok] /\
  Pr[K(Seq).main() @ &m : !Kv.ok] = Pr[K(Seq).main() @ &m : !last false Trials.outs].
proof.
have e1 : Pr[K(Seq).main() @ &m : Kv.b /\ Kv.ok] <=
          Pr[Pre.main() @ &m : res /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)].
- byequiv => //; proc*; inline K(Seq).main; wp.
  seq 3 1 : (Kv.b{1} = r{2} /\ ={RSE.FunRO.f, RTE.FunRO.f, Trials.q} /\
             TB.p{1} = mu dstate (pass RSE.FunRO.f{1} RTE.FunRO.f{1} Trials.q{1}) /\ Trials.outs{1} = []).
  + wp; call (_ : ={glob D} ==> ={res, RSE.FunRO.f, RTE.FunRO.f, Trials.q}); 1: by sim.
    by auto.
  by exlim TB.p{1} => p0; call{1} (seq_sel p0); auto => />; smt(ge0_mu).
have e2 : Pr[Pre.main() @ &m : res] = Pr[K(Seq).main() @ &m : Kv.b].
- byequiv => //; proc*; inline K(Seq).main; wp.
  call{2} seq_ll; wp; call (_ : ={glob D} ==> ={res}); 1: by sim.
  by auto.
have h0 : hoare [K(Seq).main : true ==> (Kv.ok <=> last false Trials.outs)].
- proc; wp; call (seq_last TB); wp; call (_ : true ==> true); 1: by trivial.
  by auto => /> outs h1; rewrite nth_last /#.
have e3 : Pr[K(Seq).main() @ &m : !Kv.ok] = Pr[K(Seq).main() @ &m : !last false Trials.outs].
- byequiv (_ : ={glob K(Seq)} ==> ={Kv.ok, Trials.outs} /\ (Kv.ok <=> last false Trials.outs){1}) => //.
  by conseq (_ : _ ==> ={Kv.ok, Trials.outs}) h0 _ => //; sim.
have e4 : Pr[Pre.main() @ &m : res /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)] <=
          Pr[Pre.main() @ &m : res] by rewrite Pr[mu_sub].
have e5 : Pr[K(Seq).main() @ &m : Kv.b] <= Pr[K(Seq).main() @ &m : Kv.b /\ Kv.ok] + Pr[K(Seq).main() @ &m : !Kv.ok].
- have : Pr[K(Seq).main() @ &m : Kv.b] <= Pr[K(Seq).main() @ &m : (Kv.b /\ Kv.ok) \/ !Kv.ok].
  + by rewrite Pr[mu_sub] => // &hr /#.
  rewrite Pr[mu_or]; smt(mu_bounded).
smt().
qed.

(* The distinguisher stops, so the cutoff event of the sequential rule is one of the generation. *)
local lemma cut_gen &m : Pr[GenGame(Setup0P(Seq), D).main() @ &m : !last false Trials.outs] =
  Pr[Setup0P(Seq).run() @ &m : !last false Trials.outs].
proof.
byequiv => //; proc*; inline GenGame(Setup0P(Seq), D).main; wp.
call{1} (_ : true ==> true).
- by apply (D_ll IP); proc; inline *; auto => />; smt(dans_ll dseed_ll dct_ll ddata_ll).
by wp; call (_ : true ==> ={res, Trials.outs}); [sim | auto].
qed.

(* A covered rule gives the probability of the run with the value drawn uniformly from the passing
   set, on the event that this set is not empty. *)
local lemma fr_cov (Ru <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                                -Trials, -Gen, -D, -TB, -Sv, -VV.RO, -VV.FRO, -Kv}) :
  hoare [Ru(Rec(TB)).select : Trials.outs = [] ==> 0 <= res < size Trials.outs /\ nth false Trials.outs res] =>
  (forall (p0 : real), phoare [Ru(Rec(TB)).select : TB.p = p0 /\ Trials.outs = [] /\ 0%r < p0 <= 1%r ==>
                                0 <= res < size Trials.outs /\ nth false Trials.outs res] = 1%r) =>
  forall &m, Pr[GenGame(Setup0P(Ru), D).main() @ &m : res] =
             Pr[Pre.main() @ &m : res /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)].
proof.
move=> hp hs &m.
have c := chain Ru (fun b _ => b) &m.
have a1 : Pr[FR(Ru).main() @ &m : res /\ (0 <= Sv.i < size Trials.outs /\ nth false Trials.outs Sv.i)] =
          Pr[K(Ru).main() @ &m : Kv.b /\ Kv.ok] by byequiv (fr_k Ru) => // /#.
have a2 : Pr[FR(Ru).main() @ &m : !(0 <= Sv.i < size Trials.outs /\ nth false Trials.outs Sv.i)] =
          Pr[K(Ru).main() @ &m : !Kv.ok] by byequiv (fr_k Ru) => // /#.
have z : Pr[K(Ru).main() @ &m : !Kv.ok] = 0%r.
- byphoare => //; hoare; proc; wp; call hp; wp; call (_ : true ==> true); 1: by trivial.
  by auto.
have k := k_cov Ru hs &m.
have s : Pr[FR(Ru).main() @ &m : res /\ !(0 <= Sv.i < size Trials.outs /\ nth false Trials.outs Sv.i)] <=
         Pr[FR(Ru).main() @ &m : !(0 <= Sv.i < size Trials.outs /\ nth false Trials.outs Sv.i)].
- by rewrite Pr[mu_sub] => /#.
move: c; rewrite /= => ->; rewrite Pr[mu_split (0 <= Sv.i < size Trials.outs /\ nth false Trials.outs Sv.i)].
smt(mu_bounded).
qed.

local lemma rl_cov &m : Pr[GenGame(Setup0P(Rl), D).main() @ &m : res] =
  Pr[Pre.main() @ &m : res /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)].
proof. by apply (fr_cov Rl (Rl_pass TB) (sel_cov Rl (Rl_pass TB) (Rl_ll (Rec(TB))))). qed.

(* Two covered rules give the same distribution: every covered rule gives that of the sequential
   rule of the specification. *)
lemma selection_eq &m :
  Pr[GenGame(Setup0P(Rl), D).main() @ &m : res] = Pr[GenGame(Setup0P(SeqU), D).main() @ &m : res].
proof.
rewrite (rl_cov &m).
by rewrite (fr_cov SeqU (SeqU_pass TB) (sel_cov SeqU (SeqU_pass TB) (SeqU_ll (Rec(TB)))) &m).
qed.

(* A covered rule and the sequential rule cut off after ntr trials differ at most by the chance
   that the cut rule reaches its cutoff without a passing trial. *)
lemma selection &m :
  `| Pr[GenGame(Setup0P(Rl), D).main() @ &m : res] - Pr[GenGame(Setup0P(Seq), D).main() @ &m : res] |
    <= Pr[Setup0P(Seq).run() @ &m : !last false Trials.outs].
proof.
have k1 := rl_cov &m.
have c2 := chain Seq (fun b _ => b) &m.
have c3 := chain Seq (fun _ outs => !last false outs) &m.
have k2 := k_seq &m.
have g := cut_gen &m.
have a3 : Pr[FR(Seq).main() @ &m : res /\ (0 <= Sv.i < size Trials.outs /\ nth false Trials.outs Sv.i)] =
          Pr[K(Seq).main() @ &m : Kv.b /\ Kv.ok] by byequiv (fr_k Seq) => // /#.
have a4 : Pr[FR(Seq).main() @ &m : !(0 <= Sv.i < size Trials.outs /\ nth false Trials.outs Sv.i)] =
          Pr[K(Seq).main() @ &m : !Kv.ok] by byequiv (fr_k Seq) => // /#.
have a5 : Pr[FR(Seq).main() @ &m : !last false Trials.outs] = Pr[K(Seq).main() @ &m : !last false Trials.outs].
- by byequiv (fr_k Seq) => // /#.
have s3 : Pr[FR(Seq).main() @ &m : res] <=
          Pr[FR(Seq).main() @ &m : res /\ (0 <= Sv.i < size Trials.outs /\ nth false Trials.outs Sv.i)] +
          Pr[FR(Seq).main() @ &m : !(0 <= Sv.i < size Trials.outs /\ nth false Trials.outs Sv.i)].
- rewrite Pr[mu_split (0 <= Sv.i < size Trials.outs /\ nth false Trials.outs Sv.i)].
  have : Pr[FR(Seq).main() @ &m : res /\ !(0 <= Sv.i < size Trials.outs /\ nth false Trials.outs Sv.i)] <=
         Pr[FR(Seq).main() @ &m : !(0 <= Sv.i < size Trials.outs /\ nth false Trials.outs Sv.i)].
  + by rewrite Pr[mu_sub] => /#.
  smt().
have s4 : Pr[FR(Seq).main() @ &m : res /\ (0 <= Sv.i < size Trials.outs /\ nth false Trials.outs Sv.i)] <=
          Pr[FR(Seq).main() @ &m : res] by rewrite Pr[mu_sub].
move: c2 c3 => /= c2 c3.
smt().
qed.

(* With the cutoff bound: a covered rule changes any probability of the generation by at most 2^-256. *)
lemma selection_bound &m :
  `| Pr[GenGame(Setup0P(Rl), D).main() @ &m : res] - Pr[GenGame(Setup0P(Seq), D).main() @ &m : res] |
    <= inv (2%r ^ 256).
proof. by have := selection &m; have := seq_cutoff &m; smt(). qed.
end section Selection.

(* ---- The sequential rule with a limit and a failure -------------------------------------------- *)
(* The sequential rule stopped after n trials: the index of the first passing trial, or no index when
   none of them passed. *)
module SeqF (T : TRIALS) = {
  proc select(n : int) : int option = {
    var ok, i;
    ok <- false;
    i <- -1;
    while (!ok /\ i + 1 < n) { ok <@ T.trial(); i <- i + 1; }
    return if ok then Some i else None;
  }
}.

(* Θ0 with that rule and with the creation refusal. A generation that fails creates no container: the
   adversary does not run, and the game has no output. *)
module GameF (A : AdvP) (Rf : AFTERP) = {
  proc main(n : int) : (seed * (pw * pp)) option = {
    var io, y, om, out, r;
    R.RO.init(); RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Trials.q <- Gen.q; Trials.vals <- []; Trials.outs <- [];
    io <@ SeqF(Trials).select(n);
    r <- None;
    if (io <> None) {
      Gen.e <- nth witness Trials.vals (oget io);
      Gen.sd <@ RS.RO.get(Gen.e, Gen.q);
      y <@ Net(Ideal).enc(Gen.p, Gen.e);
      om <@ RW.RO.get(Gen.sd);
      if (y = Gen.e) {
        out <@ Rf.run(Gen.p, Gen.q, y);
      } else {
        CountP(IP).init();
        out <@ A(CountP(IP)).guess(y, om);
      }
      r <- Some out;
    }
    return r;
  }
}.

(* ---- Every covered rule, from the cut rule ---------------------------------------------------- *)
(* A game with refusal splits into the run without the refused branch and the refusal; both are
   distinguishers of the generation, so selection_bound moves each from the rule to the cut rule. *)
section Transfer.
declare op E : seed * (pw * pp) -> pw -> pp -> seed -> bool.
declare module Rl <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                           -Trials, -Gen, -Count, -CountP}.
declare axiom Rl_pass (T <: TRIALS {-Rl, -Trials}) :
  hoare [Rl(Rec(T)).select : Trials.outs = [] ==>
           0 <= res < size Trials.outs /\ nth false Trials.outs res].
declare axiom Rl_ll (T <: TRIALS {-Rl}) (P : glob T -> bool) (b : real) :
  0%r < b => phoare [T.trial : P (glob T) ==> P (glob T) /\ res] = b =>
  phoare [T.trial : P (glob T) ==> P (glob T)] = 1%r =>
  phoare [Rl(T).select : P (glob T) ==> true] = 1%r.
declare module A <: AdvP {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                          -RTE.FunRO, -RW.RO, -Trials, -Gen, -Count, -CountP, -Rl}.
declare axiom A_ll (O <: OraclesP {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless A(O).guess.
declare module Rf <: AFTERP {-Gen}.
declare axiom Rf_ll : islossless Rf.run.

local module DE (O : OraclesP) = {
  var r : bool
  proc run(y : state, om : data, p : pw, q : pp, e : state, sd : seed) : bool = {
    var out, b;
    r <- y = e;
    b <- false;
    if (!r) { CountP(O).init(); out <@ A(CountP(O)).guess(y, om); b <- E out p q sd; }
    return b;
  }
}.

local module DR (O : OraclesP) = {
  proc run(y : state, om : data, p : pw, q : pp, e : state, sd : seed) : bool = { return y = e; }
}.

local lemma DE_ll (O <: OraclesP {-DE}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless DE(O).run.
proof.
move=> ha hb hh hs ht hw; proc; sp; if => //; wp.
call (A_ll (CountP(O)) _ _ _ _ _ _); 1..6: by proc; inline *; wp; (call ha || call hb || call hh ||
  call hs || call ht || call hw); auto.
by inline *; auto.
qed.

local lemma DR_ll (O <: OraclesP {-DR}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless DR(O).run.
proof. by move=> *; proc; auto. qed.

(* The refused branch of the game is the refusal of the distinguisher. *)
local lemma split_up (Ru <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                                  -Trials, -Gen, -Count, -CountP, -A, -DE}) &m :
  Pr[GamePR(Setup0P(Ru), A, Rf).main() @ &m : E res Gen.p Gen.q Gen.sd] <=
  Pr[GenGame(Setup0P(Ru), DE).main() @ &m : res \/ DE.r].
proof.
byequiv => //; proc; inline DE(IP).run.
seq 1 1 : (={y, om, glob A, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); 1: by sim => /#.
sp; if{1}.
- rcondf{2} 1; 1: by auto => /#.
  by wp; call{1} Rf_ll; auto => /#.
rcondt{2} 1; 1: by auto => /#.
wp; call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct,
              CountP.cw}); 1..6: by sim.
by inline *; auto => /> /#.
qed.

local lemma split_lo (Ru <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                                  -Trials, -Gen, -Count, -CountP, -A, -DE}) &m :
  Pr[GenGame(Setup0P(Ru), DE).main() @ &m : res] <=
  Pr[GamePR(Setup0P(Ru), A, Rf).main() @ &m : E res Gen.p Gen.q Gen.sd].
proof.
byequiv => //; proc; inline DE(IP).run.
seq 1 1 : (={y, om, glob A, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); 1: by sim => /#.
sp; if{2}.
- rcondf{1} 1; 1: by auto => /#.
  by wp; call{2} Rf_ll; auto.
rcondt{1} 1; 1: by auto => /#.
wp; call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct,
              CountP.cw}); 1..6: by sim.
by inline *; auto => /> /#.
qed.

local lemma ref_DR (Ru <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                                -Trials, -Gen, -Count, -CountP, -A, -DE}) &m :
  Pr[GenGame(Setup0P(Ru), DE).main() @ &m : DE.r] = Pr[GenGame(Setup0P(Ru), DR).main() @ &m : res].
proof.
byequiv => //; proc; inline DE(IP).run DR(IP).run.
seq 1 1 : (={y, Gen.e}); 1: by sim => /#.
sp; if{1}; last by auto.
wp; call{1} (A_ll (CountP(IP)) _ _ _ _ _ _); 1..6: by proc; inline *; auto => />;
  smt(dans_ll dseed_ll dct_ll ddata_ll).
by inline *; auto.
qed.

(* Without refusal in the cut game, the distinguisher wins at most when the game does, and the game
   at most when the distinguisher wins or refuses. *)
local lemma p_lo &m : Pr[GenGame(Setup0P(Seq), DE).main() @ &m : res] <=
  Pr[GameP(Setup0P(Seq), A).main() @ &m : E res Gen.p Gen.q Gen.sd].
proof.
byequiv => //; proc; inline DE(IP).run.
seq 1 1 : (={y, om, glob A, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); 1: by sim => /#.
sp; if{1}.
- wp; call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct,
                CountP.cw}); 1..6: by sim.
  by inline *; auto => /> /#.
wp; call{2} (A_ll (CountP(IP)) _ _ _ _ _ _); 1..6: by proc; inline *; auto => />;
  smt(dans_ll dseed_ll dct_ll ddata_ll).
by inline *; auto.
qed.

local lemma p_up &m : Pr[GameP(Setup0P(Seq), A).main() @ &m : E res Gen.p Gen.q Gen.sd] <=
  Pr[GenGame(Setup0P(Seq), DE).main() @ &m : res \/ DE.r].
proof.
byequiv => //; proc; inline DE(IP).run.
seq 1 1 : (={y, om, glob A, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); 1: by sim => /#.
sp; if{2}.
- wp; call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct,
                CountP.cw}); 1..6: by sim.
  by inline *; auto => /> /#.
wp; call{1} (A_ll (CountP(IP)) _ _ _ _ _ _); 1..6: by proc; inline *; auto => />;
  smt(dans_ll dseed_ll dct_ll ddata_ll).
by inline *; auto => /#.
qed.

local lemma dr_seq &m : Pr[GenGame(Setup0P(Seq), DR).main() @ &m : res] <= inv (2%r ^ 256).
proof.
have <- : Pr[Setup0P(Seq).run() @ &m : res.`1 = Gen.e] = Pr[GenGame(Setup0P(Seq), DR).main() @ &m : res].
- byequiv => //; proc*; inline GenGame(Setup0P(Seq), DR).main DR(IP).run; wp.
  by call (_ : true ==> ={res, Gen.e}); [sim | auto].
exact setup_refused.
qed.

(* The rule with a limit of n trials and a failure. A failure wins nothing. When the rule selects a
   phrase within ntr trials, the cut rule selects the same one; it selects one later only if the cut
   rule ends at its cutoff without a passing trial. So an event of its game costs at most what it
   costs with the cut rule, the refusal and the cutoff. *)
local lemma capped_split &m (cap : int) :
  Pr[GameF(A, Rf).main(cap) @ &m : res <> None /\ E (oget res) Gen.p Gen.q Gen.sd] <=
  Pr[GenGame(Setup0P(Seq), DE).main() @ &m : res \/ DE.r \/ !last false Trials.outs].
proof.
have [he _] := net_ll Ideal _ _ _; 1..3: by proc; inline *; auto; smt(dans_ll).
have hIP : islossless CountP(IP).a /\ islossless CountP(IP).b /\ islossless CountP(IP).h /\
           islossless CountP(IP).s /\ islossless CountP(IP).t /\ islossless CountP(IP).w.
- by do !split; proc; inline *; auto => />; smt(dans_ll dseed_ll dct_ll ddata_ll).
byequiv (_ : ={glob A} /\ n{1} = cap ==>
              (res{1} <> None /\ E (oget res{1}) Gen.p{1} Gen.q{1} Gen.sd{1}) =>
              (res{2} \/ DE.r{2} \/ !last false Trials.outs{2})) => //.
proc.
inline{2} Setup0P(Seq).run Seq(Trials).select.
inline{1} SeqF(Trials).select.
splitwhile{1} 13 : (i + 1 < ntr).
splitwhile{2} 12 : (i0 + 1 < cap).
seq 13 12 : (={glob A, ok, Gen.p, Gen.q, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Trials.q, Trials.vals, Trials.outs} /\
             i{1} = i0{2} /\ n0{1} = cap /\ ok{2} = last false Trials.outs{2} /\
             (!ok{1} => cap <= i{1} + 1 \/ ntr <= i{1} + 1)).
- while (={ok, RS.RO.m, RT.RO.m, Trials.q, Trials.vals, Trials.outs} /\ i{1} = i0{2} /\ n0{1} = cap /\
         ok{2} = last false Trials.outs{2}).
  + wp; call (_ : ={RS.RO.m, RT.RO.m, Trials.q, Trials.vals, Trials.outs} ==>
                  ={res, RS.RO.m, RT.RO.m, Trials.q, Trials.vals, Trials.outs} /\
                  res{2} = last false Trials.outs{2}).
    * by proc; inline *; auto => />; smt(last_rcons).
    by auto => /> /#.
  by inline *; auto => /> /#.
case (ok{1}).
- (* a phrase is selected within ntr trials: the cut rule has stopped at the same trial *)
  rcondf{1} 1; 1: by move=> &2; auto => /> /#.
  rcondf{2} 1; 1: by move=> &1; auto => /> /#.
  rcondt{1} 3; 1: by move=> &2; auto => /> /#.
  seq 6 6 : (={glob A, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, y, om}).
  + wp; call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
    call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
    call (_ : ={arg, RS.RO.m} ==> ={res, RS.RO.m}); 1: by sim.
    by auto => /> /#.
  inline{2} DE(IP).run.
  sp; if{1}.
  + rcondf{2} 1; 1: by auto => /#.
    by wp; call{1} Rf_ll; auto => /#.
  rcondt{2} 1; 1: by auto => /#.
  wp; call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct,
                CountP.cw}); 1..6: by sim.
  by inline *; auto => /> /#.
case (cap <= i{1} + 1).
- (* the limit is reached without a passing trial: no container, and the cut rule's game only ends *)
  rcondf{1} 1; 1: by move=> &2; auto => /> /#.
  rcondf{1} 3; 1: by move=> &2; auto => /> /#.
  call{2} (DE_ll IP _ _ _ _ _ _); 1..6: by proc; inline *; auto => />; smt(dans_ll dseed_ll dct_ll ddata_ll).
  wp; call{2} rw_get_ll; call{2} he; call{2} rs_get_ll; wp.
  while{2} true (ntr - i0{2}).
  + by move=> &1 z; inline *; auto => />; smt(dstate_ll dseed_ll dct_ll).
  by auto => /> /#.
(* the cut rule ends at its cutoff without a passing trial, while the rule with the limit goes on *)
rcondf{2} 1; 1: by move=> &1; auto => /> /#.
call{2} (DE_ll IP _ _ _ _ _ _); 1..6: by proc; inline *; auto => />; smt(dans_ll dseed_ll dct_ll ddata_ll).
wp; call{2} rw_get_ll; call{2} he; call{2} rs_get_ll; wp.
seq 1 0 : (!last false Trials.outs{2}).
- while{1} (!last false Trials.outs{2}) (n0{1} - i{1}).
  + by move=> &2 z; inline *; auto => />; smt(dstate_ll dseed_ll dct_ll).
  by auto => /> /#.
sp 2 0; if{1}; 2: by auto => /> /#.
seq 4 0 : (!last false Trials.outs{2}).
- by call{1} rw_get_ll; call{1} he; call{1} rs_get_ll; auto => /> /#.
wp; if{1}.
- by call{1} Rf_ll; auto => /> /#.
have [ha [hb [hh [hs [ht hw]]]]] := hIP.
by call{1} (A_ll (CountP(IP)) ha hb hh hs ht hw); inline CountP(IP).init Count(IP).init; auto => /> /#.
qed.

(* The cutoff of the cut rule, seen at the end of the distinguisher's game. *)
local lemma cut_DE &m : Pr[GenGame(Setup0P(Seq), DE).main() @ &m : !last false Trials.outs] <= inv (2%r ^ 256).
proof.
have <- : Pr[Setup0P(Seq).run() @ &m : !last false Trials.outs] =
          Pr[GenGame(Setup0P(Seq), DE).main() @ &m : !last false Trials.outs].
- byequiv => //; proc*; inline GenGame(Setup0P(Seq), DE).main; wp.
  call{2} (DE_ll IP _ _ _ _ _ _); 1..6: by proc; inline *; auto => />; smt(dans_ll dseed_ll dct_ll ddata_ll).
  by call (_ : true ==> ={Trials.outs}); [sim | auto].
exact seq_cutoff.
qed.

lemma capped_up &m (n0 : int) :
  Pr[GameF(A, Rf).main(n0) @ &m : res <> None /\ E (oget res) Gen.p Gen.q Gen.sd] <=
  Pr[GameP(Setup0P(Seq), A).main() @ &m : E res Gen.p Gen.q Gen.sd] + 2%r * inv (2%r ^ 256).
proof.
have h1 := capped_split &m n0.
have h2 := ref_DR Seq &m.
have h3 := p_lo &m.
have h4 := dr_seq &m.
have h5 := cut_DE &m.
have h6 : Pr[GenGame(Setup0P(Seq), DE).main() @ &m : res \/ DE.r \/ !last false Trials.outs] <=
          Pr[GenGame(Setup0P(Seq), DE).main() @ &m : res] + Pr[GenGame(Setup0P(Seq), DE).main() @ &m : DE.r] +
          Pr[GenGame(Setup0P(Seq), DE).main() @ &m : !last false Trials.outs].
- by rewrite Pr[mu_or] Pr[mu_or]; smt(mu_bounded).
smt().
qed.

(* Theorem 5 and Corollary W5 move to a covered rule at a cost of 3 * 2^-256, Proposition W7 at a
   cost of 2 * 2^-256; W2's constant deltacut leaves room for both inside delta_gen. *)
lemma rule_up &m : Pr[GamePR(Setup0P(Rl), A, Rf).main() @ &m : E res Gen.p Gen.q Gen.sd] <=
  Pr[GameP(Setup0P(Seq), A).main() @ &m : E res Gen.p Gen.q Gen.sd] + 3%r * inv (2%r ^ 256).
proof.
have h1 := split_up Rl &m.
have h2 := ref_DR Rl &m.
have s1 := selection_bound Rl DE Rl_pass Rl_ll DE_ll &m.
have s2 := selection_bound Rl DR Rl_pass Rl_ll DR_ll &m.
have h3 := p_lo &m.
have h4 := dr_seq &m.
have h5 : Pr[GenGame(Setup0P(Rl), DE).main() @ &m : res \/ DE.r] <=
          Pr[GenGame(Setup0P(Rl), DE).main() @ &m : res] + Pr[GenGame(Setup0P(Rl), DE).main() @ &m : DE.r].
- by rewrite Pr[mu_or]; smt(mu_bounded).
smt().
qed.

lemma rule_lo &m : Pr[GameP(Setup0P(Seq), A).main() @ &m : E res Gen.p Gen.q Gen.sd] - 2%r * inv (2%r ^ 256) <=
  Pr[GamePR(Setup0P(Rl), A, Rf).main() @ &m : E res Gen.p Gen.q Gen.sd].
proof.
have h1 := split_lo Rl &m.
have s1 := selection_bound Rl DE Rl_pass Rl_ll DE_ll &m.
have h2 := p_up &m.
have h3 := ref_DR Seq &m.
have h4 := dr_seq &m.
have h5 : Pr[GenGame(Setup0P(Seq), DE).main() @ &m : res \/ DE.r] <=
          Pr[GenGame(Setup0P(Seq), DE).main() @ &m : res] + Pr[GenGame(Setup0P(Seq), DE).main() @ &m : DE.r].
- by rewrite Pr[mu_or]; smt(mu_bounded).
smt().
qed.
end section Transfer.

(* ---- Lemma W2 for every covered rule ---------------------------------------------------------- *)
(* In particular for the sequential rule of the specification, SeqU (SeqU_pass, SeqU_ll). *)
section W2.
declare op kS : int.
declare op qT : int.
declare module Rl <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                           -Trials, -Gen, -Count, -CountP}.
declare axiom Rl_pass (T <: TRIALS {-Rl, -Trials}) :
  hoare [Rl(Rec(T)).select : Trials.outs = [] ==>
           0 <= res < size Trials.outs /\ nth false Trials.outs res].
declare axiom Rl_ll (T <: TRIALS {-Rl}) (P : glob T -> bool) (b : real) :
  0%r < b => phoare [T.trial : P (glob T) ==> P (glob T) /\ res] = b =>
  phoare [T.trial : P (glob T) ==> P (glob T)] = 1%r =>
  phoare [Rl(T).select : P (glob T) ==> true] = 1%r.
declare module J <: ADVJ {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                          -Gen, -Trials, -Count, -CountP, -Rl}.
declare axiom J_bounded (O <: OraclesP {-Count, -CountP, -J}) :
  hoare [J(CountP(O)).run :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    CountP.cs <= kS /\ CountP.ct <= qT].
declare axiom J_ll (O <: OraclesP {-J}) :
  (islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
   islossless O.w => islossless J(O).run) /\
  (islossless O.a => islossless O.b => islossless O.h => islossless O.w => islossless J(O).judge).

local module DJ (O : OraclesP) = {
  proc run(y : state, om : data, p : pw, q : pp, e : state, sd : seed) : bool = {
    var b;
    CountP(O).init();
    J(CountP(O)).run(y, om);
    b <@ J(CountP(O)).judge(p, q, e, sd);
    return b;
  }
}.

local lemma DJ_ll (O <: OraclesP {-DJ}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless DJ(O).run.
proof.
move=> ha hb hh hs ht hw; have [hr hj] := J_ll (CountP(O)); proc.
call (hj _ _ _ _); 1..4: by proc; inline *; wp; (call ha || call hb || call hh || call hw); auto.
call (hr _ _ _ _ _ _); 1..6: by proc; inline *; wp;
  (call ha || call hb || call hh || call hs || call ht || call hw); auto.
by inline *; auto.
qed.

lemma W2 &m : 0 <= kS => 0 <= qT =>
  `| Pr[Judged(Setup0P(Rl), J).main() @ &m : res] - Pr[Judged(Setup0P', J).main() @ &m : res] |
    <= deltagen kS qT.
proof.
move=> hkS hqT.
have h1 := W2_cut kS qT J J_bounded J_ll &m hkS hqT.
have s := selection_bound Rl DJ Rl_pass Rl_ll DJ_ll &m.
have e1 : Pr[Judged(Setup0P(Rl), J).main() @ &m : res] = Pr[GenGame(Setup0P(Rl), DJ).main() @ &m : res].
- by byequiv => //; proc; inline DJ(IP).run; wp; sim.
have e2 : Pr[Judged(Setup0P(Seq), J).main() @ &m : res] = Pr[GenGame(Setup0P(Seq), DJ).main() @ &m : res].
- by byequiv => //; proc; inline DJ(IP).run; wp; sim.
have := deltacut_le kS qT hkS hqT.
smt(expr_gt0 invr_gt0).
qed.
end section W2.
