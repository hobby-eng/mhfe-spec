(* The chain of Selection.ec for a continuation that also receives the outcomes of the owner's
   trials (DESIGN-NOTES A.6, "The number of trials"). *)
require import AllCore List Distr DBool DProd FMap IntDiv StdBigop StdOrder Xreal.
require import Suite3 Chain Collision Passphrase Generation Selection.
require (*--*) PROM.
import W128 StdBigop.Bigreal.BRA RealOrder.

(* A continuation that also sees the outcomes of the owner's trials. *)
module type CONTO (O : OraclesP) = {
  proc run(y : state, om : data, p : pw, q : pp, e : state, sd : seed, outs : bool list) : bool
}.

module GenGameO (S : SETUPP) (D : CONTO) = {
  proc main() : bool = {
    var y, om, b;
    (y, om) <@ S.run();
    b <@ D(IP).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd, Trials.outs);
    return b;
  }
}.

(* ---- S and T as whole functions ---- *)
module TrGO (GS : RS.RO) (GT : RT.RO) = {
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

module IPSTO (GS : RS.RO) (GT : RT.RO) : OraclesP = {
  proc a = Ideal.a
  proc b = Ideal.b
  proc h = Ideal.h
  proc s(e : state, q : pp) = { var d; d <@ GS.get(e, q); return d; }
  proc t(d : seed) = { var c; c <@ GT.get(d); return c; }
  proc w = IP.w
}.

module GGO (Ru : RULE) (D : CONTO) (GS : RS.RO) (GT : RT.RO) = {
  proc main() : bool = {
    var i, y, om, b;
    R.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Trials.q <- Gen.q; Trials.vals <- []; Trials.outs <- [];
    i <@ Ru(TrGO(GS, GT)).select();
    Gen.e <- nth witness Trials.vals i;
    Gen.sd <@ GS.get(Gen.e, Gen.q);
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    b <@ D(IPSTO(GS, GT)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd, Trials.outs);
    return b;
  }
}.

module DSdO (Ru : RULE) (D : CONTO) (GS : RS.RO) = {
  proc distinguish() : bool = { var b; RT.RO.init(); b <@ GGO(Ru, D, GS, RT.RO).main(); return b; }
}.

module DTdO (Ru : RULE) (D : CONTO) (GT : RT.RO) = {
  proc distinguish() : bool = { var b; RSE.FunRO.init(); b <@ GGO(Ru, D, RSE.FunRO, GT).main(); return b; }
}.

lemma to_eagerO (Ru <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                             -Trials, -Gen})
                (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                             -RTE.FunRO, -RW.RO, -Trials, -Gen, -Ru})
                (E : bool -> bool list -> bool) &m :
  Pr[GenGameO(Setup0P(Ru), D).main() @ &m : E res Trials.outs] =
  Pr[RT.MainD(DTdO(Ru, D), RTE.FunRO).distinguish() @ &m : E res Trials.outs].
proof.
have -> : Pr[GenGameO(Setup0P(Ru), D).main() @ &m : E res Trials.outs] =
          Pr[RS.MainD(DSdO(Ru, D), RS.RO).distinguish() @ &m : E res Trials.outs].
- byequiv (_ : ={glob D, glob Ru} ==> ={res, Trials.outs}) => //; proc.
  inline Setup0P(Ru).run DSdO(Ru, D, RS.RO).distinguish GGO(Ru, D, RS.RO, RT.RO).main; wp.
  call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); 1..6: by sim.
  wp; call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
  call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
  call (_ : ={arg, RS.RO.m} ==> ={res, RS.RO.m}); 1: by sim.
  wp; call (_ : ={RS.RO.m, RT.RO.m, Trials.q, Trials.vals, Trials.outs}); 1: by sim.
  by inline *; auto.
have -> : Pr[RS.MainD(DSdO(Ru, D), RS.RO).distinguish() @ &m : E res Trials.outs] =
          Pr[RS.MainD(DSdO(Ru, D), RSE.FunRO).distinguish() @ &m : E res Trials.outs].
- byequiv (_ : ={glob DSdO(Ru, D), arg} ==> ={res, glob DSdO(Ru, D)}) => //.
  transitivity RS.MainD(DSdO(Ru, D), RSE.FinRO).distinguish
    (={glob DSdO(Ru, D), arg} ==> ={res, glob DSdO(Ru, D)})
    (={glob DSdO(Ru, D), arg} ==> ={res, glob DSdO(Ru, D)}) => //.
  + by move=> &1 &2 h; exists (glob D){1} (glob Ru){1} Gen.e{1} Gen.p{1} Gen.q{1} Gen.sd{1} Trials.outs{1}
      Trials.q{1} Trials.vals{1} RT.RO.m{1} RW.RO.m{1} R.RO.m{1} arg{1}.
  + by apply (RSE.RO_FinRO_D _ (DSdO(Ru, D))) => _; exact dseed_ll.
  by apply (RSE.FinRO_FunRO_D _ (DSdO(Ru, D))) => _; exact dseed_ll.
have -> : Pr[RS.MainD(DSdO(Ru, D), RSE.FunRO).distinguish() @ &m : E res Trials.outs] =
          Pr[RT.MainD(DTdO(Ru, D), RT.RO).distinguish() @ &m : E res Trials.outs].
- by byequiv (_ : ={glob D, glob Ru} ==> ={res, Trials.outs}) => //; proc; inline *; sim; auto.
byequiv (_ : ={glob DTdO(Ru, D), arg} ==> ={res, glob DTdO(Ru, D)}) => //.
transitivity RT.MainD(DTdO(Ru, D), RTE.FinRO).distinguish
  (={glob DTdO(Ru, D), arg} ==> ={res, glob DTdO(Ru, D)})
  (={glob DTdO(Ru, D), arg} ==> ={res, glob DTdO(Ru, D)}) => //.
- by move=> &1 &2 h; exists (glob D){1} (glob Ru){1} Gen.e{1} Gen.p{1} Gen.q{1} Gen.sd{1} Trials.outs{1}
    Trials.q{1} Trials.vals{1} RSE.FunRO.f{1} RW.RO.m{1} R.RO.m{1} arg{1}.
- by apply (RTE.RO_FinRO_D _ (DTdO(Ru, D))) => _; exact dct_ll.
by apply (RTE.FinRO_FunRO_D _ (DTdO(Ru, D))) => _; exact dct_ll.
qed.

(* ---- A trial as an outcome first, then a value given the outcome ---- *)
module TrSO = {
  proc trial() : bool = {
    var b, e;
    b <$ Biased.dbiased (mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q));
    e <$ dval RSE.FunRO.f RTE.FunRO.f Trials.q b;
    Trials.vals <- rcons Trials.vals e;
    Trials.outs <- rcons Trials.outs (pass RSE.FunRO.f RTE.FunRO.f Trials.q e);
    return pass RSE.FunRO.f RTE.FunRO.f Trials.q e;
  }
}.

clone DProd.DLetSampling as SDO with type t <- bool, type u <- state.

equiv trial_splitO : TrGO(RSE.FunRO, RTE.FunRO).trial ~ TrSO.trial :
  ={Trials.q, Trials.vals, Trials.outs, RSE.FunRO.f, RTE.FunRO.f} ==>
  ={res, Trials.q, Trials.vals, Trials.outs, RSE.FunRO.f, RTE.FunRO.f}.
proof.
proc; inline *.
outline {2} [1 .. 2] by { e <@ SDO.SampleDep.sample(Biased.dbiased (mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)),
                                                     dval RSE.FunRO.f RTE.FunRO.f Trials.q); }.
rewrite equiv[{2} 1 SDO.SampleDepDLet].
inline *; wp; rnd; auto => /> &2.
by rewrite /dval -(Biased.marginal_sampling_pred dstate _ dstate_ll).
qed.

module GESO (Ru : RULE) (D : CONTO) = {
  proc main() : bool = {
    var i, y, om, b;
    RTE.FunRO.init(); RSE.FunRO.init(); R.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Trials.q <- Gen.q; Trials.vals <- []; Trials.outs <- [];
    i <@ Ru(TrSO).select();
    Gen.e <- nth witness Trials.vals i;
    Gen.sd <@ RSE.FunRO.get(Gen.e, Gen.q);
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    b <@ D(IPSTO(RSE.FunRO, RTE.FunRO)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd, Trials.outs);
    return b;
  }
}.

lemma to_splitO (Ru <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                             -Trials, -Gen})
                (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                             -RTE.FunRO, -RW.RO, -Trials, -Gen, -Ru})
                (E : bool -> bool list -> bool) &m :
  Pr[RT.MainD(DTdO(Ru, D), RTE.FunRO).distinguish() @ &m : E res Trials.outs] =
  Pr[GESO(Ru, D).main() @ &m : E res Trials.outs].
proof.
byequiv (_ : ={glob D, glob Ru} ==> ={res, Trials.outs}) => //; proc.
inline DTdO(Ru, D, RTE.FunRO).distinguish GGO(Ru, D, RSE.FunRO, RTE.FunRO).main; wp.
call (_ : ={R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f}); 1..6: by sim.
wp; call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
call (_ : ={arg, RSE.FunRO.f} ==> ={res, RSE.FunRO.f}); 1: by sim.
wp; call (_ : ={Trials.q, Trials.vals, Trials.outs, RSE.FunRO.f, RTE.FunRO.f}); 1: by conseq trial_splitO.
by inline *; auto.
qed.

(* ---- The values of the trials, drawn only when read ---- *)
module TBO = {
  var p : real
  proc trial() : bool = { var b; b <$ Biased.dbiased p; return b; }
}.

module SvO = { var i : int }.

clone PROM.FullRO as VVO with
  type in_t <- int * bool * ((state * pp -> seed) * (seed -> W16.word * W240.word) * pp),
  type out_t <- state, op dout <- dtrial, type d_in_t <- unit, type d_out_t <- bool.

module TrVO (V : VVO.RO) = {
  proc trial() : bool = {
    var b;
    b <@ TBO.trial();
    V.sample((size Trials.outs, b, (RSE.FunRO.f, RTE.FunRO.f, Trials.q)));
    Trials.outs <- rcons Trials.outs b;
    return b;
  }
}.

module GVdO (Ru : RULE) (D : CONTO) (V : VVO.RO) = {
  proc distinguish() : bool = {
    var y, om, b;
    RTE.FunRO.init(); RSE.FunRO.init(); R.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Trials.q <- Gen.q; Trials.vals <- []; Trials.outs <- [];
    TBO.p <- mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q);
    SvO.i <@ Ru(TrVO(V)).select();
    Gen.e <- witness;
    if (0 <= SvO.i < size Trials.outs) {
      Gen.e <@ V.get((SvO.i, nth false Trials.outs SvO.i, (RSE.FunRO.f, RTE.FunRO.f, Trials.q)));
    }
    Gen.sd <@ RSE.FunRO.get(Gen.e, Gen.q);
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    b <@ D(IPSTO(RSE.FunRO, RTE.FunRO)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd, Trials.outs);
    return b;
  }
}.

lemma to_vvO (Ru <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                          -Trials, -Gen, -TBO, -SvO, -VVO.RO, -VVO.FRO})
             (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                          -RTE.FunRO, -RW.RO, -Trials, -Gen, -Ru, -TBO, -SvO, -VVO.RO, -VVO.FRO})
             (E : bool -> bool list -> bool) &m :
  Pr[GESO(Ru, D).main() @ &m : E res Trials.outs] =
  Pr[VVO.MainD(GVdO(Ru, D), VVO.RO).distinguish() @ &m : E res Trials.outs].
proof.
byequiv (_ : ={glob D, glob Ru} ==> ={res, Trials.outs}) => //; proc.
inline GVdO(Ru, D, VVO.RO).distinguish; wp.
call (_ : ={R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f}); 1..6: by sim.
wp; call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
call (_ : ={arg, RSE.FunRO.f} ==> ={res, RSE.FunRO.f}); 1: by sim.
conseq (_ : _ ==> ={glob D, Gen.p, Gen.q, Gen.e, R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f, Trials.outs}) => />.
seq 10 13 : (={glob D, Gen.p, Gen.q, R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f, Trials.q, Trials.outs} /\
             i{1} = SvO.i{2} /\
             vvinv VVO.RO.m{2} Trials.outs{2} Trials.vals{1} (RSE.FunRO.f{2}, RTE.FunRO.f{2}, Trials.q{2})).
- call (_ : ={RSE.FunRO.f, RTE.FunRO.f, Trials.q, Trials.outs} /\
            TBO.p{2} = mu dstate (pass RSE.FunRO.f{2} RTE.FunRO.f{2} Trials.q{2}) /\
            vvinv VVO.RO.m{2} Trials.outs{2} Trials.vals{1} (RSE.FunRO.f{2}, RTE.FunRO.f{2}, Trials.q{2})).
  + proc; inline TBO.trial VVO.RO.sample VVO.RO.get; wp.
    rnd; wp; rnd; auto => /> &1 &2 hs hk hv b hb.
    rewrite (dtrial_dval _ _ _ _ _ hb) /= => e he.
    have := vvinv_step VVO.RO.m{2} Trials.outs{2} Trials.vals{1} (RSE.FunRO.f{2}, RTE.FunRO.f{2}, Trials.q{2})
              b e _; 1: by [].
    by rewrite (dval_pass _ _ _ _ _ he) /vvinv /=; smt().
  by inline *; auto => />; smt(mem_empty).
sp; if{2}.
- inline{2} VVO.RO.get; rcondf{2} 3; 1: by auto => /> /#.
  by wp; rnd{2}; auto => />; smt(dtrial_ll).
by auto => />; smt(nth_default nth_neg).
qed.

module FRO (Ru : RULE) (D : CONTO) = {
  proc main() : bool = {
    var y, om, b;
    RTE.FunRO.init(); RSE.FunRO.init(); R.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Trials.q <- Gen.q; Trials.outs <- [];
    TBO.p <- mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q);
    SvO.i <@ Ru(Rec(TBO)).select();
    Gen.e <- witness;
    if (0 <= SvO.i < size Trials.outs) {
      Gen.e <$ dtrial (SvO.i, nth false Trials.outs SvO.i, (RSE.FunRO.f, RTE.FunRO.f, Trials.q));
    }
    Gen.sd <@ RSE.FunRO.get(Gen.e, Gen.q);
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    b <@ D(IPSTO(RSE.FunRO, RTE.FunRO)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd, Trials.outs);
    return b;
  }
}.

lemma chainO (Ru <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                          -Trials, -Gen, -TBO, -SvO, -VVO.RO, -VVO.FRO})
             (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                          -RTE.FunRO, -RW.RO, -Trials, -Gen, -Ru, -TBO, -SvO, -VVO.RO, -VVO.FRO})
             (E : bool -> bool list -> bool) &m :
  Pr[GenGameO(Setup0P(Ru), D).main() @ &m : E res Trials.outs] = Pr[FRO(Ru, D).main() @ &m : E res Trials.outs].
proof.
rewrite (to_eagerO Ru D E &m) (to_splitO Ru D E &m) (to_vvO Ru D E &m).
have -> : Pr[VVO.MainD(GVdO(Ru, D), VVO.RO).distinguish() @ &m : E res Trials.outs] =
          Pr[VVO.MainD(GVdO(Ru, D), VVO.LRO).distinguish() @ &m : E res Trials.outs].
- by byequiv (VVO.FullEager.RO_LRO (GVdO(Ru, D)) dtrial_ll) => //.
byequiv (_ : ={glob D, glob Ru} ==> ={res, Trials.outs}) => //; proc.
inline GVdO(Ru, D, VVO.LRO).distinguish; wp.
call (_ : ={R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f}); 1..6: by sim.
wp; call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
call (_ : ={arg, RSE.FunRO.f} ==> ={res, RSE.FunRO.f}); 1: by sim.
seq 13 10 : (={glob D, Gen.p, Gen.q, R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f, Trials.q, Trials.outs, SvO.i} /\
             VVO.RO.m{1} = empty).
- call (_ : ={TBO.p, Trials.outs} /\ VVO.RO.m{1} = empty); 1: by proc; inline *; auto.
  by inline *; auto.
by sp; if => //; inline *; auto => />; smt(mem_empty get_set_sameE).
qed.
