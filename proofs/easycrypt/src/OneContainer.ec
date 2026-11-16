(* One container of a short source: games Γ0, Γ1, Γ2, Lemmas G1 and G4, Theorem 3, Remark G9 and
   Corollaries G6, G7, G8, G10 (DESIGN-NOTES A.2-A.4). The theory is abstract in the source length;
   Instances.ec instantiates it. *)
require import AllCore List Distr DBool DProd FMap IntDiv StdBigop StdOrder Xreal.
require import Suite3 Chain Collision.
require (*--*) PROM DProd.
import W128 StdBigop.Bigreal.BRA RealOrder.

abstract theory Source.

(* ---- The source and the packing pack(E) = E || Trunc_r G(E) --------------------------------- *)
type ent, ver, rest.                       (* ENT-bit entropy; the r-bit verifier and the rest of a G output *)
op ENT : int.
op r : int.
axiom ENT_r : ENT + r = 256.
axiom ENT_range : 128 <= ENT <= 256.

op dent : ent distr.
axiom dent_ll : is_lossless dent.
axiom dent1 (e : ent) : mu1 dent e = inv (2%r ^ ENT).
op dver : ver distr.
axiom dver_ll : is_lossless dver.
axiom dver1 (v : ver) : mu1 dver v = inv (2%r ^ r).
op drest : rest distr.
axiom drest_ll : is_lossless drest.
axiom drest_funi : is_funiform drest.

type hash = ver * rest.                    (* a G output: Trunc_r is the first component *)
op dhash : hash distr = dver `*` drest.

op pack : ent -> ver -> state.
op unpack : state -> ent * ver.
axiom unpack_pack (e : ent) (v : ver) : unpack (pack e v) = (e, v).
axiom pack_unpack (x : state) : pack (unpack x).`1 (unpack x).`2 = x.
op lead : ent -> W128.word.                (* the first 128 bits of E, which are L_0 *)
axiom lead_pack (e : ent) (v : ver) : (pack e v).`1 = lead e.

clone import PROM.FullRO as RG with
  type in_t <- ent, type out_t <- hash, op dout <- (fun _ => dhash),
  type d_in_t <- unit, type d_out_t <- bool.

(* ---- Oracles of the adversary and their counts --------------------------------------------- *)
module type Oracles = {
  include ABHB
  proc g(e : ent) : hash
}.

module CountG (O : Oracles) = {
  var cg : int
  proc init() = { CountB(O).init(); cg <- 0; }
  proc a = CountB(O).a
  proc b = CountB(O).b
  proc h = CountB(O).h
  proc abatch = CountB(O).abatch
  proc g(e : ent) = { var v; cg <- cg + 1; v <@ O.g(e); return v; }
}.

(* The ideal oracles. [es] is e* and [bad] records a G query at e*. *)
module IG : Oracles = {
  var es  : ent
  var bad : bool
  proc a = Ideal.a
  proc b = Ideal.b
  proc h = Ideal.h
  proc abatch = Batch(Ideal).abatch
  proc g(e : ent) = { var v; if (e = es) bad <- true; v <@ RG.RO.get(e); return v; }
}.

(* ---- The challengers of Γ0, Γ1, Γ2 ---------------------------------------------------------- *)
(* Γ0: P is drawn, E is uniform, X = pack(E), Y = Perm_P(X); e* = E. *)
module Setup0 = {
  var x : state
  proc run() : pw * state = {
    var p, e, hv, y;
    R.RO.init(); RG.RO.init();
    p <$ dP;
    e <$ dent;
    hv <@ RG.RO.get(e);
    x <- pack e hv.`1;
    y <@ Net(Ideal).enc(p, x);
    IG.es <- e;
    return (p, y);
  }
}.

(* Γ1: Y is uniform, x* = Inv_P(Y), and G(e* ) is v* followed by uniform bits. *)
module Setup1 = {
  proc run() : pw * state = {
    var p, y, xs, rs;
    R.RO.init(); RG.RO.init();
    p <$ dP;
    y <$ dstate;
    xs <@ Net(Ideal).dec(p, y);
    rs <$ drest;
    RG.RO.set((unpack xs).`1, ((unpack xs).`2, rs));
    IG.es <- (unpack xs).`1;
    return (p, y);
  }
}.

(* Γ2: Γ1 without the programmed point. *)
module Setup2 = {
  proc run() : pw * state = {
    var p, y, xs;
    R.RO.init(); RG.RO.init();
    p <$ dP;
    y <$ dstate;
    xs <@ Net(Ideal).dec(p, y);
    IG.es <- (unpack xs).`1;
    return (p, y);
  }
}.

module type SETUP = { proc run() : pw * state }.

(* A game on a challenger: [C] plays the adversary's part against the counted oracles and decides
   the outcome; it receives P and E only to decide it. *)
module type PLAY (O : Oracles) = { proc play(p : pw, e : ent, y : state) : bool }.

module Game (S : SETUP) (C : PLAY) = {
  proc main() : bool = {
    var p, y, b;
    (p, y) <@ S.run();
    IG.bad <- false;
    CountG(IG).init();
    b <@ C(CountG(IG)).play(p, IG.es, y);
    return b;
  }
}.

(* Γ0 with creation refusal: if Y = X the owner changes the password or the settings; [R] stands for
   every possible continuation and decides the outcome itself. *)
module type AFTER = { proc run(p : pw, e : ent, y : state) : bool }.

module GameR (C : PLAY) (Rf : AFTER) = {
  proc main() : bool = {
    var p, y, b;
    (p, y) <@ Setup0.run();
    if (y = Setup0.x) {
      b <@ Rf.run(p, IG.es, y);
    } else {
      IG.bad <- false;
      CountG(IG).init();
      b <@ C(CountG(IG)).play(p, IG.es, y);
    }
    return b;
  }
}.

(* ---- The steps shared by every game on one container ---------------------------------------- *)
section G1.
declare module C <: PLAY {-R.RO, -R.FRO, -RE.FunRO, -IG, -Setup0, -Count, -CountB, -CountG}.

local module IGF (G : R.RO) : Oracles = {
  proc a = Orc(G).a
  proc b = Orc(G).b
  proc h = Orc(G).h
  proc abatch = Batch(Orc(G)).abatch
  proc g = IG.g
}.

(* Γ0 and Γ1 as programs on the oracle of A, B, H. *)
local module D0 (G : R.RO) = {
  proc distinguish() : bool = {
    var p, e, hv, y, b;
    RG.RO.init();
    p <$ dP;
    e <$ dent;
    hv <@ RG.RO.get(e);
    Setup0.x <- pack e hv.`1;
    y <@ Net(Orc(G)).enc(p, Setup0.x);
    IG.es <- e;
    IG.bad <- false;
    CountG(IGF(G)).init();
    b <@ C(CountG(IGF(G))).play(p, IG.es, y);
    return b;
  }
}.

local module D1 (G : R.RO) = {
  proc distinguish() : bool = {
    var p, y, xs, rs, b;
    RG.RO.init();
    p <$ dP;
    y <$ dstate;
    xs <@ Net(Orc(G)).dec(p, y);
    rs <$ drest;
    RG.RO.set((unpack xs).`1, ((unpack xs).`2, rs));
    IG.es <- (unpack xs).`1;
    IG.bad <- false;
    CountG(IGF(G)).init();
    b <@ C(CountG(IGF(G))).play(p, IG.es, y);
    return b;
  }
}.

(* The same with A, B, H sampled as a whole function in advance. *)
local module H0 = {
  proc main() : bool = {
    var p, e, hv, y, b;
    RE.FunRO.init(); RG.RO.init();
    p <$ dP;
    e <$ dent;
    hv <$ dhash;
    RG.RO.m <- RG.RO.m.[e <- hv];
    Setup0.x <- pack e hv.`1;
    y <- perm RE.FunRO.f p Setup0.x;
    IG.es <- e;
    IG.bad <- false;
    CountG(IGF(RE.FunRO)).init();
    b <@ C(CountG(IGF(RE.FunRO))).play(p, IG.es, y);
    return b;
  }
}.

local module H1 = {
  proc main() : bool = {
    var p, y, xs, rs, b;
    RE.FunRO.init(); RG.RO.init();
    p <$ dP;
    y <$ dstate;
    rs <$ drest;
    xs <- invperm RE.FunRO.f p y;
    RG.RO.m <- RG.RO.m.[(unpack xs).`1 <- ((unpack xs).`2, rs)];
    IG.es <- (unpack xs).`1;
    IG.bad <- false;
    CountG(IGF(RE.FunRO)).init();
    b <@ C(CountG(IGF(RE.FunRO))).play(p, IG.es, y);
    return b;
  }
}.

local clone DProd.ProdSampling as PS0 with type t1 <- ent, type t2 <- hash.
local clone DProd.ProdSampling as PS1 with type t1 <- state, type t2 <- rest.

(* The core of G1: (E, v, rest) and (Y, rest) correspond one to one through pack and Perm_P. *)
local equiv H0_H1 : H0.main ~ H1.main : ={glob C} ==> ={res, glob C, IG.bad}.
proof.
proc.
seq 3 3 : (={p, RE.FunRO.f, glob C} /\ RG.RO.m{1} = empty /\ RG.RO.m{2} = empty).
- by inline *; auto.
seq 6 5 : (={p, y, RE.FunRO.f, RG.RO.m, IG.es, glob C}); last by sim.
outline {1} [1 .. 2] ~ PS0.S.sample2.
rewrite equiv[{1} 1 -PS0.sample_sample2].
outline {2} [1 .. 2] ~ PS1.S.sample2.
rewrite equiv[{2} 1 -PS1.sample_sample2].
inline PS0.S.sample PS1.S.sample.
wp; rnd (fun (er : ent * hash) => (perm RE.FunRO.f{1} p{1} (pack er.`1 er.`2.`1), er.`2.`2))
        (fun (yr : state * rest) =>
           ((unpack (invperm RE.FunRO.f{1} p{1} yr.`1)).`1,
            ((unpack (invperm RE.FunRO.f{1} p{1} yr.`1)).`2, yr.`2))).
auto => /> &2; split.
- by move=> [y rs] _ /=; rewrite pack_unpack permK.
move=> _; split.
- move=> [y rs] _ /=; rewrite /dhash !dprod1E dstate1_256 dent1 dver1.
  have -> : inv (2%r ^ 256) = inv (2%r ^ ENT) * inv (2%r ^ r).
  + by rewrite -RField.invfM -RField.exprD_nneg; smt(ENT_r ENT_range).
  by ring.
move=> _ [e [v rs]] her /=; rewrite invpermK unpack_pack /=.
rewrite supp_dprod /=; split; 2: smt(supp_dprod).
rewrite /dstate supp_dprod; smt(funi_ll_full dhalf_funi dhalf_ll).
qed.

local equiv G0_D0 : Game(Setup0, C).main ~ R.MainD(D0, R.RO).distinguish :
  ={glob C} ==> ={res, glob C, IG.bad}.
proof. by proc; inline *; sim. qed.

local equiv G1_D1 : Game(Setup1, C).main ~ R.MainD(D1, R.RO).distinguish :
  ={glob C} ==> ={res, glob C, IG.bad}.
proof. by proc; inline *; sim. qed.

local equiv D0_H0 : R.MainD(D0, RE.FunRO).distinguish ~ H0.main : ={glob C} ==> ={res, glob C, IG.bad}.
proof.
proc; inline D0(RE.FunRO).distinguish.
seq 5 4 : (={p, e, RE.FunRO.f, glob C} /\ RG.RO.m{1} = empty /\ RG.RO.m{2} = empty).
- by inline *; auto.
seq 2 3 : (={p, e, hv, RE.FunRO.f, RG.RO.m, Setup0.x, glob C}).
- inline *; rcondt{1} ^if; 1: by auto => />; smt(mem_empty).
  by auto => />; smt(get_set_sameE).
seq 1 1 : (={p, e, y, RE.FunRO.f, RG.RO.m, glob C}); last by sim.
by exlim p{1}, Setup0.x{1} => p0 x0; call{1} (enc_fun_ph p0 x0); auto.
qed.

local equiv D1_H1 : R.MainD(D1, RE.FunRO).distinguish ~ H1.main : ={glob C} ==> ={res, glob C, IG.bad}.
proof.
proc; inline D1(RE.FunRO).distinguish.
seq 5 4 : (={p, y, RE.FunRO.f, RG.RO.m, glob C}).
- by inline *; auto.
seq 1 0 : (={p, y, RE.FunRO.f, RG.RO.m, glob C} /\ xs{1} = invperm RE.FunRO.f{1} p{1} y{1}).
- by exlim p{1}, y{1} => p0 y0; call{1} (dec_fun_ph p0 y0); auto.
swap{2} 2 -1; seq 0 1 : (={p, y, xs, RE.FunRO.f, RG.RO.m, glob C}); 1: by auto.
seq 2 2 : (={p, y, xs, rs, RE.FunRO.f, RG.RO.m, glob C}); 1: by inline *; auto.
by sim.
qed.

lemma G1 : equiv [Game(Setup0, C).main ~ Game(Setup1, C).main : ={glob C} ==> ={res, glob C, IG.bad}].
proof.
transitivity H0.main (={glob C} ==> ={res, glob C, IG.bad}) (={glob C} ==> ={res, glob C, IG.bad}) => //.
- by move=> &1 &2 h; exists (glob C){1}.
- transitivity R.MainD(D0, RE.FunRO).distinguish
    (={glob C} ==> ={res, glob C, IG.bad}) (={glob C} ==> ={res, glob C, IG.bad}) => //.
  + by move=> &1 &2 h; exists (glob C){1}.
  + transitivity R.MainD(D0, R.RO).distinguish
      (={glob C} ==> ={res, glob C, IG.bad}) (={glob D0, arg} ==> ={res, glob D0}) => //.
    * move=> &1 &2 h.
      by exists (glob C){2} CountB.dp{2} CountG.cg{2} IG.bad{2} IG.es{2} Setup0.x{2}
                Count.ca{2} Count.cb{2} Count.ch{2} RG.RO.m{2} arg{2}.
    * exact G0_D0.
    exact (RO_FunRO D0).
  exact D0_H0.
transitivity H1.main (={glob C} ==> ={res, glob C, IG.bad}) (={glob C} ==> ={res, glob C, IG.bad}) => //.
- by move=> &1 &2 h; exists (glob C){1}.
- exact H0_H1.
transitivity R.MainD(D1, RE.FunRO).distinguish
  (={glob C} ==> ={res, glob C, IG.bad}) (={glob C} ==> ={res, glob C, IG.bad}) => //.
- by move=> &1 &2 h; exists (glob C){1}.
- by symmetry; conseq D1_H1.
transitivity R.MainD(D1, R.RO).distinguish
  (={glob D1, arg} ==> ={res, glob D1}) (={glob C} ==> ={res, glob C, IG.bad}) => //.
- move=> &1 &2 h.
  by exists (glob C){1} CountB.dp{1} CountG.cg{1} IG.bad{1} IG.es{1}
            Count.ca{1} Count.cb{1} Count.ch{1} RG.RO.m{1} arg{1}.
- by symmetry; conseq (RO_FunRO D1).
by symmetry; conseq G1_D1.
qed.
end section G1.

section Refusal.
declare module C <: PLAY {-R.RO, -IG, -Setup0, -Count, -CountB, -CountG}.
declare module Rf <: AFTER.
declare axiom C_ll (O <: Oracles {-C}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.abatch => islossless O.g =>
  islossless C(O).play.
declare axiom Rf_ll : islossless Rf.run.

local lemma IG_ll : islossless CountG(IG).a /\ islossless CountG(IG).b /\ islossless CountG(IG).h /\
                    islossless CountG(IG).abatch /\ islossless CountG(IG).g.
proof.
do! split; 1..3: by proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; wp; while true (size rest); auto => />; smt(dans_ll size_behead size_eq0 size_ge0).
by proc; inline *; auto => />; smt(dprod_ll dver_ll drest_ll).
qed.

local lemma play_ll : islossless C(CountG(IG)).play.
proof. by have [? [? [? [? ?]]]] := IG_ll; apply (C_ll (CountG(IG))). qed.

local module Flag = { var r : bool }.

local module GameF = {
  proc main() : bool = {
    var p, y, b;
    (p, y) <@ Setup0.run();
    Flag.r <- y = Setup0.x;
    IG.bad <- false;
    CountG(IG).init();
    b <@ C(CountG(IG)).play(p, IG.es, y);
    return b;
  }
}.

(* The first attempt of Γ0 alone. *)
local module T = {
  proc main() : bool = {
    var p, e, hv, y;
    R.RO.init(); RG.RO.init();
    p <$ dP;
    e <$ dent;
    hv <@ RG.RO.get(e);
    Setup0.x <- pack e hv.`1;
    y <@ Net(Ideal).enc(p, Setup0.x);
    return y = Setup0.x;
  }
}.

local lemma T_pr &m : Pr[T.main() @ &m : res] = inv (2%r ^ 256).
proof.
byphoare => //; proc.
seq 5 : (R.RO.m = empty) 1%r (inv (2%r ^ 256)) 0%r _ => //.
- by inline *; auto => />; smt(dP_ll dent_ll dprod_ll dver_ll drest_ll).
- sp; exlim p, Setup0.x => p0 x0.
  have := enc_uniform_ph p0 x0 x0; rewrite dstate1_256 => h.
  by call h; auto => />; smt(mem_empty).
by hoare; inline *; auto.
qed.

lemma refusal &m :
  Pr[GameR(C, Rf).main() @ &m : res] <= Pr[Game(Setup0, C).main() @ &m : res] + inv (2%r ^ 256).
proof.
have h1 : Pr[GameR(C, Rf).main() @ &m : res] <= Pr[GameF.main() @ &m : res \/ Flag.r].
- byequiv => //; proc.
  seq 1 1 : (={p, y, glob C, glob Setup0, IG.es, R.RO.m, RG.RO.m}); 1: by sim.
  if{1}.
  + wp; call{2} play_ll; call{1} Rf_ll; inline *; auto => />.
  by sim : (={b}) => /> /#.
have h2 : Pr[GameF.main() @ &m : Flag.r] = Pr[T.main() @ &m : res].
- byequiv => //; proc; inline Setup0.run.
  call{1} play_ll; inline CountG(IG).init CountB(IG).init Count(IG).init; wp.
  by sim.
have h3 : Pr[GameF.main() @ &m : res] = Pr[Game(Setup0, C).main() @ &m : res].
- by byequiv => //; proc; sim.
have h4 : Pr[GameF.main() @ &m : res \/ Flag.r] <=
          Pr[GameF.main() @ &m : res] + Pr[GameF.main() @ &m : Flag.r].
- rewrite Pr [mu_or].
  have : 0%r <= Pr[GameF.main() @ &m : res /\ Flag.r] by rewrite Pr[mu_ge0].
  smt().
smt(T_pr).
qed.
end section Refusal.

section UpToBad.
declare module C <: PLAY {-R.RO, -RG.RO, -IG, -Count, -CountB, -CountG}.
declare axiom C_ll (O <: Oracles {-C}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.abatch => islossless O.g =>
  islossless C(O).play.

local equiv upto : Game(Setup1, C).main ~ Game(Setup2, C).main :
  ={glob C} ==> ={IG.bad} /\ (!IG.bad{2} => ={res}).
proof.
proc; inline Setup1.run Setup2.run.
call (_ : IG.bad,
          ={R.RO.m, IG.es, IG.bad, Count.ca, Count.cb, Count.ch, CountB.dp, CountG.cg} /\
          eq_except (pred1 IG.es{1}) RG.RO.m{1} RG.RO.m{2} /\ IG.es{1} \notin RG.RO.m{2},
          ={IG.bad}).
- exact C_ll.
- by proc; inline *; auto => />.
- by move=> &2 _; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />.
- by move=> &2 _; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />.
- by move=> &2 _; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- proc; inline *; wp.
  while (={rest, ks0, R.RO.m}); 1: by auto.
  by auto.
- move=> &2 _; proc; inline *; wp.
  by while true (size rest); auto => />; smt(dans_ll size_behead size_eq0 size_ge0).
- move=> &1; proc; inline *; wp.
  by while true (size rest); auto => />; smt(dans_ll size_behead size_eq0 size_ge0).
- proc; inline *; case (e{1} = IG.es{1}).
  + rcondt{1} 3; 1: by auto.
    rcondt{2} 3; 1: by auto => /> /#.
    by auto => />.
  rcondf{1} 3; 1: by auto.
  rcondf{2} 3; 1: by auto => /> /#.
  seq 4 4 : (#pre /\ ={x, r} /\ x{1} = e{1}); 1: by auto.
  if; 1: smt(eq_exceptP).
  + by auto => />; smt(eq_except_set_eq mem_set get_setE eq_exceptP).
  by auto => />; smt(eq_exceptP).
- by move=> &2 hb; proc; inline *; auto => />; smt(dprod_ll dver_ll drest_ll).
- by move=> &1; proc; inline *; auto => />; smt(dprod_ll dver_ll drest_ll).
inline CountG(IG).init CountB(IG).init Count(IG).init RG.RO.set; wp; rnd{1}.
call (_ : ={R.RO.m}); 1: by sim.
by inline *; auto => />; smt(eq_except_setl mem_empty drest_ll).
qed.

(* Γ1 and Γ2 are identical until Bad (inequality (1) of A.3). *)
lemma upto_bad &m :
  Pr[Game(Setup1, C).main() @ &m : IG.bad] = Pr[Game(Setup2, C).main() @ &m : IG.bad] /\
  Pr[Game(Setup1, C).main() @ &m : res /\ !IG.bad] = Pr[Game(Setup2, C).main() @ &m : res /\ !IG.bad].
proof. by split; byequiv upto => // /#. qed.

end section UpToBad.

(* Inequality (1) of A.3 for every play: Pr_Γ0[win] = Pr_Γ1[win] <= Pr_Γ2[win \/ Bad]. *)
lemma ineq1 (C <: PLAY {-R.RO, -R.FRO, -RE.FunRO, -RG.RO, -IG, -Setup0, -Count, -CountB, -CountG}) &m :
  (forall (O <: Oracles {-C}), islossless O.a => islossless O.b => islossless O.h => islossless O.abatch =>
     islossless O.g => islossless C(O).play) =>
  Pr[Game(Setup0, C).main() @ &m : res] <= Pr[Game(Setup2, C).main() @ &m : res \/ IG.bad].
proof.
move=> hll.
have -> : Pr[Game(Setup0, C).main() @ &m : res] = Pr[Game(Setup1, C).main() @ &m : res] by byequiv (G1 C).
have [hb hw] := upto_bad C hll &m.
have h1 : Pr[Game(Setup1, C).main() @ &m : res] =
          Pr[Game(Setup1, C).main() @ &m : res /\ IG.bad] + Pr[Game(Setup1, C).main() @ &m : res /\ !IG.bad].
- by rewrite Pr[mu_split IG.bad].
have h2 : Pr[Game(Setup1, C).main() @ &m : res /\ IG.bad] <= Pr[Game(Setup1, C).main() @ &m : IG.bad].
- by rewrite Pr[mu_sub] => // &hr [].
have h3 : Pr[Game(Setup2, C).main() @ &m : res \/ IG.bad] =
          Pr[Game(Setup2, C).main() @ &m : (res \/ IG.bad) /\ IG.bad] +
          Pr[Game(Setup2, C).main() @ &m : (res \/ IG.bad) /\ !IG.bad].
- by rewrite Pr[mu_split IG.bad].
have h4 : Pr[Game(Setup2, C).main() @ &m : IG.bad] <= Pr[Game(Setup2, C).main() @ &m : (res \/ IG.bad) /\ IG.bad].
- by rewrite Pr[mu_sub] => // &hr /#.
have h5 : Pr[Game(Setup2, C).main() @ &m : res /\ !IG.bad] <= Pr[Game(Setup2, C).main() @ &m : (res \/ IG.bad) /\ !IG.bad].
- by rewrite Pr[mu_sub] => // &hr /#.
smt().
qed.

(* Remark G9: for every password, state and table of A and B, over a fresh H the network fixes the
   state with probability exactly 2^-256. *)
lemma G9 &m (p : pw) (x : state) :
  (forall c, c \in R.RO.m{m} => isA c \/ isB c) =>
  Pr[Net(Ideal).enc(p, x) @ &m : res = x] = inv (2%r ^ 256).
proof. by move=> hf; rewrite (enc_uniform &m p x x hf) dstate1_256. qed.

(* ---- Theorem 3 ------------------------------------------------------------------------------- *)
module type Adv (O : Oracles) = { proc guess(y : state) : pw }.

module Play (A : Adv) (O : Oracles) = {
  proc play(p : pw, e : ent, y : state) : bool = { var g; g <@ A(O).guess(y); return g = p; }
}.

(* The adversary together with its own G, as an adversary on A, B, H for the lazy game of Chain.
   [gq] is Q_G. *)
module WithG (O : ABHB) : Oracles = {
  var gq : ent list
  proc a = O.a
  proc b = O.b
  proc h = O.h
  proc abatch = O.abatch
  proc g(e : ent) = { var v; gq <- rcons gq e; CountG.cg <- CountG.cg + 1; v <@ RG.RO.get(e); return v; }
}.

module AG (A : Adv) (O : ABHB) = {
  var out : pw
  proc run(y : state) : unit = {
    var o;
    RG.RO.init(); WithG.gq <- []; CountG.cg <- 0;
    o <@ A(WithG(O)).guess(y);
    out <- o;
  }
}.

op eps3 (kA qB qH qG : int) : real =
  (qG%r + qB%r + 12%r * p1 * kA%r + 66%r) / 2%r ^ 128 + qH%r / 2%r ^ 256.

(* AG's oracles without the count of G. The adversary counted by CountG on them makes the same calls
   as on WithG, so its budgets carry over to AG. *)
module GX (O : ABHB) : Oracles = {
  proc a = O.a
  proc b = O.b
  proc h = O.h
  proc abatch = O.abatch
  proc g(e : ent) = { var v; WithG.gq <- rcons WithG.gq e; v <@ RG.RO.get(e); return v; }
}.

lemma dhash_ll : is_lossless dhash.
proof. by rewrite /dhash; apply/dprod_ll; rewrite dver_ll drest_ll. qed.

lemma rg_get_ll : islossless RG.RO.get by proc; auto; smt(dhash_ll).

(* ---- The potentials of Lemma G4 ------------------------------------------------------------- *)
(* For a chain without Early: once complete, Bad without Comp(P) needs L_0 among L, the first 128
   bits of the G queries, and a last point that the adversary did not query; before that, the
   fresh mask of the last round is still to come. *)
op psi4 (L : W128.word list) (log : (point * int) list) (st : cst) : real =
  if st.`early then 0%r
  else if st.`fin then b2r (st.`xs.`1 \in L /\ !(last witness st.`chain \in map fst log))
  else (size L)%r * e128.

(* After the run, while the budget of G holds. *)
op phi4 (qG : int) (gq : ent list) (log : (point * int) list) (st : cst) : real =
  if size gq <= qG then psi4 (map lead gq) log st else 0%r.

(* During the run: a while the budget of G holds, b after it. *)
op r4 (qG : int) (a b : real) (gq : ent list) : real = if size gq <= qG then a else b.

(* A fresh answer at the last point of the chain keeps the potential in expectation. *)
lemma Ep_psi4 L log (m : (point, ans) fmap) p st c :
  Ep dans (fun r => (psi4 L log (cstep true p st c true r [] m.[c <- r]))%xr) <= (psi4 L log st)%xr.
proof.
case: (!st.`early /\ !st.`fin /\ last witness st.`chain = c) => [[hea [hfin hl]] | hno]; last first.
- rewrite (eq_Ep _ _ (fun _ => (psi4 L log st)%xr)) => [r _ /= | ]; 2: by rewrite EpC dans_ll smul1m.
  case: (st.`early) => hea; 1: by rewrite /psi4 hea (early_mono _ _ _ _ _ _ _ _ hea).
  by rewrite /cstep (_ : !(true /\ !st.`fin /\ last witness st.`chain = c)) 1:/#.
case: (!isA c /\ !isB c /\ !(0 < st.`ri)) => [[hA [hB hri]] | hmore].
- (* the last answer: L_0 = R_1 + M_0 with a fresh mask M_0 *)
  apply (xle_trans (Ep dans (fun r => (st.`oth +^ mask_of r \in L)%xr))).
  + apply le_Ep => r _ /=; apply le_pos.
    by rewrite /cstep hfin hl /= hB hA /= hri /= /psi4 /= hea; smt().
  rewrite Ep_mu (dans_maskE (fun x => st.`oth +^ x \in L)) (dhalf_shift _ (mem L)).
  apply xle_rle; split; 1: by apply ge0_mu.
  move=> _; rewrite /psi4 hea hfin /=; apply mu_mem_le_mu1 => x.
  by rewrite dhalf1 /e128; smt().
(* another point of the chain is defined *)
apply (xle_trans (Ep dans (fun _ => (psi4 L log st)%xr))); 2: by rewrite EpC dans_ll smul1m.
apply le_Ep => r _ /=; apply le_pos.
rewrite /cstep hfin hl /= /psi4 hea hfin /= /push /=.
by case: (isB c) => hB /=; [|case: (isA c) => hA /=]; smt(e128_gt0 size_ge0).
qed.

(* After the run a query keeps the potential: only the real chain's step moves it. *)
lemma query_g4 qG :
  ehoare [Mon.query : (!Mon.inrun /\ pend = []) `|` (phi4 qG WithG.gq Mon.log (Bwd.sts Bwd.p))%xr ==>
                      (!Mon.inrun) `|` (phi4 qG WithG.gq Mon.log (Bwd.sts Bwd.p))%xr].
proof.
proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hp]; rewrite hi hp /= ?if_same.
case: (c{hr} \in R.RO.m{hr}) => hc /=.
- rewrite (eq_Ep _ _ (fun _ => (phi4 qG WithG.gq{hr} Mon.log{hr} (Bwd.sts{hr} Bwd.p{hr}))%xr)).
  + by move=> r _ /=; rewrite /cstep.
  by rewrite EpC dans_ll smul1m.
rewrite /phi4; case: (size WithG.gq{hr} <= qG) => hq /=; last by rewrite EpC dans_ll smul1m.
rewrite (eq_Ep _ _ (fun r => (psi4 (map lead WithG.gq{hr}) Mon.log{hr}
           (cstep true Bwd.p{hr} (Bwd.sts{hr} Bwd.p{hr}) c{hr} true r [] R.RO.m{hr}.[c{hr} <- r]))%xr)).
- by move=> r _ /=; rewrite get_set_sameE oget_some.
exact Ep_psi4.
qed.

lemma mon_b_g4 qG : ehoare [Mon.b :
  (!Mon.inrun) `|` (phi4 qG WithG.gq Mon.log (Bwd.sts Bwd.p))%xr ==>
  (!Mon.inrun) `|` (phi4 qG WithG.gq Mon.log (Bwd.sts Bwd.p))%xr].
proof. by proc; call (query_g4 qG); auto. qed.

lemma mon_a_g4 qG : ehoare [Mon.a :
  (!Mon.inrun) `|` (phi4 qG WithG.gq Mon.log (Bwd.sts Bwd.p))%xr ==>
  (!Mon.inrun) `|` (phi4 qG WithG.gq Mon.log (Bwd.sts Bwd.p))%xr].
proof. by proc; call (query_g4 qG); auto. qed.

lemma mon_h_g4 qG : ehoare [Mon.h :
  (!Mon.inrun) `|` (phi4 qG WithG.gq Mon.log (Bwd.sts Bwd.p))%xr ==>
  (!Mon.inrun) `|` (phi4 qG WithG.gq Mon.log (Bwd.sts Bwd.p))%xr].
proof. by proc; call (query_g4 qG); auto. qed.

lemma dec_g4 qG : ehoare [Net(Mon).dec :
  (!Mon.inrun) `|` (phi4 qG WithG.gq Mon.log (Bwd.sts Bwd.p))%xr ==>
  (!Mon.inrun) `|` (phi4 qG WithG.gq Mon.log (Bwd.sts Bwd.p))%xr].
proof.
proc; while ((!Mon.inrun) `|` (phi4 qG WithG.gq Mon.log (Bwd.sts Bwd.p))%xr).
- by move=> &hr; apply xle_cxr_r.
- conseq (_ : ((!Mon.inrun) `|` (phi4 qG WithG.gq Mon.log (Bwd.sts Bwd.p))%xr) ==> _).
  + by move=> &hr; apply xle_cxr_r.
  + by move=> &hr; apply xle_cxr_r.
  wp; call (mon_h_g4 qG); call (mon_a_g4 qG); call (mon_b_g4 qG); skip => &hr; apply xlexx.
by auto.
qed.

(* During the run a query keeps the guard and the potential. *)
lemma query_r4 qG a b : ehoare [Mon.query :
  (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG a b WithG.gq)%xr ==>
  (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG a b WithG.gq)%xr].
proof.
proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hf]; rewrite hi /=.
apply (xle_trans (Ep dans (fun _ => (r4 qG a b WithG.gq{hr})%xr))); 2: by rewrite EpC dans_ll smul1m.
apply le_Ep => r _ /=; case: (c{hr} \in R.RO.m{hr}) => hc /=; apply xle_cxr_l => //;
  exact (fin_logged_step _ _ _ _ _ _ _ _ hf).
qed.

lemma countb_a_r4 qG a b : ehoare [CountB(Mon).a :
  (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG a b WithG.gq)%xr ==>
  (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG a b WithG.gq)%xr].
proof. by proc; inline Count(Mon).a Mon.a; wp; call (query_r4 qG a b); auto. qed.

lemma count_b_r4 qG a b : ehoare [Count(Mon).b :
  (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG a b WithG.gq)%xr ==>
  (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG a b WithG.gq)%xr].
proof. by proc; inline Mon.b; wp; call (query_r4 qG a b); auto. qed.

lemma count_h_r4 qG a b : ehoare [Count(Mon).h :
  (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG a b WithG.gq)%xr ==>
  (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG a b WithG.gq)%xr].
proof. by proc; inline Mon.h; wp; call (query_r4 qG a b); auto. qed.

lemma countb_abatch_r4 qG a b : ehoare [CountB(Mon).abatch :
  (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG a b WithG.gq)%xr ==>
  (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG a b WithG.gq)%xr].
proof.
proc; inline Mon.abatch; wp.
while ((Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG a b WithG.gq)%xr).
- by move=> &hr; apply xle_cxr_r => _; apply xlexx.
- conseq (_ : ((Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG a b WithG.gq)%xr) ==> _).
  + by move=> &hr; apply xle_cxr_r.
  + by move=> &hr; apply xle_cxr_r.
  by wp; call (query_r4 qG a b); auto.
by auto.
qed.

lemma withg_g_r4 qG a b : b <= a => ehoare [WithG(CountB(Mon)).g :
  (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG a b WithG.gq)%xr ==>
  (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG a b WithG.gq)%xr].
proof.
move=> hba; proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hf]; rewrite hi hf /= ?if_same.
rewrite EpC dhash_ll smul1m /=; apply le_pos.
by rewrite /r4 size_rcons; smt().
qed.

(* At the end of the run the potential of G4 is within its bound. *)
lemma run_end4 qG gq log (st : cst) : 0 <= qG => (st.`fin => last witness st.`chain \in map fst log) =>
  phi4 qG gq log st <= r4 qG (qG%r * e128) 0%r gq.
proof.
move=> hqG hf; rewrite /phi4 /r4; case: (size gq <= qG) => hq //=.
rewrite /psi4; case: (st.`early) => _ /=; 1: smt(e128_gt0).
case: (st.`fin) => hfin /=; 1: by rewrite (hf hfin) /=; smt(e128_gt0).
by rewrite size_map; smt(e128_gt0).
qed.

(* Without Early_P, the chain is ordered: if its last point was queried, so were all of them. *)
lemma ordered_comp log (chain : point list) : chain <> [] => ordered log chain =>
  last witness chain \in map fst log => comp chain log.
proof.
move=> hne; rewrite /ordered => hord hl.
have h : forall k, 0 <= k => k < size chain => nth witness chain (size chain - 1 - k) \in map fst log.
- elim=> [_ | k ge0k ih hk]; 1: by rewrite (_ : size chain - 1 - 0 = size chain - 1) 1:/# nth_last.
  have [+ _] := hord (size chain - 1 - k) _ (ih _); 1,2: smt().
  by rewrite (_ : size chain - 1 - k - 1 = size chain - 1 - (k + 1)) 1:/#.
rewrite /comp; apply/allP => x; rewrite mem_filter => -[_ hx].
have := h (size chain - 1 - index x chain) _ _; 1,2: smt(index_ge0 index_mem).
by rewrite (_ : size chain - 1 - (size chain - 1 - index x chain) = index x chain) 1:/# (nth_index witness x chain hx).
qed.

(* At the end of the game the potential covers Bad without Comp(P) and Early_P. *)
lemma post4 qG (gq : ent list) log (st : cst) (x : state) :
  ((unpack x).`1 \in gq /\ !comp st.`chain log /\ !st.`early /\ size gq <= qG /\ st.`fin /\ x = st.`xs /\
   ordered log st.`chain /\ st.`chain <> [])%xr <= (phi4 qG gq log st)%xr.
proof.
case: ((unpack x).`1 \in gq /\ !comp st.`chain log /\ !st.`early /\ size gq <= qG /\ st.`fin /\ x = st.`xs /\
       ordered log st.`chain /\ st.`chain <> []) => [[hg [hc [hea [hq [hfin [hx [hord hne]]]]]]] | _]; last first.
- by apply rp_le; rewrite /phi4 /psi4; smt(e128_gt0 size_ge0).
rewrite /phi4 hq /psi4 hea hfin /=.
have -> : st.`xs.`1 \in map lead gq.
- by rewrite -hx -(pack_unpack x) lead_pack; apply map_f; exact hg.
have -> // : !(last witness st.`chain \in map fst log).
by apply/negP => hl; apply hc; apply ordered_comp.
qed.

(* Pr[P in C' + {p*}] and Pr[P in C'] for a run independent of P. *)
lemma mass_cands log (out : pw) k : count isA (map fst log) <= k =>
  mu dP (mem (out :: cands log)) <= top (k %/ 12 + 1).
proof.
move=> hk; have hs := cands_size log.
rewrite mu_mem; apply (ler_trans _ _ _ (mass_top _ (undup_uniq _))); apply top_mono.
have : size (cands log) <= k %/ 12 by rewrite lez_divRL //; smt().
smt(size_undup).
qed.

lemma mass_cands0 log k : count isA (map fst log) <= k => mu dP (mem (cands log)) <= top (k %/ 12).
proof.
move=> hk; have hs := cands_size log.
rewrite mu_mem; apply (ler_trans _ _ _ (mass_top _ (undup_uniq _))); apply top_mono.
have : size (cands log) <= k %/ 12 by rewrite lez_divRL //; smt().
smt(size_undup).
qed.

(* ---- Γ2 run lazily, for every adversary: no budget and no termination are needed ----------- *)
section LazyGamma2.
declare module A <: Adv {-R.RO, -R.FRO, -RE.FunRO, -RG.RO, -IG, -Setup0, -Count, -CountB, -CountG,
                         -Mon, -Bwd, -WithG, -AG}.

local module Res = { var es : ent  var won : bool }.

local module IGL (G : R.RO) : Oracles = {
  proc a = Orc(G).a
  proc b = Orc(G).b
  proc h = Orc(G).h
  proc abatch = Batch(Orc(G)).abatch
  proc g(e : ent) = { var v; WithG.gq <- rcons WithG.gq e; v <@ RG.RO.get(e); return v; }
}.

(* Γ2 with the G queries recorded; the chain of P is evaluated before the run (L0) or after it (L1). *)
local module L0 (G : R.RO) = {
  proc distinguish() : bool = {
    var p, y, xs, g;
    RG.RO.init(); WithG.gq <- [];
    p <$ dP;
    y <$ dstate;
    xs <@ Net(Orc(G)).dec(p, y);
    Res.es <- (unpack xs).`1;
    CountG(IGL(G)).init();
    g <@ A(CountG(IGL(G))).guess(y);
    Res.won <- g = p;
    return Res.won;
  }
}.

local module L1 (G : R.RO) = {
  proc distinguish() : bool = {
    var p, y, xs, g;
    RG.RO.init(); WithG.gq <- [];
    p <$ dP;
    y <$ dstate;
    CountG(IGL(G)).init();
    g <@ A(CountG(IGL(G))).guess(y);
    xs <@ Net(Orc(G)).dec(p, y);
    Res.es <- (unpack xs).`1;
    Res.won <- g = p;
    return Res.won;
  }
}.

local equiv lzA : Game(Setup2, Play(A)).main ~ R.MainD(L0, R.RO).distinguish :
  ={glob A} ==> res{1} = Res.won{2} /\ IG.bad{1} = (Res.es \in WithG.gq){2}.
proof.
proc; inline Setup2.run Play(A, CountG(IG)).play L0(R.RO).distinguish; wp.
call (_ : ={R.RO.m, RG.RO.m} /\ IG.bad{1} = (IG.es{1} \in WithG.gq{2})).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; wp; while (={rest, ks0, R.RO.m}); auto.
- by proc; inline *; auto => />; smt(mem_rcons).
seq 5 7 : (={glob A, R.RO.m, RG.RO.m, xs} /\ p0{1} = p{2} /\ y0{1} = y{2} /\ WithG.gq{2} = []).
- by call (_ : ={R.RO.m}); [sim | inline *; auto].
by inline *; auto => />; smt(mem_empty).
qed.

local equiv lzC : R.MainD(L0, RE.FunRO).distinguish ~ R.MainD(L1, RE.FunRO).distinguish :
  ={glob A} ==> ={res, Res.won, Res.es, WithG.gq}.
proof.
proc; inline L0(RE.FunRO).distinguish L1(RE.FunRO).distinguish.
swap{1} 8 2.
seq 6 6 : (={glob A, p, y, RE.FunRO.f, RG.RO.m, WithG.gq}); 1: by sim.
seq 1 0 : (#pre /\ xs{1} = invperm RE.FunRO.f{1} p{1} y{1}).
- by exlim p{1}, y{1} => p0 y0; call{1} (dec_fun_ph p0 y0); auto.
seq 2 2 : (={glob A, g, p, y, RE.FunRO.f, RG.RO.m, WithG.gq, Count.ca, Count.cb, Count.ch,
             CountB.dp, CountG.cg} /\ xs{1} = invperm RE.FunRO.f{1} p{1} y{1}).
- call (_ : ={RE.FunRO.f, RG.RO.m, WithG.gq, Count.ca, Count.cb, Count.ch, CountB.dp, CountG.cg}).
  + by proc; inline *; auto.
  + by proc; inline *; auto.
  + by proc; inline *; auto.
  + by proc; inline *; wp; while (={rest, ks0, RE.FunRO.f}); auto.
  + by proc; inline *; auto.
  by inline *; auto.
seq 0 1 : (#pre /\ xs{2} = invperm RE.FunRO.f{2} p{2} y{2}).
- by exlim p{2}, y{2} => p0 y0; call{2} (dec_fun_ph p0 y0); auto.
by auto.
qed.

local equiv lzE : R.MainD(L1, R.RO).distinguish ~ ChainGame(AG(A)).main :
  ={glob A} ==> Res.won{1} = (AG.out = Bwd.p){2} /\
                (Res.es \in WithG.gq){1} = ((unpack res).`1 \in WithG.gq){2}.
proof.
proc; inline L1(R.RO).distinguish AG(A, CountB(Mon)).run.
wp; call (_ : ={R.RO.m}).
- while (={i, p, y, R.RO.m}); 2: by auto.
  wp; call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by proc; inline *; auto.
  wp; call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by proc; inline *; auto.
  wp; call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by proc; inline *; auto.
  by auto.
wp; call (_ : ={R.RO.m, RG.RO.m, WithG.gq}).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- proc; inline *; wp.
  while (pend{2} = map PA rest{1} /\ ={ks0, R.RO.m}).
  + by auto => /> &1 &2; case: (rest{1}) => // -[q s] l _ _ rL _ /=; smt().
  by auto => />; smt().
- by proc; inline *; auto.
by inline *; auto => />.
qed.

(* Γ2 run lazily: the chain of P is evaluated after the adversary halts, and Bad is read from the
   recorded G queries. *)
lemma lazy_gamma2 : equiv [Game(Setup2, Play(A)).main ~ ChainGame(AG(A)).main : ={glob A} ==>
  res{1} = (AG.out = Bwd.p){2} /\ IG.bad{1} = ((unpack res).`1 \in WithG.gq){2}].
proof.
transitivity R.MainD(L0, R.RO).distinguish
  (={glob A} ==> res{1} = Res.won{2} /\ IG.bad{1} = (Res.es \in WithG.gq){2})
  (={glob A} ==> Res.won{1} = (AG.out = Bwd.p){2} /\
                 (Res.es \in WithG.gq){1} = ((unpack res).`1 \in WithG.gq){2}) => //.
- by move=> &1 &2 h; exists (glob A){1}.
- exact lzA.
transitivity R.MainD(L1, R.RO).distinguish
  (={glob A} ==> ={Res.won, Res.es, WithG.gq})
  (={glob A} ==> Res.won{1} = (AG.out = Bwd.p){2} /\
                 (Res.es \in WithG.gq){1} = ((unpack res).`1 \in WithG.gq){2}) => //.
- by move=> &1 &2 h; exists (glob A){1}.
- transitivity R.MainD(L0, RE.FunRO).distinguish
    (={glob L0, arg} ==> ={res, glob L0}) (={glob A} ==> ={Res.won, Res.es, WithG.gq}) => //.
  + move=> &1 &2 h.
    by exists (glob A){1} CountB.dp{1} CountG.cg{1} Res.es{1} Res.won{1} WithG.gq{1}
              Count.ca{1} Count.cb{1} Count.ch{1} RG.RO.m{1} arg{1}.
  + exact (RO_FunRO L0).
  transitivity R.MainD(L1, RE.FunRO).distinguish
    (={glob A} ==> ={Res.won, Res.es, WithG.gq}) (={glob L1, arg} ==> ={res, glob L1}) => //.
  + move=> &1 &2 h.
    by exists (glob A){2} CountB.dp{2} CountG.cg{2} Res.es{2} Res.won{2} WithG.gq{2}
              Count.ca{2} Count.cb{2} Count.ch{2} RG.RO.m{2} arg{2}.
  + by conseq lzC.
  by symmetry; conseq (RO_FunRO L1).
exact lzE.
qed.
end section LazyGamma2.

section Theorem3.

declare op kA : int.
declare op qB : int.
declare op qH : int.
declare op qG : int.

declare module A <: Adv {-R.RO, -R.FRO, -RE.FunRO, -RG.RO, -IG, -Setup0, -Count, -CountB, -CountG,
                         -Mon, -Bwd, -WithG, -AG}.

declare axiom A_bounded (O <: Oracles {-Count, -CountB, -CountG, -A}) :
  hoare [A(CountG(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ CountG.cg <= qG].

declare axiom A_ll (O <: Oracles {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.abatch => islossless O.g =>
  islossless A(O).guess.


(* ---- The budgets of AG ----------------------------------------------------------------------- *)
equiv AG_eqv (O <: ABHB {-Count, -CountB, -CountG, -A, -WithG, -RG.RO}) :
  A(WithG(CountB(O))).guess ~ A(CountG(GX(O))).guess :
  ={glob A, glob O, arg, RG.RO.m, WithG.gq, Count.ca, Count.cb, Count.ch, CountB.dp, CountG.cg} ==>
  ={Count.ca, Count.cb, Count.ch, CountB.dp, CountG.cg}.
proof.
proc (={glob O, RG.RO.m, WithG.gq, Count.ca, Count.cb, Count.ch, CountB.dp, CountG.cg}) => //.
- by proc; inline *; sim.
- by proc; inline *; sim.
- by proc; inline *; sim.
- by proc; inline *; sim.
by proc; inline *; auto.
qed.

local lemma AG_bounded (O <: ABHB {-Count, -CountB, -CountG, -A, -WithG, -RG.RO, -AG}) :
  hoare [AG(A, CountB(O)).run : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 ==>
         Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ size WithG.gq <= qG].
proof.
proc; wp.
call (_ : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 /\ size WithG.gq = CountG.cg ==>
          Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ CountG.cg <= qG /\ size WithG.gq = CountG.cg).
- conseq (_ : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 ==>
              Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ CountG.cg <= qG)
         (_ : size WithG.gq = CountG.cg ==> size WithG.gq = CountG.cg) => //.
  + proc (size WithG.gq = CountG.cg) => //.
    + by proc; inline *; wp; call (_ : true); auto.
    + by proc; inline *; wp; call (_ : true); auto.
    + by proc; inline *; wp; call (_ : true); auto.
    + by proc; inline *; wp; call (_ : true); auto.
    by proc; inline *; auto => />; smt(size_rcons).
  by conseq (AG_eqv O) (A_bounded (GX(O))) => /#.
by inline *; auto.
qed.

local lemma budget_cg : hoare [ChainGame(AG(A)).main : true ==>
  Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ size WithG.gq <= qG].
proof.
proc; inline Net(Mon).dec.
wp; while (Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ size WithG.gq <= qG); 1: by inline *; auto.
by wp; call (AG_bounded Mon); inline *; auto.
qed.

(* ---- Lemma G4 ---------------------------------------------------------------------------------- *)
local lemma facts4 : hoare [ChainGame(AG(A)).main : true ==>
  size WithG.gq <= qG /\
  (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs /\
     ordered Mon.log (Bwd.sts Bwd.p).`chain /\ (Bwd.sts Bwd.p).`chain <> [])].
proof.
conseq budget_cg (_ : true ==> !(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs /\
  ordered Mon.log (Bwd.sts Bwd.p).`chain /\ (Bwd.sts Bwd.p).`chain <> []) => //.
conseq (chain_end (AG(A))) (_ : true ==> !(Bwd.sts Bwd.p).`early =>
  ordered Mon.log (Bwd.sts Bwd.p).`chain /\ (Bwd.sts Bwd.p).`chain <> []) => //; 1: smt().
conseq (G2 (AG(A))) (G5 (AG(A))) => // &hr _ p sts log [hG2 hG5] hea.
by have [hs _] := hG5 hea; split; [exact (hG2 hea) | rewrite -size_eq0 hs].
qed.

local lemma G4_e : 0 <= qG =>
  ehoare [ChainGame(AG(A)).main : (qG%r * e128)%xr ==>
    ((unpack res).`1 \in WithG.gq /\ !comp (Bwd.sts Bwd.p).`chain Mon.log /\ !(Bwd.sts Bwd.p).`early /\
     size WithG.gq <= qG /\ (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs /\
     ordered Mon.log (Bwd.sts Bwd.p).`chain /\ (Bwd.sts Bwd.p).`chain <> [])%xr].
proof.
move=> hqG; proc.
conseq (_ : _ ==> (!Mon.inrun) `|` (phi4 qG WithG.gq Mon.log (Bwd.sts Bwd.p))%xr).
- by move=> _; apply xle_cxr_l => // *; apply xle_cxr_r => _; apply post4.
- by move=> &hr; apply xle_cxr_r => h; apply h.
call (dec_g4 qG); wp.
conseq (_ : _ ==> (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG (qG%r * e128) 0%r WithG.gq)%xr).
- move=> _; apply xle_cxr_l => // *; apply xle_cxr_r => -[_ hf] /=; apply le_pos.
  by apply run_end4 => //; move: hf; rewrite /fin_logged => hf; apply hf.
- by move=> &hr; apply xle_cxr_r => h; apply h.
inline AG(A, CountB(Mon)).run; wp.
call (: (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG (qG%r * e128) 0%r WithG.gq)%xr ==>
        (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG (qG%r * e128) 0%r WithG.gq)%xr).
- proc ((Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG (qG%r * e128) 0%r WithG.gq)%xr).
  + by move=> &hr; apply xlexx.
  + by move=> &hr; apply xlexx.
  + exact (countb_a_r4 qG (qG%r * e128) 0%r).
  + exact (count_b_r4 qG (qG%r * e128) 0%r).
  + exact (count_h_r4 qG (qG%r * e128) 0%r).
  + exact (countb_abatch_r4 qG (qG%r * e128) 0%r).
  by apply (withg_g_r4 qG (qG%r * e128) 0%r); smt(e128_gt0).
inline *; auto => &hr.
rewrite (eq_Ep _ _ (fun _ => (qG%r * e128)%xr)) => [p0 _ /= | ].
- rewrite (eq_Ep _ _ (fun _ => (qG%r * e128)%xr)) => [y1 _ /= | ].
  + have -> : fin_logged [] (fun _ => cbwd y1) = true by rewrite eqT /fin_logged /cbwd.
    by rewrite /r4 /= hqG.
  by rewrite EpC dstate_ll smul1m.
by rewrite EpC dP_ll smul1m.
qed.

(* Lemma G4. *)
lemma G4 &m : 0 <= qG =>
  Pr[ChainGame(AG(A)).main() @ &m :
     (unpack res).`1 \in WithG.gq /\ !comp (Bwd.sts Bwd.p).`chain Mon.log /\ !(Bwd.sts Bwd.p).`early] <= qG%r / 2%r ^ 128.
proof.
move=> hqG.
have h1 : Pr[ChainGame(AG(A)).main() @ &m : !(size WithG.gq <= qG /\
             (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs /\
              ordered Mon.log (Bwd.sts Bwd.p).`chain /\ (Bwd.sts Bwd.p).`chain <> []))] = 0%r.
- by byphoare => //; hoare; conseq facts4.
have h2 : Pr[ChainGame(AG(A)).main() @ &m :
             (unpack res).`1 \in WithG.gq /\ !comp (Bwd.sts Bwd.p).`chain Mon.log /\ !(Bwd.sts Bwd.p).`early /\
             size WithG.gq <= qG /\ (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs /\
             ordered Mon.log (Bwd.sts Bwd.p).`chain /\ (Bwd.sts Bwd.p).`chain <> []] <= qG%r * e128.
- byehoare (_ : (qG%r * e128)%xr ==> _) => //; 1: exact (G4_e hqG).
  smt(e128_gt0).
have h3 : Pr[ChainGame(AG(A)).main() @ &m :
             (unpack res).`1 \in WithG.gq /\ !comp (Bwd.sts Bwd.p).`chain Mon.log /\ !(Bwd.sts Bwd.p).`early] <=
          Pr[ChainGame(AG(A)).main() @ &m :
             ((unpack res).`1 \in WithG.gq /\ !comp (Bwd.sts Bwd.p).`chain Mon.log /\ !(Bwd.sts Bwd.p).`early /\
              size WithG.gq <= qG /\ (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs /\
              ordered Mon.log (Bwd.sts Bwd.p).`chain /\ (Bwd.sts Bwd.p).`chain <> []) \/
             !(size WithG.gq <= qG /\
               (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs /\
                ordered Mon.log (Bwd.sts Bwd.p).`chain /\ (Bwd.sts Bwd.p).`chain <> []))].
- by rewrite Pr[mu_sub] => // &hr /#.
move: h3; rewrite Pr[mu_or] h1; move: h2; rewrite /e128; smt(mu_bounded).
qed.

(* ---- The term top(...): P drawn after the run, the decryption dropped ------------------------- *)
local module TopG = {
  proc main() : unit = {
    var p, y;
    R.RO.init();
    CountB(Mon).init();
    y <$ dstate;
    Mon.init(y);
    AG(A, CountB(Mon)).run(y);
    Mon.inrun <- false;
    p <$ dP;
    Bwd.p <- p;
  }
}.

local equiv late_top : ChainLate(AG(A)).main ~ TopG.main : ={glob A} ==> ={Bwd.p, Mon.log, AG.out}.
proof.
proc; inline{1} Net(Mon).dec.
seq 8 8 : (={Bwd.p, Mon.log, AG.out} /\ !Mon.inrun{1}).
- by wp; rnd; wp; conseq (_ : _ ==> ={Mon.log, AG.out}) => //; sim.
wp; while{1} (!Mon.inrun{1} /\ ={Bwd.p, Mon.log, AG.out}) (i{1} + 1).
- by move=> &m z; inline *; auto => />; smt(dans_ll).
by auto => /> /#.
qed.

local lemma top_e (S : (point * int) list -> pw -> pw list) (n : real) :
  (forall log out, count isA (map fst log) <= kA => mu dP (mem (S log out)) <= n) => 0%r <= n =>
  ehoare [TopG.main : n%xr ==> (Bwd.p \in S Mon.log AG.out /\ count isA (map fst Mon.log) <= kA)%xr].
proof.
move=> hS hn; proc.
seq 5 : ((Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG n n WithG.gq)%xr).
- inline AG(A, CountB(Mon)).run; wp.
  call (: (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG n n WithG.gq)%xr ==>
          (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG n n WithG.gq)%xr).
  + proc ((Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (r4 qG n n WithG.gq)%xr).
    * by move=> &hr; apply xlexx.
    * by move=> &hr; apply xlexx.
    * exact (countb_a_r4 qG n n).
    * exact (count_b_r4 qG n n).
    * exact (count_h_r4 qG n n).
    * exact (countb_abatch_r4 qG n n).
    by apply (withg_g_r4 qG n n).
  inline *; auto => &hr.
  rewrite (eq_Ep _ _ (fun _ => n%xr)) => [y1 _ /= | ].
  + have -> : fin_logged [] (fun _ => cbwd y1) = true by rewrite eqT /fin_logged /cbwd.
    by rewrite /r4 if_same.
  by rewrite EpC dstate_ll smul1m.
auto => &hr; apply xle_cxr_r => _; rewrite Ep_mu /r4 if_same.
apply xle_rle; split; 1: by apply ge0_mu.
move=> _; case: (count isA (map fst Mon.log{hr}) <= kA) => hc.
- by apply (ler_trans _ _ _ _ (hS _ AG.out{hr} hc)); apply mu_le => p _ /=.
by rewrite mu0_false.
qed.

lemma top_ge0 (k : int) : 0%r <= top k.
proof. by rewrite /top; apply StdBigop.Bigreal.sumr_ge0 => i _; apply pr_ge0. qed.

lemma top_pr &m (S : (point * int) list -> pw -> pw list) (n : real) :
  (forall log out, count isA (map fst log) <= kA => mu dP (mem (S log out)) <= n) => 0%r <= n =>
  Pr[ChainGame(AG(A)).main() @ &m : Bwd.p \in S Mon.log AG.out] <= n.
proof.
move=> hS hn.
have h0 : Pr[ChainGame(AG(A)).main() @ &m : !(count isA (map fst Mon.log) <= kA)] = 0%r.
- by byphoare => //; hoare; conseq (log_count (AG(A))) budget_cg => /#.
have h1 : Pr[ChainGame(AG(A)).main() @ &m : Bwd.p \in S Mon.log AG.out /\ count isA (map fst Mon.log) <= kA] =
          Pr[TopG.main() @ &m : Bwd.p \in S Mon.log AG.out /\ count isA (map fst Mon.log) <= kA].
- have -> : Pr[ChainGame(AG(A)).main() @ &m : Bwd.p \in S Mon.log AG.out /\ count isA (map fst Mon.log) <= kA] =
            Pr[ChainLate(AG(A)).main() @ &m : Bwd.p \in S Mon.log AG.out /\ count isA (map fst Mon.log) <= kA].
  + by byequiv (chain_late (AG(A))).
  by byequiv late_top.
have h2 : Pr[TopG.main() @ &m : Bwd.p \in S Mon.log AG.out /\ count isA (map fst Mon.log) <= kA] <= n.
- by byehoare (_ : n%xr ==> _) => //; exact (top_e S n hS hn).
have h3 : Pr[ChainGame(AG(A)).main() @ &m : Bwd.p \in S Mon.log AG.out] <=
          Pr[ChainGame(AG(A)).main() @ &m : (Bwd.p \in S Mon.log AG.out /\ count isA (map fst Mon.log) <= kA) \/
                                            !(count isA (map fst Mon.log) <= kA)].
- by rewrite Pr[mu_sub] => // &hr /#.
move: h3; rewrite Pr[mu_or] h0 h1; smt(mu_bounded).
qed.

(* ---- Theorem 3 ---------------------------------------------------------------------------------- *)
(* In Γ2 run lazily, an outcome of win or Bad lies in {P in S}, in Early_P, or in Bad without
   Comp(P), for a set S that contains p* on win and, almost surely, P on Comp(P) without Early_P. *)
lemma split2 &m (S : (point * int) list -> pw -> pw list) (E : pw -> pw -> bool) :
  (forall log out p, E out p => p \in S log out) =>
  Pr[ChainGame(AG(A)).main() @ &m : !(Bwd.sts Bwd.p).`early /\ comp (Bwd.sts Bwd.p).`chain Mon.log /\
     !(Bwd.p \in S Mon.log AG.out)] = 0%r =>
  Pr[ChainGame(AG(A)).main() @ &m : E AG.out Bwd.p \/ (unpack res).`1 \in WithG.gq] <=
  Pr[ChainGame(AG(A)).main() @ &m : Bwd.p \in S Mon.log AG.out] +
  Pr[ChainGame(AG(A)).main() @ &m : (Bwd.sts Bwd.p).`early] +
  Pr[ChainGame(AG(A)).main() @ &m :
     (unpack res).`1 \in WithG.gq /\ !comp (Bwd.sts Bwd.p).`chain Mon.log /\ !(Bwd.sts Bwd.p).`early].
proof.
move=> hE hD.
have h : Pr[ChainGame(AG(A)).main() @ &m : E AG.out Bwd.p \/ (unpack res).`1 \in WithG.gq] <=
         Pr[ChainGame(AG(A)).main() @ &m : (Bwd.p \in S Mon.log AG.out \/ (Bwd.sts Bwd.p).`early) \/
            (((unpack res).`1 \in WithG.gq /\ !comp (Bwd.sts Bwd.p).`chain Mon.log /\ !(Bwd.sts Bwd.p).`early) \/
             (!(Bwd.sts Bwd.p).`early /\ comp (Bwd.sts Bwd.p).`chain Mon.log /\ !(Bwd.p \in S Mon.log AG.out)))].
- by rewrite Pr[mu_sub] => // &hr; smt().
by move: h; do ! rewrite Pr[mu_or]; rewrite hD; smt(mu_bounded).
qed.

(* On Comp(P) without Early_P, P is in C' (Lemma G5). *)
local lemma comp_cands &m (S : (point * int) list -> pw -> pw list) :
  (forall log out p, p \in cands log => p \in S log out) =>
  Pr[ChainGame(AG(A)).main() @ &m : !(Bwd.sts Bwd.p).`early /\ comp (Bwd.sts Bwd.p).`chain Mon.log /\
     !(Bwd.p \in S Mon.log AG.out)] = 0%r.
proof.
move=> hC; byphoare => //; hoare; conseq (G5 (AG(A))) => &hr _ p sts log out hG5.
apply/negP => -[hea [hc hS]]; apply hS; apply hC; rewrite /cands mem_filter PwT.enumP /=.
by have [_ [_ hcnt]] := hG5 hea; apply hcnt.
qed.

lemma G3_AG &m : 0 <= kA => 0 <= qB => 0 <= qH =>
  Pr[ChainGame(AG(A)).main() @ &m : (Bwd.sts Bwd.p).`early] <=
    (12%r * p1 * kA%r + 66%r + qB%r) / 2%r ^ 128 + qH%r / 2%r ^ 256.
proof. by apply (G3 kA qB qH (AG(A)) _ &m) => O; conseq (AG_bounded O). qed.

lemma gamma2 &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= qG =>
  Pr[Game(Setup2, Play(A)).main() @ &m : res \/ IG.bad] <= top (kA %/ 12 + 1) + eps3 kA qB qH qG.
proof.
move=> hkA hqB hqH hqG.
have -> : Pr[Game(Setup2, Play(A)).main() @ &m : res \/ IG.bad] =
          Pr[ChainGame(AG(A)).main() @ &m : AG.out = Bwd.p \/ (unpack res).`1 \in WithG.gq].
- by byequiv (lazy_gamma2 A) => // /#.
have /= h := split2 &m (fun log out => out :: cands log) (fun out p => out = p) _ _; 1: smt().
- by apply comp_cands => /#.
have /= hT := top_pr &m (fun log out => out :: cands log) (top (kA %/ 12 + 1)) _ (top_ge0 _).
- by move=> log out hc; apply mass_cands.
have hE := G3_AG &m hkA hqB hqH.
have hB := G4 &m hqG.
rewrite /eps3; smt().
qed.

lemma gamma2_bad &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= qG =>
  Pr[Game(Setup2, Play(A)).main() @ &m : IG.bad] <= top (kA %/ 12) + eps3 kA qB qH qG.
proof.
move=> hkA hqB hqH hqG.
have -> : Pr[Game(Setup2, Play(A)).main() @ &m : IG.bad] =
          Pr[ChainGame(AG(A)).main() @ &m : false \/ (unpack res).`1 \in WithG.gq].
- by byequiv (lazy_gamma2 A) => // /#.
have /= h := split2 &m (fun log _ => cands log) (fun _ _ => false) _ _; 1: smt().
- by apply comp_cands.
have /= hT := top_pr &m (fun log _ => cands log) (top (kA %/ 12)) _ (top_ge0 _).
- by move=> log out hc; apply mass_cands0.
have hE := G3_AG &m hkA hqB hqH.
have hB := G4 &m hqG.
rewrite /eps3; smt().
qed.

(* Theorem 3. *)
lemma theorem3 &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= qG =>
  Pr[Game(Setup0, Play(A)).main() @ &m : res] <= top (kA %/ 12 + 1) + eps3 kA qB qH qG.
proof.
move=> hkA hqB hqH hqG.
have := ineq1 (Play(A)) &m _; 2: by have := gamma2 &m hkA hqB hqH hqG; smt().
by move=> O ha hb hh hab hg; proc; call (A_ll O ha hb hh hab hg).
qed.

end section Theorem3.

(* ---- Corollary G6: source recovery ----------------------------------------------------------- *)
module type Adv6 (O : Oracles) = { proc guess(y : state) : ent }.

module Play6 (A : Adv6) (O : Oracles) = {
  proc play(p : pw, e : ent, y : state) : bool = { var e'; e' <@ A(O).guess(y); return e' = e; }
}.

(* The adversary of G6 with its output submitted to G as one more query; it guesses nothing. *)
module A6G (A : Adv6) (O : Oracles) = {
  proc guess(y : state) : pw = { var e, v; e <@ A(O).guess(y); v <@ O.g(e); return witness; }
}.

section G6.
declare op kA : int.
declare op qB : int.
declare op qH : int.
declare op qG : int.
declare module A <: Adv6 {-R.RO, -R.FRO, -RE.FunRO, -RG.RO, -IG, -Setup0, -Count, -CountB, -CountG,
                          -Mon, -Bwd, -WithG, -AG}.
declare axiom A_bounded (O <: Oracles {-Count, -CountB, -CountG, -A}) :
  hoare [A(CountG(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ CountG.cg <= qG].
declare axiom A_ll (O <: Oracles {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.abatch => islossless O.g =>
  islossless A(O).guess.

local lemma A6G_bounded (O <: Oracles {-Count, -CountB, -CountG, -A}) :
  hoare [A6G(A, CountG(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ CountG.cg <= qG + 1].
proof. by proc; inline CountG(O).g; wp; call (_ : true); wp; call (A_bounded O); auto => /#. qed.

local lemma A6G_ll (O <: Oracles {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.abatch => islossless O.g =>
  islossless A6G(A, O).guess.
proof. by move=> ha hb hh hab hg; proc; call hg; call (A_ll O ha hb hh hab hg). qed.

(* In Γ2, recovering e* or Bad is Bad for the adversary that submits its output to G. *)
local equiv g6_bad : Game(Setup2, Play6(A)).main ~ Game(Setup2, Play(A6G(A))).main :
  ={glob A} ==> (res \/ IG.bad){1} = IG.bad{2}.
proof.
proc; inline Play6(A, CountG(IG)).play Play(A6G(A), CountG(IG)).play A6G(A, CountG(IG)).guess.
inline{2} CountG(IG).g IG.g; wp.
call{2} rg_get_ll; wp.
call (_ : ={glob IG, R.RO.m, RG.RO.m, Count.ca, Count.cb, Count.ch, CountB.dp, CountG.cg}); 1..5: by sim.
by wp; conseq (_ : _ ==> ={glob A, IG.es, IG.bad, R.RO.m, RG.RO.m, Count.ca, Count.cb, Count.ch, CountB.dp,
  CountG.cg, y}) => //; sim.
qed.

(* Corollary G6. The output counts as one more G query. *)
lemma G6 &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= qG =>
  Pr[Game(Setup0, Play6(A)).main() @ &m : res] <= top (kA %/ 12) + eps3 kA qB qH (qG + 1).
proof.
move=> hkA hqB hqH hqG.
have := ineq1 (Play6(A)) &m _.
- by move=> O ha hb hh hab hg; proc; call (A_ll O ha hb hh hab hg).
have -> : Pr[Game(Setup2, Play6(A)).main() @ &m : res \/ IG.bad] = Pr[Game(Setup2, Play(A6G(A))).main() @ &m : IG.bad].
- by byequiv g6_bad.
have := gamma2_bad kA qB qH (qG + 1) (A6G(A)) A6G_bounded A6G_ll &m hkA hqB hqH _; 1: smt().
smt().
qed.
end section G6.

(* ---- Corollary G7: depth --------------------------------------------------------------------- *)
(* The Argon2id queries come in at most eleven batches; CountB.dp counts them. *)
section G7.
declare op kA : int.
declare op qB : int.
declare op qH : int.
declare op qG : int.
declare module A <: Adv {-R.RO, -R.FRO, -RE.FunRO, -RG.RO, -IG, -Setup0, -Count, -CountB, -CountG,
                         -Mon, -Bwd, -WithG, -AG}.
declare axiom A_bounded (O <: Oracles {-Count, -CountB, -CountG, -A}) :
  hoare [A(CountG(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 /\ CountB.dp = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ CountG.cg <= qG /\ CountB.dp <= 11].
declare axiom A_ll (O <: Oracles {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.abatch => islossless O.g =>
  islossless A(O).guess.

(* The budgets of Theorem 3: the adversary does not read the count of batches. *)
local equiv eq_dp (O <: Oracles {-Count, -CountB, -CountG, -A}) :
  A(CountG(O)).guess ~ A(CountG(O)).guess :
  ={glob A, glob O, arg, Count.ca, Count.cb, Count.ch, CountG.cg} ==> ={Count.ca, Count.cb, Count.ch, CountG.cg}.
proof. by proc (={glob O, Count.ca, Count.cb, Count.ch, CountG.cg}) => //; proc; inline *; sim. qed.

local lemma A_bounded3 (O <: Oracles {-Count, -CountB, -CountG, -A}) :
  hoare [A(CountG(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ CountG.cg <= qG].
proof. by conseq (eq_dp O) (A_bounded O) => /#. qed.

local lemma AG_batches : hoare [ChainGame(AG(A)).main : true ==> CountB.dp <= 11].
proof.
proc; inline Net(Mon).dec.
wp; while (CountB.dp <= 11); 1: by inline *; auto.
inline AG(A, CountB(Mon)).run; wp.
call (_ : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 /\ CountB.dp = 0 ==> CountB.dp <= 11).
- by conseq (AG_eqv kA qB qH qG A A_bounded3 A_ll Mon) (A_bounded (GX(Mon))) => /#.
by inline *; auto.
qed.

(* Corollary G7. *)
lemma G7 &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= qG =>
  Pr[Game(Setup0, Play(A)).main() @ &m : res] <= p1 + eps3 kA qB qH qG.
proof.
move=> hkA hqB hqH hqG.
have := ineq1 (Play(A)) &m _.
- by move=> O ha hb hh hab hg; proc; call (A_ll O ha hb hh hab hg).
have -> : Pr[Game(Setup2, Play(A)).main() @ &m : res \/ IG.bad] =
          Pr[ChainGame(AG(A)).main() @ &m : AG.out = Bwd.p \/ (unpack res).`1 \in WithG.gq].
- by byequiv (lazy_gamma2 A) => // /#.
have hD : Pr[ChainGame(AG(A)).main() @ &m : !(Bwd.sts Bwd.p).`early /\ comp (Bwd.sts Bwd.p).`chain Mon.log /\
             !(Bwd.p \in [AG.out])] = 0%r.
- by byphoare => //; hoare; conseq (comp_depth (AG(A))) AG_batches => /#.
have /= h := split2 kA qB qH qG A A_bounded3 A_ll &m (fun _ out => [out]) (fun out p => out = p) _ hD; 1: smt().
have /= hT := top_pr kA qB qH qG A A_bounded3 A_ll &m (fun _ out => [out]) p1 _ p1_ge0.
- by move=> log out _; rewrite (mu_eq _ _ (pred1 out)) 1:/#; apply mu1_p1.
have hE := G3_AG kA qB qH qG A A_bounded3 A_ll &m hkA hqB hqH.
have hB := G4 kA qB qH qG A A_bounded3 A_ll &m hqG.
rewrite /eps3; smt().
qed.
end section G7.

(* ---- Proposition G8: the matching attack ----------------------------------------------------- *)
(* Inverts Y under each of the first m candidates, tests Trunc_r G(e(w)) = v(w) with one G query,
   outputs the first password that passes and otherwise the last candidate. The first B point
   (11, L_12) is queried once and shared. *)
module Match (O : Oracles) = {
  var cands : pw list
  proc guess(y : state) : pw = {
    var s11, j, w, i, z, s, k, m, v, found, out;
    s11 <@ O.b(rd 11, y.`1);
    found <- false;
    out <- nth witness cands (size cands - 1);
    j <- 0;
    while (j < size cands - 1 /\ !found) {
      w <- nth witness cands j;
      z <- y;
      i <- 11;
      while (0 <= i) {
        if (i = 11) { s <- s11; } else { s <@ O.b(rd i, z.`1); }
        k <@ O.a(w, s);
        m <@ O.h(k, rd i, z.`1);
        z <- unround m z;
        i <- i - 1;
      }
      v <@ O.g((unpack z).`1);
      if (v.`1 = (unpack z).`2) { found <- true; out <- w; }
      j <- j + 1;
    }
    return out;
  }
}.

op delta8 : real = inv (2%r ^ r) + inv (2%r ^ 128) + 12%r / 2%r ^ 256.

(* The proof of G8: Γ0 and Γ1 agree (G1); A, B, H become a whole function drawn first (D8); then a
   potential over the tests: each untested candidate before P passes with chance phi8g, 2^-r while its
   G point is unqueried and the test's outcome once it is queried. At the start the candidates whose
   inversion meets e* are bounded by the pair lemma. *)
module IGF8 (G : R.RO) : Oracles = {
  proc a = Orc(G).a
  proc b = Orc(G).b
  proc h = Orc(G).h
  proc abatch = Batch(Orc(G)).abatch
  proc g = IG.g
}.

module D8 (G : R.RO) = {
  proc distinguish() : bool = {
    var p, y, xs, rs, b;
    RG.RO.init();
    p <$ dP;
    y <$ dstate;
    xs <@ Net(Orc(G)).dec(p, y);
    rs <$ drest;
    RG.RO.set((unpack xs).`1, ((unpack xs).`2, rs));
    IG.es <- (unpack xs).`1;
    IG.bad <- false;
    CountG(IGF8(G)).init();
    b <@ Play(Match, CountG(IGF8(G))).play(p, IG.es, y);
    return b;
  }
}.

op phi8g (gm : (ent, hash) fmap) (z : state) : real =
  if (unpack z).`1 \in gm then b2r ((oget gm.[(unpack z).`1]).`1 = (unpack z).`2) else inv (2%r ^ r).

op S8 (f : point -> ans) (y : state) (ws : pw list) (p : pw) (j : int) (gm : (ent, hash) fmap) : real =
  bigi predT (fun i => phi8g gm (invperm f (nth witness ws i) y)) j (index p ws).

op Phi8 (f : point -> ans) (y : state) (ws : pw list) (gm : (ent, hash) fmap) (found : bool) (out : pw)
        (j : int) (p : pw) : real =
  if found then b2r (out <> p) else if p \in ws /\ j <= index p ws then S8 f y ws p j gm else 1%r.

(* At the start each candidate before P passes with chance 2^-r, or surely if its inversion is e*. *)
op Phi8b (f : point -> ans) (y : state) (ws : pw list) (p : pw) : real =
  if p \in ws then bigi predT (fun i => inv (2%r ^ r) + b2r (invperm f (nth witness ws i) y = invperm f p y)) 0 (index p ws)
  else 1%r.

op phi8 (ws : pw list) (p : pw) : real = if p \in ws then (index p ws)%r * delta8 else 1%r.

lemma phi8g_ge0 gm z : 0%r <= phi8g gm z.
proof. by rewrite /phi8g; case: ((unpack z).`1 \in gm) => _; [apply b2r_ge0 | smt(expr_gt0 invr_gt0)]. qed.

lemma Ep_phi8g (gm : (ent, hash) fmap) (x : ent) (z : state) : x \notin gm =>
  Ep dhash (fun v => (phi8g gm.[x <- v] z)%xr) = (phi8g gm z)%xr.
proof.
move=> hx; rewrite /phi8g; case: ((unpack z).`1 = x) => hz.
- rewrite hz hx /= (eq_Ep _ _ (fun (v : hash) => (v.`1 = (unpack z).`2)%xr)) => [v _ /= | ].
  + by rewrite mem_set get_set_sameE.
  rewrite Ep_mu (mu_eq _ _ (fun (v : hash) => pred1 (unpack z).`2 v.`1)) => [v | ]; 1: by rewrite /pred1.
  by rewrite /dhash (dprodEl dver drest (pred1 (unpack z).`2)) drest_ll dver1.
rewrite (eq_Ep _ _ (fun _ => (if (unpack z).`1 \in gm then b2r ((oget gm.[(unpack z).`1]).`1 = (unpack z).`2)
                               else inv (2%r ^ r))%xr)) => [v _ /= | ].
- by rewrite mem_set hz /= get_set_neqE.
by rewrite EpC dhash_ll smul1m.
qed.

lemma S8_ge0 f y ws p j gm : 0%r <= S8 f y ws p j gm.
proof. by rewrite /S8; apply Bigreal.sumr_ge0 => i _; apply phi8g_ge0. qed.

lemma Ep_S8 f y ws p j (gm : (ent, hash) fmap) (x : ent) : x \notin gm =>
  Ep dhash (fun v => (S8 f y ws p j gm.[x <- v])%xr) = (S8 f y ws p j gm)%xr.
proof.
move=> hx; rewrite /S8 Ep_sum => [i v | ]; 1: by apply phi8g_ge0.
rewrite (BXA.eq_bigr _ _ (fun i => (phi8g gm (invperm f (nth witness ws i) y))%xr)) => [i _ /= | ].
- by apply Ep_phi8g.
by rewrite bigXR // => i _; apply phi8g_ge0.
qed.

lemma phi8g_init (xs z : state) rs :
  phi8g empty.[(unpack xs).`1 <- ((unpack xs).`2, rs)] z <= inv (2%r ^ r) + b2r (z = xs).
proof.
have h0 : 0%r < inv (2%r ^ r) by smt(expr_gt0 invr_gt0).
rewrite /phi8g mem_set mem_empty /=; case: ((unpack z).`1 = (unpack xs).`1) => h /=; 2: smt(b2r_ge0).
rewrite h get_set_sameE /=; case: ((unpack xs).`2 = (unpack z).`2) => h2 /=; 2: smt(b2r_ge0).
have -> : z = xs by rewrite -(pack_unpack z) -(pack_unpack xs) h h2.
by rewrite /=; smt().
qed.

lemma core8_e (ws : pw list) (M : int) : uniq ws => size ws = M + 1 => 0 <= M =>
  ehoare [R.MainD(D8, RE.FunRO).distinguish :
    (Match.cands = ws) `|` (Ep dP (fun p => (phi8 ws p)%xr)) ==> (!res)%xr].
proof.
move=> hu hs hM; proc.
inline D8(RE.FunRO).distinguish Play(Match, CountG(IGF8(RE.FunRO))).play Match(CountG(IGF8(RE.FunRO))).guess.
wp.
while ((Match.cands = ws /\ xs = invperm RE.FunRO.f p y1 /\ p0 = p /\
        RG.RO.m.[(unpack xs).`1] = Some ((unpack xs).`2, rs) /\ s11 = salt_of (RE.FunRO.f (PB (rd 11, y1.`1))) /\
        0 <= j /\ (!found => out = nth witness ws M)) `|`
       (Phi8 RE.FunRO.f y1 ws RG.RO.m found out j p)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hc8 hx hp hG hs11 hj hout.
  rewrite hp; apply xr_ble; rewrite /Phi8; move: hc hout; case: (found{hr}) => /= [// | hnf hc hout].
  case: (p{hr} \in ws /\ j{hr} <= index p{hr} ws) => hc2 /=; 2: by smt().
  have hk : index p{hr} ws = M by move: hc; rewrite hc8 hs; smt(index_mem).
  rewrite hout -hk nth_index 1:/# /=.
  by apply Bigreal.sumr_ge0 => i _ /=; apply phi8g_ge0.
- seq 4 : ((Match.cands = ws /\ xs = invperm RE.FunRO.f p y1 /\ p0 = p /\
            RG.RO.m.[(unpack xs).`1] = Some ((unpack xs).`2, rs) /\ s11 = salt_of (RE.FunRO.f (PB (rd 11, y1.`1))) /\
            0 <= j < M /\ !found /\ out = nth witness ws M /\ w = nth witness ws j /\
            z = invperm RE.FunRO.f w y1) `|`
           (Phi8 RE.FunRO.f y1 ws RG.RO.m found out j p)%xr).
  + while ((Match.cands = ws /\ xs = invperm RE.FunRO.f p y1 /\ p0 = p /\
            RG.RO.m.[(unpack xs).`1] = Some ((unpack xs).`2, rs) /\ s11 = salt_of (RE.FunRO.f (PB (rd 11, y1.`1))) /\
            0 <= j < M /\ !found /\ out = nth witness ws M /\ w = nth witness ws j /\ -1 <= i <= 11 /\
            z = foldl (fun (u : state) k => unround (mask RE.FunRO.f w (rd k) u.`1) u) y1
                      (rev (iota_ (i + 1) (11 - i)))) `|`
           (Phi8 RE.FunRO.f y1 ws RG.RO.m found out j p)%xr).
    * move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hc8 hx hp hG hs11 hj0 hj1 hnf hout hw hi0 hi1 hz /=.
      apply xle_cxr_l; 2: by [].
      have hzx : z{hr} = invperm RE.FunRO.f{hr} w{hr} y1{hr} by rewrite hz (_ : i{hr} = -1) 1:/# /invperm.
      by rewrite hzx /=; smt().
    * inline *; auto => &hr /=; apply xle_cxr_r => -[hc [#] hc8 hx hp hG hs11 hj0 hj1 hnf hout hw hi0 hi1 hz].
      have hstep : forall s0, s0 = salt_of (RE.FunRO.f{hr} (PB (rd i{hr}, z{hr}.`1))) =>
        unround (mask_of (RE.FunRO.f{hr} (PH (key_of (RE.FunRO.f{hr} (PA (w{hr}, s0))), rd i{hr}, z{hr}.`1)))) z{hr} =
        foldl (fun (u : state) k => unround (mask RE.FunRO.f{hr} w{hr} (rd k) u.`1) u) y1{hr}
              (rev (iota_ i{hr} (11 - (i{hr} - 1)))).
      - move=> s0 ->; rewrite (_ : 11 - (i{hr} - 1) = (11 - i{hr}) + 1) 1:/# iotaS 1:/# rev_cons foldl_rcons -hz.
        by rewrite /mask.
      case: (i{hr} = 11) => hi11 /=.
      - apply xle_cxr_l; 2: by [].
        have hz1 : z{hr} = y1{hr} by rewrite hz hi11 /= iota0.
        have h := hstep s11{hr} _; 1: by rewrite hs11 hz1 hi11.
        by rewrite h; smt().
      apply xle_cxr_l; 2: by [].
      have h := hstep (salt_of (RE.FunRO.f{hr} (PB (rd i{hr}, z{hr}.`1)))) _ => //.
      by rewrite h; smt().
    auto => &hr /=; apply xle_cxr_r => -[[hc hnf] [#] hc8 hx hp hG hs11 hj hout].
    by apply xle_cxr_l => //; rewrite iota0 //=; smt().
  inline *; auto => &hr /=; apply xle_cxr_r => -[#] hc8 hx hp hG hs11 hj0 hj1 hnf hout hw hz.
  have hG' : forall r, (unpack z{hr}).`1 \notin RG.RO.m{hr} =>
             RG.RO.m{hr}.[(unpack z{hr}).`1 <- r].[(unpack xs{hr}).`1] = Some ((unpack xs{hr}).`2, rs{hr}).
  - by move=> r hn; rewrite get_set_neqE //; apply/negP => h; move: hn; rewrite -h domE hG.
  have hf : found{hr} = false by smt().
  case: (p{hr} \in ws /\ j{hr} < index p{hr} ws) => hc2.
  - have [hpin hjk] := hc2.
    have hwp : w{hr} <> p{hr} by rewrite hw; apply (before_index witness); smt().
    have hsplit : forall (gm : (ent, hash) fmap), S8 RE.FunRO.f{hr} y1{hr} ws p{hr} j{hr} gm =
                  phi8g gm z{hr} + S8 RE.FunRO.f{hr} y1{hr} ws p{hr} (j{hr} + 1) gm.
    + by move=> gm; rewrite /S8 big_ltn 1:/# /= hz hw.
    have hpt : forall (gm : (ent, hash) fmap), (unpack z{hr}).`1 \in gm =>
      (if (oget gm.[(unpack z{hr}).`1]).`1 = (unpack z{hr}).`2
       then Phi8 RE.FunRO.f{hr} y1{hr} ws gm true w{hr} (j{hr} + 1) p{hr}
       else Phi8 RE.FunRO.f{hr} y1{hr} ws gm found{hr} out{hr} (j{hr} + 1) p{hr})
      <= S8 RE.FunRO.f{hr} y1{hr} ws p{hr} j{hr} gm.
    + move=> gm hin; rewrite hsplit /phi8g hin /=; have := S8_ge0 RE.FunRO.f{hr} y1{hr} ws p{hr} (j{hr} + 1) gm.
      case: ((oget gm.[(unpack z{hr}).`1]).`1 = (unpack z{hr}).`2) => hv /=.
      * by rewrite /Phi8 /= hwp /=; smt().
      by rewrite /Phi8 hf /= hpin (_ : j{hr} + 1 <= index p{hr} ws) 1:/# /=; smt().
    have -> : Phi8 RE.FunRO.f{hr} y1{hr} ws RG.RO.m{hr} found{hr} out{hr} j{hr} p{hr} =
              S8 RE.FunRO.f{hr} y1{hr} ws p{hr} j{hr} RG.RO.m{hr}.
    + by rewrite /Phi8 hf /= hpin (_ : j{hr} <= index p{hr} ws) 1:/#.
    case: ((unpack z{hr}).`1 \in RG.RO.m{hr}) => hxin /=.
    + rewrite EpC dhash_ll smul1m; have := hpt _ hxin.
      case: ((oget RG.RO.m{hr}.[(unpack z{hr}).`1]).`1 = (unpack z{hr}).`2) => hv /= h.
      * by apply xle_cxr_l; [smt() | apply xr_le].
      by apply xle_cxr_l; [smt() | apply xr_le].
    apply (xle_trans (Ep dhash (fun r => (S8 RE.FunRO.f{hr} y1{hr} ws p{hr} j{hr} RG.RO.m{hr}.[(unpack z{hr}).`1 <- r])%xr))).
    + apply le_Ep => r _ /=; have := hpt RG.RO.m{hr}.[(unpack z{hr}).`1 <- r] _; 1: by rewrite mem_set.
      case: ((oget RG.RO.m{hr}.[(unpack z{hr}).`1 <- r].[(unpack z{hr}).`1]).`1 = (unpack z{hr}).`2) => hv /= h.
      * by apply xle_cxr_l; [rewrite hG' //; smt() | apply xr_le].
      by apply xle_cxr_l; [rewrite hG' //; smt() | apply xr_le].
    by rewrite Ep_S8.
  case: (p{hr} \in ws /\ j{hr} = index p{hr} ws) => hc3.
  - have [hpin hjk] := hc3.
    have hwp : w{hr} = p{hr} by rewrite hw hjk nth_index.
    have hzx : z{hr} = xs{hr} by rewrite hz hwp hx.
    have hxin : (unpack z{hr}).`1 \in RG.RO.m{hr} by rewrite hzx domE hG.
    rewrite hxin /= hzx hG /= EpC dhash_ll smul1m.
    apply xle_cxr_l; 1: smt().
    rewrite /Phi8 /= hwp /= hf /= hpin hjk /= /S8 big_geq //.
  have -> : Phi8 RE.FunRO.f{hr} y1{hr} ws RG.RO.m{hr} found{hr} out{hr} j{hr} p{hr} = 1%r.
  - by rewrite /Phi8 hf /=; smt().
  have hle : forall (gm : (ent, hash) fmap) fd o, Phi8 RE.FunRO.f{hr} y1{hr} ws gm fd o (j{hr} + 1) p{hr} <= 1%r.
  - by move=> gm fd o; rewrite /Phi8; case: fd => _ /=; [smt() | smt()].
  apply (xle_trans (Ep dhash (fun _ => 1%xr))); 2: by rewrite EpC dhash_ll smul1m.
  apply le_Ep => r _ /=; case: ((unpack z{hr}).`1 \in RG.RO.m{hr}) => hxin /=.
  + case: ((oget RG.RO.m{hr}.[(unpack z{hr}).`1]).`1 = (unpack z{hr}).`2) => hv /=.
    * by apply xle_cxr_l; [smt() | apply xr_le; apply hle].
    by apply xle_cxr_l; [smt() | apply xr_le; apply hle].
  case: ((oget RG.RO.m{hr}.[(unpack z{hr}).`1 <- r].[(unpack z{hr}).`1]).`1 = (unpack z{hr}).`2) => hv /=.
  + by apply xle_cxr_l; [rewrite hG' //; smt() | apply xr_le; apply hle].
  by apply xle_cxr_l; [rewrite hG' //; smt() | apply xr_le; apply hle].
inline *; wp.
conseq (_ : _ ==> (y2 = invperm RE.FunRO.f p y /\ RG.RO.m = empty /\ Match.cands = ws) `|` (Phi8b RE.FunRO.f y ws p)%xr).
- move=> &hr; apply xle_cxr_l => // m1 f p3 y4 y2_0; apply xle_cxr_r => -[#] hy h1 h2 /=.
  apply (xle_trans (Ep drest (fun _ => (Phi8b f y4 ws p3)%xr))); 2: by rewrite EpC drest_ll smul1m.
  apply le_Ep => rs0 _ /=; apply xle_cxr_l; 1: by rewrite h1 h2 hy get_set_sameE /= hs.
  apply xr_le; rewrite /Phi8 /Phi8b /=; case: (p3 \in ws) => hin //=.
  rewrite index_ge0 /= /S8; apply Bigreal.ler_sum => i _ /=; rewrite h1 -hy; apply phi8g_init.
- move=> &hr; apply xle_cxr_r => h.
  exact (h RG.RO.m{hr} RE.FunRO.f{hr} p{hr} y{hr} y2{hr}).
while ((p1 = p /\ -1 <= i0 <= 11 /\ RG.RO.m = empty /\ Match.cands = ws /\
        y2 = foldl (fun (u : state) k => unround (mask RE.FunRO.f p (rd k) u.`1) u) y
                   (rev (iota_ (i0 + 1) (11 - i0)))) `|` (Phi8b RE.FunRO.f y ws p)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hp hi0 hi1 hG hc8 hy.
  by apply xle_cxr_l => //; rewrite hG hc8 hy /= (_ : i0{hr} = -1) 1:/# /invperm.
- auto => &hr /=; apply xle_cxr_r => -[hc [#] hp hi0 hi1 hG hc8 hy].
  apply xle_cxr_l => //; rewrite hp hG hc8 /=; split; 1: smt().
  rewrite (_ : 11 - (i0{hr} - 1) = (11 - i0{hr}) + 1) 1:/# iotaS 1:/# rev_cons foldl_rcons -hy /=.
  by rewrite /mask.
wp; skip => &hr /=; apply xle_cxr_r => hc8.
have hll : is_lossless (RE.MUniFinFun.dfun (fun (_ : point) => dans)).
- by apply RE.MUniFinFun.dfun_ll => z /=; apply dans_ll.
apply (xle_trans (Ep (RE.MUniFinFun.dfun (fun (_ : point) => dans))
         (fun f => Ep dP (fun pv => Ep dstate (fun yv => (Phi8b f yv ws pv)%xr))))).
- apply le_Ep => f _ /=; apply le_Ep => pv _ /=; apply le_Ep => yv _ /=.
  by apply xle_cxr_l; [rewrite hc8 iota0 | done].
rewrite Ep_swap; apply le_Ep => pv _ /=; rewrite Ep_swap.
apply (xle_trans (Ep dstate (fun _ => (phi8 ws pv)%xr))); 2: by rewrite EpC dstate_ll smul1m.
apply le_Ep => yv _ /=; case: (pv \in ws) => hin; last first.
- by rewrite /Phi8b /phi8 hin /= EpC hll smul1m.
have hr0 : 0%r < inv (2%r ^ r) by smt(expr_gt0 invr_gt0).
rewrite /Phi8b hin /= Ep_sum => [i f | ]; 1: smt(b2r_ge0).
rewrite (BXA.eq_bigr _ _ (fun i => (inv (2%r ^ r) + mu (RE.MUniFinFun.dfun (fun (_ : point) => dans))
            (fun f => invperm f (nth witness ws i) yv = invperm f pv yv))%xr)) => [i _ /= | ].
- by rewrite (Ep_cb _ _ _ hll) //; smt().
rewrite bigXR => [i _ | ]; 1: smt(ge0_mu).
apply xr_le; rewrite /phi8 hin /=.
apply (ler_trans (bigi predT (fun _ => delta8) 0 (index pv ws))).
- apply Bigreal.ler_sum_seq => i /mem_range hi _ /=; rewrite /delta8.
  have hne : pv <> nth witness ws i.
  + by apply/negP => h; have := before_index witness pv ws i _; [smt() | rewrite -h].
  have h1 := pair_coll &hr pv (nth witness ws i) yv hne.
  have h2 := mu_le (RE.MUniFinFun.dfun (fun (_ : point) => dans))
               (fun f => invperm f (nth witness ws i) yv = invperm f pv yv)
               (fun f => (invperm f (nth witness ws i) yv).`1 = (invperm f pv yv).`1) _; 1: smt().
  by move: h1; rewrite /e128 /e256; smt().
by rewrite sumri_const; [smt(index_ge0) | rewrite RField.intmulr; smt()].
qed.

lemma core8 &m (ws : pw list) (M : int) : Match.cands{m} = ws => uniq ws => size ws = M + 1 =>
  bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * delta8)) 0 (M + 1)
    <= Pr[R.MainD(D8, RE.FunRO).distinguish() @ &m : res].
proof.
move=> hc hu hs; case: (M < 0) => hM; 1: by rewrite big_geq 1:/#; smt(mu_bounded).
have hd : 0%r <= delta8 by rewrite /delta8; smt(expr_gt0 invr_gt0).
have hS := sum_cands ws (fun p => (index p ws)%r * delta8) hu.
have hR : bigi predT (fun j => mu1 dP (nth witness ws j) *
            (1%r - (fun p => (index p ws)%r * delta8) (nth witness ws j))) 0 (size ws) =
          bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * delta8)) 0 (M + 1).
- by rewrite hs; apply eq_big_int => j hj /=; rewrite index_uniq // /#.
move: hS; rewrite hR => hS.
have hge : 0%r <= 1%r - bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * delta8)) 0 (M + 1).
- rewrite -hS; apply Bigreal.sumr_ge0 => p _ /=.
  by case: (p \in ws) => _; smt(ge0_mu index_ge0 mulr_ge0).
have hE : Ep dP (fun p => (phi8 ws p)%xr) =
          (1%r - bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * delta8)) 0 (M + 1))%xr.
- rewrite (eq_Ep _ _ (fun p => ((if p \in ws then (index p ws)%r * delta8 else 1%r))%xr)) => [p _ /= | ].
  + by rewrite /phi8.
  by rewrite Ep_dP => [p | ]; [case: (p \in ws) => _ //; smt(index_ge0) | rewrite hS].
have hll : islossless R.MainD(D8, RE.FunRO).distinguish.
- have hdf : is_lossless (RE.MUniFinFun.dfun (fun (_ : point) => dans)).
  + by apply RE.MUniFinFun.dfun_ll => z /=; apply dans_ll.
  proc; inline *; wp; while true (size Match.cands - 1 - j).
  + move=> z0; wp; rnd; wp; while true (i2 + 1); 1: by move=> z1; auto => /#.
    auto => /> &hr hj hnf i20; split; 1: smt().
    by move=> _; rewrite (mu_eq _ _ predT) 1:/#; apply dhash_ll.
  wp; rnd; wp; while true (i + 1); 1: by move=> z1; auto => /#.
  by auto => />; smt(dP_ll dstate_ll drest_ll).
have h1 : Pr[R.MainD(D8, RE.FunRO).distinguish() @ &m : !res] <=
          1%r - bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * delta8)) 0 (M + 1).
- byehoare (_ : (Match.cands = ws) `|` (Ep dP (fun p => (phi8 ws p)%xr)) ==> (!res)%xr) => //.
  + by apply (core8_e ws M hu hs); smt().
  by rewrite hc /= hE.
have h2 : Pr[R.MainD(D8, RE.FunRO).distinguish() @ &m : true] = 1%r by byphoare => //; apply hll.
have h3 : Pr[R.MainD(D8, RE.FunRO).distinguish() @ &m : !res] =
          Pr[R.MainD(D8, RE.FunRO).distinguish() @ &m : true] - Pr[R.MainD(D8, RE.FunRO).distinguish() @ &m : res].
- by rewrite Pr[mu_not].
smt().
qed.

(* With w_1 ... w_(m+1) the candidates in order. *)
lemma G8 &m (ws : pw list) (m : int) : Match.cands{m} = ws => uniq ws => size ws = m + 1 =>
  bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * delta8)) 0 (m + 1)
    <= Pr[Game(Setup0, Play(Match)).main() @ &m : res].
proof.
move=> hc hu hs.
have -> : Pr[Game(Setup0, Play(Match)).main() @ &m : res] = Pr[Game(Setup1, Play(Match)).main() @ &m : res].
- by byequiv (G1 (Play(Match))).
have -> : Pr[Game(Setup1, Play(Match)).main() @ &m : res] = Pr[R.MainD(D8, R.RO).distinguish() @ &m : res].
- by byequiv => //; proc; inline *; sim.
have -> : Pr[R.MainD(D8, R.RO).distinguish() @ &m : res] = Pr[R.MainD(D8, RE.FunRO).distinguish() @ &m : res].
- by byequiv (RO_FunRO D8).
exact (core8 &m ws m hc hu hs).
qed.

lemma G8_top &m (m : int) : 0 <= m => m + 1 <= PwT.card => Match.cands{m} = take (m + 1) ranked =>
  top (m + 1) * (1%r - m%r * delta8) <= Pr[Game(Setup0, Play(Match)).main() @ &m : res].
proof.
move=> hm hcard hc; have [hu [hs ht]] := ranked_top m delta8 hm hcard _.
- by rewrite /delta8; smt(expr_gt0 invr_gt0).
exact (StdOrder.RealOrder.ler_trans _ _ _ ht (G8 &m (take (m + 1) ranked) m hc hu hs)).
qed.

lemma G8_budget (O <: Oracles {-Count, -CountB, -CountG, -Match}) (m : int) : 0 <= m =>
  hoare [Match(CountG(O)).guess :
    size Match.cands = m + 1 /\ Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 ==>
    Count.ca <= 12 * m /\ Count.cb <= 11 * m + 1 /\ Count.ch <= 12 * m /\ CountG.cg <= m].
proof.
move=> hm; proc.
while (0 <= j <= m /\ size Match.cands = m + 1 /\ Count.ca = 12 * j /\ Count.cb = 1 + 11 * j /\
       Count.ch = 12 * j /\ CountG.cg = j).
- inline CountG(O).g; wp; call (_ : true); wp.
  while (-1 <= i <= 11 /\ 0 <= j < m /\ size Match.cands = m + 1 /\ Count.ca = 12 * j + (11 - i) /\
         Count.cb = 1 + 11 * j + max 0 (10 - i) /\ Count.ch = 12 * j + (11 - i) /\ CountG.cg = j).
  + inline *; wp; call (_ : true); wp; call (_ : true); wp.
    if; 1: by auto => /> /#.
    by wp; call (_ : true); auto => /> /#.
  by auto => /> /#.
by inline *; wp; call (_ : true); auto => /> /#.
qed.

(* The attack halts whenever its oracles do. *)
lemma match_ll (O <: Oracles {-Match}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.g => islossless Match(O).guess.
proof.
move=> ha hb hh hg; proc.
while true (size Match.cands - 1 - j).
- move=> z; wp; call hg; while true (i + 1).
  + by move=> z'; wp; call hh; call ha; if; [auto | call hb; auto]; auto => /#.
  by auto => /#.
by wp; call hb; auto => /#.
qed.

(* ---- G8 and Theorem 3 bracket the best adversary ---------------------------------------------- *)
section Bracket8.
declare op ws0 : pw list.

(* The attack with its candidate list fixed: an adversary of Theorem 3. *)
local module M8 (O : Oracles) = {
  proc guess(y : state) : pw = { var o; Match.cands <- ws0; o <@ Match(O).guess(y); return o; }
}.

lemma G8_upper &m (m : int) : 0 <= m => size ws0 = m + 1 => Match.cands{m} = ws0 =>
  Pr[Game(Setup0, Play(Match)).main() @ &m : res] <=
    top (m + 1) + eps3 (12 * m) (11 * m + 1) (12 * m) m.
proof.
move=> hm hs hc.
have -> : Pr[Game(Setup0, Play(Match)).main() @ &m : res] = Pr[Game(Setup0, Play(M8)).main() @ &m : res].
- byequiv (_ : ={glob Match} /\ Match.cands{1} = ws0 ==> ={res}) => //.
  proc; inline Play(M8, CountG(IG)).play M8(CountG(IG)).guess Play(Match, CountG(IG)).play; wp.
  call (_ : ={arg, glob Match, glob CountG(IG)} ==> ={res}); 1: by sim.
  inline CountG(IG).init CountB(IG).init Count(IG).init; wp.
  by call (_ : true ==> ={res, R.RO.m, RG.RO.m, IG.es}); [sim | auto].
have := theorem3 (12 * m) (11 * m + 1) (12 * m) m M8 _ _ &m _ _ _ _; 3..6: smt().
- by move=> O; proc; call (G8_budget O m hm); auto => /> /#.
- by move=> O ha hb hh hab hg; proc; call (match_ll O ha hb hh hg); auto.
by rewrite (_ : 12 * m %/ 12 = m) 1:/#.
qed.
end section Bracket8.

(* With the m + 1 likeliest passwords the attack succeeds with a probability between the lower bound
   of G8 and the bound of Theorem 3 at k_A = 12m, so the success of the best adversary with the
   attack's budget lies between the two. *)
lemma G8_bracket &m (m : int) : 0 <= m => m + 1 <= PwT.card => Match.cands{m} = take (m + 1) ranked =>
  top (m + 1) * (1%r - m%r * delta8) <= Pr[Game(Setup0, Play(Match)).main() @ &m : res] /\
  Pr[Game(Setup0, Play(Match)).main() @ &m : res] <= top (m + 1) + eps3 (12 * m) (11 * m + 1) (12 * m) m.
proof.
move=> hm hcard hc; split; 1: exact (G8_top &m m hm hcard hc).
apply (G8_upper (take (m + 1) ranked) &m m hm _ hc).
by rewrite size_take 1:/# /ranked size_sort /PwT.card; smt().
qed.

(* ---- Corollary G10: wallet data --------------------------------------------------------------- *)
(* Omega idealizes the data of the wallet of the original phrase with the empty or a known BIP39
   passphrase: an ideal uniform output of lambda bits, not a serialized record. *)
type data.
op lambda : int.
op ddata : data distr.
axiom ddata_ll : is_lossless ddata.
axiom ddata1 (d : data) : mu1 ddata d = inv (2%r ^ lambda).

clone import PROM.FullRO as RW with
  type in_t <- ent, type out_t <- data, op dout <- (fun _ => ddata).

lemma rw_get_ll : islossless RW.RO.get by proc; auto; smt(ddata_ll).

module type OraclesW = {
  include Oracles
  proc w(e : ent) : data
}.
module type AdvW (O : OraclesW) = { proc guess(y : state, d : data) : pw }.

module WithW (O : Oracles) : OraclesW = {
  var cw : int
  proc a = O.a
  proc b = O.b
  proc h = O.h
  proc abatch = O.abatch
  proc g = O.g
  proc w(e : ent) = { var d; cw <- cw + 1; d <@ RW.RO.get(e); return d; }
}.

(* The adversary also receives omega* = Omega(E) and may query Omega. *)
module PlayW (A : AdvW) (O : Oracles) = {
  proc play(p : pw, e : ent, y : state) : bool = {
    var d, g;
    RW.RO.init();
    WithW.cw <- 0;
    d <@ RW.RO.get(e);
    g <@ A(WithW(O)).guess(y, d);
    return g = p;
  }
}.

(* Counts every call, for any implementation of the oracles. *)
module CountW (O : OraclesW) = {
  proc a = CountG(O).a
  proc b = CountG(O).b
  proc h = CountG(O).h
  proc abatch = CountG(O).abatch
  proc g = CountG(O).g
  proc w(e : ent) = { var d; WithW.cw <- WithW.cw + 1; d <@ O.w(e); return d; }
}.

(* The proof of G10: Omega with Bad_W, a query at e*; Omega answered after a G query at the same
   point; the same without counting that query. *)
module WithWB (O : Oracles) : OraclesW = {
  var badw : bool
  proc a = O.a
  proc b = O.b
  proc h = O.h
  proc abatch = O.abatch
  proc g = O.g
  proc w(e : ent) = { var d; WithW.cw <- WithW.cw + 1; if (e = IG.es) badw <- true; d <@ RW.RO.get(e); return d; }
}.

module WithWX (O : Oracles) : OraclesW = {
  proc a = O.a
  proc b = O.b
  proc h = O.h
  proc abatch = O.abatch
  proc g = O.g
  proc w(e : ent) = { var v, d; WithW.cw <- WithW.cw + 1; v <@ O.g(e); d <@ RW.RO.get(e); return d; }
}.

module WXB (O : Oracles) : OraclesW = {
  proc a = O.a
  proc b = O.b
  proc h = O.h
  proc abatch = O.abatch
  proc g = O.g
  proc w(e : ent) = { var v, d; v <@ O.g(e); d <@ RW.RO.get(e); return d; }
}.

(* The adversary of G10 as one of Theorem 3: it draws omega* itself and submits every Omega query to
   G as well. *)
module AWX (A : AdvW) (O : Oracles) = {
  proc guess(y : state) : pw = {
    var d, g;
    RW.RO.init(); WithW.cw <- 0;
    d <$ ddata;
    g <@ A(WithWX(O)).guess(y, d);
    return g;
  }
}.

section G10.
declare op kA : int.
declare op qB : int.
declare op qH : int.
declare op qG : int.
declare op qW : int.
declare module A <: AdvW {-R.RO, -R.FRO, -RE.FunRO, -RG.RO, -RG.FRO, -RW.RO, -IG, -Setup0, -Count, -CountB,
                          -CountG, -WithW, -WithWB, -Mon, -Bwd, -WithG, -AG}.
declare axiom A_bounded (O <: OraclesW {-Count, -CountB, -CountG, -WithW.cw, -A}) :
  hoare [A(CountW(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 /\ WithW.cw = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ CountG.cg <= qG /\ WithW.cw <= qW].
declare axiom A_ll (O <: OraclesW {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.abatch => islossless O.g =>
  islossless O.w => islossless A(O).guess.

(* The budgets of AWX: every Omega query is one more G query. *)
local equiv eqWX (O <: Oracles {-Count, -CountB, -CountG, -WithW, -A, -RW.RO}) :
  A(WithWX(CountG(O))).guess ~ A(CountW(WXB(O))).guess :
  ={glob A, glob O, arg, RW.RO.m, Count.ca, Count.cb, Count.ch, CountB.dp, WithW.cw} /\
  CountG.cg{1} = CountG.cg{2} + WithW.cw{2} ==>
  ={Count.ca, Count.cb, Count.ch, WithW.cw} /\ CountG.cg{1} = CountG.cg{2} + WithW.cw{2}.
proof.
proc (={glob O, RW.RO.m, Count.ca, Count.cb, Count.ch, CountB.dp, WithW.cw} /\
      CountG.cg{1} = CountG.cg{2} + WithW.cw{2}) => //;
  1..4: by proc; inline *; wp; call (_ : true); auto => />.
- by proc; inline *; wp; call (_ : true); auto => /#.
by proc; inline *; auto; call (_ : true); auto => /#.
qed.

local lemma AWX_bounded (O <: Oracles {-Count, -CountB, -CountG, -WithW, -A, -RW.RO}) :
  hoare [AWX(A, CountG(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ CountG.cg <= qG + qW].
proof.
proc; call (_ : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 /\ WithW.cw = 0 ==>
                Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ CountG.cg <= qG + qW).
- by conseq (eqWX O) (A_bounded (WXB(O))) => /#.
by inline *; auto.
qed.

local lemma AWX_ll (O <: Oracles {-AWX(A)}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.abatch => islossless O.g =>
  islossless AWX(A, O).guess.
proof.
move=> ha hb hh hab hg; proc; call (A_ll (WithWX(O)) ha hb hh hab hg _).
- by proc; call rw_get_ll; call hg; auto.
by rnd; inline *; auto => />; exact ddata_ll.
qed.

(* PlayW with the flag Bad_W, and with omega* drawn on its own and Omega not programmed at e*. *)
local module PlayW1 (O : Oracles) = {
  proc play(p : pw, e : ent, y : state) : bool = {
    var d, g;
    RW.RO.init(); WithW.cw <- 0; WithWB.badw <- false;
    d <@ RW.RO.get(e);
    g <@ A(WithWB(O)).guess(y, d);
    return g = p;
  }
}.

local module PlayW2 (O : Oracles) = {
  proc play(p : pw, e : ent, y : state) : bool = {
    var d, g;
    RW.RO.init(); WithW.cw <- 0; WithWB.badw <- false;
    d <$ ddata;
    g <@ A(WithWB(O)).guess(y, d);
    return g = p;
  }
}.

local equiv w_flag : Game(Setup2, PlayW(A)).main ~ Game(Setup2, PlayW1).main : ={glob A} ==> ={res, IG.bad}.
proof.
proc; inline PlayW(A, CountG(IG)).play PlayW1(CountG(IG)).play; wp.
call (_ : ={R.RO.m, RG.RO.m, RW.RO.m, IG.es, IG.bad, WithW.cw, Count.ca, Count.cb, Count.ch, CountB.dp, CountG.cg}).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; wp; while (={rest, ks0, R.RO.m}); auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
by inline RW.RO.get; wp; rnd; wp; conseq (_ : _ ==> ={p0, y0, e, glob A, R.RO.m, RG.RO.m, RW.RO.m, IG.es, IG.bad,
  Count.ca, Count.cb, Count.ch, CountB.dp, CountG.cg}) => />; sim.
qed.

(* Γ2 with and without the programmed Omega are identical until Bad_W. *)
local equiv upto_w : Game(Setup2, PlayW1).main ~ Game(Setup2, PlayW2).main :
  ={glob A} ==> ={WithWB.badw} /\ (!WithWB.badw{2} => ={res, IG.bad}).
proof.
proc; inline PlayW1(CountG(IG)).play PlayW2(CountG(IG)).play; wp.
call (_ : WithWB.badw,
          ={R.RO.m, RG.RO.m, IG.es, IG.bad, WithWB.badw, WithW.cw, Count.ca, Count.cb, Count.ch, CountB.dp, CountG.cg} /\
          eq_except (pred1 IG.es{1}) RW.RO.m{1} RW.RO.m{2} /\ IG.es{1} \notin RW.RO.m{2},
          ={WithWB.badw}).
- exact A_ll.
- by proc; inline *; auto => />.
- by move=> &2 hb; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />.
- by move=> &2 hb; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />.
- by move=> &2 hb; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- proc; inline *; wp.
  while (={rest, ks0, R.RO.m}); 1: by auto.
  by auto.
- move=> &2 hb; proc; inline *; wp.
  by while true (size rest); auto => />; smt(dans_ll size_behead size_eq0 size_ge0).
- move=> &1; proc; inline *; wp.
  by while true (size rest); auto => />; smt(dans_ll size_behead size_eq0 size_ge0).
- by proc; inline *; auto => />.
- by move=> &2 hb; proc; inline *; auto => />; smt(dprod_ll dver_ll drest_ll).
- by move=> &1; proc; inline *; auto => />; smt(dprod_ll dver_ll drest_ll).
- proc; inline *; case (e{1} = IG.es{1}).
  + rcondt{1} 2; 1: by auto.
    rcondt{2} 2; 1: by auto => /> /#.
    by auto => />; smt(ddata_ll).
  rcondf{1} 2; 1: by auto.
  rcondf{2} 2; 1: by auto => /> /#.
  seq 3 3 : (#pre /\ ={x, r} /\ x{1} = e{1}); 1: by auto.
  if; 1: smt(eq_exceptP).
  + by auto => />; smt(eq_except_set_eq mem_set get_setE eq_exceptP).
  by auto => />; smt(eq_exceptP).
- by move=> &2 hb; proc; inline *; auto => />; smt(ddata_ll).
- by move=> &1; proc; inline *; auto => />; smt(ddata_ll).
inline CountG(IG).init CountB(IG).init Count(IG).init RW.RO.init RW.RO.get; wp; rnd; wp.
call (_ : true ==> ={res, R.RO.m, RG.RO.m, IG.es}); 1: by sim.
by auto => />; smt(eq_except_setl mem_empty get_set_sameE).
qed.

(* The G queries in Γ2 through an oracle module, and Omega after a sample of G at the same point:
   with the lazy oracle the sample does nothing, with the eager one it is the extra G query. *)
module IGR (G : RG.RO) : Oracles = {
  proc a = Ideal.a
  proc b = Ideal.b
  proc h = Ideal.h
  proc abatch = Batch(Ideal).abatch
  proc g(e : ent) = { var v; if (e = IG.es) IG.bad <- true; v <@ G.get(e); return v; }
}.

local module WithWR (G : RG.RO) (O : Oracles) : OraclesW = {
  proc a = O.a
  proc b = O.b
  proc h = O.h
  proc abatch = O.abatch
  proc g = O.g
  proc w(e : ent) = {
    var d;
    WithW.cw <- WithW.cw + 1; if (e = IG.es) IG.bad <- true; G.sample(e); d <@ RW.RO.get(e); return d;
  }
}.

local module DW (G : RG.RO) = {
  proc distinguish() : bool = {
    var p, y, xs, d, g;
    R.RO.init();
    p <$ dP;
    y <$ dstate;
    xs <@ Net(Ideal).dec(p, y);
    IG.es <- (unpack xs).`1;
    IG.bad <- false;
    CountG(IGR(G)).init();
    RW.RO.init(); WithW.cw <- 0;
    d <$ ddata;
    g <@ A(WithWR(G, CountG(IGR(G)))).guess(y, d);
    return g = p \/ IG.bad;
  }
}.

local equiv dw_lro : Game(Setup2, PlayW2).main ~ RG.MainD(DW, RG.LRO).distinguish :
  ={glob A} ==> (res \/ IG.bad \/ WithWB.badw){1} = res{2}.
proof.
proc; inline Setup2.run PlayW2(CountG(IG)).play DW(RG.LRO).distinguish; wp.
call (_ : ={R.RO.m, RG.RO.m, RW.RO.m, IG.es, WithW.cw, Count.ca, Count.cb, Count.ch, CountB.dp, CountG.cg} /\
          IG.bad{2} = (IG.bad \/ WithWB.badw){1}).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; wp; while (={rest, ks0, R.RO.m}); auto.
- by proc; inline *; auto => /> /#.
- by proc; inline *; auto => /> /#.
inline CountG(IG).init CountB(IG).init Count(IG).init RW.RO.init.
inline CountG(IGR(RG.LRO)).init CountB(IGR(RG.LRO)).init Count(IGR(RG.LRO)).init; wp; rnd; wp.
call (_ : ={R.RO.m}); 1: by sim.
by inline *; auto.
qed.

local equiv dw_ro : RG.MainD(DW, RG.RO).distinguish ~ Game(Setup2, Play(AWX(A))).main :
  ={glob A} ==> res{1} = (res \/ IG.bad){2}.
proof.
proc; inline Setup2.run Play(AWX(A), CountG(IG)).play AWX(A, CountG(IG)).guess DW(RG.RO).distinguish; wp.
call (_ : ={R.RO.m, RG.RO.m, RW.RO.m, IG.es, IG.bad, WithW.cw, Count.ca, Count.cb, Count.ch, CountB.dp}).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; wp; while (={rest, ks0, R.RO.m}); auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
inline CountG(IG).init CountB(IG).init Count(IG).init RW.RO.init.
inline CountG(IGR(RG.RO)).init CountB(IGR(RG.RO)).init Count(IGR(RG.RO)).init; wp; rnd; wp.
call (_ : ={R.RO.m}); 1: by sim.
by inline *; auto.
qed.

(* Corollary G10. Omega queries count with the G queries. *)
lemma G10 &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= qG => 0 <= qW =>
  Pr[Game(Setup0, PlayW(A)).main() @ &m : res] <= top (kA %/ 12 + 1) + eps3 kA qB qH (qG + qW).
proof.
move=> hkA hqB hqH hqG hqW.
have := ineq1 (PlayW(A)) &m _.
- move=> O ha hb hh hab hg; proc; call (A_ll (WithW(O)) ha hb hh hab hg _).
  + by proc; call rw_get_ll; auto.
  by call rw_get_ll; inline *; auto.
have -> : Pr[Game(Setup2, PlayW(A)).main() @ &m : res \/ IG.bad] =
          Pr[Game(Setup2, PlayW1).main() @ &m : res \/ IG.bad] by byequiv w_flag.
have h2 : Pr[Game(Setup2, PlayW1).main() @ &m : res \/ IG.bad] <=
          Pr[Game(Setup2, PlayW2).main() @ &m : res \/ IG.bad \/ WithWB.badw] by byequiv upto_w => // /#.
have h3 : Pr[Game(Setup2, PlayW2).main() @ &m : res \/ IG.bad \/ WithWB.badw] =
          Pr[Game(Setup2, Play(AWX(A))).main() @ &m : res \/ IG.bad].
- have -> : Pr[Game(Setup2, PlayW2).main() @ &m : res \/ IG.bad \/ WithWB.badw] =
            Pr[RG.MainD(DW, RG.LRO).distinguish() @ &m : res] by byequiv dw_lro.
  have <- : Pr[RG.MainD(DW, RG.RO).distinguish() @ &m : res] =
            Pr[RG.MainD(DW, RG.LRO).distinguish() @ &m : res].
  + have hll : forall (x : ent), is_lossless dhash by move=> _; exact dhash_ll.
    by byequiv (RG.FullEager.RO_LRO DW hll).
  by byequiv dw_ro.
have := gamma2 kA qB qH (qG + qW) (AWX(A)) AWX_bounded AWX_ll &m hkA hqB hqH _; 1: smt().
smt().
qed.
end section G10.

(* The checksum-aware form: the data is D(phrase(e, G(e))) for a random function D on phrases; the
   phrase determines e. *)
type phrase.
op phr : ent -> hash -> phrase.
op ent_of : phrase -> ent.
axiom ent_of_phr (e : ent) (v : hash) : ent_of (phr e v) = e.
(* The phrases of the entropy e, named so that the provers see one symbol, not a fresh lambda. *)
op ofent (e : ent) (f : phrase) = ent_of f = e.

clone import PROM.FullRO as RD with
  type in_t <- phrase, type out_t <- data, op dout <- (fun _ => ddata).

lemma rd_get_ll : islossless RD.RO.get by proc; auto; smt(ddata_ll).

module type OraclesD = {
  include Oracles
  proc dq(f : phrase) : data
}.
module type AdvD (O : OraclesD) = { proc guess(y : state, d : data) : pw }.

module WithD (O : Oracles) : OraclesD = {
  var cd : int
  proc a = O.a
  proc b = O.b
  proc h = O.h
  proc abatch = O.abatch
  proc g = O.g
  proc dq(f : phrase) = { var d; cd <- cd + 1; d <@ RD.RO.get(f); return d; }
}.

module PlayD (A : AdvD) (O : Oracles) = {
  proc play(p : pw, e : ent, y : state) : bool = {
    var hv, d, g;
    RD.RO.init();
    WithD.cd <- 0;
    hv <@ RG.RO.get(e);
    d <@ RD.RO.get(phr e hv);
    g <@ A(WithD(O)).guess(y, d);
    return g = p;
  }
}.

(* Counts every call, for any implementation of the oracles. *)
module CountD (O : OraclesD) = {
  proc a = CountG(O).a
  proc b = CountG(O).b
  proc h = CountG(O).h
  proc abatch = CountG(O).abatch
  proc g = CountG(O).g
  proc dq(f : phrase) = { var d; WithD.cd <- WithD.cd + 1; d <@ O.dq(f); return d; }
}.

(* The proof of G10_derived: D with Bad_D, a query at a phrase of e*; D answered after a G query at
   the entropy of the phrase; the same without counting that query. *)
module WithDB (O : Oracles) : OraclesD = {
  var badd : bool
  proc a = O.a
  proc b = O.b
  proc h = O.h
  proc abatch = O.abatch
  proc g = O.g
  proc dq(f : phrase) = {
    var d;
    WithD.cd <- WithD.cd + 1; if (ent_of f = IG.es) badd <- true; d <@ RD.RO.get(f); return d;
  }
}.

module WithDX (O : Oracles) : OraclesD = {
  proc a = O.a
  proc b = O.b
  proc h = O.h
  proc abatch = O.abatch
  proc g = O.g
  proc dq(f : phrase) = { var v, d; WithD.cd <- WithD.cd + 1; v <@ O.g(ent_of f); d <@ RD.RO.get(f); return d; }
}.

module DXB (O : Oracles) : OraclesD = {
  proc a = O.a
  proc b = O.b
  proc h = O.h
  proc abatch = O.abatch
  proc g = O.g
  proc dq(f : phrase) = { var v, d; v <@ O.g(ent_of f); d <@ RD.RO.get(f); return d; }
}.

module ADX (A : AdvD) (O : Oracles) = {
  proc guess(y : state) : pw = {
    var d, g;
    RD.RO.init(); WithD.cd <- 0;
    d <$ ddata;
    g <@ A(WithDX(O)).guess(y, d);
    return g;
  }
}.

section G10D.
declare op kA : int.
declare op qB : int.
declare op qH : int.
declare op qG : int.
declare op qD : int.
declare module A <: AdvD {-R.RO, -R.FRO, -RE.FunRO, -RG.RO, -RG.FRO, -RD.RO, -IG, -Setup0, -Count, -CountB,
                          -CountG, -WithD, -WithDB, -Mon, -Bwd, -WithG, -AG}.
declare axiom A_bounded (O <: OraclesD {-Count, -CountB, -CountG, -WithD.cd, -A}) :
  hoare [A(CountD(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 /\ WithD.cd = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ CountG.cg <= qG /\ WithD.cd <= qD].
declare axiom A_ll (O <: OraclesD {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.abatch => islossless O.g =>
  islossless O.dq => islossless A(O).guess.

local equiv eqDX (O <: Oracles {-Count, -CountB, -CountG, -WithD, -A, -RD.RO}) :
  A(WithDX(CountG(O))).guess ~ A(CountD(DXB(O))).guess :
  ={glob A, glob O, arg, RD.RO.m, Count.ca, Count.cb, Count.ch, CountB.dp, WithD.cd} /\
  CountG.cg{1} = CountG.cg{2} + WithD.cd{2} ==>
  ={Count.ca, Count.cb, Count.ch, WithD.cd} /\ CountG.cg{1} = CountG.cg{2} + WithD.cd{2}.
proof.
proc (={glob O, RD.RO.m, Count.ca, Count.cb, Count.ch, CountB.dp, WithD.cd} /\
      CountG.cg{1} = CountG.cg{2} + WithD.cd{2}) => //;
  1..4: by proc; inline *; wp; call (_ : true); auto => />.
- by proc; inline *; wp; call (_ : true); auto => /#.
by proc; inline *; auto; call (_ : true); auto => /#.
qed.

local lemma ADX_bounded (O <: Oracles {-Count, -CountB, -CountG, -WithD, -A, -RD.RO}) :
  hoare [ADX(A, CountG(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ CountG.cg <= qG + qD].
proof.
proc; call (_ : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 /\ WithD.cd = 0 ==>
                Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\ CountG.cg <= qG + qD).
- by conseq (eqDX O) (A_bounded (DXB(O))) => /#.
by inline *; auto.
qed.

local lemma ADX_ll (O <: Oracles {-ADX(A)}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.abatch => islossless O.g =>
  islossless ADX(A, O).guess.
proof.
move=> ha hb hh hab hg; proc; call (A_ll (WithDX(O)) ha hb hh hab hg _).
- by proc; call rd_get_ll; call hg; auto.
by rnd; inline *; auto => />; exact ddata_ll.
qed.

(* PlayD with the flag Bad_D, and with the data drawn on its own and D not programmed. *)
local module PlayD1 (O : Oracles) = {
  proc play(p : pw, e : ent, y : state) : bool = {
    var hv, d, g;
    RD.RO.init(); WithD.cd <- 0; WithDB.badd <- false;
    hv <@ RG.RO.get(e);
    d <@ RD.RO.get(phr e hv);
    g <@ A(WithDB(O)).guess(y, d);
    return g = p;
  }
}.

local module PlayD2 (O : Oracles) = {
  proc play(p : pw, e : ent, y : state) : bool = {
    var d, g;
    RD.RO.init(); WithD.cd <- 0; WithDB.badd <- false;
    d <$ ddata;
    g <@ A(WithDB(O)).guess(y, d);
    return g = p;
  }
}.

(* PlayD reads G at E itself, which the shared step G1 does not allow; PlayDG asks its oracle instead.
   The extra query moves only the G counter and the flag, which the outcome does not read. *)
local module PlayDG (O : Oracles) = {
  proc play(p : pw, e : ent, y : state) : bool = {
    var hv, d, g;
    RD.RO.init(); WithD.cd <- 0;
    hv <@ O.g(e);
    d <@ RD.RO.get(phr e hv);
    g <@ A(WithD(O)).guess(y, d);
    return g = p;
  }
}.

local equiv d_g0 : Game(Setup0, PlayD(A)).main ~ Game(Setup0, PlayDG).main : ={glob A} ==> ={res}.
proof.
proc; inline PlayD(A, CountG(IG)).play PlayDG(CountG(IG)).play; wp.
call (_ : ={R.RO.m, RG.RO.m, RD.RO.m, IG.es, WithD.cd, Count.ca, Count.cb, Count.ch, CountB.dp});
  try (proc; inline *; auto; done).
- by proc; inline *; wp; while (={rest, ks0, R.RO.m}); auto.
inline CountG(IG).g IG.g; wp; conseq (_ : _ ==> ={p0, y0, d, glob A, R.RO.m, RG.RO.m, RD.RO.m, IG.es, WithD.cd,
  Count.ca, Count.cb, Count.ch, CountB.dp}) => />; sim.
qed.

local equiv d_flag : Game(Setup1, PlayDG).main ~ Game(Setup1, PlayD1).main : ={glob A} ==> ={res}.
proof.
proc; inline PlayDG(CountG(IG)).play PlayD1(CountG(IG)).play; wp.
call (_ : ={R.RO.m, RG.RO.m, RD.RO.m, IG.es, WithD.cd, Count.ca, Count.cb, Count.ch, CountB.dp});
  try (proc; inline *; auto; done).
- by proc; inline *; wp; while (={rest, ks0, R.RO.m}); auto.
by inline RD.RO.get RG.RO.get CountG(IG).g IG.g; wp; rnd; wp; rnd; wp; conseq (_ : _ ==> ={p0, y0, e, glob A,
  R.RO.m, RG.RO.m, RD.RO.m, IG.es, Count.ca, Count.cb, Count.ch, CountB.dp}) => />; sim.
qed.

(* Γ1 with the programmed G and D and Γ2 without them are identical until a G query at e* or a D
   query at a phrase of e*; the game itself reads G only at e* and D only at the phrase of e*. *)
local equiv upto_d : Game(Setup1, PlayD1).main ~ Game(Setup2, PlayD2).main :
  ={glob A} ==> (IG.bad \/ WithDB.badd){1} = (IG.bad \/ WithDB.badd){2} /\ (!(IG.bad \/ WithDB.badd){2} => ={res}).
proof.
proc; inline Setup1.run Setup2.run PlayD1(CountG(IG)).play PlayD2(CountG(IG)).play; wp.
call (_ : IG.bad \/ WithDB.badd,
          ={R.RO.m, IG.es, IG.bad, WithDB.badd, WithD.cd, Count.ca, Count.cb, Count.ch, CountB.dp, CountG.cg} /\
          eq_except (pred1 IG.es{1}) RG.RO.m{1} RG.RO.m{2} /\ IG.es{1} \notin RG.RO.m{2} /\
          eq_except (ofent IG.es{1}) RD.RO.m{1} RD.RO.m{2} /\
          (forall f, ent_of f = IG.es{1} => f \notin RD.RO.m{2}),
          (IG.bad \/ WithDB.badd){1}).
- exact A_ll.
- by proc; inline *; auto => />.
- by move=> &2 hb; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />.
- by move=> &2 hb; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />.
- by move=> &2 hb; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- proc; inline *; wp.
  while (={rest, ks0, R.RO.m}); 1: by auto.
  by auto.
- move=> &2 hb; proc; inline *; wp.
  by while true (size rest); auto => />; smt(dans_ll size_behead size_eq0 size_ge0).
- move=> &1; proc; inline *; wp.
  by while true (size rest); auto => />; smt(dans_ll size_behead size_eq0 size_ge0).
- proc; inline *; case (e{1} = IG.es{1}).
  + rcondt{1} 3; 1: by auto.
    rcondt{2} 3; 1: by auto => /> /#.
    by auto => />; smt(dprod_ll dver_ll drest_ll).
  rcondf{1} 3; 1: by auto.
  rcondf{2} 3; 1: by auto => /> /#.
  seq 4 4 : (#pre /\ ={x, r} /\ x{1} = e{1}); 1: by auto.
  if; 1: smt(eq_exceptP).
  + by auto => />; smt(eq_except_set_eq mem_set get_setE eq_exceptP).
  by auto => />; smt(eq_exceptP).
- by move=> &2 hb; proc; inline *; auto => />; smt(dprod_ll dver_ll drest_ll).
- by move=> &1; proc; inline *; auto => />; smt(dprod_ll dver_ll drest_ll).
- proc; inline *; case (ent_of f{1} = IG.es{1}).
  + rcondt{1} 2; 1: by auto.
    rcondt{2} 2; 1: by auto => /> /#.
    by auto => />; smt(ddata_ll).
  rcondf{1} 2; 1: by auto.
  rcondf{2} 2; 1: by auto => /> /#.
  seq 3 3 : (#pre /\ ={x, r} /\ x{1} = f{1}); 1: by auto.
  if; 1: smt(eq_exceptP).
  + by auto => />; smt(eq_except_set_eq mem_set get_setE eq_exceptP).
  by auto => />; smt(eq_exceptP).
- by move=> &2 hb; proc; inline *; auto => />; smt(ddata_ll).
- by move=> &1; proc; inline *; auto => />; smt(ddata_ll).
inline CountG(IG).init CountB(IG).init Count(IG).init RD.RO.init RD.RO.get RG.RO.get RG.RO.set; wp.
rnd; wp; rnd{1}; wp; rnd{1}; wp.
call (_ : ={R.RO.m}); 1: by sim.
by inline *; auto => />; smt(eq_except_setl mem_empty get_set_sameE ent_of_phr drest_ll dhash_ll).
qed.

local module WithDR (G : RG.RO) (O : Oracles) : OraclesD = {
  proc a = O.a
  proc b = O.b
  proc h = O.h
  proc abatch = O.abatch
  proc g = O.g
  proc dq(f : phrase) = {
    var d;
    WithD.cd <- WithD.cd + 1; if (ent_of f = IG.es) IG.bad <- true; G.sample(ent_of f);
    d <@ RD.RO.get(f); return d;
  }
}.

local module DD (G : RG.RO) = {
  proc distinguish() : bool = {
    var p, y, xs, d, g;
    R.RO.init();
    p <$ dP;
    y <$ dstate;
    xs <@ Net(Ideal).dec(p, y);
    IG.es <- (unpack xs).`1;
    IG.bad <- false;
    CountG(IGR(G)).init();
    RD.RO.init(); WithD.cd <- 0;
    d <$ ddata;
    g <@ A(WithDR(G, CountG(IGR(G)))).guess(y, d);
    return g = p \/ IG.bad;
  }
}.

local equiv dd_lro : Game(Setup2, PlayD2).main ~ RG.MainD(DD, RG.LRO).distinguish :
  ={glob A} ==> (res \/ IG.bad \/ WithDB.badd){1} = res{2}.
proof.
proc; inline Setup2.run PlayD2(CountG(IG)).play DD(RG.LRO).distinguish; wp.
call (_ : ={R.RO.m, RG.RO.m, RD.RO.m, IG.es, WithD.cd, Count.ca, Count.cb, Count.ch, CountB.dp, CountG.cg} /\
          IG.bad{2} = (IG.bad \/ WithDB.badd){1}).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; wp; while (={rest, ks0, R.RO.m}); auto.
- by proc; inline *; auto => /> /#.
- by proc; inline *; auto => /> /#.
inline CountG(IG).init CountB(IG).init Count(IG).init RD.RO.init.
inline CountG(IGR(RG.LRO)).init CountB(IGR(RG.LRO)).init Count(IGR(RG.LRO)).init; wp; rnd; wp.
call (_ : ={R.RO.m}); 1: by sim.
by inline *; auto.
qed.

local equiv dd_ro : RG.MainD(DD, RG.RO).distinguish ~ Game(Setup2, Play(ADX(A))).main :
  ={glob A} ==> res{1} = (res \/ IG.bad){2}.
proof.
proc; inline Setup2.run Play(ADX(A), CountG(IG)).play ADX(A, CountG(IG)).guess DD(RG.RO).distinguish; wp.
call (_ : ={R.RO.m, RG.RO.m, RD.RO.m, IG.es, IG.bad, WithD.cd, Count.ca, Count.cb, Count.ch, CountB.dp}).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; wp; while (={rest, ks0, R.RO.m}); auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
inline CountG(IG).init CountB(IG).init Count(IG).init RD.RO.init.
inline CountG(IGR(RG.RO)).init CountB(IGR(RG.RO)).init Count(IGR(RG.RO)).init; wp; rnd; wp.
call (_ : ={R.RO.m}); 1: by sim.
by inline *; auto.
qed.

(* Corollary G10 in its checksum-aware form. D queries count with the G queries. *)
lemma G10_derived &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= qG => 0 <= qD =>
  Pr[Game(Setup0, PlayD(A)).main() @ &m : res] <= top (kA %/ 12 + 1) + eps3 kA qB qH (qG + qD).
proof.
move=> hkA hqB hqH hqG hqD.
have -> : Pr[Game(Setup0, PlayD(A)).main() @ &m : res] = Pr[Game(Setup0, PlayDG).main() @ &m : res].
- by byequiv d_g0.
have -> : Pr[Game(Setup0, PlayDG).main() @ &m : res] = Pr[Game(Setup1, PlayDG).main() @ &m : res].
- by byequiv (G1 PlayDG).
have -> : Pr[Game(Setup1, PlayDG).main() @ &m : res] = Pr[Game(Setup1, PlayD1).main() @ &m : res].
- by byequiv d_flag.
have h1 : Pr[Game(Setup1, PlayD1).main() @ &m : res] <=
          Pr[Game(Setup2, PlayD2).main() @ &m : res \/ IG.bad \/ WithDB.badd].
- have e1 : Pr[Game(Setup1, PlayD1).main() @ &m : res] =
            Pr[Game(Setup1, PlayD1).main() @ &m : res /\ (IG.bad \/ WithDB.badd)] +
            Pr[Game(Setup1, PlayD1).main() @ &m : res /\ !(IG.bad \/ WithDB.badd)].
  + by rewrite Pr[mu_split (IG.bad \/ WithDB.badd)].
  have e2 : Pr[Game(Setup1, PlayD1).main() @ &m : res /\ !(IG.bad \/ WithDB.badd)] =
            Pr[Game(Setup2, PlayD2).main() @ &m : res /\ !(IG.bad \/ WithDB.badd)].
  + by byequiv upto_d => // /#.
  have e3 : Pr[Game(Setup1, PlayD1).main() @ &m : IG.bad \/ WithDB.badd] =
            Pr[Game(Setup2, PlayD2).main() @ &m : IG.bad \/ WithDB.badd].
  + by byequiv upto_d => // /#.
  have e4 : Pr[Game(Setup1, PlayD1).main() @ &m : res /\ (IG.bad \/ WithDB.badd)] <=
            Pr[Game(Setup1, PlayD1).main() @ &m : IG.bad \/ WithDB.badd] by rewrite Pr[mu_sub].
  have e5 : Pr[Game(Setup2, PlayD2).main() @ &m : res \/ IG.bad \/ WithDB.badd] =
            Pr[Game(Setup2, PlayD2).main() @ &m : (res \/ IG.bad \/ WithDB.badd) /\ (IG.bad \/ WithDB.badd)] +
            Pr[Game(Setup2, PlayD2).main() @ &m : (res \/ IG.bad \/ WithDB.badd) /\ !(IG.bad \/ WithDB.badd)].
  + by rewrite Pr[mu_split (IG.bad \/ WithDB.badd)].
  have e6 : Pr[Game(Setup2, PlayD2).main() @ &m : IG.bad \/ WithDB.badd] <=
            Pr[Game(Setup2, PlayD2).main() @ &m : (res \/ IG.bad \/ WithDB.badd) /\ (IG.bad \/ WithDB.badd)].
  + by rewrite Pr[mu_sub] => // &hr /#.
  have e7 : Pr[Game(Setup2, PlayD2).main() @ &m : res /\ !(IG.bad \/ WithDB.badd)] <=
            Pr[Game(Setup2, PlayD2).main() @ &m : (res \/ IG.bad \/ WithDB.badd) /\ !(IG.bad \/ WithDB.badd)].
  + by rewrite Pr[mu_sub] => // &hr /#.
  smt().
have h2 : Pr[Game(Setup2, PlayD2).main() @ &m : res \/ IG.bad \/ WithDB.badd] =
          Pr[Game(Setup2, Play(ADX(A))).main() @ &m : res \/ IG.bad].
- have -> : Pr[Game(Setup2, PlayD2).main() @ &m : res \/ IG.bad \/ WithDB.badd] =
            Pr[RG.MainD(DD, RG.LRO).distinguish() @ &m : res] by byequiv dd_lro.
  have <- : Pr[RG.MainD(DD, RG.RO).distinguish() @ &m : res] =
            Pr[RG.MainD(DD, RG.LRO).distinguish() @ &m : res].
  + have hll : forall (x : ent), is_lossless dhash by move=> _; exact dhash_ll.
    by byequiv (RG.FullEager.RO_LRO DD hll).
  by byequiv dd_ro.
have := gamma2 kA qB qH (qG + qD) (ADX(A)) ADX_bounded ADX_ll &m hkA hqB hqH _; 1: smt().
smt().
qed.
end section G10D.

(* ---- A 24-word source without wallet data (end of A.4) ------------------------------------- *)
(* With no verifier (r = 0) every G output is the one verifier value followed by uniform bits, so
   programming G(e* ) in Γ1 changes nothing: Γ0 equals Γ2, the container says nothing about the
   password, and the adversary wins with probability at most p_1, whatever it queries. *)
lemma ver_unique : r = 0 => forall (v v' : ver), v = v'.
proof.
move=> hr v v'; case: (v = v') => // hne.
have h := le1_mu dver (predU (pred1 v) (pred1 v')).
rewrite mu_disjoint in h; 1: by move=> x @/predI @/pred1 @/pred0 /#.
by move: h; rewrite !dver1 hr RField.expr0 RField.invr1.
qed.

section NoData.
declare module A <: Adv {-R.RO, -R.FRO, -RE.FunRO, -RG.RO, -RG.FRO, -IG, -Setup0, -Count, -CountB, -CountG,
                         -Mon, -Bwd, -WithG, -AG}.
declare axiom A_ll (O <: Oracles {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.abatch => islossless O.g =>
  islossless A(O).guess.

(* Γ1 and Γ2 with G as a parameter: Γ1 programs G(e* ), here a fresh sample of G at e*. *)
local module D12 (G : RG.RO) = {
  proc distinguish() : bool = {
    var p, y, xs, b;
    R.RO.init();
    p <$ dP;
    y <$ dstate;
    xs <@ Net(Ideal).dec(p, y);
    G.sample((unpack xs).`1);
    IG.es <- (unpack xs).`1;
    IG.bad <- false;
    CountG(IGR(G)).init();
    b <@ Play(A, CountG(IGR(G))).play(p, IG.es, y);
    return b;
  }
}.

local lemma g1_d12 : r = 0 =>
  equiv [Game(Setup1, Play(A)).main ~ RG.MainD(D12, RG.RO).distinguish : ={glob A} ==> ={res}].
proof.
move=> hr; proc; inline Setup1.run D12(RG.RO).distinguish RG.RO.sample RG.RO.get RG.RO.set.
seq 5 6 : (={glob A, xs, R.RO.m, RG.RO.m} /\ p0{1} = p{2} /\ y0{1} = y{2} /\ RG.RO.m{1} = empty).
- call (_ : ={R.RO.m}); 1: by sim.
  by inline *; auto.
seq 5 5 : (={glob A, xs, R.RO.m, RG.RO.m, IG.es} /\ p0{1} = p{2} /\ y0{1} = y{2}).
- rcondt{2} 4; 1: by auto => />; smt(mem_empty).
  wp; rnd (fun rs => ((unpack xs{1}).`2, rs)) (fun (r0 : hash) => r0.`2).
  auto => /> &2; split => [r0 _ | _]; 1: by have := ver_unique hr r0.`1 (unpack xs{2}).`2; smt().
  split => [[v rs] _ /= | _ rs hrs]; 1: by rewrite /dhash dprod1E dver1 hr RField.expr0 RField.invr1 RField.mul1r.
  rewrite /dhash supp_dprod /= hrs /= /support dver1 hr RField.expr0 RField.invr1; smt().
inline Play(A, CountG(IG)).play Play(A, CountG(IGR(RG.RO))).play.
wp; call (_ : ={R.RO.m, RG.RO.m, IG.es, IG.bad, Count.ca, Count.cb, Count.ch, CountB.dp, CountG.cg}).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; wp; while (={rest, ks0, R.RO.m}); auto.
- by proc; inline *; auto.
by inline *; auto.
qed.

local equiv d12_g2 : RG.MainD(D12, RG.LRO).distinguish ~ Game(Setup2, Play(A)).main : ={glob A} ==> ={res}.
proof.
proc; inline Setup2.run D12(RG.LRO).distinguish RG.LRO.sample.
inline Play(A, CountG(IG)).play Play(A, CountG(IGR(RG.LRO))).play.
wp; call (_ : ={R.RO.m, RG.RO.m, IG.es, IG.bad, Count.ca, Count.cb, Count.ch, CountB.dp, CountG.cg}).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; wp; while (={rest, ks0, R.RO.m}); auto.
- by proc; inline *; auto.
inline CountG(IGR(RG.LRO)).init CountB(IGR(RG.LRO)).init Count(IGR(RG.LRO)).init.
inline CountG(IG).init CountB(IG).init Count(IG).init; wp.
call (_ : ={R.RO.m}); 1: by sim.
by inline *; auto.
qed.

(* Without wallet data, a 24-word source: Pr[win] <= p_1. *)
lemma G0_p1 &m : r = 0 => Pr[Game(Setup0, Play(A)).main() @ &m : res] <= p1.
proof.
move=> hr.
have -> : Pr[Game(Setup0, Play(A)).main() @ &m : res] = Pr[Game(Setup1, Play(A)).main() @ &m : res].
- by byequiv (G1 (Play(A))).
have -> : Pr[Game(Setup1, Play(A)).main() @ &m : res] = Pr[RG.MainD(D12, RG.RO).distinguish() @ &m : res].
- by byequiv (g1_d12 hr).
have -> : Pr[RG.MainD(D12, RG.RO).distinguish() @ &m : res] = Pr[RG.MainD(D12, RG.LRO).distinguish() @ &m : res].
- have hll : forall (x : ent), is_lossless dhash by move=> _; exact dhash_ll.
  by byequiv (RG.FullEager.RO_LRO D12 hll).
have -> : Pr[RG.MainD(D12, RG.LRO).distinguish() @ &m : res] = Pr[Game(Setup2, Play(A)).main() @ &m : res].
- by byequiv d12_g2.
have -> : Pr[Game(Setup2, Play(A)).main() @ &m : res] = Pr[ChainGame(AG(A)).main() @ &m : AG.out = Bwd.p].
- by byequiv (lazy_gamma2 A) => // /#.
have -> : Pr[ChainGame(AG(A)).main() @ &m : AG.out = Bwd.p] = Pr[ChainLate(AG(A)).main() @ &m : AG.out = Bwd.p].
- by byequiv (chain_late (AG(A))).
byphoare => //; proc.
seq 6 : true 1%r p1 0%r 0%r => //.
seq 2 : (AG.out = Bwd.p) p1 1%r 1%r 0%r => //.
- wp; rnd (pred1 AG.out); auto => &hr /=; last by apply p1_ge0.
  by have h := mu1_p1 AG.out{hr}; split => // v _ ->.
hoare; call (_ : AG.out <> Bwd.p ==> AG.out <> Bwd.p); 2: by auto.
by proc; while (AG.out <> Bwd.p); [inline *; auto | auto].
qed.
end section NoData.

(* The matching attack of G8 extended by a test against Omega: a candidate passes if its verifier
   matches and Omega(e(w)) = omega*. *)
module MatchW (O : OraclesW) = {
  var cands : pw list
  proc guess(y : state, d : data) : pw = {
    var s11, j, w, i, z, s, k, m, v, dw, found, out;
    s11 <@ O.b(rd 11, y.`1);
    found <- false;
    out <- nth witness cands (size cands - 1);
    j <- 0;
    while (j < size cands - 1 /\ !found) {
      w <- nth witness cands j;
      z <- y;
      i <- 11;
      while (0 <= i) {
        if (i = 11) { s <- s11; } else { s <@ O.b(rd i, z.`1); }
        k <@ O.a(w, s);
        m <@ O.h(k, rd i, z.`1);
        z <- unround m z;
        i <- i - 1;
      }
      v <@ O.g((unpack z).`1);
      dw <@ O.w((unpack z).`1);
      if (v.`1 = (unpack z).`2 /\ dw = d) { found <- true; out <- w; }
      j <- j + 1;
    }
    return out;
  }
}.

op delta10 : real = inv (2%r ^ (r + lambda)) + inv (2%r ^ 128) + 12%r / 2%r ^ 256.

(* The proof of G10's matching bound, as for G8: a candidate before P passes with chance phi10g, which
   is 2^-(r + lambda) while its G and Omega points are unqueried. *)
module D10 (G : R.RO) = {
  proc distinguish() : bool = {
    var p, y, xs, rs, b;
    RG.RO.init();
    p <$ dP;
    y <$ dstate;
    xs <@ Net(Orc(G)).dec(p, y);
    rs <$ drest;
    RG.RO.set((unpack xs).`1, ((unpack xs).`2, rs));
    IG.es <- (unpack xs).`1;
    IG.bad <- false;
    CountG(IGF8(G)).init();
    b <@ PlayW(MatchW, CountG(IGF8(G))).play(p, IG.es, y);
    return b;
  }
}.

op phi10g (gm : (ent, hash) fmap) (wm : (ent, data) fmap) (d : data) (z : state) : real =
  if (unpack z).`1 \in gm then b2r ((oget gm.[(unpack z).`1]).`1 = (unpack z).`2 /\ oget wm.[(unpack z).`1] = d)
  else inv (2%r ^ (r + lambda)).

op S10 (f : point -> ans) (y : state) (ws : pw list) (p : pw) (j : int) (gm : (ent, hash) fmap)
       (wm : (ent, data) fmap) (d : data) : real =
  bigi predT (fun i => phi10g gm wm d (invperm f (nth witness ws i) y)) j (index p ws).

op Phi10 (f : point -> ans) (y : state) (ws : pw list) (gm : (ent, hash) fmap) (wm : (ent, data) fmap)
         (d : data) (found : bool) (out : pw) (j : int) (p : pw) : real =
  if found then b2r (out <> p) else if p \in ws /\ j <= index p ws then S10 f y ws p j gm wm d else 1%r.

op Phi10b (f : point -> ans) (y : state) (ws : pw list) (p : pw) : real =
  if p \in ws then
    bigi predT (fun i => inv (2%r ^ (r + lambda)) + b2r (invperm f (nth witness ws i) y = invperm f p y)) 0 (index p ws)
  else 1%r.

op phi10 (ws : pw list) (p : pw) : real = if p \in ws then (index p ws)%r * delta10 else 1%r.

lemma phi10g_ge0 gm wm d z : 0%r <= phi10g gm wm d z.
proof. by rewrite /phi10g; case: ((unpack z).`1 \in gm) => _; [apply b2r_ge0 | smt(expr_gt0 invr_gt0)]. qed.

lemma Ep_phi10g (gm : (ent, hash) fmap) (wm : (ent, data) fmap) d (x : ent) (z : state) : x \notin gm =>
  Ep (dhash `*` ddata) (fun (vd : hash * data) => (phi10g gm.[x <- vd.`1] wm.[x <- vd.`2] d z)%xr) =
  (phi10g gm wm d z)%xr.
proof.
move=> hx; rewrite /phi10g; case: ((unpack z).`1 = x) => hz.
- rewrite hz hx /= (eq_Ep _ _ (fun (vd : hash * data) => (vd.`1.`1 = (unpack z).`2 /\ vd.`2 = d)%xr)) => [vd _ /= | ].
  + by rewrite mem_set !get_set_sameE.
  rewrite Ep_mu (mu_eq _ _ (fun (vd : hash * data) => (fun (v : hash) => v.`1 = (unpack z).`2) vd.`1 /\
                   pred1 d vd.`2)) => [vd | ]; 1: by rewrite /pred1.
  rewrite (dprodE (fun (v : hash) => v.`1 = (unpack z).`2) (pred1 d) dhash ddata).
  rewrite (mu_eq _ _ (fun (v : hash) => pred1 (unpack z).`2 v.`1)) => [v | ]; 1: by rewrite /pred1.
  rewrite /dhash (dprodEl dver drest (pred1 (unpack z).`2)) drest_ll dver1 ddata1 /=.
  by rewrite (RField.exprD 2%r r lambda).
rewrite (eq_Ep _ _ (fun _ => (if (unpack z).`1 \in gm then
            b2r ((oget gm.[(unpack z).`1]).`1 = (unpack z).`2 /\ oget wm.[(unpack z).`1] = d)
          else inv (2%r ^ (r + lambda)))%xr)) => [vd _ /= | ].
- by rewrite mem_set hz /= !get_set_neqE.
have hll : is_lossless (dhash `*` ddata) by apply/dprod_ll; rewrite dhash_ll ddata_ll.
by rewrite EpC hll smul1m.
qed.

lemma S10_ge0 f y ws p j gm wm d : 0%r <= S10 f y ws p j gm wm d.
proof. by rewrite /S10; apply Bigreal.sumr_ge0 => i _; apply phi10g_ge0. qed.

lemma Ep_S10 f y ws p j (gm : (ent, hash) fmap) (wm : (ent, data) fmap) d (x : ent) : x \notin gm =>
  Ep (dhash `*` ddata) (fun (vd : hash * data) => (S10 f y ws p j gm.[x <- vd.`1] wm.[x <- vd.`2] d)%xr) =
  (S10 f y ws p j gm wm d)%xr.
proof.
move=> hx; rewrite /S10 Ep_sum => [i v | ]; 1: by apply phi10g_ge0.
rewrite (BXA.eq_bigr _ _ (fun i => (phi10g gm wm d (invperm f (nth witness ws i) y))%xr)) => [i _ /= | ].
- by apply Ep_phi10g.
by rewrite bigXR // => i _; apply phi10g_ge0.
qed.

lemma phi10g_init (xs z : state) rs d :
  phi10g empty.[(unpack xs).`1 <- ((unpack xs).`2, rs)] empty.[(unpack xs).`1 <- d] d z
  <= inv (2%r ^ (r + lambda)) + b2r (z = xs).
proof.
have h0 : 0%r < inv (2%r ^ (r + lambda)) by smt(expr_gt0 invr_gt0).
rewrite /phi10g mem_set mem_empty /=; case: ((unpack z).`1 = (unpack xs).`1) => h /=; 2: smt(b2r_ge0).
rewrite h !get_set_sameE /=; case: ((unpack xs).`2 = (unpack z).`2) => h2 /=; 2: smt(b2r_ge0).
have -> : z = xs by rewrite -(pack_unpack z) -(pack_unpack xs) h h2.
by rewrite /=; smt().
qed.

lemma core10_e (ws : pw list) (M : int) : uniq ws => size ws = M + 1 => 0 <= M =>
  ehoare [R.MainD(D10, RE.FunRO).distinguish :
    (MatchW.cands = ws) `|` (Ep dP (fun p => (phi10 ws p)%xr)) ==> (!res)%xr].
proof.
move=> hu hs hM; proc.
inline D10(RE.FunRO).distinguish PlayW(MatchW, CountG(IGF8(RE.FunRO))).play
  MatchW(WithW(CountG(IGF8(RE.FunRO)))).guess.
wp.
while ((MatchW.cands = ws /\ xs = invperm RE.FunRO.f p y1 /\ p0 = p /\
        RG.RO.m.[(unpack xs).`1] = Some ((unpack xs).`2, rs) /\
        RW.RO.m.[(unpack xs).`1] = Some d0 /\ (forall x, x \in RG.RO.m <=> x \in RW.RO.m) /\ s11 = salt_of (RE.FunRO.f (PB (rd 11, y1.`1))) /\
        0 <= j /\ (!found => out = nth witness ws M)) `|`
       (Phi10 RE.FunRO.f y1 ws RG.RO.m RW.RO.m d0 found out j p)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hc8 hx hp hG hW hdom hs11 hj hout.
  rewrite hp; apply xr_ble; rewrite /Phi10; move: hc hout; case: (found{hr}) => /= [// | hnf hc hout].
  case: (p{hr} \in ws /\ j{hr} <= index p{hr} ws) => hc2 /=; 2: by smt().
  have hk : index p{hr} ws = M by move: hc; rewrite hc8 hs; smt(index_mem).
  rewrite hout -hk nth_index 1:/# /=.
  by rewrite /S10; apply Bigreal.sumr_ge0 => i _ /=; apply phi10g_ge0.
- seq 4 : ((MatchW.cands = ws /\ xs = invperm RE.FunRO.f p y1 /\ p0 = p /\
            RG.RO.m.[(unpack xs).`1] = Some ((unpack xs).`2, rs) /\
        RW.RO.m.[(unpack xs).`1] = Some d0 /\ (forall x, x \in RG.RO.m <=> x \in RW.RO.m) /\ s11 = salt_of (RE.FunRO.f (PB (rd 11, y1.`1))) /\
            0 <= j < M /\ !found /\ out = nth witness ws M /\ w = nth witness ws j /\
            z = invperm RE.FunRO.f w y1) `|`
           (Phi10 RE.FunRO.f y1 ws RG.RO.m RW.RO.m d0 found out j p)%xr).
  + while ((MatchW.cands = ws /\ xs = invperm RE.FunRO.f p y1 /\ p0 = p /\
            RG.RO.m.[(unpack xs).`1] = Some ((unpack xs).`2, rs) /\
        RW.RO.m.[(unpack xs).`1] = Some d0 /\ (forall x, x \in RG.RO.m <=> x \in RW.RO.m) /\ s11 = salt_of (RE.FunRO.f (PB (rd 11, y1.`1))) /\
            0 <= j < M /\ !found /\ out = nth witness ws M /\ w = nth witness ws j /\ -1 <= i <= 11 /\
            z = foldl (fun (u : state) k => unround (mask RE.FunRO.f w (rd k) u.`1) u) y1
                      (rev (iota_ (i + 1) (11 - i)))) `|`
           (Phi10 RE.FunRO.f y1 ws RG.RO.m RW.RO.m d0 found out j p)%xr).
    * move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hc8 hx hp hG hW hdom hs11 hj0 hj1 hnf hout hw hi0 hi1 hz /=.
      apply xle_cxr_l; 2: by [].
      have hzx : z{hr} = invperm RE.FunRO.f{hr} w{hr} y1{hr} by rewrite hz (_ : i{hr} = -1) 1:/# /invperm.
      by rewrite hzx /=; smt().
    * inline *; auto => &hr /=; apply xle_cxr_r => -[hc [#] hc8 hx hp hG hW hdom hs11 hj0 hj1 hnf hout hw hi0 hi1 hz].
      have hstep : forall s0, s0 = salt_of (RE.FunRO.f{hr} (PB (rd i{hr}, z{hr}.`1))) =>
        unround (mask_of (RE.FunRO.f{hr} (PH (key_of (RE.FunRO.f{hr} (PA (w{hr}, s0))), rd i{hr}, z{hr}.`1)))) z{hr} =
        foldl (fun (u : state) k => unround (mask RE.FunRO.f{hr} w{hr} (rd k) u.`1) u) y1{hr}
              (rev (iota_ i{hr} (11 - (i{hr} - 1)))).
      - move=> s0 ->; rewrite (_ : 11 - (i{hr} - 1) = (11 - i{hr}) + 1) 1:/# iotaS 1:/# rev_cons foldl_rcons -hz.
        by rewrite /mask.
      case: (i{hr} = 11) => hi11 /=.
      - apply xle_cxr_l; 2: by [].
        have hz1 : z{hr} = y1{hr} by rewrite hz hi11 /= iota0.
        have h := hstep s11{hr} _; 1: by rewrite hs11 hz1 hi11.
        by rewrite h; smt().
      apply xle_cxr_l; 2: by [].
      have h := hstep (salt_of (RE.FunRO.f{hr} (PB (rd i{hr}, z{hr}.`1)))) _ => //.
      by rewrite h; smt().
    auto => &hr /=; apply xle_cxr_r => -[[hc hnf] [#] hc8 hx hp hG hW hdom hs11 hj hout].
    by apply xle_cxr_l => //; rewrite iota0 //=; smt().
  inline *; auto => &hr /=; apply xle_cxr_r => -[#] hc8 hx hp hG hW hdom hs11 hj0 hj1 hnf hout hw hz.
  have hf : found{hr} = false by smt().
  have hG' : forall r, (unpack z{hr}).`1 \notin RG.RO.m{hr} =>
             RG.RO.m{hr}.[(unpack z{hr}).`1 <- r].[(unpack xs{hr}).`1] = Some ((unpack xs{hr}).`2, rs{hr}).
  - by move=> r hn; rewrite get_set_neqE //; apply/negP => h; move: hn; rewrite -h domE hG.
  have hW' : forall r, (unpack z{hr}).`1 \notin RG.RO.m{hr} =>
             RW.RO.m{hr}.[(unpack z{hr}).`1 <- r].[(unpack xs{hr}).`1] = Some d0{hr}.
  - by move=> r hn; rewrite get_set_neqE //; apply/negP => h; move: hn; rewrite -h domE hG.
  have hll : is_lossless (dhash `*` ddata) by apply/dprod_ll; rewrite dhash_ll ddata_ll.
  case: (p{hr} \in ws /\ j{hr} < index p{hr} ws) => hc2.
  - have [hpin hjk] := hc2.
    have hwp : w{hr} <> p{hr} by rewrite hw; apply (before_index witness); smt().
    have hsplit : forall (gm : (ent, hash) fmap) (wm : (ent, data) fmap),
                  S10 RE.FunRO.f{hr} y1{hr} ws p{hr} j{hr} gm wm d0{hr} =
                  phi10g gm wm d0{hr} z{hr} + S10 RE.FunRO.f{hr} y1{hr} ws p{hr} (j{hr} + 1) gm wm d0{hr}.
    + by move=> gm wm; rewrite /S10 big_ltn 1:/# /= hz hw.
    have hpt : forall (gm : (ent, hash) fmap) (wm : (ent, data) fmap), (unpack z{hr}).`1 \in gm =>
      (if (oget gm.[(unpack z{hr}).`1]).`1 = (unpack z{hr}).`2 /\ oget wm.[(unpack z{hr}).`1] = d0{hr}
       then Phi10 RE.FunRO.f{hr} y1{hr} ws gm wm d0{hr} true w{hr} (j{hr} + 1) p{hr}
       else Phi10 RE.FunRO.f{hr} y1{hr} ws gm wm d0{hr} found{hr} out{hr} (j{hr} + 1) p{hr})
      <= S10 RE.FunRO.f{hr} y1{hr} ws p{hr} j{hr} gm wm d0{hr}.
    + move=> gm wm hin; rewrite hsplit /phi10g hin /=.
      have := S10_ge0 RE.FunRO.f{hr} y1{hr} ws p{hr} (j{hr} + 1) gm wm d0{hr}.
      case: ((oget gm.[(unpack z{hr}).`1]).`1 = (unpack z{hr}).`2 /\ oget wm.[(unpack z{hr}).`1] = d0{hr}) => hv /=.
      * by rewrite /Phi10 /= hwp /=; smt().
      by rewrite /Phi10 hf /= hpin (_ : j{hr} + 1 <= index p{hr} ws) 1:/# /=; smt().
    have -> : Phi10 RE.FunRO.f{hr} y1{hr} ws RG.RO.m{hr} RW.RO.m{hr} d0{hr} found{hr} out{hr} j{hr} p{hr} =
              S10 RE.FunRO.f{hr} y1{hr} ws p{hr} j{hr} RG.RO.m{hr} RW.RO.m{hr} d0{hr}.
    + by rewrite /Phi10 hf /= hpin (_ : j{hr} <= index p{hr} ws) 1:/#.
    case: ((unpack z{hr}).`1 \in RG.RO.m{hr}) => hxin.
    + have hxw : (unpack z{hr}).`1 \in RW.RO.m{hr} by rewrite -hdom.
      rewrite hxw /= !EpC dhash_ll ddata_ll !smul1m; have := hpt _ RW.RO.m{hr} hxin.
      case: ((oget RG.RO.m{hr}.[(unpack z{hr}).`1]).`1 = (unpack z{hr}).`2 /\
             oget RW.RO.m{hr}.[(unpack z{hr}).`1] = d0{hr}) => hv /= h.
      * by apply xle_cxr_l; [smt() | apply xr_le].
      by apply xle_cxr_l; [smt() | apply xr_le].
    have hxw : (unpack z{hr}).`1 \notin RW.RO.m{hr} by rewrite -hdom.
    rewrite hxw /= Ep_dprod.
    apply (xle_trans (Ep (dhash `*` ddata) (fun (vd : hash * data) => (S10 RE.FunRO.f{hr} y1{hr} ws p{hr} j{hr}
             RG.RO.m{hr}.[(unpack z{hr}).`1 <- vd.`1] RW.RO.m{hr}.[(unpack z{hr}).`1 <- vd.`2] d0{hr})%xr))).
    + apply le_Ep => vd _ /=.
      have := hpt RG.RO.m{hr}.[(unpack z{hr}).`1 <- vd.`1] RW.RO.m{hr}.[(unpack z{hr}).`1 <- vd.`2] _; 1: by rewrite mem_set.
      case: ((oget RG.RO.m{hr}.[(unpack z{hr}).`1 <- vd.`1].[(unpack z{hr}).`1]).`1 = (unpack z{hr}).`2 /\
             oget RW.RO.m{hr}.[(unpack z{hr}).`1 <- vd.`2].[(unpack z{hr}).`1] = d0{hr}) => hv /= h.
      * by apply xle_cxr_l; [rewrite hG' // hW' //; smt(mem_set) | apply xr_le].
      by apply xle_cxr_l; [rewrite hG' // hW' //; smt(mem_set) | apply xr_le].
    by rewrite Ep_S10.
  case: (p{hr} \in ws /\ j{hr} = index p{hr} ws) => hc3.
  - have [hpin hjk] := hc3.
    have hwp : w{hr} = p{hr} by rewrite hw hjk nth_index.
    have hzx : z{hr} = xs{hr} by rewrite hz hwp hx.
    have hxin : (unpack z{hr}).`1 \in RG.RO.m{hr} by rewrite hzx domE hG.
    have hxw : (unpack z{hr}).`1 \in RW.RO.m{hr} by rewrite -hdom.
    rewrite hxin hxw /= hzx hG hW /= !EpC dhash_ll ddata_ll !smul1m.
    apply xle_cxr_l; 1: smt().
    by rewrite /Phi10 /= hwp /= hf /= hpin hjk /= /S10 big_geq.
  have -> : Phi10 RE.FunRO.f{hr} y1{hr} ws RG.RO.m{hr} RW.RO.m{hr} d0{hr} found{hr} out{hr} j{hr} p{hr} = 1%r.
  - by rewrite /Phi10 hf /=; smt().
  have hle : forall (gm : (ent, hash) fmap) (wm : (ent, data) fmap) fd o,
             Phi10 RE.FunRO.f{hr} y1{hr} ws gm wm d0{hr} fd o (j{hr} + 1) p{hr} <= 1%r.
  - by move=> gm wm fd o; rewrite /Phi10; case: fd => _ /=; [smt() | smt()].
  case: ((unpack z{hr}).`1 \in RG.RO.m{hr}) => hxin.
  - have hxw : (unpack z{hr}).`1 \in RW.RO.m{hr} by rewrite -hdom.
    rewrite hxw /= !EpC dhash_ll ddata_ll !smul1m.
    case: ((oget RG.RO.m{hr}.[(unpack z{hr}).`1]).`1 = (unpack z{hr}).`2 /\
           oget RW.RO.m{hr}.[(unpack z{hr}).`1] = d0{hr}) => hv /=.
    + by apply xle_cxr_l; [smt() | apply xr_le; apply hle].
    by apply xle_cxr_l; [smt() | apply xr_le; apply hle].
  have hxw : (unpack z{hr}).`1 \notin RW.RO.m{hr} by rewrite -hdom.
  rewrite hxw /= Ep_dprod; apply (xle_trans (Ep (dhash `*` ddata) (fun _ => 1%xr))); 2: by rewrite EpC hll smul1m.
  apply le_Ep => vd _ /=.
  case: ((oget RG.RO.m{hr}.[(unpack z{hr}).`1 <- vd.`1].[(unpack z{hr}).`1]).`1 = (unpack z{hr}).`2 /\
         oget RW.RO.m{hr}.[(unpack z{hr}).`1 <- vd.`2].[(unpack z{hr}).`1] = d0{hr}) => hv /=.
  + by apply xle_cxr_l; [rewrite hG' // hW' //; smt(mem_set) | apply xr_le; apply hle].
  by apply xle_cxr_l; [rewrite hG' // hW' //; smt(mem_set) | apply xr_le; apply hle].
inline *; wp.
conseq (_ : _ ==> (y2 = invperm RE.FunRO.f p y /\ RG.RO.m = empty /\ MatchW.cands = ws) `|` (Phi10b RE.FunRO.f y ws p)%xr).
- move=> &hr; apply xle_cxr_l => // m1 f p3 y4 y2_0; apply xle_cxr_r => -[#] hy h1 h2 /=.
  apply (xle_trans (Ep drest (fun _ => (Phi10b f y4 ws p3)%xr))); 2: by rewrite EpC drest_ll smul1m.
  apply le_Ep => rs0 _ /=.
  apply (xle_trans (Ep ddata (fun _ => (Phi10b f y4 ws p3)%xr))); 2: by rewrite EpC ddata_ll smul1m.
  apply le_Ep => d _ /=; rewrite mem_empty /=; apply xle_cxr_l.
  + by rewrite h1 h2 hy !get_set_sameE /= hs; smt(mem_set mem_empty).
  apply xr_le; rewrite /Phi10 /Phi10b /=; case: (p3 \in ws) => hin //=.
  rewrite index_ge0 /= /S10; apply Bigreal.ler_sum => i _ /=; rewrite h1 get_set_sameE /= -hy.
  by apply phi10g_init.
- move=> &hr; apply xle_cxr_r => h.
  exact (h RG.RO.m{hr} RE.FunRO.f{hr} p{hr} y{hr} y2{hr}).
while ((p1 = p /\ -1 <= i0 <= 11 /\ RG.RO.m = empty /\ MatchW.cands = ws /\
        y2 = foldl (fun (u : state) k => unround (mask RE.FunRO.f p (rd k) u.`1) u) y
                   (rev (iota_ (i0 + 1) (11 - i0)))) `|` (Phi10b RE.FunRO.f y ws p)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hp hi0 hi1 hG hc8 hy.
  by apply xle_cxr_l => //; rewrite hG hc8 hy /= (_ : i0{hr} = -1) 1:/# /invperm.
- auto => &hr /=; apply xle_cxr_r => -[hc [#] hp hi0 hi1 hG hc8 hy].
  apply xle_cxr_l => //; rewrite hp hG hc8 /=; split; 1: smt().
  rewrite (_ : 11 - (i0{hr} - 1) = (11 - i0{hr}) + 1) 1:/# iotaS 1:/# rev_cons foldl_rcons -hy /=.
  by rewrite /mask.
wp; skip => &hr /=; apply xle_cxr_r => hc8.
have hll : is_lossless (RE.MUniFinFun.dfun (fun (_ : point) => dans)).
- by apply RE.MUniFinFun.dfun_ll => z /=; apply dans_ll.
apply (xle_trans (Ep (RE.MUniFinFun.dfun (fun (_ : point) => dans))
         (fun f => Ep dP (fun pv => Ep dstate (fun yv => (Phi10b f yv ws pv)%xr))))).
- apply le_Ep => f _ /=; apply le_Ep => pv _ /=; apply le_Ep => yv _ /=.
  by apply xle_cxr_l; [rewrite hc8 iota0 | done].
rewrite Ep_swap; apply le_Ep => pv _ /=; rewrite Ep_swap.
apply (xle_trans (Ep dstate (fun _ => (phi10 ws pv)%xr))); 2: by rewrite EpC dstate_ll smul1m.
apply le_Ep => yv _ /=; case: (pv \in ws) => hin; last first.
- by rewrite /Phi10b /phi10 hin /= EpC hll smul1m.
have hr0 : 0%r < inv (2%r ^ (r + lambda)) by smt(expr_gt0 invr_gt0).
rewrite /Phi10b hin /= Ep_sum => [i f | ]; 1: smt(b2r_ge0).
rewrite (BXA.eq_bigr _ _ (fun i => (inv (2%r ^ (r + lambda)) + mu (RE.MUniFinFun.dfun (fun (_ : point) => dans))
            (fun f => invperm f (nth witness ws i) yv = invperm f pv yv))%xr)) => [i _ /= | ].
- by rewrite (Ep_cb _ _ _ hll) //; smt().
rewrite bigXR => [i _ | ]; 1: smt(ge0_mu).
apply xr_le; rewrite /phi10 hin /=.
apply (ler_trans (bigi predT (fun _ => delta10) 0 (index pv ws))).
- apply Bigreal.ler_sum_seq => i /mem_range hi _ /=; rewrite /delta10.
  have hne : pv <> nth witness ws i.
  + by apply/negP => h; have := before_index witness pv ws i _; [smt() | rewrite -h].
  have h1 := pair_coll &hr pv (nth witness ws i) yv hne.
  have h2 := mu_le (RE.MUniFinFun.dfun (fun (_ : point) => dans))
               (fun f => invperm f (nth witness ws i) yv = invperm f pv yv)
               (fun f => (invperm f (nth witness ws i) yv).`1 = (invperm f pv yv).`1) _; 1: smt().
  by move: h1; rewrite /e128 /e256; smt().
by rewrite sumri_const; [smt(index_ge0) | rewrite RField.intmulr; smt()].
qed.

lemma core10 &m (ws : pw list) (M : int) : MatchW.cands{m} = ws => uniq ws => size ws = M + 1 =>
  bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * delta10)) 0 (M + 1)
    <= Pr[R.MainD(D10, RE.FunRO).distinguish() @ &m : res].
proof.
move=> hc hu hs; case: (M < 0) => hM; 1: by rewrite big_geq 1:/#; smt(mu_bounded).
have hd : 0%r <= delta10 by rewrite /delta10; smt(expr_gt0 invr_gt0).
have hS := sum_cands ws (fun p => (index p ws)%r * delta10) hu.
have hR : bigi predT (fun j => mu1 dP (nth witness ws j) *
            (1%r - (fun p => (index p ws)%r * delta10) (nth witness ws j))) 0 (size ws) =
          bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * delta10)) 0 (M + 1).
- by rewrite hs; apply eq_big_int => j hj /=; rewrite index_uniq // /#.
move: hS; rewrite hR => hS.
have hge : 0%r <= 1%r - bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * delta10)) 0 (M + 1).
- rewrite -hS; apply Bigreal.sumr_ge0 => p _ /=.
  by case: (p \in ws) => _; smt(ge0_mu index_ge0 mulr_ge0).
have hE : Ep dP (fun p => (phi10 ws p)%xr) =
          (1%r - bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * delta10)) 0 (M + 1))%xr.
- rewrite (eq_Ep _ _ (fun p => ((if p \in ws then (index p ws)%r * delta10 else 1%r))%xr)) => [p _ /= | ].
  + by rewrite /phi10.
  by rewrite Ep_dP => [p | ]; [case: (p \in ws) => _ //; smt(index_ge0) | rewrite hS].
have hll : islossless R.MainD(D10, RE.FunRO).distinguish.
- have hdf : is_lossless (RE.MUniFinFun.dfun (fun (_ : point) => dans)).
  + by apply RE.MUniFinFun.dfun_ll => z /=; apply dans_ll.
  proc; inline *; wp; while true (size MatchW.cands - 1 - j).
  + move=> z0; wp; rnd; wp; rnd; wp; while true (i2 + 1); 1: by move=> z1; auto => /#.
    auto => /> &hr hj hnf i20; split; 1: smt().
    move=> _; rewrite (mu_eq _ _ predT) => [r | ]; 2: by apply dhash_ll.
    by rewrite /predT /= (mu_eq _ _ predT) 1:/# ddata_ll.
  wp; rnd; wp; rnd; wp; while true (i + 1); 1: by move=> z1; auto => /#.
  by auto => />; smt(dP_ll dstate_ll drest_ll ddata_ll).
have h1 : Pr[R.MainD(D10, RE.FunRO).distinguish() @ &m : !res] <=
          1%r - bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * delta10)) 0 (M + 1).
- byehoare (_ : (MatchW.cands = ws) `|` (Ep dP (fun p => (phi10 ws p)%xr)) ==> (!res)%xr) => //.
  + by apply (core10_e ws M hu hs); smt().
  by rewrite hc /= hE.
have h2 : Pr[R.MainD(D10, RE.FunRO).distinguish() @ &m : true] = 1%r by byphoare => //; apply hll.
have h3 : Pr[R.MainD(D10, RE.FunRO).distinguish() @ &m : !res] =
          Pr[R.MainD(D10, RE.FunRO).distinguish() @ &m : true] - Pr[R.MainD(D10, RE.FunRO).distinguish() @ &m : res].
- by rewrite Pr[mu_not].
smt().
qed.

lemma G10_match &m (ws : pw list) (m : int) : MatchW.cands{m} = ws => uniq ws => size ws = m + 1 =>
  bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * delta10)) 0 (m + 1)
    <= Pr[Game(Setup0, PlayW(MatchW)).main() @ &m : res].
proof.
move=> hc hu hs.
have -> : Pr[Game(Setup0, PlayW(MatchW)).main() @ &m : res] = Pr[Game(Setup1, PlayW(MatchW)).main() @ &m : res].
- by byequiv (G1 (PlayW(MatchW))).
have -> : Pr[Game(Setup1, PlayW(MatchW)).main() @ &m : res] = Pr[R.MainD(D10, R.RO).distinguish() @ &m : res].
- by byequiv => //; proc; inline *; sim.
have -> : Pr[R.MainD(D10, R.RO).distinguish() @ &m : res] = Pr[R.MainD(D10, RE.FunRO).distinguish() @ &m : res].
- by byequiv (RO_FunRO D10).
exact (core10 &m ws m hc hu hs).
qed.

lemma G10_top &m (m : int) : 0 <= m => m + 1 <= PwT.card => MatchW.cands{m} = take (m + 1) ranked =>
  top (m + 1) * (1%r - m%r * delta10) <= Pr[Game(Setup0, PlayW(MatchW)).main() @ &m : res].
proof.
move=> hm hcard hc; have [hu [hs ht]] := ranked_top m delta10 hm hcard _.
- by rewrite /delta10; smt(expr_gt0 invr_gt0).
exact (StdOrder.RealOrder.ler_trans _ _ _ ht (G10_match &m (take (m + 1) ranked) m hc hu hs)).
qed.

lemma G10_budget (O <: OraclesW {-Count, -CountB, -CountG, -WithW, -MatchW}) (m : int) : 0 <= m =>
  hoare [MatchW(CountW(O)).guess :
    size MatchW.cands = m + 1 /\ Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountG.cg = 0 /\
    WithW.cw = 0 ==>
    Count.ca <= 12 * m /\ Count.cb <= 11 * m + 1 /\ Count.ch <= 12 * m /\ CountG.cg <= m /\
    WithW.cw <= m].
proof.
move=> hm; proc.
while (0 <= j <= m /\ size MatchW.cands = m + 1 /\ Count.ca = 12 * j /\ Count.cb = 1 + 11 * j /\
       Count.ch = 12 * j /\ CountG.cg = j /\ WithW.cw = j).
- inline *; wp; call (_ : true); wp; call (_ : true); wp.
  while (-1 <= i <= 11 /\ 0 <= j < m /\ size MatchW.cands = m + 1 /\ Count.ca = 12 * j + (11 - i) /\
         Count.cb = 1 + 11 * j + max 0 (10 - i) /\ Count.ch = 12 * j + (11 - i) /\ CountG.cg = j /\
         WithW.cw = j).
  + wp; call (_ : true); wp; call (_ : true); wp.
    if; 1: by auto => /> /#.
    by wp; call (_ : true); auto => /> /#.
  by auto => /> /#.
by inline *; wp; call (_ : true); auto => /> /#.
qed.

end Source.
