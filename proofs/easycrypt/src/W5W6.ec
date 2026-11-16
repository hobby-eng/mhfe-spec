(* Corollary W5 (the phrase and passphrase) and Corollary W6 (an ordinary 24-word source)
   (DESIGN-NOTES A.6). *)
require import AllCore List Distr DBool DProd FMap IntDiv StdBigop StdOrder Xreal.
require import Suite3 Chain Collision Passphrase Generation Selection Theta2 Theorem5.
import W128 StdBigop.Bigreal.BRA RealOrder.

(* ---- Corollary W5: phrase and passphrase, and Corollary W6: an ordinary 24-word source ------- *)
(* E is uniform without the profile, seed* = S(E, Q) and omega* = Omega(seed* ). *)
module Setup0O = {
  proc run() : state * data = {
    var y, om;
    R.RO.init(); RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Gen.e <$ dstate;
    Gen.sd <@ RS.RO.get(Gen.e, Gen.q);
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    return (y, om);
  }
}.


(* Lemma W3 for an ordinary source: Θ0 of Corollary W6 and Θ1 without T agree. *)
section W3O.
declare module D <: CONT {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RT.RO, -RW.RO, -Gen}.

local module IPG (G : R.RO) : OraclesP = {
  proc a = Orc(G).a
  proc b = Orc(G).b
  proc h = Orc(G).h
  proc s = IP.s
  proc t = IP.t
  proc w = IP.w
}.

local module V0 (G : R.RO) = {
  proc distinguish() : bool = {
    var y, om, b;
    RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Gen.e <$ dstate;
    Gen.sd <$ dseed;
    RS.RO.set((Gen.e, Gen.q), Gen.sd);
    y <@ Net(Orc(G)).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    b <@ D(IPG(G)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd);
    return b;
  }
}.

local module V1 (G : R.RO) = {
  proc distinguish() : bool = {
    var y, om, b;
    RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    y <$ dstate;
    om <$ ddata;
    Gen.sd <$ dseed;
    Gen.e <@ Net(Orc(G)).dec(Gen.p, y);
    RS.RO.set((Gen.e, Gen.q), Gen.sd);
    RW.RO.set(Gen.sd, om);
    b <@ D(IPG(G)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd);
    return b;
  }
}.

local equiv G0_V0 : GenGame(Setup0O, D).main ~ R.MainD(V0, R.RO).distinguish : ={glob D} ==> ={res, glob D}.
proof. by proc; inline *; sim; auto => />; smt(mem_empty get_set_sameE). qed.

local equiv G1_V1 : GenGame(Setup1O, D).main ~ R.MainD(V1, R.RO).distinguish : ={glob D} ==> ={res, glob D}.
proof. by proc; inline *; sim. qed.

local equiv core3 : R.MainD(V0, RE.FunRO).distinguish ~ R.MainD(V1, RE.FunRO).distinguish :
  ={glob D} ==> ={res, glob D}.
proof.
proc; inline V0(RE.FunRO).distinguish V1(RE.FunRO).distinguish.
seq 7 7 : (={glob D, RE.FunRO.f, RS.RO.m, RT.RO.m, RW.RO.m, Gen.p, Gen.q} /\ RW.RO.m{1} = empty).
- by inline *; auto.
swap{2} 2 1.
seq 2 2 : (={glob D, RE.FunRO.f, RS.RO.m, RT.RO.m, RW.RO.m, Gen.p, Gen.q, Gen.sd} /\ RW.RO.m{1} = empty /\
           y{2} = perm RE.FunRO.f{1} Gen.p{1} Gen.e{1}).
- rnd; rnd (fun e => perm RE.FunRO.f{1} Gen.p{1} e) (fun y => invperm RE.FunRO.f{1} Gen.p{1} y).
  by auto => /> &2; split => [y _ | _ e _]; [rewrite permK | rewrite invpermK].
swap{2} 1 2.
seq 0 1 : (#pre /\ Gen.e{2} = invperm RE.FunRO.f{2} Gen.p{2} y{2}).
- by exlim Gen.p{2}, y{2} => p0 y0; call{2} (dec_fun_ph p0 y0); auto.
seq 1 1 : (={glob D, RE.FunRO.f, RS.RO.m, RT.RO.m, RW.RO.m, Gen.p, Gen.q, Gen.sd, Gen.e} /\
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

lemma W3O : equiv [GenGame(Setup0O, D).main ~ GenGame(Setup1O, D).main : ={glob D} ==> ={res, glob D}].
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
end section W3O.

op epsW6 (kA kS qB qH qW : int) : real =
  (s1 * kS%r + qB%r + (1%r + 12%r * p1) * kA%r + 66%r) / 2%r ^ 128 + (qH%r + kA%r) / 2%r ^ 256
  + qW%r / 2%r ^ 512 + inv (2%r ^ 256).

module type AdvP5 (O : OraclesP) = { proc guess(y : state, om : data) : state * pp }.
module type AFTER5 = { proc run(p : pw, q : pp, y : state) : state * pp }.

(* The adversary wins if it outputs (E, Q). *)
module Game5 (S : SETUPP) (A : AdvP5) (Rf : AFTER5) = {
  proc main() : state * pp = {
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

(* The creation refusal: Y = E has chance 2^-256 over the network, which E does not use. *)
module T6 = {
  proc main() : bool = {
    var y;
    R.RO.init(); RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Gen.e <$ dstate;
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    return y = Gen.e;
  }
}.

lemma T6_pr &m : Pr[T6.main() @ &m : res] <= inv (2%r ^ 256).
proof.
byphoare => //; proc.
seq 7 : true 1%r (inv (2%r ^ 256)) 0%r 0%r (R.RO.m = empty) => //; 1: by inline *; auto.
exlim Gen.p, Gen.e => p0 x0.
have := enc_uniform_ph p0 x0 x0; rewrite dstate1_256 => h.
call (_ : arg = (p0, x0) /\ (forall c, c \in R.RO.m => isA c \/ isB c) ==> res = x0).
- bypr => &m0; split; 1: smt(expr_gt0 invr_gt0).
  move=> hpre; have -> // : Pr[Net(Ideal).enc(p{m0}, x{m0}) @ &m0 : res = x0] = inv (2%r ^ 256).
  by byphoare h => //; smt().
by auto => />; smt(mem_empty).
qed.

lemma setup_refusedO &m : Pr[Setup0O.run() @ &m : res.`1 = Gen.e] <= inv (2%r ^ 256).
proof.
have <- : Pr[T6.main() @ &m : res] = Pr[Setup0O.run() @ &m : res.`1 = Gen.e]; 2: exact T6_pr.
byequiv => //; proc; call{2} rw_get_ll.
call (_ : ={R.RO.m}); 1: by sim.
call{2} rs_get_ll.
by conseq (_ : _ ==> ={Gen.p, Gen.e, R.RO.m}) => //; sim.
qed.

section W6.
declare op kA : int.
declare op qB : int.
declare op qH : int.
declare op kS : int.
declare op qT : int.
declare op qW : int.
declare module A <: AdvP {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO,
                           -RW.RO, -Gen, -Trials, -Count,
                          -CountB, -CountP, -Mon, -Bwd, -WithP, -AP}.
declare module Rf <: AFTERP {-Gen}.
declare axiom Rf_ll : islossless Rf.run.
declare axiom A_bounded (O <: OraclesP {-Count, -CountP, -A}) :
  hoare [A(CountP(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
    CountP.cs <= kS /\ CountP.ct <= qT /\ CountP.cw <= qW].
declare axiom A_ll (O <: OraclesP {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless A(O).guess.

local lemma guess_ll6 : islossless A(CountP(IP)).guess.
proof. by apply (A_ll (CountP(IP))); proc; inline *; auto => />; smt(dans_ll dseed_ll dct_ll ddata_ll). qed.

(* The budgets are nonnegative: the counters start at 0 and the adversary terminates. *)
local module GB6 = {
  proc main() : unit = {
    var out;
    CountP(IP).init();
    out <@ A(CountP(IP)).guess(witness, witness);
  }
}.

local lemma ge0_budgets6 &m : 0 <= qB /\ 0 <= qH /\ 0 <= kS /\ 0 <= qW.
proof.
case: (0 <= qB /\ 0 <= qH /\ 0 <= kS /\ 0 <= qW) => // hneg.
have h1 : Pr[GB6.main() @ &m : true] = 1%r.
- by byphoare => //; proc; call guess_ll6; inline *; auto.
have h2 : Pr[GB6.main() @ &m : !(0 <= qB /\ 0 <= qH /\ 0 <= kS /\ 0 <= qW)] = 0%r.
- byphoare => //; hoare; proc.
  call (_ : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
            0 <= qB /\ 0 <= qH /\ 0 <= kS /\ 0 <= qW).
  + conseq (A_bounded IP) (_ : 0 <= Count.cb /\ 0 <= Count.ch /\ 0 <= CountP.cs /\ 0 <= CountP.cw ==>
                               0 <= Count.cb /\ 0 <= Count.ch /\ 0 <= CountP.cs /\ 0 <= CountP.cw) => [/# | /# |].
    by proc (0 <= Count.cb /\ 0 <= Count.ch /\ 0 <= CountP.cs /\ 0 <= CountP.cw) => //; proc; inline *; auto => /#.
  by inline *; auto.
have : Pr[GB6.main() @ &m : !(0 <= qB /\ 0 <= qH /\ 0 <= kS /\ 0 <= qW)] = Pr[GB6.main() @ &m : true].
- by rewrite Pr[mu_eq] => // /#.
smt().
qed.

local module Flag6 = { var r : bool }.

local module GameF6 = {
  proc main() : seed * (pw * pp) = {
    var y, om, out;
    (y, om) <@ Setup0O.run();
    Flag6.r <- y = Gen.e;
    CountP(IP).init();
    out <@ A(CountP(IP)).guess(y, om);
    return out;
  }
}.

local lemma refusal6 (E : seed * (pw * pp) -> pw -> pp -> seed -> bool) &m :
  Pr[GamePR(Setup0O, A, Rf).main() @ &m : E res Gen.p Gen.q Gen.sd] <=
  Pr[GameP(Setup0O, A).main() @ &m : E res Gen.p Gen.q Gen.sd] + inv (2%r ^ 256).
proof.
have h1 : Pr[GamePR(Setup0O, A, Rf).main() @ &m : E res Gen.p Gen.q Gen.sd] <=
          Pr[GameF6.main() @ &m : E res Gen.p Gen.q Gen.sd \/ Flag6.r].
- byequiv => //; proc.
  seq 1 1 : (={y, om, glob A, glob Gen, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); 1: by sim.
  if{1}.
  + conseq (_ : _ ==> Flag6.r{2}) => [/# | ].
    wp; call{2} guess_ll6; call{1} Rf_ll; inline *; auto => />.
  by sim : (={out, Gen.p, Gen.q, Gen.sd}) => /> /#.
have h2 : Pr[GameF6.main() @ &m : Flag6.r] = Pr[T6.main() @ &m : res].
- byequiv => //; proc; inline Setup0O.run.
  call{1} guess_ll6; inline CountP(IP).init Count(IP).init; wp.
  call{1} rw_get_ll.
  call (_ : ={R.RO.m}); 1: by sim.
  call{1} rs_get_ll.
  by conseq (_ : _ ==> ={Gen.p, Gen.e, R.RO.m}) => //; sim.
have h3 : Pr[GameF6.main() @ &m : E res Gen.p Gen.q Gen.sd] =
          Pr[GameP(Setup0O, A).main() @ &m : E res Gen.p Gen.q Gen.sd].
- by byequiv => //; proc; sim : (={out, Gen.p, Gen.q, Gen.sd}) => /> /#.
have h4 : Pr[GameF6.main() @ &m : E res Gen.p Gen.q Gen.sd \/ Flag6.r] <=
          Pr[GameF6.main() @ &m : E res Gen.p Gen.q Gen.sd] + Pr[GameF6.main() @ &m : Flag6.r].
- by rewrite Pr[mu_or]; smt(mu_bounded).
smt(T6_pr).
qed.


(* Lemma W3O for any event of the output and the secrets. *)
local module DX (O : OraclesP) = {
  var out : seed * (pw * pp)
  var p : pw
  var q : pp
  var sd : seed
  proc run(y : state, om : data, p0 : pw, q0 : pp, e : state, sd0 : seed) : bool = {
    CountP(O).init();
    out <@ A(CountP(O)).guess(y, om);
    p <- p0; q <- q0; sd <- sd0;
    return true;
  }
}.

local lemma gen6 (E : seed * (pw * pp) -> pw -> pp -> seed -> bool) &m :
  Pr[GameP(Setup0O, A).main() @ &m : E res Gen.p Gen.q Gen.sd] =
  Pr[GameP(Setup1O, A).main() @ &m : E res Gen.p Gen.q Gen.sd].
proof.
have -> : Pr[GameP(Setup0O, A).main() @ &m : E res Gen.p Gen.q Gen.sd] =
          Pr[GenGame(Setup0O, DX).main() @ &m : E DX.out DX.p DX.q DX.sd].
- byequiv => //; proc; inline DX(IP).run; wp.
  call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct, CountP.cw}); 1..6: by sim.
  inline CountP(IP).init Count(IP).init; wp.
  by call (_ : true ==> ={res, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); [sim | auto].
have -> : Pr[GameP(Setup1O, A).main() @ &m : E res Gen.p Gen.q Gen.sd] =
          Pr[GenGame(Setup1O, DX).main() @ &m : E DX.out DX.p DX.q DX.sd].
- byequiv => //; proc; inline DX(IP).run; wp.
  call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct, CountP.cw}); 1..6: by sim.
  inline CountP(IP).init Count(IP).init; wp.
  by call (_ : true ==> ={res, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); [sim | auto].
by byequiv (W3O DX) => // /#.
qed.

lemma W6_seed &m : 0 <= kA =>
  Pr[GamePR(Setup0O, A, Rf).main() @ &m : res.`1 = Gen.sd] <=
    top2 (kA %/ 12) kS + epsW6 kA kS qB qH qW + inv (2%r ^ 512).
proof.
move=> hkA; have [hqB [hqH [hkS hqW]]] := ge0_budgets6 &m.
have h0 := refusal6 (fun (out : seed * (pw * pp)) (_ : pw) (_ : pp) (sd : seed) => out.`1 = sd) &m.
have h1 := gen6 (fun (out : seed * (pw * pp)) (_ : pw) (_ : pp) (sd : seed) => out.`1 = sd) &m.
have h2 := theorem5O_seed kA qB qH kS qT qW A A_bounded A_ll &m hkA hqB hqH hkS hqW.
by move: h0 h1 h2; rewrite /epsW6 /=; smt().
qed.

lemma W6_pair &m : 0 <= kA =>
  Pr[GamePR(Setup0O, A, Rf).main() @ &m : res.`2 = (Gen.p, Gen.q)] <=
    minr (top2 (kA %/ 12 + 1) (kS + 1)) (top2 (kA %/ 12) kS + p1 * s1) + epsW6 kA kS qB qH qW.
proof.
move=> hkA; have [hqB [hqH [hkS hqW]]] := ge0_budgets6 &m.
have h0 := refusal6 (fun (out : seed * (pw * pp)) (p : pw) (q : pp) (_ : seed) => out.`2 = (p, q)) &m.
have h1 := gen6 (fun (out : seed * (pw * pp)) (p : pw) (q : pp) (_ : seed) => out.`2 = (p, q)) &m.
have h2 := theorem5O_pair kA qB qH kS qT qW A A_bounded A_ll &m hkA hqB hqH hkS hqW.
by move: h0 h1 h2; rewrite /epsW6 /=; smt().
qed.
end section W6.

(* Corollaries W5 and W6 for the phrase: the wrapped adversary records its guess (e, q) and asks it of
   S. A correct guess is then a query of S at (e*, Q), which is Bad in Θ2, so the bound has no term for
   guessing seed*. *)
module AW5 (A : AdvP5) (O : OraclesP) = {
  var g : state * pp
  proc guess(y : state, om : data) : seed * (pw * pp) = {
    var sd;
    g <@ A(O).guess(y, om);
    sd <@ O.s(g.`1, g.`2);
    return (sd, (witness, witness));
  }
}.


section W5.
declare op kA : int.
declare op qB : int.
declare op qH : int.
declare op kS : int.
declare op qT : int.
declare op qW : int.
declare module A <: AdvP5 {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO,
                           -RW.RO, -Gen, -Trials, -Count,
                           -CountB, -CountP, -Mon, -Bwd, -WithP, -AP, -AW5}.
declare module Rf <: AFTER5 {-Gen}.
declare axiom Rf_ll : islossless Rf.run.
declare axiom A_bounded (O <: OraclesP {-Count, -CountP, -A}) :
  hoare [A(CountP(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
    CountP.cs <= kS /\ CountP.ct <= qT /\ CountP.cw <= qW].
declare axiom A_ll (O <: OraclesP {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless A(O).guess.

local lemma AW5_bounded (O <: OraclesP {-Count, -CountP, -A, -AW5}) :
  hoare [AW5(A, CountP(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
    CountP.cs <= kS + 1 /\ CountP.ct <= qT /\ CountP.cw <= qW].
proof. by proc; inline CountP(O).s; wp; call (_ : true); wp; call (A_bounded O); auto => /> /#. qed.

local lemma AW5_ll (O <: OraclesP {-A, -AW5}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless AW5(A, O).guess.
proof. by move=> ha hb hh hs ht hw; proc; call hs; call (A_ll O ha hb hh hs ht hw); auto. qed.


local lemma guess_ll5 : islossless AW5(A, CountP(IP)).guess.
proof. by apply (AW5_ll (CountP(IP))); proc; inline *; auto => />; smt(dans_ll dseed_ll dct_ll ddata_ll). qed.

(* The refused creation: Y = E. *)
local module GF5 (S : SETUPP) = {
  var r : bool
  proc main() : seed * (pw * pp) = {
    var y, om, out;
    (y, om) <@ S.run();
    r <- y = Gen.e;
    CountP(IP).init();
    out <@ AW5(A, CountP(IP)).guess(y, om);
    return out;
  }
}.

local lemma ref5O &m :
  Pr[Game5(Setup0O, A, Rf).main() @ &m : res = (Gen.e, Gen.q)] <=
  Pr[GameP(Setup0O, AW5(A)).main() @ &m : AW5.g = (Gen.e, Gen.q)] + Pr[Setup0O.run() @ &m : res.`1 = Gen.e].
proof.
have h1 : Pr[Game5(Setup0O, A, Rf).main() @ &m : res = (Gen.e, Gen.q)] <=
          Pr[GF5(Setup0O).main() @ &m : AW5.g = (Gen.e, Gen.q) \/ GF5.r].
- byequiv => //; proc.
  seq 1 1 : (={glob A, y, om, Gen.p, Gen.q, Gen.e, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); 1: by sim.
  if{1}.
  + conseq (_ : _ ==> GF5.r{2}) => [/# | ].
    wp; call{2} guess_ll5; call{1} Rf_ll; inline *; auto => />.
  inline AW5(A, CountP(IP)).guess CountP(IP).s IP.s RS.RO.get; wp; rnd{2}; wp.
  call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct,
              CountP.cw}); 1..6: by sim.
  by inline *; auto => />; smt(dseed_ll).
have h2 : Pr[GF5(Setup0O).main() @ &m : AW5.g = (Gen.e, Gen.q)] = Pr[GameP(Setup0O, AW5(A)).main() @ &m : AW5.g = (Gen.e, Gen.q)].
- by byequiv => //; proc; sim.
have h3 : Pr[GF5(Setup0O).main() @ &m : GF5.r] = Pr[Setup0O.run() @ &m : res.`1 = Gen.e].
- byequiv => //; proc*; inline GF5(Setup0O).main; wp; call{1} guess_ll5.
  by inline CountP(IP).init Count(IP).init; wp; call (_ : true ==> ={res, Gen.e}); [sim | auto].
have h4 : Pr[GF5(Setup0O).main() @ &m : AW5.g = (Gen.e, Gen.q) \/ GF5.r] <=
          Pr[GF5(Setup0O).main() @ &m : AW5.g = (Gen.e, Gen.q)] + Pr[GF5(Setup0O).main() @ &m : GF5.r].
- by rewrite Pr[mu_or]; smt(mu_bounded).
smt().
qed.

(* Lemmas W2 and W3 for the guess. Lemma W2 concerns the adversary's view, and the wrapper's query of
   S at the guess follows that view, so the judge runs A alone, with A's own budget kS. *)
local module J5 (O : OraclesP) = {
  proc run(y : state, om : data) : unit = { AW5.g <@ A(O).guess(y, om); }
  proc judge(p : pw, q : pp, e : state, sd : seed) : bool = { return AW5.g = (e, q); }
}.

local module D5 (O : OraclesP) = {
  proc run(y : state, om : data, p : pw, q : pp, e : state, sd : seed) : bool = {
    var out;
    CountP(O).init();
    out <@ AW5(A, CountP(O)).guess(y, om);
    return AW5.g = (e, q);
  }
}.

local equiv aw5_eq : AW5(A, CountP(IP)).guess ~ AW5(A, CountP(IP)).guess :
  ={arg, glob A, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct, CountP.cw}
  ==> ={AW5.g}.
proof. by sim. qed.

local lemma gen5 &m : 0 <= kS => 0 <= qT =>
  Pr[GameP(Setup0P(Seq), AW5(A)).main() @ &m : AW5.g = (Gen.e, Gen.q)] <=
  Pr[GameP(Setup1P, AW5(A)).main() @ &m : AW5.g = (Gen.e, Gen.q)] + deltacut kS qT.
proof.
move=> hkS hqT; have := theta01 kS qT J5 _ _ &m hkS hqT.
- by move=> O; proc; call (A_bounded O).
- move=> O; split; 2: by move=> *; proc; auto.
  by move=> ha hb hh hs ht hw; proc; call (A_ll O ha hb hh hs ht hw).
have -> : Pr[Judged(Setup0P(Seq), J5).main() @ &m : res] =
          Pr[GameP(Setup0P(Seq), AW5(A)).main() @ &m : AW5.g = (Gen.e, Gen.q)].
- byequiv => //; proc; inline J5(CountP(IP)).run J5(CountP(IP)).judge AW5(A, CountP(IP)).guess; wp.
  call{2} (_ : true ==> true); 1: by proc; inline *; auto => />; smt(dseed_ll).
  wp; call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct,
                CountP.cw}); 1..6: by sim.
  inline CountP(IP).init Count(IP).init; wp.
  by call (_ : true ==> ={res, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); [sim | auto].
have -> : Pr[Judged(Setup1P, J5).main() @ &m : res] =
          Pr[GameP(Setup1P, AW5(A)).main() @ &m : AW5.g = (Gen.e, Gen.q)].
- byequiv => //; proc; inline J5(CountP(IP)).run J5(CountP(IP)).judge AW5(A, CountP(IP)).guess; wp.
  call{2} (_ : true ==> true); 1: by proc; inline *; auto => />; smt(dseed_ll).
  wp; call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct,
                CountP.cw}); 1..6: by sim.
  inline CountP(IP).init Count(IP).init; wp.
  by call (_ : true ==> ={res, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); [sim | auto].
smt().
qed.

local lemma gen5O &m :
  Pr[GameP(Setup0O, AW5(A)).main() @ &m : AW5.g = (Gen.e, Gen.q)] =
  Pr[GameP(Setup1O, AW5(A)).main() @ &m : AW5.g = (Gen.e, Gen.q)].
proof.
have -> : Pr[GameP(Setup0O, AW5(A)).main() @ &m : AW5.g = (Gen.e, Gen.q)] = Pr[GenGame(Setup0O, D5).main() @ &m : res].
- byequiv => //; proc; inline D5(IP).run; wp; call aw5_eq.
  inline CountP(IP).init Count(IP).init; wp.
  by call (_ : true ==> ={res, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); [sim | auto].
have -> : Pr[GameP(Setup1O, AW5(A)).main() @ &m : AW5.g = (Gen.e, Gen.q)] = Pr[GenGame(Setup1O, D5).main() @ &m : res].
- byequiv => //; proc; inline D5(IP).run; wp; call aw5_eq.
  inline CountP(IP).init Count(IP).init; wp.
  by call (_ : true ==> ={res, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); [sim | auto].
by byequiv (W3O D5).
qed.

(* In Θ2 the recorded guess is among the queries of S. *)
local lemma aw5_sq : hoare [Theta2L(AW5(A)).main : true ==> AW5.g \in WithP.sq].
proof.
proc; inline ChainGame(AP(AW5(A))).main AP(AW5(A), CountB(Mon)).run AW5(A, WithP(CountB(Mon))).guess
  WithP(CountB(Mon)).s RS.RO.get.
auto; call (_ : true ==> true); 1: by proc; while true; [inline *; auto | auto].
auto; call (_ : true); 1..6: by proc; inline *; auto.
by inline *; auto => />; smt(mem_rcons).
qed.

local lemma logged (X : state -> pp -> seed -> seed list -> seed list -> bool) &m :
  Pr[Theta2L(AW5(A)).main() @ &m :
       AW5.g = (res, Gen.q) \/ (res, Gen.q) \in WithP.sq \/ X res Gen.q Gen.sd WithP.tq WithP.wq] <=
  Pr[Theta2L(AW5(A)).main() @ &m : (res, Gen.q) \in WithP.sq \/ X res Gen.q Gen.sd WithP.tq WithP.wq].
proof.
have h0 : Pr[Theta2L(AW5(A)).main() @ &m : !(AW5.g \in WithP.sq)] = 0%r.
- by byphoare => //; hoare; conseq aw5_sq.
rewrite Pr[mu_split (AW5.g \in WithP.sq)].
have h1 : Pr[Theta2L(AW5(A)).main() @ &m :
               (AW5.g = (res, Gen.q) \/ (res, Gen.q) \in WithP.sq \/ X res Gen.q Gen.sd WithP.tq WithP.wq) /\
               AW5.g \in WithP.sq] <=
          Pr[Theta2L(AW5(A)).main() @ &m : (res, Gen.q) \in WithP.sq \/ X res Gen.q Gen.sd WithP.tq WithP.wq].
- by rewrite Pr[mu_sub] => /#.
have h2 : Pr[Theta2L(AW5(A)).main() @ &m :
               (AW5.g = (res, Gen.q) \/ (res, Gen.q) \in WithP.sq \/ X res Gen.q Gen.sd WithP.tq WithP.wq) /\
               !(AW5.g \in WithP.sq)] <= Pr[Theta2L(AW5(A)).main() @ &m : !(AW5.g \in WithP.sq)].
- by rewrite Pr[mu_sub].
smt().
qed.

(* Corollary W5 for the rule cut off after ntr trials and without refusal; W5R below states it for
   every covered rule with refusal. *)
lemma W5_cut &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qT => 0 <= qW =>
  Pr[GameP(Setup0P(Seq), AW5(A)).main() @ &m : AW5.g = (Gen.e, Gen.q)] <=
    top2 (kA %/ 12) (kS + 1) + epsC kA (kS + 1) qB qH qT qW + deltacut kS qT.
proof.
move=> hkA hqB hqH hkS hqT hqW.
have h2 := gen5 &m hkS hqT.
have h3 := upto_bad_theta kA qB qH (kS + 1) qT qW (AW5(A)) AW5_bounded AW5_ll
             (fun (g : glob AW5(A)) _ _ (q : pp) (e : state) _ => g.`2 = (e, q)) &m.
have h4 := logged (fun _ _ (sd : seed) (tq wq : seed list) => sd \in tq \/ sd \in wq) &m.
have h5 := theta_bad kA qB qH (kS + 1) qT qW (AW5(A)) AW5_bounded AW5_ll &m hkA hqB hqH _ hqT hqW.
- smt().
move: h2 h3 h4 h5; rewrite /epsC /=; smt().
qed.

(* The budgets are nonnegative: the counters start at 0 and the adversary terminates. *)
local module GB5 = {
  proc main() : unit = {
    var out;
    CountP(IP).init();
    out <@ A(CountP(IP)).guess(witness, witness);
  }
}.

local lemma ge0_budgets5 &m : 0 <= qB /\ 0 <= qH /\ 0 <= kS /\ 0 <= qW.
proof.
case: (0 <= qB /\ 0 <= qH /\ 0 <= kS /\ 0 <= qW) => // hneg.
have h1 : Pr[GB5.main() @ &m : true] = 1%r.
- byphoare => //; proc; call (A_ll (CountP(IP))); 1..6: by proc; inline *; auto => />; smt(dans_ll dseed_ll dct_ll ddata_ll).
  by inline *; auto.
have h2 : Pr[GB5.main() @ &m : !(0 <= qB /\ 0 <= qH /\ 0 <= kS /\ 0 <= qW)] = 0%r.
- byphoare => //; hoare; proc.
  call (_ : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
            0 <= qB /\ 0 <= qH /\ 0 <= kS /\ 0 <= qW).
  + conseq (A_bounded IP) (_ : 0 <= Count.cb /\ 0 <= Count.ch /\ 0 <= CountP.cs /\ 0 <= CountP.cw ==>
                               0 <= Count.cb /\ 0 <= Count.ch /\ 0 <= CountP.cs /\ 0 <= CountP.cw) => [/# | /# |].
    by proc (0 <= Count.cb /\ 0 <= Count.ch /\ 0 <= CountP.cs /\ 0 <= CountP.cw) => //; proc; inline *; auto => /#.
  by inline *; auto.
have : Pr[GB5.main() @ &m : !(0 <= qB /\ 0 <= qH /\ 0 <= kS /\ 0 <= qW)] = Pr[GB5.main() @ &m : true].
- by rewrite Pr[mu_eq] => // /#.
smt().
qed.

(* Corollary W6 for the phrase. *)
lemma W6_phrase &m : 0 <= kA =>
  Pr[Game5(Setup0O, A, Rf).main() @ &m : res = (Gen.e, Gen.q)] <=
    top2 (kA %/ 12) (kS + 1) + epsW6 kA (kS + 1) qB qH qW.
proof.
move=> hkA; have [hqB [hqH [hkS hqW]]] := ge0_budgets5 &m.
have h0 := ref5O &m.
have h1 := setup_refusedO &m.
have h2 := gen5O &m.
have h3 := upto_bad_thetaO kA qB qH (kS + 1) qT qW (AW5(A)) AW5_bounded AW5_ll
             (fun (g : glob AW5(A)) _ _ (q : pp) (e : state) _ => g.`2 = (e, q)) &m.
have h4 := logged (fun _ _ (sd : seed) _ (wq : seed list) => sd \in wq) &m.
have h5 := theta_badO kA qB qH (kS + 1) qT qW (AW5(A)) AW5_bounded AW5_ll &m hkA hqB hqH _ hqW.
- smt().
move: h0 h1 h2 h3 h4 h5; rewrite /epsW6 /=; smt().
qed.
end section W5.

(* ---- Corollary W5 for every covered rule ----------------------------------------------------- *)
section W5R.
declare op kA : int.
declare op qB : int.
declare op qH : int.
declare op kS : int.
declare op qT : int.
declare op qW : int.
declare module Rl <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                           -Trials, -Gen, -Count, -CountP}.
declare axiom Rl_pass (T <: TRIALS {-Rl, -Trials}) :
  hoare [Rl(Rec(T)).select : Trials.outs = [] ==>
           0 <= res < size Trials.outs /\ nth false Trials.outs res].
declare axiom Rl_ll (T <: TRIALS {-Rl}) (P : glob T -> bool) (b : real) :
  0%r < b => phoare [T.trial : P (glob T) ==> P (glob T) /\ res] = b =>
  phoare [T.trial : P (glob T) ==> P (glob T)] = 1%r =>
  phoare [Rl(T).select : P (glob T) ==> true] = 1%r.
declare module A <: AdvP5 {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO,
                           -RW.RO, -Gen, -Trials, -Count, -CountB, -CountP, -Mon, -Bwd, -WithP, -AP, -AW5, -Rl}.
declare module Rf <: AFTER5 {-Gen}.
declare axiom Rf_ll : islossless Rf.run.
declare axiom A_bounded (O <: OraclesP {-Count, -CountP, -A}) :
  hoare [A(CountP(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
    CountP.cs <= kS /\ CountP.ct <= qT /\ CountP.cw <= qW].
declare axiom A_ll (O <: OraclesP {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless A(O).guess.

(* As in Selection.ec: the run without the refused branch, and the refusal, as distinguishers. *)
local module DE5 (O : OraclesP) = {
  var r : bool
  proc run(y : state, om : data, p : pw, q : pp, e : state, sd : seed) : bool = {
    var out, b;
    r <- y = e;
    b <- false;
    if (!r) { CountP(O).init(); out <@ A(CountP(O)).guess(y, om); b <- out = (e, q); }
    return b;
  }
}.

local module DR5 (O : OraclesP) = {
  proc run(y : state, om : data, p : pw, q : pp, e : state, sd : seed) : bool = { return y = e; }
}.

local lemma A_ll_IP : islossless A(CountP(IP)).guess.
proof. by apply (A_ll (CountP(IP))); proc; inline *; auto => />; smt(dans_ll dseed_ll dct_ll ddata_ll). qed.

local lemma DE5_ll (O <: OraclesP {-DE5}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless DE5(O).run.
proof.
move=> ha hb hh hs ht hw; proc; sp; if => //; wp.
call (A_ll (CountP(O)) _ _ _ _ _ _); 1..6: by proc; inline *; wp; (call ha || call hb || call hh ||
  call hs || call ht || call hw); auto.
by inline *; auto.
qed.

local lemma DR5_ll (O <: OraclesP {-DR5}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless DR5(O).run.
proof. by move=> *; proc; auto. qed.

local lemma split5 &m : Pr[Game5(Setup0P(Rl), A, Rf).main() @ &m : res = (Gen.e, Gen.q)] <=
  Pr[GenGame(Setup0P(Rl), DE5).main() @ &m : res] + Pr[GenGame(Setup0P(Rl), DR5).main() @ &m : res].
proof.
have h1 : Pr[Game5(Setup0P(Rl), A, Rf).main() @ &m : res = (Gen.e, Gen.q)] <=
          Pr[GenGame(Setup0P(Rl), DE5).main() @ &m : res \/ DE5.r].
- byequiv => //; proc; inline DE5(IP).run.
  seq 1 1 : (={y, om, glob A, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); 1: by sim => /#.
  sp; if{1}.
  + rcondf{2} 1; 1: by auto => /#.
    by wp; call{1} Rf_ll; auto => /#.
  rcondt{2} 1; 1: by auto => /#.
  wp; call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct,
                CountP.cw}); 1..6: by sim.
  by inline *; auto => /> /#.
have h2 : Pr[GenGame(Setup0P(Rl), DE5).main() @ &m : DE5.r] = Pr[GenGame(Setup0P(Rl), DR5).main() @ &m : res].
- byequiv => //; proc; inline DE5(IP).run DR5(IP).run.
  seq 1 1 : (={y, Gen.e}); 1: by sim => /#.
  sp; if{1}; last by auto.
  by wp; call{1} A_ll_IP; inline *; auto.
have h3 : Pr[GenGame(Setup0P(Rl), DE5).main() @ &m : res \/ DE5.r] <=
          Pr[GenGame(Setup0P(Rl), DE5).main() @ &m : res] + Pr[GenGame(Setup0P(Rl), DE5).main() @ &m : DE5.r].
- by rewrite Pr[mu_or]; smt(mu_bounded).
smt().
qed.

local lemma cut5 &m : Pr[GenGame(Setup0P(Seq), DE5).main() @ &m : res] <=
  Pr[GameP(Setup0P(Seq), AW5(A)).main() @ &m : AW5.g = (Gen.e, Gen.q)].
proof.
byequiv => //; proc; inline DE5(IP).run AW5(A, CountP(IP)).guess.
seq 1 1 : (={y, om, glob A, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); 1: by sim => /#.
sp; if{1}.
- wp; call{2} (_ : true ==> true); 1: by proc; inline *; auto => />; smt(dseed_ll).
  wp; call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct,
                CountP.cw}); 1..6: by sim.
  by inline *; auto => /> /#.
wp; call{2} (_ : true ==> true); 1: by proc; inline *; auto => />; smt(dseed_ll).
by wp; call{2} A_ll_IP; inline *; auto.
qed.

local lemma ref5 &m : Pr[GenGame(Setup0P(Seq), DR5).main() @ &m : res] <= inv (2%r ^ 256).
proof.
have <- : Pr[Setup0P(Seq).run() @ &m : res.`1 = Gen.e] = Pr[GenGame(Setup0P(Seq), DR5).main() @ &m : res].
- byequiv => //; proc*; inline GenGame(Setup0P(Seq), DR5).main DR5(IP).run; wp.
  by call (_ : true ==> ={res, Gen.e}); [sim | auto].
exact setup_refused.
qed.

(* Corollary W5: epsW with kS + 1 in place of kS, except in deltagen (see J5). *)
lemma W5 &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qT => 0 <= qW =>
  Pr[Game5(Setup0P(Rl), A, Rf).main() @ &m : res = (Gen.e, Gen.q)] <=
    top2 (kA %/ 12) (kS + 1) + epsC kA (kS + 1) qB qH qT qW + deltagen kS qT + inv (2%r ^ 256).
proof.
move=> hkA hqB hqH hkS hqT hqW.
have h1 := split5 &m.
have s1 := selection_bound Rl DE5 Rl_pass Rl_ll DE5_ll &m.
have s2 := selection_bound Rl DR5 Rl_pass Rl_ll DR5_ll &m.
have h2 := cut5 &m.
have h3 := ref5 &m.
have h4 := W5_cut kA qB qH kS qT qW A Rf Rf_ll A_bounded A_ll &m hkA hqB hqH hkS hqT hqW.
have h5 := deltacut_le kS qT hkS hqT.
by move: h1 h2 h3 h4 h5; smt().
qed.
end section W5R.
