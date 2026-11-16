(* Deniability: the honest and prepared experiments, Theorems 1 and 2 and the simulation of a
   prepared disclosure. Lemmas 1-3 are in Model.ec. The theory is abstract in the half width, so it
   covers suite 3 (256-bit states) and suite 4 (ENT-bit states); salts stay 128 bits and keys 256 bits
   in both. *)
require import AllCore List Distr DBool DProd Dexcepted FMap StdBigop.
require (*--*) Model PROM StdOrder FSet Mu_mem.

abstract theory Denial.

clone include Model.Feistel.

op W : int.                                 (* state width: 256 in suite 3, ENT in suite 4 *)
axiom dstate1 (x : state) : mu1 dstate x = inv (2%r ^ W).
axiom dkey1 (k : key) : mu1 dkey k = inv (2%r ^ 256).

(* ---- The experiments ---------------------------------------------------------------------- *)
(* The real source: ENT-bit entropy packed with an r-bit verifier from G, as in A.1; for a full-width
   source the packing is the identity. *)
type ent, ver, rest.
op ENT : int.
op dent : ent distr.
axiom dent_ll : is_lossless dent.
axiom dent1 (e : ent) : mu1 dent e = inv (2%r ^ ENT).
op dver : ver distr.
axiom dver_ll : is_lossless dver.
op drest : rest distr.
axiom drest_ll : is_lossless drest.
op pack : ent -> ver -> state.

clone PROM.FullRO as RG with
  type in_t <- ent, type out_t <- ver * rest, op dout <- (fun _ => dver `*` drest),
  type d_in_t <- unit, type d_out_t <- bool.

(* Phrases and records. A wallet is identified by its phrase, length included. [ph] reads a state at
   the full width; [phE] is the phrase of the real source at its own length. *)
type phrase, record.
op ph  : state -> phrase.
op phE : ent -> phrase.
axiom ph_inj : injective ph.
axiom phE_inj : injective phE.
op empty : record.

(* The usage scenario U: a record for a phrase, independent of everything else. The real wallet is
   used in any way: its record may depend on the source E, the password, the state X, the container,
   the decoy password, the disclosed state and the decoy's record. *)
op dU : phrase -> record distr.
axiom dU_ll (f : phrase) : is_lossless (dU f).
op dReal : ent -> pw -> state -> state -> pw -> state -> record -> record distr.
axiom dReal_ll e p x y q xd rc : is_lossless (dReal e p x y q xd rc).

module type OraclesD = {
  proc a(p : pw, s : salt) : key
  proc b(i : ridx, r : half) : salt
  proc h(k : key, i : ridx, r : half) : half
  proc g(e : ent) : ver * rest
  proc look(f : phrase) : record
}.

(* The record oracle: the disclosed phrase returns its record; in the prepared experiment the real
   phrase, when it differs from the disclosed one, returns the real record; every other phrase
   returns an empty record. *)
module Look = {
  var disc : phrase
  var drec : record
  var real : phrase option
  var rrec : record
  proc look(f : phrase) : record = {
    var out;
    out <- empty;
    if (f = disc) { out <- drec; } else { if (Some f = real) out <- rrec; }
    return out;
  }
}.

(* Counts the distinct passwords of Argon2id queries, the HMAC queries and the lookups. *)
module CountD (O : OraclesD) = {
  var pws : pw list
  var cq, cl : int
  proc init() = { pws <- []; cq <- 0; cl <- 0; }
  proc a(p : pw, s : salt) = { var k; pws <- undup (rcons pws p); k <@ O.a(p, s); return k; }
  proc b = O.b
  proc h(k : key, i : ridx, r : half) = { var m; cq <- cq + 1; m <@ O.h(k, i, r); return m; }
  proc g = O.g
  proc look(f : phrase) = { var c; cl <- cl + 1; c <@ O.look(f); return c; }
}.

module IdealD : OraclesD = {
  proc a = Ideal.a
  proc b = Ideal.b
  proc h = Ideal.h
  proc g(e : ent) = { var v; v <@ RG.RO.get(e); return v; }
  proc look = Look.look
}.

(* The adversary receives the container, the disclosed password, the disclosed state and its
   record, and outputs its guess of the experiment ("prepared" is true). *)
module type Dist (O : OraclesD) = {
  proc guess(y : state, q : pw, x : state, rc : record) : bool
}.

(* What happens after a refused creation or a decoy equal to the password; every continuation is
   allowed, including the redraw of the text and its failure symbol. *)
module type AFTERD = { proc run() : bool }.

module Honest (D : Dist) (Rh : AFTERD) = {
  proc main() : bool = {
    var p, x, y, rc, b;
    R.RO.init(); RG.RO.init();
    p <$ dP;
    x <$ dstate;
    y <@ Net(Ideal).enc(p, x);
    if (y = x) {
      b <@ Rh.run();
    } else {
      rc <$ dU (ph x);
      Look.disc <- ph x; Look.drec <- rc; Look.real <- None;
      CountD(IdealD).init();
      b <@ D(CountD(IdealD)).guess(y, p, x, rc);
    }
    return b;
  }
}.

module Prepared (D : Dist) (Rp : AFTERD) = {
  proc main() : bool = {
    var p, e, v, x, y, q, xd, rc, rr, b;
    R.RO.init(); RG.RO.init();
    p <$ dP;
    e <$ dent;
    v <@ RG.RO.get(e);
    x <- pack e v.`1;
    y <@ Net(Ideal).enc(p, x);
    q <$ dP;
    if (y = x \/ q = p) {
      b <@ Rp.run();
    } else {
      xd <@ Net(Ideal).dec(q, y);
      rc <$ dU (ph xd);
      rr <$ dReal e p x y q xd rc;
      Look.disc <- ph xd; Look.drec <- rc; Look.real <- Some (phE e); Look.rrec <- rr;
      CountD(IdealD).init();
      b <@ D(CountD(IdealD)).guess(y, q, xd, rc);
    }
    return b;
  }
}.

(* ---- Theorem 1 ------------------------------------------------------------------------------ *)
(* A full-width source, no lookups, refusal and redraw ignored: the oracles, the container, the
   disclosed password, the disclosed state and its record have the same joint distribution. *)
module type Dist1 (O : ABH) = {
  proc guess(y : state, q : pw, x : state, rc : record) : bool
}.

module Honest1 (D : Dist1) = {
  proc main() : bool = {
    var p, x, y, rc, b;
    R.RO.init();
    p <$ dP;
    x <$ dstate;
    y <@ Net(Ideal).enc(p, x);
    rc <$ dU (ph x);
    b <@ D(Ideal).guess(y, p, x, rc);
    return b;
  }
}.

module Prepared1 (D : Dist1) = {
  proc main() : bool = {
    var p, x, y, q, xd, rc, b;
    R.RO.init();
    p <$ dP;
    x <$ dstate;
    y <@ Net(Ideal).enc(p, x);
    q <$ dP;
    xd <@ Net(Ideal).dec(q, y);
    rc <$ dU (ph xd);
    b <@ D(Ideal).guess(y, q, xd, rc);
    return b;
  }
}.

(* The two experiments as programs on the oracle of A, B, H; with RE.FunRO and without its
   initialization, they run on the fixed functions RE.FunRO.f of the initial memory. *)
module HonestG (D : Dist1) (G : R.RO) = {
  proc distinguish() : bool = {
    var p, x, y, rc, b;
    p <$ dP;
    x <$ dstate;
    y <@ Net(Orc(G)).enc(p, x);
    rc <$ dU (ph x);
    b <@ D(Orc(G)).guess(y, p, x, rc);
    return b;
  }
}.

module PreparedG (D : Dist1) (G : R.RO) = {
  proc distinguish() : bool = {
    var p, x, y, q, xd, rc, b;
    p <$ dP;
    x <$ dstate;
    y <@ Net(Orc(G)).enc(p, x);
    q <$ dP;
    xd <@ Net(Orc(G)).dec(q, y);
    rc <$ dU (ph xd);
    b <@ D(Orc(G)).guess(y, q, xd, rc);
    return b;
  }
}.

section Theorem1.
declare module D <: Dist1 {-R.RO, -R.FRO, -RE.FunRO}.

(* For fixed functions: (q, Inv_q(Y)) for Y = Perm_p(X) is (q, X') for a uniform X'. *)
local equiv core_f : PreparedG(D, RE.FunRO).distinguish ~ HonestG(D, RE.FunRO).distinguish :
  ={glob D, RE.FunRO.f} ==> ={res}.
proof.
proc.
swap{1} 4 -3.
seq 3 2 : (={glob D, RE.FunRO.f} /\ q{1} = p{2} /\
           x{2} = invperm RE.FunRO.f{1} q{1} (perm RE.FunRO.f{1} p{1} x{1})).
- rnd (fun xl => invperm RE.FunRO.f{1} q{1} (perm RE.FunRO.f{1} p{1} xl))
      (fun xr => invperm RE.FunRO.f{1} p{1} (perm RE.FunRO.f{1} q{1} xr)).
  rnd{1}; rnd; auto => />; smt(permK invpermK dstate_funi dstate_full dP_ll).
seq 1 1 : (={glob D, RE.FunRO.f, y} /\ q{1} = p{2} /\ x{2} = invperm RE.FunRO.f{1} q{1} y{1}).
- exlim p{1}, x{1} => p1 x1; call{1} (enc_fun_ph p1 x1).
  exlim p{2}, x{2} => p2 x2; call{2} (enc_fun_ph p2 x2).
  by auto => />; smt(permK).
seq 1 0 : (={glob D, RE.FunRO.f, y} /\ q{1} = p{2} /\ xd{1} = x{2}).
- exlim q{1}, y{1} => q1 y1; call{1} (dec_fun_ph q1 y1).
  by auto.
wp; call (_ : ={RE.FunRO.f}); 1..3: by proc; inline *; auto.
by auto.
qed.

(* Theorem 1 for any fixed functions in place of the oracles (the text's "even for fixed functions"):
   the f of the initial memory. *)
lemma theorem1_fixed &m :
  Pr[PreparedG(D, RE.FunRO).distinguish() @ &m : res] = Pr[HonestG(D, RE.FunRO).distinguish() @ &m : res].
proof. by byequiv core_f. qed.

local equiv core : R.MainD(PreparedG(D), RE.FunRO).distinguish ~ R.MainD(HonestG(D), RE.FunRO).distinguish :
  ={glob D} ==> ={res}.
proof. by proc; call core_f; inline *; auto. qed.

(* Theorem 1. *)
lemma theorem1 &m : Pr[Prepared1(D).main() @ &m : res] = Pr[Honest1(D).main() @ &m : res].
proof.
have -> : Pr[Prepared1(D).main() @ &m : res] = Pr[R.MainD(PreparedG(D), R.RO).distinguish() @ &m : res].
- by byequiv => //; proc; inline *; sim.
have -> : Pr[Honest1(D).main() @ &m : res] = Pr[R.MainD(HonestG(D), R.RO).distinguish() @ &m : res].
- by byequiv => //; proc; inline *; sim.
have -> : Pr[R.MainD(PreparedG(D), R.RO).distinguish() @ &m : res] = Pr[R.MainD(PreparedG(D), RE.FunRO).distinguish() @ &m : res].
- by byequiv (RO_FunRO (PreparedG(D))).
have -> : Pr[R.MainD(HonestG(D), R.RO).distinguish() @ &m : res] = Pr[R.MainD(HonestG(D), RE.FunRO).distinguish() @ &m : res].
- by byequiv (RO_FunRO (HonestG(D))).
by byequiv core.
qed.
end section Theorem1.

(* ---- Theorem 2 ------------------------------------------------------------------------------ *)
(* The private copies of A and H for the password P and the keys K_i in Game 2 of the proof. *)
clone PROM.FullRO as RP with
  type in_t <- point, type out_t <- ans, op dout <- (fun _ => dans),
  type d_in_t <- unit, type d_out_t <- bool.

(* The private answers' keys, one per round, drawn by an oracle of their own. *)
clone PROM.FullRO as RK with
  type in_t <- ridx, type out_t <- ans, op dout <- (fun _ => dans),
  type d_in_t <- unit, type d_out_t <- bool.
clone RK.FinEager as RKE with op FinFrom.enum <- RidxT.enum
proof FinFrom.enum_spec by exact RidxT.enum_spec.

(* The private table holds Argon2id points of [p0] only, and HMAC points whose key is one of [mk]. *)
op privP (p0 : pw) (mp : (point, ans) fmap) (mk : (ridx, ans) fmap) =
  (forall w s, PA (w, s) \in mp => w = p0) /\
  (forall k j r, PH (k, j, r) \in mp => exists c, c \in mk /\ key_of (oget mk.[c]) = k).
op hitK (mk : (ridx, ans) fmap) (hk : key list) = exists c, c \in mk /\ key_of (oget mk.[c]) \in hk.

lemma rd_val (c : ridx) : rd (Ridx.val c) = c.
proof. by rewrite /rd Ridx.valKd. qed.

(* Game 1's table is the shared table of Game 2 joined with the private one; a query adds its point
   to the shared table if the private one misses it, and to the private one otherwise. *)
lemma join_set_sh ['a 'b] (m1 m2 : ('a, 'b) fmap) x v : x \notin m2 => (m1 + m2).[x <- v] = m1.[x <- v] + m2.
proof. by move=> hx; apply fmap_eqP => y; rewrite get_setE !joinE get_setE; case: (y = x) => // ->; rewrite hx. qed.

lemma join_set_pv ['a 'b] (m1 m2 : ('a, 'b) fmap) x v : (m1 + m2).[x <- v] = m1 + m2.[x <- v].
proof. by apply fmap_eqP => y; rewrite get_setE !joinE get_setE mem_set; case: (y = x). qed.

section Theorem2.
declare op k : int.
declare op q : int.
declare op l : int.
declare axiom ge0_k : 0 <= k.
declare axiom ge0_q : 0 <= q.
declare axiom ge0_l : 0 <= l.
declare module D <: Dist {-R.RO, -R.FRO, -RE.FunRO, -RG.RO, -RG.FRO, -RP.RO, -RK.RO, -RK.FRO,
                          -RKE.FunRO, -Look, -CountD}.
declare module Rh <: AFTERD.
declare module Rp <: AFTERD.
declare axiom Rh_ll : islossless Rh.run.
declare axiom Rp_ll : islossless Rp.run.

declare axiom D_bounded (O <: OraclesD {-CountD, -D}) :
  hoare [D(CountD(O)).guess : CountD.pws = [] /\ CountD.cq = 0 /\ CountD.cl = 0 ==>
                              size CountD.pws <= k /\ CountD.cq <= q /\ CountD.cl <= l].
declare axiom D_ll (O <: OraclesD {-D}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.g => islossless O.look =>
  islossless D(O).guess.

(* Game 1: the prepared experiment without refusal and redraw; [rf] records their event. *)
local module G1 = {
  var rf : bool
  proc main() : bool = {
    var p, e, v, x, y, q, xd, rc, rr, b;
    R.RO.init(); RG.RO.init();
    p <$ dP; e <$ dent; v <@ RG.RO.get(e); x <- pack e v.`1;
    y <@ Net(Ideal).enc(p, x);
    q <$ dP;
    rf <- y = x \/ q = p;
    xd <@ Net(Ideal).dec(q, y);
    rc <$ dU (ph xd); rr <$ dReal e p x y q xd rc;
    Look.disc <- ph xd; Look.drec <- rc; Look.real <- Some (phE e); Look.rrec <- rr;
    CountD(IdealD).init();
    b <@ D(CountD(IdealD)).guess(y, q, xd, rc);
    return b;
  }
}.

(* Game 3: the honest experiment without refusal; [rf] records its event. *)
local module G3 = {
  var rf : bool
  proc main() : bool = {
    var p, x, y, rc, b;
    R.RO.init(); RG.RO.init();
    p <$ dP; x <$ dstate;
    y <@ Net(Ideal).enc(p, x);
    rf <- y = x;
    rc <$ dU (ph x);
    Look.disc <- ph x; Look.drec <- rc; Look.real <- None;
    CountD(IdealD).init();
    b <@ D(CountD(IdealD)).guess(y, p, x, rc);
    return b;
  }
}.

local lemma IdealD_ll : islossless D(CountD(IdealD)).guess.
proof.
by apply (D_ll (CountD(IdealD))); proc; inline *; auto => />; smt(dans_ll dprod_ll dver_ll drest_ll).
qed.

local lemma ideal_ll : islossless Net(Ideal).enc /\ islossless Net(Ideal).dec.
proof. by apply (net_ll Ideal); proc; inline *; auto => />; exact dans_ll. qed.

(* Refusal and redraw happen only on [rf]. *)
local equiv e01 : Prepared(D, Rp).main ~ G1.main : ={glob D} ==> !G1.rf{2} => ={res}.
proof.
have [_ hd] := ideal_ll.
proc; seq 8 9 : (={glob D, p, e, x, y, q, R.RO.m, RG.RO.m} /\ G1.rf{2} = (y = x \/ q = p){1}).
- by wp; conseq (_ : _ ==> ={glob D, p, e, x, y, q, R.RO.m, RG.RO.m}) => //; sim.
if{1}; last by conseq (_ : _ ==> ={b}) => //; sim.
conseq (_ : _ ==> true) => //.
call{1} Rp_ll; call{2} IdealD_ll; inline{2} CountD(IdealD).init; wp; rnd{2}; rnd{2}; call{2} hd.
by auto => />; smt(dU_ll dReal_ll).
qed.

local equiv e3h : G3.main ~ Honest(D, Rh).main : ={glob D, Look.rrec} ==> !G3.rf{1} => ={res}.
proof.
proc; seq 6 5 : (={glob D, p, x, y, R.RO.m, RG.RO.m, Look.rrec} /\ G3.rf{1} = (y = x){2}).
- by wp; conseq (_ : _ ==> ={glob D, p, x, y, R.RO.m, RG.RO.m, Look.rrec}) => //; sim.
if{2}; last by conseq (_ : _ ==> ={b}) => //; sim.
conseq (_ : _ ==> true) => //.
by call{2} Rh_ll; call{1} IdealD_ll; inline *; auto => />; smt(dU_ll).
qed.

(* The fixed point of a fresh network has probability 2^-W, for every input (Remark G9). *)
local lemma pr_fix (x0 : state) :
  phoare [Net(Ideal).enc : x = x0 /\ R.RO.m = FMap.empty ==> res = x0] <= (inv (2%r ^ W)).
proof.
bypr => &m; rewrite -(dstate1 x0); split => [|[hx he]]; 1: exact ge0_mu.
by rewrite -hx (enc_uniform &m p{m} x{m} x{m}) // he => c; rewrite FMap.mem_empty.
qed.

local lemma pr_rf1 &m : Pr[G1.main() @ &m : G1.rf] <= inv (2%r ^ W) + p1.
proof.
byphoare => //; proc.
seq 9 : G1.rf (inv (2%r ^ W) + p1) 1%r 1%r 0%r => //.
- seq 7 : (y = x) (inv (2%r ^ W)) 1%r 1%r p1 => //.
  + seq 6 : (R.RO.m = FMap.empty) 1%r (inv (2%r ^ W)) 0%r 0%r => //.
    * by exlim x => x0; call (pr_fix x0); auto.
    by hoare; inline *; auto.
  + by wp; rnd (pred1 p); auto => />; smt(mu1_p1 pr_ge0).
by hoare; call (_ : true); auto; inline *; auto; while (!G1.rf); auto.
qed.

local lemma pr_rf3 &m : Pr[G3.main() @ &m : G3.rf] <= inv (2%r ^ W).
proof.
byphoare => //; proc.
seq 6 : G3.rf (inv (2%r ^ W)) 1%r 1%r 0%r => //; last by hoare; call (_ : true); auto; inline *; auto.
wp; seq 4 : (R.RO.m = FMap.empty) 1%r (inv (2%r ^ W)) 0%r 0%r => //.
- by exlim x => x0; call (pr_fix x0); auto.
by hoare; inline *; auto.
qed.

(* ---- Game 2: private copies of A and H for the real encryption ------------------------------ *)
(* [ah]: the decoy decryption or the adversary queries a point of RP; [lk]: a lookup of the real
   phrase that is not the disclosed one. *)
local module Bad = { var ah, lk : bool }.

local module Priv : ABH = {
  proc a(p : pw, s : salt) = { var r; r <@ RP.RO.get(PA (p, s)); return key_of r; }
  proc b = Ideal.b
  proc h(k : key, i : ridx, x : half) = { var r; r <@ RP.RO.get(PH (k, i, x)); return mask_of r; }
}.

local module Sh : ABH = {
  proc a(p : pw, s : salt) = {
    var k; Bad.ah <- Bad.ah \/ PA (p, s) \in RP.RO.m; k <@ Ideal.a(p, s); return k;
  }
  proc b = Ideal.b
  proc h(k : key, i : ridx, x : half) = {
    var m; Bad.ah <- Bad.ah \/ PH (k, i, x) \in RP.RO.m; m <@ Ideal.h(k, i, x); return m;
  }
}.

local module O2 : OraclesD = {
  proc a = Sh.a
  proc b = Sh.b
  proc h = Sh.h
  proc g = IdealD.g
  proc look(f : phrase) : record = {
    Bad.lk <- Bad.lk \/ f <> Look.disc /\ Some f = Look.real;
    return if f = Look.disc then Look.drec else empty;
  }
}.

local module G2 = {
  proc main() : bool = {
    var p, e, v, x, y, q, xd, rc, b;
    R.RO.init(); RG.RO.init(); RP.RO.init();
    p <$ dP; e <$ dent; v <@ RG.RO.get(e); x <- pack e v.`1;
    y <@ Net(Priv).enc(p, x);
    q <$ dP;
    Bad.ah <- false; Bad.lk <- false;
    xd <@ Net(Sh).dec(q, y);
    rc <$ dU (ph xd);
    Look.disc <- ph xd; Look.drec <- rc; Look.real <- Some (phE e);
    CountD(O2).init();
    b <@ D(CountD(O2)).guess(y, q, xd, rc);
    return b;
  }
}.

op onlyB (m : (point, ans) fmap) = forall c, c \in m => isB c.
op noB (m : (point, ans) fmap) = forall c, c \in m => !isB c.

(* The real encryption puts its A and H points into RP, the shared table holds only B points. *)
local equiv pv_a : Ideal.a ~ Priv.a :
  ={arg} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2} /\ noB RP.RO.m{2} /\ onlyB R.RO.m{2} ==>
  ={res} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2} /\ noB RP.RO.m{2} /\ onlyB R.RO.m{2}.
proof. by proc; inline *; auto => />; smt(join_set_pv joinE mem_join mem_set get_setE). qed.

local equiv pv_h : Ideal.h ~ Priv.h :
  ={arg} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2} /\ noB RP.RO.m{2} /\ onlyB R.RO.m{2} ==>
  ={res} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2} /\ noB RP.RO.m{2} /\ onlyB R.RO.m{2}.
proof. by proc; inline *; auto => />; smt(join_set_pv joinE mem_join mem_set get_setE). qed.

local equiv pv_b : Ideal.b ~ Priv.b :
  ={arg} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2} /\ noB RP.RO.m{2} /\ onlyB R.RO.m{2} ==>
  ={res} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2} /\ noB RP.RO.m{2} /\ onlyB R.RO.m{2}.
proof. by proc; inline *; auto => />; smt(join_set_sh joinE mem_join mem_set get_setE). qed.

local equiv enc_priv : Net(Ideal).enc ~ Net(Priv).enc :
  ={arg} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2} /\ noB RP.RO.m{2} /\ onlyB R.RO.m{2} ==>
  ={res} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2} /\ noB RP.RO.m{2} /\ onlyB R.RO.m{2}.
proof.
proc; while (={i, p, x} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2} /\ noB RP.RO.m{2} /\ onlyB R.RO.m{2}).
- by wp; call pv_h; call pv_a; call pv_b; auto.
by auto.
qed.

(* A query of the others gives the same answer while no query has hit a private point. *)
local equiv sh_a : Ideal.a ~ Sh.a :
  !Bad.ah{2} => ={arg} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2} ==>
  !Bad.ah{2} => ={res} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2}.
proof. by proc; inline *; auto => />; smt(join_set_sh joinE mem_join get_setE). qed.

local equiv sh_b : Ideal.b ~ Sh.b :
  (!Bad.ah{2} => ={arg} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2}) /\ noB RP.RO.m{2} ==>
  !Bad.ah{2} => ={res} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2}.
proof. by proc; inline *; auto => />; smt(join_set_sh joinE mem_join get_setE). qed.

local equiv sh_h : Ideal.h ~ Sh.h :
  !Bad.ah{2} => ={arg} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2} ==>
  !Bad.ah{2} => ={res} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2}.
proof. by proc; inline *; auto => />; smt(join_set_sh joinE mem_join get_setE). qed.

local equiv dec_sh : Net(Ideal).dec ~ Net(Sh).dec :
  ={arg} /\ (!Bad.ah{2} => R.RO.m{1} = R.RO.m{2} + RP.RO.m{2}) /\ noB RP.RO.m{2} ==>
  (!Bad.ah{2} => ={res} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2}) /\ noB RP.RO.m{2}.
proof.
proc; while (={i, p} /\ (!Bad.ah{2} => ={y} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2}) /\ noB RP.RO.m{2}).
- case (Bad.ah{2}).
  + by conseq (_ : _ ==> ={i, p} /\ Bad.ah{2} /\ noB RP.RO.m{2}) => //; inline *; auto => /> /#.
  by wp; call sh_h; call sh_a; call sh_b; auto => /> /#.
by auto.
qed.

local lemma D2_ll : islossless D(CountD(O2)).guess.
proof. by apply (D_ll (CountD(O2))); proc; inline *; auto => />; smt(dans_ll dprod_ll dver_ll drest_ll). qed.

local lemma D2_ah : phoare [D(CountD(O2)).guess : Bad.ah ==> Bad.ah] = 1%r.
proof. by conseq D2_ll (_ : Bad.ah ==> Bad.ah) => //; proc (Bad.ah) => //; proc; inline *; auto => /> /#. qed.

(* Games 1 and 2 are identical until Bad (the text's bad events of Game 2). *)
local equiv e12 : G1.main ~ G2.main : ={glob D} ==> !(Bad.ah \/ Bad.lk){2} => ={res}.
proof.
proc.
seq 10 12 : (={glob D, p, e, x, y, q, RG.RO.m} /\ !Bad.lk{2} /\ noB RP.RO.m{2} /\
             (!Bad.ah{2} => ={xd} /\ R.RO.m{1} = R.RO.m{2} + RP.RO.m{2})).
- call dec_sh; wp; rnd; call enc_priv; wp; call (_ : ={RG.RO.m}); 1: by sim.
  inline *; auto => /> *; split; 2: smt(FMap.mem_empty).
  by apply fmap_eqP => c; rewrite joinE FMap.mem_empty.
case (Bad.ah{2}).
- conseq (_ : _ ==> Bad.ah{2}) => [/# |].
  call{1} IdealD_ll; call{2} D2_ah; inline CountD(IdealD).init CountD(O2).init; wp.
  by rnd{1}; rnd{1}; rnd{2}; auto => />; smt(dU_ll dReal_ll).
call (_ : Bad.ah \/ Bad.lk, ={CountD.pws, CountD.cq, CountD.cl, Look.disc, Look.drec, Look.real, RG.RO.m} /\
          R.RO.m{1} = R.RO.m{2} + RP.RO.m{2} /\ noB RP.RO.m{2}).
- exact D_ll.
- by proc; inline CountD(IdealD).a CountD(O2).a; wp; call sh_a; auto => /> /#.
- by move=> &2 _; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />; smt(join_set_sh joinE mem_join get_setE).
- by move=> &2 _; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline CountD(IdealD).h CountD(O2).h; wp; call sh_h; auto => /> /#.
- by move=> &2 _; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />.
- by move=> &2 _; proc; inline *; auto => />; smt(dprod_ll dver_ll drest_ll).
- by move=> &1; proc; inline *; auto => />; smt(dprod_ll dver_ll drest_ll).
- by proc; inline *; auto => /> /#.
- by move=> &2 _; proc; inline *; auto.
- by move=> &1; proc; inline *; auto => /> /#.
inline CountD(IdealD).init CountD(O2).init; wp; rnd{1}; rnd; auto => />; smt(dReal_ll).
qed.

(* ---- Game 2 gives the honest distribution, and its lookups miss the real phrase ---------------- *)
(* The adversary's oracles over an oracle G of A, B, H. *)
local module OG (G : R.RO) : OraclesD = {
  proc a = Orc(G).a
  proc b = Orc(G).b
  proc h = Orc(G).h
  proc g = IdealD.g
  proc look = O2.look
}.

(* The real encryption of Game 2 without its private points: B from G and fresh masks. *)
local module EncB (G : R.RO) = {
  proc run(x : state) : state = {
    var i, s, r;
    i <- 0;
    while (i < 12) { s <@ Orc(G).b(rd i, x.`2); r <$ dans; x <- round (mask_of r) x; i <- i + 1; }
    return x;
  }
}.

local module DB (G : R.RO) = {
  proc distinguish() : bool = {
    var p, e, v, x, y, q, xd, rc, b;
    RG.RO.init();
    p <$ dP; e <$ dent; v <@ RG.RO.get(e); x <- pack e v.`1;
    y <@ EncB(G).run(x);
    q <$ dP;
    Bad.lk <- false;
    xd <@ Net(Orc(G)).dec(q, y);
    rc <$ dU (ph xd);
    Look.disc <- ph xd; Look.drec <- rc; Look.real <- Some (phE e);
    CountD(OG(G)).init();
    b <@ D(CountD(OG(G))).guess(y, q, xd, rc);
    return b;
  }
}.

(* The private A points of the encryption are never read again, and its H points are fresh. *)
local equiv enc_b : Net(Priv).enc ~ EncB(R.RO).run : ={x, R.RO.m} /\ RP.RO.m{1} = FMap.empty ==> ={res, R.RO.m}.
proof.
proc; while (={i, x, R.RO.m} /\ 0 <= i{1} /\ forall k j r, PH (k, j, r) \in RP.RO.m{1} => Ridx.val j < i{1}).
- seq 1 1 : (={i, x, R.RO.m, s} /\ 0 <= i{1} < 12 /\ forall k j r, PH (k, j, r) \in RP.RO.m{1} => Ridx.val j < i{1}).
  + by inline *; auto => /> /#.
  seq 1 0 : (={i, x, R.RO.m} /\ 0 <= i{1} < 12 /\ forall k j r, PH (k, j, r) \in RP.RO.m{1} => Ridx.val j < i{1}).
  + by inline *; auto => />; smt(mem_set dans_ll).
  inline *; rcondt{1} ^if; 1: by auto => />; smt(rdK).
  by auto => />; smt(mem_set rdK get_set_sameE).
by auto => />; smt(FMap.mem_empty).
qed.

local equiv dec_ns : Net(Sh).dec ~ Net(Ideal).dec : ={arg, R.RO.m} ==> ={res, R.RO.m}.
proof. by proc; while (={i, p, y, R.RO.m}); [inline *; auto | auto]. qed.

local equiv e2b : G2.main ~ R.MainD(DB, R.RO).distinguish : ={glob D} ==> ={res, Bad.lk}.
proof.
proc; inline DB(R.RO).distinguish; wp.
call (_ : ={R.RO.m, RG.RO.m, CountD.pws, CountD.cq, CountD.cl, Look.disc, Look.drec, Look.real, Bad.lk}).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
inline CountD(O2).init CountD(OG(R.RO)).init; wp; rnd.
call dec_ns; wp; rnd; call enc_b; wp; call (_ : ={RG.RO.m}); 1: by sim.
by inline *; auto.
qed.

local equiv e2e : R.MainD(DB, R.RO).distinguish ~ R.MainD(DB, RE.FunRO).distinguish :
  ={glob DB} ==> ={res, Bad.lk}.
proof. by conseq (RO_FunRO DB). qed.

(* With the whole function, the B queries of the encryption are pure and the masks give a uniform
   container; G is then an oracle of its own, and the lookups are logged. *)
local module Lk = { var l : phrase list }.

local module OGR (GR : RG.RO) : OraclesD = {
  proc a = Orc(RE.FunRO).a
  proc b = Orc(RE.FunRO).b
  proc h = Orc(RE.FunRO).h
  proc g(e : ent) = { var v; v <@ GR.get(e); return v; }
  proc look(f : phrase) : record = {
    Lk.l <- f :: Lk.l;
    return if f = Look.disc then Look.drec else empty;
  }
}.

local module DG (GR : RG.RO) = {
  proc distinguish() : bool = {
    var p, e, y, q, xd, rc, b;
    RE.FunRO.init();
    p <$ dP; e <$ dent; GR.sample(e);
    y <@ SampleState.run();
    q <$ dP;
    xd <@ Net(Orc(RE.FunRO)).dec(q, y);
    rc <$ dU (ph xd);
    Look.disc <- ph xd; Look.drec <- rc; Look.real <- None;
    Lk.l <- [];
    CountD(OGR(GR)).init();
    b <@ D(CountD(OGR(GR))).guess(y, q, xd, rc);
    Bad.lk <- phE e \in Lk.l /\ phE e <> Look.disc;
    return b;
  }
}.

local equiv encb_unif : EncB(RE.FunRO).run ~ SampleState.run : true ==> ={res}.
proof.
transitivity Masks.run (={x} ==> ={res}) (true ==> ={res}) => //.
- by move=> &1 &2 _; exists arg{1}.
- by proc; while (={i, x}); [inline *; auto | auto].
exact masks_uniform.
qed.

local equiv eDG : R.MainD(DB, RE.FunRO).distinguish ~ RG.MainD(DG, RG.RO).distinguish :
  ={glob D} ==> ={res, Bad.lk}.
proof.
proc; inline DB(RE.FunRO).distinguish DG(RG.RO).distinguish; wp.
call (_ : ={RE.FunRO.f, RG.RO.m, CountD.pws, CountD.cq, CountD.cl, Look.disc, Look.drec} /\
          Look.real{1} <> None /\ Look.real{2} = None /\
          Bad.lk{1} = (oget Look.real{1} \in Lk.l{2} /\ oget Look.real{1} <> Look.disc{2})).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto => /> /#.
inline CountD(OG(RE.FunRO)).init CountD(OGR(RG.RO)).init; wp; rnd.
call (_ : ={RE.FunRO.f}); 1: by sim.
wp; rnd; call encb_unif; wp.
swap{2} 1 1; inline *; auto => /> /#.
qed.

local equiv eLRO : RG.MainD(DG, RG.RO).distinguish ~ RG.MainD(DG, RG.LRO).distinguish :
  ={glob DG} ==> ={res, Bad.lk}.
proof. by conseq (RG.FullEager.RO_LRO DG _) => // _; apply dprod_ll; rewrite dver_ll drest_ll. qed.

(* The real source is drawn after the run. *)
local module GL = {
  proc main() : bool = {
    var e, y, q, xd, rc, b;
    RE.FunRO.init(); RG.RO.init();
    y <$ dstate; q <$ dP;
    xd <@ Net(Orc(RE.FunRO)).dec(q, y);
    rc <$ dU (ph xd);
    Look.disc <- ph xd; Look.drec <- rc; Look.real <- None;
    Lk.l <- [];
    CountD(OGR(RG.RO)).init();
    b <@ D(CountD(OGR(RG.RO))).guess(y, q, xd, rc);
    e <$ dent;
    Bad.lk <- phE e \in Lk.l /\ phE e <> Look.disc;
    return b;
  }
}.

local equiv eGL : RG.MainD(DG, RG.LRO).distinguish ~ GL.main : ={glob D} ==> ={res, Bad.lk}.
proof.
proc; inline DG(RG.LRO).distinguish RG.LRO.sample SampleState.run; wp.
swap{1} [4..6] 11; wp; rnd; rnd{1}.
call (_ : ={RE.FunRO.f, RG.RO.m, CountD.pws, CountD.cq, CountD.cl, Look.disc, Look.drec, Look.real, Lk.l}).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
inline CountD(OGR(RG.LRO)).init CountD(OGR(RG.RO)).init; wp; rnd.
call (_ : ={RE.FunRO.f}); 1: by sim.
by inline *; auto => />; smt(dP_ll).
qed.

(* Each lookup hits the phrase of a fresh source with probability at most 2^-ENT. *)
local lemma mu_phE (L : phrase list) : mu dent (fun e => phE e \in L) <= (size L)%r * inv (2%r ^ ENT).
proof.
elim: L => [|f L ih]; 1: by rewrite (mu_eq _ _ pred0) 1:/# mu0.
rewrite (mu_eq _ _ (predU (fun e => phE e = f) (fun e => phE e \in L))) 1:/# mu_or.
have h1 : mu dent (fun e => phE e = f) <= inv (2%r ^ ENT).
- case: (exists e0, phE e0 = f) => [[e0 <-] | hn].
  + rewrite (mu_eq _ _ (pred1 e0)) 2:dent1 // => x; rewrite /pred1 /=; smt(phE_inj).
  by rewrite (mu_eq _ _ pred0) 1:/# mu0; have := dent1 witness; smt(ge0_mu).
have := ge0_mu dent (predI (fun e => phE e = f) (fun e => phE e \in L)).
smt().
qed.

local lemma lk_bound &m : Pr[GL.main() @ &m : Bad.lk] <= l%r / 2%r ^ ENT.
proof.
byphoare => //; proc.
seq 12 : (size Lk.l <= l) 1%r (l%r / 2%r ^ ENT) 0%r 0%r => //.
- have h0 : 0%r <= inv (2%r ^ ENT) by apply StdOrder.RealOrder.invr_ge0; apply StdOrder.RealOrder.expr_ge0.
  wp; rnd; 2: by move=> _; apply StdOrder.RealOrder.mulr_ge0; smt(ge0_l).
  skip => &hr [hs _]; split => [|/#].
  apply (StdOrder.RealOrder.ler_trans _ _ _ (mu_sub _ _ (fun e => phE e \in Lk.l{hr}) _)) => [x [] //|].
  by apply (StdOrder.RealOrder.ler_trans _ _ _ (mu_phE Lk.l{hr})); apply StdOrder.RealOrder.ler_wpmul2r => //; smt(le_fromint).
hoare; call (_ : CountD.pws = [] /\ CountD.cq = 0 /\ CountD.cl = 0 /\ Lk.l = [] ==> size Lk.l <= l).
- conseq (D_bounded (OGR(RG.RO))) (_ : size Lk.l = CountD.cl ==> size Lk.l = CountD.cl); 1,2: smt().
  by proc (size Lk.l = CountD.cl) => //; proc; inline *; auto => /> /#.
by inline *; auto; while (true); auto.
qed.

(* The honest experiment without refusal, as a program on the oracle of A, B, H. *)
local module D3 (G : R.RO) = {
  proc distinguish() : bool = {
    var p, x, y, rc, b;
    RG.RO.init();
    p <$ dP; x <$ dstate;
    y <@ Net(Orc(G)).enc(p, x);
    rc <$ dU (ph x);
    Look.disc <- ph x; Look.drec <- rc; Look.real <- None;
    CountD(OG(G)).init();
    b <@ D(CountD(OG(G))).guess(y, p, x, rc);
    return b;
  }
}.

local equiv e3d : G3.main ~ R.MainD(D3, R.RO).distinguish : ={glob D} ==> ={res}.
proof.
proc; inline D3(R.RO).distinguish; wp.
call (_ : ={R.RO.m, RG.RO.m, CountD.pws, CountD.cq, CountD.cl, Look.disc, Look.drec, Look.real} /\
          Look.real{1} = None).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto => /> /#.
inline CountD(IdealD).init CountD(OG(R.RO)).init; wp; rnd; wp.
call (_ : ={R.RO.m}); 1: by sim.
by inline *; auto.
qed.

(* Theorem 1's argument: (Y, Q, Inv_Q(Y)) for a uniform Y is (Perm_P(X), P, X) for a uniform X. *)
local equiv eGL3 : GL.main ~ R.MainD(D3, RE.FunRO).distinguish : ={glob D} ==> ={res}.
proof.
proc; inline D3(RE.FunRO).distinguish; wp; rnd{1}; wp.
call (_ : ={RE.FunRO.f, RG.RO.m, CountD.pws, CountD.cq, CountD.cl, Look.disc, Look.drec, Look.real}).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
inline CountD(OGR(RG.RO)).init CountD(OG(RE.FunRO)).init; wp; rnd.
seq 2 3 : (={glob D, RE.FunRO.f, RG.RO.m}); 1: by inline *; auto.
swap{1} 1 1; seq 1 1 : (={glob D, RE.FunRO.f, RG.RO.m} /\ q{1} = p{2}); 1: by auto.
seq 1 1 : (={glob D, RE.FunRO.f, RG.RO.m} /\ q{1} = p{2} /\ y{1} = perm RE.FunRO.f{2} p{2} x0{2}).
- rnd (fun y => invperm RE.FunRO.f{1} q{1} y) (fun x => perm RE.FunRO.f{1} q{1} x).
  by auto => />; smt(permK invpermK dstate_funi dstate_full).
exlim q{1}, y{1} => q1 y1; call{1} (dec_fun_ph q1 y1).
exlim p{2}, x0{2} => p2 x2; call{2} (enc_fun_ph p2 x2).
by auto => />; smt(invpermK dent_ll).
qed.

(* ---- Game 2's private points are hit with probability at most (k + 1) p1 + 12 (q + 12) 2^-256 *)
(* A hit needs an Argon2id query with P or an HMAC query with one of the keys K_i. The encryption's
   masks are fresh, so the container depends on neither: both are drawn after the run. *)
local module LA = {
  var hk : key list
  var ba : bool
}.

local module ShA : ABH = {
  proc a = Ideal.a
  proc b = Ideal.b
  proc h(k : key, i : ridx, r : half) = { var m; LA.hk <- k :: LA.hk; m <@ Ideal.h(k, i, r); return m; }
}.

local module OA : OraclesD = {
  proc a = ShA.a
  proc b = ShA.b
  proc h = ShA.h
  proc g = IdealD.g
  proc look = O2.look
}.

local module EncK (K : RK.RO) = {
  proc run(x : state) : state = {
    var i, s, r;
    i <- 0;
    while (i < 12) {
      s <@ Ideal.b(rd i, x.`2); K.sample(rd i); r <$ dans; x <- round (mask_of r) x; i <- i + 1;
    }
    return x;
  }
}.

local module DA (K : RK.RO) = {
  proc distinguish() : bool = {
    var p, e, v, x, y, q, xd, rc, b, i, r, bh;
    R.RO.init(); RG.RO.init();
    p <$ dP; e <$ dent; v <@ RG.RO.get(e); x <- pack e v.`1;
    y <@ EncK(K).run(x);
    q <$ dP;
    LA.hk <- [];
    xd <@ Net(ShA).dec(q, y);
    rc <$ dU (ph xd);
    Look.disc <- ph xd; Look.drec <- rc; Look.real <- Some (phE e);
    CountD(OA).init();
    b <@ D(CountD(OA)).guess(y, q, xd, rc);
    LA.ba <- p = q \/ p \in CountD.pws;
    bh <- false; i <- 0;
    while (i < 12) { r <@ K.get(rd i); bh <- bh \/ key_of r \in LA.hk; i <- i + 1; }
    return bh;
  }
}.

local equiv enc_k (p0 : pw) : Net(Priv).enc ~ EncK(RK.RO).run :
  p{1} = p0 /\ ={x, R.RO.m} /\ RP.RO.m{1} = FMap.empty /\ RK.RO.m{2} = FMap.empty ==>
  ={res, R.RO.m} /\ privP p0 RP.RO.m{1} RK.RO.m{2} /\ forall c, c \in RK.RO.m{2}.
proof.
proc.
while (={i, x, R.RO.m} /\ p{1} = p0 /\ 0 <= i{1} <= 12 /\ privP p0 RP.RO.m{1} RK.RO.m{2} /\
       (forall c, c \in RK.RO.m{2} <=> Ridx.val c < i{1}) /\
       (forall k j r, PH (k, j, r) \in RP.RO.m{1} => Ridx.val j < i{1}) /\
       (forall s, PA (p0, s) \in RP.RO.m{1} => exists c, c \in RK.RO.m{2} /\
          key_of (oget RP.RO.m{1}.[PA (p0, s)]) = key_of (oget RK.RO.m{2}.[c]))).
- seq 1 1 : (={i, x, R.RO.m, s} /\ p{1} = p0 /\ 0 <= i{1} < 12 /\ privP p0 RP.RO.m{1} RK.RO.m{2} /\
               (forall c, c \in RK.RO.m{2} <=> Ridx.val c < i{1}) /\
               (forall k j r, PH (k, j, r) \in RP.RO.m{1} => Ridx.val j < i{1}) /\
               (forall s, PA (p0, s) \in RP.RO.m{1} => exists c, c \in RK.RO.m{2} /\
                  key_of (oget RP.RO.m{1}.[PA (p0, s)]) = key_of (oget RK.RO.m{2}.[c]))).
  + by call (_ : ={R.RO.m}); [sim | auto].
  seq 1 1 : (={i, x, R.RO.m} /\ p{1} = p0 /\ 0 <= i{1} < 12 /\ privP p0 RP.RO.m{1} RK.RO.m{2} /\
             (forall c, c \in RK.RO.m{2} <=> Ridx.val c <= i{1}) /\
             (forall k j r, PH (k, j, r) \in RP.RO.m{1} => Ridx.val j < i{1}) /\
             (forall s, PA (p0, s) \in RP.RO.m{1} => exists c, c \in RK.RO.m{2} /\
                key_of (oget RP.RO.m{1}.[PA (p0, s)]) = key_of (oget RK.RO.m{2}.[c])) /\
             exists c, c \in RK.RO.m{2} /\ k{1} = key_of (oget RK.RO.m{2}.[c])).
  + inline *; rcondt{2} ^if; 1: by auto => />; smt(rdK).
    case (PA (p0, s{1}) \in RP.RO.m{1}).
    * rcondf{1} ^if; 1: by auto.
      auto => /> &1 &2 hi0 hi12 hA hH hK hPH hPA hin r _.
      have hf : rd i{2} \notin RK.RO.m{2} by smt(rdK).
      do ! split; smt(mem_set get_setE rdK rd_val).
    rcondt{1} ^if; 1: by auto.
    auto => /> &1 &2 hi0 hi12 hA hH hK hPH hPA hin r _.
    have hf : rd i{2} \notin RK.RO.m{2} by smt(rdK).
    do ! split; smt(mem_set get_setE rdK rd_val).
  inline *; rcondt{1} ^if; 1: by auto => />; smt(rdK).
  auto => /> &1 &2 hi0 hi12 hA hH hK hPH hPA c hc r _.
  do ! split; smt(mem_set get_setE rdK rd_val).
by auto => />; smt(FMap.mem_empty Ridx.valP).
qed.

local equiv dec_k (p0 q0 : pw) : Net(Sh).dec ~ Net(ShA).dec :
  ={arg, R.RO.m} /\ arg{1}.`1 = q0 /\ privP p0 RP.RO.m{1} RK.RO.m{2} /\
  (Bad.ah{1} => q0 = p0 \/ hitK RK.RO.m{2} LA.hk{2}) ==>
  ={res, R.RO.m} /\ (Bad.ah{1} => q0 = p0 \/ hitK RK.RO.m{2} LA.hk{2}).
proof.
proc; while (={i, y, p, R.RO.m} /\ p{1} = q0 /\ privP p0 RP.RO.m{1} RK.RO.m{2} /\
              (Bad.ah{1} => q0 = p0 \/ hitK RK.RO.m{2} LA.hk{2})).
- by inline *; auto => />; smt(in_cons).
by auto.
qed.

local equiv eA : G2.main ~ RK.MainD(DA, RK.RO).distinguish :
  ={glob D} ==> Bad.ah{1} => LA.ba{2} \/ res{2}.
proof.
proc; inline{2} DA(RK.RO).distinguish; wp.
while{2} ((Bad.ah{1} => LA.ba{2} \/ hitK RK.RO.m{2} LA.hk{2}) /\ (forall c, c \in RK.RO.m{2}) /\
          0 <= i{2} /\ (bh{2} <=> exists j, 0 <= j < i{2} /\ key_of (oget RK.RO.m{2}.[rd j]) \in LA.hk{2}))
         (12 - i{2}).
- move=> &1 z; inline *; rcondf ^if; 1: by auto => /> /#.
  by auto => />; smt(dans_ll).
wp; seq 9 10 : (={glob D, p, e, y, q, R.RO.m, RG.RO.m} /\ privP p{1} RP.RO.m{1} RK.RO.m{2} /\
                (forall c, c \in RK.RO.m{2})).
- rnd; seq 7 8 : (={glob D, p, e, R.RO.m, RG.RO.m} /\ x{1} = x0{2} /\
                   RP.RO.m{1} = FMap.empty /\ RK.RO.m{2} = FMap.empty); 1: by inline *; auto.
  by exlim p{1} => p0; call (enc_k p0); auto.
exlim p{1}, q{1} => p0 q0.
call (_ : ={R.RO.m, RG.RO.m, CountD.pws, CountD.cq, CountD.cl, Look.disc, Look.drec, Look.real} /\
          privP p0 RP.RO.m{1} RK.RO.m{2} /\
          (Bad.ah{1} => q0 = p0 \/ p0 \in CountD.pws{2} \/ hitK RK.RO.m{2} LA.hk{2})).
- by proc; inline *; auto => />; smt(mem_undup mem_rcons).
- by proc; inline *; auto.
- by proc; inline *; auto => />; smt(in_cons).
- by proc; inline *; auto.
- by proc; inline *; auto.
inline CountD(O2).init CountD(OA).init; wp; rnd.
call (dec_k p0 q0); auto => />; smt(rd_val Ridx.valP).
qed.

local equiv eKF : RK.MainD(DA, RK.RO).distinguish ~ RK.MainD(DA, RKE.FunRO).distinguish :
  ={glob DA, arg} ==> ={res, glob DA}.
proof.
transitivity RK.MainD(DA, RKE.FinRO).distinguish
  (={glob DA, arg} ==> ={res, glob DA}) (={glob DA, arg} ==> ={res, glob DA}) => //.
- by move=> &1 &2 h; exists (glob D){1} Bad.lk{1} CountD.cl{1} CountD.cq{1} CountD.pws{1} LA.ba{1} LA.hk{1}
    Look.disc{1} Look.drec{1} Look.real{1} R.RO.m{1} RG.RO.m{1} arg{1}; smt().
- by apply (RKE.RO_FinRO_D _ DA) => _; exact dans_ll.
by apply (RKE.FinRO_FunRO_D _ DA) => _; exact dans_ll.
qed.

(* The password and the keys are drawn after the run. *)
local module GZ = {
  proc main() : bool = {
    var e, v, x, y, q, xd, rc, b, p, f;
    R.RO.init(); RG.RO.init();
    e <$ dent; v <@ RG.RO.get(e); x <- pack e v.`1;
    y <@ EncK(RKE.FunRO).run(x);
    q <$ dP;
    LA.hk <- [];
    xd <@ Net(ShA).dec(q, y);
    rc <$ dU (ph xd);
    Look.disc <- ph xd; Look.drec <- rc; Look.real <- Some (phE e);
    CountD(OA).init();
    b <@ D(CountD(OA)).guess(y, q, xd, rc);
    p <$ dP;
    f <$ RKE.MUniFinFun.dfun (fun _ => dans);
    return (p = q \/ p \in CountD.pws) \/ exists c, key_of (f c) \in LA.hk;
  }
}.

local equiv eZ : RK.MainD(DA, RKE.FunRO).distinguish ~ GZ.main : ={glob D} ==> (LA.ba \/ res){1} = res{2}.
proof.
proc; inline{1} DA(RKE.FunRO).distinguish RKE.FunRO.init; wp.
while{1} (0 <= i{1} /\ (bh{1} <=> exists j, 0 <= j < i{1} /\ key_of (RKE.FunRO.f{1} (rd j)) \in LA.hk{1}))
         (12 - i{1}).
- by move=> &2 z; inline *; auto => /> /#.
wp; swap{1} 5 13; swap{1} 1 17; rnd; rnd.
call (_ : ={R.RO.m, RG.RO.m, CountD.pws, CountD.cq, CountD.cl, Look.disc, Look.drec, Look.real, LA.hk}).
- by sim.
- by sim.
- by sim.
- by sim.
- by sim.
inline CountD(OA).init; wp; rnd; call (_ : ={R.RO.m, LA.hk}); 1: by sim.
wp; rnd; call (_ : ={R.RO.m}); 1: by sim.
by inline *; auto => />; smt(rd_val Ridx.valP).
qed.

(* One key of the function lies in a list of HMAC keys with probability at most |L| 2^-256. *)
local lemma dfun_key (c : ridx) (L : key list) :
  mu (RKE.MUniFinFun.dfun (fun _ => dans)) (fun f => key_of (f c) \in L) <= (size L)%r / 2%r ^ 256.
proof.
have -> : mu (RKE.MUniFinFun.dfun (fun _ => dans)) (fun f => key_of (f c) \in L) =
          mu (dmap (RKE.MUniFinFun.dfun (fun _ => dans)) (fun f => f c)) (fun a => key_of a \in L).
- by rewrite dmapE /(\o).
have hw : weight (RKE.MUniFinFun.dfun (fun _ => dans)) = 1%r.
- by apply RKE.MUniFinFun.dfun_ll => x /=; exact dans_ll.
have hd : weight dans = 1%r by exact dans_ll.
rewrite RKE.MUniFinFun.dfun_projE /= hw hd /= dscalar1 /dans.
rewrite (mu_eq _ _ (fun (a : ans) => (mem L) a.`1)) 1:/# (dprodEl dkey (dsalt `*` dhalf) (mem L)).
rewrite weight_dprod dsalt_ll dhalf_ll /=.
by apply (Mu_mem.mu_mem_le_size L dkey) => x _; rewrite dkey1.
qed.

local lemma dfun_keys (L : key list) :
  mu (RKE.MUniFinFun.dfun (fun _ => dans)) (fun f => exists c, key_of (f c) \in L) <=
  12%r * ((size L)%r / 2%r ^ 256).
proof.
have hc : FSet.card (FSet.oflist RidxT.enum) = 12.
- rewrite FSet.cardE -(perm_eq_size (undup RidxT.enum)) 1:FSet.oflistK undup_id 1:RidxT.enum_uniq.
  by rewrite /RidxT.enum size_map size_iota.
rewrite -hc (mu_eq _ _ (fun f => exists c, FSet.mem (FSet.oflist RidxT.enum) c /\ key_of (f c) \in L)).
- by move=> f /=; smt(FSet.mem_oflist RidxT.enumP).
by apply (Mu_mem.mu_mem_le_gen _ _ (fun c (f : ridx -> ans) => key_of (f c) \in L)) => c _; apply dfun_key.
qed.

local lemma gz_bound &m :
  Pr[GZ.main() @ &m : res] <= (k + 1)%r * p1 + 12%r * (q + 12)%r / 2%r ^ 256.
proof.
byphoare => //; proc.
seq 15 : (size CountD.pws <= k /\ size LA.hk <= Denial.q + 12) 1%r ((k + 1)%r * p1 + 12%r * (Denial.q + 12)%r / 2%r ^ 256)
         0%r 0%r => //.
- seq 1 : (p = q \/ p \in CountD.pws) ((k + 1)%r * p1) 1%r 1%r (12%r * (Denial.q + 12)%r / 2%r ^ 256)
          (size CountD.pws <= k /\ size LA.hk <= Denial.q + 12) => //.
  + by auto.
  + rnd; 2: by move=> _; apply StdOrder.RealOrder.mulr_ge0; [smt(ge0_k) | exact pr_ge0].
    skip => /> &hr hk _.
    rewrite (mu_eq _ _ (mem (q{hr} :: CountD.pws{hr}))) 1:/#.
    apply (StdOrder.RealOrder.ler_trans _ _ _ (Mu_mem.mu_mem_le_size _ _ p1 _)); 1: by move=> x _; exact mu1_p1.
    by apply StdOrder.RealOrder.ler_wpmul2r; [exact pr_ge0 | smt(le_fromint)].
  rnd; 2: by move=> _; apply StdOrder.RealOrder.divr_ge0; [smt(ge0_q) | apply StdOrder.RealOrder.expr_ge0].
  skip => /> &hr _ hh _.
  apply (StdOrder.RealOrder.ler_trans _ _ _ (dfun_keys LA.hk{hr})).
  have h0 : 0%r <= inv (2%r ^ 256) by apply StdOrder.RealOrder.invr_ge0; apply StdOrder.RealOrder.expr_ge0.
  rewrite -RField.mulrA; apply StdOrder.RealOrder.ler_wpmul2l => //.
  by apply StdOrder.RealOrder.ler_wpmul2r => //; smt(le_fromint).
hoare; call (_ : CountD.pws = [] /\ CountD.cq = 0 /\ CountD.cl = 0 /\ size LA.hk = 12 ==>
                 size CountD.pws <= k /\ size LA.hk <= Denial.q + 12).
- conseq (D_bounded OA) (_ : size LA.hk = 12 + CountD.cq ==> size LA.hk = 12 + CountD.cq); 1,2: smt().
  by proc (size LA.hk = 12 + CountD.cq) => //; proc; inline *; auto => /> /#.
inline CountD(OA).init; wp; rnd.
call (_ : LA.hk = [] ==> size LA.hk = 12).
- by proc; while (size LA.hk = 11 - i /\ -1 <= i); [inline *; auto => /> /# | auto => /> /#].
by inline *; auto; while (true); auto.
qed.

local lemma ah_bound &m : Pr[G2.main() @ &m : Bad.ah] <= (k + 1)%r * p1 + 12%r * (q + 12)%r / 2%r ^ 256.
proof.
have h1 : Pr[G2.main() @ &m : Bad.ah] <= Pr[RK.MainD(DA, RK.RO).distinguish() @ &m : LA.ba \/ res].
- by byequiv eA.
have h2 : Pr[RK.MainD(DA, RK.RO).distinguish() @ &m : LA.ba \/ res] =
          Pr[RK.MainD(DA, RKE.FunRO).distinguish() @ &m : LA.ba \/ res] by byequiv eKF => // /#.
have h3 : Pr[RK.MainD(DA, RKE.FunRO).distinguish() @ &m : LA.ba \/ res] = Pr[GZ.main() @ &m : res].
- by byequiv eZ.
smt(gz_bound).
qed.

(* Game 2's result and lookup event are those of GL. *)
local lemma e2L &m (E : bool -> bool -> bool) :
  Pr[G2.main() @ &m : E res Bad.lk] = Pr[GL.main() @ &m : E res Bad.lk].
proof.
have -> : Pr[G2.main() @ &m : E res Bad.lk] = Pr[R.MainD(DB, R.RO).distinguish() @ &m : E res Bad.lk].
- by byequiv e2b => // /#.
have -> : Pr[R.MainD(DB, R.RO).distinguish() @ &m : E res Bad.lk] =
          Pr[R.MainD(DB, RE.FunRO).distinguish() @ &m : E res Bad.lk] by byequiv e2e => // /#.
have -> : Pr[R.MainD(DB, RE.FunRO).distinguish() @ &m : E res Bad.lk] =
          Pr[RG.MainD(DG, RG.RO).distinguish() @ &m : E res Bad.lk] by byequiv eDG => // /#.
have -> : Pr[RG.MainD(DG, RG.RO).distinguish() @ &m : E res Bad.lk] =
          Pr[RG.MainD(DG, RG.LRO).distinguish() @ &m : E res Bad.lk] by byequiv eLRO => // /#.
by byequiv eGL => // /#.
qed.

(* In suite 3 (W = 256) the last two terms are (12 q + 146) 2^-256; in suite 4 (W = ENT) they are
   2 * 2^-ENT + 12 (q + 12) 2^-256. *)
lemma theorem2 &m :
  `| Pr[Prepared(D, Rp).main() @ &m : res] - Pr[Honest(D, Rh).main() @ &m : res] | <=
    (k + 2)%r * p1 + l%r / 2%r ^ ENT + 2%r / 2%r ^ W + 12%r * (q + 12)%r / 2%r ^ 256.
proof.
(* Refusal and redraw of the prepared experiment. *)
have a1 : Pr[Prepared(D, Rp).main() @ &m : res] <= Pr[G1.main() @ &m : res \/ G1.rf] by byequiv e01 => // /#.
have a2 : Pr[G1.main() @ &m : res /\ !G1.rf] <= Pr[Prepared(D, Rp).main() @ &m : res].
- by byequiv (_ : ={glob D} ==> (res /\ !G1.rf){1} => res{2}) => //; symmetry; conseq e01 => /#.
(* Game 1 to Game 2: up to a hit of a private point or a lookup of the real phrase. *)
have b1 : Pr[G1.main() @ &m : res] <= Pr[G2.main() @ &m : res \/ (Bad.ah \/ Bad.lk)] by byequiv e12 => // /#.
have b2 : Pr[G2.main() @ &m : res /\ !(Bad.ah \/ Bad.lk)] <= Pr[G1.main() @ &m : res].
- by byequiv (_ : ={glob D} ==> (res /\ !(Bad.ah \/ Bad.lk)){1} => res{2}) => //; symmetry; conseq e12 => /#.
(* Game 2 gives Game 3's result. *)
have c1 : Pr[G2.main() @ &m : res] = Pr[G3.main() @ &m : res].
- rewrite (e2L &m (fun b _ => b)) /=.
  have -> : Pr[GL.main() @ &m : res] = Pr[R.MainD(D3, RE.FunRO).distinguish() @ &m : res] by byequiv eGL3.
  have -> : Pr[R.MainD(D3, RE.FunRO).distinguish() @ &m : res] = Pr[R.MainD(D3, R.RO).distinguish() @ &m : res].
  + by rewrite eq_sym; byequiv (RO_FunRO D3).
  by rewrite eq_sym; byequiv e3d.
have c2 : Pr[G2.main() @ &m : Bad.lk] <= l%r / 2%r ^ ENT.
- by rewrite (e2L &m (fun _ b => b)) /=; apply lk_bound.
(* Refusal of the honest experiment. *)
have d1 : Pr[G3.main() @ &m : res /\ !G3.rf] <= Pr[Honest(D, Rh).main() @ &m : res] by byequiv e3h => // /#.
have d2 : Pr[Honest(D, Rh).main() @ &m : res] <= Pr[G3.main() @ &m : res \/ G3.rf].
- by byequiv (_ : ={glob D, Look.rrec} ==> res{1} => (res \/ G3.rf){2}) => //; symmetry; conseq e3h => /#.
(* Union bounds, and the event split by the bad flag. *)
have o1 : Pr[G1.main() @ &m : res \/ G1.rf] <= Pr[G1.main() @ &m : res] + Pr[G1.main() @ &m : G1.rf].
- by rewrite Pr[mu_or]; smt(mu_bounded).
have o2 : Pr[G2.main() @ &m : res \/ (Bad.ah \/ Bad.lk)] <=
          Pr[G2.main() @ &m : res] + Pr[G2.main() @ &m : Bad.ah \/ Bad.lk].
- by rewrite Pr[mu_or]; smt(mu_bounded).
have o2' : Pr[G2.main() @ &m : Bad.ah \/ Bad.lk] <= Pr[G2.main() @ &m : Bad.ah] + Pr[G2.main() @ &m : Bad.lk].
- by rewrite Pr[mu_or]; smt(mu_bounded).
have o3 : Pr[G3.main() @ &m : res \/ G3.rf] <= Pr[G3.main() @ &m : res] + Pr[G3.main() @ &m : G3.rf].
- by rewrite Pr[mu_or]; smt(mu_bounded).
have s1 : Pr[G1.main() @ &m : res] <= Pr[G1.main() @ &m : res /\ !G1.rf] + Pr[G1.main() @ &m : G1.rf].
- rewrite Pr[mu_split G1.rf]; have : Pr[G1.main() @ &m : res /\ G1.rf] <= Pr[G1.main() @ &m : G1.rf].
  + by rewrite Pr[mu_sub].
  smt().
have s2 : Pr[G2.main() @ &m : res] <=
          Pr[G2.main() @ &m : res /\ !(Bad.ah \/ Bad.lk)] + Pr[G2.main() @ &m : Bad.ah \/ Bad.lk].
- rewrite Pr[mu_split (Bad.ah \/ Bad.lk)].
  have : Pr[G2.main() @ &m : res /\ (Bad.ah \/ Bad.lk)] <= Pr[G2.main() @ &m : Bad.ah \/ Bad.lk].
  + by rewrite Pr[mu_sub].
  smt().
have s3 : Pr[G3.main() @ &m : res] <= Pr[G3.main() @ &m : res /\ !G3.rf] + Pr[G3.main() @ &m : G3.rf].
- rewrite Pr[mu_split G3.rf]; have : Pr[G3.main() @ &m : res /\ G3.rf] <= Pr[G3.main() @ &m : G3.rf].
  + by rewrite Pr[mu_sub].
  smt().
have hd : `|Pr[Prepared(D, Rp).main() @ &m : res] - Pr[Honest(D, Rh).main() @ &m : res]| <=
          Pr[G1.main() @ &m : G1.rf] + Pr[G3.main() @ &m : G3.rf] +
          Pr[G2.main() @ &m : Bad.ah] + Pr[G2.main() @ &m : Bad.lk] by smt().
have ek : (k + 2)%r * p1 = (k + 1)%r * p1 + p1 by rewrite !fromintD; ring.
have ew : 2%r / 2%r ^ W = inv (2%r ^ W) + inv (2%r ^ W) by ring.
have := pr_rf1 &m; have := pr_rf3 &m; have := ah_bound &m.
smt().
qed.
end section Theorem2.

(* ---- Simulating a prepared disclosure with a programmable record oracle -------------------- *)
(* The functions need not be ideal: [O] is any implementation. The real-wallet record oracle [Base]
   is given. The prepared disclosure redraws the decoy until it differs from the real password P;
   the simulator does not know P and draws once. *)
module type LOOKUP = { proc look(f : phrase) : record }.
module type DistS (O : ABH) (L : LOOKUP) = {
  proc guess(y : state, q : pw, x : state, rc : record) : bool
}.

module Wrap (Base : LOOKUP) = {
  var disc : phrase
  var drec : record
  proc look(f : phrase) : record = {
    var out;
    if (f = disc) { out <- drec; } else { out <@ Base.look(f); }
    return out;
  }
}.

module PrepDisc (O : ABH) (Base : LOOKUP) (D : DistS) = {
  proc main(p : pw, y : state) : bool = {
    var q, xd, rc, b;
    q <$ dP \ pred1 p;
    xd <@ Net(O).dec(q, y);
    rc <$ dU (ph xd);
    Wrap.disc <- ph xd; Wrap.drec <- rc;
    b <@ D(O, Wrap(Base)).guess(y, q, xd, rc);
    return b;
  }
}.

module SimDisc (O : ABH) (Base : LOOKUP) (D : DistS) = {
  proc main(y : state) : bool = {
    var q, xd, rc, b;
    q <$ dP;
    xd <@ Net(O).dec(q, y);
    rc <$ dU (ph xd);
    Wrap.disc <- ph xd; Wrap.drec <- rc;
    b <@ D(O, Wrap(Base)).guess(y, q, xd, rc);
    return b;
  }
}.

section Simulation.
declare module O <: ABH {-Wrap}.
declare module Base <: LOOKUP {-Wrap, -O}.
declare module D <: DistS {-Wrap, -O, -Base}.
declare axiom O_ll : islossless O.a /\ islossless O.b /\ islossless O.h.
declare axiom D_ll : islossless D(O, Wrap(Base)).guess.

local clone Dexcepted.TwoStepSampling as TS with type i <- pw, type t <- pw, op dt <- (fun _ => dP).

(* The decoy drawn from dP and redrawn if it is P; [bad] records the first draw. *)
local module Q = {
  var bad : bool
  proc direct(p : pw) : pw = { var q; q <$ dP \ pred1 p; return q; }
  proc indirect(p : pw) : pw = {
    var q;
    q <$ dP;
    bad <- q = p;
    if (q = p) q <$ dP \ pred1 p;
    return q;
  }
}.

local equiv q_direct_indirect : Q.direct ~ Q.indirect : ={p} ==> ={res}.
proof.
transitivity TS.S.direct (p{1} = x{2} /\ X{2} = pred1 ==> ={res}) (x{1} = p{2} /\ X{1} = pred1 ==> ={res}) => //.
- by move=> &1 &2 ->; exists (p{2}, pred1).
- by proc; auto.
transitivity TS.S.indirect (={x, X} ==> ={res}) (x{1} = p{2} /\ X{1} = pred1 ==> ={res}) => //.
- by move=> &1 &2 [-> ->]; exists (p{2}, pred1).
- by conseq TS.ll_direct_indirect_eq => /> *; smt(dP_ll).
proc; seq 1 2 : (r{1} = q{2} /\ x{1} = p{2} /\ X{1} = pred1); 1: by auto.
if => //.
by rnd; skip => &1 &2 [[_ [-> ->]] _].
qed.

local module PrepI = {
  proc main(p : pw, y : state) : bool = {
    var q, xd, rc, b;
    q <@ Q.indirect(p);
    xd <@ Net(O).dec(q, y);
    rc <$ dU (ph xd);
    Wrap.disc <- ph xd; Wrap.drec <- rc;
    b <@ D(O, Wrap(Base)).guess(y, q, xd, rc);
    return b;
  }
}.

local module SimI = {
  proc main(p : pw, y : state) : bool = {
    var q, xd, rc, b;
    q <$ dP;
    Q.bad <- q = p;
    xd <@ Net(O).dec(q, y);
    rc <$ dU (ph xd);
    Wrap.disc <- ph xd; Wrap.drec <- rc;
    b <@ D(O, Wrap(Base)).guess(y, q, xd, rc);
    return b;
  }
}.

local lemma rest_ll : islossless Net(O).dec.
proof. by have [ha [hb hh]] := O_ll; have [_ ->] := net_ll O ha hb hh. qed.

(* Up to the first draw being P, the two experiments are the same. *)
(* The redraw is lossless when P does not carry all the mass. *)
local equiv prep_sim : PrepI.main ~ SimI.main :
  ={glob O, glob Base, glob D, glob Wrap, p, y} /\ mu1 dP p{1} < 1%r ==> ={Q.bad} /\ (!Q.bad{2} => ={res}).
proof.
proc; inline Q.indirect.
seq 3 2 : (={glob O, glob Base, glob D, glob Wrap, p, y, Q.bad} /\ q0{1} = q{2} /\ p0{1} = p{1} /\
           Q.bad{1} = (q{2} = p{2}) /\ mu1 dP p{1} < 1%r); 1: by auto.
case (Q.bad{1}).
- conseq (_ : _ ==> ={Q.bad}) => //.
  call{1} D_ll; call{2} D_ll; wp; rnd{1}; rnd{2}; call{1} rest_ll; call{2} rest_ll; wp.
  if{1}; last by skip => />; smt(dU_ll).
  by rnd{1}; skip => />; smt(dU_ll dexcepted_ll dP_ll).
rcondf{1} 1; 1: by auto => /> /#.
by sim => /> /#.
qed.

local lemma pr_bad &m (p : pw) (y : state) : Pr[SimI.main(p, y) @ &m : Q.bad] = mu1 dP p.
proof.
byphoare (_ : arg = (p, y) ==> Q.bad) => //; proc.
seq 2 : Q.bad (mu1 dP p) 1%r (1%r - mu1 dP p) 0%r (Q.bad = (q = p)) => //.
- by auto.
- by wp; rnd (pred1 p); auto => /> /#.
- have [ha [hb hh]] := O_ll.
  call D_ll; auto; call rest_ll; auto => />; smt(dU_ll).
- by hoare; call (_ : true); auto; call (_ : true).
qed.

lemma simulation &m (p : pw) (y : state) :
  `| Pr[PrepDisc(O, Base, D).main(p, y) @ &m : res] - Pr[SimDisc(O, Base, D).main(y) @ &m : res] |
    <= mu1 dP p.
proof.
case: (mu1 dP p < 1%r) => hp1; last by smt(mu_bounded).
have -> : Pr[PrepDisc(O, Base, D).main(p, y) @ &m : res] = Pr[PrepI.main(p, y) @ &m : res].
- byequiv => //; proc.
  seq 1 1 : (={glob O, glob Base, glob D, p, y, q}); 2: by sim.
  outline {1} [1 .. 1] ~ Q.direct.
  by call q_direct_indirect; auto.
have -> : Pr[SimDisc(O, Base, D).main(y) @ &m : res] = Pr[SimI.main(p, y) @ &m : res].
- by byequiv => //; proc; wp; sim.
have h1 : Pr[PrepI.main(p, y) @ &m : res /\ !Q.bad] = Pr[SimI.main(p, y) @ &m : res /\ !Q.bad].
- by byequiv prep_sim => // /#.
have h2 : Pr[PrepI.main(p, y) @ &m : Q.bad] = Pr[SimI.main(p, y) @ &m : Q.bad].
- by byequiv prep_sim => // /#.
have e1 : Pr[PrepI.main(p, y) @ &m : res] =
          Pr[PrepI.main(p, y) @ &m : res /\ Q.bad] + Pr[PrepI.main(p, y) @ &m : res /\ !Q.bad].
- by rewrite Pr[mu_split Q.bad].
have e2 : Pr[SimI.main(p, y) @ &m : res] =
          Pr[SimI.main(p, y) @ &m : res /\ Q.bad] + Pr[SimI.main(p, y) @ &m : res /\ !Q.bad].
- by rewrite Pr[mu_split Q.bad].
have := pr_bad &m p y.
have : Pr[PrepI.main(p, y) @ &m : res /\ Q.bad] <= Pr[PrepI.main(p, y) @ &m : Q.bad] by rewrite Pr[mu_sub].
have : Pr[SimI.main(p, y) @ &m : res /\ Q.bad] <= Pr[SimI.main(p, y) @ &m : Q.bad] by rewrite Pr[mu_sub].
smt(mu_bounded).
qed.
end section Simulation.

end Denial.
