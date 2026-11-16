(* A known pair (DESIGN-NOTES A.5): the games Δ0 and Δ1_j and Lemma K1. G plays no role. *)
require import AllCore List Distr DBool DInterval FMap IntDiv StdBigop Xreal.
require import Suite3 Chain Collision.
require RealSeries DProd Mu_mem.
import W128 StdBigop.Bigreal.BRA.

(* The forward chain of p from X. *)
module Fwd = {
  var p   : pw
  var x   : state
  var sts : pw -> cst
  var odd : bool     (* a fresh query of the finalization off the chain it evaluates *)
  proc init(x0 : state) = { x <- x0; sts <- fun _ => cfwd x0; odd <- false; }
  proc on(c : point, fresh : bool, r : ans) = {
    sts <- fun w => cstep false w (sts w) c fresh r [] R.RO.m;
  }
}.

(* A fresh query of the finalization that is not the next point of the chain it evaluates: the
   forward chain until it is complete, then the backward chain. Without Early it never happens. *)
op oddq (c : point) (f b : cst) =
  !f.`early /\ (if f.`fin then !b.`early /\ (b.`fin \/ c <> last witness b.`chain)
                else c <> last witness f.`chain).

(* The ideal oracle with the bookkeeping of both chains and the adversary's query log; every call is
   a batch of its own, so the batch numbers give the order of the queries. *)
module Mon2 : ABH = {
  var inrun : bool
  var log   : (point * int) list
  var bn    : int

  proc query(c : point) : ans = {
    var fresh, r;
    fresh <- c \notin R.RO.m;
    if (inrun) log <- rcons log (c, bn);
    Fwd.odd <- Fwd.odd \/ !inrun /\ fresh /\ oddq c (Fwd.sts Fwd.p) (Bwd.sts Bwd.p);
    r <@ R.RO.get(c);
    Fwd.on(c, fresh, r);
    Bwd.on(c, fresh, r, []);
    return r;
  }

  proc a(p : pw, s : W128.word) = { var r; bn <- bn + 1; r <@ query(PA (p, s)); return key_of r; }
  proc b(i : ridx, x : W128.word) = { var r; bn <- bn + 1; r <@ query(PB (i, x)); return salt_of r; }
  proc h(k : W256.word, i : ridx, x : W128.word) = {
    var r; bn <- bn + 1; r <@ query(PH (k, i, x)); return mask_of r;
  }
}.

(* Rounds lo .. hi-1 forward from x, and rounds hi down to lo backward from y. *)
module Part (O : ABH) = {
  proc fwd(p : pw, x : state, lo : int, hi : int) : state = {
    var i, s, k, m;
    i <- lo;
    while (i < hi) {
      s <@ O.b(rd i, x.`2); k <@ O.a(p, s); m <@ O.h(k, rd i, x.`2);
      x <- round m x; i <- i + 1;
    }
    return x;
  }
  proc bwd(p : pw, y : state, hi : int, lo : int) : state = {
    var i, s, k, m;
    i <- hi;
    while (lo <= i) {
      s <@ O.b(rd i, y.`1); k <@ O.a(p, s); m <@ O.h(k, rd i, y.`1);
      y <- unround m y; i <- i - 1;
    }
    return y;
  }
}.

module type AdvKP (O : ABH) = {
  proc guess(x : state, y : state) : pw
}.

(* Δ0: X is fixed, P is drawn and Y = Perm_P(X). *)
module Setup0K = {
  proc run(x : state) : pw * state = {
    var p, y;
    R.RO.init();
    p <$ dP;
    y <@ Net(Ideal).enc(p, x);
    return (p, y);
  }
}.

(* An answer of the oracle with its H component replaced; the other components stay uniform. *)
op with_mask (r : ans) (m : W128.word) : ans = (r.`1, (r.`2.`1, m)).

(* Δ1_j: Y is uniform and H is programmed at h_j and h_(j+1). *)
module Setup1K = {
  proc run(x : state, j : int) : pw * state = {
    var p, y, wj, wj2, sj, kj, sj1, kj1, r0, r1;
    R.RO.init();
    p <$ dP;
    y <$ dstate;
    wj  <@ Part(Ideal).fwd(p, x, 0, j);              (* W_j *)
    wj2 <@ Part(Ideal).bwd(p, y, 11, j + 2);         (* W_(j+2) *)
    sj  <@ Ideal.b(rd j, wj.`2);         kj  <@ Ideal.a(p, sj);
    sj1 <@ Ideal.b(rd (j + 1), wj2.`1);  kj1 <@ Ideal.a(p, sj1);
    r0 <$ dans; r1 <$ dans;
    R.RO.set(PH (kj, rd j, wj.`2), with_mask r0 (wj2.`1 +^ wj.`1));         (* M_j = L_(j+2) xor L_j *)
    R.RO.set(PH (kj1, rd (j + 1), wj2.`1), with_mask r1 (wj2.`2 +^ wj.`2)); (* M_(j+1) = R_(j+2) xor R_j *)
    return (p, y);
  }
}.

(* A game on a challenger: [C] plays the adversary's part and decides the outcome. *)
module type PLAYK (O : ABH) = { proc play(p : pw, x : state, y : state) : bool }.

module Delta0 (C : PLAYK) = {
  proc main(x : state) : bool = {
    var p, y, b;
    (p, y) <@ Setup0K.run(x);
    Count(Ideal).init();
    b <@ C(Count(Ideal)).play(p, x, y);
    return b;
  }
}.

module Delta1 (C : PLAYK) = {
  proc main(x : state, j : int) : bool = {
    var p, y, b;
    (p, y) <@ Setup1K.run(x, j);
    Count(Ideal).init();
    b <@ C(Count(Ideal)).play(p, x, y);
    return b;
  }
}.

module PlayK (A : AdvKP) (O : ABH) = {
  proc play(p : pw, x : state, y : state) : bool = { var g; g <@ A(O).guess(x, y); return g = p; }
}.

(* ---- Lemma K1 as functions ------------------------------------------------------------------ *)
(* Rounds lo .. hi-1 of Perm_p forward, and rounds hi down to lo of Inv_p. *)
op fwdp f p (x : state) (lo hi : int) : state =
  foldl (fun (w : state) i => round (mask f p (rd i) w.`2) w) x (iota_ lo (hi - lo)).
op bwdp f p (y : state) (hi lo : int) : state =
  foldl (fun (w : state) i => unround (mask f p (rd i) w.`1) w) y (rev (iota_ lo (hi + 1 - lo))).

lemma rounds_inv f p (s : int list) (w : state) :
  foldl (fun (w : state) i => unround (mask f p (rd i) w.`1) w)
        (foldl (fun (w : state) i => round (mask f p (rd i) w.`2) w) w s) (rev s) = w.
proof. by elim: s w => [|k ks ih] w //=; rewrite rev_cons foldl_rcons ih /= unround_round. qed.

lemma unrounds_inv f p (s : int list) (y : state) :
  foldl (fun (w : state) i => round (mask f p (rd i) w.`2) w)
        (foldl (fun (w : state) i => unround (mask f p (rd i) w.`1) w) y (rev s)) s = y.
proof. by elim/last_ind: s y => [|ks k ih] y //=; rewrite rev_rcons /= foldl_rcons ih /= round_unround. qed.

(* The points of rounds j and j + 1 that Δ1_j programs: H points with these round indices. *)
op tpt (j : int) (c : point) =
  with c = PA _ => false with c = PB _ => false with c = PH t => Ridx.val t.`2 = j \/ Ridx.val t.`2 = j + 1.

lemma mask_loc j f g p i r : (forall c, !tpt j c => f c = g c) => 0 <= i < 12 => i <> j => i <> j + 1 =>
  mask f p (rd i) r = mask g p (rd i) r.
proof. by move=> h hi h1 h2; rewrite /mask /= !h //; rewrite /=; smt(rdK). qed.

lemma fwdp_loc j f g p x lo hi : (forall c, !tpt j c => f c = g c) => 0 <= lo => hi <= 12 =>
  (hi <= j \/ j + 2 <= lo) => fwdp f p x lo hi = fwdp g p x lo hi.
proof.
move=> h hlo hhi hj; rewrite /fwdp; apply eq_in_foldl => // w i /mem_iota hin.
by rewrite /= (mask_loc j f g) // /#.
qed.

lemma bwdp_loc j f g p y hi lo : (forall c, !tpt j c => f c = g c) => 0 <= lo => hi < 12 =>
  (hi < j \/ j + 2 <= lo) => bwdp f p y hi lo = bwdp g p y hi lo.
proof.
move=> h hlo hhi hj; rewrite /bwdp; apply eq_in_foldl => // w i; rewrite mem_rev => /mem_iota hin.
by rewrite /= (mask_loc j f g) // /#.
qed.

(* Perm_p through rounds j and j + 1, and the backward rounds undo the forward ones. *)
lemma perm_split f p (x : state) (j : int) : 0 <= j <= 10 =>
  perm f p x = fwdp f p (round (mask f p (rd (j + 1)) (round (mask f p (rd j) (fwdp f p x 0 j).`2) (fwdp f p x 0 j)).`2)
                               (round (mask f p (rd j) (fwdp f p x 0 j).`2) (fwdp f p x 0 j))) (j + 2) 12.
proof.
move=> hj; have e : iota_ 0 12 = iota_ 0 j ++ j :: (j + 1) :: iota_ (j + 2) (10 - j).
- rewrite (_ : 12 = j + (10 - j + 1 + 1)) 1:/# iota_add 1,2:/# /= (_ : 12 - j = 11 - j + 1) 1:/#.
  by rewrite iotaS 1:/# (_ : 11 - j = 10 - j + 1) 1:/# iotaS 1:/# /#.
by rewrite /perm /fwdp e foldl_cat /= (_ : 12 - (j + 2) = 10 - j) 1:/#.
qed.

lemma bwdp_fwdp f p (w : state) lo hi : lo <= hi => bwdp f p (fwdp f p w lo hi) (hi - 1) lo = w.
proof. by move=> h; rewrite /bwdp /fwdp (_ : hi - 1 + 1 - lo = hi - lo) 1:/# rounds_inv. qed.

lemma fwdp_bwdp f p (y : state) lo hi : lo <= hi => fwdp f p (bwdp f p y (hi - 1) lo) lo hi = y.
proof. by move=> h; rewrite /bwdp /fwdp (_ : hi - 1 + 1 - lo = hi - lo) 1:/# unrounds_inv. qed.

lemma xor_solve (a b m : W128.word) : (a +^ m = b) <=> (m = b +^ a).
proof. smt(xorA xorC xorK xor0). qed.

(* The text's first bullet: Perm_p(X) = Y exactly when the masks of rounds j and j + 1 take the
   required values M_j = L_(j+2) xor L_j and M_(j+1) = R_(j+2) xor R_j. *)
lemma perm_req f p (x y : state) j : 0 <= j <= 10 =>
  (perm f p x = y) <=>
  (mask f p (rd j) (fwdp f p x 0 j).`2 = (bwdp f p y 11 (j + 2)).`1 +^ (fwdp f p x 0 j).`1 /\
   mask f p (rd (j + 1)) (bwdp f p y 11 (j + 2)).`1 = (bwdp f p y 11 (j + 2)).`2 +^ (fwdp f p x 0 j).`2).
proof.
move=> hj; rewrite (perm_split _ _ _ j) //.
pose w := fwdp f p x 0 j; pose v := bwdp f p y 11 (j + 2).
pose W := round (mask f p (rd (j + 1)) (round (mask f p (rd j) w.`2) w).`2) (round (mask f p (rd j) w.`2) w).
have -> : (fwdp f p W (j + 2) 12 = y) <=> (W = v).
- have h1 := bwdp_fwdp f p W (j + 2) 12 _; 1: smt().
  have h2 := fwdp_bwdp f p y (j + 2) 12 _; 1: smt().
  by move: h1 h2; rewrite /v /= => h1 h2; split => [<- | ->]; [rewrite h1 | rewrite h2].
by rewrite /W /round /=; smt(xor_solve).
qed.

(* Δ1_j as a function of (H', Y, r0, r1): the two programmed points and the programmed table. *)
op upd (f : point -> ans) (c : point) (v : ans) = fun z => if z = c then v else f z.
op h0 f p (x : state) j =
  PH (key_of (f (PA (p, salt_of (f (PB (rd j, (fwdp f p x 0 j).`2)))))), rd j, (fwdp f p x 0 j).`2).
op h1 f p (y : state) j =
  PH (key_of (f (PA (p, salt_of (f (PB (rd (j + 1), (bwdp f p y 11 (j + 2)).`1)))))), rd (j + 1),
      (bwdp f p y 11 (j + 2)).`1).
op prog f p (x : state) j (y : state) r0 r1 =
  upd (upd f (h0 f p x j) (with_mask r0 ((bwdp f p y 11 (j + 2)).`1 +^ (fwdp f p x 0 j).`1)))
      (h1 f p y j) (with_mask r1 ((bwdp f p y 11 (j + 2)).`2 +^ (fwdp f p x 0 j).`2)).

lemma h_loc j f g p x y : 0 <= j <= 10 => (forall c, !tpt j c => f c = g c) =>
  h0 f p x j = h0 g p x j /\ h1 f p y j = h1 g p y j /\
  fwdp f p x 0 j = fwdp g p x 0 j /\ bwdp f p y 11 (j + 2) = bwdp g p y 11 (j + 2).
proof.
move=> hj h; have e1 := fwdp_loc j f g p x 0 j h _ _ _; 1..3: smt().
have e2 := bwdp_loc j f g p y 11 (j + 2) h _ _ _; 1..3: smt().
by rewrite /h0 /h1 e1 e2 /= !h //; rewrite /tpt.
qed.

lemma h_tpt f g p x y j : 0 <= j <= 10 =>
  tpt j (h0 f p x j) /\ tpt j (h1 g p y j) /\ h0 f p x j <> h1 g p y j.
proof. by move=> hj; rewrite /h0 /h1 /=; smt(rdK). qed.

(* The event that Δ1_j yields the table g and the container y0. *)
lemma ev_split g f p x j y0 y r0 r1 : 0 <= j <= 10 =>
  ((prog f p x j y r0 r1, y) = (g, y0)) <=>
  (y = y0 /\ (forall z, z <> h0 g p x j => z <> h1 g p y0 j => f z = g z) /\
   r0.`1 = (g (h0 g p x j)).`1 /\ r0.`2.`1 = (g (h0 g p x j)).`2.`1 /\
   r1.`1 = (g (h1 g p y0 j)).`1 /\ r1.`2.`1 = (g (h1 g p y0 j)).`2.`1 /\ perm g p x = y0).
proof.
move=> hj; rewrite (perm_req _ _ _ _ j) //.
have [t0 [t1 n01]] := h_tpt f f p x y j hj.
split => [[hp <-] | [-> [hA [k0 [s0 [k1 [s1 [m0 m1]]]]]]]].
- have hz : forall z, g z = prog f p x j y r0 r1 z by move=> z; rewrite -hp.
  have hT : forall c, !tpt j c => f c = g c by move=> c hc; rewrite hz /prog /upd /= /#.
  have [e0 [e1 [e2 e3]]] := h_loc j f g p x y hj hT.
  have g0 := hz (h0 f p x j); have g1 := hz (h1 f p y j).
  move: g0 g1; rewrite /prog /upd /= n01 /= -e0 -e1 /with_mask => g0 g1.
  split; 1: by move=> z h0z h1z; rewrite hz /prog /upd /= h0z h1z.
  have -> : mask g p (rd j) (fwdp g p x 0 j).`2 = mask_of (g (h0 g p x j)) by rewrite /mask /h0.
  have -> : mask g p (rd (j + 1)) (bwdp g p y 11 (j + 2)).`1 = mask_of (g (h1 g p y j)) by rewrite /mask /h1.
  by rewrite -e0 -e1 g0 g1 /mask_of /= e2 e3.
have [_ [_ n01']] := h_tpt g g p x y0 j hj.
have [t0' [t1' _]] := h_tpt g g p x y0 j hj.
have hT : forall c, !tpt j c => f c = g c by move=> c hc; apply hA; smt().
have [e0 [e1 [e2 e3]]] := h_loc j f g p x y0 hj hT.
have m0' : mask_of (g (h0 g p x j)) = (bwdp g p y0 11 (j + 2)).`1 +^ (fwdp g p x 0 j).`1 by rewrite -m0 /mask /h0.
have m1' : mask_of (g (h1 g p y0 j)) = (bwdp g p y0 11 (j + 2)).`2 +^ (fwdp g p x 0 j).`2 by rewrite -m1 /mask /h1.
suff -> : prog f p x j y0 r0 r1 = g by done.
apply fun_ext => z; rewrite /prog /upd e0 e1 e2 e3 /=.
case: (z = h1 g p y0 j) => [-> | hz1]; 1: by rewrite /with_mask -m1'; smt().
case: (z = h0 g p x j) => [-> | hz0]; 1: by rewrite /with_mask -m0'; smt().
by rewrite hA.
qed.

(* A uniform table agrees with g outside two points with probability mu1 g / (mu1 g(c0) mu1 g(c1)). *)
lemma big2 (F : point -> real) c0 c1 : c0 <> c1 =>
  StdBigop.Bigreal.BRM.big predT F PointT.enum =
  F c0 * (F c1 * StdBigop.Bigreal.BRM.big (predI (predC1 c0) (predC1 c1)) F PointT.enum).
proof.
move=> hne; rewrite (StdBigop.Bigreal.BRM.bigD1 _ _ c0) ?PointT.enumP ?PointT.enum_uniq //.
by rewrite (StdBigop.Bigreal.BRM.bigD1_cond _ _ _ c1) ?PointT.enumP ?PointT.enum_uniq // /predC1 /#.
qed.

lemma dF_two (g : point -> ans) c0 c1 : c0 <> c1 =>
  mu1 (RE.MUniFinFun.dfun (fun _ => dans)) g =
  mu1 dans (g c0) * mu1 dans (g c1) *
  mu (RE.MUniFinFun.dfun (fun _ => dans)) (fun f => forall z, z <> c0 => z <> c1 => f z = g z).
proof.
move=> hne; rewrite RE.MUniFinFun.dfun1E.
rewrite (mu_eq _ _ (fun f => forall z, (fun z v => z <> c0 => z <> c1 => v = g z) z (f z))) 1:// RE.MUniFinFun.dfunE /=.
rewrite (big2 _ c0 c1) // (big2 _ c0 c1) //=.
have hl : mu dans (fun (_ : ans) => true) = 1%r by apply dans_ll.
rewrite hl (StdBigop.Bigreal.BRM.eq_bigr _ (fun (x : point) => mu dans (fun (v : ans) => x <> c0 => x <> c1 => v = g x))
                                         (fun x => mu1 dans (g x))) /=.
- by move=> x; rewrite /predI /predC1 /= => -[h0 h1]; rewrite h0 h1.
by rewrite RField.mulrA.
qed.

(* The key and the salt of an answer: probability 2^128 times that of the whole answer. *)
lemma dans_ks (v : ans) : mu dans (fun r : ans => r.`1 = v.`1 /\ r.`2.`1 = v.`2.`1) = mu1 dans v * 2%r ^ 128.
proof.
rewrite /dans (dprodE (pred1 v.`1) (fun b : W128.word * W128.word => b.`1 = v.`2.`1)).
rewrite (dprodEl _ _ (pred1 v.`2.`1)) W128.DWord.dunifin_ll.
case: v => k [s m]; rewrite dprod1E dprod1E /= !dhalf1.
have h : 2%r ^ 128 <> 0%r by smt(StdOrder.RealOrder.expr_gt0).
by field.
qed.

(* Δ0 and Δ1_j through the whole table: the table and the container they give. *)
module S0K = {
  proc run(p : pw, x : state) : (point -> ans) * state = {
    var f;
    f <$ RE.MUniFinFun.dfun (fun _ => dans);
    return (f, perm f p x);
  }
}.

module S1K = {
  proc run(p : pw, x : state, j : int) : (point -> ans) * state = {
    var f, y, r0, r1;
    f <$ RE.MUniFinFun.dfun (fun _ => dans);
    y <$ dstate; r0 <$ dans; r1 <$ dans;
    return (prog f p x j y r0 r1, y);
  }
}.

lemma pr_s0 &m p0 x0 g y0 :
  Pr[S0K.run(p0, x0) @ &m : res = (g, y0)] =
  b2r (perm g p0 x0 = y0) * mu1 (RE.MUniFinFun.dfun (fun _ => dans)) g.
proof.
byphoare (_ : p = p0 /\ x = x0 ==> res = (g, y0)) => //; proc; rnd; skip => />.
case: (perm g p0 x0 = y0) => h /=.
- by apply mu_eq => f /#.
by rewrite (mu_eq _ _ pred0) 1:/# mu0.
qed.

lemma pr_s1 &m p0 x0 j0 g y0 : 0 <= j0 <= 10 =>
  Pr[S1K.run(p0, x0, j0) @ &m : res = (g, y0)] =
  b2r (perm g p0 x0 = y0) * mu1 (RE.MUniFinFun.dfun (fun _ => dans)) g.
proof.
move=> hj; have [_ [_ hne]] := h_tpt g g p0 x0 y0 j0 hj.
pose c0 := h0 g p0 x0 j0; pose c1 := h1 g p0 y0 j0.
pose q0 := mu dans (fun r : ans => r.`1 = (g c0).`1 /\ r.`2.`1 = (g c0).`2.`1).
pose q1 := mu dans (fun r : ans => r.`1 = (g c1).`1 /\ r.`2.`1 = (g c1).`2.`1).
pose b := b2r (perm g p0 x0 = y0).
have -> : b * mu1 (RE.MUniFinFun.dfun (fun _ => dans)) g =
          mu (RE.MUniFinFun.dfun (fun _ => dans)) (fun f => forall z, z <> c0 => z <> c1 => f z = g z) *
          (mu1 dstate y0 * (q0 * (q1 * b))).
- rewrite (dF_two g c0 c1) // /q0 /q1 !dans_ks dstate1_256.
  have e : 2%r ^ 128 * 2%r ^ 128 = 2%r ^ 256 by rewrite -RField.exprD.
  have nz : 2%r ^ 256 <> 0%r by smt(StdOrder.RealOrder.expr_gt0).
  by field.
byphoare (_ : p = p0 /\ x = x0 /\ j = j0 ==> res = (g, y0)) => //; proc.
pose A := fun f : point -> ans => forall z, z <> c0 => z <> c1 => f z = g z.
seq 1 : (A f) (mu (RE.MUniFinFun.dfun (fun _ => dans)) A) (mu1 dstate y0 * (q0 * (q1 * b)))
        (1%r - mu (RE.MUniFinFun.dfun (fun _ => dans)) A) 0%r (p = p0 /\ x = x0 /\ j = j0) => //.
- by auto.
- by rnd; skip.
- seq 1 : (y = y0) (mu1 dstate y0) (q0 * (q1 * b)) (1%r - mu1 dstate y0) 0%r (A f /\ p = p0 /\ x = x0 /\ j = j0) => //.
  + by auto.
  + by rnd; skip.
  + seq 1 : (r0.`1 = (g c0).`1 /\ r0.`2.`1 = (g c0).`2.`1) q0 (q1 * b) (1%r - q0) 0%r
            (A f /\ y = y0 /\ p = p0 /\ x = x0 /\ j = j0) => //.
    * by auto.
    * by rnd; skip.
    * rnd; skip => /> &hr hA hk hs.
      rewrite (mu_eq _ _ (fun r : ans => (r.`1 = (g c1).`1 /\ r.`2.`1 = (g c1).`2.`1) /\ perm g p0 x0 = y0)).
      - by move=> r; have := ev_split g f{hr} p0 x0 j0 y0 y0 r0{hr} r hj; rewrite /= => ->; smt().
      rewrite /b; case: (perm g p0 x0 = y0) => h /=; 1: done.
      by rewrite (mu_eq _ _ pred0) 1:/# mu0.
    * by hoare; rnd; skip => &hr hpre r _; smt(ev_split).
  + by hoare; rnd; rnd; skip => &hr hpre r0 _ r1 _; smt(ev_split).
by hoare; rnd; rnd; rnd; skip => &hr hpre y _ r0 _ r1 _; smt(ev_split).
qed.

(* Through the whole function, the partial rounds compute fwdp and bwdp. *)
lemma fwd_fun (p0 : pw) (x0 : state) (lo0 hi0 : int) :
  hoare [Part(Orc(RE.FunRO)).fwd : p = p0 /\ x = x0 /\ lo = lo0 /\ hi = hi0 /\ lo0 <= hi0 ==>
                                   res = fwdp RE.FunRO.f p0 x0 lo0 hi0].
proof.
proc; inline *.
while (lo0 <= i <= hi0 /\ p = p0 /\ hi = hi0 /\
       x = foldl (fun (w : state) j => round (mask RE.FunRO.f p0 (rd j) w.`2) w) x0 (iota_ lo0 (i - lo0))).
- auto => /> &hr h1 h2 h3; split; 1: smt().
  by rewrite (_ : i{hr} + 1 - lo0 = (i{hr} - lo0) + 1) 1:/# iotaSr 1:/# -cats1 foldl_cat /= /mask /#.
by auto => />; rewrite /fwdp iota0 //=; smt().
qed.

lemma fwd_fun_ph (p0 : pw) (x0 : state) (lo0 hi0 : int) :
  phoare [Part(Orc(RE.FunRO)).fwd : p = p0 /\ x = x0 /\ lo = lo0 /\ hi = hi0 /\ lo0 <= hi0 ==>
                                    res = fwdp RE.FunRO.f p0 x0 lo0 hi0] = 1%r.
proof.
conseq (: true ==> true) (fwd_fun p0 x0 lo0 hi0) => //.
by proc; inline *; while true (hi - i); auto => /#.
qed.

lemma bwd_fun (p0 : pw) (y0 : state) (hi0 lo0 : int) :
  hoare [Part(Orc(RE.FunRO)).bwd : p = p0 /\ y = y0 /\ hi = hi0 /\ lo = lo0 /\ lo0 <= hi0 + 1 ==>
                                   res = bwdp RE.FunRO.f p0 y0 hi0 lo0].
proof.
proc; inline *.
while (lo0 - 1 <= i <= hi0 /\ p = p0 /\ lo = lo0 /\
       y = foldl (fun (w : state) j => unround (mask RE.FunRO.f p0 (rd j) w.`1) w) y0
                 (rev (iota_ (i + 1) (hi0 - i)))).
- auto => /> &hr h1 h2 h3; split; 1: smt().
  rewrite (_ : hi0 - (i{hr} - 1) = (hi0 - i{hr}) + 1) 1:/# iotaS 1:/# rev_cons foldl_rcons /=.
  by rewrite /mask.
by auto => />; rewrite /bwdp iota0 //=; smt().
qed.

lemma bwd_fun_ph (p0 : pw) (y0 : state) (hi0 lo0 : int) :
  phoare [Part(Orc(RE.FunRO)).bwd : p = p0 /\ y = y0 /\ hi = hi0 /\ lo = lo0 /\ lo0 <= hi0 + 1 ==>
                                    res = bwdp RE.FunRO.f p0 y0 hi0 lo0] = 1%r.
proof.
conseq (: true ==> true) (bwd_fun p0 y0 hi0 lo0) => //.
by proc; inline *; while true (i - lo + 1); auto => /#.
qed.

section K1.
declare module C <: PLAYK {-R.RO, -R.FRO, -RE.FunRO, -Count}.

local module KX = {
  var x : state
  var j : int
}.

(* Δ0 and Δ1_j as programs on the oracle; x and j are stored in KX. *)
local module D0 (G : R.RO) = {
  proc distinguish() : bool = {
    var p, y, b;
    p <$ dP;
    y <@ Net(Orc(G)).enc(p, KX.x);
    Count(Orc(G)).init();
    b <@ C(Count(Orc(G))).play(p, KX.x, y);
    return b;
  }
}.

local module D1 (G : R.RO) = {
  proc distinguish() : bool = {
    var p, y, wj, wj2, sj, kj, sj1, kj1, r0, r1, b;
    p <$ dP;
    y <$ dstate;
    wj  <@ Part(Orc(G)).fwd(p, KX.x, 0, KX.j);
    wj2 <@ Part(Orc(G)).bwd(p, y, 11, KX.j + 2);
    sj  <@ Orc(G).b(rd KX.j, wj.`2);         kj  <@ Orc(G).a(p, sj);
    sj1 <@ Orc(G).b(rd (KX.j + 1), wj2.`1);  kj1 <@ Orc(G).a(p, sj1);
    r0 <$ dans; r1 <$ dans;
    G.set(PH (kj, rd KX.j, wj.`2), with_mask r0 (wj2.`1 +^ wj.`1));
    G.set(PH (kj1, rd (KX.j + 1), wj2.`1), with_mask r1 (wj2.`2 +^ wj.`2));
    Count(Orc(G)).init();
    b <@ C(Count(Orc(G))).play(p, KX.x, y);
    return b;
  }
}.

local module W0 (G : R.RO) = {
  proc main(x : state) : bool = {
    var b;
    KX.x <- x; Count(Orc(G)).init();
    b <@ R.MainD(D0, G).distinguish();
    return b;
  }
}.

local module W1 (G : R.RO) = {
  proc main(x : state, j : int) : bool = {
    var b;
    KX.x <- x; KX.j <- j; Count(Orc(G)).init();
    b <@ R.MainD(D1, G).distinguish();
    return b;
  }
}.

(* The same experiments with the table and the container drawn by S0K and S1K. *)
local module V0 = {
  proc main(x : state) : bool = {
    var p, y, b;
    p <$ dP;
    (RE.FunRO.f, y) <@ S0K.run(p, x);
    Count(Orc(RE.FunRO)).init();
    b <@ C(Count(Orc(RE.FunRO))).play(p, x, y);
    return b;
  }
}.

local module V1 = {
  proc main(x : state, j : int) : bool = {
    var p, y, b;
    p <$ dP;
    (RE.FunRO.f, y) <@ S1K.run(p, x, j);
    Count(Orc(RE.FunRO)).init();
    b <@ C(Count(Orc(RE.FunRO))).play(p, x, y);
    return b;
  }
}.

local equiv e0 : Delta0(C).main ~ W0(R.RO).main : ={glob C, x} ==> ={res, glob C}.
proof.
proc; inline Setup0K.run R.MainD(D0, R.RO).distinguish D0(R.RO).distinguish; wp.
call (_ : ={R.RO.m, Count.ca, Count.cb, Count.ch}); 1..3: by sim.
inline Count(Ideal).init Count(Orc(R.RO)).init; wp.
call (_ : ={R.RO.m}); 1: by sim.
by inline *; auto.
qed.

local equiv e1 : Delta1(C).main ~ W1(R.RO).main : ={glob C, x, j} ==> ={res, glob C}.
proof.
proc; inline Setup1K.run R.MainD(D1, R.RO).distinguish D1(R.RO).distinguish; wp.
call (_ : ={R.RO.m, Count.ca, Count.cb, Count.ch}); 1..3: by sim.
inline Count(Ideal).init Count(Orc(R.RO)).init R.RO.set; wp; rnd; rnd.
do 6! (call (_ : ={R.RO.m}); 1: by sim).
by inline *; auto.
qed.

local equiv ef0 : W0(R.RO).main ~ W0(RE.FunRO).main : ={glob C, x} ==> ={res, glob C}.
proof. by proc; call (RO_FunRO D0); inline *; auto. qed.

local equiv ef1 : W1(R.RO).main ~ W1(RE.FunRO).main : ={glob C, x, j} ==> ={res, glob C}.
proof. by proc; call (RO_FunRO D1); inline *; auto. qed.

local equiv s01 : S0K.run ~ S1K.run : ={p, x} /\ 0 <= j{2} <= 10 ==> ={res}.
proof.
bypr (res{1}) (res{2}) => // &1 &2 [g y0] [[hp hx] hj].
by rewrite (pr_s0 &1 p{1} x{1} g y0) (pr_s1 &2 p{2} x{2} j{2} g y0) // hp hx.
qed.

local equiv ev0 : W0(RE.FunRO).main ~ V0.main : ={glob C, x} ==> ={res, glob C}.
proof.
proc; inline R.MainD(D0, RE.FunRO).distinguish D0(RE.FunRO).distinguish RE.FunRO.init S0K.run; wp.
call (_ : ={RE.FunRO.f, Count.ca, Count.cb, Count.ch}); 1..3: by sim.
inline Count(Orc(RE.FunRO)).init; wp.
ecall{1} (enc_fun_ph p{1} KX.x{1}); swap{1} 8 -2.
by wp; rnd; wp; rnd; auto.
qed.

local equiv ev01 : V0.main ~ V1.main : ={glob C, x} /\ 0 <= j{2} <= 10 ==> ={res, glob C}.
proof.
proc; call (_ : ={RE.FunRO.f, Count.ca, Count.cb, Count.ch}); 1..3: by sim.
by inline Count(Orc(RE.FunRO)).init; wp; call s01; auto.
qed.

local equiv ev1 : V1.main ~ W1(RE.FunRO).main : ={glob C, x, j} /\ 0 <= j{1} <= 10 ==> ={res, glob C}.
proof.
proc; inline R.MainD(D1, RE.FunRO).distinguish D1(RE.FunRO).distinguish RE.FunRO.init S1K.run; wp.
call (_ : ={RE.FunRO.f, Count.ca, Count.cb, Count.ch}); 1..3: by sim.
inline Count(Orc(RE.FunRO)).init RE.FunRO.set Orc(RE.FunRO).a Orc(RE.FunRO).b RE.FunRO.get.
swap{2} 9 -2; wp; rnd; rnd; wp.
ecall{2} (bwd_fun_ph p{2} y{2} 11 (KX.j{2} + 2)).
ecall{2} (fwd_fun_ph p{2} KX.x{2} 0 KX.j{2}).
by wp; rnd; wp; rnd; wp; rnd; auto => /> /#.
qed.

(* Lemma K1: for every j, (P, A, B, H, Y) has the same joint distribution in Δ0 and Δ1_j. *)
lemma K1 (j0 : int) : 0 <= j0 <= 10 =>
  equiv [Delta0(C).main ~ Delta1(C).main : ={glob C, x} /\ j{2} = j0 ==> ={res, glob C}].
proof.
move=> hj; bypr (res, glob C){1} (res, glob C){2} => // &1 &2 a [[hc hx] hj2].
have -> : Pr[Delta0(C).main(x{1}) @ &1 : (res, glob C) = a] = Pr[V0.main(x{1}) @ &1 : (res, glob C) = a].
- have -> : Pr[Delta0(C).main(x{1}) @ &1 : (res, glob C) = a] = Pr[W0(R.RO).main(x{1}) @ &1 : (res, glob C) = a].
  + by byequiv e0 => // /#.
  have -> : Pr[W0(R.RO).main(x{1}) @ &1 : (res, glob C) = a] = Pr[W0(RE.FunRO).main(x{1}) @ &1 : (res, glob C) = a].
  + by byequiv ef0 => // /#.
  by byequiv ev0 => // /#.
have -> : Pr[Delta1(C).main(x{2}, j{2}) @ &2 : (res, glob C) = a] = Pr[V1.main(x{2}, j{2}) @ &2 : (res, glob C) = a].
- have -> : Pr[Delta1(C).main(x{2}, j{2}) @ &2 : (res, glob C) = a] = Pr[W1(R.RO).main(x{2}, j{2}) @ &2 : (res, glob C) = a].
  + by byequiv e1 => // /#.
  have -> : Pr[W1(R.RO).main(x{2}, j{2}) @ &2 : (res, glob C) = a] = Pr[W1(RE.FunRO).main(x{2}, j{2}) @ &2 : (res, glob C) = a].
  + by byequiv ef1 => // /#.
  by rewrite eq_sym; byequiv ev1 => // /#.
by byequiv ev01 => // /#.
qed.
end section K1.
