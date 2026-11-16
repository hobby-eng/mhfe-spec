(* The lazy game Δ2 of A.5: the forward and backward chains of every password, their invariants,
   the bad events and the potentials of Lemmas K2 (Cross) and K3 (DESIGN-NOTES A.5). *)
require import AllCore List Distr DBool DInterval FMap IntDiv StdBigop Xreal.
require import Suite3 Chain Collision KnownPair.
require RealSeries DProd Mu_mem.
import W128 StdBigop.Bigreal.BRA.

(* Δ2 run lazily: P is drawn first and not used during the run, Y is uniform, and after the
   adversary halts the forward chain of P from X and then the backward chain from Y are evaluated. *)
module KPGame (A : AdvKP) = {
  var out : pw
  proc main(x : state) : unit = {
    var p, y, xf, xb;
    R.RO.init();
    Count(Mon2).init();
    p <$ dP;
    y <$ dstate;
    Fwd.init(x);
    Bwd.init(y);
    Mon2.inrun <- true; Mon2.log <- []; Mon2.bn <- 0;
    out <@ A(Count(Mon2)).guess(x, y);
    Mon2.inrun <- false;
    Fwd.p <- p; Bwd.p <- p;
    xf <@ Net(Mon2).enc(p, x);
    xb <@ Net(Mon2).dec(p, y);
  }
}.

(* ---- The invariants of the known-pair game ----------------------------------------------- *)
lemma inv_init_f p x : inv false true empty [] 0 p (cfwd x) (cfwd x).
proof.
apply invI.
- by move=> z.
- by move=> _ z; rewrite mem_empty.
- by [].
- exact shape_fwd.
- by move=> _ t.
- by move=> _; rewrite /stopped mem_empty.
- by rewrite /cfwd.
- by move=> _ t; rewrite /cfwd /= /#.
by move=> _; apply determined_init; rewrite /stopped mem_empty.
qed.

(* The forward chain stands at round i with state x, before its last point c is answered. *)
op atf (w : cst) (i : int) (x : state) (c : point) =
  !w.`fin /\ w.`ri = i /\ w.`cur = x.`2 /\ w.`oth = x.`1 /\ last witness w.`chain = c.

lemma stepBf p (w w' : cst) i (x : state) r (m : (point, ans) fmap) :
  atf w i x (PB (rd i, x.`2)) => strip w' = strip (cstep false p w (PB (rd i, x.`2)) true r [] m) =>
  atf w' i x (PA (p, salt_of r)).
proof.
move=> [hf [hri [hc [ho hl]]]] /strip_eq; rewrite /cstep hf hl /= /push /=.
by rewrite /atf => -[-> [-> [-> [-> [-> _]]]]]; rewrite last_rcons hf hri hc ho.
qed.

lemma stepAf p (w w' : cst) i (x : state) s r (m : (point, ans) fmap) :
  atf w i x (PA (p, s)) => strip w' = strip (cstep false p w (PA (p, s)) true r [] m) =>
  atf w' i x (PH (key_of r, rd i, x.`2)).
proof.
move=> [hf [hri [hc [ho hl]]]] /strip_eq; rewrite /cstep hf hl /= /push /=.
by rewrite /atf => -[-> [-> [-> [-> [-> _]]]]]; rewrite last_rcons hf hri hc ho.
qed.

lemma stepHf p (w w' : cst) i (x : state) k r (m : (point, ans) fmap) :
  atf w i x (PH (k, rd i, x.`2)) => strip w' = strip (cstep false p w (PH (k, rd i, x.`2)) true r [] m) =>
  (i < 11 => atf w' (i + 1) (round (mask_of r) x) (PB (rd (i + 1), (round (mask_of r) x).`2))) /\
  (!(i < 11) => w'.`fin /\ w'.`xs = round (mask_of r) x).
proof.
move=> [hf [hri [hc [ho hl]]]] /strip_eq; rewrite /cstep hf hl /= hri.
case: (i < 11) => hi /=.
- by rewrite /push /atf /= => -[-> [-> [-> [-> [-> _]]]]]; rewrite last_rcons /round hc ho.
by move=> [_ [-> [_ [_ [_ ->]]]]]; rewrite /round hc ho.
qed.

(* The invariant of the run, for both chains of every password. *)
op irun2 (inrun : bool) (m : (point, ans) fmap) (log : (point * int) list) (bn : int) (x y : state)
         (fs bs : pw -> cst) =
  inrun /\ (forall w, inv false true m log bn w (cfwd x) (fs w)) /\
  (forall w, inv true true m log bn w (cbwd y) (bs w)).

lemma query_spec2 inr m0 l0 b0 fs0 bs0 c0 o0 :
  hoare [Mon2.query : Mon2.inrun = inr /\ R.RO.m = m0 /\ Mon2.log = l0 /\ Mon2.bn = b0 /\
                      Fwd.sts = fs0 /\ Bwd.sts = bs0 /\ c = c0 /\ Fwd.odd = o0 ==>
    Mon2.inrun = inr /\ Mon2.bn = b0 /\
    R.RO.m = (if c0 \in m0 then m0 else m0.[c0 <- res]) /\ (c0 \in m0 => res = oget m0.[c0]) /\
    Mon2.log = (if inr then rcons l0 (c0, b0) else l0) /\
    Fwd.sts = (fun w => cstep false w (fs0 w) c0 (c0 \notin m0) res [] R.RO.m) /\
    Bwd.sts = (fun w => cstep true w (bs0 w) c0 (c0 \notin m0) res [] R.RO.m) /\
    Fwd.odd = (o0 \/ !inr /\ c0 \notin m0 /\ oddq c0 (fs0 Fwd.p) (bs0 Bwd.p))].
proof. by proc; inline *; auto => />; smt(get_set_sameE). qed.

(* One call of the adversary: a batch of its own and one answer. *)
lemma irun2_call (m m' : (point, ans) fmap) log bn x y fs bs fs' bs' c r :
  irun2 true m log bn x y fs bs =>
  m' = (if c \in m then m else m.[c <- r]) =>
  fs' = (fun w => cstep false w (fs w) c (c \notin m) r [] m') =>
  bs' = (fun w => cstep true w (bs w) c (c \notin m) r [] m') =>
  irun2 true m' (rcons log (c, bn + 1)) (bn + 1) x y fs' bs'.
proof.
move=> [_ [hf hb]] hm hfs hbs; rewrite /irun2 /=; split=> w.
- have [hI hlat] := inv_bump false m log bn w (cfwd x) (fs w) [c] (hf w).
  have [] // := inv_step false true m m' log (rcons log (c, bn + 1)) (bn + 1) w (cfwd x) (fs w) (fs' w)
                  c r [] hI _ hm _ _; 1: by move=> _; apply hlat.
  + by simplify.
  by rewrite hfs.
have [hI hlat] := inv_bump true m log bn w (cbwd y) (bs w) [c] (hb w).
have [] // := inv_step true true m m' log (rcons log (c, bn + 1)) (bn + 1) w (cbwd y) (bs w) (bs' w)
                c r [] hI _ hm _ _; 1: by move=> _; apply hlat.
- by simplify.
by rewrite hbs.
qed.

lemma mon2_a_run : hoare [Mon2.a :
  irun2 Mon2.inrun R.RO.m Mon2.log Mon2.bn Fwd.x Bwd.y Fwd.sts Bwd.sts /\ !Fwd.odd ==>
  irun2 Mon2.inrun R.RO.m Mon2.log Mon2.bn Fwd.x Bwd.y Fwd.sts Bwd.sts /\ !Fwd.odd].
proof.
proc; ecall (query_spec2 Mon2.inrun R.RO.m Mon2.log Mon2.bn Fwd.sts Bwd.sts (PA (p, s)) Fwd.odd).
auto => &hr [hI hod] /= r o' bs' fs' log' m' [hm [_ [hl [hfs [hbs ho]]]]].
have hi : Mon2.inrun{hr} by case: hI.
rewrite ho hod hi /=.
by move: hI; rewrite hl hi /= => hI; apply (irun2_call _ _ _ _ _ _ _ _ _ _ _ r hI hm hfs hbs).
qed.

lemma mon2_b_run : hoare [Mon2.b :
  irun2 Mon2.inrun R.RO.m Mon2.log Mon2.bn Fwd.x Bwd.y Fwd.sts Bwd.sts /\ !Fwd.odd ==>
  irun2 Mon2.inrun R.RO.m Mon2.log Mon2.bn Fwd.x Bwd.y Fwd.sts Bwd.sts /\ !Fwd.odd].
proof.
proc; ecall (query_spec2 Mon2.inrun R.RO.m Mon2.log Mon2.bn Fwd.sts Bwd.sts (PB (i, x)) Fwd.odd).
auto => &hr [hI hod] /= r o' bs' fs' log' m' [hm [_ [hl [hfs [hbs ho]]]]].
have hi : Mon2.inrun{hr} by case: hI.
rewrite ho hod hi /=.
by move: hI; rewrite hl hi /= => hI; apply (irun2_call _ _ _ _ _ _ _ _ _ _ _ r hI hm hfs hbs).
qed.

lemma mon2_h_run : hoare [Mon2.h :
  irun2 Mon2.inrun R.RO.m Mon2.log Mon2.bn Fwd.x Bwd.y Fwd.sts Bwd.sts /\ !Fwd.odd ==>
  irun2 Mon2.inrun R.RO.m Mon2.log Mon2.bn Fwd.x Bwd.y Fwd.sts Bwd.sts /\ !Fwd.odd].
proof.
proc; ecall (query_spec2 Mon2.inrun R.RO.m Mon2.log Mon2.bn Fwd.sts Bwd.sts (PH (k, i, x)) Fwd.odd).
auto => &hr [hI hod] /= r o' bs' fs' log' m' [hm [_ [hl [hfs [hbs ho]]]]].
have hi : Mon2.inrun{hr} by case: hI.
rewrite ho hod hi /=.
by move: hI; rewrite hl hi /= => hI; apply (irun2_call _ _ _ _ _ _ _ _ _ _ _ r hI hm hfs hbs).
qed.

(* A complete chain does not move. *)
lemma fin_step bwd p st c fresh r pend m : st.`fin => cstep bwd p st c fresh r pend m = st.
proof. by rewrite /cstep => ->. qed.

(* Without Early, a fresh query at the table's chain is the bookkeeping's last point. *)
lemma fresh_last bwd p m log bn st0 st j c : inv bwd false m log bn p st0 st => !st.`early => 0 <= j =>
  tracks bwd p m st0 j => !(iter j (adv bwd p m) st0).`fin => last witness (iter j (adv bwd p m) st0).`chain = c =>
  c \notin m => last witness st.`chain = c /\ !st.`fin.
proof.
move=> [_ [_ [_ hne]]] hea hj htr hfin hl hc; have [_ [_ [_ [_ hdet]]]] := hne hea.
have hs : stopped m (iter j (adv bwd p m) st0) by rewrite /stopped hl hc.
by have /strip_eq [-> [-> _]] := determined_end _ _ _ _ _ _ hdet hj htr hs; rewrite hl hfin.
qed.

lemma oddq_enc p m log bn x f b j c : inv false false m log bn p (cfwd x) f => 0 <= j =>
  tracks false p m (cfwd x) j => !(iter j (adv false p m) (cfwd x)).`fin =>
  last witness (iter j (adv false p m) (cfwd x)).`chain = c => c \notin m => !oddq c f b.
proof.
move=> hI hj htr hfin hl hc; rewrite /oddq; case: (f.`early) => //= hea.
by have [-> ->] := fresh_last _ _ _ _ _ _ _ _ _ hI hea hj htr hfin hl hc.
qed.

lemma oddq_dec p m log bn y f b j c : (!f.`early => f.`fin) => inv true false m log bn p (cbwd y) b => 0 <= j =>
  tracks true p m (cbwd y) j => !(iter j (adv true p m) (cbwd y)).`fin =>
  last witness (iter j (adv true p m) (cbwd y)).`chain = c => c \notin m => !oddq c f b.
proof.
move=> hff hI hj htr hfin hl hc; rewrite /oddq; case: (f.`early) => //= hea; rewrite hff //=.
case: (b.`early) => //= heb.
by have [-> ->] := fresh_last _ _ _ _ _ _ _ _ _ hI heb hj htr hfin hl hc.
qed.

(* The finalization evaluates the forward chain of P from X ... *)
lemma enc2_spec : hoare [Net(Mon2).enc :
  !Mon2.inrun /\ p = Fwd.p /\ x = Fwd.x /\
  inv false false R.RO.m Mon2.log Mon2.bn Fwd.p (cfwd Fwd.x) (Fwd.sts Fwd.p) /\
  inv true false R.RO.m Mon2.log Mon2.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\ !Fwd.odd ==>
  !Mon2.inrun /\
  inv false false R.RO.m Mon2.log Mon2.bn Fwd.p (cfwd Fwd.x) (Fwd.sts Fwd.p) /\
  inv true false R.RO.m Mon2.log Mon2.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
  (!(Fwd.sts Fwd.p).`early => (Fwd.sts Fwd.p).`fin /\ res = (Fwd.sts Fwd.p).`xs) /\ !Fwd.odd].
proof.
proc; inline Mon2.a Mon2.b Mon2.h.
while (!Mon2.inrun /\ p = Fwd.p /\ 0 <= i <= 12 /\
       inv false false R.RO.m Mon2.log Mon2.bn Fwd.p (cfwd Fwd.x) (Fwd.sts Fwd.p) /\
       inv true false R.RO.m Mon2.log Mon2.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
       tracks false Fwd.p R.RO.m (cfwd Fwd.x) (3 * i) /\
       (i < 12 => atf (iter (3 * i) (adv false Fwd.p R.RO.m) (cfwd Fwd.x)) i x (PB (rd i, x.`2))) /\
       (i = 12 => (iter (3 * i) (adv false Fwd.p R.RO.m) (cfwd Fwd.x)).`fin /\
                  (iter (3 * i) (adv false Fwd.p R.RO.m) (cfwd Fwd.x)).`xs = x) /\ !Fwd.odd).
- seq 5 : (!Mon2.inrun /\ p = Fwd.p /\ 0 <= i < 12 /\
           inv false false R.RO.m Mon2.log Mon2.bn Fwd.p (cfwd Fwd.x) (Fwd.sts Fwd.p) /\
           inv true false R.RO.m Mon2.log Mon2.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
           tracks false Fwd.p R.RO.m (cfwd Fwd.x) (3 * i + 1) /\
           atf (iter (3 * i + 1) (adv false Fwd.p R.RO.m) (cfwd Fwd.x)) i x (PA (Fwd.p, s)) /\ !Fwd.odd).
  + wp; ecall (query_spec2 Mon2.inrun R.RO.m Mon2.log Mon2.bn Fwd.sts Bwd.sts (PB (rd i, x.`2)) Fwd.odd); auto.
    move=> &hr [[hi [hp [hrng [hinvf [hinvb [htr [hat [_ hod]]]]]]]] hc] /= r bs' o' fs' log' m' [hm [hr' [hl [hfs [hbs ho]]]]].
    have -> : log' = Mon2.log{hr} by rewrite hl hi.
    have hat' := hat _; 1: smt().
    have [hfin [_ [_ [_ hlast]]]] := hat'.
    have hj : 0 <= 3 * i{hr} by smt().
    have hno : !o' by rewrite ho hod /=; apply/negP => -[_ [hc' hq]]; by have := oddq_enc _ _ _ _ _ _ (Bwd.sts{hr} Bwd.p{hr}) _ _ hinvf hj htr hfin hlast hc'; rewrite hq.
    have [htr' hw] := iter_query false Fwd.p{hr} _ m' _ _ _ r hj htr hfin hlast hm hr'.
    have hstf : fs' Fwd.p{hr} = cstep false Fwd.p{hr} (Fwd.sts{hr} Fwd.p{hr}) (PB (rd i{hr}, x{hr}.`2))
                  (PB (rd i{hr}, x{hr}.`2) \notin R.RO.m{hr}) r [] m' by rewrite hfs.
    have hstb : bs' Bwd.p{hr} = cstep true Bwd.p{hr} (Bwd.sts{hr} Bwd.p{hr}) (PB (rd i{hr}, x{hr}.`2))
                  (PB (rd i{hr}, x{hr}.`2) \notin R.RO.m{hr}) r [] m' by rewrite hbs.
    rewrite hi hp hno /= (inv_step_off false _ m' _ _ (Mon2.bn{hr} + 1) _ _ _ _ _ r [] hinvf hm hstf).
    rewrite (inv_step_off true _ m' _ _ (Mon2.bn{hr} + 1) _ _ _ _ _ r [] hinvb hm hstb) htr' /=.
    by split; [smt() | exact (stepBf _ _ _ _ _ _ _ hat' hw)].
  seq 5 : (!Mon2.inrun /\ p = Fwd.p /\ 0 <= i < 12 /\
           inv false false R.RO.m Mon2.log Mon2.bn Fwd.p (cfwd Fwd.x) (Fwd.sts Fwd.p) /\
           inv true false R.RO.m Mon2.log Mon2.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
           tracks false Fwd.p R.RO.m (cfwd Fwd.x) (3 * i + 1 + 1) /\
           atf (iter (3 * i + 1 + 1) (adv false Fwd.p R.RO.m) (cfwd Fwd.x)) i x (PH (k, rd i, x.`2)) /\ !Fwd.odd).
  + wp; ecall (query_spec2 Mon2.inrun R.RO.m Mon2.log Mon2.bn Fwd.sts Bwd.sts (PA (Fwd.p, s)) Fwd.odd); auto.
    move=> &hr [hi [hp [hrng [hinvf [hinvb [htr [hat hod]]]]]]] /=; split; 1: exact hp.
    move=> _ r bs' o' fs' log' m' [hm [hr' [hl [hfs [hbs ho]]]]].
    have -> : log' = Mon2.log{hr} by rewrite hl hi.
    have [hfin [_ [_ [_ hlast]]]] := hat.
    have hj : 0 <= 3 * i{hr} + 1 by smt().
    have hno : !o' by rewrite ho hod /=; apply/negP => -[_ [hc' hq]]; by have := oddq_enc _ _ _ _ _ _ (Bwd.sts{hr} Bwd.p{hr}) _ _ hinvf hj htr hfin hlast hc'; rewrite hq.
    have [htr' hw] := iter_query false Fwd.p{hr} _ m' _ _ _ r hj htr hfin hlast hm hr'.
    have hstf : fs' Fwd.p{hr} = cstep false Fwd.p{hr} (Fwd.sts{hr} Fwd.p{hr}) (PA (Fwd.p{hr}, s{hr}))
                  (PA (Fwd.p{hr}, s{hr}) \notin R.RO.m{hr}) r [] m' by rewrite hfs.
    have hstb : bs' Bwd.p{hr} = cstep true Bwd.p{hr} (Bwd.sts{hr} Bwd.p{hr}) (PA (Fwd.p{hr}, s{hr}))
                  (PA (Fwd.p{hr}, s{hr}) \notin R.RO.m{hr}) r [] m' by rewrite hbs.
    move: htr' hw; rewrite (_ : 3 * i{hr} + 1 + 1 = 3 * i{hr} + 2) 1:/# => htr' hw.
    rewrite hi hp hno /= (inv_step_off false _ m' _ _ (Mon2.bn{hr} + 1) _ _ _ _ _ r [] hinvf hm hstf).
    rewrite (inv_step_off true _ m' _ _ (Mon2.bn{hr} + 1) _ _ _ _ _ r [] hinvb hm hstb) htr' /=.
    by split; [smt() | exact (stepAf _ _ _ _ _ _ _ _ hat hw)].
  wp; ecall (query_spec2 Mon2.inrun R.RO.m Mon2.log Mon2.bn Fwd.sts Bwd.sts (PH (k, rd i, x.`2)) Fwd.odd); auto.
  move=> &hr [hi [hp [hrng [hinvf [hinvb [htr [hat hod]]]]]]] /= r bs' o' fs' log' m' [hm [hr' [hl [hfs [hbs ho]]]]].
  have -> : log' = Mon2.log{hr} by rewrite hl hi.
  have [hfin [_ [_ [_ hlast]]]] := hat.
  have hj : 0 <= 3 * i{hr} + 2 by smt().
  have hno : !o' by rewrite ho hod /=; apply/negP => -[_ [hc' hq]]; by have := oddq_enc _ _ _ _ _ _ (Bwd.sts{hr} Bwd.p{hr}) _ _ hinvf hj htr hfin hlast hc'; rewrite hq.
  have [htr' hw] := iter_query false Fwd.p{hr} _ m' _ _ _ r hj htr hfin hlast hm hr'.
  have hstf : fs' Fwd.p{hr} = cstep false Fwd.p{hr} (Fwd.sts{hr} Fwd.p{hr}) (PH (k{hr}, rd i{hr}, x{hr}.`2))
                (PH (k{hr}, rd i{hr}, x{hr}.`2) \notin R.RO.m{hr}) r [] m' by rewrite hfs.
  have hstb : bs' Bwd.p{hr} = cstep true Bwd.p{hr} (Bwd.sts{hr} Bwd.p{hr}) (PH (k{hr}, rd i{hr}, x{hr}.`2))
                (PH (k{hr}, rd i{hr}, x{hr}.`2) \notin R.RO.m{hr}) r [] m' by rewrite hbs.
  have [hB hF] := stepHf _ _ _ _ _ _ _ _ hat hw.
  move: htr' hB hF; rewrite (_ : 3 * i{hr} + 2 + 1 = 3 * (i{hr} + 1)) 1:/# => htr' hB hF.
  rewrite hi hp hno /= (inv_step_off false _ m' _ _ (Mon2.bn{hr} + 1) _ _ _ _ _ r [] hinvf hm hstf).
  rewrite (inv_step_off true _ m' _ _ (Mon2.bn{hr} + 1) _ _ _ _ _ r [] hinvb hm hstb) htr' /=.
  split; 1: smt().
  by split=> h; [apply hB | apply hF]; smt().
auto => &hr [hi [hp [hx [hinvf [hinvb hod]]]]]; split.
- rewrite hi hp hinvf hinvb hod /=; split; 1: by rewrite /tracks /#.
  by rewrite iter0 // /atf /cfwd hx.
move=> o fs bn log bs m i x' hni [_ [_ [hrng [hinvf' [hinvb' [htr [_ [hend hod']]]]]]]].
rewrite hi hinvf' hinvb' hod' /= => hea.
have [hfin hxs] := hend _; 1: smt().
have [_ [_ [_ hne]]] := hinvf'; have [_ [_ [_ [_ hdet]]]] := hne hea.
have hj : 0 <= 3 * i by smt().
have hs : stopped m (iter (3 * i) (adv false Fwd.p{hr} m) (cfwd Fwd.x{hr})) by rewrite /stopped hfin.
have := determined_end _ _ _ _ _ _ hdet hj htr hs.
by move=> /strip_eq [_ [-> [_ [_ [_ ->]]]]]; rewrite hfin hxs.
qed.

(* ... and then the backward chain from Y; a complete forward chain stays complete. *)
lemma dec2_spec : hoare [Net(Mon2).dec :
  !Mon2.inrun /\ p = Bwd.p /\ y = Bwd.y /\ (!(Fwd.sts Fwd.p).`early => (Fwd.sts Fwd.p).`fin) /\
  inv false false R.RO.m Mon2.log Mon2.bn Fwd.p (cfwd Fwd.x) (Fwd.sts Fwd.p) /\
  inv true false R.RO.m Mon2.log Mon2.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\ !Fwd.odd ==>
  !Mon2.inrun /\ (!(Fwd.sts Fwd.p).`early => (Fwd.sts Fwd.p).`fin) /\
  inv false false R.RO.m Mon2.log Mon2.bn Fwd.p (cfwd Fwd.x) (Fwd.sts Fwd.p) /\
  inv true false R.RO.m Mon2.log Mon2.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
  (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs) /\ !Fwd.odd].
proof.
proc; inline Mon2.a Mon2.b Mon2.h.
while (!Mon2.inrun /\ p = Bwd.p /\ -1 <= i <= 11 /\ (!(Fwd.sts Fwd.p).`early => (Fwd.sts Fwd.p).`fin) /\
       inv false false R.RO.m Mon2.log Mon2.bn Fwd.p (cfwd Fwd.x) (Fwd.sts Fwd.p) /\
       inv true false R.RO.m Mon2.log Mon2.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
       tracks true Bwd.p R.RO.m (cbwd Bwd.y) (3 * (11 - i)) /\
       (0 <= i => at (iter (3 * (11 - i)) (adv true Bwd.p R.RO.m) (cbwd Bwd.y)) i y (PB (rd i, y.`1))) /\
       (i = -1 => (iter (3 * (11 - i)) (adv true Bwd.p R.RO.m) (cbwd Bwd.y)).`fin /\
                  (iter (3 * (11 - i)) (adv true Bwd.p R.RO.m) (cbwd Bwd.y)).`xs = y) /\ !Fwd.odd).
- seq 5 : (!Mon2.inrun /\ p = Bwd.p /\ 0 <= i <= 11 /\ (!(Fwd.sts Fwd.p).`early => (Fwd.sts Fwd.p).`fin) /\
           inv false false R.RO.m Mon2.log Mon2.bn Fwd.p (cfwd Fwd.x) (Fwd.sts Fwd.p) /\
           inv true false R.RO.m Mon2.log Mon2.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
           tracks true Bwd.p R.RO.m (cbwd Bwd.y) (3 * (11 - i) + 1) /\
           at (iter (3 * (11 - i) + 1) (adv true Bwd.p R.RO.m) (cbwd Bwd.y)) i y (PA (Bwd.p, s)) /\ !Fwd.odd).
  + wp; ecall (query_spec2 Mon2.inrun R.RO.m Mon2.log Mon2.bn Fwd.sts Bwd.sts (PB (rd i, y.`1)) Fwd.odd); auto.
    move=> &hr [[hi [hp [hrng [hff [hinvf [hinvb [htr [hat [_ hod]]]]]]]]] hc] /= r bs' o' fs' log' m' [hm [hr' [hl [hfs [hbs ho]]]]].
    have -> : log' = Mon2.log{hr} by rewrite hl hi.
    have hat' := hat hc; have [hfin [_ [_ [_ hlast]]]] := hat'.
    have hj : 0 <= 3 * (11 - i{hr}) by smt().
    have hno : !o' by rewrite ho hod /=; apply/negP => -[_ [hc' hq]]; by have := oddq_dec _ _ _ _ _ (Fwd.sts{hr} Fwd.p{hr}) _ _ _ hff hinvb hj htr hfin hlast hc'; rewrite hq.
    have [htr' hw] := iter_query true Bwd.p{hr} _ m' _ _ _ r hj htr hfin hlast hm hr'.
    have hstf : fs' Fwd.p{hr} = cstep false Fwd.p{hr} (Fwd.sts{hr} Fwd.p{hr}) (PB (rd i{hr}, y{hr}.`1))
                  (PB (rd i{hr}, y{hr}.`1) \notin R.RO.m{hr}) r [] m' by rewrite hfs.
    have hstb : bs' Bwd.p{hr} = cstep true Bwd.p{hr} (Bwd.sts{hr} Bwd.p{hr}) (PB (rd i{hr}, y{hr}.`1))
                  (PB (rd i{hr}, y{hr}.`1) \notin R.RO.m{hr}) r [] m' by rewrite hbs.
    rewrite hi hp hno /= (inv_step_off false _ m' _ _ (Mon2.bn{hr} + 1) _ _ _ _ _ r [] hinvf hm hstf).
    rewrite (inv_step_off true _ m' _ _ (Mon2.bn{hr} + 1) _ _ _ _ _ r [] hinvb hm hstb) htr' /=.
    split; 1: smt().
    split; 1: by rewrite hstf; smt(fin_step early_mono).
    exact (stepB _ _ _ _ _ _ _ hat' hw).
  seq 5 : (!Mon2.inrun /\ p = Bwd.p /\ 0 <= i <= 11 /\ (!(Fwd.sts Fwd.p).`early => (Fwd.sts Fwd.p).`fin) /\
           inv false false R.RO.m Mon2.log Mon2.bn Fwd.p (cfwd Fwd.x) (Fwd.sts Fwd.p) /\
           inv true false R.RO.m Mon2.log Mon2.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
           tracks true Bwd.p R.RO.m (cbwd Bwd.y) (3 * (11 - i) + 1 + 1) /\
           at (iter (3 * (11 - i) + 1 + 1) (adv true Bwd.p R.RO.m) (cbwd Bwd.y)) i y (PH (k, rd i, y.`1)) /\ !Fwd.odd).
  + wp; ecall (query_spec2 Mon2.inrun R.RO.m Mon2.log Mon2.bn Fwd.sts Bwd.sts (PA (Bwd.p, s)) Fwd.odd); auto.
    move=> &hr [hi [hp [hrng [hff [hinvf [hinvb [htr [hat hod]]]]]]]] /=; split; 1: exact hp.
    move=> _ r bs' o' fs' log' m' [hm [hr' [hl [hfs [hbs ho]]]]].
    have -> : log' = Mon2.log{hr} by rewrite hl hi.
    have [hfin [_ [_ [_ hlast]]]] := hat.
    have hj : 0 <= 3 * (11 - i{hr}) + 1 by smt().
    have hno : !o' by rewrite ho hod /=; apply/negP => -[_ [hc' hq]]; by have := oddq_dec _ _ _ _ _ (Fwd.sts{hr} Fwd.p{hr}) _ _ _ hff hinvb hj htr hfin hlast hc'; rewrite hq.
    have [htr' hw] := iter_query true Bwd.p{hr} _ m' _ _ _ r hj htr hfin hlast hm hr'.
    have hstf : fs' Fwd.p{hr} = cstep false Fwd.p{hr} (Fwd.sts{hr} Fwd.p{hr}) (PA (Bwd.p{hr}, s{hr}))
                  (PA (Bwd.p{hr}, s{hr}) \notin R.RO.m{hr}) r [] m' by rewrite hfs.
    have hstb : bs' Bwd.p{hr} = cstep true Bwd.p{hr} (Bwd.sts{hr} Bwd.p{hr}) (PA (Bwd.p{hr}, s{hr}))
                  (PA (Bwd.p{hr}, s{hr}) \notin R.RO.m{hr}) r [] m' by rewrite hbs.
    move: htr' hw; rewrite (_ : 3 * (11 - i{hr}) + 1 + 1 = 3 * (11 - i{hr}) + 2) 1:/# => htr' hw.
    rewrite hi hp hno /= (inv_step_off false _ m' _ _ (Mon2.bn{hr} + 1) _ _ _ _ _ r [] hinvf hm hstf).
    rewrite (inv_step_off true _ m' _ _ (Mon2.bn{hr} + 1) _ _ _ _ _ r [] hinvb hm hstb) htr' /=.
    split; 1: smt().
    split; 1: by rewrite hstf; smt(fin_step early_mono).
    exact (stepA _ _ _ _ _ _ _ _ hat hw).
  wp; ecall (query_spec2 Mon2.inrun R.RO.m Mon2.log Mon2.bn Fwd.sts Bwd.sts (PH (k, rd i, y.`1)) Fwd.odd); auto.
  move=> &hr [hi [hp [hrng [hff [hinvf [hinvb [htr [hat hod]]]]]]]] /= r bs' o' fs' log' m' [hm [hr' [hl [hfs [hbs ho]]]]].
  have -> : log' = Mon2.log{hr} by rewrite hl hi.
  have [hfin [_ [_ [_ hlast]]]] := hat.
  have hj : 0 <= 3 * (11 - i{hr}) + 2 by smt().
  have hno : !o' by rewrite ho hod /=; apply/negP => -[_ [hc' hq]]; by have := oddq_dec _ _ _ _ _ (Fwd.sts{hr} Fwd.p{hr}) _ _ _ hff hinvb hj htr hfin hlast hc'; rewrite hq.
  have [htr' hw] := iter_query true Bwd.p{hr} _ m' _ _ _ r hj htr hfin hlast hm hr'.
  have hstf : fs' Fwd.p{hr} = cstep false Fwd.p{hr} (Fwd.sts{hr} Fwd.p{hr}) (PH (k{hr}, rd i{hr}, y{hr}.`1))
                (PH (k{hr}, rd i{hr}, y{hr}.`1) \notin R.RO.m{hr}) r [] m' by rewrite hfs.
  have hstb : bs' Bwd.p{hr} = cstep true Bwd.p{hr} (Bwd.sts{hr} Bwd.p{hr}) (PH (k{hr}, rd i{hr}, y{hr}.`1))
                (PH (k{hr}, rd i{hr}, y{hr}.`1) \notin R.RO.m{hr}) r [] m' by rewrite hbs.
  have [hB hF] := stepH _ _ _ _ _ _ _ _ hat hw.
  move: htr' hB hF; rewrite (_ : 3 * (11 - i{hr}) + 2 + 1 = 3 * (11 - i{hr}) + 3) 1:/# => htr' hB hF.
  rewrite (_ : 3 * (11 - (i{hr} - 1)) = 3 * (11 - i{hr}) + 3) 1:/#.
  rewrite hi hp hno /= (inv_step_off false _ m' _ _ (Mon2.bn{hr} + 1) _ _ _ _ _ r [] hinvf hm hstf).
  rewrite (inv_step_off true _ m' _ _ (Mon2.bn{hr} + 1) _ _ _ _ _ r [] hinvb hm hstb) htr' /=.
  split; 1: smt().
  split; 1: by rewrite hstf; smt(fin_step early_mono).
  by split=> h; [apply hB | apply hF]; smt().
auto => &hr [hi [hp [hy [hff [hinvf [hinvb hod]]]]]]; split.
- have ht : tracks true Bwd.p{hr} R.RO.m{hr} (cbwd Bwd.y{hr}) (3 * (11 - 11)) by rewrite /tracks /#.
  by rewrite iter0 /=; smt().
move=> o fs bn log bs m i y' hni [_ [_ [hrng [hff' [hinvf' [hinvb' [htr [_ [hend hod']]]]]]]]].
do 4!(split; 1: done); split; 2: exact hod'; move=> hea.
have [hfin hxs] := hend _; 1: smt().
have [_ [_ [_ hne]]] := hinvb'; have [_ [_ [_ [_ hdet]]]] := hne hea.
have hj : 0 <= 3 * (11 - i) by smt().
have hs : stopped m (iter (3 * (11 - i)) (adv true Bwd.p{hr} m) (cbwd Bwd.y{hr})) by rewrite /stopped hfin.
have := determined_end _ _ _ _ _ _ hdet hj htr hs.
by move=> /strip_eq [_ [-> [_ [_ [_ ->]]]]]; rewrite hfin hxs.
qed.

(* ---- The positions of the points of a chain ------------------------------------------------ *)
(* A chain is never empty, and its points come by position: B, A, H. *)
op typed (chain : point list) = chain <> [] /\ forall t, 0 <= t < size chain => pos (nth witness chain t) = t %% 3.

lemma typed_cstep bwd p st c fresh r pend m : typed st.`chain => typed (cstep bwd p st c fresh r pend m).`chain.
proof.
move=> [hne ht]; rewrite /cstep /push.
case: (fresh /\ !st.`fin /\ last witness st.`chain = c) => // -[_ [_ hl]] /=.
have hlast : pos c = (size st.`chain - 1) %% 3.
- by rewrite -hl -(nth_last witness) ht; smt(size_ge0 size_eq0).
have hpush : forall q, pos q = (pos c + 1) %% 3 => typed (rcons st.`chain q).
- move=> q hq; split; 1: exact rcons_ne0.
  move=> t; rewrite size_rcons nth_rcons => hrange.
  case: (t < size st.`chain) => htl; 1: by apply ht; smt().
  by rewrite (_ : t = size st.`chain) 1:/# /= hq hlast; smt().
case: (isB c) => hB /=; 1: by apply hpush; rewrite (posB _ hB).
case: (isA c) => hA /=; 1: by apply hpush; rewrite (posA _ hA).
case: (if bwd then 0 < st.`ri else st.`ri < 11) => _ /=; 2: by split.
by apply hpush; rewrite (posH _ hA hB).
qed.

op tall (fs bs : pw -> cst) = forall w, typed (fs w).`chain /\ typed (bs w).`chain.

lemma typed_q : hoare [Mon2.query : tall Fwd.sts Bwd.sts ==> tall Fwd.sts Bwd.sts].
proof. by proc; inline *; auto => /> &hr h r _ w; smt(typed_cstep). qed.

lemma typed_a : hoare [Mon2.a : tall Fwd.sts Bwd.sts ==> tall Fwd.sts Bwd.sts].
proof. by proc; call typed_q; auto. qed.

lemma typed_b : hoare [Mon2.b : tall Fwd.sts Bwd.sts ==> tall Fwd.sts Bwd.sts].
proof. by proc; call typed_q; auto. qed.

lemma typed_h : hoare [Mon2.h : tall Fwd.sts Bwd.sts ==> tall Fwd.sts Bwd.sts].
proof. by proc; call typed_q; auto. qed.

(* If the adversary queried a point of an ordered chain, it queried every earlier point. *)
lemma ordered_prefix log (chain : point list) : ordered log chain =>
  forall s t, 0 <= s <= t < size chain => nth witness chain t \in map fst log => nth witness chain s \in map fst log.
proof.
rewrite /ordered => hord.
have h : forall k, 0 <= k => forall t, k <= t < size chain => nth witness chain t \in map fst log =>
                   nth witness chain (t - k) \in map fst log.
- elim=> [t _ h0 | k ge0k ih t ht h0]; 1: by rewrite (_ : t - 0 = t) 1:/#.
  have h1 := ih t _ h0; 1: smt().
  have [+ _] := hord (t - k) _ h1; 1: smt().
  by rewrite (_ : t - k - 1 = t - (k + 1)) 1:/#.
move=> s t hst h0; have := h (t - s) _ t _ h0; 1,2: smt().
by rewrite (_ : t - (t - s) = s) 1:/#.
qed.

(* A predicate closed downwards on 0 .. n-1 holds exactly below its count. *)
lemma count_down (P : int -> bool) n : 0 <= n => (forall i j, 0 <= i <= j < n => P j => P i) =>
  forall j, 0 <= j < n => P j <=> j < count P (iota_ 0 n).
proof.
elim: n => [_ j | n ge0n ih hd j hj]; 1: smt().
have ih' := ih _; 1: by move=> i k hik; apply hd; smt().
have hc : count P (iota_ 0 n) <= n by have := count_size P (iota_ 0 n); rewrite size_iota; smt().
rewrite iotaSr // count_rcons1 /=.
case: (P n) => hPn.
- have hall : count P (iota_ 0 n) = n.
  + case: (n = 0) => [h0 | hn0]; 1: smt(count_ge0).
    have h1 : P (n - 1) by apply (hd (n - 1) n); smt().
    have [h2 _] := ih' (n - 1) _; 1: smt().
    by have := h2 h1; smt().
  rewrite hall /b2i /=; split => _; 1: smt().
  by apply (hd j n); smt().
rewrite /b2i /=; case: (j = n) => [-> | hjn]; 1: smt().
by apply ih'; smt().
qed.

(* Bad_j: the adversary queried the forward H point of round j or the backward one of round j+1. *)
op badj (log : (point * int) list) (fc bc : point list) (j : int) =
  nth witness fc (3 * j + 2) \in map fst log \/ nth witness bc (3 * (10 - j) + 2) \in map fst log.
op nbad (log : (point * int) list) (fc bc : point list) = count (badj log fc bc) (iota_ 0 11).

(* Cross: a forward A point of round i equals a backward A point of a round i' <> i. *)
op cross (fc bc : point list) =
  exists i i', 0 <= i < 12 /\ 0 <= i' < 12 /\ i <> i' /\
               nth witness fc (3 * i + 1) = nth witness bc (3 * (11 - i') + 1).

(* Lemma K4, combinatorial part: with the counts f and b of queried forward and backward H points,
   n_bad <= min(11, f + b) and the adversary made at least min(12, f + b) distinct A queries with
   password p. *)
lemma K4_pure log (fc bc : point list) p :
  size fc = 36 => size bc = 36 => typed fc => typed bc => uniq fc => uniq bc =>
  ordered log fc => ordered log bc =>
  all (fun c => isA c => isApw p c) fc => all (fun c => isA c => isApw p c) bc =>
  !cross fc bc => nbad log fc bc <= min 11 (count (isApw p) (undup (map fst log))).
proof.
move=> hsf hsb [_ htf] [_ htb] huf hub hof hob haf hab hcr.
pose Qf := fun j => nth witness fc (3 * j + 2) \in map fst log.
pose Qb := fun k => nth witness bc (3 * k + 2) \in map fst log.
pose f := count Qf (iota_ 0 11).
pose b := count Qb (iota_ 0 11).
have hpf := ordered_prefix _ _ hof; have hpb := ordered_prefix _ _ hob.
have hF := count_down Qf 11 _ _; 1: done.
- by move=> i j hij hq; apply (hpf (3 * i + 2) (3 * j + 2)) => //; smt().
have hB := count_down Qb 11 _ _; 1: done.
- by move=> i j hij hq; apply (hpb (3 * i + 2) (3 * j + 2)) => //; smt().
have hf : 0 <= f <= 11 by rewrite /f; smt(count_ge0 count_size size_iota).
have hb : 0 <= b <= 11 by rewrite /b; smt(count_ge0 count_size size_iota).
(* n_bad <= 11 and n_bad <= f + b *)
have hn1 : nbad log fc bc <= 11 by rewrite /nbad; smt(count_size size_iota).
have hr : count (fun j => Qb (10 - j)) (iota_ 0 11) = b.
- rewrite /b; have <- : count Qb (map (fun j => 10 - j) (iota_ 0 11)) = count (fun j => Qb (10 - j)) (iota_ 0 11).
  + by rewrite count_map /preim.
  have hp : perm_eq (map (fun j => 10 - j) (iota_ 0 11)) (iota_ 0 11).
  + apply uniq_perm_eq; 2: exact iota_uniq.
    * by rewrite map_inj_in_uniq ?iota_uniq // /#.
    move=> x; rewrite mem_iota; split => [/mapP [j [/mem_iota ? ->]] /# | hx].
    by apply/mapP; exists (10 - x); rewrite mem_iota /#.
  by have [h _] := perm_eqP (map (fun j => 10 - j) (iota_ 0 11)) (iota_ 0 11); apply h.
have hn2 : nbad log fc bc <= f + b.
- rewrite /nbad (eq_count _ (predU Qf (fun j => Qb (10 - j)))).
  + by move=> j; rewrite /badj /predU /Qf /Qb.
  by rewrite count_predU hr; smt(count_ge0).
(* the distinct A queries with password p *)
pose b2 := min b (12 - f).
have hb2 : 0 <= b2 <= b /\ b2 <= 12 - f by rewrite /b2; smt().
pose L := map (fun i => nth witness fc (3 * i + 1)) (iota_ 0 f) ++ map (fun k => nth witness bc (3 * k + 1)) (iota_ 0 b2).
have hL : size L <= count (isApw p) (undup (map fst log)).
- rewrite -size_filter; apply uniq_leq_size.
  + rewrite cat_uniq; split.
    * rewrite map_inj_in_uniq ?iota_uniq // => i j /mem_iota hi /mem_iota hj /= heq.
      case: (i = j) => // hne; move/(nth_uniqP fc) : huf => h.
      by have := h (3 * i + 1) (3 * j + 1) _ _ _; smt().
    split.
    * apply/hasPn => c /mapP [k [/mem_iota hk ->]] /=; apply/negP => /mapP [i [/mem_iota hi heq]].
      apply hcr; exists i (11 - k); smt().
    rewrite map_inj_in_uniq ?iota_uniq // => i j /mem_iota hi /mem_iota hj /= heq.
    case: (i = j) => // hne; move/(nth_uniqP bc) : hub => h.
    by have := h (3 * i + 1) (3 * j + 1) _ _ _; smt().
  move=> c; rewrite mem_cat mem_filter mem_undup => -[/mapP [i [/mem_iota hi ->]] | /mapP [k [/mem_iota hk ->]]] /=.
  + have hA : isA (nth witness fc (3 * i + 1)) by have := htf (3 * i + 1) _; smt(posA posB posH).
    split; 1: by move/allP: haf => /(_ (nth witness fc (3 * i + 1)) _); [apply mem_nth; smt() | move=> /= /(_ hA)].
    have hq : Qf (f - 1) by rewrite hF; smt().
    by apply (hpf (3 * i + 1) (3 * (f - 1) + 2)); smt().
  have hA : isA (nth witness bc (3 * k + 1)) by have := htb (3 * k + 1) _; smt(posA posB posH).
  split; 1: by move/allP: hab => /(_ (nth witness bc (3 * k + 1)) _); [apply mem_nth; smt() | move=> /= /(_ hA)].
  have hq : Qb (b - 1) by rewrite hB; smt().
  by apply (hpb (3 * k + 1) (3 * (b - 1) + 2)); smt().
have hsL : size L = f + b2 by rewrite /L size_cat !size_map !size_iota /#.
smt().
qed.

(* ---- Without Early, the chains of the known-pair game follow the final table --------------- *)
(* A step of the bookkeeping keeps the chain or appends one point. *)
lemma adv_grow bwd p (m : (point, ans) fmap) st :
  (adv bwd p m st).`chain = st.`chain \/ exists q, (adv bwd p m st).`chain = rcons st.`chain q.
proof.
rewrite /adv /cstep /push; case: (stopped m st) => _ //=.
case: (st.`fin) => hf //=; case: (isB (last witness st.`chain)) => _ /=; 1: smt().
case: (isA (last witness st.`chain)) => _ /=; 1: smt().
by case: (if bwd then 0 < st.`ri else st.`ri < 11) => _ /=; smt().
qed.

lemma iter_nth bwd p (m : (point, ans) fmap) st0 k d : 0 <= k => 0 <= d =>
  size (iter k (adv bwd p m) st0).`chain <= size (iter (k + d) (adv bwd p m) st0).`chain /\
  forall i, 0 <= i < size (iter k (adv bwd p m) st0).`chain =>
    nth witness (iter (k + d) (adv bwd p m) st0).`chain i = nth witness (iter k (adv bwd p m) st0).`chain i.
proof.
move=> hk; elim: d => [|d hd [ih1 ih2]]; 1: smt().
rewrite (_ : k + (d + 1) = (k + d) + 1) 1:/# iterS 1:/#.
case: (adv_grow bwd p m (iter (k + d) (adv bwd p m) st0)) => [-> // | [q ->]].
by rewrite size_rcons; split => [/# | i hi]; rewrite nth_rcons; smt().
qed.

lemma shape_adv bwd p (m : (point, ans) fmap) st : shape bwd p st => shape bwd p (adv bwd p m st).
proof. by rewrite /adv; case: (stopped m st) => //= _; apply shape_cstep. qed.

lemma shape_iter bwd p (m : (point, ans) fmap) st0 k : 0 <= k => shape bwd p st0 =>
  shape bwd p (iter k (adv bwd p m) st0).
proof.
move=> hk h0; elim: k hk => [|k hk ih]; 1: by rewrite iter0.
by rewrite iterS //; apply shape_adv.
qed.

op tabf (m : (point, ans) fmap) : point -> ans = fun c => oget m.[c].

(* The three steps of round i of the forward chain on the table. *)
lemma fwd_round p x (m : (point, ans) fmap) i (w : state) : 0 <= i < 12 =>
  atf (iter (3 * i) (adv false p m) (cfwd x)) i w (PB (rd i, w.`2)) =>
  (forall k, 3 * i <= k < 3 * i + 2 => !stopped m (iter k (adv false p m) (cfwd x))) =>
  atf (iter (3 * i + 2) (adv false p m) (cfwd x)) i w
      (PH (key_of (tabf m (PA (p, salt_of (tabf m (PB (rd i, w.`2)))))), rd i, w.`2)) /\
  (!stopped m (iter (3 * i + 2) (adv false p m) (cfwd x)) => i < 11 =>
   atf (iter (3 * i + 3) (adv false p m) (cfwd x)) (i + 1)
       (round (mask (tabf m) p (rd i) w.`2) w) (PB (rd (i + 1), (round (mask (tabf m) p (rd i) w.`2) w).`2))).
proof.
move=> hi h0 hs.
have s0 := hs (3 * i) _; 1: smt().
have s1 := hs (3 * i + 1) _; 1: smt().
have h1 := stepBf p (iter (3 * i) (adv false p m) (cfwd x)) (iter (3 * i + 1) (adv false p m) (cfwd x)) i w
             (oget m.[PB (rd i, w.`2)]) m h0 _.
- by rewrite iterS 1:/# (adv_go _ _ _ _ s0); have [_ [_ [_ [_ ->]]]] := h0.
have h2 := stepAf p (iter (3 * i + 1) (adv false p m) (cfwd x)) (iter (3 * i + 2) (adv false p m) (cfwd x)) i w
             (salt_of (oget m.[PB (rd i, w.`2)])) (oget m.[PA (p, salt_of (oget m.[PB (rd i, w.`2)]))]) m h1 _.
- by rewrite (_ : 3 * i + 2 = (3 * i + 1) + 1) 1:/# iterS 1:/# (adv_go _ _ _ _ s1); have [_ [_ [_ [_ ->]]]] := h1.
split; 1: by rewrite /tabf.
move=> s2 hi11.
have h3 := stepHf p (iter (3 * i + 2) (adv false p m) (cfwd x)) (iter (3 * i + 3) (adv false p m) (cfwd x)) i w
             (key_of (oget m.[PA (p, salt_of (oget m.[PB (rd i, w.`2)]))]))
             (oget m.[PH (key_of (oget m.[PA (p, salt_of (oget m.[PB (rd i, w.`2)]))]), rd i, w.`2)]) m h2 _.
- by rewrite (_ : 3 * i + 3 = (3 * i + 2) + 1) 1:/# iterS 1:/# (adv_go _ _ _ _ s2); have [_ [_ [_ [_ ->]]]] := h2.
by have [h3' _] := h3; have := h3' hi11; rewrite /mask /tabf.
qed.

lemma fwd_track p x (m : (point, ans) fmap) i : 0 <= i < 12 => tracks false p m (cfwd x) (3 * i) =>
  atf (iter (3 * i) (adv false p m) (cfwd x)) i (fwdp (tabf m) p x 0 i) (PB (rd i, (fwdp (tabf m) p x 0 i).`2)).
proof.
move=> [hi0 hi12]; elim: i hi0 hi12 => [|i hi ih] hi12 htr.
- by rewrite /= iter0 // /fwdp /atf /cfwd /= iota0.
move: htr; rewrite (_ : 3 * (i + 1) = 3 * i + 3) 1:/# => htr.
have hw : fwdp (tabf m) p x 0 (i + 1) = round (mask (tabf m) p (rd i) (fwdp (tabf m) p x 0 i).`2) (fwdp (tabf m) p x 0 i).
- by rewrite /fwdp /= iotaSr // foldl_rcons.
have [_ h] := fwd_round p x m i (fwdp (tabf m) p x 0 i) _ (ih _ _) _.
- smt(). - smt(). - by move=> k hk; apply htr; smt(). - by move=> k hk; apply htr; smt().
by rewrite hw; apply h; [apply htr | ]; smt().
qed.

lemma size_iter_le bwd p (m : (point, ans) fmap) st0 k : 0 <= k =>
  size (iter k (adv bwd p m) st0).`chain <= size st0.`chain + k.
proof.
elim: k => [|k hk ih]; 1: by rewrite iter0.
rewrite iterS //; case: (adv_grow bwd p m (iter k (adv bwd p m) st0)) => [-> | [q ->]]; rewrite ?size_rcons /#.
qed.

(* Without Early, the forward H point of round j is the one of the final table's path. *)
lemma fwd_chain p x (m : (point, ans) fmap) st j : 0 <= j < 12 =>
  determined false p m (cfwd x) st => st.`fin =>
  nth witness st.`chain (3 * j + 2) = h0 (tabf m) p x j.
proof.
move=> hj [n [ge0n [hst [htight _]]]] hfin.
have [hch [hf _]] := strip_eq _ _ hst.
have hsh := shape_iter false p m (cfwd x) n ge0n (shape_fwd p x).
have hle := size_iter_le false p m (cfwd x) n ge0n.
have hn : 35 <= n.
- move: hsh hle; rewrite /shape /ndone /= -hf hfin /cfwd /=; smt().
have htr : tracks false p m (cfwd x) (3 * j) by move=> k hk; apply htight; smt().
have hat := fwd_track p x m j hj htr.
have [h2 _] := fwd_round p x m j _ _ hat _; 1: smt().
- by move=> k hk; apply htight; smt().
have [_ [hri [_ [_ hl]]]] := h2.
have hs2 := shape_iter false p m (cfwd x) (3 * j + 2) _ (shape_fwd p x); 1: smt().
have hsz2 : size (iter (3 * j + 2) (adv false p m) (cfwd x)).`chain = 3 * j + 3.
- by move: hs2; rewrite /shape /ndone /= hri hl /=; smt().
have [_ hnth] := iter_nth false p m (cfwd x) (3 * j + 2) (n - (3 * j + 2)) _ _; 1,2: smt().
rewrite hch (_ : n = 3 * j + 2 + (n - (3 * j + 2))) 1:/# hnth 1:/#.
have e := nth_last witness (iter (3 * j + 2) (adv false p m) (cfwd x)).`chain.
by move: e; rewrite hsz2 (_ : 3 * j + 3 - 1 = 3 * j + 2) 1:/# hl /h0 => ->.
qed.

(* The same for the backward chain from Y; after k rounds it stands at round 11 - k. *)
lemma bwd_round p y (m : (point, ans) fmap) k (w : state) : 0 <= k < 12 =>
  at (iter (3 * k) (adv true p m) (cbwd y)) (11 - k) w (PB (rd (11 - k), w.`1)) =>
  (forall t, 3 * k <= t < 3 * k + 2 => !stopped m (iter t (adv true p m) (cbwd y))) =>
  at (iter (3 * k + 2) (adv true p m) (cbwd y)) (11 - k) w
     (PH (key_of (tabf m (PA (p, salt_of (tabf m (PB (rd (11 - k), w.`1)))))), rd (11 - k), w.`1)) /\
  (!stopped m (iter (3 * k + 2) (adv true p m) (cbwd y)) => k < 11 =>
   at (iter (3 * k + 3) (adv true p m) (cbwd y)) (11 - k - 1)
      (unround (mask (tabf m) p (rd (11 - k)) w.`1) w)
      (PB (rd (11 - k - 1), (unround (mask (tabf m) p (rd (11 - k)) w.`1) w).`1))).
proof.
move=> hk h0 hs.
have s0 := hs (3 * k) _; 1: smt().
have s1 := hs (3 * k + 1) _; 1: smt().
have h1 := stepB p (iter (3 * k) (adv true p m) (cbwd y)) (iter (3 * k + 1) (adv true p m) (cbwd y)) (11 - k) w
             (oget m.[PB (rd (11 - k), w.`1)]) m h0 _.
- by rewrite iterS 1:/# (adv_go _ _ _ _ s0); have [_ [_ [_ [_ ->]]]] := h0.
have h2 := stepA p (iter (3 * k + 1) (adv true p m) (cbwd y)) (iter (3 * k + 2) (adv true p m) (cbwd y)) (11 - k) w
             (salt_of (oget m.[PB (rd (11 - k), w.`1)])) (oget m.[PA (p, salt_of (oget m.[PB (rd (11 - k), w.`1)]))]) m h1 _.
- by rewrite (_ : 3 * k + 2 = (3 * k + 1) + 1) 1:/# iterS 1:/# (adv_go _ _ _ _ s1); have [_ [_ [_ [_ ->]]]] := h1.
split; 1: by rewrite /tabf.
move=> s2 hk11.
have h3 := stepH p (iter (3 * k + 2) (adv true p m) (cbwd y)) (iter (3 * k + 3) (adv true p m) (cbwd y)) (11 - k) w
             (key_of (oget m.[PA (p, salt_of (oget m.[PB (rd (11 - k), w.`1)]))]))
             (oget m.[PH (key_of (oget m.[PA (p, salt_of (oget m.[PB (rd (11 - k), w.`1)]))]), rd (11 - k), w.`1)]) m h2 _.
- by rewrite (_ : 3 * k + 3 = (3 * k + 2) + 1) 1:/# iterS 1:/# (adv_go _ _ _ _ s2); have [_ [_ [_ [_ ->]]]] := h2.
by have [h3' _] := h3; have := h3' _; [smt() | rewrite /mask /tabf].
qed.

lemma bwd_track p y (m : (point, ans) fmap) k : 0 <= k < 12 => tracks true p m (cbwd y) (3 * k) =>
  at (iter (3 * k) (adv true p m) (cbwd y)) (11 - k) (bwdp (tabf m) p y 11 (12 - k))
     (PB (rd (11 - k), (bwdp (tabf m) p y 11 (12 - k)).`1)).
proof.
move=> [hk0 hk12]; elim: k hk0 hk12 => [|k hk ih] hk12 htr.
- by rewrite /= iter0 // /bwdp /at /cbwd /= iota0.
move: htr; rewrite (_ : 3 * (k + 1) = 3 * k + 3) 1:/# => htr.
have hw : bwdp (tabf m) p y 11 (12 - (k + 1)) =
          unround (mask (tabf m) p (rd (11 - k)) (bwdp (tabf m) p y 11 (12 - k)).`1) (bwdp (tabf m) p y 11 (12 - k)).
- rewrite /bwdp (_ : 11 + 1 - (12 - (k + 1)) = k + 1) 1:/# (_ : 11 + 1 - (12 - k) = k) 1:/#.
  by rewrite (_ : 12 - (k + 1) = 11 - k) 1:/# iotaS // rev_cons foldl_rcons /=.
have [_ h] := bwd_round p y m k (bwdp (tabf m) p y 11 (12 - k)) _ (ih _ _) _.
- smt(). - smt(). - by move=> t ht; apply htr; smt(). - by move=> t ht; apply htr; smt().
rewrite hw (_ : 11 - (k + 1) = 11 - k - 1) 1:/#; apply h; [apply htr | ]; smt().
qed.

lemma bwd_chain p y (m : (point, ans) fmap) st j : 0 <= j <= 10 =>
  determined true p m (cbwd y) st => st.`fin =>
  nth witness st.`chain (3 * (10 - j) + 2) = h1 (tabf m) p y j.
proof.
move=> hj [n [ge0n [hst [htight _]]]] hfin.
have [hch [hf _]] := strip_eq _ _ hst.
have hsh := shape_iter true p m (cbwd y) n ge0n (shape_bwd p y).
have hle := size_iter_le true p m (cbwd y) n ge0n.
have hn : 35 <= n.
- move: hsh hle; rewrite /shape /ndone /= -hf hfin /cbwd /=; smt().
have htr : tracks true p m (cbwd y) (3 * (10 - j)) by move=> k hk; apply htight; smt().
have hat := bwd_track p y m (10 - j) _ htr; 1: smt().
have [h2 _] := bwd_round p y m (10 - j) _ _ hat _; 1: smt().
- by move=> k hk; apply htight; smt().
have [_ [hri [_ [_ hl]]]] := h2.
have hs2 := shape_iter true p m (cbwd y) (3 * (10 - j) + 2) _ (shape_bwd p y); 1: smt().
have hsz2 : size (iter (3 * (10 - j) + 2) (adv true p m) (cbwd y)).`chain = 3 * (10 - j) + 3.
- by move: hs2; rewrite /shape /ndone /= hri hl /=; smt().
have [_ hnth] := iter_nth true p m (cbwd y) (3 * (10 - j) + 2) (n - (3 * (10 - j) + 2)) _ _; 1,2: smt().
rewrite hch (_ : n = 3 * (10 - j) + 2 + (n - (3 * (10 - j) + 2))) 1:/# hnth 1:/#.
have e := nth_last witness (iter (3 * (10 - j) + 2) (adv true p m) (cbwd y)).`chain.
move: e; rewrite hsz2 (_ : 3 * (10 - j) + 3 - 1 = 3 * (10 - j) + 2) 1:/# hl => ->.
by rewrite /h1 (_ : 11 - (10 - j) = j + 1) 1:/# (_ : 12 - (10 - j) = j + 2) 1:/#.
qed.

(* The H point of the backward round 11 - t, after t rounds from y. *)
op hb f p (y : state) t =
  PH (key_of (f (PA (p, salt_of (f (PB (rd (11 - t), (bwdp f p y 11 (12 - t)).`1)))))), rd (11 - t),
      (bwdp f p y 11 (12 - t)).`1).

lemma hb_h1 f p y j : hb f p y (10 - j) = h1 f p y j.
proof. by rewrite /hb /h1 (_ : 11 - (10 - j) = j + 1) 1:/# (_ : 12 - (10 - j) = j + 2) 1:/#. qed.

(* The table m extends m0. *)
op ext (m0 m : (point, ans) fmap) = forall c, c \in m0 => m.[c] = m0.[c].

lemma ext_trans (m0 m1 m2 : (point, ans) fmap) : ext m0 m1 => ext m1 m2 => ext m0 m2.
proof. by move=> h1 h2 c hc; rewrite h2 ?h1 // domE h1 // -domE. qed.

lemma ext_mem (m0 m : (point, ans) fmap) c : ext m0 m => c \in m0 => c \in m.
proof. by move=> h hc; rewrite domE h // -domE. qed.

lemma ext_tab (m0 m : (point, ans) fmap) c : ext m0 m => c \in m0 => tabf m c = tabf m0 c.
proof. by move=> h hc; rewrite /tabf h. qed.

(* The answer of the lazy oracle extends its table with the queried point. *)
lemma get_ext (c0 : point) (m0 : (point, ans) fmap) :
  hoare [R.RO.get : x = c0 /\ R.RO.m = m0 ==> ext m0 R.RO.m /\ c0 \in R.RO.m /\ res = tabf R.RO.m c0].
proof. by proc; auto => />; smt(get_setE mem_set). qed.

(* The rounds below n of the forward path of the table m from x are answered in m. *)
op fpath (m : (point, ans) fmap) p (x : state) n = forall i, 0 <= i < n =>
  PB (rd i, (fwdp (tabf m) p x 0 i).`2) \in m /\
  PA (p, salt_of (tabf m (PB (rd i, (fwdp (tabf m) p x 0 i).`2)))) \in m /\ h0 (tabf m) p x i \in m.

lemma fwdpS f p (x : state) n : 0 <= n =>
  fwdp f p x 0 (n + 1) = round (mask f p (rd n) (fwdp f p x 0 n).`2) (fwdp f p x 0 n).
proof. by move=> hn; rewrite /fwdp /= iotaSr // foldl_rcons. qed.

lemma fpath_ext (m0 m : (point, ans) fmap) p x n : 0 <= n => ext m0 m => fpath m0 p x n =>
  fwdp (tabf m) p x 0 n = fwdp (tabf m0) p x 0 n /\
  (forall i, 0 <= i < n => h0 (tabf m) p x i = h0 (tabf m0) p x i) /\ fpath m p x n.
proof.
move=> hn he; elim: n hn => [|n hn ih] hp.
- by rewrite /fwdp !iota0 //=; split => [i | i] /#.
have [e1 [e2 e3]] := ih _; 1: by move=> i hi; apply hp; smt().
have [hb [ha hh]] := hp n _; 1: smt().
have tb := ext_tab m0 m _ he hb; have ta := ext_tab m0 m _ he ha; have th := ext_tab m0 m _ he hh.
have en : h0 (tabf m) p x n = h0 (tabf m0) p x n by rewrite /h0 e1 tb /= -/(tabf m) ta.
have em : mask (tabf m) p (rd n) (fwdp (tabf m0) p x 0 n).`2 = mask (tabf m0) p (rd n) (fwdp (tabf m0) p x 0 n).`2.
- by rewrite /mask /= tb ta; move: th; rewrite /h0 /= => ->.
have ef : fwdp (tabf m) p x 0 (n + 1) = fwdp (tabf m0) p x 0 (n + 1) by rewrite !fwdpS // e1 em.
split; 1: exact ef.
split => [i hi | i hi]; 1: by case: (i = n) => [-> | hin]; [exact en | apply e2; smt()].
case: (i = n) => [-> | hin]; 2: by apply e3; smt().
by rewrite e1 tb en; smt(ext_mem).
qed.

(* One round of the forward evaluation on the lazy oracle: three answers that extend the table. *)
lemma fpath_step (m m1 m2 m3 : (point, ans) fmap) p x i : 0 <= i =>
  fpath m p x i => ext m m1 => ext m1 m2 => ext m2 m3 =>
  PB (rd i, (fwdp (tabf m) p x 0 i).`2) \in m1 =>
  PA (p, salt_of (tabf m1 (PB (rd i, (fwdp (tabf m) p x 0 i).`2)))) \in m2 =>
  PH (key_of (tabf m2 (PA (p, salt_of (tabf m1 (PB (rd i, (fwdp (tabf m) p x 0 i).`2)))))), rd i,
      (fwdp (tabf m) p x 0 i).`2) \in m3 =>
  fpath m3 p x (i + 1) /\
  fwdp (tabf m3) p x 0 (i + 1) =
    round (mask_of (tabf m3 (PH (key_of (tabf m2 (PA (p, salt_of (tabf m1 (PB (rd i, (fwdp (tabf m) p x 0 i).`2)))))),
                                 rd i, (fwdp (tabf m) p x 0 i).`2)))) (fwdp (tabf m) p x 0 i) /\
  map (h0 (tabf m3) p x) (iota_ 0 (i + 1)) =
    rcons (map (h0 (tabf m) p x) (iota_ 0 i))
          (PH (key_of (tabf m2 (PA (p, salt_of (tabf m1 (PB (rd i, (fwdp (tabf m) p x 0 i).`2)))))), rd i,
               (fwdp (tabf m) p x 0 i).`2)).
proof.
move=> hi hp e1 e2 e3 hb ha hh.
have e13 := ext_trans _ _ _ e1 (ext_trans _ _ _ e2 e3).
have [ew [eh hp3]] := fpath_ext m m3 p x i hi e13 hp.
have tb : tabf m3 (PB (rd i, (fwdp (tabf m) p x 0 i).`2)) = tabf m1 (PB (rd i, (fwdp (tabf m) p x 0 i).`2)).
- by apply (ext_tab m1 m3) => //; apply (ext_trans _ _ _ e2 e3).
have ta := ext_tab m2 m3 _ e3 ha.
have eh0 : h0 (tabf m3) p x i =
  PH (key_of (tabf m2 (PA (p, salt_of (tabf m1 (PB (rd i, (fwdp (tabf m) p x 0 i).`2)))))), rd i,
      (fwdp (tabf m) p x 0 i).`2) by rewrite /h0 ew tb ta.
split.
- move=> t ht; case: (t = i) => [-> | hti]; 2: by apply hp3; smt().
  rewrite ew tb eh0 hh /=; split; 1: by apply (ext_mem m1 m3) => //; apply (ext_trans _ _ _ e2 e3).
  by apply (ext_mem m2 m3).
split; 1: by rewrite fwdpS // ew /mask /= tb ta.
rewrite iotaSr // map_rcons eh0; congr.
by apply eq_in_map => t /mem_iota ht; apply eh; smt().
qed.

lemma bwdpS f p (y : state) t : 0 <= t =>
  bwdp f p y 11 (12 - (t + 1)) = unround (mask f p (rd (11 - t)) (bwdp f p y 11 (12 - t)).`1) (bwdp f p y 11 (12 - t)).
proof.
move=> ht; rewrite /bwdp (_ : 11 + 1 - (12 - (t + 1)) = t + 1) 1:/# (_ : 11 + 1 - (12 - t) = t) 1:/#.
by rewrite (_ : 12 - (t + 1) = 11 - t) 1:/# iotaS // rev_cons foldl_rcons /=.
qed.

(* The backward rounds 11 down to 12 - n of the table m from y are answered in m. *)
op bpath (m : (point, ans) fmap) p (y : state) n = forall t, 0 <= t < n =>
  PB (rd (11 - t), (bwdp (tabf m) p y 11 (12 - t)).`1) \in m /\
  PA (p, salt_of (tabf m (PB (rd (11 - t), (bwdp (tabf m) p y 11 (12 - t)).`1)))) \in m /\
  hb (tabf m) p y t \in m.

lemma bpath_ext (m0 m : (point, ans) fmap) p y n : 0 <= n => ext m0 m => bpath m0 p y n =>
  bwdp (tabf m) p y 11 (12 - n) = bwdp (tabf m0) p y 11 (12 - n) /\
  (forall t, 0 <= t < n => hb (tabf m) p y t = hb (tabf m0) p y t) /\ bpath m p y n.
proof.
move=> hn he; elim: n hn => [|n hn ih] hp.
- by rewrite /bwdp !iota0 //= /bpath; smt().
have [e1 [e2 e3]] := ih _; 1: by move=> t ht; apply hp; smt().
have [hb [ha hh]] := hp n _; 1: smt().
have tb := ext_tab m0 m _ he hb; have ta := ext_tab m0 m _ he ha; have th := ext_tab m0 m _ he hh.
have en : hb (tabf m) p y n = hb (tabf m0) p y n by rewrite /hb e1 tb /= -/(tabf m) ta.
have em : mask (tabf m) p (rd (11 - n)) (bwdp (tabf m0) p y 11 (12 - n)).`1 =
          mask (tabf m0) p (rd (11 - n)) (bwdp (tabf m0) p y 11 (12 - n)).`1.
- by rewrite /mask /= tb ta; move: th; rewrite /hb /= => ->.
split; 1: by rewrite !bwdpS // e1 em.
split => [t ht | t ht]; 1: by case: (t = n) => [-> | htn]; [exact en | apply e2; smt()].
case: (t = n) => [-> | htn]; 2: by apply e3; smt().
by rewrite e1 tb en; smt(ext_mem).
qed.

lemma bpath_step (m m1 m2 m3 : (point, ans) fmap) p y t : 0 <= t =>
  bpath m p y t => ext m m1 => ext m1 m2 => ext m2 m3 =>
  PB (rd (11 - t), (bwdp (tabf m) p y 11 (12 - t)).`1) \in m1 =>
  PA (p, salt_of (tabf m1 (PB (rd (11 - t), (bwdp (tabf m) p y 11 (12 - t)).`1)))) \in m2 =>
  PH (key_of (tabf m2 (PA (p, salt_of (tabf m1 (PB (rd (11 - t), (bwdp (tabf m) p y 11 (12 - t)).`1)))))),
      rd (11 - t), (bwdp (tabf m) p y 11 (12 - t)).`1) \in m3 =>
  bpath m3 p y (t + 1) /\
  bwdp (tabf m3) p y 11 (12 - (t + 1)) =
    unround (mask_of (tabf m3 (PH (key_of (tabf m2 (PA (p, salt_of (tabf m1 (PB (rd (11 - t),
                (bwdp (tabf m) p y 11 (12 - t)).`1)))))), rd (11 - t), (bwdp (tabf m) p y 11 (12 - t)).`1))))
            (bwdp (tabf m) p y 11 (12 - t)) /\
  map (hb (tabf m3) p y) (iota_ 0 (t + 1)) =
    rcons (map (hb (tabf m) p y) (iota_ 0 t))
          (PH (key_of (tabf m2 (PA (p, salt_of (tabf m1 (PB (rd (11 - t), (bwdp (tabf m) p y 11 (12 - t)).`1)))))),
               rd (11 - t), (bwdp (tabf m) p y 11 (12 - t)).`1)).
proof.
move=> ht hp e1 e2 e3 hb ha hh.
have e13 := ext_trans _ _ _ e1 (ext_trans _ _ _ e2 e3).
have [ew [eh hp3]] := bpath_ext m m3 p y t ht e13 hp.
have tb : tabf m3 (PB (rd (11 - t), (bwdp (tabf m) p y 11 (12 - t)).`1)) =
          tabf m1 (PB (rd (11 - t), (bwdp (tabf m) p y 11 (12 - t)).`1)).
- by apply (ext_tab m1 m3) => //; apply (ext_trans _ _ _ e2 e3).
have ta := ext_tab m2 m3 _ e3 ha.
have eh0 : hb (tabf m3) p y t =
  PH (key_of (tabf m2 (PA (p, salt_of (tabf m1 (PB (rd (11 - t), (bwdp (tabf m) p y 11 (12 - t)).`1)))))),
      rd (11 - t), (bwdp (tabf m) p y 11 (12 - t)).`1) by rewrite /hb ew tb ta.
split.
- move=> u hu; case: (u = t) => [-> | hut]; 2: by apply hp3; smt().
  rewrite ew tb eh0 hh /=; split; 1: by apply (ext_mem m1 m3) => //; apply (ext_trans _ _ _ e2 e3).
  by apply (ext_mem m2 m3).
split; 1: by rewrite bwdpS // ew /mask /= tb ta.
rewrite iotaSr // map_rcons eh0; congr.
by apply eq_in_map => u /mem_iota hu; apply eh; smt().
qed.

(* ---- A permutation of the rounds 0 .. 10 that puts the rounds of B first ---------------------- *)
op perm11 (B : int -> bool) : int list = filter B (range 0 11) ++ filter (predC B) (range 0 11).
op sig (B : int -> bool) (j : int) : int = index j (perm11 B).
op sigi (B : int -> bool) (k : int) : int = nth 0 (perm11 B) k.

lemma perm11_perm B : perm_eq (perm11 B) (range 0 11).
proof. by rewrite /perm11 perm_filterC. qed.

lemma perm11_size B : size (perm11 B) = 11.
proof. by rewrite (perm_eq_size _ _ (perm11_perm B)) size_range. qed.

lemma perm11_uniq B : uniq (perm11 B).
proof. by rewrite (perm_eq_uniq _ _ (perm11_perm B)) range_uniq. qed.

lemma perm11_mem B j : (j \in perm11 B) = (0 <= j < 11).
proof. by rewrite (perm_eq_mem _ _ (perm11_perm B)) mem_range. qed.

lemma sig_range B j : 0 <= j < 11 => 0 <= sig B j < 11.
proof. by move=> hj; rewrite /sig index_ge0 /= -(perm11_size B) index_mem perm11_mem. qed.

lemma sigi_range B k : 0 <= k < 11 => 0 <= sigi B k < 11.
proof. by move=> hk; rewrite -(perm11_mem B) /sigi mem_nth perm11_size. qed.

lemma sigK B j : 0 <= j < 11 => sigi B (sig B j) = j.
proof. by move=> hj; rewrite /sigi /sig nth_index // perm11_mem. qed.

lemma sigiK B k : 0 <= k < 11 => sig B (sigi B k) = k.
proof. by move=> hk; rewrite /sig /sigi index_uniq ?perm11_uniq // perm11_size. qed.

lemma sig_bad B j : 0 <= j < 11 => B j => sig B j < count B (range 0 11).
proof.
move=> hj hb; rewrite /sig /perm11 index_cat.
have hm : j \in filter B (range 0 11) by rewrite mem_filter mem_range.
by rewrite hm /= -size_filter index_mem.
qed.

(* The event of (2) for the round j. *)
op ev4 (out p : pw) (log : (point * int) list) (sf sb : cst) (j : int) =
  out = p \/ badj log sf.`chain sb.`chain j \/ sf.`early \/ sb.`early.

(* ---- A late password and a late round ------------------------------------------------------- *)
lemma mu_prod_sum (dQ : int distr) (E : pw -> int -> bool) :
  mu (dP `*` dQ) (fun (pj : pw * int) => E pj.`1 pj.`2) = big predT (fun w => mu1 dP w * mu dQ (E w)) PwT.enum.
proof.
rewrite dprod_dlet dletE (RealSeries.sumE_fin _ PwT.enum) ?PwT.enum_uniq; 1: by move=> w _; apply PwT.enumP.
apply eq_bigr => w _ /=; congr.
by rewrite dletE muE; apply RealSeries.eq_sum => j /=; rewrite dunitE /=; smt().
qed.

lemma mu_dinter_lt (n : int) : 0 <= n => mu [0..10] (fun j => j < n) <= n%r / 11%r.
proof.
move=> hn; rewrite dinterE /=.
have : size (filter (fun j => j < n) (range 0 11)) <= size (range 0 n).
- apply uniq_leq_size; 1: by apply filter_uniq; apply range_uniq.
  by move=> j; rewrite mem_filter !mem_range /#.
rewrite size_range /= => h.
have -> : max 0 11 = 11 by smt().
by apply StdOrder.RealOrder.ler_wpmul2r; [smt() | smt(le_fromint)].
qed.

(* A guess and the passwords' query counts N_w, against a late password and a late round: the
   fractional top of A.5. *)
lemma late_guess (out : pw) (N : pw -> int) (k : int) :
  (forall w, 0 <= N w) => StdBigop.Bigint.BIA.big predT N PwT.enum <= k =>
  mu (dP `*` [0..10]) (fun (pj : pw * int) => out = pj.`1 \/ pj.`2 < N pj.`1) <= ftop (1%r + k%r / 11%r).
proof.
move=> hN hk; rewrite (mu_prod_sum [0..10] (fun w j => out = w \/ j < N w)); apply ftop_max.
- by move=> w /=; split; [apply ge0_mu | move=> _; apply le1_mu].
apply (StdOrder.RealOrder.ler_trans (big predT (fun w => b2r (out = w) + (N w)%r / 11%r) PwT.enum)).
- apply StdBigop.Bigreal.ler_sum => w _ /=; case: (out = w) => hw /=; 1: by have := hN w; smt(le1_mu ge0_mu le_fromint).
  by apply mu_dinter_lt; apply hN.
rewrite big_split -mulr_suml -StdBigop.Bigreal.sumr_ofint.
rewrite (bigD1 _ _ out) ?PwT.enumP ?PwT.enum_uniq /= big1 => [w /= hw | ]; 1: smt().
smt(StdOrder.RealOrder.ler_wpmul2r le_fromint).
qed.

op epsK (kA qB qH : int) : real =
  (24%r * p1 * kA%r + 2%r * qB%r + 419%r) / 2%r ^ 128 + (2%r * qH%r + 12%r) / 2%r ^ 256.

(* ---- Lemma K3: the risk of both chains ----------------------------------------------------- *)
(* A complete chain carries no risk. *)
lemma rho_fin bwd w S st : shape bwd w st => st.`fin => rho bwd w S st = 0%r.
proof.
move=> [_ [_ [_ [hcnt [_ [hf _]]]]]] hfin; have [hn hp] := hf hfin.
have hA : nA st = 0 by rewrite /nA hcnt hn hp.
have hB : bigi predT (fun j => if futB bwd st j then hitB S j else 0%r) 0 12 = 0%r.
- by rewrite big1 // => j _ /=; rewrite /futB; move: hn; rewrite /ndone; case: bwd => /#.
have hH : bigi predT (fun j => if futH bwd st j then hitH S j else 0%r) 0 12 = 0%r.
- by rewrite big1 // => j _ /=; rewrite /futH /futB hp; move: hn; rewrite /ndone; case: bwd => /#.
by rewrite /rho hA hB hH; smt().
qed.

(* The backward chain never reads a B point of round 11 again. *)
lemma psi_B11 w S st z : shape true w st =>
  psi true w (fun x => S x \/ x = PB (rd 11, z)) st = psi true w S st.
proof.
move=> [hri _]; rewrite /psi; case: (st.`early) => //= _; rewrite /rho.
have -> : hitA (fun x => S x \/ x = PB (rd 11, z)) w = hitA S w by rewrite /hitA; apply mu_eq.
have -> : (isA (last witness st.`chain) /\ !(S (last witness st.`chain) \/ last witness st.`chain = PB (rd 11, z))) =
          (isA (last witness st.`chain) /\ !S (last witness st.`chain)) by case: (last witness st.`chain).
have -> : bigi predT (fun j => if futB true st j then hitB (fun x => S x \/ x = PB (rd 11, z)) j else 0%r) 0 12 =
          bigi predT (fun j => if futB true st j then hitB S j else 0%r) 0 12.
- apply eq_big_int => j hj /=; rewrite /futB /=; case: (0 <= j < st.`ri) => // hjr.
  rewrite /hitB; apply mu_eq => x /=; have : rd j <> rd 11 by smt(rd_inj).
  smt().
have -> // : bigi predT (fun j => if futH true st j then hitH (fun x => S x \/ x = PB (rd 11, z)) j else 0%r) 0 12 =
             bigi predT (fun j => if futH true st j then hitH S j else 0%r) 0 12.
apply eq_big_int => j _ /=; congr; rewrite /hitH; apply mu_eq => k /=; smt().
qed.

(* What the next point of the forward chain adds to the risk of the backward chain, and the allowance
   for the points of the forward chain still to come: a B point of round j <= 10 costs e128 (round 11
   is never read again backward), an A point of P 12 e128, an H point e256. *)
op costF (st : cst) : real =
  if isB (last witness st.`chain) then (if st.`ri < 11 then e128 else 0%r)
  else if isA (last witness st.`chain) then 12%r * e128 else e256.

op allowF (st : cst) : real =
  if st.`fin then 0%r
  else (if isB (last witness st.`chain) /\ st.`ri < 11 then e128 else 0%r)
       + (if isB (last witness st.`chain) \/ isA (last witness st.`chain) then 12%r * e128 else 0%r)
       + (12 * (11 - st.`ri) + max 0 (10 - st.`ri))%r * e128 + (12 - st.`ri)%r * e256.

lemma allowF_ge0 p st : shape false p st => 0%r <= allowF st.
proof. by move=> [hri _]; rewrite /allowF; have := e128_gt0; have := e256_gt0; smt(). qed.

lemma allowF_le p st : shape false p st => allowF st <= 155%r * e128 + 12%r * e256.
proof. by move=> [hri _]; rewrite /allowF; have := e128_gt0; have := e256_gt0; smt(). qed.

lemma allowF_step p st c r (m : (point, ans) fmap) : shape false p st => !st.`fin => last witness st.`chain = c =>
  allowF (cstep false p st c true r [] m) = allowF st - costF st.
proof.
move=> [hri _] hfin hl; rewrite /cstep hfin hl /= /allowF /costF hfin hl /=.
case: c hl => [a | b | h] hl /=; rewrite /push /= ?last_rcons /=; 1,2: smt().
case: (st.`ri < 11) => hr /=; rewrite ?last_rcons /=; smt().
qed.

(* The next point of the forward chain raises the risk of the backward chain by at most its cost. *)
lemma psi_costF w S st f : shape true w st => shape false w f => !f.`fin =>
  psi true w (fun x => S x \/ x = last witness f.`chain) st <= psi true w S st + costF f.
proof.
move=> hsb [hri [hne [_ [_ [hall [_ hl]]]]]] hfin; have hmem := last_mem _ hne.
have hA : isA (last witness f.`chain) => isApw w (last witness f.`chain) by move: hall => /allP /(_ _ hmem).
have hP : isApw w (last witness f.`chain) => isA (last witness f.`chain) by case: (last witness f.`chain).
have := psi_add true w S (last witness f.`chain) st hsb.
rewrite /costF; case: (isB (last witness f.`chain)) => hB.
- case: (f.`ri < 11) => hr; 1: smt(e128_gt0).
  have hi := hl _; 1: by move: hB; case: (last witness f.`chain).
  move: hB hi; case: (last witness f.`chain) => // -[i z] _ /= -> _.
  by rewrite (_ : f.`ri = 11) 1:/# (psi_B11 _ _ _ _ hsb).
by case: (isA (last witness f.`chain)) => hA'; smt(e128_gt0 e256_gt0).
qed.

(* The potential of the finalization: 0 after an odd query or beyond a budget, 1 after Early, and
   otherwise the risk of both chains of P with the allowance for the forward points to come. *)
op potF (kA qB qH ca cb ch : int) (odd : bool) (m : (point, ans) fmap) (p : pw) (f b : cst) : real =
  if odd \/ !(ca <= kA /\ cb <= qB /\ ch <= qH) then 0%r
  else if f.`early \/ b.`early then 1%r
  else psi false p (fun x => x \in m) f + psi true p (fun x => x \in m) b + allowF f.

(* A complete chain without Early carries no risk. *)
lemma psi_fin bwd w S st : shape bwd w st => st.`fin => !st.`early => psi bwd w S st = 0%r.
proof. by move=> hsh hf he; rewrite /psi he /= (rho_fin _ _ _ _ hsh hf). qed.

(* The expectation of a sum of two nonnegative risks and a constant. *)
lemma Ep_sum3 (F G : ans -> real) (K : real) : (forall r, 0%r <= F r) => (forall r, 0%r <= G r) => 0%r <= K =>
  Ep dans (fun r => (F r + G r + K)%xr) = Ep dans (fun r => (F r)%xr) + Ep dans (fun r => (G r)%xr) + K%xr.
proof.
move=> hF hG hK; rewrite (eq_Ep _ _ ((fun r => (F r)%xr) + (fun r => (G r)%xr) + (fun _ => K%xr))) => [r _ /= | ].
- by have h1 := hF r; have h2 := hG r; rewrite -(of_realD _ _ h1 h2) -of_realD // /#.
by rewrite !EpD EpC dans_ll.
qed.

(* Outside an odd query and the budgets, the potential is at most the risks and the allowance. *)
lemma potF_le kA qB qH ca cb ch odd m p f b : shape false p f => shape true p b =>
  potF kA qB qH ca cb ch odd m p f b <=
  psi false p (fun x => x \in m) f + psi true p (fun x => x \in m) b + allowF f.
proof.
move=> hsf hsb; have := psi_ge0 false p (fun x => x \in m) f hsf.
have := psi_ge0 true p (fun x => x \in m) b hsb; have := allowF_ge0 p f hsf.
by rewrite /potF /psi; smt().
qed.

lemma potF_ge0 kA qB qH ca cb ch odd m p f b : shape false p f => shape true p b =>
  0%r <= potF kA qB qH ca cb ch odd m p f b.
proof.
move=> hsf hsb; have := psi_ge0 false p (fun x => x \in m) f hsf.
have := psi_ge0 true p (fun x => x \in m) b hsb; have := allowF_ge0 p f hsf.
by rewrite /potF; smt().
qed.

(* One query of the finalization keeps the expected potential: an answered point changes nothing,
   and a fresh one is odd or the next point of the chain being evaluated, the forward chain paying
   the backward risk it adds from its allowance. *)
lemma Ep_fin1 kA qB qH ca cb ch odd (m : (point, ans) fmap) p f b c :
  shape false p f => shape true p b =>
  Ep dans (fun r =>
    if c \notin m then
      (shape false p (cstep false p f c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r]) /\
       shape true p (cstep true p b c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r])) `|`
      (potF kA qB qH ca cb ch (odd \/ (c \notin m) /\ oddq c f b) m.[c <- r] p
         (cstep false p f c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r])
         (cstep true p b c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r]))%xr
    else
      (shape false p (cstep false p f c (c \notin m) (oget m.[c]) [] m) /\
       shape true p (cstep true p b c (c \notin m) (oget m.[c]) [] m)) `|`
      (potF kA qB qH ca cb ch (odd \/ (c \notin m) /\ oddq c f b) m p
         (cstep false p f c (c \notin m) (oget m.[c]) [] m)
         (cstep true p b c (c \notin m) (oget m.[c]) [] m))%xr)
  <= (potF kA qB qH ca cb ch odd m p f b)%xr.
proof.
move=> hsf hsb.
have hg : forall fresh r' (m' : (point, ans) fmap),
  (shape false p (cstep false p f c fresh r' [] m') /\ shape true p (cstep true p b c fresh r' [] m')) = true.
- by move=> *; rewrite eqT; split; apply shape_cstep.
case: (c \in m) => cm /=.
- by rewrite /cstep /= hsf hsb /= EpC dans_ll smul1m.
rewrite (eq_Ep _ _ (fun r => (potF kA qB qH ca cb ch (odd \/ oddq c f b) m.[c <- r] p
           (cstep false p f c true r [] m.[c <- r]) (cstep true p b c true r [] m.[c <- r]))%xr)).
- by move=> r _ /=; rewrite get_set_sameE oget_some hg.
pose S1 := fun x => x \in m \/ x = c.
have hS : forall r, (fun x => x \in m.[c <- r]) = S1 by move=> r; apply fun_ext => x; rewrite /S1 mem_set.
have hS1 : forall r q, (q \in m.[c <- r] \/ q \in []) = S1 q by move=> r q; rewrite /S1 mem_set.
case: (odd \/ !(ca <= kA /\ cb <= qB /\ ch <= qH)) => hz.
- rewrite (eq_Ep _ _ (fun _ => 0%xr)) => [r _ /= | ]; 1: by rewrite /potF /#.
  by rewrite EpC dans_ll smul1m; apply xle0x.
have [ho hbud] : !odd /\ (ca <= kA /\ cb <= qB /\ ch <= qH) by smt().
case: (f.`early \/ b.`early) => he.
- have h1 : potF kA qB qH ca cb ch odd m p f b = 1%r by rewrite /potF ho hbud /= he.
  apply (xle_trans (Ep dans (fun _ => (potF kA qB qH ca cb ch odd m p f b)%xr))).
  + apply le_Ep => r _ /=; apply le_pos.
    rewrite h1; have : (cstep false p f c true r [] m.[c <- r]).`early \/ (cstep true p b c true r [] m.[c <- r]).`early.
    * by case: he => h; [left | right]; apply early_mono.
    by rewrite /potF; smt().
  by rewrite EpC dans_ll smul1m.
have [hef heb] : !f.`early /\ !b.`early by smt().
case: (oddq c f b) => hq.
- rewrite (eq_Ep _ _ (fun _ => 0%xr)) => [r _ /= | ]; 1: by rewrite /potF.
  by rewrite EpC dans_ll smul1m; apply xle0x.
apply (xle_trans (Ep dans (fun r => (psi false p S1 (cstep false p f c true r [] m.[c <- r]) +
                                     psi true p S1 (cstep true p b c true r [] m.[c <- r]) +
                                     allowF (cstep false p f c true r [] m.[c <- r]))%xr))).
- by apply le_Ep => r _ /=; rewrite -(hS r); apply le_pos; apply potF_le; apply shape_cstep.
have hp := potF_le kA qB qH ca cb ch odd m p f b hsf hsb.
move: hq; rewrite /oddq hef heb /=; case: (f.`fin) => hff /= hq.
- have [hbf hl] : !b.`fin /\ last witness b.`chain = c by smt().
  rewrite (eq_Ep _ _ (fun r => (psi true p S1 (cstep true p b c true r [] m.[c <- r]))%xr)) => [r _ /= | ].
  + by rewrite !(fin_step _ _ _ _ _ _ _ _ hff) (psi_fin _ _ _ _ hsf hff hef) /allowF hff /= ?add0r ?addr0.
  apply (xle_trans _ _ _ (Ep_answer true p m c [] b S1 hsb _ hS1)); 1: by rewrite /S1.
  rewrite /potF ho hbud /= hef heb /= (psi_fin _ _ _ _ hsf hff hef) /allowF hff /=.
  by apply le_pos; have := psi_own true p (fun x => x \in m) b hsb; rewrite hl.
have hl : last witness f.`chain = c by smt().
rewrite (eq_Ep _ _ (fun r => (psi false p S1 (cstep false p f c true r [] m.[c <- r]) +
                              psi true p S1 (cstep true p b c true r [] m.[c <- r]) + (allowF f - costF f))%xr)).
- by move=> r _ /=; rewrite (allowF_step _ _ _ _ _ hsf hff hl).
have hK : 0%r <= allowF f - costF f.
- by rewrite -(allowF_step _ _ _ witness empty hsf hff hl); apply (allowF_ge0 p); apply shape_cstep.
rewrite (Ep_sum3 _ _ _ _ _ hK) => [r | r | ]; 1,2: by apply psi_ge0; apply shape_cstep.
have e1 := Ep_answer false p m c [] f S1 hsf _ hS1; 1: by rewrite /S1.
have e2 := Ep_answer true p m c [] b S1 hsb _ hS1; 1: by rewrite /S1.
apply (xle_trans _ _ _ (xler_add _ _ _ _ (xler_add _ _ _ _ e1 e2) (xlexx (allowF f - costF f)%xr))).
have o1 := psi_own false p (fun x => x \in m) f hsf.
have o2 := psi_costF p (fun x => x \in m) b f hsb hsf hff.
move: o1 o2; rewrite hl /= -/S1 => o1 o2.
have g1 := psi_ge0 false p S1 f hsf; have g2 := psi_ge0 true p S1 b hsb.
have gp := potF_ge0 kA qB qH ca cb ch odd m p f b hsf hsb.
rewrite (to_pos_pos _ g1) (to_pos_pos _ g2) (to_pos_pos _ hK) (to_pos_pos _ gp).
by rewrite /potF ho hbud /= hef heb /=; smt().
qed.

lemma mon2_a_fin kA qB qH : ehoare [Mon2.a :
  (!Mon2.inrun /\ Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
  (potF kA qB qH Count.ca Count.cb Count.ch Fwd.odd R.RO.m Fwd.p (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr ==>
  (!Mon2.inrun /\ Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
  (potF kA qB qH Count.ca Count.cb Count.ch Fwd.odd R.RO.m Fwd.p (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr].
proof.
proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi [hp [hsf hsb]]].
by move: hsf; rewrite hi hp /= => hsf; apply (Ep_fin1 _ _ _ _ _ _ _ _ _ _ _ _ hsf hsb).
qed.

lemma mon2_b_fin kA qB qH : ehoare [Mon2.b :
  (!Mon2.inrun /\ Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
  (potF kA qB qH Count.ca Count.cb Count.ch Fwd.odd R.RO.m Fwd.p (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr ==>
  (!Mon2.inrun /\ Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
  (potF kA qB qH Count.ca Count.cb Count.ch Fwd.odd R.RO.m Fwd.p (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr].
proof.
proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi [hp [hsf hsb]]].
by move: hsf; rewrite hi hp /= => hsf; apply (Ep_fin1 _ _ _ _ _ _ _ _ _ _ _ _ hsf hsb).
qed.

lemma mon2_h_fin kA qB qH : ehoare [Mon2.h :
  (!Mon2.inrun /\ Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
  (potF kA qB qH Count.ca Count.cb Count.ch Fwd.odd R.RO.m Fwd.p (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr ==>
  (!Mon2.inrun /\ Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
  (potF kA qB qH Count.ca Count.cb Count.ch Fwd.odd R.RO.m Fwd.p (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr].
proof.
proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi [hp [hsf hsb]]].
by move: hsf; rewrite hi hp /= => hsf; apply (Ep_fin1 _ _ _ _ _ _ _ _ _ _ _ _ hsf hsb).
qed.

(* The finalization keeps the potential. *)
lemma enc_eK kA qB qH : ehoare [Net(Mon2).enc :
  (!Mon2.inrun /\ Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
  (potF kA qB qH Count.ca Count.cb Count.ch Fwd.odd R.RO.m Fwd.p (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr ==>
  (!Mon2.inrun /\ Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
  (potF kA qB qH Count.ca Count.cb Count.ch Fwd.odd R.RO.m Fwd.p (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr].
proof.
proc; while ((!Mon2.inrun /\ Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
             (potF kA qB qH Count.ca Count.cb Count.ch Fwd.odd R.RO.m Fwd.p (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr).
- by move=> &hr; apply xle_cxr_r.
- conseq (_ : ((!Mon2.inrun /\ Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
             (potF kA qB qH Count.ca Count.cb Count.ch Fwd.odd R.RO.m Fwd.p (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr) ==> _).
  + by move=> &hr; apply xle_cxr_r.
  + by move=> &hr; apply xle_cxr_r.
  wp; call (mon2_h_fin kA qB qH); call (mon2_a_fin kA qB qH); call (mon2_b_fin kA qB qH); skip => &hr.
  by apply xlexx.
by auto.
qed.

lemma dec_eK kA qB qH : ehoare [Net(Mon2).dec :
  (!Mon2.inrun /\ Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
  (potF kA qB qH Count.ca Count.cb Count.ch Fwd.odd R.RO.m Fwd.p (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr ==>
  (!Mon2.inrun /\ Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
  (potF kA qB qH Count.ca Count.cb Count.ch Fwd.odd R.RO.m Fwd.p (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr].
proof.
proc; while ((!Mon2.inrun /\ Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
             (potF kA qB qH Count.ca Count.cb Count.ch Fwd.odd R.RO.m Fwd.p (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr).
- by move=> &hr; apply xle_cxr_r.
- conseq (_ : ((!Mon2.inrun /\ Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
             (potF kA qB qH Count.ca Count.cb Count.ch Fwd.odd R.RO.m Fwd.p (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr) ==> _).
  + by move=> &hr; apply xle_cxr_r.
  + by move=> &hr; apply xle_cxr_r.
  wp; call (mon2_h_fin kA qB qH); call (mon2_a_fin kA qB qH); call (mon2_b_fin kA qB qH); skip => &hr.
  by apply xlexx.
by auto.
qed.


(* The share of a query in the budgets, and what is left of them with the allowance of the
   finalization; a query raises the risk of both chains. *)
op costq (c : point) : real =
  (if isA c then 12%r * p1 * e128 else 0%r) + (if isB c then e128 else 0%r) + (if !isA c /\ !isB c then e256 else 0%r).

op budK (kA qB qH ca cb ch : int) : real =
  (24%r * p1 * (kA - ca)%r + 2%r * (qB - cb)%r + 155%r) * e128 + (2%r * (qH - ch)%r + 12%r) * e256.

lemma budK_ge0 kA qB qH ca cb ch : ca <= kA => cb <= qB => ch <= qH => 0%r <= budK kA qB qH ca cb ch.
proof.
move=> ha hb hh; have := p1_ge0; have := e128_gt0; have := e256_gt0.
have : 0%r <= (kA - ca)%r by smt(). have : 0%r <= (qB - cb)%r by smt(). have : 0%r <= (qH - ch)%r by smt().
by rewrite /budK; smt().
qed.

lemma budK_step kA qB qH ca cb ch c :
  budK kA qB qH (ca + b2i (isA c)) (cb + b2i (isB c)) (ch + b2i (!isA c /\ !isB c)) =
  budK kA qB qH ca cb ch - 2%r * costq c.
proof. by rewrite /budK /costq /b2i; case: (isA c) => _; case: (isB c) => _ /=; rewrite ?fromintD ?fromintB; ring. qed.

(* The potential of the adversary's run: the expected risk of both chains of a password drawn from
   dP, and the budgets left. *)
op phiK (kA qB qH ca cb ch : int) (m : (point, ans) fmap) (fs bs : pw -> cst) : real =
  if ca <= kA /\ cb <= qB /\ ch <= qH
  then big predT (fun w => mu1 dP w * (psi false w (fun x => x \in m) (fs w) + psi true w (fun x => x \in m) (bs w)))
         PwT.enum + budK kA qB qH ca cb ch
  else 0%r.

lemma Ep_sum2 (F G : ans -> real) : (forall r, 0%r <= F r) => (forall r, 0%r <= G r) =>
  Ep dans (fun r => (F r + G r)%xr) = Ep dans (fun r => (F r)%xr) + Ep dans (fun r => (G r)%xr).
proof.
move=> hF hG; rewrite (eq_Ep _ _ ((fun r => (F r)%xr) + (fun r => (G r)%xr))) => [r _ /= | ]; 2: by rewrite EpD.
by have h1 := hF r; have h2 := hG r; rewrite -(of_realD _ _ h1 h2).
qed.

lemma big_mu2 (a b : pw -> real) :
  big predT (fun w => mu1 dP w * (a w + b w)) PwT.enum =
  big predT (fun w => mu1 dP w * a w) PwT.enum + big predT (fun w => mu1 dP w * b w) PwT.enum.
proof. by rewrite -big_split; apply eq_bigr => w _ /=; ring. qed.

lemma phiK_ge0 kA qB qH ca cb ch m fs bs : (forall w, shape false w (fs w)) => (forall w, shape true w (bs w)) =>
  0%r <= phiK kA qB qH ca cb ch m fs bs.
proof.
move=> hsf hsb; rewrite /phiK; case: (ca <= kA /\ cb <= qB /\ ch <= qH) => // -[ha [hb hh]].
have := budK_ge0 _ _ _ _ _ _ ha hb hh.
have : 0%r <= big predT (fun w => mu1 dP w * (psi false w (fun x => x \in m) (fs w) + psi true w (fun x => x \in m) (bs w)))
                 PwT.enum.
- by apply StdBigop.Bigreal.sumr_ge0 => w _ /=; smt(psi_ge0 ge0_mu).
smt().
qed.

(* One query of the adversary's run, in a batch of its own: both risks rise by its share of the
   budgets when it is submitted, and do not rise in expectation when it is answered. *)
lemma Ep_runK kA qB qH ca cb ch ca' cb' ch' (m : (point, ans) fmap) (fs bs : pw -> cst) c :
  (forall w, shape false w (fs w)) => (forall w, shape true w (bs w)) =>
  ca' = ca + b2i (isA c) => cb' = cb + b2i (isB c) => ch' = ch + b2i (!isA c /\ !isB c) =>
  Ep dans (fun r =>
    if c \notin m then
      ((forall w, shape false w (cstep false w (fs w) c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r])) /\
       (forall w, shape true w (cstep true w (bs w) c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r]))) `|`
      (phiK kA qB qH ca' cb' ch' m.[c <- r]
         (fun w => cstep false w (fs w) c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r])
         (fun w => cstep true w (bs w) c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r]))%xr
    else
      ((forall w, shape false w (cstep false w (fs w) c (c \notin m) (oget m.[c]) [] m)) /\
       (forall w, shape true w (cstep true w (bs w) c (c \notin m) (oget m.[c]) [] m))) `|`
      (phiK kA qB qH ca' cb' ch' m
         (fun w => cstep false w (fs w) c (c \notin m) (oget m.[c]) [] m)
         (fun w => cstep true w (bs w) c (c \notin m) (oget m.[c]) [] m))%xr)
  <= (phiK kA qB qH ca cb ch m fs bs)%xr.
proof.
move=> hsf hsb -> -> ->.
have hg : forall fresh r' (m' : (point, ans) fmap),
  ((forall w, shape false w (cstep false w (fs w) c fresh r' [] m')) /\
   (forall w, shape true w (cstep true w (bs w) c fresh r' [] m'))) = true.
- by move=> *; rewrite eqT; split => w; apply shape_cstep; [apply hsf | apply hsb].
have hc0 : 0%r <= costq c by rewrite /costq; smt(p1_ge0 e128_gt0 e256_gt0).
have hstep := budK_step kA qB qH ca cb ch c.
case: (c \in m) => cm /=.
- have hf : (fun w => cstep false w (fs w) c false (oget m.[c]) [] m) = fs by apply fun_ext => w; rewrite /cstep.
  have hb : (fun w => cstep true w (bs w) c false (oget m.[c]) [] m) = bs by apply fun_ext => w; rewrite /cstep.
  rewrite hg hf hb /= EpC dans_ll smul1m; apply xle_rle; split; 1: by apply phiK_ge0.
  have := phiK_ge0 kA qB qH ca cb ch m fs bs hsf hsb.
  by rewrite /phiK hstep /b2i; smt().
rewrite (eq_Ep _ _ (fun r => (phiK kA qB qH (ca + b2i (isA c)) (cb + b2i (isB c)) (ch + b2i (!isA c /\ !isB c)) m.[c <- r]
           (fun w => cstep false w (fs w) c true r [] m.[c <- r]) (fun w => cstep true w (bs w) c true r [] m.[c <- r]))%xr)).
- by move=> r _ /=; rewrite get_set_sameE oget_some hg.
case: (ca + b2i (isA c) <= kA /\ cb + b2i (isB c) <= qB /\ ch + b2i (!isA c /\ !isB c) <= qH) => hg'; last first.
- rewrite (eq_Ep _ _ (fun _ => 0%xr)) => [r _ /= | ]; 1: by rewrite /phiK hg'.
  by rewrite EpC dans_ll smul1m; apply xle0x.
have [ha [hb hh]] : ca <= kA /\ cb <= qB /\ ch <= qH by move: hg'; rewrite /b2i; smt().
have [ha' [hb' hh']] := hg'.
pose S1 := fun x => x \in m \/ x = c.
have hS : forall r, (fun x => x \in m.[c <- r]) = S1 by move=> r; apply fun_ext => x; rewrite /S1 mem_set.
have hS1 : forall r q, (q \in m.[c <- r] \/ q \in []) = S1 q by move=> r q; rewrite /S1 mem_set.
rewrite (eq_Ep _ _ (fun r => (big predT (fun w => mu1 dP w * (psi false w S1 (cstep false w (fs w) c true r [] m.[c <- r]) +
                                 psi true w S1 (cstep true w (bs w) c true r [] m.[c <- r]))) PwT.enum
                              + budK kA qB qH (ca + b2i (isA c)) (cb + b2i (isB c)) (ch + b2i (!isA c /\ !isB c)))%xr)).
- by move=> r _ /=; rewrite /phiK hg' (hS r).
apply (xle_trans _ _ _ (Ep_sum_le _ _ (fun w => psi false w S1 (fs w) + psi true w S1 (bs w)) _ _ dans_ll _ _ _ _)).
- by move=> w r /=; smt(psi_ge0 shape_cstep).
- by move=> w /=; smt(psi_ge0).
- exact (budK_ge0 _ _ _ _ _ _ ha' hb' hh').
- move=> w /=; have g1 := psi_ge0 false w S1 (fs w) (hsf w); have g2 := psi_ge0 true w S1 (bs w) (hsb w).
  rewrite (Ep_sum2 (fun r => psi false w S1 (cstep false w (fs w) c true r [] m.[c <- r]))
                   (fun r => psi true w S1 (cstep true w (bs w) c true r [] m.[c <- r]))).
  + by move=> r; apply psi_ge0; apply shape_cstep; apply hsf.
  + by move=> r; apply psi_ge0; apply shape_cstep; apply hsb.
  have -> : (psi false w S1 (fs w) + psi true w S1 (bs w))%xr = (psi false w S1 (fs w))%xr + (psi true w S1 (bs w))%xr.
  + by rewrite /= -(of_realD _ _ g1 g2).
  apply xler_add.
  + by apply (Ep_answer false w m c [] (fs w) S1 (hsf w) _ hS1); rewrite /S1.
  by apply (Ep_answer true w m c [] (bs w) S1 (hsb w) _ hS1); rewrite /S1.
have s1 := sum_psi_add false (fun x => x \in m) c fs hsf.
have s2 := sum_psi_add true (fun x => x \in m) c bs hsb.
have e1 := big_mu2 (fun w => psi false w S1 (fs w)) (fun w => psi true w S1 (bs w)).
have e2 := big_mu2 (fun w => psi false w (fun x => x \in m) (fs w)) (fun w => psi true w (fun x => x \in m) (bs w)).
move: s1 s2 e1 e2; rewrite /= -/S1 => s1 s2 e1 e2.
rewrite /phiK ha hb hh /= hstep e1 e2; apply le_pos; move: s1 s2; rewrite /costq; smt().
qed.

lemma count_a_run kA qB qH : ehoare [Count(Mon2).a :
  (Mon2.inrun /\ (forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|`
  (phiK kA qB qH Count.ca Count.cb Count.ch R.RO.m Fwd.sts Bwd.sts)%xr ==>
  (Mon2.inrun /\ (forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|`
  (phiK kA qB qH Count.ca Count.cb Count.ch R.RO.m Fwd.sts Bwd.sts)%xr].
proof.
proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi [hsf hsb]]; rewrite hi /=.
by apply (Ep_runK _ _ _ _ _ _ _ _ _ _ _ _ _ hsf hsb); rewrite /b2i.
qed.

lemma count_b_run kA qB qH : ehoare [Count(Mon2).b :
  (Mon2.inrun /\ (forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|`
  (phiK kA qB qH Count.ca Count.cb Count.ch R.RO.m Fwd.sts Bwd.sts)%xr ==>
  (Mon2.inrun /\ (forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|`
  (phiK kA qB qH Count.ca Count.cb Count.ch R.RO.m Fwd.sts Bwd.sts)%xr].
proof.
proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi [hsf hsb]]; rewrite hi /=.
by apply (Ep_runK _ _ _ _ _ _ _ _ _ _ _ _ _ hsf hsb); rewrite /b2i.
qed.

lemma count_h_run kA qB qH : ehoare [Count(Mon2).h :
  (Mon2.inrun /\ (forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|`
  (phiK kA qB qH Count.ca Count.cb Count.ch R.RO.m Fwd.sts Bwd.sts)%xr ==>
  (Mon2.inrun /\ (forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|`
  (phiK kA qB qH Count.ca Count.cb Count.ch R.RO.m Fwd.sts Bwd.sts)%xr].
proof.
proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi [hsf hsb]]; rewrite hi /=.
by apply (Ep_runK _ _ _ _ _ _ _ _ _ _ _ _ _ hsf hsb); rewrite /b2i.
qed.

(* At the start every chain carries the 66 pairs of its own A points, and the budgets are unused. *)
lemma phiK_init kA qB qH x y : 0 <= kA => 0 <= qB => 0 <= qH =>
  phiK kA qB qH 0 0 0 empty (fun _ => cfwd x) (fun _ => cbwd y) =
  (24%r * p1 * kA%r + 2%r * qB%r + 287%r) * e128 + (2%r * qH%r + 12%r) * e256.
proof.
move=> hkA hqB hqH.
have hS : forall c, !(c \in empty<:point, ans>) by move=> c; rewrite mem_empty.
have h66 : forall bwd w st, st.`chain = [PB (rd (if bwd then 11 else 0), st.`cur)] => !st.`early =>
             psi bwd w (fun x => x \in empty<:point, ans>) st = 66%r * e128.
- move=> bwd w st hc he; rewrite /psi he /= /rho /nA hc /=.
  have -> : hitA (fun x => x \in empty<:point, ans>) w = 0%r by rewrite /hitA mu0_false // => s _; apply hS.
  rewrite big1 /=; 1: by move=> j; rewrite /hitB mu0_false //; smt(mem_empty).
  rewrite big1 /=; 1: by move=> j; rewrite /hitH mu0_false //; smt(mem_empty).
  smt().
rewrite /phiK /= hkA hqB hqH /=.
rewrite (eq_bigr _ _ (fun w => mu1 dP w * (66%r * e128 + 66%r * e128))) => [w _ /= | ].
- by rewrite (h66 false w (cfwd x)) 1,2:/cfwd // (h66 true w (cbwd y)) 1,2:/cbwd.
by rewrite -mulr_suml sum_dP /budK; ring.
qed.

(* After the decryption the potential bounds Early, with no odd query, the budgets kept and both
   chains shaped. *)
lemma post_leK kA qB qH ca cb ch (inrun odd : bool) m (pf pb : pw) (f b : cst) :
  ((f.`early \/ b.`early) /\ !odd /\ ca <= kA /\ cb <= qB /\ ch <= qH /\
   pf = pb /\ shape false pf f /\ shape true pb b)%xr <=
  (!inrun /\ pf = pb /\ shape false pf f /\ shape true pb b) `|` (potF kA qB qH ca cb ch odd m pf f b)%xr.
proof.
apply xle_cxr_r => -[_ [hp [hsf hsb]]]; move: hsb; rewrite -hp => hsb.
apply xle_rle; split; 1: by apply b2r_ge0.
by have := potF_ge0 kA qB qH ca cb ch odd m pf f b hsf hsb; rewrite /potF; smt().
qed.

(* Drawing P after the run: the potential of the run bounds the expected potential of the
   finalization, whose allowance is at most the 155 e128 + 12 e256 kept in the budgets. *)
lemma run_decK kA qB qH ca cb ch (inrun odd : bool) (m : (point, ans) fmap) (fs bs : pw -> cst) :
  Ep dP (fun p => (!false /\ p = p /\ shape false p (fs p) /\ shape true p (bs p)) `|`
                  (potF kA qB qH ca cb ch odd m p (fs p) (bs p))%xr) <=
  (inrun /\ (forall w, shape false w (fs w)) /\ (forall w, shape true w (bs w))) `|`
  (phiK kA qB qH ca cb ch m fs bs)%xr.
proof.
apply xle_cxr_r => -[_ [hsf hsb]].
pose F := fun p => if ca <= kA /\ cb <= qB /\ ch <= qH
                   then psi false p (fun x => x \in m) (fs p) + psi true p (fun x => x \in m) (bs p) + allowF (fs p)
                   else 0%r.
have hF : forall p, 0%r <= F p.
- move=> p; rewrite /F; have := psi_ge0 false p (fun x => x \in m) (fs p) (hsf p).
  by have := psi_ge0 true p (fun x => x \in m) (bs p) (hsb p); have := allowF_ge0 p (fs p) (hsf p); smt().
apply (xle_trans (Ep dP (fun p => (F p)%xr))).
- apply le_Ep => p _ /=; rewrite hsf hsb /=; apply le_pos.
  rewrite /F; case: (ca <= kA /\ cb <= qB /\ ch <= qH) => hg; 2: by rewrite /potF hg.
  by apply potF_le; [apply hsf | apply hsb].
rewrite (Ep_fin PwT.enum) ?PwT.enum_uniq; 1: by move=> p _; apply PwT.enumP.
rewrite (BXA.eq_bigr _ _ (fun p => (mu1 dP p * F p)%xr)) => [p _ /= | ].
- by rewrite -(of_realM _ _ (ge0_mu dP (pred1 p)) (hF p)).
rewrite bigXR; 1: by move=> p _; have := hF p; have := ge0_mu dP (pred1 p); smt().
apply xle_rle; split.
- by apply StdBigop.Bigreal.sumr_ge0 => p _ /=; have := hF p; have := ge0_mu dP (pred1 p); smt().
rewrite /F /phiK; case: (ca <= kA /\ cb <= qB /\ ch <= qH) => hg /=; last by rewrite big1_eq.
have [ha [hb hh]] := hg.
have -> : big predT (fun p => mu1 dP p * (psi false p (fun x => x \in m) (fs p) + psi true p (fun x => x \in m) (bs p)
                                         + allowF (fs p))) PwT.enum =
          big predT (fun p => mu1 dP p * (psi false p (fun x => x \in m) (fs p) + psi true p (fun x => x \in m) (bs p)))
            PwT.enum + big predT (fun p => mu1 dP p * allowF (fs p)) PwT.enum.
- by rewrite -big_split; apply eq_bigr => p _ /=; ring.
have hA : big predT (fun p => mu1 dP p * allowF (fs p)) PwT.enum <= 155%r * e128 + 12%r * e256.
- apply (StdOrder.RealOrder.ler_trans (big predT (fun p => mu1 dP p * (155%r * e128 + 12%r * e256)) PwT.enum)).
  + apply StdBigop.Bigreal.ler_sum => p _ /=; have := allowF_le p (fs p) (hsf p).
    by have := ge0_mu dP (pred1 p); smt().
  by rewrite -mulr_suml sum_dP.
have hB : 155%r * e128 + 12%r * e256 <= budK kA qB qH ca cb ch.
- rewrite /budK; have := p1_ge0; have := e128_gt0; have := e256_gt0.
  have : 0%r <= (kA - ca)%r by smt(). have : 0%r <= (qB - cb)%r by smt(). have : 0%r <= (qH - ch)%r by smt().
  smt().
smt().
qed.

lemma inv_shape bwd inr m log bn p st0 st : inv bwd inr m log bn p st0 st => shape bwd p st.
proof. by move=> [_ [_ [hsh _]]]. qed.

(* ---- Lemma K2, Cross ----------------------------------------------------------------------- *)
(* The A point of round i of a chain, once it is defined. *)
op aP (bwd : bool) (st : cst) (i : int) : point option =
  if 3 * ndone bwd i + 1 < size st.`chain then Some (nth witness st.`chain (3 * ndone bwd i + 1)) else None.

(* The risk of Cross at a pair of rounds: e128 while one of the two A points is undefined, and their
   equality once both are; 0 after Early. *)
op phiX (a a' : point option) : real = if a <> None /\ a' <> None then b2r (a = a') else e128.

op psiX (f b : cst) : real =
  if f.`early \/ b.`early then 0%r
  else bigi predT (fun i => bigi predT (fun i' => if i <> i' then phiX (aP false f i) (aP true b i') else 0%r) 0 12)
         0 12.

lemma phiX_ge0 a a' : 0%r <= phiX a a'.
proof. by rewrite /phiX; smt(e128_gt0 b2r_ge0). qed.

lemma psiX_ge0 f b : 0%r <= psiX f b.
proof.
rewrite /psiX; case: (f.`early \/ b.`early) => // _.
by apply StdBigop.Bigreal.sumr_ge0 => i _ /=; apply StdBigop.Bigreal.sumr_ge0 => i' _ /=; smt(phiX_ge0).
qed.

(* The answer at the last point of a chain defines its A point of round i exactly when that point is
   the B point of round i. *)
op grows (bwd : bool) (st : cst) (c : point) (i : int) =
  !st.`fin /\ last witness st.`chain = c /\ isB c /\ 3 * ndone bwd i + 1 = size st.`chain.

lemma aP_grow bwd w st c r (m : (point, ans) fmap) i : grows bwd st c i =>
  aP bwd st i = None /\ aP bwd (cstep bwd w st c true r [] m) i = Some (PA (w, salt_of r)).
proof.
move=> [hf [hl [hB hk]]]; rewrite /aP hk /= /cstep hf hl /= hB /push /= size_rcons /=.
by rewrite nth_rcons; smt().
qed.

lemma aP_keep bwd w st c r (m : (point, ans) fmap) i : shape bwd w st => !grows bwd st c i =>
  aP bwd (cstep bwd w st c true r [] m) i = aP bwd st i.
proof.
move=> [_ [_ [hsz _]]] hg; rewrite /cstep /=.
case: (!st.`fin /\ last witness st.`chain = c) => hc /=; last by [].
have [hf hl] := hc; move: hsz; rewrite hl => hsz.
case: (isB c) => hB /=.
- have hk : 3 * ndone bwd i + 1 <> size st.`chain by move: hg; rewrite /grows hf hl hB.
  by rewrite /aP /push /= size_rcons nth_rcons; smt().
case: (isA c) => hA /=.
- rewrite /aP /push /= size_rcons nth_rcons; have := posA c hA; smt().
case: (if bwd then 0 < st.`ri else st.`ri < 11) => hm /=.
- rewrite /aP /push /= size_rcons nth_rcons; have := posH c hA hB; smt().
by rewrite /aP.
qed.

lemma mu_PA w v : mu dans (fun r => PA (w, salt_of r) = v) <= e128.
proof.
case: v => [[w' s'] | p | p] /=; 2,3: by rewrite mu0_false; smt(e128_gt0).
apply (StdOrder.RealOrder.ler_trans (mu dans (fun r => salt_of r = s'))); 1: by apply mu_le => /#.
by have := dans_salt (pred1 s'); rewrite /pred1 => ->; rewrite dhalf1 /e128.
qed.

(* One answer keeps the expected risk of a pair of distinct rounds: a defined A point never changes,
   and a new one is PA(w, salt) with a fresh salt; one answer defines both only when i = i'. *)
lemma Ep_phiX wf wb f b c (m : (point, ans) fmap) i i' :
  shape false wf f => shape true wb b => 0 <= i < 12 => 0 <= i' < 12 => i <> i' =>
  Ep dans (fun r => (phiX (aP false (cstep false wf f c true r [] m.[c <- r]) i)
                          (aP true (cstep true wb b c true r [] m.[c <- r]) i'))%xr)
  <= (phiX (aP false f i) (aP true b i'))%xr.
proof.
move=> hsf hsb hi hi' hne.
case: (grows false f c i) => gf; case: (grows true b c i') => gb.
- have [_ [hlf [hB hkf]]] := gf; have [_ [hlb [_ hkb]]] := gb.
  have [hrf [_ [hszf [_ [_ [_ hlr_f]]]]]] := hsf; have [hrb [_ [hszb [_ [_ [_ hlr_b]]]]]] := hsb.
  have hA : !isA c by smt(posA posB).
  have e1 := hlr_f _; 1: by rewrite hlf.
  have e2 := hlr_b _; 1: by rewrite hlb.
  move: hkf hkb hszf hszb e1 e2; rewrite hlf hlb (posB _ hB) /ndone /=.
  smt(rd_inj).
- have [hN0 _] := aP_grow false wf f c witness empty i gf.
  rewrite (eq_Ep _ _ (fun r => (phiX (Some (PA (wf, salt_of r))) (aP true b i'))%xr)) => [r _ /= | ].
  + have [_ ->] := aP_grow false wf f c r m.[c <- r] i gf.
    by rewrite (aP_keep true wb b c r m.[c <- r] i' hsb gb).
  rewrite /phiX hN0 /=.
  case: (aP true b i') => [| v] /=; 1: by rewrite EpC dans_ll.
  by rewrite Ep_mu; apply xle_rle; split; [apply ge0_mu | move=> _; apply mu_PA].
- have [hN0 _] := aP_grow true wb b c witness empty i' gb.
  rewrite (eq_Ep _ _ (fun r => (phiX (aP false f i) (Some (PA (wb, salt_of r))))%xr)) => [r _ /= | ].
  + have [_ ->] := aP_grow true wb b c r m.[c <- r] i' gb.
    by rewrite (aP_keep false wf f c r m.[c <- r] i hsf gf).
  rewrite /phiX hN0 /=.
  case: (aP false f i) => [| u] /=; 1: by rewrite EpC dans_ll.
  rewrite Ep_mu (mu_eq _ _ (fun r => PA (wb, salt_of r) = u)) 1:/#.
  by apply xle_rle; split; [apply ge0_mu | move=> _; apply mu_PA].
rewrite (eq_Ep _ _ (fun _ => (phiX (aP false f i) (aP true b i'))%xr)) => [r _ /= | ].
- by rewrite (aP_keep false wf f c r m.[c <- r] i hsf gf) (aP_keep true wb b c r m.[c <- r] i' hsb gb).
by rewrite EpC dans_ll.
qed.

(* The expectation of a sum is at most the sum of the bounds. *)
lemma Ep_big_le (F : int -> ans -> real) (G : int -> real) (l : int list) :
  (forall j r, 0%r <= F j r) => (forall j, 0%r <= G j) =>
  (forall j, j \in l => Ep dans (fun r => (F j r)%xr) <= (G j)%xr) =>
  Ep dans (fun r => (big predT (fun j => F j r) l)%xr) <= (big predT G l)%xr.
proof.
move=> hF hG; elim: l => [|j l ih] hE.
- rewrite big_nil (eq_Ep _ _ (fun _ => (0%r)%xr)) => [r _ /= | ]; 1: by rewrite big_nil.
  by rewrite EpC dans_ll.
have hl : forall r, 0%r <= big predT (fun j => F j r) l by move=> r; apply StdBigop.Bigreal.sumr_ge0 => *; apply hF.
have hl' : 0%r <= big predT G l by apply StdBigop.Bigreal.sumr_ge0 => *; apply hG.
rewrite (eq_Ep _ _ ((fun r => (F j r)%xr) + (fun r => (big predT (fun j => F j r) l)%xr))) => [r _ /= | ].
- by rewrite big_cons /predT /= -(of_realD _ _ (hF j r) (hl r)).
have -> : (big predT G (j :: l))%xr = (G j)%xr + (big predT G l)%xr.
- by rewrite big_cons /predT /= -(of_realD _ _ (hG j) hl').
rewrite EpD; apply xler_add; 1: by apply hE; rewrite in_cons.
by apply ih => j' hj'; apply hE; rewrite in_cons hj'.
qed.

(* One answer keeps the expected risk of Cross. *)
lemma Ep_psiX wf wb f b c (m : (point, ans) fmap) : shape false wf f => shape true wb b =>
  Ep dans (fun r => (psiX (cstep false wf f c true r [] m.[c <- r]) (cstep true wb b c true r [] m.[c <- r]))%xr)
  <= (psiX f b)%xr.
proof.
move=> hsf hsb; case: (f.`early \/ b.`early) => he.
- rewrite (eq_Ep _ _ (fun _ => (0%r)%xr)) => [r _ /= | ]; 2: by rewrite EpC dans_ll /psiX he.
  have : (cstep false wf f c true r [] m.[c <- r]).`early \/ (cstep true wb b c true r [] m.[c <- r]).`early.
  + by case: he => h; [left | right]; apply early_mono.
  by rewrite /psiX => ->.
apply (xle_trans (Ep dans (fun r => (bigi predT (fun i => bigi predT (fun i' => if i <> i' then
          phiX (aP false (cstep false wf f c true r [] m.[c <- r]) i) (aP true (cstep true wb b c true r [] m.[c <- r]) i')
          else 0%r) 0 12) 0 12)%xr))).
- apply le_Ep => r _ /=; apply le_pos; rewrite /psiX.
  case: ((cstep false wf f c true r [] m.[c <- r]).`early \/ (cstep true wb b c true r [] m.[c <- r]).`early) => // _.
  by apply StdBigop.Bigreal.sumr_ge0 => i _ /=; apply StdBigop.Bigreal.sumr_ge0 => i' _ /=; smt(phiX_ge0).
rewrite /psiX he /=; apply Ep_big_le => [i r | i | i /mem_range hi].
- by apply StdBigop.Bigreal.sumr_ge0 => i' _ /=; smt(phiX_ge0).
- by apply StdBigop.Bigreal.sumr_ge0 => i' _ /=; smt(phiX_ge0).
apply Ep_big_le => [i' r | i' | i' /mem_range hi' /=]; 1,2: smt(phiX_ge0).
case: (i <> i') => hne /=; 2: by rewrite EpC dans_ll.
exact (Ep_phiX wf wb f b c m i i' hsf hsb hi hi' hne).
qed.

(* The risk of Cross during the run, for a password drawn from dP. *)
op PsiX (fs bs : pw -> cst) : real = big predT (fun w => mu1 dP w * psiX (fs w) (bs w)) PwT.enum.

lemma Ep_runX (m : (point, ans) fmap) (fs bs : pw -> cst) c :
  (forall w, shape false w (fs w)) => (forall w, shape true w (bs w)) =>
  Ep dans (fun r =>
    if c \notin m then
      ((forall w, shape false w (cstep false w (fs w) c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r])) /\
       (forall w, shape true w (cstep true w (bs w) c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r]))) `|`
      (PsiX (fun w => cstep false w (fs w) c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r])
            (fun w => cstep true w (bs w) c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r]))%xr
    else
      ((forall w, shape false w (cstep false w (fs w) c (c \notin m) (oget m.[c]) [] m)) /\
       (forall w, shape true w (cstep true w (bs w) c (c \notin m) (oget m.[c]) [] m))) `|`
      (PsiX (fun w => cstep false w (fs w) c (c \notin m) (oget m.[c]) [] m)
            (fun w => cstep true w (bs w) c (c \notin m) (oget m.[c]) [] m))%xr)
  <= (PsiX fs bs)%xr.
proof.
move=> hsf hsb.
have hg : forall fresh r' (m' : (point, ans) fmap),
  ((forall w, shape false w (cstep false w (fs w) c fresh r' [] m')) /\
   (forall w, shape true w (cstep true w (bs w) c fresh r' [] m'))) = true.
- by move=> *; rewrite eqT; split => w; apply shape_cstep; [apply hsf | apply hsb].
case: (c \in m) => cm /=.
- have hf : (fun w => cstep false w (fs w) c false (oget m.[c]) [] m) = fs by apply fun_ext => w; rewrite /cstep.
  have hb : (fun w => cstep true w (bs w) c false (oget m.[c]) [] m) = bs by apply fun_ext => w; rewrite /cstep.
  by rewrite hg hf hb /= EpC dans_ll smul1m.
rewrite (eq_Ep _ _ (fun r => (big predT (fun w => mu1 dP w * psiX (cstep false w (fs w) c true r [] m.[c <- r])
                                 (cstep true w (bs w) c true r [] m.[c <- r])) PwT.enum + 0%r)%xr)).
- by move=> r _ /=; rewrite get_set_sameE oget_some hg /= /PsiX.
apply (xle_trans _ _ _ (Ep_sum_le _ _ (fun w => psiX (fs w) (bs w)) _ _ dans_ll _ _ _ _)).
- by move=> w r /=; apply psiX_ge0.
- by move=> w /=; apply psiX_ge0.
- done.
- by move=> w /=; apply (Ep_psiX w w (fs w) (bs w) c m (hsf w) (hsb w)).
by rewrite /PsiX /=; smt().
qed.

lemma Ep_finX wf wb f b c (m : (point, ans) fmap) :
  shape false wf f => shape true wb b =>
  Ep dans (fun r =>
    if c \notin m then
      (shape false wf (cstep false wf f c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r]) /\
       shape true wb (cstep true wb b c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r])) `|`
      (psiX (cstep false wf f c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r])
            (cstep true wb b c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r]))%xr
    else
      (shape false wf (cstep false wf f c (c \notin m) (oget m.[c]) [] m) /\
       shape true wb (cstep true wb b c (c \notin m) (oget m.[c]) [] m)) `|`
      (psiX (cstep false wf f c (c \notin m) (oget m.[c]) [] m) (cstep true wb b c (c \notin m) (oget m.[c]) [] m))%xr)
  <= (psiX f b)%xr.
proof.
move=> hsf hsb.
have hg : forall fresh r' (m' : (point, ans) fmap),
  (shape false wf (cstep false wf f c fresh r' [] m') /\ shape true wb (cstep true wb b c fresh r' [] m')) = true.
- by move=> *; rewrite eqT; split; apply shape_cstep.
case: (c \in m) => cm /=.
- by rewrite /cstep /= hsf hsb /= EpC dans_ll smul1m.
rewrite (eq_Ep _ _ (fun r => (psiX (cstep false wf f c true r [] m.[c <- r]) (cstep true wb b c true r [] m.[c <- r]))%xr)).
- by move=> r _ /=; rewrite get_set_sameE oget_some hg.
exact (Ep_psiX wf wb f b c m hsf hsb).
qed.

lemma count_a_runX : ehoare [Count(Mon2).a :
  ((forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|` (PsiX Fwd.sts Bwd.sts)%xr ==>
  ((forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|` (PsiX Fwd.sts Bwd.sts)%xr].
proof. by proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hsf hsb]; apply (Ep_runX _ _ _ _ hsf hsb). qed.

lemma count_b_runX : ehoare [Count(Mon2).b :
  ((forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|` (PsiX Fwd.sts Bwd.sts)%xr ==>
  ((forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|` (PsiX Fwd.sts Bwd.sts)%xr].
proof. by proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hsf hsb]; apply (Ep_runX _ _ _ _ hsf hsb). qed.

lemma count_h_runX : ehoare [Count(Mon2).h :
  ((forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|` (PsiX Fwd.sts Bwd.sts)%xr ==>
  ((forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|` (PsiX Fwd.sts Bwd.sts)%xr].
proof. by proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hsf hsb]; apply (Ep_runX _ _ _ _ hsf hsb). qed.

lemma mon2_a_finX : ehoare [Mon2.a :
  (shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|` (psiX (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr ==>
  (shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|` (psiX (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr].
proof. by proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hsf hsb]; apply (Ep_finX _ _ _ _ _ _ hsf hsb). qed.

lemma mon2_b_finX : ehoare [Mon2.b :
  (shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|` (psiX (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr ==>
  (shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|` (psiX (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr].
proof. by proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hsf hsb]; apply (Ep_finX _ _ _ _ _ _ hsf hsb). qed.

lemma mon2_h_finX : ehoare [Mon2.h :
  (shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|` (psiX (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr ==>
  (shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|` (psiX (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr].
proof. by proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hsf hsb]; apply (Ep_finX _ _ _ _ _ _ hsf hsb). qed.

lemma enc_eX : ehoare [Net(Mon2).enc :
  (shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|` (psiX (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr ==>
  (shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|` (psiX (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr].
proof.
proc; while ((shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|` (psiX (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr).
- by move=> &hr; apply xle_cxr_r.
- conseq (_ : ((shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|` (psiX (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr) ==> _).
  + by move=> &hr; apply xle_cxr_r.
  + by move=> &hr; apply xle_cxr_r.
  wp; call mon2_h_finX; call mon2_a_finX; call mon2_b_finX; skip => &hr.
  by apply xlexx.
by auto.
qed.

lemma dec_eX : ehoare [Net(Mon2).dec :
  (shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|` (psiX (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr ==>
  (shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|` (psiX (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr].
proof.
proc; while ((shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|` (psiX (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr).
- by move=> &hr; apply xle_cxr_r.
- conseq (_ : ((shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|` (psiX (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr) ==> _).
  + by move=> &hr; apply xle_cxr_r.
  + by move=> &hr; apply xle_cxr_r.
  wp; call mon2_h_finX; call mon2_a_finX; call mon2_b_finX; skip => &hr.
  by apply xlexx.
by auto.
qed.

(* Drawing P after the run. *)
lemma run_decX (fs bs : pw -> cst) :
  Ep dP (fun p => (shape false p (fs p) /\ shape true p (bs p)) `|` (psiX (fs p) (bs p))%xr) <=
  ((forall w, shape false w (fs w)) /\ (forall w, shape true w (bs w))) `|` (PsiX fs bs)%xr.
proof.
apply xle_cxr_r => -[hsf hsb].
rewrite (eq_Ep _ _ (fun p => (psiX (fs p) (bs p))%xr)) => [p _ /= | ]; 1: by rewrite hsf hsb.
rewrite (Ep_fin PwT.enum) ?PwT.enum_uniq; 1: by move=> p _; apply PwT.enumP.
rewrite (BXA.eq_bigr _ _ (fun p => (mu1 dP p * psiX (fs p) (bs p))%xr)) => [p _ /= | ].
- by rewrite -(of_realM _ _ (ge0_mu dP (pred1 p)) (psiX_ge0 (fs p) (bs p))).
rewrite bigXR; 1: by move=> p _; have := psiX_ge0 (fs p) (bs p); have := ge0_mu dP (pred1 p); smt().
by rewrite /PsiX xlexx.
qed.

(* The 132 ordered pairs of distinct rounds. *)
lemma sum_pairs (e : real) :
  bigi predT (fun i => bigi predT (fun i' => if i <> i' then e else 0%r) 0 12) 0 12 = 132%r * e.
proof.
rewrite (eq_big_int 0 12 _ (fun _ => 11%r * e)) => [i hi /= | ].
- rewrite (bigD1 _ _ i) ?mem_range ?range_uniq //=.
  rewrite (eq_bigr _ _ (fun _ => e)) => [i' hi' /= | ]; 1: by move: hi'; rewrite /predC1; smt().
  rewrite StdBigop.Bigreal.sumr_const.
  have := count_predC (pred1 i) (range 0 12).
  rewrite size_range (count_uniq_mem _ _ (range_uniq 0 12)) mem_range hi /b2i /=.
  have -> : predC (pred1 i) = predC1 i by apply fun_ext => j; rewrite /predC /pred1 /predC1 /#.
  smt().
by rewrite StdBigop.Bigreal.sumri_const //; ring.
qed.

lemma PsiX_init x y : PsiX (fun _ => cfwd x) (fun _ => cbwd y) = 132%r * e128.
proof.
have h : psiX (cfwd x) (cbwd y) = 132%r * e128.
- rewrite /psiX /cfwd /cbwd /= -(sum_pairs e128); apply eq_big_int => i hi /=; apply eq_big_int => i' hi' /=.
  by rewrite /phiX /aP /ndone /=; smt().
by rewrite /PsiX (eq_bigr _ _ (fun w => mu1 dP w * (132%r * e128))) => [w _ /= | ]; [rewrite h | rewrite -mulr_suml sum_dP].
qed.

(* A nonnegative term is at most the sum over the rounds. *)
lemma big_ge_term (F : int -> real) i : (forall j, 0%r <= F j) => 0 <= i < 12 => F i <= bigi predT F 0 12.
proof.
move=> hF hi; rewrite (bigD1 _ _ i) ?mem_range ?range_uniq //=.
have : 0%r <= big (predC1 i) F (range 0 12) by apply StdBigop.Bigreal.sumr_ge0 => j _; apply hF.
smt().
qed.

(* At the end, Cross without Early is one of the pairs. *)
lemma post_leX pf pb (f b : cst) :
  (cross f.`chain b.`chain /\ !(f.`early \/ b.`early) /\ f.`fin /\ b.`fin /\ shape false pf f /\ shape true pb b)%xr <=
  (shape false pf f /\ shape true pb b) `|` (psiX f b)%xr.
proof.
apply xle_cxr_r => -[hsf hsb]; apply xle_rle; split; 1: by apply b2r_ge0.
move=> _.
case: (cross f.`chain b.`chain /\ !(f.`early \/ b.`early) /\ f.`fin /\ b.`fin /\ shape false pf f /\ shape true pb b)
  => [[[i i' [hi [hi' [hne he]]]] [hea [hff [hfb _]]]] | _] /=; last by apply psiX_ge0.
have [_ [_ [hszf [_ [_ [hf _]]]]]] := hsf; have [hn hp] := hf hff.
have [_ [_ [hszb [_ [_ [hb _]]]]]] := hsb; have [hn' hp'] := hb hfb.
have h36 : size f.`chain = 36 /\ size b.`chain = 36 by rewrite hszf hszb hn hp hn' hp'.
rewrite /psiX hea /=.
have hge : forall j j', 0%r <= (if j <> j' then phiX (aP false f j) (aP true b j') else 0%r) by smt(phiX_ge0).
apply (StdOrder.RealOrder.ler_trans (bigi predT (fun j' => if i <> j' then phiX (aP false f i) (aP true b j') else 0%r) 0 12)).
- apply (StdOrder.RealOrder.ler_trans (if i <> i' then phiX (aP false f i) (aP true b i') else 0%r)).
  + by rewrite hne /phiX /aP /ndone /=; smt().
  by apply (big_ge_term (fun j' => if i <> j' then phiX (aP false f i) (aP true b j') else 0%r) i' (hge i)).
apply (big_ge_term (fun j => bigi predT (fun j' => if j <> j' then phiX (aP false f j) (aP true b j') else 0%r) 0 12) i).
- by move=> j /=; apply StdBigop.Bigreal.sumr_ge0 => j' _ /=; apply hge.
done.
qed.
