(* The backward chain of a password and the lazy game with finalization (DESIGN-NOTES A.3), for an
   adversary that sees only A, B, H. Lemmas G2, G3 and G5. Argon2id queries may come in batches
   (Corollary G7); every other call is a batch of its own. *)
require import AllCore List Distr DBool FMap StdBigop StdOrder Xreal.
import StdBigop.Bigreal RealOrder.
require import Suite3.
import W128.

(* An inequality of reals read in realp, as xreal goals become after a case split. *)
lemma rp_le (x y : real) : x <= y => x%rp <= y%rp.
proof. by move=> h; rewrite /= /(%pos); smt(). qed.

op isApw (p : pw) (c : point) = with c = PA x => x.`1 = p with c = PB _ => false with c = PH _ => false.

(* The bookkeeping of one chain of a password. The backward chain from Y is
   c_1 = (11, L_12), c_2 = (p, S_11), c_3 = (K_11, 11, R_11), c_4 = (10, R_10), ..., c_36 = (K_0, 0, R_0);
   the forward chain from X is d_1 = (0, R_0), d_2 = (p, S_0), d_3 = (K_0, 0, R_0), d_4 = (1, R_1), ...
   The first point is defined from the start; the next one becomes defined when the answer at the
   last one is sampled fresh. [early] records Early: a point that is already in the table, or pending
   in the current batch, at the moment it becomes defined. *)
type cst = {
  chain : point list;   (* the points defined so far *)
  early : bool;
  fin   : bool;         (* the last round is answered *)
  ri    : int;          (* round of the last point *)
  cur   : W128.word;    (* the half that round reads: R_i *)
  oth   : W128.word;    (* the half its mask is added to: R_(i+1) backward, L_i forward *)
  xs    : state;        (* the end state once complete: (L_0, R_0) backward, W_12 forward *)
}.

op cbwd (y : state) : cst =
  {| chain = [PB (rd 11, y.`1)]; early = false; fin = false; ri = 11; cur = y.`1; oth = y.`2;
     xs = witness |}.

op cfwd (x : state) : cst =
  {| chain = [PB (rd 0, x.`2)]; early = false; fin = false; ri = 0; cur = x.`2; oth = x.`1;
     xs = witness |}.

(* Defines the next point q, with Early if q is already in the table m or pending. *)
op push (st : cst) (q : point) (m : (point, ans) fmap) (pend : point list) : cst =
  {| st with chain = rcons st.`chain q; early = st.`early \/ q \in m \/ q \in pend |}.

(* One step after the answer r at c, with [fresh] telling whether it was sampled just now; m is the
   table after the answer. Backward chains count rounds down, forward chains up. *)
op cstep (bwd : bool) (p : pw) (st : cst) (c : point) (fresh : bool) (r : ans) (pend : point list)
         (m : (point, ans) fmap) : cst =
  if !(fresh /\ !st.`fin /\ last witness st.`chain = c) then st
  else if isB c then push st (PA (p, salt_of r)) m pend
  else if isA c then push st (PH (key_of r, rd st.`ri, st.`cur)) m pend
  else
    let l = st.`oth +^ mask_of r in
    if (if bwd then 0 < st.`ri else st.`ri < 11) then
      let j = if bwd then st.`ri - 1 else st.`ri + 1 in
      {| (push st (PB (rd j, l)) m pend) with ri = j; cur = l; oth = st.`cur |}
    else {| st with fin = true; xs = if bwd then (l, st.`cur) else (st.`cur, l) |}.

(* ---- What the table determines ------------------------------------------------------------- *)
(* The bookkeeping without its Early flag. *)
op strip (st : cst) : cst = {| st with early = false |}.

(* Complete, or its last point is not answered yet. *)
op stopped (m : (point, ans) fmap) (st : cst) = st.`fin \/ last witness st.`chain \notin m.

(* The step that the table's answer at the last point triggers, if it is answered. *)
op adv (bwd : bool) (p : pw) (m : (point, ans) fmap) (st : cst) : cst =
  if stopped m st then st
  else cstep bwd p st (last witness st.`chain) true (oget m.[last witness st.`chain]) [] m.

(* While Early has not happened, the bookkeeping is the first stopped state of [adv] from the start. *)
op determined (bwd : bool) (p : pw) (m : (point, ans) fmap) (st0 st : cst) =
  exists n, 0 <= n /\ strip st = strip (iter n (adv bwd p m) st0) /\
            (forall k, 0 <= k < n => !stopped m (iter k (adv bwd p m) st0)) /\ stopped m st.

lemma strip_cstep bwd p st c fresh r pend pend' (m m' : (point, ans) fmap) :
  strip (cstep bwd p st c fresh r pend m) = strip (cstep bwd p (strip st) c fresh r pend' m').
proof. by rewrite /cstep /push /strip /=; smt(). qed.

lemma strip_cstep_tab bwd p st c fresh r pend pend' (m m' : (point, ans) fmap) :
  strip (cstep bwd p st c fresh r pend m) = strip (cstep bwd p st c fresh r pend' m').
proof. by rewrite (strip_cstep _ _ _ _ _ _ pend pend m m') (strip_cstep _ _ _ _ _ _ pend' pend m' m'). qed.

lemma stopped_strip m st : stopped m (strip st) = stopped m st.
proof. by rewrite /stopped /strip. qed.

lemma adv_strip bwd p m st : strip (adv bwd p m st) = strip (adv bwd p m (strip st)).
proof.
rewrite /adv stopped_strip; case: (stopped m st) => _ //.
by rewrite (strip_cstep _ _ _ _ _ _ [] [] m m) /strip.
qed.

(* An answer at a point that the step does not read changes nothing but Early. *)
lemma adv_ext bwd p (m : (point, ans) fmap) c r st :
  c \notin m => (st.`fin \/ last witness st.`chain <> c) =>
  strip (adv bwd p m.[c <- r] st) = strip (adv bwd p m st).
proof.
move=> cm hc; rewrite /adv /stopped mem_set.
case: (st.`fin) => //= hfin; have hl : last witness st.`chain <> c by smt().
rewrite hl /=; case: (last witness st.`chain \in m) => //= hin.
by rewrite get_set_neqE // (strip_cstep_tab _ _ _ _ _ _ [] [] _ m).
qed.

lemma iter_ext bwd p (m : (point, ans) fmap) c r st0 n :
  c \notin m => 0 <= n => (forall k, 0 <= k < n => !stopped m (iter k (adv bwd p m) st0)) =>
  strip (iter n (adv bwd p m.[c <- r]) st0) = strip (iter n (adv bwd p m) st0).
proof.
move=> cm; elim: n => [|n ge0n ih] hk; 1: by rewrite !iter0.
rewrite !iterS // adv_strip ih; 1: by move=> k hk'; apply hk; smt().
rewrite -adv_strip adv_ext //.
have := hk n _; 1: smt().
by rewrite /stopped negb_or => -[-> /=]; apply/contra => ->.
qed.

lemma determined_init bwd p st0 : stopped empty st0 => determined bwd p empty st0 st0.
proof. by move=> h; exists 0; rewrite iter0 //=; smt(). qed.

lemma stopped_ext (m : (point, ans) fmap) c r st :
  !stopped m st => !stopped m.[c <- r] st.
proof. by rewrite /stopped mem_set => /#. qed.

(* A fresh answer keeps the bookkeeping determined by the table, unless it sets Early. *)
lemma determined_fresh bwd p (m : (point, ans) fmap) st0 st c r pend :
  c \notin m => determined bwd p m st0 st =>
  !(cstep bwd p st c true r pend m.[c <- r]).`early =>
  determined bwd p m.[c <- r] st0 (cstep bwd p st c true r pend m.[c <- r]).
proof.
move=> cm [n [ge0n [hst [htight hstop]]]] hne.
have hext : forall k, 0 <= k <= n =>
  strip (iter k (adv bwd p m.[c <- r]) st0) = strip (iter k (adv bwd p m) st0).
- by move=> k hk; apply iter_ext; [exact cm | smt() | move=> j hj; apply htight; smt()].
have htight' : forall k, 0 <= k < n => !stopped m.[c <- r] (iter k (adv bwd p m.[c <- r]) st0).
- move=> k hk; rewrite -stopped_strip hext 1:/# stopped_strip.
  by apply stopped_ext; apply htight.
case: (st.`fin \/ last witness st.`chain <> c) => hc.
- have -> : cstep bwd p st c true r pend m.[c <- r] = st by rewrite /cstep /#.
  exists n; do! split => //; 1: by rewrite hst hext.
  by move: hstop hc; rewrite /stopped mem_set /#.
have [hfin hl] : !st.`fin /\ last witness st.`chain = c by smt().
exists (n + 1); do! split; 1: smt().
- rewrite iterS // adv_strip hext // -hst -adv_strip /adv /stopped mem_set hfin hl /=.
  by rewrite get_set_sameE (strip_cstep_tab _ _ _ _ _ _ [] pend _ m.[c <- r]).
- move=> k hk; case: (k < n) => hkn; 1: by apply htight'; smt().
  have -> : k = n by smt().
  by rewrite -stopped_strip hext // -hst stopped_strip /stopped mem_set hfin hl.
move: hne; rewrite /stopped /cstep hfin hl /push /=.
by case: (isB c) => //=; case: (isA c) => //= *; smt(last_rcons).
qed.

(* ---- The shape of a chain ----------------------------------------------------------------- *)
op pos (c : point) : int = with c = PA _ => 1 with c = PB _ => 0 with c = PH _ => 2.

(* The round index of a B or H point. *)
op ridxof (c : point) : ridx = with c = PA _ => witness with c = PB x => x.`1 with c = PH x => x.`2.

(* Rounds completed before the round of the last point. *)
op ndone (bwd : bool) (ri : int) : int = if bwd then 11 - ri else ri.

(* The points come in rounds of B, A, H; every A point carries the password; a complete chain ends
   with the H point of its last round; a last B or H point belongs to the current round. *)
op shape (bwd : bool) (p : pw) (st : cst) =
  0 <= st.`ri <= 11 /\ st.`chain <> [] /\
  size st.`chain = 3 * ndone bwd st.`ri + pos (last witness st.`chain) + 1 /\
  count isA st.`chain = ndone bwd st.`ri + b2i (1 <= pos (last witness st.`chain)) /\
  all (fun c => isA c => isApw p c) st.`chain /\
  (st.`fin => ndone bwd st.`ri = 11 /\ pos (last witness st.`chain) = 2) /\
  (!isA (last witness st.`chain) => ridxof (last witness st.`chain) = rd st.`ri).

lemma rcons_ne0 (s : 'a list) x : rcons s x <> [].
proof. by case: s. qed.

lemma count_rcons1 (q : 'a -> bool) (s : 'a list) x : count q (rcons s x) = count q s + b2i (q x).
proof. by rewrite -cats1 count_cat. qed.

lemma all_rcons1 (q : 'a -> bool) (s : 'a list) x : all q (rcons s x) = (all q s /\ q x).
proof. by rewrite -cats1 all_cat. qed.

lemma count_isA_PA (ps : (pw * W128.word) list) : count isA (map PA ps) = size ps.
proof. by elim: ps => [|x l ih] //=; smt(). qed.

lemma shape_bwd p y : shape true p (cbwd y).
proof. by rewrite /shape /cbwd /ndone. qed.

lemma shape_fwd p x : shape false p (cfwd x).
proof. by rewrite /shape /cfwd /ndone. qed.

lemma shape_cstep bwd p st c fresh r pend m :
  shape bwd p st => shape bwd p (cstep bwd p st c fresh r pend m).
proof.
rewrite /cstep; case: (fresh /\ !st.`fin /\ last witness st.`chain = c) => //= -[_ [hfin hl]].
rewrite /shape /ndone /push /= hfin /=; move=> [hri [hne [hsz [hcnt [hall hlr]]]]].
move: hsz hcnt hlr; rewrite hl; case: c hl => [a|b|h] hl /=.
- by rewrite last_rcons size_rcons count_rcons1 all_rcons1 hall rcons_ne0 /= => /#.
- by rewrite last_rcons size_rcons count_rcons1 all_rcons1 hall rcons_ne0 /= => /#.
case: bwd hri => /= hri; [case: (0 < st.`ri) | case: (st.`ri < 11)] => /= hmore;
  rewrite ?last_rcons ?size_rcons ?count_rcons1 ?all_rcons1 ?hall ?rcons_ne0 ?hl /= => /#.
qed.

(* Comp(P): the adversary itself queried all twelve A points of the chain. *)
op comp (chain : point list) (log : (point * int) list) =
  all (fun c => c \in map fst log) (filter isA chain).

(* The batch of the adversary's first query of c. *)
op bnof (log : (point * int) list) (c : point) : int = (nth witness log (index c (map fst log))).`2.

(* ---- The invariant of a run ----------------------------------------------------------------- *)
(* The adversary's queries are logged with their batch numbers. Without Early: if the adversary
   queried a point of the chain, it queried the point before it first, in an earlier batch. *)
op ordered (log : (point * int) list) (chain : point list) =
  forall t, 1 <= t < size chain => nth witness chain t \in map fst log =>
    nth witness chain (t - 1) \in map fst log /\
    bnof log (nth witness chain (t - 1)) < bnof log (nth witness chain t).

(* A point of the chain that the adversary has not queried, whose predecessor was first queried in
   the current batch, is not among the queries [pend] left in that batch. *)
op later (log : (point * int) list) (bn : int) (chain : point list) (pend : point list) =
  forall t, 1 <= t < size chain => !(nth witness chain t \in map fst log) =>
    bnof log (nth witness chain (t - 1)) = bn => !(nth witness chain t \in pend).

(* Logged queries are in the table; during the adversary's run the table holds exactly the logged
   queries. Without Early the chain is ordered, stopped, without repeats, and answered up to its
   last point, and determined by the table. *)
op inv (bwd inrun : bool) (m : (point, ans) fmap) (log : (point * int) list) (bn : int) (p : pw)
       (st0 st : cst) =
  (forall x, x \in map fst log => x \in m) /\
  (inrun => (forall x, x \in m => x \in map fst log) /\ all (fun (e : point * int) => e.`2 <= bn) log) /\
  shape bwd p st /\
  (!st.`early => ordered log st.`chain /\ stopped m st /\ uniq st.`chain /\
                 (forall t, 0 <= t < size st.`chain - 1 => nth witness st.`chain t \in m) /\
                 determined bwd p m st0 st).

lemma bnof_rcons log c b x : bnof (rcons log (c, b)) x =
  if !(x \in map fst log) /\ x = c then b else bnof log x.
proof.
rewrite /bnof map_rcons nth_rcons -cats1 index_cat size_map.
case: (x \in map fst log) => hx /=; 1: by rewrite -(size_map fst) index_mem hx.
have -> : index x (map fst log) = size log.
- by have := index_size x (map fst log); have := index_mem x (map fst log); rewrite hx size_map /#.
rewrite (nth_default _ log (size log)) // index_cons.
case: (x = c) => hxc /=; 1: smt().
have -> : index x [] = 0 by rewrite /index.
by rewrite (_ : !(size log + 1 < size log)) 1:/# (_ : size log + 1 <> size log) 1:/#.
qed.

lemma bnof_le log bn x : x \in map fst log => all (fun (e : point * int) => e.`2 <= bn) log =>
  bnof log x <= bn.
proof.
move=> hx /allP hall; apply (hall (nth witness log (index x (map fst log)))).
by apply mem_nth; rewrite index_ge0 /= -(size_map fst) index_mem.
qed.

(* The batch numbers of the logged A queries. *)
op bset (log : (point * int) list) : int list = map snd (filter (fun (e : point * int) => isA e.`1) log).

lemma bset_rcons log c b : bset (rcons log (c, b)) = if isA c then rcons (bset log) b else bset log.
proof. by rewrite /bset filter_rcons /=; case: (isA c) => _ //=; rewrite map_rcons. qed.

lemma bset_fresh log bn b : all (fun (e : point * int) => e.`2 <= bn) log => bn < b => !(b \in bset log).
proof.
move=> /allP h hb; rewrite /bset mapP negb_exists => e /=; rewrite mem_filter.
by apply/negP => -[[_ he] heq]; have := h e he; rewrite /= -heq /#.
qed.

lemma size_undup_rcons (s : 'a list) x : size (undup (rcons s x)) = size (undup s) + b2i (!(x \in s)).
proof. by elim: s => [|y s ih] /=; [rewrite /b2i | rewrite mem_rcons /=; smt()]. qed.

lemma bnof_bset log x : isA x => x \in map fst log => bnof log x \in bset log.
proof.
move=> hA hx; have hi : 0 <= index x (map fst log) < size log by rewrite index_ge0 -(size_map fst) index_mem.
have h1 := nth_index witness x (map fst log) hx.
rewrite (nth_map witness witness fst) // in h1.
rewrite /bnof /bset; apply/mapP; exists (nth witness log (index x (map fst log))).
rewrite mem_filter mem_nth //=.
by move: h1 => ->.
qed.

(* Along a chain without Early, the batches of the adversary's first queries increase; so the A
   points of the chain lie in as many distinct batches. *)
lemma comp_batches log (chain : point list) : ordered log chain => comp chain log => uniq chain =>
  count isA chain <= size (undup (bset log)).
proof.
rewrite /ordered => hord hc hu.
have hmono : forall k, 0 <= k => forall s, 0 <= s => s + k + 1 < size chain =>
    nth witness chain (s + k + 1) \in map fst log =>
    nth witness chain s \in map fst log /\ bnof log (nth witness chain s) < bnof log (nth witness chain (s + k + 1)).
- elim=> [|k ge0k ih] s hs hk hin; 1: by have := hord (s + 0 + 1) _ hin => /#.
  have [h1 h2] := hord (s + (k + 1) + 1) _ hin; 1: smt().
  have := ih s hs _ _; 1: smt(); 1: by move: h1; rewrite (_ : s + (k + 1) + 1 - 1 = s + k + 1) 1:/#.
  by move: h2; rewrite (_ : s + (k + 1) + 1 - 1 = s + k + 1) 1:/# /#.
have hA : forall x, x \in filter isA chain => x \in map fst log.
- by move: hc; rewrite /comp => /allP.
rewrite -size_filter -(size_map (bnof log)); apply uniq_leq_size.
- rewrite map_inj_in_uniq ?filter_uniq // => x y hx hy hxy.
  move: (hx) (hy); rewrite !mem_filter => -[_ hxc] [_ hyc].
  case: (x = y) => // hne; have hi := index_mem x chain; have hj := index_mem y chain.
  have hij : index x chain <> index y chain.
  + by apply/negP => h; apply hne; rewrite -(nth_index witness x chain hxc) h nth_index.
  case: (index x chain < index y chain) => hlt.
  + have := hmono (index y chain - index x chain - 1) _ (index x chain) _ _ _; 1..3: smt(index_ge0).
    * by rewrite (_ : index x chain + (index y chain - index x chain - 1) + 1 = index y chain) 1:/# nth_index // hA.
    by rewrite (_ : index x chain + (index y chain - index x chain - 1) + 1 = index y chain) 1:/# !nth_index // /#.
  have := hmono (index x chain - index y chain - 1) _ (index y chain) _ _ _; 1..3: smt(index_ge0).
  + by rewrite (_ : index y chain + (index x chain - index y chain - 1) + 1 = index x chain) 1:/# nth_index // hA.
  by rewrite (_ : index y chain + (index x chain - index y chain - 1) + 1 = index x chain) 1:/# !nth_index // /#.
move=> b /mapP [x [hx ->]]; rewrite mem_undup; apply bnof_bset; 2: by apply hA.
by move: hx; rewrite mem_filter.
qed.

(* The cases of one step: nothing happens, a point is pushed, or the chain completes. *)
lemma cstep_cases bwd p st c fresh r pend m :
  (!(fresh /\ !st.`fin /\ last witness st.`chain = c) /\ cstep bwd p st c fresh r pend m = st) \/
  (fresh /\ !st.`fin /\ last witness st.`chain = c /\
   ((exists q, (cstep bwd p st c fresh r pend m).`chain = rcons st.`chain q /\
       (cstep bwd p st c fresh r pend m).`early = (st.`early \/ q \in m \/ q \in pend) /\
       !(cstep bwd p st c fresh r pend m).`fin) \/
    ((cstep bwd p st c fresh r pend m).`chain = st.`chain /\
     (cstep bwd p st c fresh r pend m).`early = st.`early /\ (cstep bwd p st c fresh r pend m).`fin))).
proof.
rewrite /cstep; case: (fresh /\ !st.`fin /\ last witness st.`chain = c) => [[hfr [hfin hl]] | _]; 2: by left.
right; rewrite hfr hfin hl /= /push /=.
case: (isB c) => _ /=; 1: by left; exists (PA (p, salt_of r)) => /=; rewrite ?hfin.
case: (isA c) => _ /=; 1: by left; exists (PH (key_of r, rd st.`ri, st.`cur)) => /=; rewrite ?hfin.
case: bwd => _ /=; [case: (0 < st.`ri) | case: (st.`ri < 11)] => _ /=; 2,4: by rewrite ?hfin /= ?right.
- by left; exists (PB (rd (st.`ri - 1), st.`oth +^ mask_of r)) => /=; rewrite ?hfin.
by left; exists (PB (rd (st.`ri + 1), st.`oth +^ mask_of r)) => /=; rewrite ?hfin.
qed.

(* A fresh answer at c, with the order of the old chain kept. *)
lemma ordered_fresh inr (m : (point, ans) fmap) log bn chain c pend :
  c \notin m => (forall x, x \in map fst log => x \in m) =>
  (inr => (forall x, x \in m => x \in map fst log) /\ all (fun (e : point * int) => e.`2 <= bn) log) =>
  (forall t, 0 <= t < size chain - 1 => nth witness chain t \in m) =>
  ordered log chain => (inr => later log bn chain (c :: pend)) =>
  ordered (if inr then rcons log (c, bn) else log) chain /\
  (inr => later (if inr then rcons log (c, bn) else log) bn chain pend).
proof.
move=> cm hlm hrun hans hord hlat; case: inr hrun hlat => hrun hlat //=.
have [hml hall] := hrun _ => //; have {hlat} hlat := hlat _ => //.
have hcl : !(c \in map fst log) by smt().
rewrite /ordered /later map_rcons; split=> t ht; rewrite !mem_rcons /= !bnof_rcons.
- case=> [htc | htl].
  + have ht' : t = size chain - 1 by smt().
    have hp : nth witness chain (t - 1) \in m by apply hans; smt().
    have hpl := hml _ hp; rewrite hpl /= htc /= hcl /=.
    have := bnof_le _ bn _ hpl hall; have := hlat t ht.
    by rewrite htc hcl /= => h; smt().
  by have [hpl hlt] := hord t ht htl; rewrite hpl htl /= hlt.
move=> /negb_or [htc htl].
have hp : nth witness chain (t - 1) \in m by apply hans; smt().
have hpl := hml _ hp; rewrite hpl /= => hb.
by move: (hlat t ht htl hb) => /= /#.
qed.

lemma ordered_rcons log chain q : !(q \in map fst log) => ordered log chain => ordered log (rcons chain q).
proof.
rewrite /ordered => hq hord t; rewrite size_rcons !nth_rcons => ht.
case: (t < size chain) => hlt /=; 2: by smt().
by rewrite (_ : t - 1 < size chain) 1:/# /=; apply hord; smt().
qed.

lemma later_rcons log bn chain q pend : !(q \in pend) => later log bn chain pend =>
  later log bn (rcons chain q) pend.
proof.
rewrite /later => hq hlat t; rewrite size_rcons !nth_rcons => ht.
case: (t < size chain) => hlt /=; 2: by smt().
by rewrite (_ : t - 1 < size chain) 1:/# /=; apply hlat; smt().
qed.

lemma ordered_eq log log' chain :
  (forall x, (x \in map fst log') = (x \in map fst log)) => (forall x, bnof log' x = bnof log x) =>
  ordered log chain => ordered log' chain.
proof. by rewrite /ordered => hm hb h t ht; rewrite !hm !hb; apply h. qed.

lemma later_eq log log' bn chain pend pend' :
  (forall x, (x \in map fst log') = (x \in map fst log)) => (forall x, bnof log' x = bnof log x) =>
  (forall x, x \in pend' => x \in pend) => later log bn chain pend => later log' bn chain pend'.
proof. by rewrite /later => hm hb hp h t ht; rewrite hm hb => h1 h2; smt(). qed.

(* Answered up to the last point, and the last point answered: the whole chain is answered. *)
lemma chain_in (m : (point, ans) fmap) chain x :
  (forall t, 0 <= t < size chain - 1 => nth witness chain t \in m) =>
  last witness chain \in m => x \in chain => x \in m.
proof.
move=> hans hl hx; have := index_mem x chain; rewrite hx /= => hi.
have <- := nth_index witness x chain hx.
case: (index x chain < size chain - 1) => h; 1: by apply hans; smt(index_ge0).
by rewrite (_ : index x chain = size chain - 1) 1:/# nth_last.
qed.

lemma invI bwd inr (m : (point, ans) fmap) log bn p st0 st :
  (forall x, x \in map fst log => x \in m) =>
  (inr => forall x, x \in m => x \in map fst log) =>
  (inr => all (fun (e : point * int) => e.`2 <= bn) log) =>
  shape bwd p st =>
  (!st.`early => ordered log st.`chain) => (!st.`early => stopped m st) =>
  (!st.`early => uniq st.`chain) =>
  (!st.`early => forall t, 0 <= t < size st.`chain - 1 => nth witness st.`chain t \in m) =>
  (!st.`early => determined bwd p m st0 st) =>
  inv bwd inr m log bn p st0 st.
proof. by rewrite /inv /#. qed.

(* One answer keeps the invariant: m' is the table after it, log' the log, st' the bookkeeping. *)
lemma inv_step bwd inr (m m' : (point, ans) fmap) log log' bn p st0 st st' c r pend :
  inv bwd inr m log bn p st0 st => (inr => !st.`early => later log bn st.`chain (c :: pend)) =>
  m' = (if c \in m then m else m.[c <- r]) => log' = (if inr then rcons log (c, bn) else log) =>
  st' = cstep bwd p st c (c \notin m) r pend m' =>
  inv bwd inr m' log' bn p st0 st' /\ (inr => !st'.`early => later log' bn st'.`chain pend).
proof.
move=> hinv hlat -> -> ->; have [hlm [hrun [hsh hne]]] := hinv.
case: (c \in m) => cm /=.
- (* an answer from the table: the bookkeeping does not move, the log gets a repeat *)
  have -> : cstep bwd p st c false r pend m = st by rewrite /cstep.
  case: inr hinv hrun hlat => hinv hrun hlat //=.
  have [hml hall] := hrun _ => //; have hcl : c \in map fst log by apply hml.
  have hmem : forall x, (x \in map fst (rcons log (c, bn))) = (x \in map fst log).
  + by move=> x; rewrite map_rcons mem_rcons /=; smt().
  have hb : forall x, bnof (rcons log (c, bn)) x = bnof log x by move=> x; rewrite bnof_rcons /#.
  split=> [|hea]; 2: by apply (later_eq log _ _ _ (c :: pend)) => //; [smt() | exact (hlat _ hea)].
  apply invI.
  + by move=> x; rewrite hmem; apply hlm.
  + by move=> _ x; rewrite hmem; apply hml.
  + by move=> _; rewrite all_rcons1 hall.
  + exact hsh.
  + by move=> /hne [hord _]; apply (ordered_eq log).
  + by move=> /hne [_ [? _]].
  + by move=> /hne [_ [_ [? _]]].
  + by move=> /hne [_ [_ [_ [? _]]]].
  by move=> /hne [_ [_ [_ [_ ?]]]].
(* a fresh answer *)
have hcl : !(c \in map fst log) by smt().
have hmem : forall x, (x \in map fst (if inr then rcons log (c, bn) else log)) =
                      (x \in map fst log \/ inr /\ x = c).
- by move=> x; case: (inr) => _ /=; rewrite ?map_rcons ?mem_rcons /= /#.
have h1 : forall x, x \in map fst (if inr then rcons log (c, bn) else log) => x \in m.[c <- r].
- by move=> x; rewrite hmem mem_set /#.
have h2 : inr => forall x, x \in m.[c <- r] => x \in map fst (if inr then rcons log (c, bn) else log).
- by move=> hi x; have [hml _] := hrun hi; rewrite hmem mem_set hi /= /#.
have h3 : inr => all (fun (e : point * int) => e.`2 <= bn) (if inr then rcons log (c, bn) else log).
- by move=> hi; have [_ hall] := hrun hi; rewrite hi /= all_rcons1 hall.
have hsh' := shape_cstep bwd p st c true r pend m.[c <- r] hsh.
have hold : !(cstep bwd p st c true r pend m.[c <- r]).`early => !st.`early /\
  ordered (if inr then rcons log (c, bn) else log) st.`chain /\
  (inr => later (if inr then rcons log (c, bn) else log) bn st.`chain pend) /\
  stopped m st /\ uniq st.`chain /\
  (forall t, 0 <= t < size st.`chain - 1 => nth witness st.`chain t \in m) /\ determined bwd p m st0 st.
- move=> hea'; have hea : !st.`early.
  + move: hea'; case: (cstep_cases bwd p st c true r pend m.[c <- r]) => [[_ -> //] | ].
    by move=> [_ [_ [_ [[q [_ [-> _]]] | [_ [-> _]]]]]] /#.
  have [hord [hst [hu [hans hdet]]]] := hne hea.
  have := ordered_fresh inr m log bn st.`chain c pend cm hlm hrun hans hord _; 1: by move=> hi; apply hlat.
  smt().
have hdet : !(cstep bwd p st c true r pend m.[c <- r]).`early =>
            determined bwd p m.[c <- r] st0 (cstep bwd p st c true r pend m.[c <- r]).
- by move=> hea'; have [_ [_ [_ [_ [_ [_ hdet]]]]]] := hold hea'; apply determined_fresh.
case: (cstep_cases bwd p st c true r pend m.[c <- r]) => [[hns hst'] | [_ [hfin [hl hcase]]]].
- (* nothing happens *)
  move: hold hsh' hdet; rewrite hst' => hold hsh' hdet.
  split; 2: by move=> hi hea; have [_ [_ [h _]]] := hold hea; apply h.
  apply invI.
  + exact h1.
  + exact h2.
  + exact h3.
  + exact hsh'.
  + by move=> /hold [_ [? _]].
  + by move=> /hold [_ [_ [_ [hst _]]]]; move: hst hns; rewrite /stopped mem_set /#.
  + by move=> /hold [_ [_ [_ [_ [? _]]]]].
  + by move=> /hold [_ [_ [_ [_ [_ [hans _]]]]]] t ht; rewrite mem_set hans.
  exact hdet.
case: hcase => [[q [hch [hea hfi]]] | [hch [hea hfi]]].
- (* a point is pushed *)
  have hq : !(cstep bwd p st c true r pend m.[c <- r]).`early => !(q \in m.[c <- r]) /\ !(q \in pend).
  + by rewrite hea /#.
  have hin : !(cstep bwd p st c true r pend m.[c <- r]).`early =>
             forall x, x \in st.`chain => x \in m.[c <- r].
  + move=> /hold [_ [_ [_ [_ [_ [hans _]]]]]] x hx; apply (chain_in _ st.`chain) => //.
    * by move=> t ht; rewrite mem_set hans.
    by rewrite hl mem_set.
  split.
  + apply invI.
    * exact h1.
    * exact h2.
    * exact h3.
    * exact hsh'.
    * move=> hea'; have [_ [hord _]] := hold hea'; rewrite hch; apply ordered_rcons => //.
      by apply/negP => /h1; have [-> _] := hq hea'.
    * by move=> hea'; rewrite /stopped hfi hch last_rcons /=; have [-> _] := hq hea'.
    * move=> hea'; have [_ [_ [_ [_ [hu _]]]]] := hold hea'; rewrite hch rcons_uniq hu /=.
      by apply/negP => /(hin hea'); have [-> _] := hq hea'.
    * move=> hea' t; rewrite hch size_rcons nth_rcons => ht; rewrite (_ : t < size st.`chain) 1:/# /=.
      by apply (hin hea'); apply mem_nth; smt().
    exact hdet.
  move=> hi hea'; have [_ [_ [h _]]] := hold hea'; rewrite hch; apply later_rcons; 2: by apply h.
  by have [_ ->] := hq hea'.
(* the chain is complete *)
split; 2: by move=> hi /hold [_ [_ [h _]]]; rewrite hch; apply h.
apply invI.
- exact h1.
- exact h2.
- exact h3.
- exact hsh'.
- by move=> /hold [_ [? _]]; rewrite hch.
- by rewrite /stopped hfi.
- by move=> /hold [_ [_ [_ [_ [? _]]]]]; rewrite hch.
- by move=> /hold [_ [_ [_ [_ [_ [hans _]]]]]]; rewrite hch => t ht; rewrite mem_set hans.
exact hdet.
qed.

lemma all_bump (log : (point * int) list) bn :
  all (fun (e : point * int) => e.`2 <= bn) log => all (fun (e : point * int) => e.`2 <= bn + 1) log.
proof. by rewrite !allP => h e he; have /= := h e he => /#. qed.

(* A new batch: no point of the chain waits for it. *)
lemma inv_bump bwd m log bn p st0 st pend : inv bwd true m log bn p st0 st =>
  inv bwd true m log (bn + 1) p st0 st /\ (!st.`early => later log (bn + 1) st.`chain pend).
proof.
move=> hinv; have [hlm [hrun [hsh hne]]] := hinv; have [hml hall] := hrun _ => //.
split; 1: by move: hinv; rewrite /inv => /> *; apply all_bump.
move=> hea; rewrite /later => t ht hnl; have [_ [_ [_ [hans _]]]] := hne hea.
have hp : nth witness st.`chain (t - 1) \in map fst log by apply hml; apply hans; smt().
by have := bnof_le _ bn _ hp hall => /#.
qed.

lemma inv_init p y : inv true true empty [] 0 p (cbwd y) (cbwd y).
proof.
apply invI.
- by move=> x.
- by move=> _ x; rewrite mem_empty.
- by [].
- exact shape_bwd.
- by move=> _ t.
- by move=> _; rewrite /stopped mem_empty.
- by rewrite /cbwd.
- by move=> _ t; rewrite /cbwd /= /#.
by move=> _; apply determined_init; rewrite /stopped mem_empty.
qed.

lemma inv_stop bwd m log bn p st0 st : inv bwd true m log bn p st0 st => inv bwd false m log bn p st0 st.
proof. by rewrite /inv /#. qed.


(* The A points of a chain without repeats, all queried by the adversary, are distinct A queries
   with the chain's password. *)
lemma comp_count p chain log : uniq chain => all (fun c => isA c => isApw p c) chain =>
  comp chain log => count isA chain <= count (isApw p) (undup (map fst log)).
proof.
move=> hu hall hc; rewrite -!size_filter; apply uniq_leq_size; 1: by apply filter_uniq.
move=> x; rewrite !mem_filter mem_undup => -[hA hx]; split; 2: by move/allP: hc; apply; rewrite mem_filter.
by move/allP: hall => /(_ x hx) /=; apply.
qed.

(* ---- Decryption through the table ---------------------------------------------------------- *)
(* The table's chain from st0 has not stopped in its first j steps. *)
op tracks bwd p (m : (point, ans) fmap) st0 j = forall k, 0 <= k < j => !stopped m (iter k (adv bwd p m) st0).

(* The chain stands at round i with halves y, before its last point c is answered. *)
op at (w : cst) (i : int) (y : state) (c : point) =
  !w.`fin /\ w.`ri = i /\ w.`cur = y.`1 /\ w.`oth = y.`2 /\ last witness w.`chain = c.

lemma adv_go bwd p (m : (point, ans) fmap) st : !stopped m st =>
  adv bwd p m st = cstep bwd p st (last witness st.`chain) true (oget m.[last witness st.`chain]) [] m.
proof. by rewrite /adv => ->. qed.

lemma inv_off bwd m log bn bn' p st0 st : inv bwd false m log bn p st0 st => inv bwd false m log bn' p st0 st.
proof. by rewrite /inv. qed.

(* One answer after the adversary's run. *)
lemma inv_step_off bwd (m m' : (point, ans) fmap) log bn bn' p st0 st st' c r pend :
  inv bwd false m log bn p st0 st => m' = (if c \in m then m else m.[c <- r]) =>
  st' = cstep bwd p st c (c \notin m) r pend m' => inv bwd false m' log bn' p st0 st'.
proof.
move=> hinv hm hst; apply (inv_off _ _ _ bn).
by have [] := inv_step bwd false m m' log log bn p st0 st st' c r pend hinv _ hm _ hst.
qed.

(* The invariant during the adversary's run, for the chains of all passwords. *)
op irun (inrun odd : bool) (m : (point, ans) fmap) (log : (point * int) list) (bn : int) (y : state)
        (sts : pw -> cst) =
  inrun /\ !odd /\ forall w, inv true true m log bn w (cbwd y) (sts w).

lemma irun_bump inr o m log bn y sts pend : irun inr o m log bn y sts =>
  irun inr o m log (bn + 1) y sts /\ (forall w, !(sts w).`early => later log (bn + 1) (sts w).`chain pend).
proof.
move=> [hi [ho hinv]]; rewrite /irun hi ho /=.
have h : forall w, inv true true m log (bn + 1) w (cbwd y) (sts w) /\
                   (!(sts w).`early => later log (bn + 1) (sts w).`chain pend).
- by move=> w; apply (inv_bump true m log bn w (cbwd y) (sts w) pend (hinv w)).
by split=> w; have [h1 h2] := h w.
qed.

(* One query of the adversary's run, with [pend] left in its batch. *)
lemma irun_step inr o (m m' : (point, ans) fmap) log log' bn y sts sts' o' c r pend p0 :
  irun inr o m log bn y sts => (forall w, !(sts w).`early => later log bn (sts w).`chain (c :: pend)) =>
  o' = (o \/ !inr /\ c \notin m /\ c <> last witness (sts p0).`chain /\ !(sts p0).`early) =>
  m' = (if c \in m then m else m.[c <- r]) => log' = (if inr then rcons log (c, bn) else log) =>
  sts' = (fun w => cstep true w (sts w) c (c \notin m) r pend m') =>
  irun inr o' m' log' bn y sts' /\ (forall w, !(sts' w).`early => later log' bn (sts' w).`chain pend).
proof.
move=> [hi [ho hinv]] hlat -> hm -> hsts; rewrite /irun hi ho /=.
have h : forall w, inv true true m' (rcons log (c, bn)) bn w (cbwd y) (sts' w) /\
                   (true => !(sts' w).`early => later (rcons log (c, bn)) bn (sts' w).`chain pend).
- move=> w; have hl : true => !(sts w).`early => later log bn (sts w).`chain (c :: pend).
  + by move=> _; apply hlat.
  have hst : sts' w = cstep true w (sts w) c (c \notin m) r pend m' by rewrite hsts.
  by apply (inv_step true true m m' log _ bn w (cbwd y) (sts w) _ c r pend (hinv w) hl hm _ hst).
by split=> w; have [h1 h2] := h w; [exact h1 | apply h2].
qed.

lemma strip_eq (a b : cst) : strip a = strip b =>
  a.`chain = b.`chain /\ a.`fin = b.`fin /\ a.`ri = b.`ri /\ a.`cur = b.`cur /\ a.`oth = b.`oth /\ a.`xs = b.`xs.
proof. by move=> h; have := congr1 (fun (s : cst) => (s.`chain, s.`fin, s.`ri, s.`cur, s.`oth, s.`xs)) _ _ h. qed.

(* A query of the decryption at the table's chain is answered already or is the bookkeeping's next
   point. *)
lemma dec_point bwd p m st0 st j : determined bwd p m st0 st => 0 <= j => tracks bwd p m st0 j =>
  !(iter j (adv bwd p m) st0).`fin =>
  last witness (iter j (adv bwd p m) st0).`chain \in m \/
  last witness (iter j (adv bwd p m) st0).`chain = last witness st.`chain.
proof.
move=> [n [ge0n [hst [htight hstop]]]] ge0j htr hfin.
case: (j < n) => hjn; 1: by left; have := htight j; rewrite ge0j hjn /stopped hfin.
have hn : stopped m (iter n (adv bwd p m) st0) by rewrite -stopped_strip -hst stopped_strip.
have hjn' : j = n by case: (n < j) => hnj; [have := htr n; rewrite ge0n hnj hn | smt()].
by right; have [-> _] := strip_eq _ _ hst; rewrite hjn'.
qed.

(* While Early has not happened, the bookkeeping is the first stopped state of the table's chain. *)
lemma determined_end bwd p m st0 st j : determined bwd p m st0 st => 0 <= j => tracks bwd p m st0 j =>
  stopped m (iter j (adv bwd p m) st0) => strip st = strip (iter j (adv bwd p m) st0).
proof.
move=> [n [ge0n [hst [htight hstop]]]] ge0j htr hj.
have hn : stopped m (iter n (adv bwd p m) st0) by rewrite -stopped_strip -hst stopped_strip.
have -> // : j = n.
case: (n < j) => hnj; 1: by have := htr n; rewrite ge0n hnj hn.
case: (j < n) => hjn; 2: smt().
by have := htight j; rewrite ge0j hjn hj.
qed.

(* A query at the last point of the table's chain after j steps moves that chain one step. *)
lemma iter_query bwd p (m m' : (point, ans) fmap) st0 j c r :
  0 <= j => tracks bwd p m st0 j => !(iter j (adv bwd p m) st0).`fin =>
  last witness (iter j (adv bwd p m) st0).`chain = c =>
  m' = (if c \in m then m else m.[c <- r]) => (c \in m => r = oget m.[c]) =>
  tracks bwd p m' st0 (j + 1) /\
  strip (iter (j + 1) (adv bwd p m') st0) = strip (cstep bwd p (iter j (adv bwd p m) st0) c true r [] m').
proof.
move=> ge0j htr hfin hl -> hr.
have hext : forall k, 0 <= k <= j =>
  strip (iter k (adv bwd p (if c \in m then m else m.[c <- r])) st0) = strip (iter k (adv bwd p m) st0).
- move=> k hk; case: (c \in m) => cm //=.
  by apply iter_ext; [exact cm | smt() | move=> k' hk'; apply htr; smt()].
have hin : c \in (if c \in m then m else m.[c <- r]) by case: (c \in m) => cm //=; rewrite mem_set.
split.
- move=> k hk; rewrite -stopped_strip hext 1:/# stopped_strip.
  case: (k < j) => hkj.
  + by case: (c \in m) => cm /=; [apply htr | apply stopped_ext; apply htr]; smt().
  have -> : k = j by smt().
  by rewrite /stopped hfin hl hin.
have hgo : !stopped (if c \in m then m else m.[c <- r]) (iter j (adv bwd p m) st0).
- by rewrite /stopped hfin hl hin.
rewrite iterS // adv_strip hext 1:/# -adv_strip (adv_go _ _ _ _ hgo) hl.
have -> // : oget (if c \in m then m else m.[c <- r]).[c] = r.
by case: (c \in m) => cm /=; [rewrite hr | rewrite get_set_sameE].
qed.

(* The three queries of one round of decryption, as steps of the backward chain. *)
lemma stepB p (w w' : cst) i (y : state) r (m : (point, ans) fmap) :
  at w i y (PB (rd i, y.`1)) => strip w' = strip (cstep true p w (PB (rd i, y.`1)) true r [] m) =>
  at w' i y (PA (p, salt_of r)).
proof.
move=> [hf [hri [hc [ho hl]]]] /strip_eq; rewrite /cstep hf hl /= /push /=.
by rewrite /at => -[-> [-> [-> [-> [-> _]]]]]; rewrite last_rcons hf hri hc ho.
qed.

lemma stepA p (w w' : cst) i (y : state) s r (m : (point, ans) fmap) :
  at w i y (PA (p, s)) => strip w' = strip (cstep true p w (PA (p, s)) true r [] m) =>
  at w' i y (PH (key_of r, rd i, y.`1)).
proof.
move=> [hf [hri [hc [ho hl]]]] /strip_eq; rewrite /cstep hf hl /= /push /=.
by rewrite /at => -[-> [-> [-> [-> [-> _]]]]]; rewrite last_rcons hf hri hc ho.
qed.

lemma stepH p (w w' : cst) i (y : state) k r (m : (point, ans) fmap) :
  at w i y (PH (k, rd i, y.`1)) => strip w' = strip (cstep true p w (PH (k, rd i, y.`1)) true r [] m) =>
  (0 < i => at w' (i - 1) (unround (mask_of r) y) (PB (rd (i - 1), (unround (mask_of r) y).`1))) /\
  (!(0 < i) => w'.`fin /\ w'.`xs = unround (mask_of r) y).
proof.
move=> [hf [hri [hc [ho hl]]]] /strip_eq; rewrite /cstep hf hl /= hri.
case: (0 < i) => hi /=.
- by rewrite /push /at /= => -[-> [-> [-> [-> [-> _]]]]]; rewrite last_rcons /unround hc ho.
by move=> [_ [-> [_ [_ [_ ->]]]]]; rewrite /unround hc ho.
qed.

(* ---- The potential of Lemma G3 ------------------------------------------------------------- *)
op e128 : real = inv (2%r ^ 128).
op e256 : real = inv (2%r ^ 256).

lemma e128_gt0 : 0%r < e128 by smt(RealOrder.expr_gt0 RealOrder.invr_gt0).
lemma e256_gt0 : 0%r < e256 by smt(RealOrder.expr_gt0 RealOrder.invr_gt0).

lemma sum_dP : BRA.big predT (mu1 dP) PwT.enum = 1%r.
proof.
rewrite -(undup_id PwT.enum) 1:PwT.enum_uniq -mu_mem -dP_ll.
by apply mu_eq => w; rewrite PwT.enumP.
qed.

lemma dans_salt (P : W128.word -> bool) : mu dans (fun r => P (salt_of r)) = mu W128.DWord.dunifin P.
proof.
have -> : (fun r => P (salt_of r)) = (fun (r : ans) => predT r.`1 /\ (fun (x : _ * _) => P x.`1) r.`2).
- by apply fun_ext => r.
have h1 := W128.DWord.dunifin_ll; have h2 := W256.DWord.dunifin_ll.
by move: h1 h2; rewrite /dans dprodE dprodEl /is_lossless => -> ->.
qed.

lemma dans_key (P : W256.word -> bool) : mu dans (fun r => P (key_of r)) = mu W256.DWord.dunifin P.
proof.
have -> : (fun r => P (key_of r)) = (fun (r : ans) => P r.`1 /\ predT r.`2) by apply fun_ext => r.
have h1 := W128.DWord.dunifin_ll.
have h2 := W256.DWord.dunifin_ll.
by move: h1 h2; rewrite /dans dprodE weight_dprod /is_lossless => -> _ /=.
qed.

lemma dans_maskE (P : W128.word -> bool) : mu dans (fun r => P (mask_of r)) = mu W128.DWord.dunifin P.
proof. by rewrite -dans_mask dmapE. qed.

(* A fixed xor leaves the uniform half uniform. *)
lemma dhalf_shift (a : W128.word) (P : W128.word -> bool) :
  mu W128.DWord.dunifin (fun x => P (a +^ x)) = mu W128.DWord.dunifin P.
proof.
rewrite -(dmapE W128.DWord.dunifin (fun x => a +^ x) P).
congr; apply (dmap_bij _ _ _ (fun x => a +^ x)) => //=.
- by move=> x _; apply W128.DWord.dunifin_fu.
- by move=> x _; rewrite !W128.DWord.dunifin1E.
- by move=> x _; rewrite xorA xorK xorC xor0.
by move=> x _; rewrite xorA xorK xorC xor0.
qed.

lemma mu_or_le ['a] (d : 'a distr) (p q : 'a -> bool) : mu d (fun x => p x \/ q x) <= mu d p + mu d q.
proof. by have := mu_or d p q; rewrite /predU /predI /=; smt(mu_bounded). qed.

(* The probability that a fresh salt, half or key puts the next A, B or H point of a chain into the
   set S of answered or submitted points. *)
op hitA (S : point -> bool) (w : pw) : real = mu W128.DWord.dunifin (fun s => S (PA (w, s))).
op hitB (S : point -> bool) (j : int) : real = mu W128.DWord.dunifin (fun x => S (PB (rd j, x))).
op hitH (S : point -> bool) (j : int) : real =
  mu W256.DWord.dunifin (fun k => exists x, S (PH (k, rd j, x))).

lemma hitA_add S c w :
  hitA (fun x => S x \/ x = c) w <= hitA S w + (if isApw w c then e128 else 0%r).
proof.
rewrite /hitA; apply (ler_trans _ _ _ (mu_or_le _ _ _)); apply ler_add2l.
case: c => [[w' s0]|b|h] /=; 2,3: by rewrite mu0_false.
case: (w' = w) => [-> | hw] /=; 2: by rewrite mu0_false // /#.
by rewrite (mu_eq _ _ (pred1 s0)) 1:/# dhalf1 /e128.
qed.

lemma hitB_add S c j :
  hitB (fun x => S x \/ x = c) j <= hitB S j + (if isB c /\ ridxof c = rd j then e128 else 0%r).
proof.
rewrite /hitB; apply (ler_trans _ _ _ (mu_or_le _ _ _)); apply ler_add2l.
case: c => [a|[i0 x0]|h] /=; 1,3: by rewrite mu0_false.
case: (i0 = rd j) => [-> | hi] /=; 2: by rewrite mu0_false // /#.
by rewrite (mu_eq _ _ (pred1 x0)) 1:/# dhalf1 /e128.
qed.

lemma hitH_add S c j :
  hitH (fun x => S x \/ x = c) j <= hitH S j + (if !isA c /\ !isB c /\ ridxof c = rd j then e256 else 0%r).
proof.
rewrite /hitH; apply (ler_trans _ _ _ (mu_le _ _ (fun k => (exists x, S (PH (k, rd j, x))) \/
                                                         exists x, PH (k, rd j, x) = c) _)).
- by move=> k _ /= [x [h | h]]; [left | right]; exists x.
apply (ler_trans _ _ _ (mu_or_le _ _ _)); apply ler_add2l.
case: c => [a|b|[k0 i0 x0]] /=; 1,2: by rewrite mu0_false.
case: (i0 = rd j) => [-> | hi] /=; 2: by rewrite mu0_false // /#.
by rewrite (mu_eq _ _ (pred1 k0)) 1:/# dkey1 /e256.
qed.

(* Rounds whose B point is still to come; the H point of the current round is to come while it is
   not the last point. *)
op futB (bwd : bool) (st : cst) (j : int) = if bwd then 0 <= j < st.`ri else st.`ri < j <= 11.
op futH (bwd : bool) (st : cst) (j : int) = futB bwd st j \/ (j = st.`ri /\ pos (last witness st.`chain) < 2).

(* The A points still to come. *)
op nA (st : cst) : int = 12 - count isA st.`chain.

(* The risk left for a chain without Early: each A point to come may hit an A point of the password
   in S, or one of the chain's own A points (nA (nA - 1) / 2 pairs, and nA more while the last point
   is an A point outside S); each B and H point to come may hit S. *)
op rho (bwd : bool) (w : pw) (S : point -> bool) (st : cst) : real =
  (nA st)%r * hitA S w + ((nA st) * (nA st - 1))%r / 2%r * e128
  + (if isA (last witness st.`chain) /\ !S (last witness st.`chain) then (nA st)%r * e128 else 0%r)
  + BRA.bigi predT (fun j => if futB bwd st j then hitB S j else 0%r) 0 12
  + BRA.bigi predT (fun j => if futH bwd st j then hitH S j else 0%r) 0 12.

op psi (bwd : bool) (w : pw) (S : point -> bool) (st : cst) : real =
  if st.`early then 1%r else rho bwd w S st.

(* Among the twelve round indices at most one is the index of a given point. *)
lemma sum_one (i0 : ridx) (P : int -> bool) (e : real) : 0%r <= e =>
  BRA.bigi predT (fun j => if P j /\ i0 = rd j then e else 0%r) 0 12 <= e.
proof.
move=> ge0e; rewrite (BRA.bigD1 _ _ (Ridx.val i0)) ?mem_range ?range_uniq; 1: smt(Ridx.valP).
rewrite BRA.big1_seq /=; 2: by smt().
move=> j [hj /mem_range hr] /=; case: (P j /\ i0 = rd j) => // -[_ h].
by move: hj; rewrite h rdK.
qed.

lemma rho_add bwd w S c st : 0 <= nA st =>
  rho bwd w (fun x => S x \/ x = c) st <=
  rho bwd w S st + (if isApw w c then (nA st)%r * e128 else 0%r)
  + (if isB c then e128 else 0%r) + (if !isA c /\ !isB c then e256 else 0%r).
proof.
move=> ge0n; rewrite /rho.
have hA : (nA st)%r * hitA (fun x => S x \/ x = c) w <=
          (nA st)%r * hitA S w + (if isApw w c then (nA st)%r * e128 else 0%r).
- have := ler_wpmul2l (nA st)%r _ _ _ (hitA_add S c w); smt().
have hB : BRA.bigi predT (fun j => if futB bwd st j then hitB (fun x => S x \/ x = c) j else 0%r) 0 12 <=
          BRA.bigi predT (fun j => if futB bwd st j then hitB S j else 0%r) 0 12 + (if isB c then e128 else 0%r).
- apply (ler_trans (BRA.bigi predT (fun j => (if futB bwd st j then hitB S j else 0%r) +
                    (if futB bwd st j /\ ridxof c = rd j then (if isB c then e128 else 0%r) else 0%r)) 0 12)).
  + by apply ler_sum => j _ /=; have := hitB_add S c j; smt().
  by rewrite BRA.big_split ler_add2l; apply sum_one; smt(e128_gt0).
have hH : BRA.bigi predT (fun j => if futH bwd st j then hitH (fun x => S x \/ x = c) j else 0%r) 0 12 <=
          BRA.bigi predT (fun j => if futH bwd st j then hitH S j else 0%r) 0 12 +
          (if !isA c /\ !isB c then e256 else 0%r).
- apply (ler_trans (BRA.bigi predT (fun j => (if futH bwd st j then hitH S j else 0%r) +
          (if futH bwd st j /\ ridxof c = rd j then (if !isA c /\ !isB c then e256 else 0%r) else 0%r)) 0 12)).
  + by apply ler_sum => j _ /=; have := hitH_add S c j; smt().
  by rewrite BRA.big_split ler_add2l; apply sum_one; smt(e256_gt0).
smt(e128_gt0).
qed.

lemma last_mem (s : point list) : s <> [] => last witness s \in s.
proof. by case: s => // x s _; rewrite last_cons (last_nth witness); apply mem_nth; smt(size_ge0). qed.

lemma rd_inj (i j : int) : 0 <= i < 12 => 0 <= j < 12 => rd i = rd j => i = j.
proof. by move=> hi hj h; rewrite -(rdK i hi) -(rdK j hj) h. qed.

(* Submitting the chain's own last point does not raise its risk. *)
lemma rho_own bwd w S st : shape bwd w st =>
  rho bwd w (fun x => S x \/ x = last witness st.`chain) st <= rho bwd w S st.
proof.
move=> hsh; have [hri [hne [_ [hcnt [hall [_ hlr]]]]]] := hsh.
case: (S (last witness st.`chain)) => hSc.
- by have -> // : (fun x => S x \/ x = last witness st.`chain) = S by apply fun_ext => x; smt().
have ge0n : 0%r <= (nA st)%r by rewrite /nA hcnt; smt().
have hpw : isA (last witness st.`chain) => isApw w (last witness st.`chain).
- by move: hall; rewrite allP => h; exact (h _ (last_mem _ hne)).
rewrite /rho; have hA := ler_wpmul2l (nA st)%r ge0n _ _ (hitA_add S (last witness st.`chain) w).
have hB : BRA.bigi predT (fun j => if futB bwd st j then hitB (fun x => S x \/ x = last witness st.`chain) j else 0%r) 0 12
          <= BRA.bigi predT (fun j => if futB bwd st j then hitB S j else 0%r) 0 12.
- apply ler_sum_seq => j /mem_range hj _ /=; case: (futB bwd st j) => // hf.
  have := hitB_add S (last witness st.`chain) j.
  case: (isB (last witness st.`chain) /\ ridxof (last witness st.`chain) = rd j) => // -[hb h].
  have hl := hlr _; 1: by move: hb; case: (last witness st.`chain).
  have hji : j = st.`ri by apply rd_inj; [smt() | smt() | rewrite -h -hl].
  by move: hf; rewrite /futB hji; smt().
have hH : BRA.bigi predT (fun j => if futH bwd st j then hitH (fun x => S x \/ x = last witness st.`chain) j else 0%r) 0 12
          <= BRA.bigi predT (fun j => if futH bwd st j then hitH S j else 0%r) 0 12.
- apply ler_sum_seq => j /mem_range hj _ /=; case: (futH bwd st j) => // hf.
  have := hitH_add S (last witness st.`chain) j.
  case: (!isA (last witness st.`chain) /\ !isB (last witness st.`chain) /\
         ridxof (last witness st.`chain) = rd j) => // -[ha [hb h]].
  have hl := hlr ha.
  have hji : j = st.`ri by apply rd_inj; [smt() | smt() | rewrite -h -hl].
  move: hf; rewrite /futH /futB hji /=.
  by move: ha hb; case: (last witness st.`chain) => //=; smt().
have hAI : (nA st)%r * hitA (fun x => S x \/ x = last witness st.`chain) w +
           (if isA (last witness st.`chain) /\ !(S (last witness st.`chain) \/
               last witness st.`chain = last witness st.`chain) then (nA st)%r * e128 else 0%r) <=
           (nA st)%r * hitA S w +
           (if isA (last witness st.`chain) /\ !S (last witness st.`chain) then (nA st)%r * e128 else 0%r).
- rewrite hSc /=; case: (isA (last witness st.`chain)) => hAc /=.
  + by move: hA; rewrite (hpw hAc) /=; smt().
  have hp : !isApw w (last witness st.`chain) by move: hAc; case: (last witness st.`chain).
  by move: hA; rewrite hp.
apply ler_add; [apply ler_add | exact hH]; [smt() | exact hB].
qed.

lemma rho_ge0 bwd w S st : 0 <= nA st => 0%r <= rho bwd w S st.
proof.
move=> ge0n; rewrite /rho.
have h1 : 0%r <= BRA.bigi predT (fun j => if futB bwd st j then hitB S j else 0%r) 0 12.
- by apply sumr_ge0 => j _ /=; case: (futB bwd st j) => // _; apply ge0_mu.
have h2 : 0%r <= BRA.bigi predT (fun j => if futH bwd st j then hitH S j else 0%r) 0 12.
- by apply sumr_ge0 => j _ /=; case: (futH bwd st j) => // _; apply ge0_mu.
have h3 : 0%r <= hitA S w by apply ge0_mu.
have h4 : 0 <= nA st * (nA st - 1) by smt().
smt(e128_gt0).
qed.

(* The expected value of a weighted sum over the passwords. *)
lemma Ep_sum_le (d : 'a distr) (F : pw -> 'a -> real) (G : pw -> real) (B : real) (l : pw list) :
  is_lossless d => (forall w x, 0%r <= F w x) => (forall w, 0%r <= G w) => 0%r <= B =>
  (forall w, Ep d (fun x => (F w x)%xr) <= (G w)%xr) =>
  Ep d (fun x => (BRA.big predT (fun w => mu1 dP w * F w x) l + B)%xr) <=
  (BRA.big predT (fun w => mu1 dP w * G w) l + B)%xr.
proof.
move=> dll hF hG; elim: l B => [|w l ih] B hB hE.
- rewrite (eq_Ep _ _ (fun _ => B%xr)) => [x _ /=|]; 1: by rewrite BRA.big_nil.
  by rewrite BRA.big_nil EpC dll.
rewrite !BRA.big_cons /predT /=.
have hl : forall x, 0%r <= BRA.big predT (fun w => mu1 dP w * F w x) l.
- by move=> x; apply sumr_ge0 => w' _ /=; smt(ge0_mu).
have hl' : 0%r <= BRA.big predT (fun w => mu1 dP w * G w) l by apply sumr_ge0 => w' _ /=; smt(ge0_mu).
rewrite (eq_Ep _ _ ((fun x => (mu1 dP w)%rp ** (F w x)%xr) +
                    (fun x => (BRA.big predT (fun w => mu1 dP w * F w x) l + B)%xr))).
- move=> x _ /=; rewrite BRA.big_cons /=.
  have hp : 0%r <= mu1 dP w by apply ge0_mu.
  have hFx := hF w x; have hlx := hl x.
  have hpF : 0%r <= mu1 dP w * F w x by smt().
  have hr : 0%r <= BRA.big predT (fun w => mu1 dP w * F w x) l + B by smt().
  by rewrite -(of_realM _ _ hp hFx) -(of_realD _ _ hpF hr) /predT; congr; ring.
have -> : (mu1 dP w * G w + BRA.big predT (fun w => mu1 dP w * G w) l + B)%xr =
          mu1 dP w ** (G w)%xr + (BRA.big predT (fun w => mu1 dP w * G w) l + B)%xr.
- have hp : 0%r <= mu1 dP w by apply ge0_mu.
  have hGw := hG w; have hpG : 0%r <= mu1 dP w * G w by smt().
  have hr : 0%r <= BRA.big predT (fun w => mu1 dP w * G w) l + B by smt().
  by rewrite /= -(of_realM _ _ hp hGw) -(of_realD _ _ hpG hr) /predT; congr; ring.
rewrite EpD EpsZ; apply xler_add; [apply xler_md => _; apply hE | by apply ih].
qed.

lemma posB c : isB c => pos c = 0 by case: c.
lemma posA c : isA c => pos c = 1 by case: c.
lemma posH c : !isA c => !isB c => pos c = 2 by case: c.

(* One answer that defines the next A point of a chain: its salt is fresh. *)
lemma Ep_stepB bwd w (m : (point, ans) fmap) c pend st (S : point -> bool) :
  shape bwd w st => !st.`early => !st.`fin => last witness st.`chain = c => isB c =>
  (forall r q, (q \in m.[c <- r] \/ q \in pend) = S q) =>
  Ep dans (fun r => (psi bwd w S (cstep bwd w st c true r pend m.[c <- r]))%xr) <= (psi bwd w S st)%xr.
proof.
move=> hsh hea hfin hl hB hS; have [hri [hne [_ [hcnt _]]]] := hsh.
have hn : 1 <= nA st by rewrite /nA hcnt hl /ndone (posB _ hB) /=; smt().
pose R := (nA st - 1)%r * hitA S w + ((nA st - 1) * (nA st - 1 - 1))%r / 2%r * e128 + (nA st - 1)%r * e128
          + BRA.bigi predT (fun j => if futB bwd st j then hitB S j else 0%r) 0 12
          + BRA.bigi predT (fun j => if futH bwd st j then hitH S j else 0%r) 0 12.
have hR : 0%r <= R.
- have h1 : 0%r <= BRA.bigi predT (fun j => if futB bwd st j then hitB S j else 0%r) 0 12.
  + by apply sumr_ge0 => j _ /=; case: (futB bwd st j) => // _; apply ge0_mu.
  have h2 : 0%r <= BRA.bigi predT (fun j => if futH bwd st j then hitH S j else 0%r) 0 12.
  + by apply sumr_ge0 => j _ /=; case: (futH bwd st j) => // _; apply ge0_mu.
  have h3 : 0%r <= hitA S w by apply ge0_mu.
  have h4 : 0 <= (nA st - 1) * (nA st - 1 - 1) by smt().
  smt(e128_gt0).
have hpt : forall r, psi bwd w S (cstep bwd w st c true r pend m.[c <- r]) <= b2r (S (PA (w, salt_of r))) + R.
- move=> r; rewrite /cstep hfin hl /= hB /psi /push /= hea /= hS.
  case: (S (PA (w, salt_of r))) => hq /=; 1: smt().
  rewrite /rho /nA /futH /futB /= last_rcons count_rcons1 hq /= /R /nA /futH /futB hl (posB _ hB) /b2i /=.
  smt().
apply (xle_trans (Ep dans (fun r => (b2r (S (PA (w, salt_of r))))%xr + R%xr))).
- apply le_Ep => r _ /=; have h := hpt r; have hb := b2r_ge0 (S (PA (w, salt_of r))).
  rewrite (to_pos_pos (b2r _)) // (to_pos_pos R) //.
  by apply (ler_trans _ _ _ (le_pos _ _ h)); rewrite to_pos_pos //; smt().
rewrite (eq_Ep _ _ ((fun r => (S (PA (w, salt_of r)))%xr) + (fun _ => R%xr))) 1:// EpD Ep_mu EpC dans_ll /=.
have -> : mu dans (fun r => S (PA (w, salt_of r))) = hitA S w by rewrite /hitA (dans_salt (fun s => S (PA (w, s)))).
have -> : psi bwd w S st = hitA S w + R.
- rewrite /psi hea /= /rho /R /nA /futH /futB hl (posB _ hB) /=.
  have -> /= : !isA c by move: hB; case: (c).
  smt().
have hA : 0%r <= hitA S w by apply ge0_mu.
by rewrite /= !to_pos_pos //; smt().
qed.

(* A sum over the rounds with one round singled out. *)
lemma sum_split (P : int -> bool) (h : int -> real) (k : int) : 0 <= k < 12 => !P k =>
  BRA.bigi predT (fun j => if P j \/ j = k then h j else 0%r) 0 12 =
  BRA.bigi predT (fun j => if P j then h j else 0%r) 0 12 + h k.
proof.
move=> hk hP; rewrite (BRA.bigD1 _ _ k) ?mem_range ?range_uniq //= (BRA.bigD1 _ _ k) ?mem_range ?range_uniq //=.
rewrite hP /=; have -> // : BRA.big (predC1 k) (fun j => if P j \/ j = k then h j else 0%r) (range 0 12) =
                            BRA.big (predC1 k) (fun j => if P j then h j else 0%r) (range 0 12).
- by apply BRA.eq_bigr => j /= hj; rewrite hj.
by ring.
qed.

(* One answer that defines the next H point of a chain: its key is fresh. *)
lemma Ep_stepA bwd w (m : (point, ans) fmap) c pend st (S : point -> bool) :
  shape bwd w st => !st.`early => !st.`fin => last witness st.`chain = c => isA c => S c =>
  (forall r q, (q \in m.[c <- r] \/ q \in pend) = S q) =>
  Ep dans (fun r => (psi bwd w S (cstep bwd w st c true r pend m.[c <- r]))%xr) <= (psi bwd w S st)%xr.
proof.
move=> hsh hea hfin hl hA hSc hS; have [hri [hne [_ [hcnt _]]]] := hsh.
have hn : 0 <= nA st by rewrite /nA hcnt /ndone; smt().
pose R := (nA st)%r * hitA S w + ((nA st) * (nA st - 1))%r / 2%r * e128
          + BRA.bigi predT (fun j => if futB bwd st j then hitB S j else 0%r) 0 12
          + BRA.bigi predT (fun j => if futB bwd st j then hitH S j else 0%r) 0 12.
have hR : 0%r <= R.
- have h1 : 0%r <= BRA.bigi predT (fun j => if futB bwd st j then hitB S j else 0%r) 0 12.
  + by apply sumr_ge0 => j _ /=; case: (futB bwd st j) => // _; apply ge0_mu.
  have h2 : 0%r <= BRA.bigi predT (fun j => if futB bwd st j then hitH S j else 0%r) 0 12.
  + by apply sumr_ge0 => j _ /=; case: (futB bwd st j) => // _; apply ge0_mu.
  have h3 : 0%r <= hitA S w by apply ge0_mu.
  have h4 : 0 <= nA st * (nA st - 1) by smt().
  smt(e128_gt0).
have hnb : !isB c by move: hA; case: (c).
have hpt : forall r, psi bwd w S (cstep bwd w st c true r pend m.[c <- r]) <=
                     b2r (S (PH (key_of r, rd st.`ri, st.`cur))) + R.
- move=> r; rewrite /cstep hfin hl /= hnb hA /psi /push /= hea /= hS.
  case: (S (PH (key_of r, rd st.`ri, st.`cur))) => hq /=; 1: smt().
  by rewrite /rho /nA /futH /futB /= last_rcons count_rcons1 /= /R /nA /futB /b2i /=; smt().
apply (xle_trans (Ep dans (fun r => (b2r (S (PH (key_of r, rd st.`ri, st.`cur))))%xr + R%xr))).
- apply le_Ep => r _ /=; have h := hpt r; have hb := b2r_ge0 (S (PH (key_of r, rd st.`ri, st.`cur))).
  rewrite (to_pos_pos (b2r _)) // (to_pos_pos R) //.
  by apply (ler_trans _ _ _ (le_pos _ _ h)); rewrite to_pos_pos //; smt().
rewrite (eq_Ep _ _ ((fun r => (S (PH (key_of r, rd st.`ri, st.`cur)))%xr) + (fun _ => R%xr))) 1:// EpD Ep_mu EpC dans_ll /=.
have hk : mu dans (fun r => S (PH (key_of r, rd st.`ri, st.`cur))) <= hitH S st.`ri.
- rewrite (dans_key (fun k => S (PH (k, rd st.`ri, st.`cur)))) /hitH.
  by apply mu_le => k _ /= h; exists st.`cur.
have -> : psi bwd w S st = R + hitH S st.`ri.
- rewrite /psi hea /= /rho /R hl hSc /=.
  rewrite /futH hl (posA _ hA) /= (sum_split (futB bwd st)) 1:/#; 1: by rewrite /futB /#.
  smt().
have h0 : 0%r <= mu dans (fun r => S (PH (key_of r, rd st.`ri, st.`cur))) by apply ge0_mu.
by rewrite /= !to_pos_pos //; smt(ge0_mu).
qed.

(* One answer that defines the next B point of a chain: its half is the fresh mask added to a fixed
   half. *)
lemma Ep_stepH bwd w (m : (point, ans) fmap) c pend st (S : point -> bool) :
  shape bwd w st => !st.`early => !st.`fin => last witness st.`chain = c => !isA c => !isB c =>
  (if bwd then 0 < st.`ri else st.`ri < 11) =>
  (forall r q, (q \in m.[c <- r] \/ q \in pend) = S q) =>
  Ep dans (fun r => (psi bwd w S (cstep bwd w st c true r pend m.[c <- r]))%xr) <= (psi bwd w S st)%xr.
proof.
move=> hsh hea hfin hl hA hB hmore hS; have [hri [hne [_ [hcnt _]]]] := hsh.
have hn : 0 <= nA st by rewrite /nA hcnt /ndone; smt().
pose R := (nA st)%r * hitA S w + ((nA st) * (nA st - 1))%r / 2%r * e128
  + BRA.bigi predT (fun k => if (if bwd then 0 <= k < st.`ri - 1 else st.`ri + 1 < k <= 11) then hitB S k else 0%r) 0 12
  + BRA.bigi predT (fun k => if futB bwd st k then hitH S k else 0%r) 0 12.
have hR : 0%r <= R.
- have h1 : 0%r <= BRA.bigi predT (fun k => if (if bwd then 0 <= k < st.`ri - 1 else st.`ri + 1 < k <= 11)
                                             then hitB S k else 0%r) 0 12.
  + by apply sumr_ge0 => k _ /=; case: (if bwd then 0 <= k < st.`ri - 1 else st.`ri + 1 < k <= 11) => // _; apply ge0_mu.
  have h2 : 0%r <= BRA.bigi predT (fun k => if futB bwd st k then hitH S k else 0%r) 0 12.
  + by apply sumr_ge0 => k _ /=; case: (futB bwd st k) => // _; apply ge0_mu.
  have h3 : 0%r <= hitA S w by apply ge0_mu.
  have h4 : 0 <= nA st * (nA st - 1) by smt().
  smt(e128_gt0).
pose j := if bwd then st.`ri - 1 else st.`ri + 1.
have hpt : forall r, psi bwd w S (cstep bwd w st c true r pend m.[c <- r]) <=
                     b2r (S (PB (rd j, st.`oth +^ mask_of r))) + R.
- move=> r; rewrite /cstep hfin hl /= hB hA /= hmore /= /psi /push /= hea /= hS.
  case: (S (PB (rd (if bwd then st.`ri - 1 else st.`ri + 1), st.`oth +^ mask_of r))) => hq /=; 1: smt().
  rewrite /rho /nA /futH /futB /= last_rcons count_rcons1 /= /R /nA /futB /b2i /=.
  have -> : BRA.bigi predT (fun k => if (if bwd then 0 <= k < (if bwd then st.`ri - 1 else st.`ri + 1)
                                          else (if bwd then st.`ri - 1 else st.`ri + 1) < k <= 11)
                                     then hitB S k else 0%r) 0 12 =
            BRA.bigi predT (fun k => if (if bwd then 0 <= k < st.`ri - 1 else st.`ri + 1 < k <= 11)
                                     then hitB S k else 0%r) 0 12.
  + by apply BRA.eq_bigr => k _ /=; smt().
  have -> : BRA.bigi predT (fun k => if (if bwd then 0 <= k < (if bwd then st.`ri - 1 else st.`ri + 1)
                                          else (if bwd then st.`ri - 1 else st.`ri + 1) < k <= 11) \/
                                        k = (if bwd then st.`ri - 1 else st.`ri + 1)
                                     then hitH S k else 0%r) 0 12 =
            BRA.bigi predT (fun k => if (if bwd then 0 <= k < st.`ri else st.`ri < k <= 11)
                                     then hitH S k else 0%r) 0 12.
  + by apply BRA.eq_bigr => k _ /=; smt().
  smt().
apply (xle_trans (Ep dans (fun r => (b2r (S (PB (rd j, st.`oth +^ mask_of r))))%xr + R%xr))).
- apply le_Ep => r _ /=; have h := hpt r; have hb := b2r_ge0 (S (PB (rd j, st.`oth +^ mask_of r))).
  rewrite (to_pos_pos (b2r _)) // (to_pos_pos R) //.
  by apply (ler_trans _ _ _ (le_pos _ _ h)); rewrite to_pos_pos //; smt().
rewrite (eq_Ep _ _ ((fun r => (S (PB (rd j, st.`oth +^ mask_of r)))%xr) + (fun _ => R%xr))) 1:// EpD Ep_mu EpC dans_ll /=.
have -> : mu dans (fun r => S (PB (rd j, st.`oth +^ mask_of r))) = hitB S j.
- by rewrite (dans_maskE (fun x => S (PB (rd j, st.`oth +^ x)))) (dhalf_shift _ (fun x => S (PB (rd j, x)))).
have -> : psi bwd w S st = R + hitB S j.
- rewrite /psi hea /= /rho /R hl /= hA /= /futH hl (posH _ hA hB) /=.
  rewrite (_ : BRA.bigi predT (fun k => if futB bwd st k then hitB S k else 0%r) 0 12 =
               BRA.bigi predT (fun k => if (if bwd then 0 <= k < st.`ri - 1 else st.`ri + 1 < k <= 11) \/ k = j
                                          then hitB S k else 0%r) 0 12).
  + by apply BRA.eq_bigr => k _ /=; rewrite /futB /j; smt().
  rewrite (sum_split (fun k => if bwd then 0 <= k < st.`ri - 1 else st.`ri + 1 < k <= 11)) /j; 1,2: smt().
  smt().
have h0 : 0%r <= hitB S j by apply ge0_mu.
by rewrite /= !to_pos_pos //; smt().
qed.

(* The answer that completes a chain changes nothing of its risk. *)
lemma Ep_last bwd w (m : (point, ans) fmap) c pend st (S : point -> bool) :
  !st.`fin => last witness st.`chain = c => !isA c => !isB c => !(if bwd then 0 < st.`ri else st.`ri < 11) =>
  Ep dans (fun r => (psi bwd w S (cstep bwd w st c true r pend m.[c <- r]))%xr) <= (psi bwd w S st)%xr.
proof.
move=> hfin hl hA hB hfinal.
rewrite (eq_Ep _ _ (fun _ => (psi bwd w S st)%xr)) => [r _ /= | ]; 2: by rewrite EpC dans_ll.
by move: hfinal; rewrite /cstep hfin hl /= hB hA /= => -> /=; rewrite /psi /rho /nA /futH /futB.
qed.

lemma early_mono bwd p st c fresh r pend m : st.`early => (cstep bwd p st c fresh r pend m).`early.
proof. by case: (cstep_cases bwd p st c fresh r pend m) => [[_ ->] | [_ [_ [_ [[q [_ [-> _]]] | [_ [-> _]]]]]]] /#. qed.

(* One fresh answer: the expected risk of a chain does not grow, its hit set S being the answered
   and submitted points, c among them. *)
lemma Ep_answer bwd w (m : (point, ans) fmap) c pend st (S : point -> bool) :
  shape bwd w st => S c => (forall r q, (q \in m.[c <- r] \/ q \in pend) = S q) =>
  Ep dans (fun r => (psi bwd w S (cstep bwd w st c true r pend m.[c <- r]))%xr) <= (psi bwd w S st)%xr.
proof.
move=> hsh hSc hS; case: (!st.`fin /\ last witness st.`chain = c) => [[hfin hl] | hno]; last first.
- rewrite (eq_Ep _ _ (fun _ => (psi bwd w S st)%xr)) => [r _ /= | ]; 2: by rewrite EpC dans_ll.
  by rewrite /cstep /= hno.
case: (st.`early) => hea.
- rewrite (eq_Ep _ _ (fun _ => 1%xr)) => [r _ /= | ]; 2: by rewrite EpC dans_ll /psi hea.
  by rewrite /psi (early_mono _ _ _ _ _ _ _ _ hea).
case: (isB c) => hB; 1: exact (Ep_stepB _ _ _ _ _ _ _ hsh hea hfin hl hB hS).
case: (isA c) => hA; 1: exact (Ep_stepA _ _ _ _ _ _ _ hsh hea hfin hl hA hSc hS).
case: (if bwd then 0 < st.`ri else st.`ri < 11) => hmore.
- exact (Ep_stepH _ _ _ _ _ _ _ hsh hea hfin hl hA hB hmore hS).
exact (Ep_last _ _ _ _ _ _ _ hfin hl hA hB hmore).
qed.

(* The potential of the adversary's run: the expected risk of the chain of a password drawn from dP,
   with the points answered or submitted, and the budget left. It is 0 once a budget is exceeded. The
   shape of the chains is a guard of the expectation judgments. *)
op phi (kA qB qH ca cb ch : int) (inrun odd : bool) (m : (point, ans) fmap) (pend : point list)
       (sts : pw -> cst) : real =
  if inrun /\ !odd /\ ca <= kA /\ cb <= qB /\ ch <= qH
  then BRA.big predT (fun w => mu1 dP w * psi true w (fun x => x \in m \/ x \in pend) (sts w)) PwT.enum
       + (12%r * p1 * (kA - ca)%r + (qB - cb)%r) * e128 + (qH - ch)%r * e256
  else 0%r.

lemma shape_nA bwd w st : shape bwd w st => 0 <= nA st <= 12.
proof. by move=> [hri [_ [_ [hcnt _]]]]; rewrite /nA hcnt /ndone; smt(). qed.

lemma psi_ge0 bwd w S st : shape bwd w st => 0%r <= psi bwd w S st.
proof. by move=> hsh; rewrite /psi; case: (st.`early) => // _; apply rho_ge0; smt(shape_nA). qed.

lemma psi_add bwd w S c st : shape bwd w st =>
  psi bwd w (fun x => S x \/ x = c) st <=
  psi bwd w S st + (if isApw w c then 12%r * e128 else 0%r) + (if isB c then e128 else 0%r)
  + (if !isA c /\ !isB c then e256 else 0%r).
proof.
move=> hsh; have hn := shape_nA _ _ _ hsh; rewrite /psi.
case: (st.`early) => _; 1: smt(e128_gt0 e256_gt0).
have := rho_add bwd w S c st _; 1: smt().
have : (nA st)%r * e128 <= 12%r * e128 by smt(e128_gt0).
smt().
qed.

(* Submitting a point raises the expected risk by at most the share of its budget. *)
lemma sum_psi_add bwd S c (sts : pw -> cst) : (forall w, shape bwd w (sts w)) =>
  BRA.big predT (fun w => mu1 dP w * psi bwd w (fun x => S x \/ x = c) (sts w)) PwT.enum <=
  BRA.big predT (fun w => mu1 dP w * psi bwd w S (sts w)) PwT.enum
  + (if isA c then 12%r * p1 * e128 else 0%r) + (if isB c then e128 else 0%r)
  + (if !isA c /\ !isB c then e256 else 0%r).
proof.
move=> hsh.
apply (ler_trans (BRA.big predT (fun w => mu1 dP w * psi bwd w S (sts w) +
                    mu1 dP w * (if isApw w c then 12%r * e128 else 0%r) +
                    mu1 dP w * ((if isB c then e128 else 0%r) + (if !isA c /\ !isB c then e256 else 0%r))) PwT.enum)).
- apply ler_sum => w _ /=; have := psi_add bwd w S c (sts w) (hsh w).
  have := ge0_mu dP (pred1 w); smt().
rewrite !BRA.big_split -BRA.mulr_suml sum_dP /=.
have hA : BRA.big predT (fun w => mu1 dP w * (if isApw w c then 12%r * e128 else 0%r)) PwT.enum <=
          (if isA c then 12%r * p1 * e128 else 0%r).
- case: c => [[w0 s0] | b | h] /=; 2,3: by rewrite BRA.big1_eq.
  rewrite (BRA.bigD1 _ _ w0) ?PwT.enumP ?PwT.enum_uniq //= BRA.big1 /=.
  + by move=> w; rewrite /= => hw; rewrite (eq_sym w0) hw.
  by have := mu1_p1 w0; smt(e128_gt0).
smt().
qed.

lemma p1_ge0 : 0%r <= p1 by rewrite /p1; apply pr_ge0.

(* Submitting a point is paid by the budget of its oracle. *)
lemma phi_submit kA qB qH ca cb ch odd (m : (point, ans) fmap) pend sts c :
  (forall w, shape true w (sts w)) =>
  phi kA qB qH (ca + b2i (isA c)) (cb + b2i (isB c)) (ch + b2i (!isA c /\ !isB c)) true odd m (c :: pend) sts
  <= phi kA qB qH ca cb ch true odd m pend sts.
proof.
move=> hsh; rewrite /phi /=.
have hge : 0%r <= BRA.big predT (fun w => mu1 dP w * psi true w (fun x => x \in m \/ x \in pend) (sts w)) PwT.enum.
- by apply sumr_ge0 => w _ /=; have := psi_ge0 true w (fun x => x \in m \/ x \in pend) (sts w) (hsh w); smt(ge0_mu).
have hS : (fun x => x \in m \/ x = c \/ x \in pend) = (fun x => (x \in m \/ x \in pend) \/ x = c).
- by apply fun_ext => x; rewrite /= /#.
rewrite hS; have /= h := sum_psi_add true (fun x => x \in m \/ x \in pend) c sts hsh.
have h1 := p1_ge0; have h2 := e128_gt0; have h3 := e256_gt0.
have eB : (12%r * p1 * (kA - (ca + b2i (isA c)))%r + (qB - (cb + b2i (isB c)))%r) * e128 +
          (qH - (ch + b2i (!isA c /\ !isB c)))%r * e256 =
          (12%r * p1 * (kA - ca)%r + (qB - cb)%r) * e128 + (qH - ch)%r * e256 -
          ((if isA c then 12%r * p1 * e128 else 0%r) + (if isB c then e128 else 0%r) +
           (if !isA c /\ !isB c then e256 else 0%r)).
- by rewrite /b2i; case: (isA c) => _; case: (isB c) => _ /=; rewrite ?fromintD ?fromintB; ring.
case: (!odd /\ ca + b2i (isA c) <= kA /\ cb + b2i (isB c) <= qB /\
                  ch + b2i (!isA c /\ !isB c) <= qH) => hg /=.
- have -> /= : !odd /\ ca <= kA /\ cb <= qB /\ ch <= qH by move: hg; rewrite /b2i; smt().
  smt().
case: (!odd /\ ca <= kA /\ cb <= qB /\ ch <= qH) => // hg'.
have hb : 0%r <= (12%r * p1 * (kA - ca)%r + (qB - cb)%r) * e128 + (qH - ch)%r * e256.
- have : 0%r <= (kA - ca)%r by smt().
  have : 0%r <= (qB - cb)%r by smt().
  have : 0%r <= (qH - ch)%r by smt().
  smt().
smt().
qed.

(* Answering a submitted point keeps the expected potential. *)
lemma Ep_phi_answer kA qB qH ca cb ch odd (m : (point, ans) fmap) pend sts c :
  (forall w, shape true w (sts w)) => c \notin m =>
  Ep dans (fun r => (phi kA qB qH ca cb ch true odd m.[c <- r] pend
                        (fun w => cstep true w (sts w) c true r pend m.[c <- r]))%xr)
  <= (phi kA qB qH ca cb ch true odd m (c :: pend) sts)%xr.
proof.
move=> hsh cm; rewrite /phi /=.
case: (!odd /\ ca <= kA /\ cb <= qB /\ ch <= qH) => hg /=; last by rewrite EpC dans_ll.
have hS : forall r, (fun x => x \in m.[c <- r] \/ x \in pend) = (fun x => x \in m \/ x = c \/ x \in pend).
- by move=> r; apply fun_ext => x; rewrite mem_set /= /#.
rewrite (eq_Ep _ _ (fun r => (BRA.big predT (fun w => mu1 dP w * psi true w (fun x => x \in m \/ x = c \/ x \in pend)
                                 (cstep true w (sts w) c true r pend m.[c <- r])) PwT.enum
                              + ((12%r * p1 * (kA - ca)%r + (qB - cb)%r) * e128 + (qH - ch)%r * e256))%xr)).
- by move=> r _ /=; rewrite hS RField.addrA.
rewrite -RField.addrA; apply Ep_sum_le.
- exact dans_ll.
- by move=> w r; apply psi_ge0; apply shape_cstep; apply hsh.
- by move=> w; apply psi_ge0; apply hsh.
- by have := p1_ge0; have := e128_gt0; have := e256_gt0; smt().
move=> w; apply Ep_answer; [apply hsh | by [] | by move=> r q; rewrite mem_set /= /#].
qed.

(* One query of the adversary's run, in a batch of its own: submitted, then answered. *)
lemma Ep_run1 kA qB qH ca cb ch ca' cb' ch' odd (m : (point, ans) fmap) sts c :
  (forall w, shape true w (sts w)) =>
  ca' = ca + b2i (isA c) => cb' = cb + b2i (isB c) => ch' = ch + b2i (!isA c /\ !isB c) =>
  Ep dans (fun r =>
    if c \notin m then
      (forall w, shape true w (cstep true w (sts w) c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r])) `|`
      (phi kA qB qH ca' cb' ch' true odd m.[c <- r] []
         (fun w => cstep true w (sts w) c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r]))%xr
    else
      (forall w, shape true w (cstep true w (sts w) c (c \notin m) (oget m.[c]) [] m)) `|`
      (phi kA qB qH ca' cb' ch' true odd m [] (fun w => cstep true w (sts w) c (c \notin m) (oget m.[c]) [] m))%xr)
  <= (phi kA qB qH ca cb ch true odd m [] sts)%xr.
proof.
move=> hsh -> -> ->; have hsub := phi_submit kA qB qH ca cb ch odd m [] sts c hsh.
case: (c \in m) => cm /=.
- have hst : (fun w => cstep true w (sts w) c false (oget m.[c]) [] m) = sts.
  + by apply fun_ext => w; rewrite /cstep.
  rewrite (eq_Ep _ _ (fun _ => (phi kA qB qH (ca + b2i (isA c)) (cb + b2i (isB c)) (ch + b2i (!isA c /\ !isB c))
                                   true odd m [] sts)%xr)) => [r _ /= | ].
  + have -> : (forall w, shape true w (cstep true w (sts w) c false (oget m.[c]) [] m)) = true.
    * by rewrite eqT => w; rewrite /cstep /=; apply hsh.
    by rewrite /= hst.
  rewrite EpC dans_ll /=; apply le_pos; move: hsub; rewrite /phi /=.
  by have -> : (fun x => x \in m \/ x = c) = (fun x => x \in m) by apply fun_ext => x /#.
rewrite (eq_Ep _ _ (fun r => (phi kA qB qH (ca + b2i (isA c)) (cb + b2i (isB c)) (ch + b2i (!isA c /\ !isB c))
                                 true odd m.[c <- r] [] (fun w => cstep true w (sts w) c true r [] m.[c <- r]))%xr)).
- move=> r _ /=; rewrite get_set_sameE oget_some.
  have -> // : (forall w, shape true w (cstep true w (sts w) c true r [] m.[c <- r])) = true.
  by rewrite eqT => w; apply shape_cstep; apply hsh.
apply (xle_trans _ _ _ (Ep_phi_answer _ _ _ _ _ _ _ _ _ _ _ hsh cm)).
by rewrite /=; apply le_pos; exact hsub.
qed.

(* One query of a batch, with [pend] left in the batch; the counters were charged for the batch. *)
lemma Ep_batch1 kA qB qH ca cb ch odd (m : (point, ans) fmap) pend sts c :
  (forall w, shape true w (sts w)) =>
  Ep dans (fun r =>
    if c \notin m then
      (forall w, shape true w (cstep true w (sts w) c (c \notin m) (oget m.[c <- r].[c]) pend m.[c <- r])) `|`
      (phi kA qB qH ca cb ch true odd m.[c <- r] pend
         (fun w => cstep true w (sts w) c (c \notin m) (oget m.[c <- r].[c]) pend m.[c <- r]))%xr
    else
      (forall w, shape true w (cstep true w (sts w) c (c \notin m) (oget m.[c]) pend m)) `|`
      (phi kA qB qH ca cb ch true odd m pend (fun w => cstep true w (sts w) c (c \notin m) (oget m.[c]) pend m))%xr)
  <= (phi kA qB qH ca cb ch true odd m (c :: pend) sts)%xr.
proof.
move=> hsh; case: (c \in m) => cm /=.
- have hst : (fun w => cstep true w (sts w) c false (oget m.[c]) pend m) = sts.
  + by apply fun_ext => w; rewrite /cstep.
  rewrite (eq_Ep _ _ (fun _ => (phi kA qB qH ca cb ch true odd m pend sts)%xr)) => [r _ /= | ].
  + have -> : (forall w, shape true w (cstep true w (sts w) c false (oget m.[c]) pend m)) = true.
    * by rewrite eqT => w; rewrite /cstep /=; apply hsh.
    by rewrite /= hst.
  rewrite EpC dans_ll /= /phi /=.
  by have -> : (fun x => x \in m \/ x = c \/ x \in pend) = (fun x => x \in m \/ x \in pend) by apply fun_ext => x /#.
rewrite (eq_Ep _ _ (fun r => (phi kA qB qH ca cb ch true odd m.[c <- r] pend
                                 (fun w => cstep true w (sts w) c true r pend m.[c <- r]))%xr)).
- move=> r _ /=; rewrite get_set_sameE oget_some.
  have -> // : (forall w, shape true w (cstep true w (sts w) c true r pend m.[c <- r])) = true.
  by rewrite eqT => w; apply shape_cstep; apply hsh.
exact (Ep_phi_answer _ _ _ _ _ _ _ _ _ _ _ hsh cm).
qed.

(* Submitting a batch of Argon2id queries. *)
lemma phi_submit_list kA qB qH ca cb ch odd (m : (point, ans) fmap) pend sts (l : (pw * W128.word) list) :
  (forall w, shape true w (sts w)) =>
  phi kA qB qH (ca + size l) cb ch true odd m (map PA l ++ pend) sts <= phi kA qB qH ca cb ch true odd m pend sts.
proof.
move=> hsh; elim: l ca => [|x l ih] ca /=; 1: by [].
have := phi_submit kA qB qH (ca + size l) cb ch odd m (map PA l ++ pend) sts (PA x) hsh; rewrite /b2i /=.
by move=> h; apply (ler_trans _ _ _ _ (ih ca)); rewrite (_ : ca + (1 + size l) = ca + size l + 1) 1:/#.
qed.

(* The potential after the run: the risk left for the chain of the real password p. *)
op phid (kA qB qH ca cb ch : int) (odd : bool) (m : (point, ans) fmap) (p : pw) (st : cst) : real =
  if !odd /\ ca <= kA /\ cb <= qB /\ ch <= qH then psi true p (fun x => x \in m) st else 0%r.

lemma psi_own bwd w S st : shape bwd w st =>
  psi bwd w (fun x => S x \/ x = last witness st.`chain) st <= psi bwd w S st.
proof. by move=> hsh; rewrite /psi; case: (st.`early) => // _; apply rho_own. qed.

(* One query of the decryption: the next point of the real chain, an answered point, or [odd]. *)
lemma Ep_dec1 kA qB qH ca cb ch odd (m : (point, ans) fmap) p st c :
  shape true p st =>
  (if c \notin m /\ c <> last witness st.`chain /\ !st.`early then
     Ep dans (fun r => if c \notin m then
        shape true p (cstep true p st c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r]) `|`
        (phid kA qB qH ca cb ch true m.[c <- r] p (cstep true p st c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r]))%xr
      else
        shape true p (cstep true p st c (c \notin m) (oget m.[c]) [] m) `|`
        (phid kA qB qH ca cb ch true m p (cstep true p st c (c \notin m) (oget m.[c]) [] m))%xr)
   else
     Ep dans (fun r => if c \notin m then
        shape true p (cstep true p st c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r]) `|`
        (phid kA qB qH ca cb ch odd m.[c <- r] p (cstep true p st c (c \notin m) (oget m.[c <- r].[c]) [] m.[c <- r]))%xr
      else
        shape true p (cstep true p st c (c \notin m) (oget m.[c]) [] m) `|`
        (phid kA qB qH ca cb ch odd m p (cstep true p st c (c \notin m) (oget m.[c]) [] m))%xr))
  <= (phid kA qB qH ca cb ch odd m p st)%xr.
proof.
move=> hsh; have hg : forall fresh r' (m' : (point, ans) fmap), shape true p (cstep true p st c fresh r' [] m') = true.
- by move=> *; rewrite eqT; apply shape_cstep.
case: (c \in m) => cm /=.
- have -> : cstep true p st c false (oget m.[c]) [] m = st by rewrite /cstep.
  by rewrite hsh /= EpC dans_ll smul1m.
case: (c <> last witness st.`chain /\ !st.`early) => hcase /=.
- rewrite (eq_Ep _ _ (fun _ => 0%xr)) => [r _ /= | ]; 2: by rewrite EpC dans_ll smul1m; apply xle0x.
  by rewrite hg /phid.
rewrite (eq_Ep _ _ (fun r => (phid kA qB qH ca cb ch odd m.[c <- r] p (cstep true p st c true r [] m.[c <- r]))%xr)).
- by move=> r _ /=; rewrite get_set_sameE oget_some hg.
rewrite /phid; case: (!odd /\ ca <= kA /\ cb <= qB /\ ch <= qH) => hgd /=; last by rewrite EpC dans_ll smul1m.
case: (st.`early) => hea.
- rewrite (eq_Ep _ _ (fun _ => 1%xr)) => [r _ /= | ]; 2: by rewrite EpC dans_ll /psi hea.
  by rewrite /psi (early_mono _ _ _ _ _ _ _ _ hea).
have hl : c = last witness st.`chain by smt().
rewrite (eq_Ep _ _ (fun r => (psi true p (fun x => x \in m \/ x = c) (cstep true p st c true r [] m.[c <- r]))%xr)).
- move=> r _ /=; congr; congr; apply fun_ext => x; rewrite mem_set //.
apply (xle_trans (psi true p (fun x => x \in m \/ x = c) st)%xr).
- by apply Ep_answer => // r q; rewrite mem_set.
by rewrite hl /=; apply le_pos; apply (psi_own true p (fun x => x \in m) st hsh).
qed.

(* After the decryption the potential bounds Early_P, the budgets kept and the chain shaped. *)
lemma post_le kA qB qH (p0 : pw) (sts : pw -> cst) (inrun odd : bool) (ca cb ch : int) (m : (point, ans) fmap) :
  ((sts p0).`early /\ !odd /\ ca <= kA /\ cb <= qB /\ ch <= qH /\ shape true p0 (sts p0))%xr <=
  (!inrun /\ shape true p0 (sts p0)) `|` (phid kA qB qH ca cb ch odd m p0 (sts p0))%xr.
proof.
apply xle_cxr_r => -[_ hsh]; apply xle_rle; split; 1: by apply b2r_ge0.
have := rho_ge0 true p0 (fun x => x \in m) (sts p0) _; 1: smt(shape_nA).
by rewrite /phid /psi; case: ((sts p0).`early) => hea /=; smt().
qed.

(* Drawing P after the run: the potential of the run is the expected potential of the real chain. *)
lemma run_dec kA qB qH ca cb ch (inrun odd : bool) (m : (point, ans) fmap) (sts : pw -> cst) :
  Ep dP (fun p => (!false /\ shape true p (sts p)) `|` (phid kA qB qH ca cb ch odd m p (sts p))%xr) <=
  (inrun /\ forall w, shape true w (sts w)) `|` (phi kA qB qH ca cb ch inrun odd m [] sts)%xr.
proof.
apply xle_cxr_r => -[hi hsh].
rewrite (eq_Ep _ _ (fun p => (phid kA qB qH ca cb ch odd m p (sts p))%xr)) => [p _ /= | ]; 1: by rewrite hsh.
rewrite (Ep_fin PwT.enum) ?PwT.enum_uniq; 1: by move=> p _; apply PwT.enumP.
have hd : forall p, 0%r <= phid kA qB qH ca cb ch odd m p (sts p).
- by move=> p; rewrite /phid; case: (!odd /\ ca <= kA /\ cb <= qB /\ ch <= qH) => // _; apply psi_ge0; apply hsh.
rewrite (BXA.eq_bigr _ _ (fun p => (mu1 dP p * phid kA qB qH ca cb ch odd m p (sts p))%xr)).
- by move=> p _ /=; rewrite -(of_realM _ _ (ge0_mu dP (pred1 p)) (hd p)).
rewrite bigXR; 1: by move=> p _; have := hd p; have := ge0_mu dP (pred1 p); smt().
apply xle_rle; split; 1: by apply sumr_ge0 => p _ /=; have := hd p; have := ge0_mu dP (pred1 p); smt().
rewrite /phid /phi hi /=; case: (!odd /\ ca <= kA /\ cb <= qB /\ ch <= qH) => hg /=; last first.
- by rewrite BRA.big1_eq.
have hb : 0%r <= (12%r * p1 * (kA - ca)%r + (qB - cb)%r) * e128 + (qH - ch)%r * e256.
- by have := p1_ge0; have := e128_gt0; have := e256_gt0; smt().
smt().
qed.

(* At the start every chain carries the 66 pairs of its own A points, and the budgets are unused. *)
lemma phi_init kA qB qH y : 0 <= kA => 0 <= qB => 0 <= qH =>
  phi kA qB qH 0 0 0 true false empty [] (fun _ => cbwd y) =
  (12%r * p1 * kA%r + 66%r + qB%r) * e128 + qH%r * e256.
proof.
move=> hkA hqB hqH.
have hS : forall c, !((c \in empty<:point, ans>) \/ (c \in [])) by move=> c; rewrite mem_empty.
have hpsi : forall w, psi true w (fun x => x \in empty<:point, ans> \/ x \in []) (cbwd y) = 66%r * e128.
- move=> w; rewrite /psi /cbwd /= /rho /nA /=.
  have -> : hitA (fun x => x \in empty<:point, ans> \/ x \in []) w = 0%r.
  + by rewrite /hitA mu0_false // => s _; apply hS.
  rewrite BRA.big1 /=; 1: by move=> j; rewrite /hitB mu0_false //; smt(mem_empty).
  rewrite BRA.big1 /=; 1: by move=> j; rewrite /hitH mu0_false //; smt(mem_empty).
  smt().
rewrite /phi /= hkA hqB hqH /=.
rewrite (BRA.eq_bigr _ _ (fun w => mu1 dP w * (66%r * e128))) => [w _ /= | ]; 1: by rewrite hpsi.
by rewrite -BRA.mulr_suml sum_dP; ring.
qed.

(* The backward chains of all passwords from the container y; the chain of the real password p is
   [sts p]. The real password is recorded after the adversary's run, which does not use it. *)
module Bwd = {
  var p   : pw
  var y   : state
  var sts : pw -> cst
  proc init(y0 : state) = { y <- y0; sts <- fun _ => cbwd y0; }
  proc on(c : point, fresh : bool, r : ans, pend : point list) = {
    sts <- fun w => cstep true w (sts w) c fresh r pend R.RO.m;
  }
}.

(* The oracle interface with batches: [abatch] submits several Argon2id queries that are all fixed
   before any of their answers is sampled. *)
module type ABHB = {
  include ABH
  proc abatch(ps : (pw * W128.word) list) : W256.word list
}.

(* Batches answered one query after another, for the oracles that need no batch bookkeeping. *)
module Batch (O : ABH) = {
  proc abatch(ps : (pw * W128.word) list) : W256.word list = {
    var ks, k, rest;
    ks <- [];
    rest <- ps;
    while (rest <> []) {
      k <@ O.a((head witness rest).`1, (head witness rest).`2);
      ks <- rcons ks k;
      rest <- behead rest;
    }
    return ks;
  }
}.

(* The ideal oracle with the bookkeeping of the backward chains and the adversary's query log. The
   adversary cannot read any of these variables. [odd] is a flag for the proof of Lemma G3: after
   the run, a fresh query that is not the next point of the real chain; it is never set. *)
module Mon : ABHB = {
  var inrun : bool
  var log   : (point * int) list   (* the adversary's queries with their batch numbers, repeats included *)
  var bn    : int                  (* the current batch *)
  var odd   : bool

  proc init(y : state) = { inrun <- true; log <- []; bn <- 0; odd <- false; Bwd.init(y); }

  proc query(c : point, pend : point list) : ans = {
    var fresh, r;
    fresh <- c \notin R.RO.m;
    if (inrun) {
      log <- rcons log (c, bn);
    } else {
      if (fresh /\ c <> last witness (Bwd.sts Bwd.p).`chain /\ !(Bwd.sts Bwd.p).`early) odd <- true;
    }
    r <@ R.RO.get(c);
    Bwd.on(c, fresh, r, pend);
    return r;
  }

  proc a(p : pw, s : W128.word) = { var r; bn <- bn + 1; r <@ query(PA (p, s), []); return key_of r; }
  proc b(i : ridx, x : W128.word) = { var r; bn <- bn + 1; r <@ query(PB (i, x), []); return salt_of r; }
  proc h(k : W256.word, i : ridx, x : W128.word) = {
    var r; bn <- bn + 1; r <@ query(PH (k, i, x), []); return mask_of r;
  }

  proc abatch(ps : (pw * W128.word) list) = {
    var pend, ks, r;
    bn <- bn + 1;
    pend <- map PA ps;
    ks <- [];
    while (pend <> []) {
      r <@ query(head witness pend, behead pend);
      ks <- rcons ks (key_of r);
      pend <- behead pend;
    }
    return ks;
  }
}.

(* Counts batched Argon2id queries one by one, and the calls that contain Argon2id queries. *)
module CountB (O : ABHB) = {
  var dp : int
  proc init() = { Count(O).init(); dp <- 0; }
  proc a(p : pw, s : W128.word) = { var k; dp <- dp + 1; k <@ Count(O).a(p, s); return k; }
  proc b = Count(O).b
  proc h = Count(O).h
  proc abatch(ps : (pw * W128.word) list) = {
    var ks;
    if (ps <> []) dp <- dp + 1;
    Count.ca <- Count.ca + size ps;
    ks <@ O.abatch(ps);
    return ks;
  }
}.

(* ---- The invariant through the monitored oracle ------------------------------------------ *)
lemma query_spec inr o0 m0 l0 b0 p0 s0 c0 pend0 :
  hoare [Mon.query : Mon.inrun = inr /\ Mon.odd = o0 /\ R.RO.m = m0 /\ Mon.log = l0 /\ Mon.bn = b0 /\
                     Bwd.p = p0 /\ Bwd.sts = s0 /\ c = c0 /\ pend = pend0 ==>
    Mon.inrun = inr /\ Mon.bn = b0 /\ Bwd.p = p0 /\
    Mon.odd = (o0 \/ !inr /\ c0 \notin m0 /\ c0 <> last witness (s0 p0).`chain /\ !(s0 p0).`early) /\
    R.RO.m = (if c0 \in m0 then m0 else m0.[c0 <- res]) /\ (c0 \in m0 => res = oget m0.[c0]) /\
    Mon.log = (if inr then rcons l0 (c0, b0) else l0) /\
    Bwd.sts = (fun w => cstep true w (s0 w) c0 (c0 \notin m0) res pend0 R.RO.m)].
proof. by proc; inline *; auto => />; smt(get_set_sameE). qed.

lemma mon_a_run : hoare [Mon.a : irun Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.y Bwd.sts ==>
                                 irun Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.y Bwd.sts].
proof.
proc; ecall (query_spec Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.p Bwd.sts (PA (p, s)) []).
auto => &hr hI /= r sts' log' o' m' [ho' [hm [_ [hl hsts]]]].
have [hI' hlat] := irun_bump _ _ _ _ _ _ _ [PA (p{hr}, s{hr})] hI.
by have [] := irun_step _ _ _ _ _ _ _ _ _ _ _ _ _ [] _ hI' hlat ho' hm hl hsts.
qed.

lemma mon_b_run : hoare [Mon.b : irun Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.y Bwd.sts ==>
                                 irun Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.y Bwd.sts].
proof.
proc; ecall (query_spec Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.p Bwd.sts (PB (i, x)) []).
auto => &hr hI /= r sts' log' o' m' [ho' [hm [_ [hl hsts]]]].
have [hI' hlat] := irun_bump _ _ _ _ _ _ _ [PB (i{hr}, x{hr})] hI.
by have [] := irun_step _ _ _ _ _ _ _ _ _ _ _ _ _ [] _ hI' hlat ho' hm hl hsts.
qed.

lemma mon_h_run : hoare [Mon.h : irun Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.y Bwd.sts ==>
                                 irun Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.y Bwd.sts].
proof.
proc; ecall (query_spec Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.p Bwd.sts (PH (k, i, x)) []).
auto => &hr hI /= r sts' log' o' m' [ho' [hm [_ [hl hsts]]]].
have [hI' hlat] := irun_bump _ _ _ _ _ _ _ [PH (k{hr}, i{hr}, x{hr})] hI.
by have [] := irun_step _ _ _ _ _ _ _ _ _ _ _ _ _ [] _ hI' hlat ho' hm hl hsts.
qed.

lemma mon_abatch_run : hoare [Mon.abatch : irun Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.y Bwd.sts ==>
                                           irun Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.y Bwd.sts].
proof.
proc; while (irun Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.y Bwd.sts /\
             forall w, !(Bwd.sts w).`early => later Mon.log Mon.bn (Bwd.sts w).`chain pend).
- wp; ecall (query_spec Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.p Bwd.sts (head witness pend) (behead pend)).
  auto => &hr [[hI hl0] hne] r sts' log' o' m' [ho' [hm [_ [hl hsts]]]].
  have hlat : forall w, !(Bwd.sts{hr} w).`early =>
    later Mon.log{hr} Mon.bn{hr} (Bwd.sts{hr} w).`chain (head witness pend{hr} :: behead pend{hr}).
  + by rewrite head_behead.
  by have [] := irun_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI hlat ho' hm hl hsts.
auto => &hr hI /=; have [hI' hlat] := irun_bump _ _ _ _ _ _ _ (map PA ps{hr}) hI.
by split; [split | move=> sts log odd m pend0 _ []].
qed.


lemma countb_b_e kA qB qH :
  ehoare [Count(Mon).b :
    (Mon.inrun /\ forall w, shape true w (Bwd.sts w)) `|`
    (phi kA qB qH Count.ca Count.cb Count.ch Mon.inrun Mon.odd R.RO.m [] Bwd.sts)%xr ==>
    (Mon.inrun /\ forall w, shape true w (Bwd.sts w)) `|`
    (phi kA qB qH Count.ca Count.cb Count.ch Mon.inrun Mon.odd R.RO.m [] Bwd.sts)%xr].
proof.
proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hsh]; rewrite hi /=.
by apply (Ep_run1 _ _ _ _ _ _ _ _ _ _ _ _ _ hsh); rewrite /b2i.
qed.

lemma countb_a_e kA qB qH :
  ehoare [CountB(Mon).a :
    (Mon.inrun /\ forall w, shape true w (Bwd.sts w)) `|`
    (phi kA qB qH Count.ca Count.cb Count.ch Mon.inrun Mon.odd R.RO.m [] Bwd.sts)%xr ==>
    (Mon.inrun /\ forall w, shape true w (Bwd.sts w)) `|`
    (phi kA qB qH Count.ca Count.cb Count.ch Mon.inrun Mon.odd R.RO.m [] Bwd.sts)%xr].
proof.
proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hsh]; rewrite hi /=.
by apply (Ep_run1 _ _ _ _ _ _ _ _ _ _ _ _ _ hsh); rewrite /b2i.
qed.

lemma countb_h_e kA qB qH :
  ehoare [Count(Mon).h :
    (Mon.inrun /\ forall w, shape true w (Bwd.sts w)) `|`
    (phi kA qB qH Count.ca Count.cb Count.ch Mon.inrun Mon.odd R.RO.m [] Bwd.sts)%xr ==>
    (Mon.inrun /\ forall w, shape true w (Bwd.sts w)) `|`
    (phi kA qB qH Count.ca Count.cb Count.ch Mon.inrun Mon.odd R.RO.m [] Bwd.sts)%xr].
proof.
proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hsh]; rewrite hi /=.
by apply (Ep_run1 _ _ _ _ _ _ _ _ _ _ _ _ _ hsh); rewrite /b2i.
qed.

lemma countb_abatch_e kA qB qH :
  ehoare [CountB(Mon).abatch :
    (Mon.inrun /\ forall w, shape true w (Bwd.sts w)) `|`
    (phi kA qB qH Count.ca Count.cb Count.ch Mon.inrun Mon.odd R.RO.m [] Bwd.sts)%xr ==>
    (Mon.inrun /\ forall w, shape true w (Bwd.sts w)) `|`
    (phi kA qB qH Count.ca Count.cb Count.ch Mon.inrun Mon.odd R.RO.m [] Bwd.sts)%xr].
proof.
proc; inline Mon.abatch; wp.
while ((Mon.inrun /\ forall w, shape true w (Bwd.sts w)) `|`
       (phi kA qB qH Count.ca Count.cb Count.ch Mon.inrun Mon.odd R.RO.m pend Bwd.sts)%xr).
- by move=> &hr; apply xle_cxr_r => /= ->.
- inline *; auto => &hr /=; apply xle_cxr_r => -[hne [hi hsh]]; rewrite hi /=.
  apply (xle_trans (phi kA qB qH Count.ca{hr} Count.cb{hr} Count.ch{hr} true Mon.odd{hr} R.RO.m{hr}
                     (head witness pend{hr} :: behead pend{hr}) Bwd.sts{hr})%xr).
  + exact (Ep_batch1 _ _ _ _ _ _ _ _ _ _ _ hsh).
  by rewrite head_behead.
auto => &hr /=; apply xle_cxr => -[hi hsh]; split; 1: by split.
have := phi_submit_list kA qB qH Count.ca{hr} Count.cb{hr} Count.ch{hr} Mon.odd{hr} R.RO.m{hr} [] Bwd.sts{hr} ps{hr} hsh.
by rewrite cats0 hi /= => h; apply le_pos.
qed.

lemma mon_b_dec kA qB qH :
  ehoare [Mon.b :
    (!Mon.inrun /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
    (phid kA qB qH Count.ca Count.cb Count.ch Mon.odd R.RO.m Bwd.p (Bwd.sts Bwd.p))%xr ==>
    (!Mon.inrun /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
    (phid kA qB qH Count.ca Count.cb Count.ch Mon.odd R.RO.m Bwd.p (Bwd.sts Bwd.p))%xr].
proof.
proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hsh]; rewrite hi /=.
exact (Ep_dec1 _ _ _ _ _ _ _ _ _ _ _ hsh).
qed.

lemma mon_a_dec kA qB qH :
  ehoare [Mon.a :
    (!Mon.inrun /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
    (phid kA qB qH Count.ca Count.cb Count.ch Mon.odd R.RO.m Bwd.p (Bwd.sts Bwd.p))%xr ==>
    (!Mon.inrun /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
    (phid kA qB qH Count.ca Count.cb Count.ch Mon.odd R.RO.m Bwd.p (Bwd.sts Bwd.p))%xr].
proof.
proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hsh]; rewrite hi /=.
exact (Ep_dec1 _ _ _ _ _ _ _ _ _ _ _ hsh).
qed.

lemma mon_h_dec kA qB qH :
  ehoare [Mon.h :
    (!Mon.inrun /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
    (phid kA qB qH Count.ca Count.cb Count.ch Mon.odd R.RO.m Bwd.p (Bwd.sts Bwd.p))%xr ==>
    (!Mon.inrun /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
    (phid kA qB qH Count.ca Count.cb Count.ch Mon.odd R.RO.m Bwd.p (Bwd.sts Bwd.p))%xr].
proof.
proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hsh]; rewrite hi /=.
exact (Ep_dec1 _ _ _ _ _ _ _ _ _ _ _ hsh).
qed.

(* The decryption keeps the potential of the real chain. *)
lemma dec_e kA qB qH :
  ehoare [Net(Mon).dec :
    (!Mon.inrun /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
    (phid kA qB qH Count.ca Count.cb Count.ch Mon.odd R.RO.m Bwd.p (Bwd.sts Bwd.p))%xr ==>
    (!Mon.inrun /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
    (phid kA qB qH Count.ca Count.cb Count.ch Mon.odd R.RO.m Bwd.p (Bwd.sts Bwd.p))%xr].
proof.
proc; while ((!Mon.inrun /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
             (phid kA qB qH Count.ca Count.cb Count.ch Mon.odd R.RO.m Bwd.p (Bwd.sts Bwd.p))%xr).
- by move=> &hr; apply xle_cxr_r.
- conseq (_ : ((!Mon.inrun /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
              (phid kA qB qH Count.ca Count.cb Count.ch Mon.odd R.RO.m Bwd.p (Bwd.sts Bwd.p))%xr) ==> _).
  + by move=> &hr; apply xle_cxr_r.
  + by move=> &hr; apply xle_cxr_r.
  wp; call (mon_h_dec kA qB qH); call (mon_a_dec kA qB qH); call (mon_b_dec kA qB qH); skip => &hr.
  by apply xlexx.
by auto.
qed.

(* The batches with logged A queries through one call of the monitored oracle. *)
lemma mon_a_bc : hoare [Mon.a : Mon.inrun /\ size (undup (bset Mon.log)) < CountB.dp /\
                                all (fun (e : point * int) => e.`2 <= Mon.bn) Mon.log ==>
                                Mon.inrun /\ size (undup (bset Mon.log)) <= CountB.dp /\
                                all (fun (e : point * int) => e.`2 <= Mon.bn) Mon.log].
proof.
proc; ecall (query_spec Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.p Bwd.sts (PA (p, s)) []).
auto => &hr [hi [hs ha]] /= r sts' log' o' m' [_ [_ [_ [hl _]]]].
by rewrite hl hi /= bset_rcons /= size_undup_rcons all_rcons1 (all_bump _ _ ha) /= /b2i; smt().
qed.

lemma mon_b_bc : hoare [Mon.b : Mon.inrun /\ size (undup (bset Mon.log)) <= CountB.dp /\
                                all (fun (e : point * int) => e.`2 <= Mon.bn) Mon.log ==>
                                Mon.inrun /\ size (undup (bset Mon.log)) <= CountB.dp /\
                                all (fun (e : point * int) => e.`2 <= Mon.bn) Mon.log].
proof.
proc; ecall (query_spec Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.p Bwd.sts (PB (i, x)) []).
auto => &hr [hi [hs ha]] /= r sts' log' o' m' [_ [_ [_ [hl _]]]].
by rewrite hl hi /= bset_rcons /= all_rcons1 (all_bump _ _ ha).
qed.

lemma mon_h_bc : hoare [Mon.h : Mon.inrun /\ size (undup (bset Mon.log)) <= CountB.dp /\
                                all (fun (e : point * int) => e.`2 <= Mon.bn) Mon.log ==>
                                Mon.inrun /\ size (undup (bset Mon.log)) <= CountB.dp /\
                                all (fun (e : point * int) => e.`2 <= Mon.bn) Mon.log].
proof.
proc; ecall (query_spec Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.p Bwd.sts (PH (k, i, x)) []).
auto => &hr [hi [hs ha]] /= r sts' log' o' m' [_ [_ [_ [hl _]]]].
by rewrite hl hi /= bset_rcons /= all_rcons1 (all_bump _ _ ha).
qed.

lemma mon_abatch_bc : hoare [Mon.abatch :
  Mon.inrun /\ size (undup (bset Mon.log)) + b2i (ps <> []) <= CountB.dp /\
  all (fun (e : point * int) => e.`2 <= Mon.bn) Mon.log ==>
  Mon.inrun /\ size (undup (bset Mon.log)) <= CountB.dp /\ all (fun (e : point * int) => e.`2 <= Mon.bn) Mon.log].
proof.
proc; while (Mon.inrun /\ size (undup (bset Mon.log)) + b2i (pend <> [] /\ !(Mon.bn \in bset Mon.log)) <= CountB.dp /\
             all (fun (e : point * int) => e.`2 <= Mon.bn) Mon.log /\ all isA pend).
- wp; ecall (query_spec Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.p Bwd.sts (head witness pend) (behead pend)).
  auto => &hr [[hi [hs [ha hA]]] hne] /= r sts' log' o' m' [_ [_ [_ [hl _]]]].
  have [hh1 hh2] : isA (head witness pend{hr}) /\ all isA (behead pend{hr}) by move: hA hne; case: (pend{hr}).
  rewrite hl hi /= bset_rcons hh1 /= size_undup_rcons mem_rcons /= all_rcons1 ha hh2 /=.
  by move: hs; rewrite hne /= /b2i; smt().
auto => &hr [hi [hs ha]] /=; split; 2: by rewrite /b2i; smt().
have hf := bset_fresh _ _ (Mon.bn{hr} + 1) ha _; 1: smt().
rewrite hi hf (all_bump _ _ ha) /=; split; 2: by elim: (ps{hr}).
by move: hs; case: (ps{hr}).
qed.

module type AdvABH (O : ABHB) = {
  proc run(y : state) : unit
}.

(* The lazy game: P is drawn and not used during the run, Y is uniform, the table starts empty, and
   after the adversary halts the finalization inverts Y under P through the same table. *)
module ChainGame (B : AdvABH) = {
  proc main() : state = {
    var p, y, x;
    R.RO.init();
    CountB(Mon).init();
    p <$ dP;
    y <$ dstate;
    Mon.init(y);
    B(CountB(Mon)).run(y);
    Mon.inrun <- false;
    Bwd.p <- p;
    x <@ Net(Mon).dec(p, y);
    return x;
  }
}.

(* The lazy game with P drawn after the adversary's run, which does not use it. *)
module ChainLate (B : AdvABH) = {
  proc main() : state = {
    var p, y, x;
    R.RO.init();
    CountB(Mon).init();
    y <$ dstate;
    Mon.init(y);
    B(CountB(Mon)).run(y);
    Mon.inrun <- false;
    p <$ dP;
    Bwd.p <- p;
    x <@ Net(Mon).dec(p, y);
    return x;
  }
}.

(* The lemmas on the real chain hold for any adversary; Lemma G3 below also uses its budgets. *)
section.

declare module B <: AdvABH {-R.RO, -Mon, -Bwd, -Count, -CountB}.

lemma run_inv : hoare [ChainGame(B).main : true ==>
  inv true false R.RO.m Mon.log Mon.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\ !Mon.odd /\
  (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs)].
proof.
proc; inline Net(Mon).dec Mon.a Mon.b Mon.h.
wp; while (!Mon.inrun /\ !Mon.odd /\ p0 = Bwd.p /\ -1 <= i <= 11 /\
           inv true false R.RO.m Mon.log Mon.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
           tracks true Bwd.p R.RO.m (cbwd Bwd.y) (3 * (11 - i)) /\
           (0 <= i => at (iter (3 * (11 - i)) (adv true Bwd.p R.RO.m) (cbwd Bwd.y)) i y0 (PB (rd i, y0.`1))) /\
           (i = -1 => (iter (3 * (11 - i)) (adv true Bwd.p R.RO.m) (cbwd Bwd.y)).`fin /\
                      (iter (3 * (11 - i)) (adv true Bwd.p R.RO.m) (cbwd Bwd.y)).`xs = y0)).
- seq 5 : (!Mon.inrun /\ !Mon.odd /\ p0 = Bwd.p /\ 0 <= i <= 11 /\
           inv true false R.RO.m Mon.log Mon.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
           tracks true Bwd.p R.RO.m (cbwd Bwd.y) (3 * (11 - i) + 1) /\
           at (iter (3 * (11 - i) + 1) (adv true Bwd.p R.RO.m) (cbwd Bwd.y)) i y0 (PA (Bwd.p, s))).
  + wp; ecall (query_spec Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.p Bwd.sts (PB (i0, x0)) []); auto.
    move=> &hr [[hi [ho [hp [hrng [hinv [htr [hat _]]]]]]] hc] /= r sts' log' o' m' [ho' [hm [hr' [hl hsts]]]].
    have -> : log' = Mon.log{hr} by rewrite hl hi.
    have hat' := hat hc; have [hfin [_ [_ [_ hlast]]]] := hat'.
    have hj : 0 <= 3 * (11 - i{hr}) by smt().
    have [htr' hw] := iter_query true Bwd.p{hr} _ m' _ _ _ r hj htr hfin hlast hm hr'.
    have -> : o' = false.
    * rewrite ho' ho hi /=; case: ((Bwd.sts{hr} Bwd.p{hr}).`early) => //= hea.
      have [_ [_ [_ hne]]] := hinv; have [_ [_ [_ [_ hdet]]]] := hne hea.
      by have := dec_point _ _ _ _ _ _ hdet hj htr hfin; rewrite hlast /#.
    have hst : sts' Bwd.p{hr} = cstep true Bwd.p{hr} (Bwd.sts{hr} Bwd.p{hr}) (PB (rd i{hr}, y0{hr}.`1))
                 (PB (rd i{hr}, y0{hr}.`1) \notin R.RO.m{hr}) r [] m' by rewrite hsts.
    rewrite hi hp /= (inv_step_off true _ m' _ _ (Mon.bn{hr} + 1) _ _ _ _ _ r [] hinv hm hst) htr' /=.
    by split; [smt() | exact (stepB _ _ _ _ _ _ _ hat' hw)].
  seq 5 : (!Mon.inrun /\ !Mon.odd /\ p0 = Bwd.p /\ 0 <= i <= 11 /\
           inv true false R.RO.m Mon.log Mon.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
           tracks true Bwd.p R.RO.m (cbwd Bwd.y) (3 * (11 - i) + 1 + 1) /\
           at (iter (3 * (11 - i) + 1 + 1) (adv true Bwd.p R.RO.m) (cbwd Bwd.y)) i y0 (PH (k, rd i, y0.`1))).
  + wp; ecall (query_spec Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.p Bwd.sts (PA (Bwd.p, s0)) []); auto.
    move=> &hr [hi [ho [hp [hrng [hinv [htr hat]]]]]] /=; split; 1: exact hp.
    move=> _ r sts' log' o' m' [ho' [hm [hr' [hl hsts]]]].
    have -> : log' = Mon.log{hr} by rewrite hl hi.
    have [hfin [_ [_ [_ hlast]]]] := hat.
    have hj : 0 <= 3 * (11 - i{hr}) + 1 by smt().
    have [htr' hw] := iter_query true Bwd.p{hr} _ m' _ _ _ r hj htr hfin hlast hm hr'.
    have -> : o' = false.
    * rewrite ho' ho hi /=; case: ((Bwd.sts{hr} Bwd.p{hr}).`early) => //= hea.
      have [_ [_ [_ hne]]] := hinv; have [_ [_ [_ [_ hdet]]]] := hne hea.
      by have := dec_point _ _ _ _ _ _ hdet hj htr hfin; rewrite hlast /#.
    have hst : sts' Bwd.p{hr} = cstep true Bwd.p{hr} (Bwd.sts{hr} Bwd.p{hr}) (PA (Bwd.p{hr}, s{hr}))
                 (PA (Bwd.p{hr}, s{hr}) \notin R.RO.m{hr}) r [] m' by rewrite hsts.
    move: htr' hw; rewrite (_ : 3 * (11 - i{hr}) + 1 + 1 = 3 * (11 - i{hr}) + 2) 1:/# => htr' hw.
    rewrite hi hp /= (inv_step_off true _ m' _ _ (Mon.bn{hr} + 1) _ _ _ _ _ r [] hinv hm hst) htr' /=.
    by split; [smt() | exact (stepA _ _ _ _ _ _ _ _ hat hw)].
  wp; ecall (query_spec Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.p Bwd.sts (PH (k0, i1, x1)) []); auto.
  move=> &hr [hi [ho [hp [hrng [hinv [htr hat]]]]]] /= r sts' log' o' m' [ho' [hm [hr' [hl hsts]]]].
  have -> : log' = Mon.log{hr} by rewrite hl hi.
  have [hfin [_ [_ [_ hlast]]]] := hat.
  have hj : 0 <= 3 * (11 - i{hr}) + 2 by smt().
  have [htr' hw] := iter_query true Bwd.p{hr} _ m' _ _ _ r hj htr hfin hlast hm hr'.
  have -> : o' = false.
  + rewrite ho' ho hi /=; case: ((Bwd.sts{hr} Bwd.p{hr}).`early) => //= hea.
    have [_ [_ [_ hne]]] := hinv; have [_ [_ [_ [_ hdet]]]] := hne hea.
    by have := dec_point _ _ _ _ _ _ hdet hj htr hfin; rewrite hlast /#.
  have hst : sts' Bwd.p{hr} = cstep true Bwd.p{hr} (Bwd.sts{hr} Bwd.p{hr}) (PH (k{hr}, rd i{hr}, y0{hr}.`1))
               (PH (k{hr}, rd i{hr}, y0{hr}.`1) \notin R.RO.m{hr}) r [] m' by rewrite hsts.
  have [hB hF] := stepH _ _ _ _ _ _ _ _ hat hw.
  move: htr' hB hF; rewrite (_ : 3 * (11 - i{hr}) + 2 + 1 = 3 * (11 - i{hr}) + 3) 1:/# => htr' hB hF.
  rewrite (_ : 3 * (11 - (i{hr} - 1)) = 3 * (11 - i{hr}) + 3) 1:/#.
  rewrite hi hp /= (inv_step_off true _ m' _ _ (Mon.bn{hr} + 1) _ _ _ _ _ r [] hinv hm hst) htr' /=.
  split; 1: smt().
  by split=> h; [apply hB | apply hF]; smt().
wp; call (_ : irun Mon.inrun Mon.odd R.RO.m Mon.log Mon.bn Bwd.y Bwd.sts).
- by proc; inline Count(Mon).a; wp; call mon_a_run; auto.
- by proc; call mon_b_run; auto.
- by proc; call mon_h_run; auto.
- by proc; call mon_abatch_run; auto.
inline *; auto => _ _ p _ y _; split.
- by rewrite /irun /= => w; apply inv_init.
move=> _ sts bn log odd m [_ [ho hinv]]; split.
- rewrite ho (inv_stop _ _ _ _ _ _ _ (hinv p)) /=; split; 1: by rewrite /tracks /#.
  by rewrite iter0 /at /cbwd.
move=> sts' bn' log' odd' m' i y' hi [ho' [hrng [hinv' [htr [_ hend]]]]].
rewrite hinv' ho' /= => hea.
have [hfin hxs] := hend _; 1: smt().
have [_ [_ [_ hne]]] := hinv'; have [_ [_ [_ [_ hdet]]]] := hne hea.
have hj : 0 <= 3 * (11 - i) by smt().
have hs : stopped m' (iter (3 * (11 - i)) (adv true p m') (cbwd y)) by rewrite /stopped hfin.
have := determined_end _ _ _ _ _ _ hdet hj htr hs.
by move=> /strip_eq [_ [-> [_ [_ [_ ->]]]]]; rewrite hfin hxs.
qed.

(* Lemma G2 (order). On not Early_P, if the adversary queried c_t, it queried c_(t-1) first, in an
   earlier batch; without batches this is an earlier query. *)
lemma G2 : hoare [ChainGame(B).main : true ==>
  !(Bwd.sts Bwd.p).`early => forall t, 1 <= t < size (Bwd.sts Bwd.p).`chain =>
    nth witness (Bwd.sts Bwd.p).`chain t \in map fst Mon.log =>
    nth witness (Bwd.sts Bwd.p).`chain (t - 1) \in map fst Mon.log /\
    bnof Mon.log (nth witness (Bwd.sts Bwd.p).`chain (t - 1)) < bnof Mon.log (nth witness (Bwd.sts Bwd.p).`chain t)].
proof.
conseq run_inv => _ _ xr p sts y bn log odd m [hinv _] hea; have [_ [_ [_ hne]]] := hinv.
by have [h _] := hne hea; move: h; rewrite /ordered.
qed.

(* Lemma G5. On not Early_P the 36 points of the chain are pairwise distinct; on Comp(P) and not
   Early_P the adversary made at least twelve distinct A queries with password P. *)
lemma G5 : hoare [ChainGame(B).main : true ==>
  !(Bwd.sts Bwd.p).`early => size (Bwd.sts Bwd.p).`chain = 36 /\ uniq (Bwd.sts Bwd.p).`chain /\
    (comp (Bwd.sts Bwd.p).`chain Mon.log => 12 <= count (isApw Bwd.p) (undup (map fst Mon.log)))].
proof.
conseq run_inv => _ _ xr p sts y bn log odd m [hinv [_ hend]] hea; have [_ [_ [hsh hne]]] := hinv.
have [_ [_ [hu _]]] := hne hea; have [hfin _] := hend hea.
have [_ [_ [hsz [hcnt [hall [hf _]]]]]] := hsh; have [hn hp] := hf hfin.
rewrite hu /=; split; 1: by rewrite hsz hn hp.
by move=> hc; have := comp_count _ _ _ hu hall hc; rewrite hcnt hn hp.
qed.

(* The invariant of the real chain at the end of the game. *)
lemma chain_inv : hoare [ChainGame(B).main : true ==>
  inv true false R.RO.m Mon.log Mon.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p)].
proof. by conseq run_inv => _ _ xr p sts y bn log odd m [h _]. qed.

(* The finalization computes Inv_P(Y), and the bookkeeping reaches its end on not Early_P. *)
lemma chain_end : hoare [ChainGame(B).main : true ==> !(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs].
proof. by conseq run_inv => _ _ xr p sts y bn log odd m [_ [_ ?]]. qed.

(* The adversary's A queries in the log are at most its A count. *)
lemma log_count : hoare [ChainGame(B).main : true ==> count isA (map fst Mon.log) <= Count.ca].
proof.
proc; inline Net(Mon).dec.
wp; while (!Mon.inrun /\ count isA (map fst Mon.log) <= Count.ca); 1: by inline *; auto => /> /#.
wp; call (_ : Mon.inrun /\ count isA (map fst Mon.log) <= Count.ca).
- by proc; inline *; auto => />; smt(map_rcons count_rcons1).
- by proc; inline *; auto => />; smt(map_rcons count_rcons1).
- by proc; inline *; auto => />; smt(map_rcons count_rcons1).
- proc; inline Mon.abatch; wp.
  while (Mon.inrun /\ count isA (map fst Mon.log) + count isA pend <= Count.ca).
  + by inline *; auto => />; smt(map_rcons count_rcons1 head_behead).
  by auto => />; smt(count_isA_PA).
by inline *; auto.
qed.

(* The batches with logged A queries are at most the calls with A queries. *)
lemma batch_count : hoare [ChainGame(B).main : true ==> size (undup (bset Mon.log)) <= CountB.dp].
proof.
proc; inline Net(Mon).dec.
wp; while (!Mon.inrun /\ size (undup (bset Mon.log)) <= CountB.dp); 1: by inline *; auto => /> /#.
wp; call (_ : Mon.inrun /\ size (undup (bset Mon.log)) <= CountB.dp /\
              all (fun (e : point * int) => e.`2 <= Mon.bn) Mon.log).
- by proc; inline Count(Mon).a; wp; call mon_a_bc; auto => /#.
- by proc; call mon_b_bc; auto.
- by proc; call mon_h_bc; auto.
- by proc; wp; call mon_abatch_bc; auto => /> &hr; rewrite /b2i /#.
by inline *; auto.
qed.

(* Corollary G7 in the lazy game: on Comp(P) without Early_P, the twelve A points of the chain lie in
   twelve batches, so at least twelve calls contained A queries. *)
lemma comp_depth : hoare [ChainGame(B).main : true ==>
  !(Bwd.sts Bwd.p).`early => comp (Bwd.sts Bwd.p).`chain Mon.log => 12 <= CountB.dp].
proof.
conseq run_inv batch_count => // &hr _ xr p sts y bn log odd m dp [[hinv [_ hend]] hdp] hea hc.
have [_ [_ [hsh hne]]] := hinv; have [hord [_ [hu _]]] := hne hea; have [hfin _] := hend hea.
have [_ [_ [_ [hcnt [_ [hf _]]]]]] := hsh; have [hn hp] := hf hfin.
by have := comp_batches _ _ hord hc hu; rewrite hcnt hn hp /b2i /= => /#.
qed.

(* P can be drawn after the run. *)
equiv chain_late : ChainGame(B).main ~ ChainLate(B).main :
  ={glob B} ==> ={res, glob B, glob Bwd, glob Mon, R.RO.m, Count.ca, Count.cb, Count.ch}.
proof.
proc; swap{1} 3 4.
call (_ : ={glob Mon, glob Bwd, R.RO.m}); 1: by sim.
wp; rnd; wp.
call (_ : ={Mon.inrun, Mon.log, Mon.bn, Mon.odd, Bwd.sts, Bwd.y, R.RO.m, Count.ca, Count.cb, Count.ch,
            CountB.dp} /\ Mon.inrun{1}).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; wp; while (={pend, ks0, Mon.inrun, Mon.log, Mon.bn, Mon.odd, Bwd.sts, R.RO.m} /\ Mon.inrun{1});
     auto.
by inline *; auto.
qed.

end section.

section.

declare op kA : int.
declare op qB : int.
declare op qH : int.

declare module B <: AdvABH {-R.RO, -Mon, -Bwd, -Count, -CountB}.

(* The budgets hold on every run, for every implementation of the oracles. *)
declare axiom B_bounded (O <: ABHB {-Count, -CountB, -B}) :
  hoare [B(CountB(O)).run : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 ==>
                            Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH].

local lemma G3s_e : 0 <= kA => 0 <= qB => 0 <= qH =>
  ehoare [ChainLate(B).main : ((12%r * p1 * kA%r + 66%r + qB%r) * e128 + qH%r * e256)%xr ==>
    ((Bwd.sts Bwd.p).`early /\ !Mon.odd /\ Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
     shape true Bwd.p (Bwd.sts Bwd.p))%xr].
proof.
move=> hkA hqB hqH; proc.
conseq (_ : _ ==> (!Mon.inrun /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
                  (phid kA qB qH Count.ca Count.cb Count.ch Mon.odd R.RO.m Bwd.p (Bwd.sts Bwd.p))%xr).
- by move=> _; apply xle_cxr_l => // *; apply post_le.
- by move=> &hr; apply xle_cxr_r => h; apply h.
call (dec_e kA qB qH); wp.
conseq (_ : _ ==> (Mon.inrun /\ forall w, shape true w (Bwd.sts w)) `|`
                  (phi kA qB qH Count.ca Count.cb Count.ch Mon.inrun Mon.odd R.RO.m [] Bwd.sts)%xr).
- by move=> _; apply xle_cxr_l => // *; apply run_dec.
- by move=> &hr; apply xle_cxr_r => h; apply h.
call (: (Mon.inrun /\ forall w, shape true w (Bwd.sts w)) `|`
        (phi kA qB qH Count.ca Count.cb Count.ch Mon.inrun Mon.odd R.RO.m [] Bwd.sts)%xr ==>
        (Mon.inrun /\ forall w, shape true w (Bwd.sts w)) `|`
        (phi kA qB qH Count.ca Count.cb Count.ch Mon.inrun Mon.odd R.RO.m [] Bwd.sts)%xr).
- proc ((Mon.inrun /\ forall w, shape true w (Bwd.sts w)) `|`
        (phi kA qB qH Count.ca Count.cb Count.ch Mon.inrun Mon.odd R.RO.m [] Bwd.sts)%xr).
  + by move=> &hr; apply xlexx.
  + by move=> &hr; apply xlexx.
  + exact (countb_a_e kA qB qH).
  + exact (countb_b_e kA qB qH).
  + exact (countb_h_e kA qB qH).
  exact (countb_abatch_e kA qB qH).
inline *; auto => _.
rewrite (eq_Ep _ _ (fun _ => ((12%r * p1 * kA%r + 66%r + qB%r) * e128 + qH%r * e256)%xr)) => [y1 _ /= | ].
- have -> : (forall w, shape true w (cbwd y1)) = true by rewrite eqT => w; apply shape_bwd.
  by rewrite /= (phi_init _ _ _ _ hkA hqB hqH).
by rewrite EpC dstate_ll smul1m.
qed.

(* Lemma G3. *)
(* The budgets hold at the end of the game; the decryption does not count. *)
local lemma counts_ok : hoare [ChainGame(B).main : true ==> Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH].
proof.
proc; inline Net(Mon).dec.
wp; while (Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH); 1: by inline *; auto.
by wp; call (B_bounded Mon); inline *; auto.
qed.

lemma G3 &m : 0 <= kA => 0 <= qB => 0 <= qH =>
  Pr[ChainGame(B).main() @ &m : (Bwd.sts Bwd.p).`early] <=
    (12%r * p1 * kA%r + 66%r + qB%r) / 2%r ^ 128 + qH%r / 2%r ^ 256.
proof.
move=> hkA hqB hqH.
have h1 : Pr[ChainGame(B).main() @ &m : Mon.odd \/ !shape true Bwd.p (Bwd.sts Bwd.p)] = 0%r.
- byphoare => //; hoare; conseq (run_inv B) => _ _ xr p sts y bn log odd m [hinv [ho _]].
  by have [_ [_ [hsh _]]] := hinv; rewrite ho hsh.
have h2 : Pr[ChainGame(B).main() @ &m : !(Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH)] = 0%r.
- by byphoare => //; hoare; conseq counts_ok.
have h3 : Pr[ChainGame(B).main() @ &m : (Bwd.sts Bwd.p).`early /\ !Mon.odd /\ Count.ca <= kA /\ Count.cb <= qB /\
               Count.ch <= qH /\ shape true Bwd.p (Bwd.sts Bwd.p)] <=
          (12%r * p1 * kA%r + 66%r + qB%r) * e128 + qH%r * e256.
- have -> : Pr[ChainGame(B).main() @ &m : (Bwd.sts Bwd.p).`early /\ !Mon.odd /\ Count.ca <= kA /\ Count.cb <= qB /\
                 Count.ch <= qH /\ shape true Bwd.p (Bwd.sts Bwd.p)] =
            Pr[ChainLate(B).main() @ &m : (Bwd.sts Bwd.p).`early /\ !Mon.odd /\ Count.ca <= kA /\ Count.cb <= qB /\
                 Count.ch <= qH /\ shape true Bwd.p (Bwd.sts Bwd.p)].
  + by byequiv (chain_late B).
  byehoare (_ : ((12%r * p1 * kA%r + 66%r + qB%r) * e128 + qH%r * e256)%xr ==> _) => //.
  + exact (G3s_e hkA hqB hqH).
  by have := p1_ge0; have := e128_gt0; have := e256_gt0; smt().
rewrite Pr[mu_split (!Mon.odd /\ Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
                     shape true Bwd.p (Bwd.sts Bwd.p))].
have h4 : Pr[ChainGame(B).main() @ &m : (Bwd.sts Bwd.p).`early /\ !(!Mon.odd /\ Count.ca <= kA /\ Count.cb <= qB /\
               Count.ch <= qH /\ shape true Bwd.p (Bwd.sts Bwd.p))] <=
          Pr[ChainGame(B).main() @ &m : (Mon.odd \/ !shape true Bwd.p (Bwd.sts Bwd.p)) \/
               !(Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH)].
- by rewrite Pr[mu_sub] => // &hr /#.
have h5 : Pr[ChainGame(B).main() @ &m : (Mon.odd \/ !shape true Bwd.p (Bwd.sts Bwd.p)) \/
               !(Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH)] <= 0%r.
- rewrite Pr[mu_or] h1 h2 /=; smt(mu_bounded).
have -> : (12%r * p1 * kA%r + 66%r + qB%r) / 2%r ^ 128 + qH%r / 2%r ^ 256 =
          (12%r * p1 * kA%r + 66%r + qB%r) * e128 + qH%r * e256 by rewrite /e128 /e256.
smt().
qed.

end section.

(* ---- Complete chains during the run ---------------------------------------------------------- *)
(* During the adversary's run a complete chain ends with a point that the adversary queried. *)
op fin_logged (log : (point * int) list) (sts : pw -> cst) =
  forall w, (sts w).`fin => last witness (sts w).`chain \in map fst log.

lemma fin_logged_step (sts : pw -> cst) log c bn fresh r pend m :
  fin_logged log sts => fin_logged (rcons log (c, bn)) (fun w => cstep true w (sts w) c fresh r pend m).
proof.
move=> h w /=; rewrite map_rcons mem_rcons /=.
case: (cstep_cases true w (sts w) c fresh r pend m) => [[_ ->] | [_ [_ [hl hc]]]].
- by move=> hf; right; apply (h w hf).
case: hc => [[q [_ [_ hfi]]] | [hch [_ _]]]; 1: by rewrite hfi.
by move=> _; rewrite hch hl; left.
qed.

(* ---- C': the passwords with which the adversary made at least twelve distinct A queries --------- *)
op cands (log : (point * int) list) : pw list =
  filter (fun w => 12 <= count (isApw w) (undup (map fst log))) PwT.enum.

lemma count_undup_le (p : 'a -> bool) (s : 'a list) : count p (undup s) <= count p s.
proof. by elim: s => //= x s ih; case: (x \in s) => _ /=; smt(count_ge0). qed.

lemma count_isApw (s : point list) :
  Bigint.BIA.big predT (fun w => count (isApw w) s) PwT.enum = count isA s.
proof.
elim: s => [|c s ih] /=; 1: by rewrite Bigint.BIA.big1_eq.
rewrite Bigint.BIA.big_split ih; congr.
case: c => [[w0 s0]|b|h] /=; 2,3: by apply Bigint.BIA.big1 => w _; smt().
rewrite (Bigint.BIA.bigD1 _ _ w0) ?PwT.enumP ?PwT.enum_uniq //= Bigint.BIA.big1 /=.
- by move=> w; rewrite /= => hw; smt().
smt().
qed.

lemma cands_size log : 12 * size (cands log) <= count isA (map fst log).
proof.
pose U := undup (map fst log).
have h1 : 12 * size (cands log) <= Bigint.BIA.big predT (fun w => count (isApw w) U) (cands log).
- rewrite -count_predT -Bigint.big_constz.
  by apply Bigint.ler_sum_seq => w hw _ /=; move: hw; rewrite /cands mem_filter.
have h2 : Bigint.BIA.big predT (fun w => count (isApw w) U) (cands log) <= count isA U.
- rewrite /cands Bigint.BIA.big_filter -(count_isApw U).
  rewrite (Bigint.BIA.big_mkcond (fun w => 12 <= count (isApw w) U) (fun w => count (isApw w) U) PwT.enum).
  by apply Bigint.ler_sum => w _ /=; case: (12 <= count (isApw w) U) => // _; apply count_ge0.
smt(count_undup_le).
qed.
