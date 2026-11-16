(* Lemmas K2-K4, the averaging inequality (2), Theorem 4 and its form with creation refusal
   (DESIGN-NOTES A.5 and Remark G9). *)
require import AllCore List Distr DBool DInterval FMap IntDiv StdBigop Xreal.
require import Suite3 Chain Collision KnownPair Delta2.
require RealSeries DProd Mu_mem.
import W128 StdBigop.Bigreal.BRA.

(* The game with P drawn after the adversary's run, which does not use it. *)
module KPL (A : AdvKP) = {
  proc main(x : state) : unit = {
    var p, y, xf, xb, out;
    R.RO.init();
    Count(Mon2).init();
    y <$ dstate;
    Fwd.init(x);
    Bwd.init(y);
    Mon2.inrun <- true; Mon2.log <- []; Mon2.bn <- 0;
    out <@ A(Count(Mon2)).guess(x, y);
    Mon2.inrun <- false;
    p <$ dP;
    Fwd.p <- p; Bwd.p <- p;
    xf <@ Net(Mon2).enc(p, x);
    xb <@ Net(Mon2).dec(p, y);
  }
}.

section K2K4.
declare module A <: AdvKP {-R.RO, -R.FRO, -RE.FunRO, -Count, -Mon2, -Fwd, -Bwd, -KPGame}.

(* ---- The run facts of the lazy game: no budget and no termination are needed ---------------- *)
lemma run_inv3 : hoare [KPGame(A).main : true ==>
  (Fwd.p = Bwd.p /\
   inv false false R.RO.m Mon2.log Mon2.bn Fwd.p (cfwd Fwd.x) (Fwd.sts Fwd.p) /\
   inv true false R.RO.m Mon2.log Mon2.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
   (!(Fwd.sts Fwd.p).`early => (Fwd.sts Fwd.p).`fin) /\ (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin)) /\
  !Fwd.odd].
proof.
proc.
call dec2_spec; call enc2_spec; wp.
call (_ : irun2 Mon2.inrun R.RO.m Mon2.log Mon2.bn Fwd.x Bwd.y Fwd.sts Bwd.sts /\ !Fwd.odd).
- by proc; call mon2_a_run; auto.
- by proc; call mon2_b_run; auto.
- by proc; call mon2_h_run; auto.
inline *; auto => &hr _ p _ y _ /=; split.
- by rewrite /irun2 /=; split=> w; [apply inv_init_f | apply inv_init].
move=> _ o fs bn log bs m [[_ [hf hb]] hod] /=.
rewrite (inv_stop _ _ _ _ _ _ _ (hf p)) (inv_stop _ _ _ _ _ _ _ (hb p)) /=.
smt().
qed.

lemma run_inv2 : hoare [KPGame(A).main : true ==>
  Fwd.p = Bwd.p /\
  inv false false R.RO.m Mon2.log Mon2.bn Fwd.p (cfwd Fwd.x) (Fwd.sts Fwd.p) /\
  inv true false R.RO.m Mon2.log Mon2.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
  (!(Fwd.sts Fwd.p).`early => (Fwd.sts Fwd.p).`fin) /\ (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin)].
proof. by conseq run_inv3 => /#. qed.

(* Lemma K2. Each call is its own batch, so [ordered] says that the preceding point was queried
   strictly earlier. *)
lemma K2_order : hoare [KPGame(A).main : true ==>
  (!(Fwd.sts Fwd.p).`early => ordered Mon2.log (Fwd.sts Fwd.p).`chain) /\
  (!(Bwd.sts Bwd.p).`early => ordered Mon2.log (Bwd.sts Bwd.p).`chain)].
proof.
conseq run_inv2 => _ _ p fs x bn log p' bs y m [_ [hif [hib _]]]; split=> hea.
- by have [_ [_ [_ hne]]] := hif; have [? _] := hne hea.
by have [_ [_ [_ hne]]] := hib; have [? _] := hne hea.
qed.

lemma K2_distinct : hoare [KPGame(A).main : true ==>
  (!(Fwd.sts Fwd.p).`early => size (Fwd.sts Fwd.p).`chain = 36 /\ uniq (Fwd.sts Fwd.p).`chain) /\
  (!(Bwd.sts Bwd.p).`early => size (Bwd.sts Bwd.p).`chain = 36 /\ uniq (Bwd.sts Bwd.p).`chain)].
proof.
conseq run_inv2 => _ _ p fs x bn log p' bs y m [_ [hif [hib [hff hfb]]]]; split=> hea.
- have [_ [_ [hsh hne]]] := hif; have [_ [_ [hu _]]] := hne hea.
  have [_ [_ [hsz [_ [_ [hf _]]]]]] := hsh; have [hn hp] := hf (hff hea).
  by rewrite hu hsz hn hp.
have [_ [_ [hsh hne]]] := hib; have [_ [_ [hu _]]] := hne hea.
have [_ [_ [hsz [_ [_ [hf _]]]]]] := hsh; have [hn hp] := hf (hfb hea).
by rewrite hu hsz hn hp.
qed.

equiv kp_late : KPGame(A).main ~ KPL(A).main : ={glob A, x} ==>
  ={Fwd.p, Bwd.p, Fwd.sts, Bwd.sts, Fwd.odd, Count.ca, Count.cb, Count.ch}.
proof.
proc; swap{1} 3 8.
call (_ : ={glob Mon2, glob Fwd, glob Bwd, R.RO.m}); 1: by sim.
call (_ : ={glob Mon2, glob Fwd, glob Bwd, R.RO.m}); 1: by sim.
wp; rnd; wp.
call (_ : ={Mon2.inrun, Mon2.log, Mon2.bn, Fwd.sts, Fwd.odd, Fwd.x, Bwd.sts, Bwd.y, R.RO.m, Count.ca, Count.cb, Count.ch} /\
          Mon2.inrun{1}).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
by inline *; auto.
qed.

(* Lemma K2, Cross: the risk of the 132 pairs of distinct rounds. *)
local lemma K2X_e : ehoare [KPL(A).main : (132%r * e128)%xr ==>
  (cross (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain /\ !((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early) /\
   (Fwd.sts Fwd.p).`fin /\ (Bwd.sts Bwd.p).`fin /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p))%xr].
proof.
proc.
conseq (_ : _ ==> (shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
                  (psiX (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr).
- by move=> _; apply xle_cxr_l => // *; apply post_leX.
- by move=> &hr; apply xle_cxr_r => h; apply h.
call dec_eX; call enc_eX; wp.
conseq (_ : _ ==> ((forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|`
                  (PsiX Fwd.sts Bwd.sts)%xr).
- by move=> _; apply xle_cxr_l => // *; apply run_decX.
- by move=> &hr; apply xle_cxr_r => h; apply h.
call (: ((forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|`
        (PsiX Fwd.sts Bwd.sts)%xr ==>
        ((forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|`
        (PsiX Fwd.sts Bwd.sts)%xr).
- proc (((forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|`
        (PsiX Fwd.sts Bwd.sts)%xr).
  + by move=> &hr; apply xlexx.
  + by move=> &hr; apply xlexx.
  + exact count_a_runX.
  + exact count_b_runX.
  exact count_h_runX.
inline *; auto => &hr.
rewrite (eq_Ep _ _ (fun _ => (132%r * e128)%xr)).
- move=> y1 _ /=; rewrite PsiX_init.
  have -> // : ((forall w, shape false w (cfwd x{hr})) /\ (forall w, shape true w (cbwd y1))) = true.
  by rewrite eqT; split => w; [apply shape_fwd | apply shape_bwd].
by rewrite EpC dstate_ll smul1m.
qed.

lemma K2_cross &m (x : state) :
  Pr[KPGame(A).main(x) @ &m : cross (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain /\ !((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early)]
    <= 132%r / 2%r ^ 128.
proof.
have h1 : Pr[KPGame(A).main(x) @ &m : !((!(Fwd.sts Fwd.p).`early => (Fwd.sts Fwd.p).`fin) /\ (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin) /\
             shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p))] = 0%r.
- byphoare => //; hoare; conseq run_inv2 => /> *; smt(inv_shape).
have h2 : Pr[KPGame(A).main(x) @ &m : (cross (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain /\ !((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early)) /\
            ((!(Fwd.sts Fwd.p).`early => (Fwd.sts Fwd.p).`fin) /\ (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin) /\
             shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p))] <= 132%r * e128.
- have -> : Pr[KPGame(A).main(x) @ &m : (cross (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain /\ !((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early)) /\
              ((!(Fwd.sts Fwd.p).`early => (Fwd.sts Fwd.p).`fin) /\ (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin) /\
             shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p))] =
            Pr[KPL(A).main(x) @ &m : (cross (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain /\ !((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early)) /\
              ((!(Fwd.sts Fwd.p).`early => (Fwd.sts Fwd.p).`fin) /\ (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin) /\
             shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p))].
  + by byequiv kp_late => // /#.
  byehoare (_ : (132%r * e128)%xr ==> _) => //.
  + by conseq K2X_e => // &hr /#.
  by have := e128_gt0; smt().
rewrite Pr[mu_split ((!(Fwd.sts Fwd.p).`early => (Fwd.sts Fwd.p).`fin) /\ (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin) /\
             shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p))].
have h3 : Pr[KPGame(A).main(x) @ &m : (cross (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain /\ !((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early)) /\ !((!(Fwd.sts Fwd.p).`early => (Fwd.sts Fwd.p).`fin) /\ (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin) /\
             shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p))] <=
          Pr[KPGame(A).main(x) @ &m : !((!(Fwd.sts Fwd.p).`early => (Fwd.sts Fwd.p).`fin) /\ (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin) /\
             shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p))].
- by rewrite Pr[mu_sub] => // &hr [].
have -> : 132%r / 2%r ^ 128 = 132%r * e128 by rewrite /e128.
smt().
qed.

local lemma typed_game : hoare [KPGame(A).main : true ==> tall Fwd.sts Bwd.sts].
proof.
proc; inline Net(Mon2).enc Net(Mon2).dec.
wp; while (tall Fwd.sts Bwd.sts); 1: by wp; call typed_h; call typed_a; call typed_b; auto.
wp; while (tall Fwd.sts Bwd.sts); 1: by wp; call typed_h; call typed_a; call typed_b; auto.
wp; call (_ : tall Fwd.sts Bwd.sts).
- by proc; call typed_a; auto.
- by proc; call typed_b; auto.
- by proc; call typed_h; auto.
by inline *; auto => />; rewrite /cfwd /cbwd /= => *; smt().
qed.

(* Lemma K4. *)
lemma K4 : hoare [KPGame(A).main : true ==>
  !((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early) => !cross (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain =>
  nbad Mon2.log (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain <= min 11 (count (isApw Fwd.p) (undup (map fst Mon2.log)))].
proof.
conseq run_inv2 typed_game => _ _ bp bsts yb fp fsts fx bn log m [[hp [hif [hib [hff hfb]]]] ht] /negb_or [heaf heab] hcr.
have [_ [_ [hshf hnef]]] := hif; have [hof [_ [huf _]]] := hnef heaf.
have [_ [_ [hshb hneb]]] := hib; have [hob [_ [hub _]]] := hneb heab.
have [_ [_ [hszf [_ [hallf [hf' _]]]]]] := hshf; have [hnf hpf] := hf' (hff heaf).
have [_ [_ [hszb [_ [hallb [hb' _]]]]]] := hshb; have [hnb hpb] := hb' (hfb heab).
have [htf htb] := ht fp.
apply (K4_pure _ _ _ fp) => //.
- by rewrite hszf hnf hpf.
- by rewrite hszb hnb hpb.
- by rewrite -hp.
by rewrite hp.
qed.
end section K2K4.

section Theorem4.

declare op kA : int.
declare op qB : int.
declare op qH : int.

declare module A <: AdvKP {-R.RO, -R.FRO, -RE.FunRO, -Count, -Mon2, -Fwd, -Bwd, -KPGame}.

declare axiom A_bounded (O <: ABH {-Count, -A}) :
  hoare [A(Count(O)).guess : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 ==>
                             Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH].

declare axiom A_ll (O <: ABH {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless A(O).guess.

(* ---- The finalization with a record of its H points ---------------------------------------- *)
local module EncRec (O : ABH) = {
  var hs : point list
  proc run(p : pw, x : state) : state = {
    var i, s, k, m;
    i <- 0; hs <- [];
    while (i < 12) {
      s <@ O.b(rd i, x.`2); k <@ O.a(p, s);
      hs <- rcons hs (PH (k, rd i, x.`2));
      m <@ O.h(k, rd i, x.`2);
      x <- round m x; i <- i + 1;
    }
    return x;
  }
}.

local module DecRec (O : ABH) = {
  var hs : point list
  proc run(p : pw, y : state) : state = {
    var i, s, k, m;
    i <- 11; hs <- [];
    while (0 <= i) {
      s <@ O.b(rd i, y.`1); k <@ O.a(p, s);
      hs <- rcons hs (PH (k, rd i, y.`1));
      m <@ O.h(k, rd i, y.`1);
      y <- unround m y; i <- i - 1;
    }
    return y;
  }
}.

local lemma encrec_fun (p0 : pw) (x0 : state) :
  hoare [EncRec(Orc(RE.FunRO)).run : p = p0 /\ x = x0 ==>
         EncRec.hs = map (h0 RE.FunRO.f p0 x0) (iota_ 0 12)].
proof.
proc; inline *.
while (0 <= i <= 12 /\ p = p0 /\ x = fwdp RE.FunRO.f p0 x0 0 i /\ EncRec.hs = map (h0 RE.FunRO.f p0 x0) (iota_ 0 i)).
- auto => /> &hr h1 h2 h3; split; 1: smt().
  rewrite iotaSr // map_rcons /h0 /=.
  by rewrite /fwdp /= iotaSr // foldl_rcons /mask.
auto => /> &hr; split; 1: by rewrite /fwdp !iota0.
by move=> i2 h1 h2 h3; rewrite (_ : i2 = 12) 1:/#.
qed.

local lemma decrec_fun (p0 : pw) (y0 : state) :
  hoare [DecRec(Orc(RE.FunRO)).run : p = p0 /\ y = y0 ==>
         DecRec.hs = map (hb RE.FunRO.f p0 y0) (iota_ 0 12)].
proof.
proc; inline *.
while (-1 <= i <= 11 /\ p = p0 /\ y = bwdp RE.FunRO.f p0 y0 11 (i + 1) /\
       DecRec.hs = map (hb RE.FunRO.f p0 y0) (iota_ 0 (11 - i))).
- auto => /> &hr h1 h2 h3; split; 1: smt().
  rewrite (_ : 11 - (i{hr} - 1) = (11 - i{hr}) + 1) 1:/# iotaSr 1:/# map_rcons /hb /=.
  rewrite (_ : 11 - (11 - i{hr}) = i{hr}) 1:/# (_ : 12 - (11 - i{hr}) = i{hr} + 1) 1:/# /=.
  rewrite /bwdp (_ : 11 + 1 - (i{hr} - 1 + 1) = (11 - i{hr}) + 1) 1:/# (_ : 11 + 1 - (i{hr} + 1) = 11 - i{hr}) 1:/#.
  by rewrite iotaS 1:/# rev_cons foldl_rcons /mask.
auto => /> &hr; split; 1: by rewrite /bwdp !iota0.
by move=> i2 h1 h2 h3; rewrite (_ : i2 = -1) 1:/#.
qed.

local lemma encrec_fun_ph (p0 : pw) (x0 : state) :
  phoare [EncRec(Orc(RE.FunRO)).run : p = p0 /\ x = x0 ==>
          EncRec.hs = map (h0 RE.FunRO.f p0 x0) (iota_ 0 12)] = 1%r.
proof.
conseq (: true ==> true) (encrec_fun p0 x0) => //.
by proc; inline *; while true (12 - i); auto => /#.
qed.

local lemma decrec_fun_ph (p0 : pw) (y0 : state) :
  phoare [DecRec(Orc(RE.FunRO)).run : p = p0 /\ y = y0 ==>
          DecRec.hs = map (hb RE.FunRO.f p0 y0) (iota_ 0 12)] = 1%r.
proof.
conseq (: true ==> true) (decrec_fun p0 y0) => //.
by proc; inline *; while true (i + 1); auto => /#.
qed.

local lemma encrec_lazy (p0 : pw) (x0 : state) :
  hoare [EncRec(Ideal).run : p = p0 /\ x = x0 ==>
         fpath R.RO.m p0 x0 12 /\ EncRec.hs = map (h0 (tabf R.RO.m) p0 x0) (iota_ 0 12)].
proof.
proc.
while (0 <= i <= 12 /\ p = p0 /\ x = fwdp (tabf R.RO.m) p0 x0 0 i /\ fpath R.RO.m p0 x0 i /\
       EncRec.hs = map (h0 (tabf R.RO.m) p0 x0) (iota_ 0 i)).
- inline Orc(R.RO).b Orc(R.RO).a Orc(R.RO).h; wp.
  ecall (get_ext (PH (k, rd i, x.`2)) R.RO.m); wp.
  ecall (get_ext (PA (p, s)) R.RO.m); wp.
  ecall (get_ext (PB (rd i, x.`2)) R.RO.m); auto => /> &hr h0i _ hp hi12 m1 e1 b1 m2 e2 a2 m3 e3 h3.
  have := fpath_step R.RO.m{hr} m1 m2 m3 p0 x0 i{hr} h0i hp e1 e2 e3 b1 a2 h3.
  by move=> [-> [-> ->]] /=; smt().
auto => /> &hr; split; 1: by rewrite /fwdp !iota0 //= => t /#.
by move=> m i h1 h2 h3 h4; rewrite (_ : i = 12) 1:/#; move: h4; rewrite (_ : i = 12) 1:/#.
qed.

local lemma decrec_lazy (p0 : pw) (y0 : state) (m0 : (point, ans) fmap) :
  hoare [DecRec(Ideal).run : p = p0 /\ y = y0 /\ R.RO.m = m0 ==>
         ext m0 R.RO.m /\ bpath R.RO.m p0 y0 12 /\ DecRec.hs = map (hb (tabf R.RO.m) p0 y0) (iota_ 0 12)].
proof.
proc.
while (-1 <= i <= 11 /\ p = p0 /\ ext m0 R.RO.m /\ y = bwdp (tabf R.RO.m) p0 y0 11 (i + 1) /\
       bpath R.RO.m p0 y0 (11 - i) /\ DecRec.hs = map (hb (tabf R.RO.m) p0 y0) (iota_ 0 (11 - i))).
- inline Orc(R.RO).b Orc(R.RO).a Orc(R.RO).h; wp.
  ecall (get_ext (PH (k, rd i, y.`1)) R.RO.m); wp.
  ecall (get_ext (PA (p, s)) R.RO.m); wp.
  ecall (get_ext (PB (rd i, y.`1)) R.RO.m); auto => /> &hr hm1 hi11 he hp hi0 m1 e1 b1 m2 e2 a2 m3 e3 h3.
  have t0 : 0 <= 11 - i{hr} by smt().
  have r1 : 11 - (11 - i{hr}) = i{hr} by smt().
  have r2 : 12 - (11 - i{hr}) = i{hr} + 1 by smt().
  pose W := bwdp (tabf R.RO.m{hr}) p0 y0 11 (12 - (11 - i{hr})).
  have b1' : PB (rd (11 - (11 - i{hr})), W.`1) \in m1 by rewrite /W r1 r2.
  have a2' : PA (p0, salt_of (tabf m1 (PB (rd (11 - (11 - i{hr})), W.`1)))) \in m2 by rewrite /W r1 r2.
  have h3' : PH (key_of (tabf m2 (PA (p0, salt_of (tabf m1 (PB (rd (11 - (11 - i{hr})), W.`1)))))),
                 rd (11 - (11 - i{hr})), W.`1) \in m3 by rewrite /W r1 r2.
  have [q1 [q2 q3]] := bpath_step R.RO.m{hr} m1 m2 m3 p0 y0 (11 - i{hr}) t0 hp e1 e2 e3 b1' a2' h3'.
  move: q1 q2 q3; rewrite r1 r2 (_ : 12 - (11 - i{hr} + 1) = i{hr}) 1:/# => q1 q2 q3.
  smt(ext_trans).
auto => />; split; 1: by rewrite /bwdp !iota0 //= /bpath; smt().
by move=> m i h1 h2 h3 h4; rewrite (_ : 11 - i = 12) 1:/#.
qed.


(* The invariants at the end of the game, for the chains of the real password. *)
(* ---- Lemma K3 ------------------------------------------------------------------------------ *)
local lemma K3_e : 0 <= kA => 0 <= qB => 0 <= qH =>
  ehoare [KPL(A).main : ((24%r * p1 * kA%r + 2%r * qB%r + 287%r) * e128 + (2%r * qH%r + 12%r) * e256)%xr ==>
    (((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early) /\ !Fwd.odd /\ Count.ca <= kA /\ Count.cb <= qB /\
     Count.ch <= qH /\ Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p))%xr].
proof.
move=> hkA hqB hqH; proc.
conseq (_ : _ ==> (!Mon2.inrun /\ Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p)) `|`
                  (potF kA qB qH Count.ca Count.cb Count.ch Fwd.odd R.RO.m Fwd.p (Fwd.sts Fwd.p) (Bwd.sts Bwd.p))%xr).
- by move=> _; apply xle_cxr_l => // *; apply post_leK.
- by move=> &hr; apply xle_cxr_r => h; apply h.
call (dec_eK kA qB qH); call (enc_eK kA qB qH); wp.
conseq (_ : _ ==> (Mon2.inrun /\ (forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|`
                  (phiK kA qB qH Count.ca Count.cb Count.ch R.RO.m Fwd.sts Bwd.sts)%xr).
- by move=> _; apply xle_cxr_l => // *; apply run_decK.
- by move=> &hr; apply xle_cxr_r => h; apply h.
call (: (Mon2.inrun /\ (forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|`
        (phiK kA qB qH Count.ca Count.cb Count.ch R.RO.m Fwd.sts Bwd.sts)%xr ==>
        (Mon2.inrun /\ (forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|`
        (phiK kA qB qH Count.ca Count.cb Count.ch R.RO.m Fwd.sts Bwd.sts)%xr).
- proc ((Mon2.inrun /\ (forall w, shape false w (Fwd.sts w)) /\ (forall w, shape true w (Bwd.sts w))) `|`
        (phiK kA qB qH Count.ca Count.cb Count.ch R.RO.m Fwd.sts Bwd.sts)%xr).
  + by move=> &hr; apply xlexx.
  + by move=> &hr; apply xlexx.
  + exact (count_a_run kA qB qH).
  + exact (count_b_run kA qB qH).
  exact (count_h_run kA qB qH).
inline *; auto => &hr.
rewrite (eq_Ep _ _ (fun _ => ((24%r * p1 * kA%r + 2%r * qB%r + 287%r) * e128 + (2%r * qH%r + 12%r) * e256)%xr)).
- move=> y1 _ /=; rewrite (phiK_init _ _ _ _ _ hkA hqB hqH).
  have -> // : ((forall w, shape false w (cfwd x{hr})) /\ (forall w, shape true w (cbwd y1))) = true.
  by rewrite eqT; split => w; [apply shape_fwd | apply shape_bwd].
by rewrite EpC dstate_ll smul1m.
qed.

(* The budgets of a lossless adversary are nonnegative: it halts, and its counts never are. *)
local module GB = {
  proc main() : unit = { var o; Count(Mon2).init(); o <@ A(Count(Mon2)).guess(witness, witness); }
}.

local lemma ge0_budgets &m : 0 <= qB /\ 0 <= qH.
proof.
case: (0 <= qB /\ 0 <= qH) => // hneg.
have h1 : Pr[GB.main() @ &m : true] = 1%r.
- byphoare => //; proc; call (A_ll (Count(Mon2)) _ _ _); 1..3: by proc; inline *; auto; smt(dans_ll).
  by inline *; auto.
have h2 : Pr[GB.main() @ &m : !(0 <= qB /\ 0 <= qH)] = 0%r.
- byphoare => //; hoare; proc.
  call (_ : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 ==> 0 <= qB /\ 0 <= qH).
  + conseq (A_bounded Mon2) (_ : 0 <= Count.cb /\ 0 <= Count.ch ==> 0 <= Count.cb /\ 0 <= Count.ch) => [/# | /# |].
    by proc (0 <= Count.cb /\ 0 <= Count.ch) => //; proc; inline *; auto => /#.
  by inline *; auto.
have : Pr[GB.main() @ &m : !(0 <= qB /\ 0 <= qH)] = Pr[GB.main() @ &m : true] by rewrite Pr[mu_eq] => // /#.
smt().
qed.

local lemma counts_okK : hoare [KPGame(A).main : true ==> Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH].
proof.
proc; inline Net(Mon2).enc Net(Mon2).dec.
wp; while (Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH); 1: by inline *; auto.
wp; while (Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH); 1: by inline *; auto.
by wp; call (A_bounded Mon2); inline *; auto.
qed.

(* Lemma K3. *)
lemma K3 &m (x : state) : 0 <= kA =>
  Pr[KPGame(A).main(x) @ &m : (Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early] <=
    (24%r * p1 * kA%r + 2%r * qB%r + 287%r) / 2%r ^ 128 + (2%r * qH%r + 12%r) / 2%r ^ 256.
proof.
move=> hkA; have [hqB hqH] := ge0_budgets &m.
have h1 : Pr[KPGame(A).main(x) @ &m : !(!Fwd.odd /\ Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
            Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p))] = 0%r.
- byphoare => //; hoare; conseq (run_inv3 A) counts_okK => /> *; smt(inv_shape).
have h2 : Pr[KPGame(A).main(x) @ &m : ((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early) /\
            (!Fwd.odd /\ Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
             Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p))] <=
          (24%r * p1 * kA%r + 2%r * qB%r + 287%r) * e128 + (2%r * qH%r + 12%r) * e256.
- have -> : Pr[KPGame(A).main(x) @ &m : ((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early) /\
              (!Fwd.odd /\ Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
               Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p))] =
            Pr[KPL(A).main(x) @ &m : ((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early) /\
              (!Fwd.odd /\ Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
               Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p))].
  + by byequiv (kp_late A) => // /#.
  byehoare (_ : ((24%r * p1 * kA%r + 2%r * qB%r + 287%r) * e128 + (2%r * qH%r + 12%r) * e256)%xr ==> _) => //.
  + by conseq (K3_e hkA hqB hqH) => // &hr /#.
  by have := p1_ge0; have := e128_gt0; have := e256_gt0; smt().
rewrite Pr[mu_split (!Fwd.odd /\ Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
                     Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p))].
have h3 : Pr[KPGame(A).main(x) @ &m : ((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early) /\
            !(!Fwd.odd /\ Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
              Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p))] <=
          Pr[KPGame(A).main(x) @ &m : !(!Fwd.odd /\ Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
            Fwd.p = Bwd.p /\ shape false Fwd.p (Fwd.sts Fwd.p) /\ shape true Bwd.p (Bwd.sts Bwd.p))].
- by rewrite Pr[mu_sub] => // &hr [].
have -> : (24%r * p1 * kA%r + 2%r * qB%r + 287%r) / 2%r ^ 128 + (2%r * qH%r + 12%r) / 2%r ^ 256 =
          (24%r * p1 * kA%r + 2%r * qB%r + 287%r) * e128 + (2%r * qH%r + 12%r) * e256 by rewrite /e128 /e256.
smt().
qed.

(* ---- Averaging over the programmed round (the first line of (2)) ---------------------------- *)
(* Without Early, the chain points of rounds j and j + 1 are those of the final table's paths. *)
local lemma kp_chains : hoare [KPGame(A).main : true ==>
  (!(Fwd.sts Fwd.p).`early => forall j, 0 <= j <= 10 =>
     nth witness (Fwd.sts Fwd.p).`chain (3 * j + 2) = h0 (tabf R.RO.m) Fwd.p Fwd.x j) /\
  (!(Bwd.sts Bwd.p).`early => forall j, 0 <= j <= 10 =>
     nth witness (Bwd.sts Bwd.p).`chain (3 * (10 - j) + 2) = h1 (tabf R.RO.m) Bwd.p Bwd.y j)].
proof.
conseq (run_inv2 A) => _ _ p fs x bn log p' bs y m [_ [hif [hib [hff hfb]]]]; split => hea j hj.
- have [_ [_ [_ hne]]] := hif; have [_ [_ [_ [_ hdet]]]] := hne hea.
  by apply (fwd_chain _ _ _ _ j _ hdet (hff hea)); smt().
have [_ [_ [_ hne]]] := hib; have [_ [_ [_ [_ hdet]]]] := hne hea.
by apply (bwd_chain _ _ _ _ j hj hdet (hfb hea)).
qed.

local module KX4 = {
  var x : state
  var j : int
  var p : pw
  var y : state
  var hj : point
  var hj1 : point
}.

local module LG = { var log : point list }.

local module LogO (O : ABH) : ABH = {
  proc a(p : pw, s : W128.word) = { var k; LG.log <- rcons LG.log (PA (p, s)); k <@ O.a(p, s); return k; }
  proc b(i : ridx, x : W128.word) = { var s; LG.log <- rcons LG.log (PB (i, x)); s <@ O.b(i, x); return s; }
  proc h(k : W256.word, i : ridx, x : W128.word) = {
    var m; LG.log <- rcons LG.log (PH (k, i, x)); m <@ O.h(k, i, x); return m;
  }
}.

(* Δ1_j, with a log of the adversary's queries. *)
local module P1 (G : R.RO) = {
  proc distinguish() : bool = {
    var wj, wj2, sj, kj, sj1, kj1, r0, r1, g;
    KX4.p <$ dP; KX4.y <$ dstate;
    wj  <@ Part(Orc(G)).fwd(KX4.p, KX4.x, 0, KX4.j);
    wj2 <@ Part(Orc(G)).bwd(KX4.p, KX4.y, 11, KX4.j + 2);
    sj  <@ Orc(G).b(rd KX4.j, wj.`2);         kj  <@ Orc(G).a(KX4.p, sj);
    sj1 <@ Orc(G).b(rd (KX4.j + 1), wj2.`1);  kj1 <@ Orc(G).a(KX4.p, sj1);
    r0 <$ dans; r1 <$ dans;
    KX4.hj <- PH (kj, rd KX4.j, wj.`2); KX4.hj1 <- PH (kj1, rd (KX4.j + 1), wj2.`1);
    G.set(KX4.hj, with_mask r0 (wj2.`1 +^ wj.`1));
    G.set(KX4.hj1, with_mask r1 (wj2.`2 +^ wj.`2));
    Count(LogO(Orc(G))).init(); LG.log <- [];
    g <@ A(Count(LogO(Orc(G)))).guess(KX4.x, KX4.y);
    return g = KX4.p;
  }
}.

(* Δ2: no programming; Bad_j is a query at h_j or h_(j+1). *)
local module P2 (G : R.RO) = {
  proc distinguish() : bool = {
    var wj, wj2, sj, kj, sj1, kj1, g;
    KX4.p <$ dP; KX4.y <$ dstate;
    wj  <@ Part(Orc(G)).fwd(KX4.p, KX4.x, 0, KX4.j);
    wj2 <@ Part(Orc(G)).bwd(KX4.p, KX4.y, 11, KX4.j + 2);
    sj  <@ Orc(G).b(rd KX4.j, wj.`2);         kj  <@ Orc(G).a(KX4.p, sj);
    sj1 <@ Orc(G).b(rd (KX4.j + 1), wj2.`1);  kj1 <@ Orc(G).a(KX4.p, sj1);
    KX4.hj <- PH (kj, rd KX4.j, wj.`2); KX4.hj1 <- PH (kj1, rd (KX4.j + 1), wj2.`1);
    Count(LogO(Orc(G))).init(); LG.log <- [];
    g <@ A(Count(LogO(Orc(G)))).guess(KX4.x, KX4.y);
    return g = KX4.p \/ KX4.hj \in LG.log \/ KX4.hj1 \in LG.log;
  }
}.

(* Δ2 run lazily: the two points are evaluated after the run, by the forward and backward passes. *)
local module P3 (G : R.RO) = {
  proc distinguish() : bool = {
    var g, xf, xb;
    KX4.p <$ dP; KX4.y <$ dstate;
    Count(LogO(Orc(G))).init(); LG.log <- [];
    g <@ A(Count(LogO(Orc(G)))).guess(KX4.x, KX4.y);
    xf <@ EncRec(Orc(G)).run(KX4.p, KX4.x);
    xb <@ DecRec(Orc(G)).run(KX4.p, KX4.y);
    return g = KX4.p \/ nth witness EncRec.hs KX4.j \in LG.log \/ nth witness DecRec.hs (10 - KX4.j) \in LG.log;
  }
}.

local module V (D : R.RO_Distinguisher) (G : R.RO) = {
  proc main(x : state, j : int) : bool = {
    var b;
    KX4.x <- x; KX4.j <- j; KX4.p <- witness; KX4.y <- witness; KX4.hj <- witness; KX4.hj1 <- witness;
    LG.log <- []; Count.ca <- 0; Count.cb <- 0; Count.ch <- 0; EncRec.hs <- []; DecRec.hs <- [];
    b <@ R.MainD(D, G).distinguish();
    return b;
  }
}.

local equiv ea : Delta1(PlayK(A)).main ~ V(P1, R.RO).main : ={glob A, x, j} ==> ={res, glob A}.
proof.
proc; inline Setup1K.run R.MainD(P1, R.RO).distinguish P1(R.RO).distinguish PlayK(A, Count(Ideal)).play; wp.
call (_ : ={R.RO.m, Count.ca, Count.cb, Count.ch}).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
inline Count(Ideal).init Count(LogO(Orc(R.RO))).init R.RO.set; wp; rnd; rnd.
do 6! (call (_ : ={R.RO.m}); 1: by sim).
by inline *; auto.
qed.

local equiv eb1 : V(P1, R.RO).main ~ V(P1, RE.FunRO).main : ={glob A, x, j} ==> ={res, glob A}.
proof. by proc; call (RO_FunRO P1); auto. qed.

local equiv eb3 : V(P3, RE.FunRO).main ~ V(P3, R.RO).main : ={glob A, x, j} ==> ={res, glob A}.
proof. by proc; symmetry; call (RO_FunRO P3); auto. qed.

(* Δ1_j and Δ2 agree until the adversary queries h_j or h_(j+1). *)
local equiv ec : V(P1, RE.FunRO).main ~ V(P2, RE.FunRO).main : ={glob A, x, j} ==> res{1} => res{2}.
proof.
proc; inline R.MainD(P1, RE.FunRO).distinguish R.MainD(P2, RE.FunRO).distinguish
             P1(RE.FunRO).distinguish P2(RE.FunRO).distinguish; wp.
call (_ : KX4.hj \in LG.log \/ KX4.hj1 \in LG.log,
          ={Count.ca, Count.cb, Count.ch, LG.log, KX4.hj, KX4.hj1} /\
          (forall c, c <> KX4.hj{2} => c <> KX4.hj1{2} => RE.FunRO.f{1} c = RE.FunRO.f{2} c) /\
          (exists k i r, KX4.hj{2} = PH (k, i, r)) /\ (exists k i r, KX4.hj1{2} = PH (k, i, r))).
- exact A_ll.
- by proc; inline *; auto; smt(mem_rcons).
- by move=> *; proc; inline *; auto => />; smt(mem_rcons).
- by move=> *; proc; inline *; auto => />; smt(mem_rcons).
- by proc; inline *; auto; smt(mem_rcons).
- by move=> *; proc; inline *; auto => />; smt(mem_rcons).
- by move=> *; proc; inline *; auto => />; smt(mem_rcons).
- by proc; inline *; auto; smt(mem_rcons).
- by move=> *; proc; inline *; auto => />; smt(mem_rcons).
- by move=> *; proc; inline *; auto => />; smt(mem_rcons).
inline Count(LogO(Orc(RE.FunRO))).init RE.FunRO.set; wp; rnd{1}; rnd{1}.
do 6! (call (_ : ={RE.FunRO.f}); 1: by sim).
inline *; auto => />; smt(dans_ll).
qed.

(* Through the whole function, the two points are the same before and after the run. *)
local equiv ed : V(P2, RE.FunRO).main ~ V(P3, RE.FunRO).main :
  ={glob A, x, j} /\ 0 <= j{1} <= 10 ==> ={res}.
proof.
proc; inline R.MainD(P2, RE.FunRO).distinguish R.MainD(P3, RE.FunRO).distinguish
             P2(RE.FunRO).distinguish P3(RE.FunRO).distinguish; wp.
ecall{2} (decrec_fun_ph KX4.p{2} KX4.y{2}).
ecall{2} (encrec_fun_ph KX4.p{2} KX4.x{2}).
call (_ : ={RE.FunRO.f, Count.ca, Count.cb, Count.ch, LG.log}); 1..3: by sim.
inline Count(LogO(Orc(RE.FunRO))).init Orc(RE.FunRO).a Orc(RE.FunRO).b RE.FunRO.get; wp.
ecall{1} (bwd_fun_ph KX4.p{1} KX4.y{1} 11 (KX4.j{1} + 2)).
ecall{1} (fwd_fun_ph KX4.p{1} KX4.x{1} 0 KX4.j{1}).
inline *; auto => /> &2 hj0 hj1 f _ p _ y _.
split; 1: smt().
rewrite (nth_map 0) 1:size_iota 1:/# nth_iota 1:/# (nth_map 0) 1:size_iota 1:/# nth_iota 1:/# /=.
by rewrite hb_h1 /h0 /h1.
qed.

(* The lazy run records the H points of the final table's paths. *)
lemma v3_pure (m m0 : (point, ans) fmap) p x y j hs hs0 : 0 <= j <= 10 =>
  fpath m p x 12 => hs = map (h0 (tabf m) p x) (iota_ 0 12) =>
  ext m m0 => hs0 = map (hb (tabf m0) p y) (iota_ 0 12) =>
  nth witness hs j = h0 (tabf m0) p x j /\ nth witness hs0 (10 - j) = h1 (tabf m0) p y j.
proof.
move=> hj hf -> he ->; have [_ [eh _]] := fpath_ext m m0 p x 12 _ he hf; 1: done.
rewrite (nth_map 0) 1:size_iota 1:/# nth_iota 1:/# (nth_map 0) 1:size_iota 1:/# nth_iota 1:/# /=.
by rewrite hb_h1 eh 1:/#.
qed.

local lemma v3_facts (j0 : int) : hoare [V(P3, R.RO).main : j = j0 /\ 0 <= j0 <= 10 ==>
  KX4.j = j0 /\ nth witness EncRec.hs KX4.j = h0 (tabf R.RO.m) KX4.p KX4.x KX4.j /\
  nth witness DecRec.hs (10 - KX4.j) = h1 (tabf R.RO.m) KX4.p KX4.y KX4.j].
proof.
proc; inline R.MainD(P3, R.RO).distinguish P3(R.RO).distinguish; wp.
ecall (decrec_lazy KX4.p KX4.y R.RO.m).
ecall (encrec_lazy KX4.p KX4.x).
call (_ : true); 1..3: by proc; inline *; auto.
by inline *; auto => /> &hr hj0 hj1 *; smt(v3_pure).
qed.

(* The lazy Δ2 and the known-pair game make the same queries; the log is the adversary's. *)
local equiv e3k : V(P3, R.RO).main ~ KPGame(A).main : ={glob A, x} ==>
  R.RO.m{1} = R.RO.m{2} /\ KX4.p{1} = Fwd.p{2} /\ KX4.x{1} = Fwd.x{2} /\ KX4.y{1} = Bwd.y{2} /\
  Fwd.p{2} = Bwd.p{2} /\ LG.log{1} = map fst Mon2.log{2} /\
  res{1} = (KPGame.out{2} = Fwd.p{2} \/ nth witness EncRec.hs{1} KX4.j{1} \in LG.log{1} \/
            nth witness DecRec.hs{1} (10 - KX4.j{1}) \in LG.log{1}).
proof.
proc; inline R.MainD(P3, R.RO).distinguish P3(R.RO).distinguish; wp.
call (_ : ={arg, R.RO.m} /\ !Mon2.inrun{2} /\ LG.log{1} = map fst Mon2.log{2} ==>
          ={R.RO.m} /\ !Mon2.inrun{2} /\ LG.log{1} = map fst Mon2.log{2}).
- by proc; while (={i, y, p, R.RO.m} /\ !Mon2.inrun{2} /\ LG.log{1} = map fst Mon2.log{2}); inline *; auto.
call (_ : ={arg, R.RO.m} /\ !Mon2.inrun{2} /\ LG.log{1} = map fst Mon2.log{2} ==>
          ={R.RO.m} /\ !Mon2.inrun{2} /\ LG.log{1} = map fst Mon2.log{2}).
- by proc; while (={i, x, p, R.RO.m} /\ !Mon2.inrun{2} /\ LG.log{1} = map fst Mon2.log{2}); inline *; auto.
wp; call (_ : ={R.RO.m, Count.ca, Count.cb, Count.ch} /\ Mon2.inrun{2} /\ LG.log{1} = map fst Mon2.log{2}).
- by proc; inline *; auto => />; smt(map_rcons).
- by proc; inline *; auto => />; smt(map_rcons).
- by proc; inline *; auto => />; smt(map_rcons).
by inline *; auto.
qed.

(* For each programmed round j: Δ0 is won at most when Δ2 is won, or Bad_j or Early_P holds. *)
local lemma avg_j &m (x : state) (j0 : int) : 0 <= j0 <= 10 =>
  Pr[Delta0(PlayK(A)).main(x) @ &m : res] <=
  Pr[KPGame(A).main(x) @ &m : KPGame.out = Fwd.p \/ badj Mon2.log (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain j0 \/
                               (Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early].
proof.
move=> hj.
have -> : Pr[Delta0(PlayK(A)).main(x) @ &m : res] = Pr[Delta1(PlayK(A)).main(x, j0) @ &m : res].
- by byequiv (K1 (PlayK(A)) j0 hj).
have -> : Pr[Delta1(PlayK(A)).main(x, j0) @ &m : res] = Pr[V(P1, R.RO).main(x, j0) @ &m : res] by byequiv ea.
have -> : Pr[V(P1, R.RO).main(x, j0) @ &m : res] = Pr[V(P1, RE.FunRO).main(x, j0) @ &m : res] by byequiv eb1.
have h2 : Pr[V(P1, RE.FunRO).main(x, j0) @ &m : res] <= Pr[V(P2, RE.FunRO).main(x, j0) @ &m : res] by byequiv ec.
have h4 : Pr[V(P2, RE.FunRO).main(x, j0) @ &m : res] = Pr[V(P3, RE.FunRO).main(x, j0) @ &m : res].
- by byequiv ed => // /#.
have h5 : Pr[V(P3, RE.FunRO).main(x, j0) @ &m : res] = Pr[V(P3, R.RO).main(x, j0) @ &m : res] by byequiv eb3.
have h3 : Pr[V(P3, R.RO).main(x, j0) @ &m : res] <=
          Pr[KPGame(A).main(x) @ &m : KPGame.out = Fwd.p \/ badj Mon2.log (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain j0 \/
                                       (Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early].
- byequiv (_ : ={glob A, x} /\ j{1} = j0 ==> _) => //.
  conseq e3k (v3_facts j0) kp_chains; 1: smt().
  by move=> &1 &2 _ *; smt().
smt().
qed.

(* Averaging over the programmed round, the first line of (2); Early_P is charged once, by K3. *)
lemma averaging &m (x : state) :
  Pr[Delta0(PlayK(A)).main(x) @ &m : res] <=
    bigi predT (fun j => Pr[KPGame(A).main(x) @ &m :
      KPGame.out = Fwd.p \/ badj Mon2.log (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain j \/ (Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early]) 0 11
    / 11%r.
proof.
have h := StdBigop.Bigreal.ler_sum_seq predT (fun _ => Pr[Delta0(PlayK(A)).main(x) @ &m : res])
  (fun j => Pr[KPGame(A).main(x) @ &m : KPGame.out = Fwd.p \/ badj Mon2.log (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain j \/
                                         (Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early]) (range 0 11) _.
- by move=> j /mem_range hj _ /=; apply (avg_j &m x j); smt().
move: h; rewrite StdBigop.Bigreal.sumri_const //= => h.
by rewrite StdOrder.RealOrder.ler_pdivl_mulr // RField.mulrC.
qed.

(* ---- Theorem 4: (2) with the round drawn uniformly ------------------------------------------- *)
local module KPJ = {
  var jj : int
  proc main(x : state) : unit = { jj <$ [0..10]; KPGame(A).main(x); }
}.

local module KPJl = {
  proc main(x : state) : unit = { KPGame(A).main(x); KPJ.jj <$ [0..10]; }
}.

local lemma kp_jj (j0 : int) : hoare [KPGame(A).main : KPJ.jj = j0 ==> KPJ.jj = j0].
proof.
proc; inline Net(Mon2).enc Net(Mon2).dec.
wp; while (KPJ.jj = j0); 1: by inline *; auto.
wp; while (KPJ.jj = j0); 1: by inline *; auto.
wp; call (_ : KPJ.jj = j0); 1..3: by proc; inline *; auto.
by inline *; auto.
qed.

(* A lower bound for every round is a lower bound for a uniform round. *)
local lemma kpj_lb &m (x0 : state) (b : real) : 0%r <= b =>
  (forall j, 0 <= j <= 10 =>
     b <= Pr[KPGame(A).main(x0) @ &m : ev4 KPGame.out Fwd.p Mon2.log (Fwd.sts Fwd.p) (Bwd.sts Bwd.p) j]) =>
  b <= Pr[KPJ.main(x0) @ &m : ev4 KPGame.out Fwd.p Mon2.log (Fwd.sts Fwd.p) (Bwd.sts Bwd.p) KPJ.jj].
proof.
move=> hb0 hb; byphoare (_ : (glob A) = (glob A){m} /\ x = x0 ==> _) => //; proc.
seq 1 : (0 <= KPJ.jj <= 10) 1%r b 0%r 0%r ((glob A) = (glob A){m} /\ x = x0) => //.
- by auto.
- rnd; skip => /> *; rewrite (mu_eq_support _ _ predT) => [j /supp_dinter /# |].
  by rewrite (is_losslessP _ (dinter_ll 0 10 _)).
- exlim KPJ.jj => j0.
  call (_ : (glob A) = (glob A){m} /\ x = x0 /\ KPJ.jj = j0 /\ 0 <= j0 <= 10 ==>
            ev4 KPGame.out Fwd.p Mon2.log (Fwd.sts Fwd.p) (Bwd.sts Bwd.p) KPJ.jj); 2: by skip => /#.
  conseq (_ : (glob A) = (glob A){m} /\ x = x0 /\ KPJ.jj = j0 /\ 0 <= j0 <= 10 ==>
              ev4 KPGame.out Fwd.p Mon2.log (Fwd.sts Fwd.p) (Bwd.sts Bwd.p) j0) (kp_jj j0).
  + by move=> &hr [? [? [-> ?]]].
  + by move=> &hr [? [? [-> ?]]] p sts out log p0 sts0 [h ->].
  bypr => &m'; split => // -[hA [hx [hj hr]]].
  have -> : Pr[KPGame(A).main(arg{m'}) @ &m' : ev4 KPGame.out Fwd.p Mon2.log (Fwd.sts Fwd.p) (Bwd.sts Bwd.p) j0] =
            Pr[KPGame(A).main(x0) @ &m : ev4 KPGame.out Fwd.p Mon2.log (Fwd.sts Fwd.p) (Bwd.sts Bwd.p) j0].
  + by byequiv (_ : ={glob A, x} ==> ={KPGame.out, Fwd.p, Bwd.p, Mon2.log, Fwd.sts, Bwd.sts}) => //; proc; sim.
  by apply hb.
qed.

(* (2): Δ0 is won at most with the probability of the event of a uniform round. *)
local lemma avg_J &m (x0 : state) :
  Pr[Delta0(PlayK(A)).main(x0) @ &m : res] <=
  Pr[KPJ.main(x0) @ &m : ev4 KPGame.out Fwd.p Mon2.log (Fwd.sts Fwd.p) (Bwd.sts Bwd.p) KPJ.jj].
proof. by apply kpj_lb => [| j hj]; [smt(mu_bounded) | apply (avg_j &m x0 j hj)]. qed.

local lemma avg_Jl &m (x0 : state) :
  Pr[KPJ.main(x0) @ &m : ev4 KPGame.out Fwd.p Mon2.log (Fwd.sts Fwd.p) (Bwd.sts Bwd.p) KPJ.jj] =
  Pr[KPJl.main(x0) @ &m : ev4 KPGame.out Fwd.p Mon2.log (Fwd.sts Fwd.p) (Bwd.sts Bwd.p) KPJ.jj].
proof. by byequiv => //; proc; swap{1} 1 1; sim. qed.

local equiv eKK : KPGame(A).main ~ KPGame(A).main : ={glob A, x} ==>
  ={KPGame.out, Fwd.p, Bwd.p, Mon2.log, Fwd.sts, Bwd.sts} /\
  (!((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early) => !cross (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain =>
   nbad Mon2.log (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain <=
   min 11 (count (isApw Fwd.p) (undup (map fst Mon2.log)))){1}.
proof. by conseq (_ : ={glob A, x} ==> ={KPGame.out, Fwd.p, Bwd.p, Mon2.log, Fwd.sts, Bwd.sts}) (K4 A) => //; sim. qed.

(* The rounds of Bad are moved to the first n_bad places; by Lemma K4 these lie below N_P. *)
local equiv eB : KPJl.main ~ KPJl.main : ={glob A, x} ==>
  ev4 KPGame.out{1} Fwd.p{1} Mon2.log{1} (Fwd.sts Fwd.p){1} (Bwd.sts Bwd.p){1} KPJ.jj{1} =>
  (KPGame.out = Fwd.p \/ KPJ.jj < count (isApw Fwd.p) (undup (map fst Mon2.log)) \/
   (Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early \/
   (cross (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain /\ !((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early))){2}.
proof.
proc.
rnd (sig (badj Mon2.log (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain){1})
    (sigi (badj Mon2.log (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain){1}).
call eKK; auto => /> p' sts' out p sts log hK4.
pose B := badj log (sts p).`chain (sts' p').`chain.
split => [j /supp_dinter hj | _]; 1: by rewrite sigiK 1:/#.
split => [j /supp_dinter hj | _]; 1: by rewrite !dinter1E; smt(sigi_range).
move=> j /supp_dinter hj; split; 1: by apply/supp_dinter; smt(sig_range).
move=> _; split; 1: by rewrite sigK 1:/#.
move=> _; rewrite /ev4 => -[-> // | [hb | [-> // | -> //]]].
case: ((sts p).`early \/ (sts' p').`early) => [/#| he]; case: (cross (sts p).`chain (sts' p').`chain) => [/# | hc].
have := hK4 he hc; have := sig_bad B j _ hb; 1: smt().
by rewrite /nbad /range /B /=; smt().
qed.

(* ---- A late password and a late round ------------------------------------------------------ *)
local clone DProd.ProdSampling as PS with type t1 <- pw, type t2 <- int.

local module Fin2 = {
  proc run(out : pw, lg : (point * int) list) : bool = {
    var p, j;
    p <$ dP; j <$ [0..10];
    return out = p \/ j < count (isApw p) (undup (map fst lg));
  }
}.

local lemma fin2_pr &m (o : pw) (l : (point * int) list) : count isA (map fst l) <= kA =>
  Pr[Fin2.run(o, l) @ &m : res] <= ftop (1%r + kA%r / 11%r).
proof.
move=> hl.
have -> : Pr[Fin2.run(o, l) @ &m : res] =
          Pr[PS.S.sample2(dP, [0..10]) @ &m : o = res.`1 \/ res.`2 < count (isApw res.`1) (undup (map fst l))].
- by byequiv (_ : out{1} = o /\ lg{1} = l /\ d1{2} = dP /\ d2{2} = [0..10] ==>
                 res{1} = (o = res{2}.`1 \/ res{2}.`2 < count (isApw res{2}.`1) (undup (map fst l)))) => //;
     proc; auto.
have -> : Pr[PS.S.sample2(dP, [0..10]) @ &m : o = res.`1 \/ res.`2 < count (isApw res.`1) (undup (map fst l))] =
          Pr[PS.S.sample(dP, [0..10]) @ &m : o = res.`1 \/ res.`2 < count (isApw res.`1) (undup (map fst l))].
- by rewrite eq_sym; byequiv PS.sample_sample2.
have -> : Pr[PS.S.sample(dP, [0..10]) @ &m : o = res.`1 \/ res.`2 < count (isApw res.`1) (undup (map fst l))] =
          mu (dP `*` [0..10]) (fun (pj : pw * int) => o = pj.`1 \/ pj.`2 < count (isApw pj.`1) (undup (map fst l))).
- by byphoare (_ : d1 = dP /\ d2 = [0..10] ==> _) => //; proc; rnd; skip.
apply (late_guess o (fun w => count (isApw w) (undup (map fst l))) kA); 1: by move=> w; apply count_ge0.
by rewrite count_isApw; smt(count_undup_le).
qed.

(* The run, then a late password and a late round. *)
local module KPF = {
  proc main(x : state) : bool = {
    var y, b;
    R.RO.init(); Count(Mon2).init();
    y <$ dstate;
    Fwd.init(x); Bwd.init(y);
    Mon2.inrun <- true; Mon2.log <- []; Mon2.bn <- 0;
    KPGame.out <@ A(Count(Mon2)).guess(x, y);
    b <@ Fin2.run(KPGame.out, Mon2.log);
    return b;
  }
}.

local lemma log_cnt : hoare [A(Count(Mon2)).guess : Mon2.inrun /\ count isA (map fst Mon2.log) <= Count.ca ==>
                             count isA (map fst Mon2.log) <= Count.ca].
proof. by proc (Mon2.inrun /\ count isA (map fst Mon2.log) <= Count.ca) => //; proc; inline *; auto => />; smt(map_rcons count_rcons1). qed.

local lemma kpf_pr &m (x0 : state) : 0 <= kA => Pr[KPF.main(x0) @ &m : res] <= ftop (1%r + kA%r / 11%r).
proof.
move=> hkA; have hf : 0%r <= ftop (1%r + kA%r / 11%r).
- have := ftop_top (1%r + kA%r / 11%r) _; 1: smt(le_fromint).
  have : 0%r <= top (floor (1%r + kA%r / 11%r)) by rewrite /top; apply StdBigop.Bigreal.sumr_ge0 => i _; apply pr_ge0.
  smt().
byphoare (_ : x = x0 ==> _) => //; proc.
seq 9 : (count isA (map fst Mon2.log) <= kA) 1%r (ftop (1%r + kA%r / 11%r)) 0%r 0%r => //.
- call (_ : count isA (map fst lg) <= kA ==> res); 2: by skip.
  bypr => &m'; split; 1: exact hf.
  by move=> hc; apply (fin2_pr &m' out{m'} lg{m'} hc).
hoare; call (_ : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ Mon2.inrun /\ count isA (map fst Mon2.log) <= Count.ca ==>
                 count isA (map fst Mon2.log) <= kA).
- by conseq (A_bounded Mon2) log_cnt => /#.
by inline *; auto.
qed.

local lemma enc_keep (l0 : (point * int) list) :
  phoare [Net(Mon2).enc : !Mon2.inrun /\ Mon2.log = l0 ==> !Mon2.inrun /\ Mon2.log = l0] = 1%r.
proof. by proc; while (!Mon2.inrun /\ Mon2.log = l0) (12 - i); [move=> z; inline *; auto => />; smt(dans_ll) | auto => /#]. qed.

local lemma dec_keep (l0 : (point * int) list) :
  phoare [Net(Mon2).dec : !Mon2.inrun /\ Mon2.log = l0 ==> !Mon2.inrun /\ Mon2.log = l0] = 1%r.
proof. by proc; while (!Mon2.inrun /\ Mon2.log = l0) (i + 1); [move=> z; inline *; auto => />; smt(dans_ll) | auto => /#]. qed.

local equiv eF : KPJl.main ~ KPF.main : ={glob A, x} ==>
  (KPGame.out = Fwd.p \/ KPJ.jj < count (isApw Fwd.p) (undup (map fst Mon2.log))){1} = res{2}.
proof.
proc; inline KPGame(A).main Fin2.run; wp.
swap{1} 4 7; rnd; wp.
ecall{1} (dec_keep Mon2.log{1}); ecall{1} (enc_keep Mon2.log{1}).
wp; rnd; wp.
call (_ : ={R.RO.m, Count.ca, Count.cb, Count.ch, Mon2.inrun, Mon2.log, Mon2.bn, Fwd.sts, Bwd.sts}); 1..3: by sim.
by inline *; auto => />.
qed.

(* Theorem 4, with the fractional top and its coarse consequence. *)
lemma theorem4 &m (x : state) : 0 <= kA =>
  Pr[Delta0(PlayK(A)).main(x) @ &m : res] <= ftop (1%r + kA%r / 11%r) + epsK kA qB qH.
proof.
move=> hkA.
have h1 := avg_J &m x; rewrite avg_Jl in h1.
have h2 : Pr[KPJl.main(x) @ &m : ev4 KPGame.out Fwd.p Mon2.log (Fwd.sts Fwd.p) (Bwd.sts Bwd.p) KPJ.jj] <=
          Pr[KPJl.main(x) @ &m : (KPGame.out = Fwd.p \/ KPJ.jj < count (isApw Fwd.p) (undup (map fst Mon2.log))) \/
                                 ((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early) \/
                                 (cross (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain /\
                                  !((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early))].
- by byequiv eB => // /#.
have o1 : Pr[KPJl.main(x) @ &m : (KPGame.out = Fwd.p \/ KPJ.jj < count (isApw Fwd.p) (undup (map fst Mon2.log))) \/
                                 ((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early) \/
                                 (cross (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain /\
                                  !((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early))] <=
          Pr[KPJl.main(x) @ &m : KPGame.out = Fwd.p \/ KPJ.jj < count (isApw Fwd.p) (undup (map fst Mon2.log))] +
          Pr[KPJl.main(x) @ &m : ((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early) \/
                                 (cross (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain /\
                                  !((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early))].
- by rewrite Pr[mu_or]; smt(mu_bounded).
have o2 : Pr[KPJl.main(x) @ &m : ((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early) \/
                                 (cross (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain /\
                                  !((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early))] <=
          Pr[KPJl.main(x) @ &m : (Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early] +
          Pr[KPJl.main(x) @ &m : cross (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain /\
                                 !((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early)].
- by rewrite Pr[mu_or]; smt(mu_bounded).
have h3 : Pr[KPJl.main(x) @ &m : KPGame.out = Fwd.p \/ KPJ.jj < count (isApw Fwd.p) (undup (map fst Mon2.log))] =
          Pr[KPF.main(x) @ &m : res] by byequiv eF.
have h4 := kpf_pr &m x hkA.
have h5 : Pr[KPJl.main(x) @ &m : (Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early] =
          Pr[KPGame(A).main(x) @ &m : (Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early].
- byequiv => //; proc *; inline{1} KPJl.main; rnd{1}; wp.
  call (_ : ={glob A, x} ==> ={Fwd.p, Bwd.p, Fwd.sts, Bwd.sts}); 1: by proc; sim.
  by auto => />; apply dinter_ll.
have h6 : Pr[KPJl.main(x) @ &m : cross (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain /\
                                 !((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early)] =
          Pr[KPGame(A).main(x) @ &m : cross (Fwd.sts Fwd.p).`chain (Bwd.sts Bwd.p).`chain /\
                                      !((Fwd.sts Fwd.p).`early \/ (Bwd.sts Bwd.p).`early)].
- byequiv => //; proc *; inline{1} KPJl.main; rnd{1}; wp.
  call (_ : ={glob A, x} ==> ={Fwd.p, Bwd.p, Fwd.sts, Bwd.sts}); 1: by proc; sim.
  by auto => />; apply dinter_ll.
have h7 := K3 &m x hkA; have h8 := K2_cross A &m x.
rewrite /epsK; smt(mu_bounded).
qed.

lemma theorem4_coarse &m (x : state) : 0 <= kA =>
  Pr[Delta0(PlayK(A)).main(x) @ &m : res] <= top (kA %/ 11 + 2) + epsK kA qB qH.
proof.
move=> hkA; have := theorem4 &m x hkA.
have [_ h] := ftop_top (1%r + kA%r / 11%r) _; 1: smt(le_fromint).
have hc : ceil (1%r + kA%r / 11%r) <= kA %/ 11 + 2.
- have := ceil_lt (1%r + kA%r / 11%r); have := divz_eq kA 11; smt(modz_ge0 ltz_pmod le_fromint).
have := top_mono _ _ hc; smt().
qed.

end section Theorem4.

(* Δ0 with creation refusal: the continuation after a refused first attempt is arbitrary. *)
module type AFTERK = { proc run(p : pw, x : state, y : state) : bool }.

module Delta0R (C : PLAYK) (Rf : AFTERK) = {
  proc main(x : state) : bool = {
    var p, y, b;
    (p, y) <@ Setup0K.run(x);
    if (y = x) {
      b <@ Rf.run(p, x, y);
    } else {
      Count(Ideal).init();
      b <@ C(Count(Ideal)).play(p, x, y);
    }
    return b;
  }
}.

section RefusalK.
declare module C <: PLAYK {-R.RO, -Count}.
declare module Rf <: AFTERK.
declare axiom C_ll (O <: ABH {-C}) :
  islossless O.a => islossless O.b => islossless O.h => islossless C(O).play.
declare axiom Rf_ll : islossless Rf.run.

local lemma Ideal_ll : islossless Count(Ideal).a /\ islossless Count(Ideal).b /\ islossless Count(Ideal).h.
proof. by do! split; proc; inline *; auto => />; smt(dans_ll). qed.

local lemma play_ll : islossless C(Count(Ideal)).play.
proof. by have [? [? ?]] := Ideal_ll; apply (C_ll (Count(Ideal))). qed.

local module FlagK = { var r : bool }.

local module Delta0F = {
  proc main(x : state) : bool = {
    var p, y, b;
    (p, y) <@ Setup0K.run(x);
    FlagK.r <- y = x;
    Count(Ideal).init();
    b <@ C(Count(Ideal)).play(p, x, y);
    return b;
  }
}.

(* The first attempt of Δ0 alone. *)
local module TK = {
  proc main(x : state) : bool = {
    var p, y;
    R.RO.init();
    p <$ dP;
    y <@ Net(Ideal).enc(p, x);
    return y = x;
  }
}.

local lemma TK_pr &m (x0 : state) : Pr[TK.main(x0) @ &m : res] = inv (2%r ^ 256).
proof.
byphoare (_ : x = x0 ==> res) => //; proc.
seq 2 : (R.RO.m = empty /\ x = x0) 1%r (inv (2%r ^ 256)) 0%r _ => //.
- by inline *; auto => />; smt(dP_ll).
- exlim p, x => p1 x1.
  have := enc_uniform_ph p1 x1 x1; rewrite dstate1_256 => h.
  by call h; auto => />; smt(mem_empty).
by hoare; inline *; auto.
qed.

(* Theorem 4 and every other game on Δ0 hold with refusal after adding 2^-256. *)
lemma refusalK &m (x : state) :
  Pr[Delta0R(C, Rf).main(x) @ &m : res] <= Pr[Delta0(C).main(x) @ &m : res] + inv (2%r ^ 256).
proof.
have h1 : Pr[Delta0R(C, Rf).main(x) @ &m : res] <= Pr[Delta0F.main(x) @ &m : res \/ FlagK.r].
- byequiv => //; proc.
  seq 1 1 : (={p, y, x, glob C, R.RO.m}); 1: by sim.
  if{1}.
  + wp; call{2} play_ll; call{1} Rf_ll; inline *; auto => />.
  by sim : (={b}) => /> /#.
have h2 : Pr[Delta0F.main(x) @ &m : FlagK.r] = Pr[TK.main(x) @ &m : res].
- byequiv => //; proc; inline Setup0K.run.
  call{1} play_ll; inline Count(Ideal).init; wp.
  by sim.
have h3 : Pr[Delta0F.main(x) @ &m : res] = Pr[Delta0(C).main(x) @ &m : res].
- by byequiv => //; proc; sim.
have h4 : Pr[Delta0F.main(x) @ &m : res \/ FlagK.r] <=
          Pr[Delta0F.main(x) @ &m : res] + Pr[Delta0F.main(x) @ &m : FlagK.r].
- rewrite Pr [mu_or].
  have : 0%r <= Pr[Delta0F.main(x) @ &m : res /\ FlagK.r] by rewrite Pr[mu_ge0].
  smt().
smt(TK_pr).
qed.
end section RefusalK.
