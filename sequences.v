(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import ssralg ssrnum fintype bigop matrix interval.
Require Import boolp reals Rstruct Rbar.
Require Import classical_sets posnum topology hierarchy landau forms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.

(* scratch file *)

(* NB(rei): lemma available in the branch uniform-entourages *)
Lemma bigmaxrD1 (I : finType) j (P : pred I) (F : I -> R) x :
  P j -> \big[maxr/x]_(i | P i) F i
    = maxr (F j) (\big[maxr/x]_(i | P i && (i != j)) F i).
Proof.
Admitted.

Lemma ler_bigmax_cond (I : finType) (P : pred I) (F : _ -> R) i0 :
  P i0 -> (forall x, 0 <= F x) -> F i0 <= \big[Num.max/0]_(i | P i) F i.
Proof. by move=> Pi0 F0; rewrite (@bigmaxrD1 _ i0) //= ler_maxr lerr. Qed.

(* TODO: move *)
Lemma squeeze (T : Type) (f g h : T -> R) (a : filter_on T) :
  (\forall x \near a, f x <= g x <= h x) -> forall (l : R),
  f @ a --> l -> h @ a --> l -> g @ a --> l.
Proof.
move=> afgh l fal hal; apply/flim_locally => _/posnumP[/= e].
rewrite near_map; near=> x.
rewrite /ball /= /AbsRing_ball /= ltr_norml; apply/andP; split.
- rewrite ltr_oppl opprB (@ler_lt_trans _ (h x - l)) //.
  + rewrite ler_sub //.
    by have /(_ _) /andP[//|_ ->] := near afgh x.
  + rewrite (@ler_lt_trans _ `|h x - l|) // ?real_ler_norm // ?num_real // distrC.
    near: x.
    move/flim_locally : hal => /(_ e%:num (posnum_gt0 e)).
    by rewrite near_map.
- rewrite (@ler_lt_trans _ (l - f x)) //.
  + rewrite ler_sub //.
    by have /(_ _) /andP[|] := near afgh x.
  + rewrite (@ler_lt_trans _ `|l - f x|) // ?real_ler_norm // ?num_real //.
    near: x.
    move/flim_locally : fal => /(_ e%:num (posnum_gt0 e)).
    by rewrite near_map.
Grab Existential Variables. all: end_near. Qed.

Definition sequence R := nat -> R.
Notation "R ^nat" := (sequence R) (at level 0).

Section sequences.

Canonical eventually_filter := FilterType eventually _.
Canonical eventually_pfilter := PFilterType eventually (filter_not_empty _).
Notation eqolimn := (@eqolim _ _ _ (eventually_filter)).
Notation eqolimPn := (@eqolimP _ _ _ (eventually_filter)).

Lemma lim_opp_sequence (u_ : (R^o) ^nat) : cvg u_ ->
  lim (- u_) = - lim u_.
Proof. by move=> u_cv; apply/flim_map_lim/lim_opp. Qed.

Lemma cvg_opp (u_ : (R^o) ^nat) : cvg (- u_) = cvg u_.
Proof.
rewrite propeqE.
split; case/cvg_ex => /= l ul; apply/cvg_ex; exists (- l); last exact/lim_opp.
move/lim_opp : ul => /subset_trans; apply.
by rewrite (_ : (fun x : nat => _) = u_) // funeqE => ?; rewrite opprK.
Qed.

Lemma lim_add_sequence (u_ v_ : (R^o) ^nat) : cvg u_ -> cvg v_ ->
  lim (u_ + v_) = lim u_ + lim v_.
Proof. by move=> u_cv v_cv; apply/flim_map_lim/lim_add. Qed.

Lemma cvg_add (u_ v_ : nat -> R^o) : cvg u_ -> cvg v_ -> cvg (u_ + v_).
Proof.
move=> /cvg_ex[l ul] /cvg_ex[l' vl']; apply/cvg_ex; exists (l + l').
apply/flim_normP => _/posnumP[e]; rewrite near_map; near=> n.
rewrite opprD addrACA (splitr e%:num) (ler_lt_trans (ler_normm_add _ _)) //.
by rewrite ltr_add //; near: n; [move: ul | move: vl'] => /flim_normP; apply.
Grab Existential Variables. all: end_near. Qed.

Lemma addo' (K : absRingType) (T : Type) (V W : normedModType K) (F : filter_on T)
  (f g : T -> V) (e : T -> W) (F' := unkeyed F) :
  [o_F e of f] + [o_F' e of g] =o_F e.
Proof. exact: addo. Qed.

Lemma lim_add3sequence (u_ v_ w_ : (R^o) ^nat) : cvg u_ -> cvg v_ -> cvg w_ ->
  lim (u_ + v_ + w_) = lim u_ + lim v_ +  lim w_.
Proof.
move=> /eqolimPn u_cv /eqolimPn v_cv /eqolimPn w_cv.
apply/flim_map_lim.
apply: eqolimn.
rewrite [in LHS]u_cv /= [in LHS]v_cv /= [in LHS]w_cv.
rewrite addrACA -!addrA.
(* rewrite showo. *)
rewrite addo'.
(* rewrite showo. *)
rewrite [cst _ + (cst _ + _)]addrA addrA.
rewrite addrACA !addrA -addrA.
rewrite [X in X + _]addrAC.
congr (_ + _ + _ + _).
rewrite addo'.
done.
Qed.

Lemma dvgP (u_ : (R^o) ^nat) : u_ --> +oo <-> forall A : posreal, \forall n \near \oo, A <= u_ n.
Proof.
split.
  move=> ulim A; rewrite -(near_map u_ \oo (<=%R A)).
  by apply: ulim; apply: locally_pinfty_ge.
move=> /(_ (PosNum _)) u_ge X [A AX].
rewrite near_simpl [\forall x \near _, X x](near_map u_ \oo).
near=> x.
apply: AX; rewrite (@ltr_le_trans _ ((maxr 0 A) +1)) //.
  by rewrite ltr_spaddr// ler_maxr lerr orbT.
by near: x; apply: u_ge; rewrite ltr_spaddr// ler_maxr lerr.
Grab Existential Variables. all: end_near. Qed.

Lemma cvg_bound (u_ : (R^o) ^nat) : cvg u_ -> exists M, forall n, `|u_ n| <= M.
Proof.
move=> cu; set l := lim u_.
have [n _ nu] : \forall n \near \oo, `|u_ n| <= 1 + `|l|.
  have : \forall n \near \oo, `|l - u_ n| < 1 by move/flim_normP : cu; apply.
  apply: filter_app; near=> n; move=> lu1; apply/ltrW.
  rewrite -ltr_sub_addr (ler_lt_trans _ lu1) // absrB.
  by rewrite (ler_trans _ (ler_distm_dist (u_ n) l)) // ler_norm.
near \oo => N.
exists (Num.max (\big[maxr/0]_(0 <= i < N.+1) `|u_ i|) (1 + `|l|)) => p.
rewrite ler_maxr.
case/boolP : (p <= N)%nat => [|].
  rewrite -ltnS => nN.
  by rewrite big_mkord (@ler_bigmax_cond _ _ _ (Ordinal nN)).
rewrite -ltnNge => Nn.
apply/orP; right; apply/nu/ltnW/(leq_ltn_trans _ Nn).
by near: N; exists n.
Grab Existential Variables. all: end_near. Qed.

Lemma squeeze_sequence (u_ v_ w_ : (R^o) ^nat) l :
  (\forall n \near \oo, u_ n <= v_ n <= w_ n) ->
  cvg u_ -> lim u_ = l ->
  cvg w_ -> lim w_ = l ->
  cvg v_ /\ lim v_ = l.
Proof.
move=> uvw cvgu ul cvgw wl.
suff vol : v_ @ \oo --> l.
  by split; [exact/(@cvgP _ _ (v_ @ \oo) l) | exact/flim_map_lim].
apply: (@squeeze _ _ _ _ _ uvw l).
- case/cvg_ex : cvgu => /= x ux; by rewrite -ul (flim_lim ux).
- case/cvg_ex : cvgw => /= x wx; by rewrite -wl (flim_lim wx).
Qed.

Lemma dvg_seq (u_ v_ : (R^o) ^nat) : (\forall n \near \oo, u_ n <= v_ n) ->
  u_ --> +oo -> v_ --> +oo.
Proof.
move=> uv.
move/dvgP => dvgu.
apply/dvgP => A.
near=> n.
have uA := dvgu A.
rewrite (@ler_trans _ (u_ n)) //; by near: n.
Grab Existential Variables. all: end_near. Qed.

Definition increasing (u_ : (R^o) ^nat) := forall n, u_ n <= u_ n.+1.

Lemma increasing_ler (u_ : (R^o) ^nat) : increasing u_ ->
  forall n m, (n <= m)%nat -> u_ n <= u_ m.
Proof.
move=> iu n; elim=> [|m ih]; first by rewrite leqn0 => /eqP ->; exact/lerr.
rewrite leq_eqVlt => /orP[/eqP <-|]; first exact/lerr.
rewrite ltnS => /ih/ler_trans; apply; apply iu.
Qed.

Lemma lim_ge0 (u_ : (R^o) ^nat) : (forall n, 0 <= u_ n) -> cvg u_ -> 0 <= lim u_.
Proof.
move=> H /flim_normP cu.
rewrite lerNgt; apply/negP => u0.
have /cu : 0 < `|[ lim u_ ]|.
  by rewrite -normmN normm_gt0 eqr_oppLR ltr_eqF // oppr0.
rewrite near_map => -[N _ K].
near \oo => m.
move: (K m).
rewrite ltrNge => Km.
suff /Km/negP : (N <= m)%nat.
  apply.
  rewrite normmB -normmN (@ler_trans _ `|- lim u_|%R) //.
  rewrite ger0_norm ?oppr_ge0; last exact/ltrW.
  rewrite (@ler_trans _ `|u_ m - lim u_|%R)// ger0_norm.
  by rewrite ler_subr_addr addrC subrr; apply/H.
  by rewrite subr_ge0 (@ler_trans _ 0) // ltrW.
near: m.
by exists N.
Grab Existential Variables. all: end_near. Qed.

Lemma lim_ler (u_ v_ : (R^o) ^nat) : (forall n, u_ n <= v_ n) ->
  cvg u_ -> cvg v_ -> lim u_ <= lim v_.
Proof.
move=> uv cu cv.
rewrite -subr_ge0 -lim_opp_sequence // -lim_add_sequence // ?cvg_opp //.
apply lim_ge0 => //; first by move=> ?; rewrite subr_ge0.
apply/cvg_add => //; by rewrite cvg_opp.
Qed.

Lemma increasing_bound_cvg (u_ : (R^o) ^nat) N : increasing u_ ->
  (forall n, u_ n <= N) -> cvg u_.
Proof.
move=> iu uN.
set S := fun x => `[< exists n, u_ n = x >].
set l := real_sup S.
have supS : has_sup S.
  apply/has_supP; split; first by exists (u_ O); rewrite in_setE; exists O.
  exists N; rewrite in_setE => /= x.
  rewrite negb_imply; apply propF => /andP[].
  rewrite in_setE => -[m] <-{x}; rewrite -ltrNge.
  by move: (uN m) => /ler_lt_trans H/H; rewrite ltrr.
move: (real_sup_ub supS); rewrite -is_upper_boundE /is_upper_bound => ubS.
apply/cvg_ex; exists l.
apply/flim_normW => _/posnumP[e]; rewrite near_map.
have [m um] : exists m, l - e%:num <= u_ m <= l.
  case: (sup_adherent supS (posnum_gt0 e)) => uns.
  rewrite in_setE => -[p] <-{uns} => supep.
  exists p; rewrite ltrW //=.
  have /ubS : S (u_ p) by apply/asboolP; exists p.
  by move/RleP.
near=> p.
rewrite normmB ler_norml -(ler_add2l l) addrCA subrr addr0.
(* NB: ler_add2r defined with {mono notation} vs. ltr_add2r (defined as an equality) *)
rewrite -[in X in _ && X](ler_add2r l) subrK; apply/andP; split; last first.
  rewrite (@ler_trans _ l) // ?ler_addr //.
  have /ubS : S (u_ p) by apply/asboolP; exists p.
  by move/RleP.
case/andP : um => /ler_trans um _; rewrite um //.
suff : (m <= p)%nat by move/increasing_ler; exact.
near: p.
rewrite nearE; by exists m.
Grab Existential Variables. all: end_near. Qed.

Definition cauchy_seq (u_ : (R^o) ^nat) :=
  forall eps : posreal, \forall n \near (\oo, \oo), `|[ u_ n.1 - u_ n.2 ]| <= eps.

Lemma cvg_cauchy_seq (u_ : (R^o) ^nat) : cvg u_ -> cauchy_seq u_.
Proof.
move/flim_normP => H e; near=> n.
rewrite -(addrK (- lim u_) (u_ n.1)) opprK -addrA.
rewrite (ler_trans (ler_normm_add _ _)) // (splitr e%:num) ltrW //.
rewrite ltr_add //; near: n; apply: filter_pair_near_of => /= x y xoo yoo.
rewrite normmB; near: x; exact: H.
near: y; exact: H.
Grab Existential Variables. all: end_near. Qed.

End sequences.

Require Import derive.

Section rewriting_differential.

Let running_example (f g h : R^o -> R^o) x :
 derivable f x 1 -> derivable g x 1 -> derivable h x 1 ->
 is_derive x 1 (f + g * h) (f^`() x + g^`() x * h x + g x * h^`() x).
Proof.
move=> /derivableP Hf /derivableP Hg /derivableP Hh.
apply: is_derive_eq.
rewrite addrAC (mulrC _ (h x)) -addrA.
by rewrite !derive1E.
Qed.

Definition f0 (g : R^o -> R^o) (x : R^o) : R^o -> R^o := fun y => g (y - x).

Lemma diff_subproof (g : {linear R^o -> R^o}) (x : R^o) : continuous g ->
  is_diff x (f0 g x) g.
Proof.
move=> cg.
set F0 := f0 g x.
suff H : forall h : R^o, F0 (h + x) = F0 x + g h +o_(h \near 0 : R^o) h.
  have df0 : 'd F0 x = g :> (R^o -> R^o).
    apply diff_unique => //.
    by rewrite funeqE.
  apply: DiffDef => //.
  apply/diff_locallyxP; split => /=; first by rewrite df0.
  by move=> h; rewrite H df0.
apply: eqaddoEx => h.
rewrite /F0 /f0 addrK subrr linear0 add0r.
apply/eqP; rewrite addrC -subr_eq subrr; apply/eqP.
rewrite littleoE; last exact: littleo0_subproof.
by [].
Qed.

Local Notation "[ 'd' x = g # p ]" := (projT1 (existT (fun f => is_diff x f g) _ p))
  (at level 0, x at next level, format "[ 'd'  x  =  g  #  p ]").

Section diff_type.
Context {K : absRingType} {V W : normedModType K}.
Structure diff_type (diff : V -> W) x := DiffType {
  diff_fun : V -> W ;
  _ : is_diff x diff_fun diff }.
End diff_type.

End rewriting_differential.
