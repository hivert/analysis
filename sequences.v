(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import ssralg ssrnum fintype bigop binomial matrix.
From mathcomp Require Import interval.
Require Import boolp reals Rstruct Rbar.
Require Import classical_sets posnum topology normedtype landau forms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.

(* wip
   tentative formalization of sequences
   started 2019-02-21 Thu *)

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

Section nat_topologicalTypeMixin.
Let D : set nat := setT.
Let b : nat -> set nat := fun i => [set i].
Let bT : \bigcup_(i in D) b i = setT.
Proof. by rewrite funeqE => i; rewrite propeqE; split => // _; exists i. Qed.
Let bD : forall i j t, D i -> D j -> b i t -> b j t ->
  exists k, D k /\ b k t /\ b k `<=` b i `&` b j.
Proof. by move=> i j t _ _ ->{t} ->{i}; exists j. Qed.
Definition nat_topologicalTypeMixin := topologyOfBaseMixin bT bD.
Canonical nat_topologicalType := Topological.Pack
  (@Topological.Class _
                      (Filtered.Class (Pointed.class nat_pointedType) _)
                      nat_topologicalTypeMixin)
  unit.
End nat_topologicalTypeMixin.

Definition sequence R := nat -> R.
Notation "R ^nat" := (sequence R) (at level 0).

Canonical eventually_filter := FilterType eventually _.
Canonical eventually_pfilter := PFilterType eventually (filter_not_empty _).
Notation eqolimn := (@eqolim _ _ _ eventually_filter).
Notation eqolimPn := (@eqolimP _ _ _ eventually_filter).

Section sequences.

Lemma lim_opp_sequence (u_ : (R^o) ^nat) : cvg u_ -> lim (- u_) = - lim u_.
Proof.
move=> u_cv; apply/flim_map_lim.
exact: (@lim_opp _ _ nat_topologicalType).
Qed.

Lemma lim_add_sequence (u_ v_ : (R^o) ^nat) : cvg u_ -> cvg v_ ->
  lim (u_ + v_) = lim u_ + lim v_.
Proof.
by move=> u_cv v_cv; apply/flim_map_lim/(@lim_add _ _ nat_topologicalType).
Qed.

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

Lemma cvg_opp (u_ : (R^o) ^nat) : cvg (- u_) = cvg u_.
Proof.
rewrite propeqE.
split; case/cvg_ex => /= l ul; apply/cvg_ex; exists (- l); last first.
  exact: (@lim_opp _ _ nat_topologicalType).
move/(@lim_opp _ _ nat_topologicalType) : ul => /subset_trans; apply.
by rewrite (_ : (fun x : nat => _) = u_) // funeqE => ?; rewrite opprK.
Qed.

Lemma cvg_cst (k : R^o) : cvg (fun _ : nat => k).
Proof.
move=> /= s; rewrite (_ : lim _ = k); last exact/flim_lim/flim_const.
move/locally_normP => [_/posnumP[/= e]] kes.
by exists O => // i _; exact/kes/ball_norm_center.
Qed.

Lemma cvg_add (u_ v_ : nat -> R^o) : cvg u_ -> cvg v_ -> cvg (u_ + v_).
Proof.
move=> /cvg_ex[l ul] /cvg_ex[l' vl']; apply/cvg_ex; exists (l + l').
apply/flim_normP => _/posnumP[e]; rewrite near_map; near=> n.
rewrite opprD addrACA (splitr e%:num) (ler_lt_trans (ler_normm_add _ _)) //.
by rewrite ltr_add //; near: n; [move: ul | move: vl'] => /flim_normP; apply.
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

Lemma lim_ge0 (u_ : (R^o) ^nat) N :
  (forall n, (N <= n)%nat -> 0 <= u_ n) -> cvg u_ -> 0 <= lim u_.
Proof.
move=> H /flim_normP cu.
rewrite lerNgt; apply/negP => u0.
have /cu : 0 < `|[ lim u_ ]|.
  by rewrite -normmN normm_gt0 eqr_oppLR ltr_eqF // oppr0.
rewrite near_map => -[M _ K].
near \oo => m.
have /K : (M <= m)%nat by near: m; exists M.
apply/negP; rewrite -lerNgt normmB -normmN (@ler_trans _ `|- lim u_|%R) //.
rewrite ger0_norm ?oppr_ge0; last exact/ltrW.
rewrite (@ler_trans _ `|u_ m - lim u_|%R)// ger0_norm.
  rewrite ler_subr_addr addrC subrr; apply/H.
  by near: m; exists N.
rewrite subr_ge0 (@ler_trans _ 0) //; first by rewrite ltrW.
by apply H; near: m; exists N.
Grab Existential Variables. all: end_near. Qed.

Lemma lim_ler (u_ v_ : (R^o) ^nat) N :
  (forall n : nat, (N <= n)%nat -> u_ n <= v_ n) ->
  cvg u_ -> cvg v_ -> lim u_ <= lim v_.
Proof.
move=> uv cu cv.
rewrite -subr_ge0 -lim_opp_sequence // -lim_add_sequence // ?cvg_opp //.
apply (@lim_ge0 _ N); last by apply/cvg_add => //; rewrite cvg_opp.
move=> n; rewrite subr_ge0; exact/uv.
Qed.

Definition increasing (u_ : (R^o) ^nat) := forall n, u_ n <= u_ n.+1.

Lemma increasing_ler (u_ : (R^o) ^nat) : increasing u_ ->
  forall n m, (n <= m)%nat -> u_ n <= u_ m.
Proof.
move=> iu n; elim=> [|m ih]; first by rewrite leqn0 => /eqP ->; exact/lerr.
rewrite leq_eqVlt => /orP[/eqP <-|]; first exact/lerr.
rewrite ltnS => /ih/ler_trans; apply; apply iu.
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
rewrite -(addrK (- lim u_) (u_ n.1)) opprK -(addrA (u_ n.1 - _)).
rewrite (ler_trans (ler_normm_add _ _)) // (splitr e%:num) ltrW //.
rewrite ltr_add //; near: n; apply: filter_pair_near_of => /= x y xoo yoo.
rewrite normmB; near: x; exact: H.
near: y; exact: H.
Grab Existential Variables. all: end_near. Qed.

End sequences.

Section exp_base.

Definition e_seq : (R^o) ^nat := fun n => (1 + 1 / n%:R) ^+ n.

Lemma e_seq0 : e_seq O = 1.
Proof. by rewrite /e_seq expr0 {1}(_ : 1 = 1%:R) // ler_nat. Qed.

Lemma e_seq1 : e_seq 1%nat = 2.
Proof. by rewrite /e_seq expr1 divr1. Qed.

Lemma e_seq2 : e_seq 2%nat = 9%:R / 4%:R.
Proof.
rewrite /e_seq -{1}(@divrr _ 2) ?unitfE // -mulrDl.
by rewrite expr_div_n {2}(_ : 1 = 1%:R) // -natrD -2!natrX.
Qed.

Section e_seq_is_bounded.

Let v_ (n m : nat) : R^o := (n - m + 2)%:R / (n - m)%:R.

Let v_increasing (n : nat) : forall m, (m < n)%nat -> v_ n.*2 m < v_ n.*2 m.+1.
Proof.
move=> m mn.
rewrite /v_.
have H : forall p q, (1 < q < p)%nat -> (p%:R : R) / q%:R < (p%:R - 1) / (q%:R - 1).
  move=> p q pq; rewrite ltr_pdivr_mulr; last first.
    by move/andP : pq => -[a b]; rewrite (_ : 0 = 0%:R) // ltr_nat (ltn_trans _ a).
  rewrite mulrAC ltr_pdivl_mulr; last first.
    by rewrite subr_gt0 (_ : 1 = 1%:R) // ltr_nat; case/andP: pq.
  by rewrite mulrBl mulrBr mul1r mulr1 ler_lt_sub // ltr_nat; case/andP : pq.
rewrite -(addn1 m) !subnDA (@natrB _ _ 1); last first.
  by rewrite subn_gt0 (leq_trans mn) // -addnn leq_addr.
rewrite (_ : (n.*2 - m - 1 + 2)%:R = (n.*2 - m + 2 - 1)%:R); last first.
  by rewrite !subn1 !addn2 /= prednK // subn_gt0 (leq_trans mn) // -addnn leq_addr.
rewrite (@natrB _ _ 1) ?subn_gt0 ?addn2 //.
apply H; apply/andP; split; last by rewrite ltnS.
move: (mn); rewrite -(ltn_add2r 1) !addn1 => mn'.
by rewrite ltn_subRL addn1 (leq_trans mn'){mn'} // -addnn -{1}(addn0 n) ltn_add2l (leq_trans _ mn).
Qed.

(* TODO: see also increasing_ler *)
Let v_increasing_ler (n : nat) : forall i, (i < n)%nat -> v_ n.*2 0 <= v_ n.*2 i.
Proof.
elim=> // -[/= _ n1|i ih ni].
  by apply/ltrW/v_increasing; rewrite (ltn_trans _ n1).
rewrite (ler_trans (ih _)) // ?(leq_trans _ ni) //.
by apply/ltrW/v_increasing; rewrite (leq_trans _ ni).
Qed.

Let v_prod (n : nat) : (0 < n)%nat ->
  \prod_(i < n) v_ n.*2 i = (n.*2.+2 * n.*2.+1)%:R / (n.+2 * n.+1)%:R.
Proof.
move=> n0; set lhs := LHS. set rhs := RHS.
rewrite -(@divr1_eq _ lhs rhs) // {}/lhs {}/rhs invf_div mulrA.
rewrite /v_ big_split /= -mulrA mulrACA.
rewrite [X in X * _ = 1](_ : _ = \prod_(i < n.+2) (n.*2 - i + 2)%:R); last first.
  rewrite 2!big_ord_recr /= -mulrA; congr (_ * _).
  by rewrite -addnn addnK subnS addnK 2!addn2 /= natrM prednK.
rewrite [X in _ * X = 1](_ : _ = \prod_(i < n.+2) (n.*2 - i + 2)%:R^-1); last first.
  rewrite 2!big_ord_recl /= mulrA [in LHS]mulrC; congr (_ * _).
    rewrite subn0 addn2 subn1 addn2 prednK ?double_gt0 //.
    by rewrite natrM invrM ?unitfE // mulrC.
    apply eq_bigr => i _; congr (_ %:R^-1).
    rewrite /bump !leq0n !add1n -addn2 subnDA subn2 addn2 /= prednK; last first.
      rewrite -subnS subn_gt0 -addnn -(addn1 i) (@leq_trans n.+1) //.
      by rewrite addn1 ltnS.
      by rewrite -{1}(addn0 n) ltn_add2l.
    by rewrite prednK // subn_gt0 -addnn (@leq_trans n) // leq_addr.
by rewrite -big_split /= big1 // => i _; rewrite divrr // ?unitfE addn2.
Qed.

Lemma e_seq_bound : forall n, (0 < n)%nat -> e_seq n < 4%:R.
Proof.
move=> n n0.
rewrite /e_seq -{1}(@divrr _ n%:R) ?unitfE ?pnatr_eq0 -?lt0n // -mulrDl.
rewrite (_ : _ ^+ n = \prod_(i < n) ((n%:R + 1) / n%:R)); last first.
  move _ : (_ / _) => h.
  elim: n n0 => // -[_ _|n ih _]; first by rewrite big_ord_recl big_ord0 mulr1 expr1.
  by rewrite exprS ih // [in RHS]big_ord_recl.
rewrite (@ler_lt_trans _ (\prod_(i < n) v_ n.*2 i)) //; last first.
  rewrite v_prod // (_ : _ / _%:R = 2%:R * (n.*2.+1)%:R / n.+2%:R); last first.
    rewrite -doubleS natrM -muln2 (natrM _ _ 2) natrM invrM ?unitfE ?pnatr_eq0 //.
    rewrite mulrCA 3!mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r; congr (_ * _).
  rewrite ltr_pdivr_mulr // (_ : 4 = 2 * 2)%nat // (natrM _ 2) -mulrA ltr_pmul2l //.
  by rewrite -natrM mul2n ltr_nat doubleS 2!ltnS -2!muln2 leq_mul2r /=.
apply ler_prod => i _; apply/andP; split.
  apply divr_ge0; last exact/ler0n.
  by rewrite [X in _ <= _ + X](_ : _ = 1%:R) // -natrD ler0n.
apply: (@ler_trans _ (v_ n.*2 (@ord0 n))).
  rewrite /v_ subn0 addn2 -doubleS.
  rewrite -2!muln2 2!natrM invrM // ?unitfE //; last first.
    by rewrite pnatr_eq0 -lt0n.
  rewrite -mulrA (mulrA 2) divrr ?unitfE // div1r.
  by rewrite [X in (_ + X) / _ <= _](_ : _ = 1%:R) // -natrD addn1.
destruct i as [i i0] => /=; exact/v_increasing_ler.
Qed.

End e_seq_is_bounded.

Section e_seq_increasing.

Let sum_group_by_2 n (f : nat -> R) :
  \sum_(i < n) f i = \sum_(i < n./2) (f i.*2 + f i.*2.+1) + if
  odd n.+1 then 0 else f n.-1.
Proof.
elim: n.+1 {-2}n (ltnSn n) => {n} // m ih [_|n].
  by rewrite 2!big_ord0 /= addr0.
rewrite ltnS => nm.
rewrite big_ord_recr /= ih // negbK; case: ifPn => /= [|].
  by move/negbTE => no; rewrite no addr0 uphalf_half no add0n.
rewrite negbK => no.
rewrite no uphalf_half no add1n addr0 big_ord_recr /= -!addrA; congr (_ + _).
move: (odd_double_half n); rewrite no add1n => nE.
by rewrite nE -{1}nE.
Qed.

Lemma increasing_e_seq : forall n, e_seq n < e_seq n.+1.
Proof.
case=> [|n]; first by rewrite e_seq0 e_seq1 {1}(_ : 1 = 1%:R) // ltr_nat /e_seq.
rewrite -(@ltr_pmul2l _ (((n.+2%:R - 1) / n.+2%:R) ^+ n.+2)); last first.
  apply/exprn_gt0/divr_gt0; last by rewrite ltr0n.
  by rewrite subr_gt0 {1}(_ : 1 = 1%:R) // ltr_nat.
rewrite [X in X < _](_ : _ = (n.+2%:R - 1) / n.+2%:R); last first.
  rewrite {1}/e_seq exprS -[RHS]mulr1 -3!mulrA; congr (_ * _).
  rewrite -mulrA; congr (_ * _).
  rewrite (_ : _ / n.+2%:R = (1 + 1 / n.+1%:R) ^-1); last first.
    rewrite -{4}(@divrr _ n.+1%:R) ?unitfE ?pnatr_eq0 // -mulrDl.
    by rewrite invf_div {2 6}(_ : 1 = 1%:R) // -natrD -natrB // subn1 addn1.
  by rewrite exprVn mulVr // unitfE expf_eq0 /= paddr_eq0 //= oner_eq0.
rewrite [X in _ < X](_ : _ = ((n.+2%:R ^+ 2 - 1) / n.+2%:R ^+ 2) ^+ n.+2); last first.
  rewrite /e_seq.
  rewrite -{4}(@divrr _ n.+2%:R) ?unitfE ?pnatr_eq0 // -mulrDl.
  rewrite -exprMn_comm; last by rewrite /GRing.comm mulrC.
  congr (_ ^+ _); rewrite mulrACA -subr_sqr expr1n; congr (_ * _).
  by rewrite -invrM // unitfE pnatr_eq0.
rewrite mulrBl divrr ?unitfE ?pnatr_eq0 // mulrBl divrr ?unitfE ?expf_eq0 /= ?pnatr_eq0 //.
rewrite exprBn_comm; last by rewrite /GRing.comm mulrC.
rewrite big_ord_recl 2!expr0 expr1n bin0 mulr1n 2![in X in _ < X]mul1r.
rewrite big_ord_recl 2!expr1 expr1n bin1 [in X in _ < X]mul1r mulN1r.
rewrite (_ : -1 / _ *+ _ = -1 / n.+2%:R); last first.
  rewrite 2!mulN1r mulNrn; congr (- _).
  rewrite expr2 invrM ?unitfE ?pnatr_eq0 //.
  rewrite -mulrnAr -[RHS]mulr1; congr (_ * _).
  by rewrite -mulr_natl divrr // unitfE pnatr_eq0.
rewrite addrA mulN1r div1r -ltr_subl_addl subrr.
pose F : 'I_n.+1 -> R :=
  fun i => (-1) ^+ i.+2 * n.+2%:R ^- 2 ^+ i.+2 *+ 'C(n.+2, i.+2).
rewrite (eq_bigr F); last first.
  by move=> i _; congr (_ *+ _); rewrite /= expr1n mulr1.
rewrite (sum_group_by_2 n.+1 (fun i => ((-1) ^+ i.+2 * n.+2%:R ^- 2 ^+ i.+2 *+ 'C(n.+2, i.+2)))).
destruct n as [|n'].
  by rewrite /= big_ord0 add0r -signr_odd /= expr0 mul1r.
set n := n'.+1.
set G := BIG_F.
have G_gt0 : forall i, 0 < G i.
  move=> /= i; rewrite /G.
  rewrite -signr_odd /= negbK odd_double expr0 mul1r.
  rewrite -signr_odd /= negbK odd_double /= expr1 mulN1r.
  rewrite mulNrn (@exprSr _ _ i.*2.+2) -mulrnAr -mulr_natr -mulrBr mulr_gt0 // ?exprn_gt0 //.
  rewrite subr_gt0 -mulr_natr ltr_pdivr_mull // -natrX -natrM.
  move: (@mul_bin_left n.+2 i.*2.+2).
  move/(congr1 (fun x => x%:R : R)).
  move/(congr1 (fun x => (i.*2.+3)%:R^-1 * x)).
  rewrite natrM mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r => ->.
  rewrite 2!natrM mulrA.
  have ? : (i.*2.+1 < n.+2)%nat.
    move: (ltn_ord i).
    rewrite 3!ltnS -(@leq_pmul2r 2) // !muln2 => /leq_trans; apply.
    case/boolP : (odd n') => on'.
      move: (odd_geq n' on'); rewrite leqnn => /esym.
      by move/leq_trans; apply; rewrite leqnSn.
    by move: (@odd_geq n' n on') => <-; rewrite leqnSn.
  rewrite ltr_pmul2r ?ltr0n ?bin_gt0 // ltr_pdivr_mull // -natrM ltr_nat.
  rewrite -(@ltn_add2r i.*2.+2) subnK // ltn_addr // -{1}(mul1n n.+2) -mulnn.
  by rewrite  mulnA ltn_mul2r /= mulSn addSn ltnS addSn.
have sum_G_gt0 : 0 < \big[+%R/0]_i G i.
  rewrite {1}(_ : 0 = \big[+%R/0]_(i < n.+1./2) 0); last by rewrite big1.
  apply: (@ltr_lerif _ _ _ false).
  rewrite (_ : false = [forall i : 'I_n.+1./2, false]); last first.
    apply/idP/forallP => //=; apply; exact: (@Ordinal _ 0).
  apply: lerif_sum => i _; exact/lerifP/G_gt0.
case: ifPn => no; first by rewrite addr0.
rewrite addr_gt0 //= -signr_odd (negbTE no) expr0 mul1r.
by rewrite pmulrn_lgt0 ?bin_gt0 // exprn_gt0.
Qed.

End e_seq_increasing.

Lemma cvg_e_seq : cvg e_seq.
Proof.
apply (@increasing_bound_cvg _ 4%:R).
  by move=> n; exact/ltrW/increasing_e_seq.
case.
by rewrite e_seq0 {1}(_ : 1 = 1%:R) // ler_nat.
by move=> n; apply/ltrW/e_seq_bound.
Qed.

Lemma lim_e_seq_lb : 2 < lim e_seq.
Proof.
apply: (@ltr_le_trans _ (e_seq 2%nat)).
  by rewrite e_seq2 ltr_pdivl_mulr // -natrM ltr_nat.
pose u_ : (R^o) ^nat := fun n => e_seq 2%nat.
rewrite (_ : e_seq _ = lim u_) //; last first.
  exact/esym/flim_map_lim/cst_continuous.
apply (@lim_ler _ _ 2%nat); last 2 first.
  exact/cvg_cst.
  exact/cvg_e_seq.
move=> i; rewrite /u_.
apply increasing_ler => ?.
exact/ltrW/increasing_e_seq.
Qed.

End exp_base.

From mathcomp Require Import div ssrint rat.

Lemma normq0 : normq 0 = 0.
Proof. by rewrite /normq /numq /denq /= div0n mulr0 normr0 rat0 mul0r. Qed.
Lemma numq0 : numq 0 = 0. Proof. by []. Qed.
Lemma numq1 : numq 1 = 1. Proof. by []. Qed.
Lemma denq1 : denq 1 = 1. Proof. by []. Qed.
Definition Normq (x : rat) : R := `| ratr x | (*`|numq x|%:~R / `|denq x|%:~R*).
Lemma Normq0 : Normq 0 = 0.
Proof. by rewrite /Normq -ratr_norm normr0 /ratr numq0 mul0r. Qed.
Lemma NormqN1 : Normq (-1) = 1.
Proof. by rewrite /Normq -ratr_norm normrN1 (_ : 1 = 1%:R) // ratr_nat. Qed.
Lemma ler_Normq_add (x y : rat) : Normq (x + y) <= Normq x + Normq y.
Proof. by rewrite /Normq rmorphD /= (ler_trans _ (ler_norm_add _ _)). Qed.
Lemma NormqM (x y : rat) : Normq (x * y) = Normq x * Normq y.
Proof. by rewrite /Normq rmorphM /= normrM. Qed.
Lemma Normq_eq0 (x : rat) : Normq x = 0 -> x = 0.
Proof.
rewrite /Normq -ratr_norm /ratr => /eqP; rewrite mulf_eq0 => /orP[|].
by rewrite intr_eq0 numq_eq0 normr_eq0 => /eqP.
by rewrite invr_eq0 intr_eq0 denq_eq0.
Qed.
Definition rat_AbsRingMixin : AbsRing.mixin_of rat_numDomainType :=
  @AbsRing.Mixin _ _ Normq0 NormqN1 ler_Normq_add NormqM Normq_eq0.
Canonical rat_absRingType := AbsRingType rat rat_AbsRingMixin.
Canonical rat_pointedType := [pointedType of rat for rat_absRingType].
Canonical rat_filteredType := [filteredType rat of rat for rat_absRingType].

Lemma scale_sequence (r_ : rat ^nat) (a : R) (a0 : 0 < a) :
  lim r_ = 0 <-> lim (fun n => ratr (r_ n) * a) = 0.
Proof.
Abort.
