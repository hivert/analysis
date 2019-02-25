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

Definition sequence R := nat -> R.
Notation "R ^nat" := (sequence R) (at level 0).

Section sequences.

Canonical eventually_filter := FilterType eventually _.
Canonical eventually_pfilter := PFilterType eventually (filter_not_empty _).
Notation eqolimn := (@eqolim _ _ _ (eventually_filter)).
Notation eqolimPn := (@eqolimP _ _ _ (eventually_filter)).

Lemma lim_add_sequence (u_ v_ : (R^o) ^nat) : cvg u_ -> cvg v_ ->
  lim (u_ + v_) = lim u_ + lim v_.
Proof. by move=> u_cv v_cv; apply/flim_map_lim/lim_add. Qed.

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

Lemma squeeze_fun (T : Type) (f g h : T -> R) (a : filter_on T) (l : R) :
  f @ a --> l ->
  h @ a --> l ->
  (\forall x \near a, f x <= g x <= h x) ->
  g @ a --> l.
Proof.
move=> fal hal afgh; apply/flim_locally => _/posnumP[/= e].
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

Lemma squeeze (u_ v_ w_ : (R^o) ^nat) l :
  (exists N, forall n, (n >= N)%nat -> u_ n <= v_ n <= w_ n) ->
  cvg u_ -> lim u_ = l ->
  cvg w_ -> lim w_ = l ->
  cvg v_ /\ lim v_ = l.
Proof.
case=> N uvw cvgu ul cvgw wl.
suff vol : v_ @ \oo --> l.
  by split; [exact/(@cvgP _ _ (v_ @ \oo) l) | exact/flim_map_lim].
apply/flim_normP => _/posnumP[e].
near_simpl; near=> N0; rewrite ltr_norml; apply/andP; split.
- rewrite ltr_oppl opprB (@ler_lt_trans _ (w_ N0 - l)) //.
  + rewrite ler_sub //.
    have /(_ _) /andP[|//] := @uvw N0.
    by near: N0; by exists N.
  + rewrite (@ler_lt_trans _ `|[w_ N0 - l]|) // ?real_ler_norm // ?num_real //.
    rewrite normmB.
    near: N0; move/flim_normP : cvgw; rewrite wl; exact.
- rewrite (@ler_lt_trans _ (l - u_ N0)) //.
  + rewrite ler_sub //.
    have /(_ _) /andP[|//] := @uvw N0.
    by near: N0; by exists N.
  + rewrite (@ler_lt_trans _ `|[u_ N0 - l]|) //.
      by rewrite -normmB real_ler_norm // num_real.
    rewrite normmB.
    near: N0; move/flim_normP : cvgu; rewrite ul; exact.
Grab Existential Variables. all: end_near. Qed.

End sequences.