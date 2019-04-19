(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import ssralg ssrnum fintype bigop binomial matrix.
From mathcomp Require Import interval.
Require Import boolp reals Rstruct Rbar.
Require Import classical_sets posnum topology normedtype landau forms derive.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

(* wip
   tentative implementation of littleo trick for differentials
   memo of 2019-02-26 Tue *)

Local Open Scope classical_set_scope.

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
