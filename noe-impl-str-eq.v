Require Import List.

(* This is a variant which uses equivalence on lists.  *)
Section NoetherianImplStreamless.
  Variable A : Set. 

  Fixpoint existsLi (P:A->Prop) (l:list A) : Prop :=
    match l with
      | nil => False
      | h::tail => (P h \/ (existsLi P tail))
    end.

  Fixpoint goodLi (R:A-> A->Prop) (l:list A) : Prop :=
    match l with
      | nil => False
      | a::tail => (existsLi (R a) tail \/ goodLi R tail)
    end.                             


  Inductive accessible (P: list A->Prop) (l: list A): Prop:=
  | accessibleBase:P l -> accessible P l
  | accessibleInd:  (forall x : A, accessible P (x :: l)) -> accessible P l.

  Definition Noetherian (R: A -> A ->Prop) : Prop := accessible (goodLi R) nil.

  
  Fixpoint Initials (n:nat) (f: nat -> A) : list A :=
    match n with
      | 0 => nil 
      | S n => (f n) :: (Initials n f)
    end.

  
  Definition Streamless  (R: A -> A ->Prop) : Prop := forall f:nat -> A,exists n:nat, (goodLi R) (Initials n f).

  Definition isInitial (l:list A) (f:nat -> A) : Prop :=  Initials (length l) f = l.
  
  Lemma noeimplstrHelp (R: A -> A ->Prop) (f:nat->A) : forall l:list A,  accessible (goodLi R) l  -> (isInitial l f) ->  exists m, (goodLi R) (Initials m f).
  Proof.
    intros l acc leq .
    unfold isInitial in leq.
    induction acc.  
    exists (length l).
    rewrite leq;auto.
    pose (H0 (f (length l) )).
    apply e.
    simpl.
    rewrite leq.
    auto.
  Qed.
  Lemma NoeimplStr (R:A->A->Prop) : Noetherian R -> Streamless R.
  Proof.
    unfold Noetherian.
    intros acc f.
    assert (isInitial nil f).
    unfold isInitial;simpl;auto.
    apply noeimplstrHelp with (l:=nil);auto.
  Qed.
  
End NoetherianImplStreamless.
