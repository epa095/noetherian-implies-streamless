Require Import List.

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

  Inductive accessible (P: list A->Prop) (l:list A): Prop:=
  | accessibleBase: P l -> accessible P l
  | accessibleInd: (forall x : A, accessible P (x :: l)) -> accessible P l.
 
  Fixpoint Initials (n:nat) (f: nat -> A) : list A :=
    match n with
      | 0 => nil 
      | S n => (f n) :: (Initials n f)
    end.

  Definition Noetherian (R: A -> A ->Prop) : Prop := accessible (goodLi R) nil.
  Definition Streamless  (R: A -> A ->Prop) : Prop := forall f:nat -> A,exists n:nat, (goodLi R) (Initials n f).

  Definition goodLiImplGoodF (R:A-> A->Prop)  (f:nat -> A) (l:list A) : Prop :=  goodLi R l -> goodLi R (Initials (length l) f).
  Definition raListImpliesRaF (R:A->A->Prop)  (f:nat -> A) (l:list A) : Prop :=  forall a:A, existsLi (R a) l -> existsLi (R a) (Initials (length l) f).


  (* This version is rather verbose to make clear what happens, it can be made shorter by using "inversion H1;auto"  *)
  Lemma noeimplstrHelp (R: A -> A ->Prop) (f:nat->A) : forall l:list A, accessible (goodLi R) l  -> (goodLiImplGoodF R f l) -> (raListImpliesRaF R f l) -> exists m, (goodLi R) (Initials m f).
  Proof.
    intros l acc eqGood eqRRel .   
    unfold goodLiImplGoodF in eqGood.
    unfold raListImpliesRaF in eqRRel.
    induction acc.  
    exists (length l).
    apply eqGood;auto.
    pose (H0 (f (length l))).
    apply e.
    intro H1.
    simpl.    
    inversion H1.
    left.   
    apply eqRRel.
    exact H2.
    right.   
    apply eqGood.
    exact H2.
    (* inversion H1;auto. *)
    intros a H1.
    inversion H1.
    simpl.
    left.
    exact H2.
    right.
    pose (eqRRel a) as e0.
    apply e0;auto.
  Qed.

  Lemma NoeimplStr (R:A->A->Prop) : Noetherian R -> Streamless R.
  Proof.
    unfold Noetherian.
    intros acc f.
    apply noeimplstrHelp with (l:=nil);auto.
    intro H; contradiction H.
    intros a H; contradiction H.
  Qed.  

End NoetherianImplStreamless.
