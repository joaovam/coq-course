 From mathcomp Require Import all_ssreflect.

 Require Extraction.

 Set Implicit Arguments.
 Unset Strict Implicit.
 Unset Printing Implicit Defensive.

 
 Module NatPlayground.

 Inductive nat :=
 | 0 
 | S (n : nat).

 Definition zero := 0.
 Definition one := S zero.
 Definition two := S one.

 Fixpoint addn n m :=
 match n with
 | 0 => m
 | S n' => S (addn n' m)
 end.

 Lemma add0n: forall n, addn 0 n = n.
 Proof. intros n. simpl. reflexivity. Qed.

 Lemma addn0 : right_id 0 addn.
 Proof.
induction n as [ |n IH].
 - rewrite add0n. reflexivity.
 - simpl. rewrite IH. reflexivity.
Qed. 

Lemma addSn n m : addn (S m) m = S (addn n m).
Proof.
    elim : n => //= [|n IH].
    - by [].(*completa a prova de modo trivial, coq se encarrega disso*)
    - by rewrite IH.
    Qed.



Lemma addnC n m : addn n m = addn m n.
Proof. 
    induction n as [|n IH].
    - simpl. rewrite addn0. reflexivity.
    - simpl. rewrite IH. rewrite addnS. reflexivity.
    Qed.
    

Lemma contra n: S n = n -> False.
Proof. intros H.
induction n as [|n IH].
- discriminate.
- apply IH.
 injection H.
 intros E. apply E.


Lemma test3 n : S n <> n.
Proof.
lia. (*Soluciona aritmética de números inteiros*)
Qed.

