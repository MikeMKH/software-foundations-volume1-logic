Set Warnings "-notation-overridden,-parsing".
Set Warnings "-deprecated-hint-without-locality".
Require Nat.

Check (forall n m : nat, n + m = m + n) : Prop.

(* non-sense is still a proposition but is not provable*)
Check 2 = 2 : Prop.
Check 3 = 2 : Prop.
Check forall n : nat, n = 2 : Prop.

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity. Qed.

Definition two_plus_two_claim : Prop := 2 + 2 = 4.
Check two_plus_two_claim. (* Prop *)

Theorem two_plus_two_claim_is_true :
  two_plus_two_claim.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.
Check is_three(3) : Prop.
Check is_three(4) : Prop.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.
Lemma succ_inj' : injective S.
Proof.
  intros n m H.
  injection H as H1.
  apply H1.
Qed.

Check @eq : forall A : Type, A -> A -> Prop.