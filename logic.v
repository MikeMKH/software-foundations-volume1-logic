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

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4. (* written /\ *)
Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  destruct n as [|n'].
  - (* 0 = 0 /\ m = 0 *)
    {
      split.
      + (* 0 = 0 *) reflexivity.
      + (* m = 0 *)
        {
          destruct m as [|m'].
          - (* 0 = 0 *) reflexivity.
          - (* S m' = 0 *) discriminate.
        }
    }
  - (* S n' = 0 /\ m = 0 *)
    {
      split.
      + (* S n' = 0 *) discriminate.
      + (* m = 0 *)
        {
          destruct m as [|m'].
          - (* 0 = 0 *) reflexivity.
          - (* s m' = 0 *) discriminate.
        }
    }
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2'' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* intros n m Hn Hm. (* does not work on my system *) *)
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  apply and_exercise in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 :
  forall P Q : Prop, P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP.
Qed.

Lemma proj2 :
  forall P Q : Prop, P /\ Q -> Q.
Proof.
  intros P Q [_ HQ].
  assumption.
Qed.

Theorem and_commut :
  forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.
Qed.

Theorem and_assoc :
  forall P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - (* P /\ Q *) split.
    + apply HP.
    + apply HQ.
  - (* R *) apply HR.
Qed.

Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on n = 0 ∨ m = 0 *)
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro_l :
  forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. destruct n as [|n'].
  - (* n = 0 *) left. reflexivity.
  - (* n = S n' *) right. simpl in H. destruct m as [|m'].
    + (* m = 0 *) reflexivity.
    + (* m = S m' *) inversion H.
Qed.

Theorem or_commut :
  forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - (* HP *) right. apply HP.
  - (* HQ *) left. apply HQ.
Qed.