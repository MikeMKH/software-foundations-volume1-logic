Theorem add_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_n_n : forall n : nat, n - n = 0.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mul_0_r : forall n : nat, n * 0 = 0.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm :
  forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm :
  forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - (* n = 0 *) rewrite -> add_0_r. induction m as [|m' IHm'].
    + (* m = 0 *) simpl. reflexivity.
    + (* m = S m' *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. induction m as [|m' IHm'].
    + (* m = 0 *) simpl. reflexivity.
    + (* m = S m' *) simpl. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc :
  forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.
Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
    | O => true
    | S m' => false
    end
  | S n' => match m with
    | O => false
    | S m' => eqb n' m'
    end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem eqb_refl :
  forall n : nat, (n =? n) = true.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O =>  false
  | S (S n') => even n'
  end.

Theorem negb_involutive :
  forall b : bool, negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem even_S :
  forall n : nat, even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - rewrite -> IHn'. rewrite -> negb_involutive. reflexivity.
Qed.