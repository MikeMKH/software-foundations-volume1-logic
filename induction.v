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

Theorem mult_0_plus' :
  forall n m : nat, (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H : n + 0 + 0 = n).
  {
    rewrite -> add_comm. simpl.
    rewrite -> add_comm. simpl.
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange :
  forall n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H : n + m = m + n).
  {
    rewrite <- add_comm.
    reflexivity.
  }
  rewrite <- H.
  reflexivity.
Qed.

Theorem add_assoc' :
  forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n' IHn'].
  - (* n = 0 *)
    simpl; reflexivity.
  - (* n = S n' *)
    {
      simpl; rewrite IHn'.
      reflexivity.
    }
Qed.

Theorem add_comm' :
  forall n m : nat, n + m = m + n.
Proof.
  intros n m. induction m as [|m' IHm'].
  - (* m = 0 *)
    {
      simpl; rewrite -> add_0_r.
      reflexivity.
    }
  - (* m = S m' *)
    {
      simpl; rewrite <- IHm'.
      rewrite <- plus_n_Sm.
      reflexivity.
    }
Qed.

Theorem eqb_refl' :
  forall n : nat, (n =? n) = true.
Proof.
  intros n. induction n as [|n' IHn'].
  - (* n = 0 *)
    simpl; reflexivity.
  - (* n = S n' *)
    {
      simpl. rewrite -> IHn'.
      reflexivity.
    }
Qed.

Theorem plus_n_n_eq_mul_2n_l :
  forall n : nat, n + n = 2 * n.
Proof.
  intros n. induction n as [|n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    {
      simpl. rewrite -> add_0_r.
      reflexivity.
    }
Qed.

Theorem add_shuffle3 :
  forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. induction n as [|n' IHn'].
  - (* n = 0 *) simpl; reflexivity.
  - (* n = S n' *)
    {
      simpl; rewrite IHn'.
      rewrite -> plus_n_Sm.
      reflexivity.
    }
Qed.

Lemma mul_n_O :
  forall n : nat, n * O = O.
Proof.
  intros n. induction n as [|n' IHn'].
  - (* n = 1 *) simpl; reflexivity.
  - (* n = S n' *)
    {
      simpl; rewrite -> IHn'.
      reflexivity.
    }
Qed.

Lemma mul_n_Sm :
  forall n m : nat, n * S m = n + n * m.
Proof.
  intros n m. induction n as [|n' IHn'].
  - (* n = 1 *) simpl; reflexivity.
  - (* n = S n' *)
    {
      simpl; rewrite -> IHn'.
      rewrite -> add_assoc, -> add_assoc.
      assert (H : m + n' = n' + m). { rewrite -> add_comm. reflexivity. }
      rewrite -> H.
      reflexivity.
    }
Qed.

Theorem mul_comm :
  forall m n : nat, m * n = n * m.
Proof.
  intros m n. induction n as [|n' IHn'].
  - (* n = 1 *)
    {
      simpl; rewrite -> mul_n_O.
      reflexivity.
    }
  - (* n = S n' *)
    {
      simpl; rewrite -> mul_n_Sm.
      rewrite <- IHn'.
      reflexivity.
    }
Qed.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Theorem plus_leb_compat_l :
  forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p H. induction p as [|p' IHp'].
  - (* p = 0 *) simpl; assumption.
  - (* p = S p' *) simpl; assumption.
Qed.