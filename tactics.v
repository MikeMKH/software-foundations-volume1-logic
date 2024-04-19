Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Theorem silly1 :
  forall (n m : nat),
  n = m -> n = m.
Proof.
  intros n m eq.
  apply eq.
Qed.

Theorem silly2 :
  forall (n m o p : nat),
  n = m -> (n = m -> [n;o] = [m;p]) -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2; apply eq1.
Qed.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
  negb (even n).

Theorem silly_ex :
  forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true -> odd (S p) = true.
Proof.
  intros p H0 H1 H2.
  apply H1.
  apply H0.
  apply H2.
Qed.

Theorem silly3 :
  forall (n m : nat), n = m -> m = n.
Proof.
  intros n m H.
  symmetry.
  apply H.
Qed.

Example trans_eq_example :
  forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  - (* [a; b] = [c; d] *) apply eq1.
  - (* [c; d] = [e; f] *) apply eq2.
Qed.

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Example trans_eq_exercise :
  forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  transitivity (n + p).
  - (* n + p = n + p *) reflexivity.
  - (* n + p = minustwo o *)
    {
      rewrite -> eq2.
      apply eq1.
    }
Qed.

Example trans_eq_exercise' :
  forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

Theorem S_injective :
  forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2.
  rewrite H1.
  simpl; reflexivity.
Qed.

Theorem S_injective' :
  forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H.
  injection H as Hnm.
  apply Hnm.
Qed.

Theorem injection_ex1 :
  forall (n m o : nat),
  [n;m] = [o;o] -> n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. rewrite H2.
  reflexivity.
Qed.

Example injection_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j H0 H1.
  injection H0. intros H2 H3.
  assert (H': z::l = y::l). { rewrite <- H1. symmetry. apply H2. }
  injection H' as Hzy.
  rewrite -> H3.
  apply Hzy.
Qed.

Theorem discriminate_ex1 :
  forall (n m : nat),
  false = true -> n = m.
Proof.
  intros n m contra.
  discriminate contra.
Qed.

Theorem discriminate_ex2 :
  forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra.
  discriminate contra.
Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] -> x = z.
Proof.
  intros X x y z l j contra.
  discriminate contra.
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
  
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Theorem eqb_0_l :
  forall n, 0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - (* n = 0 *) intros H. reflexivity.
  - (* n = S n' *)
    {
      simpl; intros contra.
      discriminate contra.
    }
Qed.

Theorem f_equal' :
  forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof.
  intros A B f x y eq.
  rewrite <- eq.
  reflexivity.
Qed.

Theorem eq_implies_succ_equal :
  forall (n m : nat),
  n = m -> S n = S m.
Proof.
  intros n m eq.
  apply f_equal'.
  rewrite <- eq.
  reflexivity.
Qed.

Theorem eq_implies_succ_equal' :
  forall (n m : nat),
  n = m -> S n = S m.
Proof.
  intros n m eq.
  f_equal.
  rewrite <- eq.
  reflexivity.
Qed.

Theorem S_inj :
  forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b -> (n =? m) = b.
Proof.
  intros n m b H.
  simpl in H.
  apply H.
Qed.

Theorem silly4 :
  forall (n m p q : nat),
  (n = m -> p = q) -> m = n -> q = p.
Proof.
  intros n m p q H1 H2.
  symmetry in H2.
  apply H1 in H2.
  symmetry in H2.
  apply H2.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Theorem add_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - (* n = 0 *) reflexivity.
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

Theorem specialize_example:
  forall n,
  (forall m, m * n = 0) -> n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  simpl in H.
  rewrite add_comm in H.
  simpl in H.
  apply H.
Qed.

Theorem trans_eq :
  forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1. rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example''' :
  forall (a b c d e f : nat),
  [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  specialize trans_eq with (m:=[c;d]) as H.
  apply H.
  - (* [a; b] = [c; d] *) apply eq1.
  - (* [c; d] = [e; f] *) apply eq2.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective :
  forall n m,
  double n = double m -> n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *)
    {
      intros m eq.
      destruct m as [| m'] eqn:E.
      + (* m = O *) discriminate eq.
      + (* m = S m' *)
        f_equal.
        apply IHn'.
        simpl in eq; injection eq as goal.
        apply goal.
    }
Qed.

Theorem eqb_true :
  forall n m,
  n =? m = true -> n = m.
Proof.
  intros n. induction n as [|n' IHn'].
  - (* n = 0 *)
    {
      intros m eq. destruct m as [|m'] eqn:E.
      + (* m = 0 *) reflexivity.
      + (* m = S m' *) discriminate eq.
    }
  - (* n = S n' *)
    {
      intros m eq. induction m as [|m' IHm'].
      + (* m = 0 *)  discriminate eq.
      + (* m = S m' *)
        {
          f_equal.
          apply IHn'.
          inversion eq.
          reflexivity.
        }
     }
Qed.

Theorem plus_n_n_injective :
  forall n m,
  n + n = m + m -> n = m.
Proof.
  intros n. induction n as [|n]. induction m.
  - (* n = 0, m = 0 *) reflexivity.
  - (* n = 0, m = S m *)
    {
      simpl; intros H.
      inversion H.
    }
  - (* n = S n, m = S m *)
    {
      intros m H.
      simpl in H.
      rewrite <- plus_n_Sm in H.
      destruct m. inversion H.
      simpl in H. rewrite <- plus_n_Sm in H.
      inversion H. apply IHn in H1.
      f_equal. apply H1.
    }
Qed.

Theorem double_injective_take2 :
  forall n m,
  double n = double m -> n = m.
Proof.
  intros n m. generalize dependent n. (* n is back in goal *)
  induction m as [|m' IHm'].
  - (* m = 0 *) simpl; intros n eq. destruct n as [|n'] eqn:E.
    + (* n = 0 *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [|n'] eqn:E.
    + (* n = 0 *) discriminate eq.
    + (* n = S n' *)
      {
        f_equal. apply IHm'.
        injection eq as goal. apply goal.
      }
Qed.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Theorem nth_error_after_last :
  forall (n : nat) (X : Type) (l : list X),
  length l = n -> nth_error l n = None.
Proof.
  intros n X l H. generalize dependent n.
  - (* n = 0 *) induction l as [|l' IHl']. simpl; reflexivity.
  intros n H.
  rewrite <- H.
  apply IHIHl'.
  reflexivity.
Qed.

Definition square n := n * n.

Theorem mult_assoc :
  forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof. Admitted.

Theorem mul_comm :
  forall m n : nat,
  m * n = n * m.
Proof. Admitted.

Lemma square_mult :
  forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl; unfold square.
  rewrite -> mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite <- mul_comm. apply mult_assoc. }
  rewrite -> H.
  rewrite -> mult_assoc.
  reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1 :
  forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2 :
  forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m. destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fact silly_fact_2' :
  forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.