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
