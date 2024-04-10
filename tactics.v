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
