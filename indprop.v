Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

Fixpoint div2 (n : nat) :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition f (n : nat) :=
  if even n then div2 n
  else (3 * n) + 1.

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

Fail Fixpoint reaches_1_in (n : nat) :=
  if n =? 1 then true
  else 1 + reaches_1_in (f n).

Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_done : Collatz_holds_for 1
  | Chf_more (n : nat) : Collatz_holds_for (f n) -> Collatz_holds_for n.

Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_done. 
Qed.

Conjecture collatz : forall n, Collatz_holds_for n.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).
Notation "n <= m" := (le n m) (at level 70).
Example le_3_5 : 3 <= 5.
Proof.
  apply le_S. (* 3 ≤ 4 *)
  apply le_S. (* 3 ≤ 3 *)
  apply le_n.
Qed.

Reserved Notation "n <= m" (at level 70).
Inductive le' : nat -> nat -> Prop :=
  | le_n' (n : nat) : n <= n
  | le_S' (n m : nat) : n <= m -> n <= (S m)
  where "n <= m" := (le' n m).
  
Inductive clos_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step (x y : X) :
      R x y -> clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y -> clos_trans R y z -> clos_trans R x z.

Inductive Person : Type := Sage | Cleo | Ridley | Moss.
Inductive parent_of : Person -> Person -> Prop :=
  po_SC : parent_of Sage Cleo
| po_SR : parent_of Sage Ridley
| po_CM : parent_of Cleo Moss.

Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.

Example ancestor_of1 : ancestor_of Sage Moss.
Proof.
  unfold ancestor_of. (* clos_trans parent_of Sage Moss *)
  apply t_trans with Cleo.
  - (* clos_trans parent_of Sage Moss *)
    {
      apply t_step. (* parent_of Sage Cleo *)
      apply po_SC.
    }
  - (* clos_trans parent_of Cleo Moss *)
    {
      apply t_step. (* parent_of Cleo Moss *)
      apply po_CM.
    }
Qed.

Inductive clos_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
    | rt_step :
        forall x y,
          R x y -> clos_refl_trans R x y
    | rt_refl :
        forall x,
          clos_refl_trans R x x
    | rt_trans :
        forall x y z,
          clos_refl_trans R x y -> clos_refl_trans R y z -> clos_refl_trans R x z.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

Example Perm3_example1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply perm3_trans with [2;1;3].
  - apply perm3_swap12.
  - apply perm3_swap23.
Qed.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0.
Qed.

Theorem ev_4' : ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

Theorem ev_plus4 :
  forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros H.
  apply ev_SS. apply ev_SS.
  assumption.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem ev_double :
  forall n, ev (double n).
Proof.
  intros n. unfold double.
  induction n as [|n' IHn'].
  - (* n = 0 *) apply ev_0.
  - (* n = n' *) apply ev_SS. assumption.
Qed.