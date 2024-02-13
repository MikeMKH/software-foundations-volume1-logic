Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Check day.
(* day : Set *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Check next_weekday.
(* next_weekday : day -> day *)

Compute (next_weekday friday).
(* = monday : day *)

Compute (next_weekday saturday).
(* = monday : day *)

Compute (next_weekday (next_weekday (next_weekday friday))).
(* = wednesday : day *)

Example next_next_weekday_after_friday :
  (next_weekday (next_weekday friday)) = tuesday.
Proof.
  simpl.
  reflexivity.
Qed.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b:bool) : bool :=
  if b then false
  else true.
Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.
Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => if b2 then false else true
  | false => true
  end.
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => andb b2 b3
  | false => false
  end.
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.
(* true : bool *)

Check true : bool.
(* true : bool : bool *)

(* Check true : day. (* The term "true" has type "bool" while it is expected to have type "day". *) *)

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary(p : rgb).

Check primary(blue) : color.
(* primary blue : color : color *)

Check primary red : color.
(* primary red : color : color *)

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary _ => false
  end.

Example black_is_monochrome: monochrome black = true.
Proof. simpl. reflexivity. Qed.

Example red_is_not_monochrome: monochrome (primary red) = false.
Proof. simpl. reflexivity. Qed.

Definition isred (c : color) : bool :=
  match c with
  | primary red => true
  | _ => false
  end.

Example red_is_isred: isred (primary red) = true.
Proof. simpl. reflexivity. Qed.

Example white_is_not_isred: isred white = false.
Proof. trivial. Qed.

Module TuplePlayground.

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b b b b : bit).

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | _ => false
  end.

Compute all_zero (bits B0 B0 B0 B0).
(* = true : bool *)

Compute all_zero (bits B1 B0 B0 B0).
(* = false : bool *)

End TuplePlayground.

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Inductive caveNat : Type :=
  | dot
  | tick (n : caveNat).

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S(n') => n'
  end.

Compute pred (S O).
(* = O : nat *)

Compute pred (S (S O)).
(* = S O : nat *)

Check S (S (S O)).
(* S (S (S O)) *)

End NatPlayground.

Check S (S (S O)).
(* 3 : nat *)

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.
  
Compute minustwo (S (S (S O))).
(* = 1 : nat *)

Compute minustwo O.
(* = 0 : nat *)

Compute minustwo (S O).
(* = 0 : nat *)

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n : nat) : bool :=
  negb (even n).

Example one_odd : odd 1 = true.
Proof. reflexivity. Qed.

Example two_even : even 2 = true.
Proof. simpl. reflexivity. Qed.

Example one_is_not_even : even 1 = false.
Proof. simpl. reflexivity. Qed.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => mult n (factorial n')
  end.

Example test_factorial3 : (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial4 : (factorial 4) = (mult 6 4).
Proof. simpl. reflexivity. Qed.

Theorem plus_0_n : forall n, 0 + n = n.
Proof. simpl. reflexivity. Qed.

Theorem plus_n_0 : forall n, n + 0 = n.
Proof.
  intros.
  induction n.
  - reflexivity.
  - intros. symmetry in |- *. auto.
Qed.

Theorem plus_n_0' : forall n, n + 0 = n.
Proof.
  intros.
  induction n.
  - reflexivity.
  - intros. symmetry in |- *. apply plus_n_O.
Qed.

Theorem plus_1_l : forall n, 1 + n = S n.
Proof. simpl. reflexivity. Qed.

Theorem mult_0_l : forall n, 0 * n = 0.
Proof. intros. simpl. reflexivity. Qed.

Theorem mult_1_r : forall n, n * 1 = n.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. apply f_equal_nat. assumption.
Qed.

Theorem plus_identical' :
  forall n m : nat, n = m -> n + n = m + m.
Proof.
  intros.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_identical'' :
  forall n m o : nat, n = m -> m = o -> n + m = m + o.
Proof.
  intros.
  rewrite -> H.
  rewrite -> H0.
  reflexivity.
Qed.

Check mult_n_O.
(* forall n : nat, 0 = n * 0 *)

Check mult_n_Sm.
(* forall n m : nat, n * m + n = n * S m *)

Theorem mult_n_0_m_0 :
  forall p q : nat, (p * 0) + (q * 0) = 0.
Proof.
  intros.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  simpl.
  reflexivity.
Qed.

Theorem mult_n_1 : forall p : nat, p * 1 = p.
Proof.
  intros.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  simpl.
  reflexivity.
Qed.