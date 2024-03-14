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

Theorem plus_1_neq_0:
  forall n : nat, (n + 1) =? 0 = false.
Proof.
  intros n.
  destruct n as [|n'] eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem negb_involutive:
  forall b : bool, negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andb_commutative:
  forall b c : bool, andb b c = andb c b.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + simpl. reflexivity.
  - destruct c eqn:Ec'.
    + simpl. reflexivity.
    + reflexivity.
Qed.

Theorem andb_true_elim2:
  forall b c : bool, andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b.
  - simpl. intros H. apply H.
  - simpl. intros H. destruct c.
    + reflexivity.
    + assumption.
Qed.

Theorem zero_nbeq_plus_1:
  forall n : nat, 0 =? (n + 1) = false.
Proof.
  intros n.
  destruct n as [| n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.
  
Compute plus' 3 4.
Compute plus' 0 5.
Compute plus' 8 0.

Theorem identity_fn_applied_twice:
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) -> forall (b : bool),
  f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice:
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) -> forall (b : bool),
  f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  rewrite -> negb_involutive.
  reflexivity.
Qed.

Theorem andb_eq_orb:
  forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
  intros b c H.
  destruct b.
  - apply eq_sym; trivial.
  - assumption.
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

Definition ltb (n m : nat) : bool :=
  if eqb n m then false
  else if leb n m then true
  else false.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Module LateDays.

Inductive letter : Type :=
  | A | B | C | D | F.

Inductive modifier : Type :=
  | Plus | Natural | Minus.

Inductive grade : Type :=
  Grade (l:letter) (m:modifier).

Inductive comparison : Type :=
  | Eq (* "equal" *)
  | Lt (* "less than" *)
  | Gt. (* "greater than" *)

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.
  
Compute letter_comparison B A.
(* = LT : comparison *)

Theorem letter_comparison_Eq :
  forall l, letter_comparison l l = Eq.
Proof.
  intros l.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.

Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with
  | Grade l1 m1, Grade l2 m2 =>
    match (letter_comparison l1 l2) with
    | Eq => modifier_comparison m1 m2
    | Lt => Lt
    | Gt => Gt
    end
  end.

Example test_grade_comparison1 :
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof.
  simpl. reflexivity.
Qed.
Example test_grade_comparison2 :
  (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof.
  simpl. reflexivity.
Qed.
Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof.
  simpl. reflexivity.
Qed.
Example test_grade_comparison4 :
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof.
  simpl. reflexivity.
Qed.

Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F (* Can't go lower than F! *)
  end.

Theorem lower_letter_F_is_F:
  lower_letter F = F.
Proof.
  simpl. reflexivity.
Qed.

Theorem lower_letter_lowers:
  forall l : letter,
  letter_comparison F l = Lt ->
  letter_comparison (lower_letter l) l = Lt.
Proof.
  intros l H.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - assumption.
Qed.

Definition lower_grade (g : grade) : grade :=
  match g with
  | Grade l m =>
    match l, m with
    | F, Minus => g
    | _, Plus => Grade l Natural
    | _, Natural => Grade l Minus
    | _, _ => Grade (lower_letter l) Plus
    end
  end.

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof.
  simpl. reflexivity.
Qed.
Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof.
  simpl. reflexivity.
Qed.
Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof.
  simpl. reflexivity.
Qed.
Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof.
  simpl. reflexivity.
Qed.
Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof.
  simpl. reflexivity.
Qed.
Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof.
  simpl. reflexivity.
Qed.
Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof.
  simpl. reflexivity.
Qed.

Compute lower_grade (Grade A Minus).
(* Grade B Plus : grade *)

Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof.
  simpl. reflexivity.
Qed.

Theorem lower_grade_lowers :
  forall g : grade,
  grade_comparison (Grade F Minus) g = Lt ->
  grade_comparison (lower_grade g) g = Lt.
Proof.
  intros g H0.
  destruct g.
  induction l.
  - induction m.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - induction m.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - induction m.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - induction m.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - induction m.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + assumption.
Qed.

Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
  if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g)).

Theorem no_penalty_for_mostly_on_time :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = true) -> apply_late_policy late_days g = g.
Proof.
  intros late_days g H.
  unfold apply_late_policy.
  rewrite -> H.
  reflexivity.
Qed.

Theorem grade_lowered_once :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = false) ->
    (late_days <? 17 = true) ->
    (grade_comparison (Grade F Minus) g = Lt) ->
    (apply_late_policy late_days g) = (lower_grade g).
Proof.
  intros late_days g H0 H1 G.
  unfold apply_late_policy.
  rewrite -> H0.
  rewrite -> H1.
  reflexivity.
Qed.

End LateDays.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 m' => B1 m'
  | B1 m' => B0 (incr m')
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B0 m' => mult 2 (bin_to_nat m')
  | B1 m' => S (mult 2 (bin_to_nat m'))
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.