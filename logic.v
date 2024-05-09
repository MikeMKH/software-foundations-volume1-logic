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

Definition not (P:Prop) := P -> False.
Check not : Prop -> Prop.
Notation "~ x" := (not x) : type_scope.

Theorem ex_falso_quodlibet :
  forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Theorem not_implies_our_not :
  forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P H Q H0.
  apply H in H0.
  destruct H0.
Qed.

Notation "x <> y" := (~(x = y)).

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  intros contra.
  discriminate contra.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not.
  intros H.
  destruct H.
Qed.

Theorem contradiction_implies_anything :
  forall P Q : Prop, (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA].
  unfold not in HNA. apply HNA in HP.
  destruct HP.
Qed.

Theorem double_neg :
  forall P : Prop, P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros G.
  apply G.
  apply H.
Qed.

Theorem contrapositive :
  forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H.
  unfold not.
  intros H0 H1.
  apply H0. apply H.
  assumption.
Qed.

Theorem not_both_true_and_false :
  forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros H.
  apply H. destruct H.
  assumption.
Qed.

Theorem de_morgan_not_or :
  forall (P Q : Prop), ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q H.
  unfold not.
  split.
  - (* P -> False *)
    {
      intros H0.
      unfold not in H. apply H.
      left.
      assumption.
    }
  - (* Q -> False *)
    {
      intros H0.
      unfold not in H. apply H.
      right.
      assumption.
    }
Qed.

Theorem not_true_is_false :
  forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Theorem not_true_is_false' :
  forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H. (* note implicit destruct b here *)
  - (* b = true *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.
  
Theorem disc_example :
  forall n, ~ (O = S n).
Proof.
  intros n H1.
  assert (H2 : disc_fn O). { simpl. apply I. }
  rewrite H1 in H2. simpl in H2. apply H2.
Qed.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

Theorem iff_sym :
  forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.
Qed.

Lemma not_true_iff_false :
  forall b, b <> true <-> b = false.
Proof.
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *) intros H. rewrite H. intros H'. discriminate H'.
Qed.

Lemma apply_iff_example1 :
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R Hiff H HP.
  apply H. apply Hiff. apply HP.
Qed.

Lemma apply_iff_example2 :
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros P Q R Hiff H HQ.
  apply H. apply Hiff. apply HQ.
Qed.

Theorem or_distributes_over_and :
  forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - (* -> *)
    {
      intros [HP | [HQ HR]].
      + (* P *)
        {
          split.
          - (* P ∨ Q *) left. assumption.
          - (* P ∨ R *) left. assumption.
        }
      + (* Q R *)
        {
          split.
          - (* P ∨ Q *) right. assumption.
          - (* P ∨ R *) right. assumption.
        }
    }
  - (* <- *)
    intros [[HP | HQ] [HP' | HR]].
    + (* P *) left. assumption.
    + (* P R *) left. assumption.
    + (* Q P *) left. assumption.
    + (* Q R *) right. split.
      * (* Q *) assumption.
      * (* R *) assumption.
Qed.

From Coq Require Import Setoids.Setoid.

Lemma mul_eq_0 :
  forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - (* n * m = 0 → n = 0 ∨ m = 0 *) apply mult_is_O.
  - (* n = 0 ∨ m = 0 → n * m = 0 *) apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - (* P ∨ Q ∨ R → (P ∨ Q) ∨ R *)
    {
      intros [H | [H | H]].
      + (* P *) left. left. assumption.
      + (* Q *) left. right. assumption.
      + (* R *) right. assumption.
    }
  - (* P ∨ Q) ∨ R → P ∨ Q ∨ R *)
    {
      intros [[H | H] | H].
      + (* P *) left. assumption.
      + (* Q *) right. left. assumption.
      + (* R *) right. right. assumption.
    }
Qed.

Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof. Admitted. (* the definition given in the text does not work *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Definition Even x := exists n : nat, x = double n.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

Theorem exists_example_2 :
  forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m H].
  exists (2 + m).
  apply H.
Qed.

Theorem dist_not_exists :
  forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  unfold not.
  intros X P H [x N].
  apply N. apply H.
Qed.

Theorem dist_exists_or :
  forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - (* (∃ x : X, P x ∨ Q x) → (∃ x : X, P x) ∨ (∃ x : X, Q x) *)
    {
      intros [x [Px | Qx]].
      + (* P x *) left. exists x. assumption.
      + (* Q x *) right. exists x. assumption.
    }
  - (* (∃ x : X, P x) ∨ (∃ x : X, Q x) → ∃ x : X, P x ∨ Q x *)
    {
      intros [[x Px] | [x Qx]].
      + (* P x *) exists x. left. assumption.
      + (* Q x *) exists x. right. assumption.
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

Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n+x.
Proof. Admitted.

Theorem plus_exists_leb : forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof. Admitted.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
  In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite -> H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros. split.
  induction l as [|x' l' IHl'].
  - (* [] *) simpl; contradiction.
  - (* x' :: l' *) simpl; intros [H | H].
    + (*  x' = y *) 
      {
        exists x'. split.
        apply H. left. reflexivity.
      }
    + (* In y (map f l') *)
      {
        apply IHl' in H. destruct H as [w [F I]].
        exists w. split.
        apply F. right. apply I.
      }
  - (* (∃ x : A, f x = y ∧ In x l) → In y (map f l) *)
    {
      intros [w [F I]].
      rewrite <- F. apply In_map. apply I.
    }
Qed.

Theorem In_app_iff :
  forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. split.
  induction l as [|h t IH].
  - (* [] *) simpl; right. apply H.
  - (* h :: t *) simpl; intros [H | H].
    + (* h = a *) left. left. assumption.
    + (* In a (t ++ l') *) apply IH in H. destruct H.
      * (* In a t *) left. right. assumption.
      * (* In a l' *) right. assumption.
  - induction l as [|h t].
    + (* [] *) intros [H | H].
      * inversion H.
      * simpl; assumption.
    + (* h :: t *) intros [H | H].
      * simpl; inversion H.
        { left. assumption. }
        { right. apply IHt. left. assumption. }
      * simpl. right. apply IHt. right. assumption.
Qed.