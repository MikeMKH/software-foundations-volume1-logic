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

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
  end.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
  (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l. split.
  - (* <- *) induction l as [|h t].
    + (* [] *) reflexivity.
    + (* h :: t *)
      {
        simpl. intros H. split.
        * (* P h *) apply H. left. reflexivity.
        * (* All P t *)
          {
            apply IHt. intros x G.
            apply H. right. apply G.
          }
      }
  - (* -> *) induction l as [|h t].
    + (* [] *) intros _ __ G. inversion G.
    + (* h :: t *)
      {
        intros H x H0.
        simpl in H. destruct H as [PH APT].
        simpl in H0. destruct H0 as [HX | IXT].
        * rewrite <- HX. assumption.
        * apply IHt. assumption. assumption.
      }
Qed.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
  
Theorem add_comm :
  forall n m : nat, n + m = m + n.
Proof. Admitted.

Check plus : nat -> nat -> nat.
Check @rev : forall X, list X -> list X.
Check add_comm : forall n m : nat, n + m = m + n.

Lemma add_comm3_fail :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite <- add_comm.
  rewrite <- add_comm.
Abort.

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite <- add_comm.
  rewrite <- (add_comm y z).
  reflexivity.
Qed.

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. intros Hl.
  rewrite -> Hl in H.
  simpl in H.
  assumption.
Qed.

Lemma in_not_nil_42_fail :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

Lemma in_not_nil_42' :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  assumption.
Qed.

Lemma in_not_nil_42'' :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  assumption.
Qed.

Lemma in_not_nil_42''' :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  assumption.
Qed.

Lemma in_not_nil_42'''' :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Theorem mul_comm :
  forall n m : nat, n * m = m * n.
Proof. Admitted.

Theorem mul_0_r :
  forall n:nat, n * 0 = 0.
Proof.
  intros n. apply mul_comm.
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
  In n (map (fun m => m * 0) ns) -> n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H) as [m [Hm _]].
  rewrite -> mul_0_r in Hm.
  rewrite <- Hm.
  reflexivity.
Qed.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

Example even_42_prop : Even 42.
Proof.
  unfold Even.
  exists 21.
  reflexivity.
Qed.

Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - (* k = 0 *) reflexivity.
  - (* k = S k' *) simpl; assumption.
Qed.

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

Lemma even_double_conv :
  forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  intros n. induction n as [|n' IHn'].
  - (* n = 0 *) exists 0. reflexivity.
  - (* n = S n' *)
    {
      rewrite -> even_S. destruct IHn' as [k HE].
      destruct (even n').
      - (* even n' = true *)
        {
          destruct k as [|k' IHk'].
          + (* k = 0 *)
            {
              exists 0.
              rewrite <- HE.
              simpl; reflexivity.
            }
          + (* k = S k' *)
            {
              simpl. rewrite -> HE.
              exists (S k').
              reflexivity.
            }
         }
      - (* even n' = false *)
        {
          simpl.
          destruct k as [|k' IHk'].
          + (* k = 0 *)
            {
              exists 1.
              rewrite -> HE.
              reflexivity.
            }
          + (* k = S k' *)
            {
              rewrite -> HE. simpl.
              exists (S (S k')). simpl.
              reflexivity.
            }
       }
    }
Qed.

Theorem even_bool_prop :
  forall n, even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
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

Theorem eqb_true :
  forall n m, n =? m = true -> n = m.
Proof. Admitted.

Theorem eqb_refl :
  forall n : nat, (n =? n) = true.
Proof. Admitted.

Theorem eqb_eq :
  forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

Definition is_even_prime n :=
  if n =? 2 then true
  else false.

Example even_10 : Even 10.
Proof.
  unfold Even.
  exists 5.
  reflexivity.
Qed.

Example even_10' : even 10 = true.
Proof. reflexivity. Qed.

Example even_10'' : Even 10.
Proof. apply even_bool_prop. reflexivity. Qed.

Example not_even_11 : even 11 = false.
Proof. reflexivity. Qed.

Example not_even_11' : ~(Even 11).
Proof.
  (* text uses rewrite <- even_bool_prop. which does not work *)
Admitted.

Lemma plus_eqb_example :
  forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  intros n m p H.
  (* text uses rewrite eqb_eq in H. which does not work *)
Admitted.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Notation "x && y" := (andb x y).

Theorem andb_true_iff :
  forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - (* -> *)
    {
      destruct b1.
      + (* b1 = true *)
        {
          destruct b2.
          * (* b2 = true *) split. reflexivity. reflexivity.
          * (* b2 = false *) intros H. inversion H.
        }
      + (* b1 = false *) intros H. inversion H.
   }
 - (* <- *)
   {
     destruct b1.
     + (* b1 = true *)
       {
         destruct b2.
         * (* b2 = true *) split.
         * (* b2 = false *) intros H. inversion H. discriminate H1.
       }
     + (* b1 = false *) intros H. inversion H. discriminate H0.
   }
Qed.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Notation "x || y" := (orb x y).

Theorem orb_true_iff :
  forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - (* -> *)
    {
      destruct b1.
      + (* b1 = true *)
        {
          destruct b2.
          * (* b2 = true *) right. reflexivity.
          * (* b2 = false *) left. reflexivity.
        }
      + (* b1 = false *)
        {
          destruct b2.
          * (* b2 = true *) right. reflexivity.
          * (* b2 = false *) intros H. discriminate H.
        }
    }
  - (* <- *)
    {
      destruct b1.
      + (* b1 = true *)
        {
          destruct b2.
          * (* b2 = true *) intros H. reflexivity.
          * (* b2 = false *) intros H. reflexivity.
        }
      + (* b1 = false *)
        {
          destruct b2.
          * (* b2 = true *) intros H. reflexivity.
          * (* b2 = false *)
            {
              intros H. inversion H.
              discriminate H0. discriminate H0.
            }
        }
    }
Qed.

Fixpoint beq_nat n m {struct n} : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => beq_nat n1 m1
  end.

Lemma beq_nat_refl : forall n, true = beq_nat n n.
Proof.
  intro x; induction x; simpl in |- *; auto.
Qed.

Definition beq_nat_eq : forall x y, true = beq_nat x y -> x = y.
Proof. Admitted.

Lemma beq_nat_true : forall x y, beq_nat x y = true -> x=y.
Proof. Admitted.

Theorem eqb_neq :
  forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y. split.
  - (* -> *)
    {
      intros H G.
      rewrite G in H.
      rewrite <- beq_nat_refl in H.
      inversion H.
    }
  - (* <- *)
    {
      intros H.
      destruct (beq_nat x y) eqn:G.
      apply beq_nat_true in G.
      apply H in G. destruct G. assumption.
    }
Qed.

Fixpoint eqb_list {A : Type}
  (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1 with
  | [] => match l2 with
         | [] => true
         | _ => false
         end
  | h1 :: t1 => match l2 with
              | [] => false
              | h2 :: t2 => eqb h1 h2 && eqb_list eqb t1 t2
              end
  end.
                  

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
  (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
  forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb H. 
  induction l1 as [|h1 t1 IHl1].
  - split.
    + (* l1 = [] *) intros G. destruct l2 as [|h2 t2].
      * (* l2 = [] *) reflexivity.
      * (* l2 = h2 :: t2 *) inversion G.
    + (* l1 = h1 :: t1 *) intros G. destruct l2 as [|h2 t2].
      * (* l2 = [] *) reflexivity.
      * (* l2 = h2 :: t2 *) inversion G.
  - induction l2 as [|h2 t2].
    + (* l2 = [] *) split.
      * (* -> *) intros G. inversion G.
      * (* <- *) intros G. inversion G.
    + (* l2 = h2 :: t2 *) simpl. split.
      * (* -> *)
        {
          intros G.
          apply andb_true_iff in G. destruct G as [G1 G2].
          apply IHl1 in G2.
          apply H in G1.
          rewrite <- G1. rewrite <- G2.
          reflexivity.
        }
      * (* <- *)
        {
          intros G. inversion G.
          apply andb_true_iff.
          split.
          - (* -> *) apply H. reflexivity.
          - (* <- *) rewrite <- H2. apply IHl1. reflexivity.
        }
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof. Admitted.
(* this section was taking too long, so I gave up,
   I am just doing this for fun anyway *)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

Print Assumptions function_equality_ex2.
(*
Axioms:
functional_extensionality
  : forall (X Y : Type) (f g : X -> Y),
(forall x : X, f x = g x) -> f = g
add_comm : forall n m : nat, n + m = m + n
*)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Theorem app_assoc :
  forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n. induction l as [|A' l' IHl'].
  - (* l = [] *) simpl; reflexivity.
  - (* l = l' *)
    {
      simpl; rewrite -> IHl'.
      reflexivity.
    }
Qed.

Theorem tr_rev_correct :
  forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  unfold tr_rev.
  intros x. induction x as [|h t IH].
  - (* x = [] *) reflexivity.
  - (* x = h :: t *)
    {
      simpl. rewrite <- IH.
      assert ( H: forall T l1 l2, @rev_append T l1 l2 = @rev_append T l1 [] ++ l2).
      { intros T. induction l1 as [|h1 t1 IH1].
        - (* l1 = [] *) simpl; reflexivity.
        - (* l1 = h1 :: t1*)
          {
            simpl. rewrite -> IH1.
            intros l2.
            rewrite -> (IH1 (h1 :: l2)).
            rewrite <- app_assoc.
            reflexivity.
          }
      }
      apply H.
    }
Qed.