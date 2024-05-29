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

Theorem ev_inversion :
  forall (n : nat),
  ev n -> (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

Theorem evSS_ev :
  forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H. apply ev_inversion in H. destruct H as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnm Hev]]. injection Hnm as Heq.
    rewrite Heq. apply Hev.
Qed.

Theorem evSS_ev' :
  forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [|n' E' Heq].
  (* We are in the E = ev_SS n' E' case now. *)
  apply E'.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H. destruct H as [| [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof.
  intros H. inversion H.
Qed.

Theorem SSSSev__even :
  forall n, ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H as [|n' H' Heq'].
  inversion H' as [|n'' H'' Heq''].
  apply H''.
Qed.

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H. inversion H1. inversion H3.
Qed.

Theorem inversion_ex1 :
  forall (n m o : nat), [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H.
  inversion H. reflexivity.
Qed.

Theorem inversion_ex2 :
  forall (n : nat), S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra.
Qed.

Definition Even x := exists n : nat, x = double n.

Lemma ev_Even :
  forall n, ev n -> Even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    unfold Even. exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : Even n' *)
    unfold Even in IH.
    destruct IH as [k Hk].
    rewrite Hk.
    unfold Even. exists (S k). simpl. reflexivity.
Qed.

Theorem exists_example_2 :
  forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm]. (* note the implicit destruct here *)
  exists (2 + m).
  apply Hm.
Qed.

Theorem dist_not_exists :
  forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  unfold not. intros X P H [x NP].
  apply NP. apply H.
Qed.

Theorem dist_exists_or :
  forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - (* -> *)
    {
      intros [x [PX | QX]].
      + (* PX *) left. exists x. assumption.
      + (* QX *) right. exists x. assumption.
    }
  - (* <- *)
    {
      intros [[x PX] | [x QX]].
      + (* x PX *) exists x. left. assumption.
      + (* x QX *) exists x. right. assumption.
    }
Qed.

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
  forall n, In n [2; 4] -> exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  (* n = n' + (n' + 0) *)
  - (* n = 2 *)
    exists 1. rewrite <- H. reflexivity.
  - (* n = 4 *)
    exists 2. rewrite <- H. reflexivity.
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
  - (* l = [], contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + (* x' = x *)
      rewrite H. left. reflexivity.
    + (* In x l' *)
      right. apply IHl'. assumption.
Qed.

Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  { induction l as [|x l' IHl'].
  (* -> *)
  - (* [] *)
    simpl. intros [].
  - (* x :: l' *)
    simpl. intros [H | H].
    + (* f x = y *)
      exists x. split.
      * assumption.
      * left. reflexivity.
    + (* In y (map f l') *)
      {
        apply IHl' in H. destruct H as [w [Fw Iw]].
        exists w. split.
        * assumption.
        * right. assumption.
      }
  }
  (* <- *)
  intros [w [Fw Iw]].
  rewrite <- Fw. apply In_map.
  assumption.
Qed.