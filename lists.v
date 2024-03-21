Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Check (pair 7 8) : natprod.

Notation "( x , y )" := (pair x y).

Definition fst (p : natprod) : nat :=
  match p with
  | (x, _) => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | (_, y) => y
  end.

Compute (fst (pair 3 5)).
Compute (fst (3,5)).
(* = 3 : nat *)

Theorem surjective_pairing :
  forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m].
  simpl; reflexivity.
Qed.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem snd_fst_is_swap :
  forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m].
  simpl; reflexivity.
Qed.

Theorem fst_swap_is_snd :
  forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [n m].
  simpl; reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Compute repeat 3 2.
(* = [3;3] : natlist *)
Compute repeat 8 0.
(* = [] : natlist *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end.

Compute length [].
(* = 0 : nat *)
Compute length [1;2;3].
(* = 3 : nat *)
Compute length (repeat 1 20).
(* = 20 : nat *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | [] => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Compute [1;2;3] ++ [4;5].
(* [1;2;3;4;5] : natlist *)
Compute [] ++ [1].
(* [1] : natlist *)
Compute [1] ++ [].
(* [1] : natlist *)
Compute [] ++ [].
(* [] : natlist *)

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: _ => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | _ :: t => t
  end.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | [] => []
  | 0 :: t => nonzeros t
  | h :: t => h :: (nonzeros t)
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | [] => []
  | h :: t =>
    if (even h)
      then (oddmembers t)
      else h :: (oddmembers t)
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | [], l2 => l2
  | l1, [] => l1
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

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

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | [] => 0
  | h :: t =>
    if (v =? h)
      then S (count v t)
      else (count v t)
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag :=
  v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint member (v : nat) (s : bag) : bool :=
  match s with
  | [] => false
  | h :: t =>
    if (v =? h)
      then true
      else (member v t)
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | [] => []
  | h :: t =>
    if (v =? h)
      then t
      else h :: (remove_one v t)
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | [] => []
  | h :: t =>
    if (v =? h)
      then (remove_all v t)
      else h :: (remove_all v t)
  end.

Example test_remove_all1:
  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all2:
  count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all3:
  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_all4:
  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint included (s1 : bag) (s2 : bag) : bool :=
  match s1 with
  | [] => true
  | v :: t =>
    match (member v s2) with
    | true => included t (remove_one v s2)
    | false => false
    end
  end.

Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Theorem eqb_refl :
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

Theorem add_inc_count :
  forall l : bag, forall v : nat,
  S (count v l) = count v (add v l).
Proof.
  intros l v. induction l as [|n l' IHl'].
  - simpl. induction v as [|v' IHv'].
    + simpl. reflexivity.
    + simpl. rewrite -> eqb_refl. reflexivity.
  - induction v as [|v' IHv'].
    + simpl. reflexivity.
    + induction n as [|n' IHn'].
      * simpl; rewrite -> eqb_refl. reflexivity.
      * simpl; rewrite -> eqb_refl. reflexivity.
Qed.

Theorem nil_app :
  forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred :
  forall l : natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = [] *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.
Qed.

Theorem app_assoc :
  forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = [] *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | [] => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.

Example test_rev2: rev [] = [].
Proof. reflexivity. Qed.

Theorem app_length :
  forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = [] *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem add_0_r :
  forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm :
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

Theorem rev_length :
  forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = cons *)
    {
      simpl. rewrite -> app_length.
      simpl. rewrite -> IHl'.
      rewrite add_comm.
      reflexivity.
    }
Qed.

Search rev.
Search (?x + ?y = ?y + ?x).

Theorem app_nil_r :
  forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [|n' l' IHl'].
  - (* l = [] *) simpl; reflexivity.
  - (* l = n' l' IHl' *)
    {
      simpl; rewrite -> IHl'.
      reflexivity.
    }
Qed.

Theorem rev_app_distr:
  forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [|n1' l1' IHl1'].
  - (* l1 = [] *)
    {
      simpl; rewrite -> app_nil_r.
      reflexivity.
    }
  - (* l1 = n1' l1' IHl1' *)
    {
      simpl; rewrite -> IHl1'.
      rewrite -> app_assoc.
      reflexivity.
    }
Qed.

Theorem rev_involutive :
  forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [|n' l' IHl'].
  - (* l = [] *) simpl; reflexivity.
  - (* l = n' l' IHl' *)
    {
      simpl; rewrite -> rev_app_distr.
      simpl; rewrite -> IHl'.
      reflexivity.
    }
Qed.

Theorem app_assoc4 :
  forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  reflexivity.
Qed.

Lemma nonzeros_app :
  forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [|n1' l1' IHl1'].
  - (* l1 = [] *) simpl; reflexivity.
  - (* l1 = n1 l1 IHl1 *)
    {
      simpl; rewrite -> IHl1'. destruct n1'.
      + reflexivity.
      + simpl; reflexivity.
    }
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ :: l2' => false
  | _ :: l1', [] => false
  | x :: l1', y :: l2' =>
    if (eqb x y)
      then (eqblist l1' l2')
      else false
  end.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. simpl; reflexivity. Qed.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. simpl; reflexivity. Qed.

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. simpl; reflexivity. Qed.

Theorem eqblist_refl :
  forall l:natlist,
  true = eqblist l l.
Proof.
  intros l. induction l as [|n' l' IHl'].
  - (* l = [] *) simpl; reflexivity.
  - (* l = n' l' *)
    {
      simpl.
      rewrite -> eqb_refl.
      assumption. (* IHl' *)
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

Theorem count_member_nonzero :
  forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros s. induction s as [|n' s' IHs'].
  - (* s = [] *) simpl; reflexivity.
  - (* s = n' s' *) simpl; reflexivity.
Qed.

Theorem leb_n_Sn :
  forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.
    
Theorem remove_does_not_increase_count:
  forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s. induction s as [|n' s' IHs'].
  - (* s = [] *) simpl; reflexivity.
  - (* s = n' s' *)
    {
      induction n' as [|n'' IHn''].
      + (* n' = 0 *)
        {
          simpl; rewrite -> leb_n_Sn.
          reflexivity.
        }
      + (* n' = n'' IHn'' *)
        {
          simpl. rewrite -> IHs'.
          reflexivity.
        }
    }
Qed.

Theorem involution_injective :
  forall (f : nat -> nat),
  (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
  intros f H n1 n2 H1.
  rewrite -> H, <- H1.
  rewrite <- H.
  reflexivity.
Qed.

Theorem rev_injective :
  forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' =>
    match n with
      | O => Some a
      | S n' => nth_error l' n'
    end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. simpl; reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. simpl; reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. simpl; reflexivity. Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption :=
  nth_error l 0.

Example test_hd_error1 : hd_error [] = None.
Proof. simpl; reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. simpl; reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. simpl; reflexivity. Qed.

Theorem option_elim_hd :
  forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default. induction l as [|n' l' IHl'].
  - (* l = [] *) simpl; reflexivity.
  - (* l = n' l' *) simpl; reflexivity.
Qed.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl :
  forall x, eqb_id x x = true.
Proof.
  intros x. destruct x.
  simpl; rewrite -> eqb_refl.
  reflexivity.
Qed.

Fixpoint beq_nat n m {struct n} : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => beq_nat n1 m1
  end.

Lemma beq_nat_refl :
  forall n, true = beq_nat n n.
Proof.
  intro x; induction x; simpl in |- *; auto.
Qed.

Definition beq_nat_eq : forall x y, true = beq_nat x y -> x = y.
Proof.
  induction x; induction y; simpl in |- *.
    reflexivity.
    intros. discriminate H.
    intros. discriminate H.
    intros. case (IHx _ H). reflexivity.
Defined.

Theorem eqb_id_equiv :
  forall n : nat,
  eqb_id (Id n) (Id n) = beq_nat n n.
Proof. intros n. simpl. reflexivity. Qed.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update
  (d : partial_map) (x : id) (value : nat) : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' =>
    if eqb_id x y
      then Some v
      else find x d'
  end.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
  find x (update d x v) = Some v.
Proof.
Admitted.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
  eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o H. induction d.
  - (* d = empty *) simpl. rewrite -> H. reflexivity.
  - (* d = record i v d' *) simpl. rewrite -> H. reflexivity.
Qed.

End NatList.