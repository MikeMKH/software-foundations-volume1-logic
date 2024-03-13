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