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