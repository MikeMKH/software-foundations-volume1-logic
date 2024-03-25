Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list : Type -> Type.
Check (nil nat) : list nat.
Check (cons nat 3 (nil nat)) : list nat.

Check nil : forall X : Type, list X.
Check cons : forall X : Type, X -> list X -> list X.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. simpl; reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. simpl; reflexivity. Qed.

Module MumbleGrumble.
Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.
Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).
(* Check d (b a 5). The term "b a 5" has type "mumble" while it is expected to have type "Type". *)
Check d mumble (b a 5). (* : grumble mumble *)
Check d bool (b a 5). (* : grumble bool *)
Check e bool true. (* : grumble bool *)
Check e mumble (b c 0). (* : grumble mumble *)
(* Check e bool (b c 0). The term "b c 0" has type "mumble" while it is expected to have type "bool". *)
Check c. (* : mumble *)
End MumbleGrumble.

(* interface *)
Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Definition list123' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat'' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat'' x count')
  end.

Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').
  
Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. simpl; reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. simpl; reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. simpl; reflexivity. Qed.

Fail Definition mynil := nil.

Definition mynil : list nat := nil.

Check @nil : forall X : Type, list X.
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
  (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
  (at level 60, right associativity).

Definition list123'' := [1; 2; 3].

Theorem app_nil_r :
  forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l. induction l as [|X' l' IHl'].
  - (* l = [] *) simpl; reflexivity.
  - (* l = l' *)
    {
      simpl; rewrite -> IHl'.
      reflexivity.
    }
Qed.

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

Lemma app_length :
  forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2. induction l1 as [|X' l1' IHl1'].
  - (* l1 = [] *) simpl; reflexivity.
  - (* l1 = l1' *)
    {
      simpl; rewrite -> IHl1'.
      reflexivity.
    }
Qed.

Theorem rev_app_distr:
  forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1 as [|x' l1' IHl1'].
  - (* l1 = [] *)
    {
      simpl; rewrite -> app_nil_r.
      reflexivity.
    }
  - (* l1 = l1' *)
    {
      simpl; rewrite -> IHl1'.
      rewrite <- app_assoc.
      reflexivity.
    }
Qed.

Theorem rev_involutive :
  forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l. induction l as [|x' l' IHl'].
  - (* l = [] *) simpl; reflexivity.
  - (* l = x' l' *)
    {
      simpl. rewrite -> rev_app_distr.
      rewrite -> IHl'.
      simpl; reflexivity.
    }
Qed.