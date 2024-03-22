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