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

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Check @combine.
(* : forall X Y : Type, list X -> list Y -> list (X * Y) *)

Compute (combine [1;2] [false;false;true;true]).
(* [(1, false); (2, false)] : list (nat * bool) *)

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t => (x :: (fst (split t)), y :: (snd (split t)))
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. simpl; reflexivity. Qed.

Module OptionPlayground.
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.
Arguments Some {X}.
Arguments None {X}.
End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat): option X :=
  match l with
  | [] => None
  | a :: l' =>
    match n with
    | O => Some a
    | S n' => nth_error l' n'
    end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. simpl; reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. simpl; reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. simpl; reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | a :: _ => Some a
  end.

Definition hd_error' {X : Type} (l : list X) : option X :=
  nth_error l 0.

Check @hd_error : forall X : Type, list X -> option X.
(* : forall X : Type, list X -> option X *)

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. simpl; reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. simpl; reflexivity. Qed.

Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

Check @doit3times : forall X : Type, (X -> X) -> X -> X.

Example test_doit3times: doit3times (fun x => x -2) 9 = 3.
Proof. simpl; reflexivity. Qed.
Example test_doit3times': doit3times negb true = false.
Proof. simpl; reflexivity. Qed.

Fixpoint filter {X:Type} (test: X -> bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
  negb (even n).

Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. simpl; reflexivity. Qed.

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

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.
  
Example test_filter2:
  filter length_is_1 [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
    = [ [3]; [4]; [8] ].
Proof. simpl; reflexivity. Qed.

Definition countoddmembers (l:list nat) : nat :=
  length (filter odd l).
  
Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl; reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. simpl; reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
Proof. simpl; reflexivity. Qed.

Fixpoint leb n m : bool :=
  match n, m with
    | 0, _ => true
    | _, 0 => false
    | S n', S m' => leb n' m'
  end.

Definition ltb n m := leb (S n) m.

Infix "<=?" := leb (at level 70) : nat_scope.
Infix "<?" := ltb (at level 70) : nat_scope.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => andb (even x) (7 <=? x)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. simpl; reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. simpl; reflexivity. Qed.

Definition partition
  {X : Type} (test : X -> bool) (l : list X) : list X * list X :=
  (filter test l, filter (fun x => negb(test x)) l).

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. simpl; reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. simpl; reflexivity. Qed.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. simpl; reflexivity. Qed.
Example test_map2:
  map odd [2;1;2;5] = [false;true;false;true].
Proof. simpl; reflexivity. Qed.
Example test_map3: map (fun n => [even n;odd n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. simpl; reflexivity. Qed.

Theorem map_app_distr :
  forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.                       
Proof.
  intros X Y f l1 l2. induction l1 as [|x' l1' IHl1'].
  - (* l1 = [] *) simpl; reflexivity.
  - (* l1 = x' :: l1' *)
    {
      simpl; rewrite -> IHl1'.
      reflexivity.
    }
Qed.

Theorem map_rev :
  forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l as [|x' l' IHl'].
  - (* l = [] *) simpl; reflexivity.
  - (* l = x' :: l' *)
    {
      simpl; rewrite -> map_app_distr.
      simpl; rewrite -> IHl'.
      reflexivity.
    }
Qed.

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) ++ (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. simpl; reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold andb) : list bool -> bool -> bool.

Example fold_example1 :
  fold andb [true;true;false;true] true = false.
Proof. simpl; reflexivity. Qed.
Example fold_example2 :
  fold mult [1;2;3;4] 1 = 24.
Proof. simpl; reflexivity. Qed.
Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. simpl; reflexivity. Qed.
Example fold_example4 :
  fold (fun x m => x - m) [9;8;2;1] 0 = 2.
  (* 9-(8-(2-(1-0))) *)
Proof. simpl; reflexivity. Qed.

Definition count {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example count_example1 :
  count [1;2;3;4;5] = 5.
Proof. simpl; reflexivity. Qed.
Example count_example2 :
  count [true;false;false] = 3.
Proof. simpl; reflexivity. Qed.
Example count_example3 :
  count ([] : list nat) = 0.
Proof. simpl; reflexivity. Qed.

Module Exercises.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0. (* funny this is exactly what I did for count *)
  
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. simpl; reflexivity. Qed.

Theorem cons_app_equiv :
  forall (X : Type) (l : list X) (x : X),
  x::l = [x] ++ l.
Proof.                           
  intros X l x. induction l as [|x' l' IHl'].
    + (* l = [] *) simpl; reflexivity.
    + (* l = x' :: l' *) simpl; reflexivity.
Qed.

Lemma fold_length_distr :
  forall (X : Type) (l1 l2 : list X),
  fold_length (l1 ++ l2) = fold_length l1 + fold_length l2.
Proof.
  intros X l1 l2. induction l1 as [|x1' l1' IHl1'].
    + (* l1 = [] *) simpl; reflexivity.
    + (* l1 = x1' :: l1' *)
      {
        unfold fold_length in *.
        simpl; rewrite -> IHl1'.
        reflexivity.
      }
Qed.

Theorem fold_length_correct :
  forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l. induction l as [|x' l' IHl'].
  - (* l = [] *) reflexivity.
  - (* l = x' :: l' *)
    {
      rewrite -> cons_app_equiv.
      rewrite -> fold_length_distr.
      simpl; rewrite -> IHl'.
      reflexivity.
    }
Qed.
