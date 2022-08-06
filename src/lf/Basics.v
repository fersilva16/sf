Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d: day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.
  
Compute (next_weekday friday).

Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | false => true
  end.


Definition negb' (b: bool) : bool :=
  if b then false
  else true.

Example test_negb1: (negb true) = false.
Proof. simpl. reflexivity. Qed.

Example test_negb2: (negb false) = true.
Proof. simpl. reflexivity. Qed.

Definition andb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition andb' (b1: bool) (b2: bool) : bool :=
  if b1 then b2
  else false.

Notation "x && y" := (andb x y).

Example test_andb1: (andb true false) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb2: (andb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb3: (andb false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb4: (andb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb5: true && true && false = false.
Proof. simpl. reflexivity. Qed.

Definition orb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Definition orb' (b1: bool) (b2: bool) : bool :=
  if b1 then true
  else b2.

Notation "x || y" := (orb x y).

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1: bool) (b2: bool) : bool := 
  negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1: bool) (b2: bool) (b3: bool) : bool :=
  andb b1 (andb b2 b3).

Example test_monochrome: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.
Check true : bool.
Check (negb true) : bool.
Check negb : bool -> bool.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | primary p => false
  | _ => true
  end.

Example test_monochrome1: (monochrome (black)) = true.
Proof. simpl. reflexivity. Qed.

Example test_monochrome2: (monochrome (white)) = true.
Proof. simpl. reflexivity. Qed.

Example test_monochrome3: (monochrome (primary blue)) = false.
Proof. simpl. reflexivity. Qed.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Compute (isred (primary red)).
Compute (isred (black)).
Compute (isred (white)).
Compute (isred (primary blue)).
Compute (isred (primary green)).

Example test_isred1: (isred (primary red)) = true.
Proof. simpl. reflexivity. Qed.

Example test_isred2: (isred (primary blue)) = false.
Proof. simpl. reflexivity. Qed.

Example test_isred3: (isred black) = false.
Proof. simpl. reflexivity. Qed.
