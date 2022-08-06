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
