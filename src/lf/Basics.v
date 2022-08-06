Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d : day) : day :=
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

Example test_next_weekday :
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.


Definition negb' (b : bool) : bool :=
  if b then false
  else true.

Example test_negb1 : (negb true) = false.
Proof. simpl. reflexivity. Qed.

Example test_negb2 : (negb false) = true.
Proof. simpl. reflexivity. Qed.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition andb' (b1 : bool) (b2 : bool) : bool :=
  if b1 then b2
  else false.

Notation "x && y" := (andb x y).

Example test_andb1 : (andb true false) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb2 : (andb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb3 : (andb false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb4 : (andb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb5 : true && true && false = false.
Proof. simpl. reflexivity. Qed.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Definition orb' (b1 : bool) (b2 : bool) : bool :=
  if b1 then true
  else b2.

Notation "x || y" := (orb x y).

Example test_orb1 : (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2 : (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb3 : (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4 : (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb5 : false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1 : bool) (b2 : bool) : bool := 
  negb (andb b1 b2).

Example test_nandb1 : (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2 : (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3 : (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4 : (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
  andb b1 (andb b2 b3).

Example test_monochrome : (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32 : (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33 : (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34 : (andb3 true true false) = false.
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

Example test_monochrome1 : (monochrome (black)) = true.
Proof. simpl. reflexivity. Qed.

Example test_monochrome2 : (monochrome (white)) = true.
Proof. simpl. reflexivity. Qed.

Example test_monochrome3 : (monochrome (primary blue)) = false.
Proof. simpl. reflexivity. Qed.

Definition isred (c : color) : bool :=
  match c with
  | primary red => true
  | _ => false
  end.

Compute (isred (primary red)).
Compute (isred (black)).
Compute (isred (white)).
Compute (isred (primary blue)).
Compute (isred (primary green)).

Example test_isred1 : (isred (primary red)) = true.
Proof. simpl. reflexivity. Qed.

Example test_isred2 : (isred (primary blue)) = false.
Proof. simpl. reflexivity. Qed.

Example test_isred3 : (isred black) = false.
Proof. simpl. reflexivity. Qed.

Module Playground.
  Definition b : rgb := blue.
End Playground.

Definition b : bool := true.

Check Playground.b : rgb.
Check b : bool.

Module TuplePlayground.
  Inductive bit : Type :=
    | B0
    | B1.

  Inductive nybble : Type :=
    | bits (b0 b1 b2 b3 : bit).
  
  Check (bits B1 B0 B1 B0)
    : nybble.

  Definition all_zero (nb : nybble) : bool :=
    match nb with
    | bits B0 B0 B0 B0 => true
    | _ => false
    end.

  Compute (all_zero (bits B1 B0 B1 B0)).

  Compute (all_zero (bits B0 B0 B0 B0)).
End TuplePlayground.

Module NatPlayground.
  Inductive nat : Type :=
    | O
    | S (n : nat).

  Inductive nat' : Type :=
    | stop
    | tick (foo : nat').

  Definition pred (n : nat) : nat :=
    match n with  
    | O => O
    | S n' => n'
    end.
End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Check S : nat -> nat.
Check pred : nat -> nat.
Check minustwo : nat -> nat.

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n : nat) : bool :=
  negb (even n).

Example test_odd1 : odd 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_odd2 : odd 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

  Compute (plus 3 2).

  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O, _ => O
    | _, O => n
    | S n', S m' => minus n' m'
    end.
End NatPlayground2.

Fixpoint exp (b p : nat) : nat :=
  match p with
  | O => S O
  | S p' => mult b (exp b p')
  end.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n') 
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                    (at level 50, left associativity)
                    : nat_scope.

Notation "x - y" := (minus x y)
                    (at level 50, left associativity)
                    : nat_scope.

Notation "x * y" := (mult x y)
                    (at level 40, left associativity)
                    : nat_scope.

Check ((0 + 1) + 1) : nat.

Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => eqb n' m'
  | _, _ => false
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Example test_eqb1 : eqb 0 0 = true.
Proof. simpl. reflexivity. Qed.

Example test_eqb2 : eqb 1 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_eqb3 : eqb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Example test_eqb4 : 1 =? 1 = true.
Proof. simpl. reflexivity. Qed.

Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | O, _ => true
  | S n', S m' => leb n' m'
  | _, _ => false
  end.

Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb1 : leb 0 0 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2 : leb 1 3 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb3 : leb 5 2 = false.
Proof. simpl. reflexivity. Qed.

Example test_leb4 : 1 <=? 2 = true.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool :=
  if eqb n m then false
  else leb n m.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1 : ltb 0 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_ltb2 : ltb 0 0 = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb3 : ltb 5 2 = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb4 : 1 <? 2 = true.
Proof. simpl. reflexivity. Qed.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_0_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_0_n'' : forall n : nat, 0 + n = n.
Proof.
  intros m. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat,
  n = m ->
  n + m = m + m.

Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m ->
  m = o ->
  n + m = m + o.

Proof.
  intros n m o.
  intros H.
  intros G.
  rewrite -> H.
  rewrite -> G.
  reflexivity. Qed.

Check mult_n_O.

Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn : E.
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn : E.
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn : Eb.
  - destruct c eqn : Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn : Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn : Eb.
  { destruct c eqn : Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn : Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

Theorem andb3_exchange : forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn : Eb.
  - destruct c eqn : Ec.
    { destruct d eqn : Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn : Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn : Ec.
    { destruct d eqn : Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn : Ed.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct c eqn : Ec.
  - reflexivity.
  - intros H. rewrite <- H. destruct b eqn : Eb.
    + reflexivity.
    + reflexivity.
Qed.

Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative'' : forall b c,
  andb c b = andb b c.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [|n].
    - reflexivity.
    - reflexivity.
Qed.

(* Level means precendence level, 1 + 2 * 3 * 4 -> (1 + ((2 * 3) * 4)) *)
(* Coq tries to understand context with scopes, type_scope *)
Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.

Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.
