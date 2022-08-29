From LF Require Export Basics.

Theorem add_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_n_n : forall n, minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn' ].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn' ].
  - simpl. rewrite -> add_0_r. reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn' ].
    - reflexivity.
    - simpl. rewrite -> IHn'. reflexivity. 
Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n. induction n as [| n' IHn' ].
  - reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. 
Qed.

Theorem eqb_refl : forall n : nat, (n =? n) = true.
Proof.
  intros n. induction n as [| n' IHn' ].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem even_S : forall n : nat, even (S n) = negb (even n).
Proof.
  intros n. induction n as [| n' IHn' ].
  - reflexivity.
  - rewrite -> IHn'. rewrite -> negb_involutive. reflexivity.  
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite IHn'. reflexivity. Qed.

  Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

(*
Theorem: Addition is commutative
Proof: By induction on n
- First, suppose n = 0, we must show that:
    0 + m = m + 0
  This follows directly from the definition of +.
- Then, suppose n = S n', we must show that:
    S n' + m = m + S n'
  By definition of +, this follows from
    S (n' + m) = S (m + n')
  which immediate from the induction hypothesis. Qed.
*)

(*
Theorem: (n =? n) = true for any n.
Proof: By induction on n
- First, suppose n = 0, we must show that:
    (0 =? 0) = true
  This follows directly from the definition of =?.
- Then, suppose n = S n', we must show that:
    (S n' =? S n') = true
  By definition of +, this follows from
    (n' =? n') = true
  which immediate from the induction hypothesis. Qed.
*)

Theorem add_shuffle3 : forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H: n + p = p + n).
    { rewrite add_comm. reflexivity. }
  rewrite -> H.
  rewrite -> add_comm.
  rewrite -> add_assoc.
  reflexivity.
Qed.

Theorem mul_comm : forall m n : nat, m * n = n * m.
Proof.
  intros m n.
  assert (H: forall p q : nat, p * S q = p + p * q).
    { intros p q. induction p as [| p' IHp' ].
      - reflexivity.
      - simpl. rewrite -> IHp'. rewrite -> add_shuffle3. reflexivity. }

  induction n as [| n' IHn' ].
  - simpl. rewrite -> mult_0_r. reflexivity.
  - simpl. rewrite -> H. rewrite -> IHn'. reflexivity.
Qed.

Check leb.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p H. induction p as [| p' IHp' ].
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IHp'. reflexivity.   
Qed.

Theorem leb_refl : forall n : nat, (n <=? n) = true.
Proof.
  intros n. induction n as [| n' IHn' ].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem zero_neqb_S : forall n : nat, 0 =? (S n) = false.
Proof.
  intros n. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool, andb b false = false.
Proof.
  intros b. destruct b.
    - reflexivity.
    - reflexivity.
Qed.

Theorem S_neqb_0 : forall n : nat, (S n) =? 0 = false.
Proof.
  intros n. reflexivity.
Qed.

Theorem mult_1_l : forall n : nat, 1 * n = n.
Proof.
  intros n. destruct n.
  - reflexivity.
  - simpl. rewrite -> add_0_r. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c. destruct b.
    - destruct c.
      + reflexivity.
      + reflexivity.
    - destruct c.
      + reflexivity.
      + reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [| n' IHn' ].
  - reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> add_assoc. reflexivity. 
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [| n' IHn' ].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> mult_plus_distr_r.
    reflexivity.
Qed.

Theorem add_shuffle3' : forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  replace (n + p) with (p + n).
  - rewrite -> add_comm. rewrite -> add_assoc. reflexivity.
  - rewrite -> add_comm. reflexivity.
Qed.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b.
  assert (H: forall p q : nat, S (S (p + q)) = S p + S q).
    { intros p q. induction p as [| p' IHp' ].
      - reflexivity.
      - simpl. rewrite -> IHp'. reflexivity. }
  induction b as [| c' IHc' | b' IHb' ].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite -> IHb'. rewrite -> H. reflexivity.
Qed.

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | 0 => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n. induction n as [| n' IHn' ].
  - reflexivity.
  - simpl. rewrite -> bin_to_nat_pres_incr. rewrite -> IHn'. reflexivity. 
Qed.

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
  intros n. reflexivity. 
Qed.

Definition double_bin (b : bin) : bin :=
  match b with
  | Z => Z
  | b => B0 b
  end.

Example double_bin_zero : double_bin Z = Z.
Proof. simpl. reflexivity. Qed.

Lemma double_incr_bin : forall b,
  double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
  - reflexivity. 
Qed.

Theorem bin_nat_bin_fails : ∀ b, nat_to_bin (bin_to_nat b) = b.
Abort.

(* The bin_nat_bin theorem fails because it also can accept bin
  with trailing zeros to the left, so no all the cases of
  bin -> nat -> bin are equal *)