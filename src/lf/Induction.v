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
