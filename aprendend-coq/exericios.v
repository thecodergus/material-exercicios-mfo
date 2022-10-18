Theorem plus_0_r: forall n : nat,
    n + 0 = n.
Proof.
    intro n. induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n : nat,
    n * 0 = 0.
Proof.
    intro n. induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
    intros n m. induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
    n + m = m + n.
Proof.
    intros n m. induction n as [| n' IHn']. 
    - simpl. rewrite add_0_r. reflexivity.
    - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.  
Qed.

Theorem add_assoc : forall n m p, 
    n + (m + p) = (n + m) + p.
Proof.
    intros n m p. induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_shuffle3 : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
    intros n m p. induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.

Lemma S_num : forall n : nat,
    S n = n + 1.
Proof.
    intro n. induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

(* Theorem mult_nm : forall n m : nat,
  n * S m = n + n * m.
Proof.
  intros n m. induction n as [|n' IH].
  - reflexivity.
  - simpl. rewrite IH. rewrite plus_swap.
    reflexivity.
Qed. *)

Lemma plus_comm : forall a b,
    a + b = b + a.
Proof.
    intros a b. induction a as [|a' IHa'].
    - simpl. rewrite plus_0_r. reflexivity.
    - simpl. rewrite <- plus_n_Sm. rewrite IHa'. reflexivity.
Qed.


Lemma plus_swap : forall m n p : nat,
    n + (m + p) = m + (n + p).
Proof.
    intros m n p. induction n as [|n' IHn'].
    - reflexivity.
    - simpl. rewrite IHn'. rewrite <- plus_comm. rewrite plus_n_Sm.
Qed.


Lemma mult_mn : forall m n,
    n * S m = n + n * m.
Proof.
    intros m n. induction n as [|n' IHn'].
    - reflexivity.
    - simpl. rewrite IHn'.
Qed.


Theorem mult_comm : forall m n : nat,
    m * n = n * m.
Proof.
    intros m n. induction m as [| m' IHm'].
    - simpl. rewrite mult_0_r. reflexivity.
    - simpl.
Qed.


