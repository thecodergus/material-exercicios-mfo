Theorem add_0_r: forall n : nat,
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

(* Theorem mul_comm : forall m n : nat,
    m * n = n * m.
Proof.
    intros m n. 
    induction m as [| m' IHm'].
        induction n as [| n' IHn'].
            reflexivity.
            simpl. rewrite <- IHn'. reflexivity.
        induction n as [| n' IHn'].
            simpl. rewrite IHm'. reflexivity.
            simpl. rewrite <- IHn'.
            rewrite (IHm' (S n')).
Qed. *)

Theorem mul_comm : forall a b, a * b = b * a.
Proof.
  induction a.
  (* Case Z *)
    induction b.
      (* Case Z *)   reflexivity.
      (* Case S b *) simpl. rewrite <- IHb. reflexivity.
  (* Case S a *)
    induction b.
      (* Case Z *)
        simpl. rewrite (IHa 0). reflexivity.
      (* Case S b *)
        simpl. rewrite <- IHb.
        rewrite (IHa (S b)).
        simpl. rewrite (IHa b).
        rewrite (plus_assoc b a (b * a)).
        rewrite (plus_assoc a b (b * a)).
        rewrite (plus_comm a b).
        reflexivity.
Qed.