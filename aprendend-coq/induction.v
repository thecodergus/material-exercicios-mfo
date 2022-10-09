Theorem add_0_r : forall n : nat,
    n + 0 = n.
Proof.
    intros n. induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite -> IHn'.
    reflexivity.
Qed.

Theorem minus_n_n : forall n,
    n - n = 0.
Proof.
    intros n. induction n as [| k].
    - reflexivity.
    - simpl. rewrite -> IHk. 
    reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + S m.
Proof.
    intros n m. induction n as [| n'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'.
    reflexivity.
Qed.

Theorem add_comm : forall a b : nat,
    a + b = b + a.
Proof.
    intros a b. induction a as [| a'].
    - simpl. rewrite add_0_r. reflexivity.
    - simpl. rewrite IHa'. rewrite plus_n_Sm.
    reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
    (n + 0 + 0) * m = n * m.
Proof.
    intros n m.
    assert (H: n + 0 + 0 = n).
        {
            rewrite add_comm.
            simpl. rewrite add_comm.
            simpl. reflexivity.
        }
    rewrite -> H.
    reflexivity.        
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
    intros n m p q.
    assert(H: n + m = m + n).
    {
        rewrite add_comm.
        reflexivity.
    }
    rewrite H.
    reflexivity.
Qed.

Theorem add_assoc' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
    intros n m p. induction n as [| n' IHn'].
    reflexivity.
    simpl. rewrite IHn'.
    reflexivity.
Qed.

Theorem add_assoc'' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
    intros n m p. induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite IHn'.
    reflexivity.   
Qed.
