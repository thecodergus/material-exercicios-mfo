Theorem plus_0_n : forall n : nat,
    0 + n = n.
Proof.
    intros n.
    simpl.
    reflexivity.
Qed.

Theorem plus_0_n': forall n : nat,
    0 + n = n .
Proof.
    intros n.
    reflexivity.
Qed.

(* Exemplo de Erro *)
(* Theorem plus_0_n'' : forall n : nat, 0 + n = 1.
Proof.
    intros m.
    reflexivity.
Qed. *)

Theorem plus_1_l : forall n : nat,
    1 + n = S n.
Proof.
    intros n.
    reflexivity.
Qed.

Theorem mult_0_n : forall n : nat,
    0 * n = 0.
Proof.
    intros n.
    reflexivity.
Qed.

(* Theorem mult_n_0 : forall n : nat,
    0 * n = 0 -> 0 * n = n * 0.
Proof.
    intros n H.
    rewrite -> H.
    reflexivity.
Qed. *)

Theorem plus_id_example : forall n m : nat,
    n = m -> n + n = m + m.
Proof.
    intros n m.
    intros H.
    rewrite -> H.
    reflexivity.
Qed.

(* Exercicio 1 *)

Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
    intros n m o.
    intros H H'.
    rewrite -> H.
    rewrite -> H'.
    reflexivity.
Qed.

(* Checar Teorema *)
(* Check plus_id_exercise. *)

(* Theorem mult_n_0_m_0 : forall p q : nat,
    (p * 0) + (q * 0) = 0.
Proof.
    intros p q.
    rewrite <- (mult_0_n (p)).
    rewrite <- (mult_0_n (q)).
    simpl.
    reflexivity.    
Qed. *)

Definition mult_n_1' (n : nat) := 
    match n with
    | 0 => 0
    | n => n * 1
    end.


(* Compute (mult_n_1' 4). *)
(* Exercicio 2 *)
(* Theorem mult_n_1 : forall p : nat,
    p * 1 = p.
Proof.
    intros p.
    simpl.
    reflexivity.    
Qed. *)


Theorem plus_1_neq_0_firsttry : forall n : nat,
    (n + 1) =? 0 = false.
Proof.
    intros n.
    simpl.
Qed.
