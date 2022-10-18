Require Import Coq.Init.Nat.
(* Não deve ser importado nenhum novo arquivo
todas as definições devem estar neste arquivo *)


Fixpoint div2 (n:nat) : nat :=
  match n with
  | O => O
  | S O => O 
  | S (S n') => S (div2 n')  
end.  

Fixpoint sum (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n + sum n'
  end.

Theorem plus_n_0 : forall n : nat,
  n + 0 = n.
Proof.
  intro n. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'.
  reflexivity.
Qed.


Theorem plus_n_1 : forall (n : nat),
  n + 1 = S (n).
Proof.
  intros n. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'.
  reflexivity.
Qed.


Theorem plus_n_Sm : forall (n m:nat),
  n + S m = S (n + m).
Proof. 
  intros n m. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'.
  reflexivity.
Qed.

Theorem mult_2_n_plus : forall (n : nat),
  n + n = 2 * n.
Proof.
  intro n. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite plus_n_0.
  reflexivity.
Qed.

Theorem div2_2 : forall n: nat,
  div2 2 = 1.
Proof.
  intro n. induction n as [| n']. 
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma mult_n_1 : forall n,
  n * 1 = n.
Proof.
  intro n. induction n as [|n' IHn'].  
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Lemma mult_n_1_1_n : forall n : nat,
  n * 1 = 1 * n.
Proof.
  intro n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite plus_n_0. rewrite mult_n_1. reflexivity.
Qed.

Lemma Sn_equal_Sn : forall n : nat,
  S n = S n.
Proof.
  intro n. induction n as [|n' IHn'].
  - reflexivity.
  - reflexivity. 
Qed.

Lemma div_2_n n : 
  div2 (2*n) = n.
Proof.
  induction n as [|n' IHn']; trivial.
  simpl mul.
  rewrite plus_n_Sm; simpl. 
  rewrite plus_n_0. rewrite mult_2_n_plus.
  rewrite IHn'.
  rewrite <- plus_n_1.
  reflexivity.
Qed.


Theorem mul2_div2 : forall n : nat,
  n = div2 (2 * n).
Proof.
    intro n. induction n as [|n' IHn']; trivial.
    rewrite div_2_n.
    reflexivity.
Qed.

(* Print mult_S. *)

Theorem div2_mult2_plus: forall (n m : nat),
  n + div2 m = div2 (2 * n + m).
Proof.
  Admitted.
    

Theorem mult_Sn_m : forall (n m : nat),
  S n * m = m + n * m.
Proof.
  Admitted.

Theorem sum_Sn : forall n : nat,
  sum (S n) = S n + sum n.
Proof.
  Admitted.


Theorem sum_n : forall n : nat,
  sum n = div2 (n * (n + 1)).
Proof.
  Admitted.