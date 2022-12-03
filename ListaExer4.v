Require Export Coq.Init.Logic.
Require Export Coq.Lists.List.
Import ListNotations.


(* Exercício 1*)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  split.
  - intros. split.
    * destruct H. left. apply H. destruct H. right. apply H.
    * destruct H. left. apply H. right. apply H.
  - intros. destruct H. destruct H, H0.
    * left. apply H.
    * left. apply H.
    * left. apply H0.
    * right. split.
      + apply H.
      + apply H0.
Qed.

(* Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intuition.
Qed. *)

(* Exercício 2*)

Theorem dist_exists_and : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  intros.
  intuition.
  destruct H.
  - destruct H.
    *     
Qed.

(* Exercício 3*)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  Admitted.

(* Exercício 4*)

Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  Admitted.

(* Exercício 5*)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | (h :: t) => P h /\ All P t 
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
 Admitted.

(* Exercício 6*)

Theorem or_implies : forall (P Q : Prop), ~P \/ Q -> P -> Q.
Proof.
  Admitted.

(* Exercício 7*)
Theorem implies_or_peirce : forall (P Q : Prop), (~P \/ Q) -> ((P -> Q) -> P) -> P.
Proof.
  Admitted.



