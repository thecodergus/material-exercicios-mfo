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
  - destruct H as [x [G1 G2]].
    * exists x. apply G1.
  - destruct H as [x [G1 G2]]. 
    * exists x. apply G2. 
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
  intros. split.
  induction l as [|h t].
  - simpl. contradiction.
  - simpl. intros [H | H].
      * exists h. split. apply H. left. reflexivity.
      * apply IHt in H. destruct H as [w [F I]].
        + exists w. split. apply F. right. apply I.
  - intros [w [F I]].
      * assert (In_map : forall (A B : Type) (f : A -> B) (l : list A) (x : A), In x l -> In (f x) (map f l)). {
          intros A' B' f' l' x'.
          induction l' as [|x'' l'' IHl''].
          - simpl. contradiction.
          - simpl. intros [H | H].
              * rewrite H. left. reflexivity.
              * right. apply IHl''. apply H.
      }
        + rewrite <- F. apply In_map. apply I.
Qed.

(* Exercício 4*)

(* Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  Admitted. *)


Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros. split.
  - induction l as [|h t].
    * simpl. intro. right. apply H.
    * simpl. intros [H | H].
      + left. left. apply H.
      + apply IHt in H. destruct H.
        { left. right. apply H. }
        { right. apply H. }
  - induction l as [|h t].
    * intros [H | H].
      + inversion H.
      + simpl. apply H.
    * intros [H | H].
      + simpl. inversion H.
        { left. apply H0. }
        { right. apply IHt. left. apply H0. }
      + simpl. right. apply IHt. right. apply H.
Qed.

(* Exercício 5*)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | (h :: t) => P h /\ All P t 
  end.

(* Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
 Admitted. *)

 Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros. split.
  - induction l as [|h t].
    * reflexivity.
    * intros. simpl. split.
      + apply H. simpl. left. reflexivity.
      + apply IHt. intros. apply H. simpl. right. apply H0.
  - induction l as [|h t].
    * intros. inversion H0.
    * intros. simpl in H0. simpl in H.
      + destruct H as [PH APT]. destruct H0 as [HX | IXT].
        ++ rewrite <- HX. apply PH.
        ++ apply IHt. apply APT. apply IXT.
Qed.

(* Exercício 6*)

Theorem or_implies : forall (P Q : Prop), ~P \/ Q -> P -> Q.
Proof.
  intuition.
Qed.
(* Exercício 7*)
Theorem implies_or_peirce : forall (P Q : Prop), (~P \/ Q) -> ((P -> Q) -> P) -> P.
Proof.
  intuition.
Qed.



