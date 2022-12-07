(** * IndProp: Inductively Defined Propositions *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
Require Coq.omega.Omega. 

(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and existential
    quantification.  In this chapter, we bring yet another new tool
    into the mix: _inductive definitions_. *)

(** In past chapters, we have seen two ways of stating that a number
    [n] is even: We can say

      (1) [evenb n = true], or

      (2) [exists k, n = double k].

    Yet another possibility is to say that [n] is even if we can
    establish its evenness from the following rules:

       - Rule [ev_0]: The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even. *)

(** To illustrate how this new definition of evenness works,
    let's imagine using it to show that [4] is even. By rule [ev_SS],
    it suffices to show that [2] is even. This, in turn, is again
    guaranteed by rule [ev_SS], as long as we can show that [0] is
    even. But this last fact follows directly from the [ev_0] rule. *)

(** We will see many definitions like this one during the rest
    of the course.  For purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: 

                              ------------             (ev_0)
                                 even 0

                                 even n
                            ----------------          (ev_SS)
                             even (S (S n))
*)

(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [ev_SS] says that, if [n]
    satisfies [even], then [S (S n)] also does.  If a rule has no
    premises above the line, then its conclusion holds
    unconditionally.

    We can represent a proof using these rules by combining rule
    applications into a _proof tree_. Here's how we might transcribe
    the above proof that [4] is even: 

                             --------  (ev_0)
                              even 0
                             -------- (ev_SS)
                              even 2
                             -------- (ev_SS)
                              even 4
*)

(** (Why call this a "tree" (rather than a "stack", for example)?
    Because, in general, inference rules can have multiple premises.
    We will see examples of this shortly. *)

(* ================================================================= *)
(** ** Inductive Definition of Evenness *)

(** Putting all of this together, we can translate the definition of
    evenness into a formal Coq definition using an [Inductive]
    declaration, where each constructor corresponds to an inference
    rule: *)

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).

(** This definition is different in one crucial respect from previous
    uses of [Inductive]: the thing we are defining is not a [Type],
    but rather a function from [nat] to [Prop] -- that is, a property
    of numbers.  We've already seen other inductive definitions that
    result in functions -- for example, [list], whose type is [Type ->
    Type].  What is really new here is that, because the [nat]
    argument of [even] appears to the _right_ of the colon, it is
    allowed to take different values in the types of different
    constructors: [0] in the type of [ev_0] and [S (S n)] in the type
    of [ev_SS].

    In contrast, the definition of [list] names the [X] parameter
    _globally_, to the _left_ of the colon, forcing the result of
    [nil] and [cons] to be the same ([list X]).  Had we tried to bring
    [nat] to the left in defining [even], we would have seen an
    error: *)

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : wrong_ev n -> wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "[wrong_ev]" must have "[n]"
        as 1st argument in "[wrong_ev 0]". *)

(** In an [Inductive] definition, an argument to the type
    constructor on the left of the colon is called a "parameter",
    whereas an argument on the right is called an "index".

    For example, in [Inductive list (X : Type) := ...], [X] is a
    parameter; in [Inductive even : nat -> Prop := ...], the
    unnamed [nat] argument is an index. *)

(** We can think of the definition of [even] as defining a Coq
    property [even : nat -> Prop], together with primitive theorems
    [ev_0 : even 0] and [ev_SS : forall n, even n -> even (S (S n))]. *)

(** That definition can also be written as follows...

  Inductive even : nat -> Prop :=
  | ev_0 : even 0
  | ev_SS : forall n, even n -> even (S (S n)).
*)

(** ... making explicit the type of the rule [ev_SS]. *)

(** Such "constructor theorems" have the same status as proven
    theorems.  In particular, we can use Coq's [apply] tactic with the
    rule names to prove [even] for particular numbers... *)

Theorem ev_4 : even 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax: *)

Theorem ev_4' : even 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** We can also prove theorems that have hypotheses involving [even]. *)

Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** **** Exercise: 1 star, standard (ev_double)  *)
Theorem ev_double : forall n,
  even (double n).
Proof.
  intros. induction n. 
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.
  
(** [] *)

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _reason about_ such evidence.

    Introducing [even] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is even, but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are even (in the sense of [even]). *)

(** In other words, if someone gives us evidence [E] for the assertion
    [even n], then we know that [E] must have one of two shapes:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [even n']). *)

(** This suggests that it should be possible to analyze a
    hypothesis of the form [even n] much as we do inductively defined
    data structures; in particular, it should be possible to argue by
    _induction_ and _case analysis_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(* ================================================================= *)
(** ** Inversion on Evidence *)

(** Suppose we are proving some fact involving a number [n], and
    we are given [even n] as a hypothesis.  We already know how to
    perform case analysis on [n] using [destruct] or [induction],
    generating separate subgoals for the case where [n = O] and the
    case where [n = S n'] for some [n'].  But for some proofs we may
    instead want to analyze the evidence that [even n] _directly_. As
    a tool, we can prove our characterization of evidence for
    [even n], using [destruct]. *)

Theorem ev_inversion :
  forall (n : nat), even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
  - (* E = ev_0 : even 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : even (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** The following theorem can easily be proved using [destruct] on
    evidence. *)

Theorem ev_minus2 : forall n,
  even n -> even (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

(** However, this variation cannot easily be handled with [destruct]. *)

Theorem evSS_ev : forall n,
  even (S (S n)) -> even n.
(** Intuitively, we know that evidence for the hypothesis cannot
    consist just of the [ev_0] constructor, since [O] and [S] are
    different constructors of the type [nat]; hence, [ev_SS] is the
    only case that applies.  Unfortunately, [destruct] is not smart
    enough to realize this, and it still generates two subgoals.  Even
    worse, in doing so, it keeps the final goal unchanged, failing to
    provide any useful information for completing the proof.  *)
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
Abort.

(** What happened, exactly?  Calling [destruct] has the effect of
    replacing all occurrences of the property argument by the values
    that correspond to each constructor.  This is enough in the case
    of [ev_minus2] because that argument [n] is mentioned directly
    in the final goal. However, it doesn't help in the case of
    [evSS_ev] since the term that gets replaced ([S (S n)]) is not
    mentioned anywhere. *)

(** We could patch this proof by replacing the goal [even n],
    which does not mention the replaced term [S (S n)], by the
    equivalent goal [even (pred (pred (S (S n))))], which does mention
    this term, after which [destruct] can make progress. But it is
    more straightforward to use our inversion lemma. *)

Theorem evSS_ev : forall n, even (S (S n)) -> even n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm.
   intro Heq. rewrite Heq. apply Hev.
Qed.

(** Coq provides a tactic called [inversion], which does the work of
    our inversion lemma and more besides. *)

(** The [inversion] tactic can detect (1) that the first case
    ([n = 0]) does not apply and (2) that the [n'] that appears in the
    [ev_SS] case must be the same as [n].  It has an "[as]" variant
    similar to [destruct], allowing us to assign names rather than
    have Coq choose them. *)

Theorem evSS_ev' : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductive
    properties, something that takes a bit more work using our
    inversion lemma. For example: *)
Theorem one_not_even : ~ even 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ even 1.
  intros H. inversion H. Qed.

(** **** Exercise: 1 star, standard (inversion_practice)  

    Prove the following result using [inversion].  For extra practice,
    prove it using the inversion lemma. *)

Theorem SSSSev__even : forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
  intros. induction n.
  - apply ev_0.
  - apply evSS_ev in H. apply evSS_ev in H. apply H.
Qed.
 
(** [] *)

(** **** Exercise: 1 star, standard (even5_nonsense)  

    Prove the following result using [inversion]. *)

Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
  intros. simpl. apply SSSSev__even in H. apply one_not_even in H. inversion H.
Qed.

 
(** [] *)

(** The [inversion] tactic does quite a bit of work. When
    applied to equalities, as a special case, it does the work of both
    [discriminate] and [injection]. In addition, it carries out the
    [intros] and [rewrite]s that are typically necessary in the case
    of [injection]. It can also be applied, more generally, to analyze
    evidence for inductively defined propositions.  As examples, we'll
    use it to reprove some theorems from [Tactics.v]. *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** Here's how [inversion] works in general.  Suppose the name
    [H] refers to an assumption [P] in the current context, where [P]
    has been defined by an [Inductive] declaration.  Then, for each of
    the constructors of [P], [inversion H] generates a subgoal in which
    [H] has been replaced by the exact, specific conditions under
    which this constructor could have been used to prove [P].  Some of
    these subgoals will be self-contradictory; [inversion] throws
    these away.  The ones that are left represent the cases that must
    be proved to establish the original goal.  For those, [inversion]
    adds all equations into the proof context that must hold of the
    arguments given to [P] (e.g., [S (S n') = n] in the proof of
    [evSS_ev]). *)

(** The [ev_double] exercise above shows that our new notion of
    evenness is implied by the two earlier ones (since, by
    [even_bool_prop] in chapter [Logic], we already know that
    those are equivalent to each other). To show that all three
    coincide, we just need the following lemma. *)

Lemma ev_even_firsttry : forall n,
  even n -> exists k, n = double k.
Proof.
(* WORKED IN CLASS *)

(** We could try to proceed by case analysis or induction on [n].  But
    since [even] is mentioned in a premise, this strategy would
    probably lead to a dead end, as in the previous section.  Thus, it
    seems better to first try [inversion] on the evidence for [even].
    Indeed, the first case can be solved trivially. *)

  intros n E. inversion E as [| n' E'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.

(** Unfortunately, the second case is harder.  We need to show [exists
    k, S (S n') = double k], but the only available assumption is
    [E'], which states that [even n'] holds.  Since this isn't
    directly useful, it seems that we are stuck and that performing
    case analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on [E], we were able to reduce the original result to a similar
    one that involves a _different_ piece of evidence for [even]:
    namely [E'].  More formally, we can finish our proof by showing
    that

        exists k', n' = double k',

    which is the same as the original statement, but with [n'] instead
    of [n].  Indeed, it is not difficult to convince Coq that this
    intermediate result suffices. *)

    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I. (* reduce the original goal to the new one *)

Abort.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** If this looks familiar, it is no coincidence: We've
    encountered similar problems in the [Induction] chapter, when
    trying to use case analysis to prove results that required
    induction.  And once again the solution is... induction!

    The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have used to build that evidence, while
    providing an induction hypotheses for each recursive occurrence of
    the property in question.

    To prove a property of [n] holds for all numbers for which [even
    n] holds, we can use induction on [even n]. This requires us to
    prove two things, corresponding to the two ways in which [even n]
    could have been constructed. If it was constructed by [ev_0], then
    [n=0], and the property must hold of [0]. If it was constructed by
    [ev_SS], then the evidence of [even n] is of the form [ev_SS n'
    E'], where [n = S (S n')] and [E'] is evidence for [even n']. In
    this case, the inductive hypothesis says that the property we are
    trying to prove holds for [n']. *)

(** Let's try our current lemma again: *)

Lemma ev_even : forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

(** Here, we can see that Coq produced an [IH] that corresponds
    to [E'], the single recursive occurrence of [even] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_even_iff : forall n,
  even n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** As we will see in later chapters, induction on evidence is a
    recurring technique across many areas, and in particular when
    formalizing the semantics of programming languages, where many
    properties of interest are defined inductively. *)

(** The following exercises provide simple examples of this
    technique, to help you familiarize yourself with it. *)

(** **** Exercise: 2 stars, standard (ev_sum)  *)
Theorem ev_sum : forall n m, even n -> even m -> even (n + m).
Proof.
  intros n m N M. induction N as [| n' N' ]. (*Indução na hipótese*)
  - apply M. 
  - simpl. apply ev_SS. apply IHN'.
Qed.
  
  
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (even'_ev)  

    In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [even]: *)

Inductive even' : nat -> Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).

(** Prove that this definition is logically equivalent to the old
    one.  (You may want to look at the previous theorem when you get
    to the induction step.) *)

Theorem ev_ev__ev : forall n m,
  even (n+m) -> even n -> even m.
Proof.
  intros n m NM N. induction N.
  - simpl in NM. apply NM.
  - apply IHN. simpl in NM. apply evSS_ev' in NM. apply NM.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus)  

    This exercise just requires applying existing lemmas.  No
    induction or even case analysis is needed, though some of the
    rewriting may be tedious. *)

Theorem ev_plus_plus : forall n m p,
  even (n+m) -> even (n+p) -> even (m+p).
Proof.
  intros n m p NM NP. 
  - apply (ev_ev__ev (n+n)).
    * rewrite <- plus_assoc. rewrite (plus_assoc n m p). rewrite plus_comm.
      rewrite <- plus_assoc. rewrite (plus_comm p n). apply ev_sum. apply NM.
      apply NP.
    * rewrite <- double_plus. apply ev_double.
Qed.

(** [] *)

(* ################################################################# *)
(** * Inductive Relations *)

(** A proposition parameterized by a number (such as [even])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module Playground.

(** One useful example is the "less than or equal to" relation on
    numbers. *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [even] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) ->
    2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *) 
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 n : even (S n) -> next_even n (S n)
  | ne_2 n (H : even (S (S n))) : next_even n (S (S n)).

(** **** Exercise: 2 stars, standard, optional (total_relation)  

    Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

(* FILL IN HERE 

    [] *)

(** **** Exercise: 2 stars, standard, optional (empty_relation)  

    Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

(* FILL IN HERE 

    [] *)

(** From the definition of [le], we can sketch the behaviors of
    [destruct], [inversion], and [induction] on a hypothesis [H]
    providing evidence of the form [le e1 e2].  Doing [destruct H]
    will generate two cases. In the first case, [e1 = e2], and it
    will replace instances of [e2] with [e1] in the goal and context.
    In the second case, [e2 = S n'] for some [n'] for which [le e1 n']
    holds, and it will replace instances of [e2] with [S n']. 
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing [induction H]
    will, in the second case, add the induction hypothesis that the
    goal holds when [e2] is replaced with [n']. *)

(** **** Exercise: 3 stars, standard, optional (le_exercises)  

    Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros. induction H0. 
  - apply H.
  - apply le_S. apply IHle.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros. induction n. reflexivity. inversion IHn. 
  - apply le_S. reflexivity.
  -inversion IHn.
    + apply le_S. rewrite H0. apply IHn.
    + rewrite H0. apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros.  induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed.


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
intros. inversion H. 
- reflexivity.
- rewrite <- H1. apply le_S. reflexivity.
Qed. 

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros. apply Sn_le_Sm__n_le_m. induction b.
  -  simpl. rewrite <- plus_n_O. apply le_n.
  - apply le_S. rewrite <- plus_n_Sm. apply IHb.
Qed.
  
Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros. split.
  - induction n2.
    + rewrite <- plus_n_O in H. apply H.
    + apply IHn2. apply le_S in H. apply Sn_le_Sm__n_le_m in H.
      rewrite plus_comm in H. simpl in H. rewrite plus_comm in H.
      apply H.
  - induction n1.
    + apply H.
    + apply IHn1. apply le_S in H. apply Sn_le_Sm__n_le_m in H. apply H.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt. intros. apply le_S in H. apply H.
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros.
  generalize dependent m.
  induction n.
  - intros. apply O_le_n.
  - intros. destruct m.
    + discriminate H.
    + simpl in H. apply IHn in H. apply n_le_m__Sn_le_Sm in H. apply H.
Qed.

(** Hint: The next one may be easiest to prove by induction on [m]. *)

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  intros.
  generalize dependent m.
  induction n.
  - intros. reflexivity.
  - intros. destruct m.
    + inversion H.
    + apply Sn_le_Sm__n_le_m in H. apply IHn in H. apply H.
Qed.

(** Hint: This one can easily be proved without using [induction]. *)

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros.
  apply leb_correct.
  apply leb_complete in H.
  apply leb_complete in H0.
  apply le_trans with(n:=m). apply H. apply H0.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (leb_iff)  *)
Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  split.
  apply leb_complete.
  apply leb_correct.
Qed.
(** [] *)

Module R.

(** **** Exercise: 3 stars, standard, recommended (R_provability)  

    We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

(* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_R_provability : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (R_fact)  

    The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq? *)

Definition fR : nat -> nat -> nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem R_equiv_fR:
  forall m n o, R m n o <-> fR m n = o.
Proof.
  unfold fR.
  intros m n o. split.
  - intros H.
    induction H as [| m' n' o' H' | m' n' o' H'].
    + reflexivity.
    + simpl. rewrite IHH'. reflexivity.
    + rewrite plus_comm. simpl.
      rewrite plus_comm. rewrite IHH'. reflexivity.
  - intros H.
    generalize dependent n.
    generalize dependent o.
    induction m as [| m' IH].
    + intros. simpl in H. rewrite H.
      generalize dependent n.
      induction o as [| o' IH].
      * intros. apply c1.
      * intros.
        apply c3.
        apply IH with o'.
        reflexivity.
    + intros.
      destruct o.
      * discriminate.
      * apply c2.
        apply IH.
        simpl in H.
        injection H as H.
        apply H.
Qed.

(* Exercise 14 *)
Inductive subseq: list nat -> list nat -> Prop :=
  | subseq_nil l: subseq [] l
  | subseq_app_any n l1 l2 (H: subseq l1 l2): subseq l1 (n :: l2)
  | subseq_app_same n l1 l2 (H: subseq l1 l2): subseq (n :: l1) (n :: l2).

Theorem subseq_refl: forall l, subseq l l.
Proof.
  intros l.
  induction l as [| a t IH].
  - apply subseq_nil.
  - apply subseq_app_same. apply IH.
Qed.

Theorem subseq_nil_nil:
  forall l, subseq l [] -> l = [].
Proof.
  induction l as [| a t IH].
  - reflexivity.
  - intros.
    inversion H.
Qed.

Lemma eq_eq:
  forall n m, n =? m = true -> n = m.
Proof.
  induction n as [| n' IH].
  - intros. destruct m.
    + reflexivity.
    + discriminate.
  - intros. destruct m.
    + discriminate.
    + apply f_equal.
      apply IH.
      apply H.
Qed.

Theorem subseq_app:
  forall (l1 l2 l3: list nat),
    subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros.
  induction H.
  - apply subseq_nil.
  - simpl. apply subseq_app_any.
    apply IHsubseq.
  - simpl. apply subseq_app_same.
    apply IHsubseq.
Qed.

Theorem subseq_trans:
  forall (l1 l2 l3: list nat),
    subseq l1 l2 ->
    subseq l2 l3 ->
    subseq l1 l3.
Proof.
  intros l1 l2 l3 H1 H2.
  generalize dependent l1.
  induction H2.
  - intros.
    apply subseq_nil_nil in H1.
    rewrite H1.
    apply subseq_nil.
  - intros.
    apply subseq_app_any.
    apply IHsubseq.
    apply H1.
  - intros.
    inversion H1.
    + apply subseq_nil.
    + apply subseq_app_any.
      apply IHsubseq.
      apply H3.
    + apply subseq_app_same.
      apply IHsubseq.
      apply H3.
Qed.

(* Exercise 15 *)
(* R 2 [1;0] is provable *)
(* R 1 [1;2;1;0] is provable *)
(* R 6 [3;2;1;0] is not provable *)

Inductive reg_exp {T: Type}: Type :=
  | EmptySet
  | EmptyStr
  | Char (t: T)
  | App (r1 r2: reg_exp)
  | Union (r1 r2: reg_exp)
  | Star (r: reg_exp).

Inductive exp_match {T}: list T -> reg_exp -> Prop :=
  | MEmpty: exp_match [] EmptyStr
  | MChar x: exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
      (H1: exp_match s1 re1)
      (H2: exp_match s2 re2):
      exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
      (H1 : exp_match s1 re1):
      exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
      (H2: exp_match s2 re2):
      exp_match s2 (Union re1 re2)
  | MStar0 re: exp_match [] (Star re)
  | MStarApp s1 s2 re
      (H1: exp_match s1 re)
      (H2: exp_match s2 (Star re)):
      exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l: list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStar1:
  forall T s (re: @reg_exp T),
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s []).
  - apply H.
  - apply MStar0.
Qed.

(* Exercie 16 *)
Lemma empty_is_empty:
  forall T (s: list T),
  ~(s =~ EmptySet).
Proof.
  intros T s H.
  inversion H.
Qed.

Lemma MUnion':
  forall T (s: list T) (re1 re2: @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [match1 | match2].
  - apply MUnionL. apply match1.
  - apply MUnionR. apply match2.
Qed.

Lemma MStar':
  forall T (ss: list (list T)) (re: reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H.
  induction ss as [| a t IH].
  - simpl. apply MStar0.
  - simpl.
    apply MStarApp.
    + apply H. simpl. left. reflexivity.
    + apply IH. intros s H'.
      apply H. simpl. right. apply H'.
Qed.

(* Exercise 17 *)
Lemma reg_exp_of_list_spec:
  forall T (s1 s2: list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  (* a much nicer version from https://github.com/cz717/bksol/blob/master/sf/IndProp.v
  intros T s1 s2.
  generalize dependent s1.
  induction s2 as [|h t].
  - (* s2 = [] *)
    split. 
    + intros H. simpl in H. inversion H. reflexivity.
    + intros H. simpl. rewrite H. apply MEmpty.
  - (* s2 = h::t *)
    intros s1. split. 
    + intros H. simpl in H. inversion H. 
      inversion H3. simpl. 
      rewrite (IHt s2) in H4. rewrite H4. reflexivity.
    + intros H. simpl. rewrite H.
      assert ( A : forall S (x:S) y, [x]++y = x::y).
      {  intros S x y. simpl. reflexivity.  }
      rewrite <- A. apply MApp.
      * apply MChar.
      * apply IHt. reflexivity.
  *)

  intros T s1 s2. split.
  - generalize dependent s2.
    generalize dependent s1.
    induction s1 as [| a1 t1 IH1].
    + destruct s2.
      * intros. reflexivity.
      * intros. simpl in H.
        inversion H.
        inversion H3.
        rewrite <- H5 in H1.
        discriminate H1.
    + intros s2 H.
      destruct s2.
      * simpl in H.
        inversion H.
      * simpl in H.
        inversion H.
        inversion H3.
        simpl.
        rewrite <- H5 in H1.
        injection H1 as H1.
        rewrite H6 in H4.
        rewrite H6.
        apply IH1 in H4.
        rewrite H4.
        reflexivity.
  - generalize dependent s2.
    generalize dependent s1.
    induction s1 as [| a1 t1 IH1].
    + intros. rewrite <- H. simpl. apply MEmpty.
    + intros.
      destruct s2.
      * discriminate.
      * simpl.
        assert (H': a1 :: t1 = [a1] ++ t1).
        { reflexivity. }
        rewrite H'.
        apply MApp.
        -- injection H as H1 H2.
           rewrite H1.
           apply MChar.
        -- injection H as _ H2.
           apply IH1. apply H2.
Qed.

Fixpoint re_chars {T} (re: reg_exp): list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match:
  forall T (s: list T) (re: reg_exp) (x: T),
    s =~ re ->
    In x s ->
    In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - simpl.
    rewrite In_app_iff in Hin.
    destruct Hin as [H1 | H2].
    + apply IH1. apply H1.
    + apply IH2. apply H2.
Qed.

(* Exercise 18 *)
Fixpoint re_not_empty {T: Type} (re: @reg_exp T): bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char t => true
  | App r1 r2 => re_not_empty r1 && re_not_empty r2
  | Union r1 r2 => re_not_empty r1 || re_not_empty r2
  | Star r => true
  end.

Lemma orb_comm:
  forall a b, orb a b = orb b a.
Proof.
  destruct a.
  - destruct b.
    + reflexivity.
    + reflexivity.
  - destruct b.
    + reflexivity.
    + reflexivity.
Qed.

Lemma re_not_empty_correct:
  forall T (re: @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re. split.
  - intros [s H].
    induction H as
      [
      | x'
      | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
      | s1 re1 re2 Hmatch IH
      | re1 s2 re2 Hmatch IH
      | re
      | s1 s2 re Hmatch1 IH1 Hmatch2 IH2
      ].
    + reflexivity.
    + reflexivity.
    + simpl. rewrite IH1, IH2. reflexivity.
    + simpl. rewrite IH. reflexivity.
    + simpl. rewrite IH. rewrite orb_comm. reflexivity.
    + reflexivity.
    + apply IH2.
  - intros H.
    induction re as
      [
      |
      | t
      | r1 IH1 r2 IH2
      | r1 IH1 r2 IH2
      | r IH
      ].
    + discriminate.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + simpl in H. apply andb_true_iff in H.
      destruct H as [H1 H2].
      destruct (IH1 H1) as [s1 H1'].
      destruct (IH2 H2) as [s2 H2'].
      exists (s1 ++ s2).
      apply MApp. apply H1'. apply H2'.
    + simpl in H. apply orb_true_iff in H.
      destruct H as [H1 | H2].
      * destruct (IH1 H1) as [s H1'].
        exists s. apply MUnionL. apply H1'.
      * destruct (IH2 H2) as [s H2'].
        exists s. apply MUnionR. apply H2'.
    + exists []. apply MStar0.
Qed.

Lemma star_app':
  forall T (s1 s2: list T) (re re': @reg_exp T),
    re' = Star re ->
    s1 =~ re' ->
    s2 =~ Star re ->
    s1 ++ s2 =~ Star re.
Proof.
  intros T s1' s2' re re' H0 H1 H2.
  induction H1 as
    [
    | x'
    | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
    | s1 re1 re2 Hmatch IH
    | re1 s2 re2 Hmatch IH
    | re''
    | s1 s2 re'' Hmatch1 IH1 Hmatch2 IH2
    ].
  - apply H2.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - apply H2.
  - rewrite <- H0 in *.
    rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2. reflexivity.
Qed.

Lemma star_app:
  forall T (s1 s2: list T) (re: @reg_exp T),
    s1 =~ Star re ->
    s2 =~ Star re ->
    s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  induction H1 as
    [
    | x'
    | s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
    | s1 re1 re2 Hmatch IH
    | re1 s2' re2 Hmatch IH
    | re''
    | s1' s2' re'' Hmatch1 IH1 Hmatch2 IH2
    ].
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - intros H. apply H.
  - intros H.
    rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2. apply Heqre'. apply H.
Qed.

(* Exercise 19 *)
Lemma MStar'':
  forall T (s: list T) (re: reg_exp),
    s =~ Star re ->
    exists (ss: list (list T)),
      s = fold app ss [] /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H1.
  remember (Star re) as re'.
  induction H1 as
    [
    |
    |
    |
    |
    | re2
    | s1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
    ].
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists []. split.
    reflexivity.
    intros s' H.
    destruct H.
  - destruct (IH2 Heqre') as [ss [H1 H2]].
    exists (s1 :: ss). split.
    + simpl. rewrite H1. reflexivity.
    + intros s' [H3 | H3].
      * rewrite <- H3.
        injection Heqre' as Heqre'.
        rewrite <- Heqre'. apply Hmatch1.
      * apply H2. apply H3.
Qed.

(* Exercise 20 *)
Fixpoint pumping_constant {T} (re: @reg_exp T): nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

Fixpoint napp {T} (n: nat) (l: list T): list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus:
  forall T (n m: nat) (l: list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma le_false_le:
  forall a b,
    a <=? b = false ->
    b <= a.
Proof.
  induction a as [| a' IH].
  - intros. discriminate.
  - intros.
    destruct (a' =? b) eqn:E1.
    + apply eqb_eq in E1.
      rewrite E1.
      apply le_S. apply le_n.
    + apply le_S. apply IH.
      destruct (a' <=? b) eqn:E2.
      * apply leb_complete in E2.
        inversion E2.
        -- rewrite H1 in E1.
           rewrite <- eqb_refl in E1.
           discriminate.
        -- apply n_le_m__Sn_le_Sm in H0.
           rewrite H2 in H0.
           apply leb_correct in H0.
           rewrite H0 in H.
           discriminate.
      * reflexivity.
Qed.

Lemma le_plus_b:
  forall a b c,
    a <= b <-> a + c <= b + c.
Proof.
  intros a b c.
  induction c as [| c' IH].
  - split.
    + intros. rewrite (plus_comm a 0), (plus_comm b 0).
      simpl. apply H.
    + intros. rewrite (plus_comm a 0), (plus_comm b 0) in H.
      simpl in H. apply H.
  - split.
    + intros.
      rewrite (plus_comm a (S c')), (plus_comm b (S c')).
      rewrite <- S_a_plus_b.
      rewrite <- S_a_plus_b.
      apply n_le_m__Sn_le_Sm.
      rewrite (plus_comm c' a), (plus_comm c' b).
      apply IH.
      apply H.
    + intros.
      rewrite (plus_comm a (S c')), (plus_comm b (S c')) in H.
      rewrite <- S_a_plus_b in H.
      rewrite <- S_a_plus_b in H.
      apply Sn_le_Sm__n_le_m in H.
      rewrite (plus_comm c' a), (plus_comm c' b) in H.
      apply IH in H. apply H.
Qed.

Lemma le_lem:
  forall a b c d,
    a + b <= c + d ->
    a <= c \/ b <= d.
Proof.
  intros a b c d H.
  destruct (a <=? c) eqn:E1.
  - apply leb_complete in E1.
    left. apply E1.
  - apply le_false_le in E1.
    apply (le_plus_b c a d) in E1.
    assert (H' := le_trans _ _ _ H E1).
    rewrite (plus_comm a b), (plus_comm a d) in H'.
    apply le_plus_b in H'.
    right. apply H'.
Qed.

Theorem le_plus_r:
  forall a b c, a + b <= c -> a <= c.
Proof.
  intros a b c H.
  induction b as [| b' IH].
  - rewrite plus_comm in H. simpl in H.
    apply H.
  - apply IH. rewrite plus_comm in H.
    rewrite <- S_a_plus_b in H.
    destruct c.
    + inversion H.
    + apply Sn_le_Sm__n_le_m in H.
      apply le_S.
      rewrite plus_comm in H.
      apply H.
Qed.

Lemma list_length_0:
  forall X l, @length X l = 0 -> l = [].
Proof.
  intros.
  destruct l.
  - reflexivity.
  - discriminate.
Qed.

Lemma pumping:
  forall T (re: @reg_exp T) s,
    s =~ re ->
    pumping_constant re <= length s ->
    exists s1 s2 s3,
      s = s1 ++ s2 ++ s3 /\
      s2 <> [] /\
      forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch as
    [
    | x
    | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
    | s1 re1 re2 Hmatch IH
    | re1 s2 re2 Hmatch IH
    | re
    | s1 s2 re Hmatch1 IH1 Hmatch2 IH2
    ].
  - simpl. intros. inversion H.
  - simpl. intros. inversion H. inversion H2.
  - simpl. intros.
    rewrite app_length in H.
    apply le_lem in H. destruct H as [H | H].
    + (* s1 is longer than the pumping length of re1 *)
      destruct (IH1 H) as
        [s1'x
          [s1'y
            [s1'z
              [IH1'1 [IH1'2 IH1'3]]
            ]
          ]
        ].
      exists s1'x, s1'y, (s1'z ++ s2).
      split.
      { rewrite IH1'1.
        rewrite app_assoc, app_assoc, app_assoc.
        reflexivity. }
      split.
      { apply IH1'2. }
      { intros.
        rewrite app_assoc, app_assoc.
        apply MApp.
        - rewrite <- app_assoc. apply IH1'3.
        - apply Hmatch2. }
    + (* s2 is longer than the pumping length of re2 *)
      destruct (IH2 H) as
        [s2'x
          [s2'y
            [s2'z
              [IH2'1 [IH2'2 IH2'3]]
            ]
          ]
        ].
      exists (s1 ++ s2'x), s2'y, s2'z.
      split.
      { rewrite IH2'1.
        rewrite app_assoc, app_assoc.
        reflexivity. }
      split.
      { apply IH2'2. }
      { intros.
        rewrite <- app_assoc.
        apply MApp.
        - apply Hmatch1.
        - apply IH2'3. }
  - (* left union, pump in the same way as s1 *)
    intros. simpl in H.
    apply le_plus_r in H.
    destruct (IH H) as
      [s1'x
        [s1'y
          [s1'z
            [IH1 [IH2 IH3]]
          ]
        ]
      ].
    exists s1'x, s1'y, s1'z.
    split.
    { apply IH1. }
    split.
    { apply IH2. }
    { intros. apply MUnionL. apply IH3. }
  - (* right union, pump in the same way as s2 *)
    intros. simpl in H.
    rewrite plus_comm in H.
    apply le_plus_r in H.
    destruct (IH H) as
      [s2'x
        [s2'y
          [s2'z
            [IH1 [IH2 IH3]]
          ]
        ]
      ].
    exists s2'x, s2'y, s2'z.
    split.
    { apply IH1. }
    split.
    { apply IH2. }
    { intros. apply MUnionR. apply IH3. }
  - intros. inversion H.
  - intros. simpl in H. rewrite app_length in H.
    destruct (length s1) eqn:E.
    + (* if s1 is empty, pump the same way as s2 *)
      simpl in H.
      apply list_length_0 in E.
      rewrite E. simpl.
      apply (IH2 H).
    + (* s1 non empty, pump with s1 *)
      exists [], s1, s2.
      split.
      { reflexivity. }
      split.
      { destruct s1. discriminate.
        intros H'. discriminate. }
      { simpl. intros m.
        induction m as [| m' IH].
        - simpl. apply Hmatch2.
        - assert (H': S m' = 1 + m').
          { reflexivity. }
          rewrite H'.
          rewrite napp_plus.
          rewrite <- app_assoc.
          apply MStarApp.
          + simpl. rewrite app_nil_r. apply Hmatch1.
          + apply IH. }
Qed.

Theorem filter_not_empty_In:
  forall n l,
    filter (fun x => n =? x) l <> [] ->
    In n l.
Proof.
  intros n l.
  induction l as [| a t IH].
  - intros. simpl in H.
    apply H. reflexivity.
  - simpl. destruct (n =? a) eqn:H.
    + intros. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + intros H'. right. apply IH. apply H'.
Qed.

Inductive reflect (P: Prop): bool -> Prop :=
  | ReflectT: P -> reflect P true
  | ReflectF: ~P -> reflect P false.

(* Inductive reflect: Prop -> bool -> Prop :=
  | ReflectT: forall P: Prop, P -> reflect P true
  | ReflectF: forall P: Prop, ~P -> reflect P false. *)

Theorem iff_reflect:
  forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros.
  destruct b eqn:E.
  - apply (ReflectT P). apply H. reflexivity.
  - apply (ReflectF P). rewrite H. intros HP.
    discriminate.
Qed.

Theorem reflect_iff:
  forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros.
  destruct H as [HP | HNP].
  - split. intros. reflexivity.
    intros. apply HP.
  - split. intros. destruct (HNP H).
    intros. discriminate.
Qed.

Lemma eqbP:
  forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m.
  apply iff_reflect.
  rewrite eqb_eq.
  reflexivity.
Qed.

Theorem filter_not_empty_In':
  forall n l,
    filter (fun x => n =? x) l <> [] ->
    In n l.
Proof.
  intros n l.
  induction l as [| a t IH].
  - simpl. intros. apply H. reflexivity.
  - simpl. destruct (eqbP n a) as [HP | HNP].
    + intros. left. rewrite HP. reflexivity.
    + intros. right. apply IH. apply H.
Qed.

(* Exercise 21 *)
Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice:
  forall n l, count n l = 0 -> ~(In n l).
Proof.
  intros n l.
  induction l as [| a t IH].
  - simpl. intros _ f. destruct f.
  - simpl. destruct (eqbP n a) as [H | H].
    + intros H'. discriminate.
    + simpl. intros H1 [H2 | H3].
      * apply H. rewrite H2. reflexivity.
      * apply IH. apply H1. apply H3.
Qed.

(* Exercise 22 *)
Inductive nostutter {X: Type}: list X -> Prop :=
  | nostutter_nil: nostutter []
  | nostutter_a (a: X): nostutter [a]
  | nostutter_next (a: X) (b: X) (l: list X):
      nostutter (b :: l) -> a <> b -> nostutter (a :: b :: l).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
  apply nostutter_next.
  apply nostutter_next.
  apply nostutter_next.
  apply nostutter_next.
  apply nostutter_next.
  apply nostutter_a.
  intros. discriminate.
  intros. discriminate.
  intros. discriminate.
  intros. discriminate.
  intros. discriminate.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof. apply nostutter_nil. Qed.

Example test_nostutter_3: nostutter [5].
Proof. apply nostutter_a. Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof.
  intros H.
  inversion H.
  inversion H2.
  apply H9. reflexivity.
Qed.

(* Exercise 23 *)
Inductive inorder_merge {X: Type}: list X -> list X -> list X -> Prop :=
  | inorder_nil: inorder_merge [] [] []
  | inorder_left a l1 l2 l:
      inorder_merge l1 l2 l -> inorder_merge (a :: l1) l2 (a :: l)
  | inorder_right a l1 l2 l:
      inorder_merge l1 l2 l -> inorder_merge l1 (a :: l2) (a :: l).

Example test_inorder_merge_1: inorder_merge [1] [2] [1; 2].
Proof.
  apply inorder_left.
  apply inorder_right.
  apply inorder_nil.
Qed.

Example test_inorder_merge_2: inorder_merge [1] [2; 3] [2; 1; 3].
Proof.
  apply inorder_right.
  apply inorder_left.
  apply inorder_right.
  apply inorder_nil.
Qed.

Example test_inorder_merge_3: ~(inorder_merge [1] [2] [1; 2; 3]).
Proof.
  intros H.
  inversion H.
  inversion H3.
  inversion H7.
Qed.

Theorem filter_correct:
  forall (X: Type) (l1 l2 l: list X)
         (test: X -> bool),
  inorder_merge l1 l2 l ->
  forallb test l1 = true ->
  forallb (fun x => negb (test x)) l2 = true ->
  filter test l = l1.
Proof.
  intros X l1 l2 l test.
  intros H.
  induction H as
    [| a l1' l2' l' H' | a l1' l2' l' H' IH].
  - intros H1 H2. reflexivity.
  - simpl. intros H1 H2.
    apply andb_true_iff in H1.
    destruct H1 as [H3 H4].
    rewrite H3.
    rewrite (IHH' H4 H2).
    reflexivity.
  - simpl. intros H1 H2.
    apply andb_true_iff in H2.
    destruct H2 as [H3 H4].
    destruct (test a).
    + discriminate.
    + apply IH. apply H1. apply H4.
Qed.

(* Exercise 24 *)
(* a weaker version on list nat *)
Theorem filter_correct_2:
  forall (l' l: list nat)
         (test: nat -> bool),
    subseq l' l ->
    forallb test l' = true ->
    length l' <= length (filter test l).
Proof.
  intros l' l test.
  intros H.
  induction H as
    [| n l1 l2 H' IH | n l1 l2 H' IH].
  - simpl. intros. apply O_le_n.
  - simpl. intros H1.
    destruct (test n).
    + simpl. apply le_S. apply IH.
      apply H1.
    + apply IH. apply H1.
  - simpl. rewrite andb_true_iff.
    intros [H1 H2].
    rewrite H1.
    apply n_le_m__Sn_le_Sm.
    apply IH. apply H2.
Qed.