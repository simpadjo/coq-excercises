(** * SearchTree: Binary Search Trees *)

(** Binary search trees are an efficient data structure for
   lookup tables, that is, mappings from keys to values.
   The [total_map] type from Maps.v is an _inefficient_
   implementation: if you add N items to your total_map,
   then looking them up takes N comparisons in the worst case,
   and N/2 comparisons in the average case.

   In contrast, if your [key] type is a total order -- that is,
   if it has a less-than comparison that's transitive and
   antisymmetric [ a<b <->  ~(b<a) ] -- then one can implement
   binary search trees (BSTs).   We will assume you know how BSTs
   work; you can learn this from:
   - Section 3.2 of  _Algorithms, Fourth Edition_,
       by Sedgewick and Wayne, Addison Wesley 2011;  or
   - Chapter 12 of _Introduction to Algorithms, 3rd Edition_,
       by Cormen, Leiserson, and Rivest, MIT Press 2009.

   Our focus here is to _prove the correctness of an implementation_
   of binary search trees. *)

Require Import Coq.Strings.String.
From VFA Require Import Perm.
Require Import FunctionalExtensionality.

(* ################################################################# *)
(** * Total and Partial Maps *)

(** Recall the [Maps] chapter of Volume 1 (Logical Foundations),
    describing functions from identifiers to some arbitrary type [A].
    VFA's [Maps] module is almost exactly the same, except that it
    implements functions from [nat] to some arbitrary type [A]. *)

From VFA Require Import Maps.

(* ################################################################# *)
(** * Sections *)

(** We will use Coq's [Section] feature to structure this development,
     so first a brief introduction to Sections.  We'll use the example
     of lookup tables implemented by lists. *)

Module SectionExample1.
  Definition mymap (V: Type) := list (nat*V).
  Definition empty (V: Type) : mymap V := nil.
  Fixpoint lookup (V: Type) (default: V) (x: nat) (m: mymap V) : V :=
    match m with
    | (a,v)::al => if x =? a then v else lookup V default x al
    | nil => default
    end.
  Theorem lookup_empty (V: Type) (default: V):
       forall x, lookup V default x (empty V) = default.
   Proof. reflexivity. Qed.
End SectionExample1.

(** It sure is tedious to repeat the [V] and [default] parameters
     in every definition and every theorem.  The [Section] feature
     allows us to declare them as parameters to every definition
     and theorem in the entire section: *)

Module SectionExample2.
  Section MAPS.
  Variable V : Type.
  Variable default: V.

  Definition mymap  := list (nat*V).
  Definition empty : mymap := nil.
  Fixpoint lookup (x: nat) (m: mymap) : V :=
    match m with
    | (a,v)::al => if x =? a then v else lookup x al
    | nil => default
    end.
  Theorem lookup_empty:
       forall x, lookup x empty = default.
   Proof. reflexivity. Qed.
  End MAPS.
End SectionExample2.

(** At the close of the section, this produces exactly the same
     result:  the functions that "need" to be parametrized by
     [V] or [default] are given extra parameters.  We can test
     this claim, as follows: *)

Goal SectionExample1.empty = SectionExample2.empty.
Proof. reflexivity.
Qed.

Goal SectionExample1.lookup = SectionExample2.lookup.
Proof.
  unfold SectionExample1.lookup, SectionExample2.lookup.
  try reflexivity. (* doesn't do anything. *)

  (** Well, not exactly the same; but certainly equivalent.
   Functions [f] and [g] are "extensionally equal" if, for every
   argument [x], [f x = g x].  The Axiom of Extensionality
   says that if two functions are "extensionally equal" then they
   are _equal_.  The [extensionality] tactic is just a convenient
   way of applying the axiom of extensionality. *)

  extensionality V; extensionality default; extensionality x.
  extensionality m; simpl.
  induction m as [| [? ?] ]; auto.
  destruct (x=?n); auto.
Qed.

(* ################################################################# *)
(** * Program for Binary Search Trees *)

Section TREES.
Variable V : Type.
Variable default: V.

Definition key := nat.

Inductive tree : Type :=
 | E : tree
 | T: tree -> key -> V -> tree -> tree.

Definition empty_tree : tree := E.

Fixpoint lookup (x: key) (t : tree) : V :=
  match t with
  | E => default
  | T tl k v tr => if x <? k then lookup x tl
                         else if k <? x then lookup x tr
                         else v
  end.

Fixpoint insert (x: key) (v: V) (s: tree) : tree :=
 match s with
 | E => T E x v E
 | T a y v' b => if  x <? y then T (insert x v a) y v' b
                        else if y <? x then T a y v' (insert x v b)
                        else T a x v b
 end.

Fixpoint elements' (s: tree) (base: list (key*V)) : list (key * V) :=
 match s with
 | E => base
 | T a k v b => elements' a ((k,v) :: elements' b base)
 end.

Definition elements (s: tree) : list (key * V) := elements' s nil.

(* ################################################################# *)
(** * Search Tree Examples *)

Section EXAMPLES.
Variables v2 v4 v5 : V.
Eval compute in insert 5 v5 (insert 2 v2 (insert 4 v5 empty_tree)).
  (*      = T (T E 2 v2 E) 4 v5 (T E 5 v5 E) *)
Eval compute in lookup 5 (T (T E 2 v2 E) 4 v5 (T E 5 v5 E)).
  (*      = v5 *)
Eval compute in lookup 3 (T (T E 2 v2 E) 4 v5 (T E 5 v5 E)).
  (*      = default *)
Eval compute in elements (T (T E 2 v2 E) 4 v5 (T E 5 v5 E)).
  (*      = [(2, v2); (4, v5); (5, v5)] *)
End EXAMPLES.

(* ################################################################# *)
(** * What Should We Prove About Search trees? *)

(** Search trees are meant to be an implementation of maps.
   That is, they have an [insert] function that corresponds to the
   [update] function of a map, and a [lookup] function that
   corresponds to applying the map to an argument.  To prove the
   correctness of a search-tree algorithm, we can prove:
   - Any search tree corresponds to some map, using a function or
         relation that we demonstrate.
   - The lookup function gives the same result as applying the map
   - The insert function returns a corresponding map.
   - Maps have the properties we actually wanted.  It would do no
     good to prove that searchtrees correspond to some abstract
     type X, if X didn't have useful properties!

  What properties do we want searchtrees to have?  If I insert
  the binding [(k,v)] into a searchtree [t], then look up [k], I
  should get [v]. If I look up [k'] in [insert (k,v) t], where [k'<>k],
  then I should get the same result as [lookup k t].  There are several
  more properties. Fortunately, all these properties are already proved
  about [total_map] in the [Maps] module: *)

Check t_update_eq. (*  : forall (A : Type) (m : total_map A) (x : id) (v : A),
       t_update m x v x = v   *)
Check t_update_neq.  (* : forall (X : Type) (v : X) (x1 x2 : id) (m : total_map X),
       x1 <> x2 -> t_update m x1 v x2 = m x2    *)
Check t_update_shadow.  (* : forall (A : Type) (m : total_map A) (v1 v2 : A) (x : id),
       t_update (t_update m x v1) x v2 = t_update m x v2    *)
Check t_update_same.  (* : forall (X : Type) (x : id) (m : total_map X),
        t_update m x (m x) = m    *)
Check t_update_permute. (* forall (X : Type) (v1 v2 : X) (x1 x2 : id) (m : total_map X),
       x2 <> x1 ->
       t_update (t_update m x2 v2) x1 v1 =
         t_update (t_update m x1 v1) x2 v2    *)
Check t_apply_empty. (* : forall (A : Type) (x : id) (v : A),
       t_empty v x = v *)

(** So, if we like those properties that [total_map] is proved to have,
   and we can prove that searchtrees behave like maps, then we don't
   have to reprove each individual property about searchtrees.

   More generally:  a job worth doing is worth doing well.
   It does no good to prove the "correctness" of a program, if you
   prove that it satisfies a wrong or useless specification. *)

(* ################################################################# *)
(** * Efficiency of Search Trees *)

(** We use binary search trees because they are efficient.  That is,
     if there are [N] elements in a (reasonably well balanced) BST,
     each insertion or lookup takes about logN time.

     What could go wrong?

     1.  The search tree might not be balanced.  In that case, each
           insertion or lookup will take as much as linear time.

	   - SOLUTION: use an algorithm, such as "red-black trees",
	   that ensures the trees stay balanced.  We'll do that in
           Chapter [RedBlack].

     2.  Our keys are natural numbers, and Coq's [nat] type takes
           linear time _per comparison_.  That is, computing (j <? k)
           takes time proportional to the _value_ of [k-j].

	   - SOLUTION: represent keys by a data type that has a more
           efficient comparison operator.  We just use [nat] in this
           chapter because it's something you're already familiar with.

     3.  There's no notion of "run time" in Coq.  That is, we can't
          say what it means that a Coq function "takes N steps to
          evaluate."  Therefore, we can't prove that binary search
          trees are efficient.

	  - SOLUTION 1: Don't prove (in Coq) that they're efficient;
          just prove that they are correct.  Prove things about their
          efficiency the old-fashioned way, on pencil and paper.

	  - SOLUTION 2: Prove in Coq some facts about the height of
          the trees, which have direct bearing on their efficiency.
          We'll explore that in later chapters.

      4.  Our functions in Coq aren't real implementations; they are
          just pretend models of real implementations.  What if there
          are bugs in the correspondence between the Coq function and
          the real implementation?

          - SOLUTION: Use Coq's [extraction] feature to derive the
	    real implementation (in Ocaml or Haskell) automatically
	    from the Coq function.  Or, use Coq's [vm_compute] or
	    [native_compute] feature to compile and run the programs
	    efficiently inside Coq.  We'll explore [extraction] in a
	    later chapter. *)

(* ################################################################# *)
(** * Proof of Correctness *)

(** We claim that a [tree] "corresponds" to a [total_map].
     So we must exhibit an "abstraction relation"
     [Abs: tree -> total_map V -> Prop].

    The idea is that [Abs t m] says that tree [t]
    is a representation of map [m]; or that map [m]
    is an abstraction of tree [t].  How should we
    define this abstraction relation?

    The empty tree is easy:   [Abs E (fun x => default)].

    Now, what about this tree?: *)

Definition example_tree (v2 v4 v5 : V) :=
   T (T E 2 v2 E) 4 v4 (T E 5 v5 E).

(** **** Exercise: 2 stars (example_map)  *)
(* Fill in the definition of example_map with a total_map that
  you think example_tree should correspond to.  Use
  [t_update] and [(t_empty default)]. *)

Definition example_map (v2 v4 v5: V) : total_map V :=
  t_update (t_update (t_update (t_empty default) 2 v2) 4 v4) 5 v5.
(** [] *)

(** To build the [Abs] relation, we'll use these two auxiliary
     functions that construct maps: *)

Definition combine {A} (pivot: key) (m1 m2: total_map A) : total_map A :=
  fun x => if x <? pivot  then m1 x else m2 x.

(** [combine pivot a b] uses the map [a] on any input less than
   [pivot], and uses map [b] on any input [ >= pivot]. *)

Inductive Abs:  tree -> total_map V -> Prop :=
| Abs_E: Abs E (t_empty default)
| Abs_T: forall a b l k v r,
      Abs l a ->
      Abs r b ->
      Abs (T l k v r)  (t_update (combine k a b) k v).

(** **** Exercise: 3 stars (check_example_map)  *)
(** Prove that your [example_map] is the right one.
     If it isn't, go back and fix your definition of [example_map].
     You will probably need the [bdestruct] tactic, and [omega]. *)

Lemma check_example_map:
  forall v2 v4 v5, Abs (example_tree v2 v4 v5) (example_map v2 v4 v5).
Proof.
intros.
unfold example_tree.
evar (m: total_map V).
replace (example_map v2 v4 v5) with m; subst m.
repeat constructor.
extensionality x.
(* HINT:
  First,    [unfold example_map, t_update, combine, t_empty, beq_id.]
  Then, repeat the following procedure:  If you see something like
  [if 4 =? x then ... else ...],    use the tactic [bdestruct (4 =? x)].
  If the arithmetic facts above the line can't all be true, use [omega].
  If you're too lazy to check for yourself whether they are true,
   use [bdestruct (4 =? x); try omega].
*)
unfold example_map, t_update, combine, t_empty.
bdestruct (4 =? x).
- subst. auto.
- bdestruct (x <? 4).
  -- bdestruct (2 =? x).
    * subst. auto.
    * assert (5 <> x). omega.
      replace (5 =? x) with false. destruct (x <? 2). auto. auto.
      symmetry. apply Nat.eqb_neq. auto.
  -- bdestruct (4 =? x).
    * subst. omega.
    * bdestruct (5 =? x). auto.
      assert (2 <> x). omega.
      replace (2 =? x) with false.
      bdestruct (x <? 5). auto.  auto.  
      symmetry. apply  Nat.eqb_neq. auto.
Qed.

(** [] *)

(** You can ignore this lemma, unless it fails. *)
Lemma check_too_clever: forall v2 v4 v5: V, True.
Proof.
intros.
evar (m: total_map V).
assert (Abs (example_tree v2 v4 v5) m).
repeat constructor.
(change m with (example_map v2 v4 v5) in H || auto);
(* auto; *)
fail "Did you use copy-and-paste, from your check_example_map proof,
       into your example_map definition?  If so, very clever.
       Please try it again with an example_map definition that
       you make up from first principles.  Or, to skip that,
       uncomment the (* auto; *) above.".
Qed.

Theorem empty_tree_relate: Abs empty_tree (t_empty default).
Proof.
constructor.
Qed.

(** **** Exercise: 3 stars (lookup_relate)  *)
Theorem lookup_relate:
  forall k t cts ,
    Abs t cts -> lookup k t =  cts k.
Proof.
  intros. induction H. auto.
  bdestruct (k <? k0).
  - assert ((k0 =? k) = false). apply Nat.eqb_neq. omega.
    assert ((k <? k0) = true). apply Nat.ltb_lt. auto.
    replace (lookup k (T l k0 v r)) with (lookup k l).
    -- rewrite -> IHAbs1. unfold t_update.
       rewrite -> H2.
       unfold combine. rewrite -> H3. auto.
    -- unfold lookup. rewrite -> H3. auto.
  - assert ((k <? k0) = false). apply Nat.ltb_ge. auto.
    bdestruct (k =? k0).
    -- subst. replace (lookup k0 (T l k0 v r)) with v.
      * unfold t_update. rewrite -> Nat.eqb_refl. auto. 
      * unfold lookup. 
        rewrite -> H2. auto.
    -- assert ((k0 =? k) = false). apply Nat.eqb_neq. omega.
       replace (lookup k (T l k0 v r)) with (lookup k r).
      * rewrite -> IHAbs2. unfold t_update. rewrite -> H4.
        unfold combine. rewrite -> H2. auto.
      * unfold lookup. rewrite -> H2.
        assert ((k0 <? k) = true). apply Nat.ltb_lt. omega.
        rewrite -> H5. auto.
Qed.
        
(** [] *)

(** **** Exercise: 4 stars (insert_relate)  *)
Theorem insert_relate:
 forall k v t cts,
    Abs t cts ->
    Abs (insert k v t) (t_update cts k v).
Proof.
 (*  Abs l a ->
      Abs r b ->
      Abs (T l k v r)  (t_update (combine k a b) k v).
 *)
  intros. induction H.
  - simpl. 
    replace (t_update (t_empty default) k v) with 
          ((t_update (combine k (t_empty default) (t_empty default)) k v)).
    -- constructor. constructor. constructor. 
    -- extensionality x.
       bdestruct (x =? k).
       * subst. unfold t_update. rewrite -> Nat.eqb_refl. auto.
       * unfold t_update. assert ((k =? x) = false). apply Nat.eqb_neq. auto.
         rewrite -> H0. unfold combine. 
         destruct (x <? k). auto. auto.
  - bdestruct (k <? k0).
    assert ((k <? k0) = true). apply Nat.ltb_lt. auto.
    -- replace (insert k v (T l k0 v0 r)) with (T (insert k v l) k0 v0 r).
       * replace (t_update (t_update (combine k0 a b) k0 v0) k v)
            with (t_update (combine k0 (t_update a k v) b) k0 v0).
         ** constructor. auto. auto.  
         ** extensionality x. 
            bdestruct (k =? x).
            + subst. unfold t_update. rewrite -> Nat.eqb_refl.
              assert ((k0 =? x) = false). apply Nat.eqb_neq. omega.
              rewrite -> H3.
              unfold combine. assert ((x <? k0) = true). apply Nat.ltb_lt. auto.
              rewrite -> H4. assert ((x =? x) = true). apply  Nat.eqb_refl.
              rewrite -> H5. auto.
            + assert ((k =? x) = false). apply Nat.eqb_neq. omega. 
             unfold t_update. rewrite -> H4.
             bdestruct (k0 =? x). auto.
             unfold combine. 
             bdestruct (x <? k0).
             ++ rewrite -> H4. auto.
             ++ auto. 
       * unfold insert. rewrite -> H2. auto.
    -- assert ((k <? k0) = false). apply Nat.ltb_ge. omega.
       bdestruct (k =? k0).
       * subst. 
         replace (insert k0 v (T l k0 v0 r)) with (T l k0 v r).
         ** replace (t_update (t_update (combine k0 a b) k0 v0) k0 v) with
             (t_update (combine k0 a b) k0 v).
            + constructor. auto. auto.
            + extensionality x. unfold t_update.
              bdestruct (k0 =? x). auto. auto.
         ** unfold insert. rewrite -> H2. auto.
       *         assert ((k0 <? k) = true). apply Nat.ltb_lt. omega.
         replace (insert k v (T l k0 v0 r)) with (T l k0 v0 (insert k v r)).
         ** replace (t_update (t_update (combine k0 a b) k0 v0) k v)
            with (t_update (combine k0 a (t_update b k v)) k0 v0).
            +  constructor. auto. auto.
            + extensionality x. unfold t_update.
               bdestruct (k0 =? x). 
               ++ subst. assert ((k =? x) = false). apply Nat.eqb_neq. omega.
                  rewrite ->  H5. auto.
               ++ bdestruct (k =? x).
                  *** subst. unfold combine. rewrite -> H2. rewrite -> Nat.eqb_refl. auto.
                  *** unfold combine.
                      bdestruct (x <? k0). auto.
                      assert ((k =? x) = false). apply Nat.eqb_neq. omega.
                      rewrite -> H8. auto.
         ** unfold insert. rewrite -> H2. rewrite -> H4. auto.
Qed.
(** [] *)

(* ################################################################# *)
(** * Correctness Proof of the [elements] Function *)

(** How should we specify what [elements] is supposed to do?
     Well, [elements t] returns a list of pairs
     [(k1,v1);(k2;v2);...;(kn,vn)] that ought to correspond to
     the total_map, [t_update ... (t_update (t_update (t_empty default)
                     (Id k1) v1) (Id k2) v2) ... (Id kn) vn].

    We can formalize this quite easily.  *)

Fixpoint list2map (el: list (key*V)) : total_map V :=
 match el with
 | nil => t_empty default
 | (i,v)::el' => t_update (list2map el') i v
 end.

(** **** Exercise: 3 stars (elements_relate_informal)  *)
Theorem elements_relate:
  forall t cts,  Abs t cts -> list2map (elements t) = cts.
Proof.
(** Don't prove this yet.  Instead, explain in your own words, with
   examples, why this must be true.  It's OK if your explanation is
   not a formal proof; it's even OK if your explanation is subtly
   wrong!  Just make it convincing. *)

  (* FILL IN YOUR EXPLANATION HERE *)
Abort.
(* Do not modify the following line: *)
Definition manual_grade_for_elements_relate_informal : option (prod nat string) := None.
(** [] *)

(** Instead of doing a _formal_ proof that [elements_relate] is true,
    prove that it's false!  That is, as long as type [V] contains at
    least two distinct values. *)

(** **** Exercise: 4 stars (not_elements_relate)  *)
Theorem not_elements_relate:
  forall v, v <> default ->
  ~ (forall t cts,  Abs t cts -> list2map (elements t) = cts).
Proof.
intros.
intro.
pose (bogus := T (T E 3 v E) 2 v E).
pose (m := t_update (t_empty default) 2 v).
pose (m' := t_update
        (combine 2
           (t_update (combine 3 (t_empty default) (t_empty default)) 3 v)
           (t_empty default)) 2 v).
assert (Paradox: list2map (elements bogus) = m /\ list2map (elements bogus) <> m).
split.
(** To prove the first subgoal, prove that [m=m'] (by [extensionality]) and
      then use [H].

     To prove the second subgoal, do an [intro] so that you can assume
      [update_list (t_empty default) (elements bogus) = m], then show that
      [update_list (t_empty default) (elements bogus) (Id 3) <> m (Id 3)].
      That's a contradiction.

      To prove the third subgoal, just destruct [Paradox] and use the
      contradiction.

      In all 3 goals, when you need to unfold local definitions such
      as [bogus] you can use [unfold bogus] or [subst bogus].  *)

- assert (m = m').
  -- subst m'. subst m. extensionality x. unfold t_update.
     bdestruct (2 =? x). auto.
     bdestruct (3 =? x).
     *  subst. unfold combine. simpl. auto.
     * unfold combine.
       bdestruct (x <? 2).
       --- assert ((3 =? x) = false). apply Nat.eqb_neq. omega.
           rewrite -> H4.
            assert ((x <? 3) = true). apply Nat.ltb_lt. omega.
           rewrite -> H5. auto.
       --- auto.
  -- rewrite -> H1. apply H0. 
     subst m'. subst bogus. repeat constructor.
- intro. assert ((list2map (elements bogus)) 3 = m 3). rewrite -> H1. auto.
  unfold bogus in H2. unfold list2map in H2. subst m. simpl in H2.
  unfold t_update in H2. simpl in H2. subst v. unfold t_empty in H. apply H. auto.
- destruct Paradox. apply H2. auto.
Qed.
(** [] *)

(** What went wrong?  Clearly, [elements_relate] is true; you just
    explained why.  And clearly, it's not true, because
    [not_elements_relate] is provable in Coq.  The problem is that the
    tree [(T (T E 3 v E) 2 v E)] is bogus: it's not a well-formed
    binary search tree, because there's a 3 in the left subtree of the
    2 node, and 3 is not less than 2.

    If you wrote a good answer to the [elements_relate_informal]
    exercise, (that is, an answer that is only subtly wrong), then the
    subtlety is that you assumed that the search tree is well formed.
    That's a reasonable assumption; but we will have to prove that all
    the trees we operate on will be well formed.  *)

(* ################################################################# *)
(** * Representation Invariants *)

(** A [tree] has the [SearchTree] property if, at any node with key
     [k], all the keys in the left subtree are less than [k], and all
     the keys in the right subtree are greater than [k].  It's not
     completely obvious how to formalize that!  Here's one way: it's
     correct, but not very practical. *)

Fixpoint forall_nodes (t: tree) (P: tree->key->V->tree->Prop) : Prop :=
 match t with
 | E => True
 | T l k v r => P l k v r /\ forall_nodes l P /\ forall_nodes r P
 end.

Definition SearchTreeX (t: tree) :=
 forall_nodes t
   (fun l k v r =>
      forall_nodes l (fun _ j _ _ => j<k) /\
      forall_nodes r (fun _ j _ _ => j>k)).

Lemma example_SearchTree_good:
   forall v2 v4 v5, SearchTreeX (example_tree v2 v4 v5).
Proof.
intros.
hnf. simpl.
repeat split; auto.
Qed.

Lemma example_SearchTree_bad:
   forall v, ~SearchTreeX (T (T E 3 v E) 2 v E).
Proof.
intros.
intro.
hnf in H; simpl in H.
do 3 destruct H.
omega.
Qed.

Theorem elements_relate_second_attempt:
  forall t cts,
  SearchTreeX t ->
  Abs t cts ->
  list2map (elements t) = cts.
Proof.

(** This is probably provable.  But the [SearchTreeX] property is
   quite unwieldy, with its two Fixpoints nested inside a Fixpoint.
   Instead of using [SearchTreeX], let's reformulate the searchtree
   property as an inductive proposition without any nested
   induction. *)

Abort.

Inductive SearchTree' : key -> tree -> key -> Prop :=
| ST_E : forall lo hi, lo <= hi -> SearchTree' lo E hi
| ST_T: forall lo l k v r hi,
    SearchTree' lo l k ->
    SearchTree' (S k) r hi ->
    SearchTree' lo (T l k v r) hi.

Inductive SearchTree: tree -> Prop :=
| ST_intro: forall t hi, SearchTree' 0 t hi -> SearchTree t.

Lemma SearchTree'_le:
  forall lo t hi, @SearchTree' lo t hi -> lo <= hi.
Proof.
induction 1; omega.
Qed.

(** Before we prove that [elements] is correct, let's consider a simpler version. *)

Fixpoint slow_elements (s: tree) : list (key * V) :=
 match s with
 | E => nil
 | T a k v b => slow_elements a ++ [(k,v)] ++ slow_elements b
 end.

(** This one is easier to understand than the [elements] function,
    because it doesn't carry the [base] list around in its recursion.
    Unfortunately, its running time is quadratic, because at each of
    the [T] nodes it does a linear-time list-concatentation.  The
    original [elements] function takes linear time overall; that's
    much more efficient.

   To prove correctness of [elements], it's actually easier to first
   prove that it's equivalent to [slow_elements], then prove the
   correctness of [slow_elements].  We don't care that [slow_elements]
   is quadratic, because we're never going to really run it; it's just
   there to support the proof. *)

(** **** Exercise: 3 stars, optional (elements_slow_elements)  *)
Theorem elements_slow_elements: elements = slow_elements.
Proof.
extensionality s.
unfold elements.
assert (forall base, elements' s base = slow_elements s ++ base).
(** [] *)
- induction s.
  -- unfold elements'. unfold slow_elements. simpl. auto.
  -- intros. replace (elements' (T s1 k v s2) base) with (elements' s1 ((k,v) :: elements' s2 base)).
    * replace (slow_elements (T s1 k v s2)) with (slow_elements s1 ++ [(k,v)] ++ slow_elements s2).
      ** rewrite -> IHs1. rewrite -> IHs2.
         rewrite <- app_assoc. f_equal.
      ** auto.
    * auto.
- rewrite -> H. rewrite -> app_nil_end. auto.
Qed.
(** [] *)


(** **** Exercise: 3 stars, optional (slow_elements_range)  *)
Lemma slow_elements_range:
 forall k v lo t hi,
  SearchTree' lo t hi ->
  In (k,v) (slow_elements t) ->
  lo <= k < hi.
Proof.
  intros. generalize dependent lo. generalize dependent hi.
  induction t; intros.
  - inv H0.
  - inv H. 
    assert ((In (k, v) (slow_elements t1)) \/ (In (k, v) ([(k0, v0)] ++ slow_elements t2))). 
    -- apply in_app_or. unfold slow_elements in H0. auto.
    -- 
      assert (k0 < hi). eapply SearchTree'_le. apply H8.
      assert (lo <= k0). eapply SearchTree'_le. apply H7.
      destruct H.
      * assert (lo <= k < k0).  apply IHt1. auto. auto.
        destruct H3. split. omega. omega.
      * assert ((In (k, v) [(k0, v0)]) \/ (In (k, v) (slow_elements t2))).
        ** apply in_app_or. apply H.
        ** destruct H3.
          --- inv H3. inv H4.
            + omega. 
            + inv H4.
          --- assert ((S k0) <= k < hi). apply IHt2. auto. auto.
              omega.
Qed.
              
        
(** [] *)

(* ================================================================= *)
(** ** Auxiliary Lemmas About [In] and [list2map] *)


Lemma In_decidable:
  forall (al: list (key*V)) (i: key),
  (exists v, In (i,v) al) \/ (~exists v, In (i,v) al).
Proof.
intros.
induction al as [ | [k v]].
right; intros [w H]; inv H.
destruct IHal as [[w H] | H].
left; exists w; right; auto.
bdestruct (k =? i).
subst k.
left; eauto.
exists v; left; auto.
right. intros [w H1].
destruct H1. inv H1. omega.
apply H; eauto.
Qed.

Lemma list2map_app_left:
  forall (al bl: list (key*V)) (i: key) v,
     In (i,v) al -> list2map (al++bl) i = list2map al i.
Proof.
intros.
revert H; induction al as [| [j w] al]; intro; simpl; auto.
inv H.
destruct H. inv H.
unfold t_update.
bdestruct (i=?i); [ | omega].
auto.
unfold t_update.
bdestruct (j=?i); auto.
Qed.

Lemma list2map_app_right:
  forall (al bl: list (key*V)) (i: key),
     ~(exists v, In (i,v) al) -> list2map (al++bl) i = list2map bl i.
Proof.
intros.
revert H; induction al as [| [j w] al]; intro; simpl; auto.
unfold t_update.
bdestruct (j=?i).
subst j.
contradiction H.
exists w; left; auto.
apply IHal.
contradict H.
destruct H as [u ?].
exists u; right; auto.
Qed.

Lemma list2map_not_in_default:
 forall (al: list (key*V)) (i: key),
   ~(exists v, In (i,v) al) -> list2map al i = default.
Proof.
intros.
induction al as [| [j w] al].
reflexivity.
simpl.
unfold t_update.
bdestruct (j=?i).
subst.
contradiction H.
exists w; left; auto.
apply IHal.
intros [v ?].
apply H. exists v; right; auto.
Qed.

(** **** Exercise: 3 stars, optional (elements_relate)  *)
Theorem elements_relate:
  forall t cts,
  SearchTree t ->
  Abs t cts ->
  list2map (elements t) = cts.
Proof.
rewrite elements_slow_elements.
intros until 1. inv H.
revert cts; induction H0; intros.
* (* ST_E case *)
inv H0.
reflexivity.
* (* ST_T case *)
inv H.
specialize (IHSearchTree'1 _ H5). clear H5.
specialize (IHSearchTree'2 _ H6). clear H6.
unfold slow_elements; fold slow_elements.
subst.
extensionality i.
destruct (In_decidable (slow_elements l) i)  as [[w H] | Hleft].
rewrite list2map_app_left with (v:=w); auto.
pose proof (slow_elements_range _ _ _ _ _ H0_ H).
unfold combine, t_update.
bdestruct (k=?i); [ omega | ].
bdestruct (i<?k); [ | omega].
auto.
(* FILL IN HERE *)
replace (list2map (slow_elements l ++ [(k, v)] ++ slow_elements r) i)
 with (list2map ([(k, v)] ++ slow_elements r) i).
- bdestruct (i =? k).
  + subst. simpl.  unfold t_update. 
    rewrite -> Nat.eqb_refl. auto.
  + assert ((k =? i) = false). apply Nat.eqb_neq. omega.
    replace (list2map ([(k, v)] ++ slow_elements r) i) with ((list2map (slow_elements r)) i).
    -- unfold t_update. rewrite -> H0.
       unfold combine.
       bdestruct (i <? k).
       ++ replace (list2map (slow_elements l) i) with default.
          *** apply list2map_not_in_default. intro. destruct H2.
              assert ((S k) <= i < hi). eapply slow_elements_range. apply H0_0. apply H2.
              omega.
          *** symmetry. apply list2map_not_in_default. auto. 
       ++ auto.
    -- symmetry. apply list2map_app_right. intro.
       destruct H1. inv H1. inv H2. auto. inv H2.
- symmetry. apply list2map_app_right. auto.
Qed.
(** [] *)

(* ################################################################# *)
(** * Preservation of Representation Invariant *)

(** How do we know that all the trees we will encounter (particularly,
  that the [elements] function will encounter), have the [SearchTree]
  property?  Well, the empty tree is a [SearchTree]; and if you insert
  into a tree that's a [SearchTree], then the result is a
  [SearchTree]; and these are the only ways that you're supposed to
  build trees.  So we need to prove those two theorems. *)

(** **** Exercise: 1 star (empty_tree_SearchTree)  *)
Theorem empty_tree_SearchTree:  SearchTree empty_tree.
Proof.
clear default.  (* This is here to avoid a nasty interaction between Admitted
   and Section/Variable.  It's also a hint that the [default] value
   is not needed in this theorem. *)
unfold empty_tree. econstructor. apply (ST_E 0 1). auto.
Qed.
(** [] *)

Lemma SearchTree_relax_l:
  forall lo hi t lo',
   SearchTree' lo t hi -> lo' <= lo -> SearchTree' lo' t hi.
Proof. 
  intros. induction H.
  - constructor. omega.
  - constructor. auto. auto.
Qed.

Lemma SearchTree_relax_r:
  forall lo hi t hi',
   SearchTree' lo t hi -> hi' >= hi -> SearchTree' lo t hi'.
Proof. 
  intros. induction H.
  - constructor. omega.
  - constructor. auto. auto.
Qed.

Theorem insert_SearchTree_aux:
  forall lo hi k v t,
   SearchTree' lo t hi -> SearchTree' (min lo k) (insert k v t) (max (S k) hi).
Proof.
intros. generalize dependent lo. generalize dependent hi.
induction t; intros.
- simpl. constructor.
  + constructor. apply Min.le_min_r.
  + destruct hi. constructor. auto. constructor. apply Peano.le_n_S. Search max.  apply Nat.le_max_l.
- bdestruct (k <? k0).
  * assert ((k <? k0) = true). apply Nat.ltb_lt. omega. 
    replace (insert k v (T t1 k0 v0 t2)) with (T (insert k v t1) k0 v0 t2).
    2 : unfold insert. 2 : rewrite -> H1.  2: auto.
    inv H. constructor.
    -- eapply SearchTree_relax_r. eapply IHt1. apply H8. 
       assert ((S k) <= k0).   omega.   
       assert ((Init.Nat.max (S k) k0) = k0). apply Max.max_r. omega.
       rewrite -> H2. omega.
    -- eapply SearchTree_relax_r. eapply H9. Search max.
       assert ( hi <= (Init.Nat.max (S k) hi)) . apply Nat.le_max_r. omega.
  * assert ((k <? k0) = false). apply Nat.ltb_ge. omega.
    bdestruct (k0 <? k).
    --  assert (k <> k0). omega.
        assert ((k0 <? k) = true). apply Nat.ltb_lt. omega.
        replace (insert k v (T t1 k0 v0 t2)) with (T t1 k0 v0 (insert k v t2)).
        + inv H. constructor.
          --- eapply SearchTree_relax_l. eapply H11. apply Nat.le_min_l.
          --- eapply SearchTree_relax_l. eapply IHt2. apply H12.
              assert ((Init.Nat.min (S k0) k) = (S k0)). 
              ++ apply Min.min_l. omega.
              ++ omega.
        + unfold insert. rewrite -> H1. rewrite -> H4. auto.
    -- assert (k = k0). omega. subst.
       replace (insert k0 v (T t1 k0 v0 t2)) with (T t1 k0 v t2).
       ** inv H. constructor.
          +  eapply SearchTree_relax_l. eauto. apply Nat.le_min_l.
          +  eapply SearchTree_relax_r. eauto. apply Nat.le_max_r.
       ** unfold insert. rewrite -> H1. auto.
Qed.
(** **** Exercise: 3 stars (insert_SearchTree)  *)
Theorem insert_SearchTree:
  forall k v t,
   SearchTree t -> SearchTree (insert k v t).
Proof.
intros.
inv H. econstructor.
eapply SearchTree_relax_l.
eapply SearchTree_relax_r.
eapply insert_SearchTree_aux.
apply H0. auto. auto.
Qed.
(** [] *)

(* ################################################################# *)
(** * We Got Lucky *)

(** Recall the statement of [lookup_relate]: *)

Check lookup_relate.
(*  forall (k : key) (t : tree) (cts : total_map V),
       Abs t cts -> lookup k t = cts (Id k)  *)

(** In general, to prove that a function satisfies the abstraction relation,
   one also needs to use the representation invariant.  That was certainly
   the case with [elements_relate]: *)

Check elements_relate.
(*  : forall (t : tree) (cts : total_map V),
       SearchTree t -> Abs t cts -> elements_property t cts   *)

(** To put that another way, the general form of [lookup_relate] should be: *)

Lemma lookup_relate':
  forall (k : key) (t : tree) (cts : total_map V),
     SearchTree t -> Abs t cts -> lookup k t = cts k.

(** That is certainly provable, since it's a weaker statement than what we proved: *)

Proof.
intros.
apply lookup_relate.
apply H0.
Qed.

Theorem insert_relate':
 forall k v t cts,
    SearchTree t ->
    Abs t cts ->
    Abs (insert k v t) (t_update cts k v).
Proof. intros. apply insert_relate; auto.
Qed.

(** The question is, why did we not need the representation invariant in
   the proof of [lookup_relate]?  The answer is that our particular Abs
   relation is much more clever than necessary:  *)

Print Abs.
(* Inductive Abs : tree -> total_map V -> Prop :=
    Abs_E : Abs E (t_empty default)
  | Abs_T : forall (a b: total_map V) (l: tree) (k: key) (v: V) (r: tree),
            Abs l a ->
            Abs r b ->
	    Abs (T l k v r) (t_update (combine k a b) (Id k) v)
*)
(** Because the [combine] function is chosen very carefully, it turns out
  that this abstraction relation even works on bogus trees! *)

Remark abstraction_of_bogus_tree:
 forall v2 v3,
   Abs (T (T E 3 v3 E) 2 v2 E) (t_update (t_empty default) 2 v2).
Proof.
intros.
evar (m: total_map V).
replace  (t_update (t_empty default) 2 v2) with m; subst m.
repeat constructor.
extensionality x.
unfold t_update, combine, t_empty.
bdestruct (2 =? x).
auto.
bdestruct (x <? 2).
bdestruct (3 =? x).
(* LOOK HERE! *)
omega.
bdestruct (x <? 3).
auto.
auto.
auto.
Qed.

(** Step through the proof to [LOOK HERE], and notice what's going on.
   Just when it seems that [(T (T E 3 v3 E) 2 v2 E)] is about to produce [v3]
  while [(t_update (t_empty default) (Id 2) v2)] is about to produce [default],
  [omega] finds a contradiction.  What's happening is that [combine 2]
  is careful to ignore any keys >= 2 in the left-hand subtree.

  For that reason, [Abs] matches the _actual_ behavior of [lookup],
  even on bogus trees.  But that's a really strong condition!  We should
  not have to care about the behavior of [lookup] (and [insert]) on
  bogus trees.  We should not need to prove anything about it, either.

  Sure, it's convenient in this case that the abstraction relation is able to
  cope with ill-formed trees.  But in general, when proving correctness of
  abstract-data-type (ADT) implementations, it may be a lot of extra
  effort to make the abstraction relation as heavy-duty as that.
  It's often much easier for the abstraction relation to assume that the
  representation is well formed.  Thus, the general statement of our
  correctness theorems will be more like [lookup_relate'] than like
  [lookup_relate].  *)

(* ################################################################# *)
(** * Every Well-Formed Tree Does Actually Relate to an Abstraction *)

(** We're not quite done yet.  We would like to know that
    _every tree that satisfies the representation invariant, means something_.

   So as a general sanity check, we need the following theorem: *)

(** **** Exercise: 2 stars (can_relate)  *)
Lemma can_relate:
 forall t,  SearchTree t -> exists cts, Abs t cts.
Proof.
   intros. inv H. induction H0.
   - econstructor. econstructor.
   - destruct IHSearchTree'1. destruct IHSearchTree'2.
     econstructor. constructor. eauto. eauto.
Qed.
(** [] *)

(** Now, because we happen to have a super-strong abstraction relation, that
   even works on bogus trees, we can prove a super-strong can_relate function: *)

(** **** Exercise: 2 stars (unrealistically_strong_can_relate)  *)
Lemma unrealistically_strong_can_relate:
 forall t,  exists cts, Abs t cts.
Proof.
  intros. induction t.
  - econstructor. econstructor.
  - destruct IHt1. destruct IHt2. econstructor. econstructor. eauto. eauto.
Qed.
(** [] *)

(* ################################################################# *)
(** * It Wasn't Really Luck, Actually *)

(** In the previous section, I said, "we got lucky that the abstraction
    relation that I happened to choose had this super-strong property."

    But actually, the first time I tried to prove correctness of search trees,
    I did _not_ get lucky.  I chose a different abstraction relation: *)

Definition AbsX (t: tree) (m: total_map V) : Prop :=
    list2map (elements t) = m.

(** It's easy to prove that [elements] respects this abstraction relation: *)

Theorem elements_relateX:
  forall t cts,
  SearchTree t ->
  AbsX t cts ->
  list2map (elements t) = cts.
Proof.
intros.
apply H0.
Qed.

(** But it's not so easy to prove that [lookup] and [insert] respect this
    relation.  For example, the following claim is not true. *)

Theorem naive_lookup_relateX:
  forall k t cts ,
    AbsX t cts -> lookup k t =  cts k.
Abort.  (* Not true *)

(** In fact, [naive_lookup_relateX] is provably false,
     as long as the type [V] contains at least two different values. *)

Theorem not_naive_lookup_relateX:
   forall v, default <> v ->
    ~ (forall k t cts , AbsX t cts -> lookup k t =  cts k).
Proof.
unfold AbsX.
intros v H.
intros H0.
pose (bogus := T (T E 3 v E) 2 v E).
pose (m := t_update (t_update (t_empty default) 2 v) 3 v).
assert (list2map (elements bogus) = m).
  reflexivity.
assert (~ lookup 3 bogus = m 3). {
  unfold bogus, m, t_update, t_empty.
  simpl.
  apply H.
}
(** Right here you see how it is proved.  [bogus] is our old friend,
    the bogus tree that does not satisfy the [SearchTree] property.
    [m] is the [total_map] that corresponds to the elements of [bogus].
    The [lookup] function returns [default] at key [3],
    but the map [m] returns [v] at key [3].  And yet, assumption [H0]
    claims that they should return the same thing. *)
apply H2.
apply H0.
apply H1.
Qed.

(** **** Exercise: 4 stars, optional (lookup_relateX)  *)
Theorem lookup_relateX:
  forall k t cts ,
    SearchTree t -> AbsX t cts -> lookup k t =  cts k.
Proof.
intros.
unfold AbsX in H0. subst cts.
inv H. remember 0 as lo in H0.
clear - H0.
rewrite elements_slow_elements.
(** To prove this, you'll need to use this collection of facts:
   [In_decidable], [list2map_app_left], [list2map_app_right],
   [list2map_not_in_default], [slow_elements_range].  The point is,
   it's not very pretty. *)
induction H0.
- simpl. auto.
- replace (slow_elements (T l k0 v r)) with ((slow_elements l) ++ ((k0, v) :: (slow_elements r))).
  2: unfold slow_elements. 2: auto. 
  destruct (In_decidable (slow_elements l) k ).
  + destruct H. replace (lookup k (T l k0 v r)) with (lookup k l).
       ** erewrite -> list2map_app_left. 2 : apply H. eapply IHSearchTree'1.
       ** assert (lo <= k < k0). eapply slow_elements_range. apply H0_. apply H.
          destruct H0. unfold lookup. bdestruct (k <? k0). auto. omega.  
  + bdestruct (k =? k0).
    -- subst.  simpl. rewrite -> Nat.ltb_irrefl. 
       erewrite -> list2map_app_right.
       ++ simpl. unfold t_update. rewrite -> Nat.eqb_refl. auto.
       ++ intro. destruct H0. apply H. exists x. eapply H0.
    -- assert ((k0 =? k) = false). apply Nat.eqb_neq. omega.
       destruct (In_decidable (slow_elements r) k ).
       ++ destruct H2.
          erewrite -> list2map_app_right.
          2 : apply H.
          replace (list2map ((k0, v) :: slow_elements r) k) with (list2map (slow_elements r) k).
          --- assert ((S k0) <= k < hi). eapply slow_elements_range. apply H0_0. eapply H2.
              replace (lookup k (T l k0 v r)) with (lookup k r).
              +++ auto.
              +++ destruct H3.  unfold lookup. 
                  bdestruct (k <? k0).
                  *** omega.
                  *** bdestruct (k0 <? k). auto. omega.
          --- simpl. unfold t_update. rewrite -> H1. auto.
       ++ rewrite -> list2map_not_in_default.
          * bdestruct (k =? k0). omega.
            bdestruct ( k <? k0).
            +++ replace (lookup k (T l k0 v r)) with (lookup k l).
                ****  rewrite -> IHSearchTree'1. apply list2map_not_in_default. auto.
                ****  assert ((k <? k0) = true). apply Nat.ltb_lt. omega. unfold lookup.
                      rewrite -> H5. auto. 
            +++  assert ((k <? k0) = false). apply Nat.ltb_ge. omega. 
                 replace (lookup k (T l k0 v r)) with (lookup k r).
                 **** rewrite -> IHSearchTree'2.  apply list2map_not_in_default. auto.
                 ****  assert ((k0 <? k) = true). bdestruct (((k0 <? k))). auto. omega.
                       unfold lookup. rewrite -> H5. rewrite -> H6. auto. 
          * intro. destruct H3.
            assert ((In (k, x) (slow_elements l)) \/ ((In (k, x) ((k0, v) :: slow_elements r)))).
            --- apply in_app_or. auto.
            --- destruct H4. 
                **** apply H. eauto.
                **** inv H4. inv H5. auto.
                     apply H2. eauto.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Coherence With [elements] Instead of [lookup] *)
(** The first definition of the abstraction relation, [Abs], is "coherent"
     with the [lookup] operation, but not very coherent with the [elements]
     operation.  That is, [Abs] treats all trees, including ill-formed ones,
     much the way [lookup] does, so it was easy to prove [lookup_relate].
     But it was harder to prove [elements_relate].

    The alternate abstraction relation, [AbsX], is coherent with [elements],
    but not very coherent with [lookup].  So proving [elements_relateX] is
    trivial, but proving [lookup_relate] is difficult.

    This kind of thing comes up frequently.  The important thing to remember
    is that you often have choices in formulating the abstraction relation,
    and the choice you make will affect the simplicity and elegance of your
    proofs.   If you find things getting too difficult, step back and reconsider
    your abstraction relation. *)

End TREES.
