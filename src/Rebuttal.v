Require Import ZProperty Confluence LambdaES lx CompositionProblemLemmas OpenPoints Lia.

Lemma open_rec_swap_term: forall t t' x i j, i <> j -> term t' -> {j ~> pterm_fvar x} ({i ~> t'} t) = {i ~> t'}({j ~> pterm_fvar x} t).
Proof.
  intro t; induction t.
  - intros t' x i j Hneq Hterm.
    simpl.
    destruct (n =? i) eqn: Hni.
    + destruct (n =? j) eqn: Hnj.
      * admit. (* ok *)
      * admit. (* ok *)
    + destruct (n =? j) eqn: Hnj.
      * simpl.
        rewrite Hnj. 
        reflexivity.
      * simpl. 
        rewrite Hni.
        rewrite Hnj.
        reflexivity.
  - intros t' x i j Hneq Hterm.
    reflexivity.
  - intros t' x i j Hneq Hterm.
     simpl.
     rewrite IHt1.
     + rewrite IHt2.
       * reflexivity.
       * assumption.
       * assumption.
     + assumption.
     + assumption.
  - intros t' x i j Hneq Hterm.
    simpl.
    rewrite IHt.
    + reflexivity.
    + lia. 
    + assumption.
  - intros t' x i j Hneq Hterm.
    simpl.
    rewrite IHt1.
    + rewrite IHt2.
      * reflexivity.
      * assumption.
      * assumption.
    + lia.
    + assumption.
Admitted.


Lemma open_rec_swap_eq: forall t t' x n, {n ~> pterm_fvar x} ({n ~> t'} t) = { n ~> { n ~> pterm_fvar x} t'} t.
Proof.
  intro t; induction t.
  - intros t x n'.
    simpl.
    destruct (n =? n') eqn:H.
    + reflexivity.
    + simpl.
      rewrite H; reflexivity.
  - intros t x n.
    reflexivity.
  - intros t x n.
    simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  - intros t x n.
    simpl.
    rewrite IHt.
Admitted.  (* problema da composicionalidade *)


Lemma open_rec_swap_neq': forall t t' x i j, i <> j -> {j ~> pterm_fvar x} ({i ~> t'} t) = {i ~> {j ~> pterm_fvar x} t'}({S j ~> pterm_fvar x} t).
Proof.
  intro t; induction t.
  - intros. 
    simpl.
    destruct (n =? i) eqn:Hni.
    + destruct (n =? j) eqn:Hnj.
      * admit.
      * admit.
    + destruct (n =? j) eqn:Hnj.
      * admit.
      * admit.
  - intros.
    simpl.
    reflexivity.
  - intros.
    simpl.
    rewrite IHt1.
    + rewrite IHt2.
      * reflexivity.
      * assumption.
    + assumption.
  - intros.
    simpl.
    rewrite IHt.
    + admit.
    + lia.
Admitted.

Lemma open_rec_swap_neq: forall t t' x i j, i <> j -> {j ~> pterm_fvar x} ({i ~> t'} t) = {i ~> {j ~> pterm_fvar x} t'}({j ~> pterm_fvar x} t).
Proof.
  intro t; induction t.
  - intros t' x i j Hneq.
    simpl.
    destruct (n =? i) eqn:Hni.
    + destruct (n =? j) eqn:Hnj.
      * apply beq_nat_true in Hni.
        apply beq_nat_true in Hnj.
        subst.
        contradiction.
      * apply beq_nat_true in Hni.
        subst.
        simpl.
        rewrite <- beq_nat_refl.
        reflexivity.
    + destruct (n =? j) eqn:Hnj.
      * simpl.
        rewrite Hnj.
        reflexivity.
      * simpl.
        rewrite Hni.
        rewrite Hnj.
        reflexivity.
  - intros t x i j Hneq.
    simpl.
    reflexivity.
  - intros t x i j Hneq.
    simpl.
    rewrite IHt1.
    + rewrite IHt2.
      * reflexivity.
      * assumption.
    + assumption.
  - intros t x i j Hneq.
    simpl.
    rewrite IHt.
    + admit. (* problema com composicionalidade. *)
    + lia.
  - intros t x i j Hneq.
    simpl.
    rewrite IHt1.
    + rewrite IHt2.
      * admit. (* problema composicionalidade *)
      * assumption.
    + lia. 
Admitted.

(**
i = 0
j = 1

x = j

t = S i
t'= j

{j ~> pterm_fvar x} ({i ~> j} t)

{i ~> {j ~> pterm_fvar x} t'}({j ~> pterm_fvar x} \ S i)


*)