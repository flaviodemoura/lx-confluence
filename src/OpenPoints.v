Require Import ZProperty Confluence LambdaES lx CompositionProblemLemmas.

Lemma full_comp: forall t u, t[u] ->_x* (t ^^ u).
Proof.
Admitted.

Lemma substitution_equality_with_P: forall t1 t2 n x, P({n ~> pterm_fvar x} t1) = P({n ~> pterm_fvar x} t2) -> P(t1) = P(t2).
Proof. 
  intros.
Admitted.

Lemma sys_x_P_eq: forall t1 t2, t1 ->_x t2 -> P t1 = P t2.
Proof.
  intros t1 t2 H.
  induction H.
  - inversion H; subst.
    + simpl.
      reflexivity.
    + simpl. unfold open in *. apply term_P in H0. 
      rewrite open_rec_term. 
      * inversion H.
        ** admit.
        ** admit.
      * apply term_bvar.
    + unfold open in *.
      simpl.
      admit.
    + reflexivity.
    + simpl. unfold open in *.
      simpl.
      admit.
  - simpl.
    rewrite IHES_contextual_closure.
    reflexivity.
  - simpl.
    rewrite IHES_contextual_closure.
    reflexivity.
  - simpl.
    pick_fresh x.
    apply notin_union in Fr.
    destruct Fr.
    apply notin_union in H1.
    destruct H1.
    apply H0 in H1.
    unfold open in H1.
    simpl in H1.
    apply substitution_equality_with_P in H1.
    rewrite H1.
    reflexivity.
  - simpl. 
    unfold open in *.
    simpl.
    pick_fresh x.
    apply notin_union in Fr.
    destruct Fr.
    apply notin_union in H2.
    destruct H2.
    apply notin_union in H2.
    destruct H2.
    apply H0 in H2.
    apply substitution_equality_with_P in H2.
    rewrite H2.
    reflexivity.
  - simpl.
    rewrite IHES_contextual_closure.
    reflexivity.
Admitted.

Lemma open_lemma: forall t x, (t ->_x* P t) -> (t^x ->_x* P t ^ x).
Proof.
  intros t x H.
  induction t.
  - simpl. 
    apply refl.
  - simpl.
    apply refl.
  - simpl.
    admit.
  - simpl.
    admit.
Admitted.

Lemma t_reduces_to_P_t: forall t, t ->_x* P t. 
Proof.
  intros t.
  induction t.
  - simpl.
    apply refl.
  - simpl.
    apply refl.
  - simpl. 
    apply x_star_app_comp.  
    + assumption.
    + assumption.
  - simpl.
    apply x_star_abs with (fv t).
    intros x Hnotin.
    apply open_lemma.
    assumption.
  - simpl.
    unfold open.
Admitted.

Lemma term_to_B: forall t, lterm t -> t ->_lx* B t.
Proof.
  intros t Htlterm.
  induction Htlterm.
  - simpl.
    apply refl.
  - simpl.
    apply refl.
  - simpl.
    admit.
  - simpl.
    
    admit.
Admitted.

Lemma B_comp_P_is_weak_Z_for_B_by_lx: f_is_weak_Z b_ctx lx (B # P).
Proof.
  unfold f_is_weak_Z.
  intros a b IH.
  induction IH.
  admit.
Admitted.