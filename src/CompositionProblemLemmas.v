Require Import ZProperty Confluence LambdaES lx Lia.

Lemma open_rec_P_fvar: forall t x n, {n ~> pterm_fvar x} (P t) = P ({n ~> pterm_fvar x} t).
Proof.
  intros t.
  induction t.
  - intros x n'.
    simpl.
    destruct (n =? n'); reflexivity.
  - intros x n.
    reflexivity.
  - intros x n.
    simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  - intros x n.
    simpl.
    rewrite IHt; reflexivity.
  - intros x n.
    simpl.
    unfold open.
    simpl in *. (** problema da composicionalidade **)
Admitted.

Lemma term_P_open_rec_fvar: forall t x, term (P (t ^ x)) -> term (P t ^ x).
Proof.
  induction t using pterm_size_induction.
  generalize dependent H.
  unfold open.
  generalize dependent 0.
  case t.
  - intros n n' IH x Hlterm.
    simpl in *.
    destruct (n =? n') eqn:H.
    + apply term_var.
    + simpl in Hlterm.
      inversion Hlterm.
      * apply Hlterm.
  - intros v n IH x Hlterm.
    simpl.
    apply term_var.
  - intros t1 t2 n IH x Hlterm.
    simpl in *.
    inversion Hlterm; subst; clear Hlterm.
    apply term_app.
    + apply IH.
      * lia.
      * assumption.
    + apply IH.
      * lia.
      * assumption.
  - intros t' n IH x Hlterm.
    simpl in *.
    rewrite open_rec_P_fvar.
    assumption.
  - intros.
    simpl in *.
    unfold open in *. (** problema da composicionalidade *)
    admit.
Admitted.

Lemma term_P: forall t, term t -> term (P t).
Proof.
  intros t0 IH.
  induction IH.
  - simpl.
    apply term_bvar.
  - simpl.
    apply term_var.
  - simpl.
    apply term_app.
    + assumption.
    + assumption.
  - simpl.
    apply term_abs with L.
    intros x Hnot_union.
    unfold open.
    apply term_P_open_rec_fvar.
    apply H0.
    assumption.
  - simpl.
Admitted.