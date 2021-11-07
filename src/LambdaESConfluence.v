Require Import ZProperty Confluence LambdaES lx CompositionProblemLemmas OpenPoints Lia.

Lemma lterm_open_rec_rename: forall t x y n, lterm ({n ~> pterm_fvar x} t) -> lterm ({n ~> pterm_fvar y} t).  
Proof.
  intros t x y.
  induction t.
  - intros n0 Hlterm.
    simpl.
    destruct(n =? n0).
    + apply lterm_var.
    + apply lterm_bvar.
  - intros.
    simpl.
    apply lterm_var.
  - intros.
    simpl.
    inversion H; subst.
    apply lterm_app.
    + apply IHt1.
      assumption.
    + apply IHt2.
      assumption.
  - intros.
    simpl in *.
    apply lterm_abs.
    apply IHt.
    inversion H.
    assumption.
  - intros.
    inversion H.
Qed.

Lemma lterm_open_rec_L: forall t1 t2, (exists L, forall x, x \notin L -> lterm (t1 ^ x)) -> lterm t2 -> lterm (t1 ^^ t2).
Proof.
  intros t1 t2 H1 H2.
  unfold open in *.
  generalize dependent 0.
  induction t1 using pterm_size_induction.
  generalize dependent H.
  case t1.
  - intros n IH n' H.
    apply lterm_msub.
    + apply lterm_bvar.
    + assumption.
  - intros v IH n H.
    apply lterm_msub.
    + apply lterm_var.
    + assumption.
  - intros t11 t12 IH n H.
    inversion H as [L]. clear H.
    pick_fresh x.
    apply notin_union in Fr.
    destruct Fr as [Fr Ht12].
    apply notin_union in Fr.
    destruct Fr as [Fr Ht11].
    apply notin_union in Fr.
    destruct Fr as [Fr Ht2].
    apply notin_union in Fr.
    destruct Fr as [Fr Ht1].
    apply notin_union in Fr.
    destruct Fr as [Fr Hn].
    simpl in *.
    apply H0 in Fr. clear H0.
    inversion Fr; subst; clear Fr.
    apply lterm_app.
    + apply IH.
      * lia.
      * exists L.
        intros x' Hnotin.
        apply lterm_open_rec_rename with x.
        apply H1; assumption.
    + apply IH.
      * lia.
      * exists L.
        intros x' Hnotin.
        apply lterm_open_rec_rename with x.
        apply H3.
  - intros t11 IH n H.
    simpl in *.
    inversion H as [L]. clear H.
    pick_fresh x.
    apply notin_union in Fr.
    destruct Fr as [Fr Ht11].
    apply notin_union in Fr.
    destruct Fr as [Fr Ht2].
    apply notin_union in Fr.
    destruct Fr as [Fr Ht1].
    apply notin_union in Fr.
    destruct Fr as [Fr Hn].
    assert (Fr' := Fr).
    apply H0 in Fr'. clear H0.
    inversion Fr'; subst. clear Fr'.
    unfold open in *.
    apply lterm_abs.
    apply IH.
    + lia.
    + exists L.
    intros x'' HL'.
    apply lterm_open_rec_rename with x.
    assumption.
  - intros t11 t12 IH n H.
    simpl in *.
    inversion H as [L]. clear H.
    pick_fresh x.
    apply notin_union in Fr.
    destruct Fr as [Fr Ht12].
    apply notin_union in Fr.
    destruct Fr as [Fr Ht11].
    apply notin_union in Fr.
    destruct Fr as [Fr Ht2].
    apply notin_union in Fr.
    destruct Fr as [Fr Ht1].
    apply notin_union in Fr.
    destruct Fr as [Fr Hn].
    apply H0 in Fr.
    inversion Fr.
Qed.

Lemma lterm_open_rec: forall t1 t2 x, lterm (t1 ^ x) -> lterm t2 -> lterm (t1 ^^ t2).
Proof.
  intros t1 t2 x.
  unfold open.
  generalize dependent 0.
  generalize dependent x.
  generalize dependent t2.
  induction t1 using pterm_size_induction.
  generalize dependent H.
  case t1.
  - intros n IH t2 x n' H1 H2.
    simpl in *.
    destruct (n =? n') eqn:H.
    + assumption.
    + apply H1.
  - intros v IH t2 x n H1 H2.
    simpl.
    apply lterm_var.
  - intros t11 t12 IH t2 x n H1 H2.
    simpl in *.
    inversion H1; subst; clear H1.
    apply lterm_app.
    + apply IH with x.
      * lia. 
      * assumption.
      * assumption.
    + apply IH with x.
      * lia. 
      * assumption.
      * assumption.
  - intros t11 IH t2 x n H1 H2.
    simpl in *.
    apply lterm_abs.
    apply IH with x.
    + lia.
    + inversion H1.
      assumption.
    + assumption.
  - intros t1' t2 IH t2' x n H1 H2.
    simpl in *.
    inversion H1.
Qed.     

Lemma llc_at_P: forall t n, llc_at n t -> llc_at n (P t). 
Proof.
  intros t.
  induction t.
  - intros n' H.
    simpl in *.
    assumption.
  - intros n H.
    simpl in *.
    auto.
  - intros n H.
    simpl in *.
    destruct H as [H1 H2]; split.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros n H.
    simpl in *.
    apply IHt; assumption.
  - intros n H.
    simpl in *.
    contradiction.
Qed.

Lemma lc_at_open_rec_eq: forall t1 t2 i, lc_at (S i) t1 -> lc_at i t2 -> lc_at i ({i ~> t2} t1).
Proof.
  induction t1.
  - intros t2 i H.
    simpl in *.
    destruct (n =? i) eqn:Heq.
    + intro Hlc; assumption.
    + intro Hlc.
      simpl.
      apply EqNat.beq_nat_false in Heq.
      apply Lt.lt_n_Sm_le in H.
      apply PeanoNat.Nat.le_lteq in H.
      destruct H.
      * assumption.
      * subst.
        contradiction.
  - intros t2 i H1 H2.
    auto.
  - intros t2 i H1 H2.
    simpl in *.
    destruct H1 as [H11 H12]; split.
    + apply IHt1_1; assumption.
    + apply IHt1_2; assumption.
  - intros t2 i H1 H2.
    simpl in *.
    apply IHt1.
    + assumption.
    + apply lc_at_weaken_ind with i.
      * assumption.
      * auto.
  - intros t2 i H1 H2.
    simpl in *.
    destruct H1 as [H11 H12]; split.
    + apply IHt1_1.
      * assumption.
      * apply lc_at_weaken_ind with i.
        ** assumption.
        ** auto.
    + apply IHt1_2; assumption.
Qed.

Lemma term_P_lterm: forall t, lterm (P t).
Proof.
  intros t.
  induction t.
  - simpl. apply lterm_bvar.
  - simpl. apply lterm_var.
  - simpl. apply lterm_app.
    + apply IHt1.
    + apply IHt2.
  - simpl. apply lterm_abs.
    apply IHt.
  - simpl. 
    apply lterm_msub.
    + apply IHt1.
    + apply IHt2.
Qed.

Lemma lterm_open_fvar_P: forall t x, lterm (P t ^ x) -> lterm (P (t ^ x)).
Proof.
  intros.
  apply term_P_lterm.
Qed.

Lemma lterm_P_open_fvar: forall t x, lterm (P (t ^ x)) -> lterm (P t ^ x).
Proof.
  intros t x H.
  unfold open in *.
  generalize dependent 0.
  generalize dependent x.
  induction t.
  - intros x n' H.
    generalize dependent H.
    case n.
    + intro H.
      simpl in *.
      destruct (0 =? n').
      * apply lterm_var.
      * assumption.
    + intros n'' H.
      simpl in *.
      destruct (S n'' =? n').
      * apply lterm_var.
      * assumption.
  - intros x n H.
    simpl.
    apply lterm_var.
  - intros x n H.
    simpl in *.
    inversion H; subst; clear H.
    apply lterm_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros x n H.
    simpl in *.
    apply lterm_abs.
    apply IHt.
    inversion H. subst. clear H.
    assumption.
  - intros x n H.
    simpl in *.
    unfold open in *.
    apply lterm_msub.
    + apply lterm_msub.
      * apply term_P_lterm.
      * apply term_P_lterm.
    + apply lterm_var.
Qed.

Lemma lterm_open_fvar_P_equiv: forall t x, lterm (P (t ^ x)) <-> lterm (P t ^ x).
Proof.
  intros.
  split.
  + apply lterm_P_open_fvar.
  + apply lterm_open_fvar_P.
Qed.

Lemma open_rec_P: forall t u n, lterm t -> P({n ~> u} t) = {n ~> P u} (P t).
Proof.
  intros t.
  induction t.
  - intros u n0 Hlterm.
    simpl.
    destruct (n =? n0).
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
  - simpl.
    intros.
    reflexivity.
  - intros.
    simpl.
    rewrite IHt1.
    + rewrite IHt2.
      * reflexivity.
      * inversion H.
        assumption.
    + inversion H.
      assumption.
  - intros.
    simpl.
    rewrite IHt.
    reflexivity.
    inversion H.
    assumption.
  - intros.
    inversion H.
Qed.

Lemma lterm_P_id: forall t, lterm t -> P t = t.
Proof.
  induction 1.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHlterm1.
    rewrite IHlterm2.
    reflexivity.
  - simpl. 
    rewrite IHlterm.
    reflexivity.
Qed.

Theorem lambda_x_Z_comp_eq: Z_comp_eq lx.
Proof.
  unfold Z_comp_eq.
  exists x_ctx, b_ctx, P, B. split.
  - intros x y; split.
    + intro HBx.
      apply union_or.
      inversion HBx; subst.
      * right; assumption.
      * left; assumption.
    + intro Hunion.
      apply union_or in Hunion.
      inversion Hunion.
      * apply x_ctx_rule. assumption.
      * apply b_ctx_rule. assumption.
  - split.
    + apply sys_x_P_eq.
    + split.
      * apply t_reduces_to_P_t.
      * split.
        ** intros b a Heq.
          apply term_to_B.
          rewrite -> Heq.
          apply term_P_lterm.
        ** apply B_comp_P_is_weak_Z_for_B_by_lx.
Qed.

Theorem lambda_x_is_confluent: Confl lx.
Proof.
  apply Zprop_implies_Confl_via_SemiConfl.
  apply Z_comp_eq_implies_Z_prop.
  apply lambda_x_Z_comp_eq.
Qed.
