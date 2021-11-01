(** * An application: Proving the confluence of a variant of the lx-calculus. *)

Require Import ZProperty Confluence InfraES.

(** Lx rules *)
Inductive rule_b : Rel pterm  :=
  reg_rule_b : forall (t u:pterm),
    body t -> term u ->
    rule_b (pterm_app(pterm_abs t) u) (t[u]).

Lemma term_regular_b: term_regular rule_b.
Proof.
 unfold term_regular.
 intros t t' Hr.
 inversion Hr; subst.
 split.
 - apply term_app.
   + unfold body in H.
     destruct H.
     apply term_abs with x.
     assumption.
   + assumption. 
 - unfold body in H.
   destruct H.
   apply term_sub with x; assumption.
Qed.

Lemma rule_b_compat_open: forall t t' n x, rule_b t t' -> rule_b ({n ~> pterm_fvar x}t) ({n ~> pterm_fvar x}t').
Proof.
  intros t1 t2 n x.
  - intro Hrule_b.
    inversion Hrule_b; subst.
    simpl.
    apply reg_rule_b.
    + unfold body in *.
      destruct  H.
      exists x0. intros x1 Hnotin.
      unfold open.
      apply term_equiv_lc_at.
      apply lc_at_open_rec.
      * apply term_var.
      * apply lc_at_open_rec_leq.
        ** apply Peano.le_n_S.
           apply Peano.le_0_n.
        ** apply  body_lc_at.
           unfold body.
           exists x0; assumption.
    + assert (H' : {n ~> pterm_fvar x} u = u).
      * apply open_rec_term; assumption.
      * rewrite H'; assumption.
Qed.

Lemma open_rec_msb: forall t k x y x0, x <> x0 -> [x ~> pterm_fvar y] (open_rec k (pterm_fvar x0) t) = (open_rec k (pterm_fvar x0) ([x ~> pterm_fvar y] t)).
Proof.
  intro t; induction t using pterm_size_induction.
  intros k x y x0 Hdiff.
  generalize dependent t.
  intro t; case t.
  - intros n IH.
    simpl.
    case (n =? k) eqn:H.
    + simpl.
      case (x0 =? x) eqn:H'.
      * apply EqNat.beq_nat_true in H'.
        contradiction.
      * reflexivity.
    + reflexivity.
  - intros v IH.
    simpl.
    case (v =? x) eqn:H; reflexivity.
  - intros t1 t2 IH.
    simpl in *.
    rewrite IH.
    + rewrite IH.
      * reflexivity.
      * auto with arith.
      * assumption.
    + auto with arith.
    + assumption.
  - intros t1 IH.
    simpl in *.
    rewrite IH.
    + reflexivity.
    + auto with arith.
    + assumption.
  - intros t1 t2 IH.
    simpl in *.
    rewrite IH.
    + rewrite IH.
      * reflexivity.
      * auto with arith.
      * assumption.
    + auto with arith.
    + assumption.
Qed.

Corollary open_msb: forall t x y x0, x <> x0 -> [x ~> pterm_fvar y] t ^ x0 = ([x ~> pterm_fvar y] t) ^ x0.
Proof.
  intros t x y x0.
  apply open_rec_msb; assumption.
Qed.

Lemma term_rename: forall t x y, term t -> term ([x ~> pterm_fvar y] t).
Proof.
  intros t x y H; induction H.
  - simpl.
    case (x0 =? x); apply term_var.
  - simpl; apply term_app; assumption.
  - specialize (H x).
    apply term_abs with (L \u {{x}} \u {{y}} \u fv t1); fold m_sb.
    intros x0 Hnot.
    apply notin_union in Hnot.
    destruct Hnot as [Hnot Hnot1].
    apply notin_union in Hnot.
    destruct Hnot as [Hnot Hnoty].
    apply notin_union in Hnot.
    destruct Hnot as [Hnot Hnotx].
    replace (([x ~> pterm_fvar y] t1) ^ x0) with ([x ~> pterm_fvar y] (t1 ^ x0)).
    + apply H0; assumption.
    + apply notin_neq in Hnotx.
      apply open_msb.
      intro H'.
      symmetry in H'.
      generalize dependent H'.
      assumption.
  - simpl.
    apply term_sub with (L \u {{x}}).
    + intros x' Hnotin.
      apply notin_union in Hnotin.
      destruct Hnotin as [HL Hx].
      rewrite <- open_msb.
      * apply H0; assumption.
      * apply notin_neq in Hx.
        intro H'.
        symmetry in H'.
        generalize dependent H'.
        assumption.
    + assumption.
Qed.

Lemma body_rename: forall t x y, body t -> body ([x ~> pterm_fvar y] t).
Proof.
  intros t x y Hbody.
  unfold body in *.
  destruct Hbody as [L].
  exists (L \u {{ x }} \u {{ y }}).
  pick_fresh z.
  intros x1 Hnot.
  apply notin_union in Hnot.
  destruct Hnot as [Hnot Hnoty].
  apply notin_union in Hnot.
  destruct Hnot as [Hnot Hnotx].
  apply notin_union in Fr.
  destruct Fr as [Fr Hfvt].
  apply notin_union in Fr.
  destruct Fr as [Fr Hy].
  apply notin_union in Fr.
  destruct Fr as [Fr Hx].
  rewrite <- open_msb.
  - apply term_rename.
    apply H; assumption.
  - apply notin_neq in Hnotx.
    intro H'.
    symmetry in H'.
    generalize dependent H'.
    assumption.
Qed.
 
Lemma red_out:  forall t t' x y, rule_b t t' -> rule_b ([x ~> pterm_fvar y] t) ([x ~> pterm_fvar y] t').
Proof.
  intros t t' x y H.
  inversion H; subst.
  simpl.
  apply reg_rule_b.
  - apply body_rename; assumption.
  - apply term_rename; assumption.
Qed.    
  
Lemma red_rename_b: red_rename rule_b.
Proof.
  unfold red_rename.
  intros x t t' y Hfv Hfv' Hb.
  assert (Hsb: t^y = [x ~> pterm_fvar y] t ^ x).
  - symmetry.
    apply m_sb_intro; assumption.
  - rewrite Hsb.
    assert (Hsb': t' ^ y = [x ~> pterm_fvar y] t' ^ x).
    {
      symmetry.
      apply m_sb_intro_open; assumption.
    }
    rewrite Hsb'.
    apply red_out; assumption.
Qed.  

Definition b_ctx t u := ES_contextual_closure rule_b t u. 
Notation "t ->_B u" := (b_ctx t u) (at level 66).
Notation "t ->_B* u" := ((refltrans b_ctx) t u) (at level 66).
                           
Corollary term_regular_b_ctx : term_regular b_ctx.
Proof.
  apply term_regular_ctx.
  apply term_regular_b.
Qed.

Lemma red_rename_b_ctx: red_rename b_ctx.
Proof.
  unfold red_rename.
  intros x t t' y Ht Ht' HB.
Admitted.

Lemma B_app_left: forall t1 t2 t3, term t3 -> t1 ->_B* t2 -> pterm_app t1 t3 ->_B* pterm_app t2 t3.
Proof.
  intros t1 t2 t3 Hterm HB.
  induction HB.
  - apply refl.
  - apply rtrans with (pterm_app b t3).
    + apply ES_app_left; assumption.      
    + apply IHHB.
Qed.

Lemma B_app_right: forall t1 t2 t3, term t1 -> t2 ->_B* t3 -> pterm_app t1 t2 ->_B* pterm_app t1 t3.
Proof.
  intros t1 t2 t3 Hterm HB.
  induction HB.
  - apply refl.
  - apply rtrans with (pterm_app t1 b).
    + apply ES_app_right; assumption.      
    + apply IHHB.
Qed.

(*
Lemma B_abs: forall t1 t2 L, (forall x, x \notin L -> t1^x ->_B* t2^x) -> pterm_abs t1 ->_B* pterm_abs t2.
Proof.
  Admitted.
 *)

Inductive sys_x : Rel pterm :=
| reg_rule_var : forall t, term t -> sys_x (pterm_bvar 0 [t]) t
| reg_rule_gc : forall t u, term t -> term u -> sys_x (t[u]) t
| reg_rule_app : forall t1 t2 u, body t1 -> body t2 -> term u ->
  sys_x ((pterm_app t1 t2)[u]) (pterm_app (t1[u]) (t2[u]))
| reg_rule_abs : forall t u, lc_at 2 t -> term u ->
  sys_x ((pterm_abs t)[u]) (pterm_abs ((& t)[u])).

Lemma term_regular_sys_x: term_regular sys_x.
Proof.
  intros t u Hsys.
  induction Hsys.
  - split.
    + apply term_sub with (fv t).
      * intros x Hfv.
        unfold open; simpl.
        apply term_var.
      * assumption.
    + assumption.
  - split.
    + apply term_sub with (fv t).
      * intros x Hfv.
        unfold open; simpl.
        rewrite open_rec_term; assumption.
      * assumption.
    + assumption.    
  - unfold body in *.
    destruct H.
    destruct H0.
    split.
    + apply term_sub with (x \u x0).
      * intros x' Hfv.
        apply notin_union in Hfv.
        destruct Hfv as [Hx Hx0].
        unfold open; simpl.
        apply term_app.
        ** apply H in Hx; assumption.
        ** apply H0 in Hx0; assumption.
      * assumption.
    + apply term_app.
      * apply term_sub with x; assumption.
      * apply term_sub with x0; assumption.
  - split.
    + apply term_sub with (fv (pterm_abs t)).
      * intros x Hnot.
        apply body_to_term.
        **  assumption.
        **  apply body_lc_at.
            apply H.
      * assumption.
    + apply term_abs with (fv (& t[u])).
      intros x Hnot.
      apply body_to_term.
      * assumption.
      * apply body_lc_at.
        split.
        **  clear x u H0 Hnot.
            apply lc_at_bswap_rec.
            *** auto.
            *** assumption.
        **  apply lc_at_weaken_ind with 0.
            *** apply term_to_lc_at; assumption.
            *** auto with arith.
Qed.

Definition x_ctx t u := ES_contextual_closure sys_x t u. 
Notation "t ->_x u" := (x_ctx t u) (at level 59, left associativity).
Notation "t ->_x* u" := ((refltrans x_ctx) t u) (at level 59, left associativity).

Corollary term_regular_x_ctx : term_regular x_ctx.
Proof.
  apply term_regular_ctx.
  apply term_regular_sys_x.
Qed.

Lemma red_rename_x_ctx: red_rename x_ctx.
Proof.
  unfold red_rename.
  intros x t t' y Ht Ht' HX.
Admitted.

Inductive lx: Rel pterm :=
| b_ctx_rule : forall t u, t ->_B u -> lx t u
| x_ctx_rule : forall t u, t ->_x u -> lx t u.
Notation "t ->_Bx u" := (lx t u) (at level 59, left associativity).
Notation "t ->_lx* u" := ((refltrans lx) t u) (at level 59, left associativity).

Lemma red_rename_lx: red_rename lx.
Proof.
  unfold red_rename.
  intros x t t' y Ht Ht' Hlx.
  inversion Hlx; subst.
  - apply b_ctx_rule.
    generalize x t t' y Ht Ht' H.
    apply red_rename_b_ctx.
  - apply x_ctx_rule.
    generalize x t t' y Ht Ht' H.
    apply red_rename_x_ctx.
Qed.

Lemma Bx_app_left: forall t1 t2 t3, term t3 -> t1 ->_Bx t2 -> pterm_app t1 t3 ->_Bx pterm_app t2 t3.
Proof.
  intros t1 t2 t3 Hterm HBx.
  inversion HBx; subst.
  - apply b_ctx_rule.
    apply ES_app_left; assumption.
  - apply x_ctx_rule.
    apply ES_app_left; assumption.
Qed.

Lemma Bx_app_right: forall t1 t2 t3, term t1 -> t2 ->_Bx t3 -> pterm_app t1 t2 ->_Bx pterm_app t1 t3.
Proof.
  intros t1 t2 t3 Hterm HBx.
  inversion HBx; subst.
  - apply b_ctx_rule.
    apply ES_app_right; assumption.
  - apply x_ctx_rule.
    apply ES_app_right; assumption.
Qed.

Lemma Bx_abs: forall t1 t2 L, (forall x, x \notin L -> t1^x ->_Bx t2^x) -> pterm_abs t1 ->_Bx pterm_abs t2.
Proof.
  intros t1 t2 L HBx.
  pick_fresh x.
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt2].
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt1].
  apply HBx in Fr.
  inversion Fr; subst.
  - clear Fr.
    apply b_ctx_rule.
    apply ES_abs_in with (fv t1 \u fv t2).
    intros x' HL.
    generalize H.
Admitted.
(*    apply red_rename_b_ctx; assumption.
  - apply x_ctx_rule.
    apply ES_abs_in with (fv t1 \u fv t2).
    intros.
    generalize H.
    apply red_rename_x_ctx; assumption.
Qed. *)

Lemma Bx_sub: forall t1 t2 t3 L, (forall x, x \notin L -> t1^x ->_Bx t2^x) -> term t3 -> pterm_sub t1 t3 ->_Bx pterm_sub t2 t3.
Proof.
  intros t1 t2 t3 L HBx Hterm.
  pick_fresh x.
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt3].
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt2].
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt1].
  apply HBx in Fr.
  clear Fvt3.
  inversion Fr; subst.
  - apply b_ctx_rule.
    apply ES_sub with L.
    + intros x' Hnot.
      generalize H.
Admitted.
(*
      apply red_rename_b_ctx; assumption.
    + assumption.
  - apply x_ctx_rule.
    apply ES_sub with L.
    + intros x' Hnot.
      generalize H.
      apply red_rename_x_ctx; assumption.
    + assumption.
Qed. *)

Lemma Bx_sub_in: forall t1 t2 t3, body t1 -> t2 ->_Bx t3 -> pterm_sub t1 t2 ->_Bx pterm_sub t1 t3.
Proof.
  intros t1 t2 t3 Hbody HBx.
  inversion HBx; subst.
  - apply b_ctx_rule.
    apply ES_sub_in; assumption.
  - apply x_ctx_rule.
    apply ES_sub_in; assumption.
Qed.

Lemma x_star_app_left: forall t1 t2 t3, term t3 -> t1 ->_x* t2 -> pterm_app t1 t3 ->_x* pterm_app t2 t3.
Proof.
Admitted.

Lemma lx_star_app_left: forall t1 t2 t3, term t3 -> t1 ->_lx* t2 -> pterm_app t1 t3 ->_lx* pterm_app t2 t3.
Proof.
  intros t1 t2 t3 Hterm Hlx.
  induction Hlx.
  - apply refl.
  - apply rtrans with (pterm_app b t3).
    + apply Bx_app_left; assumption.
    + assumption.
Qed.

Lemma x_star_app_right: forall t1 t2 t3, term t1 -> t2 ->_x* t3 -> pterm_app t1 t2 ->_x* pterm_app t1 t3.
Proof.
  Admitted.
  
Lemma lx_star_app_right: forall t1 t2 t3, term t1 -> t2 ->_lx* t3 -> pterm_app t1 t2 ->_lx* pterm_app t1 t3.
Proof.
  intros t1 t2 t3 Hterm Hlx.
  induction Hlx.
  - apply refl.
  - apply rtrans with (pterm_app t1 b).
    + apply Bx_app_right; assumption.
    + assumption.
Qed.

Lemma x_star_app_comp: forall t1 t1' t2 t2', t1 ->_x* t1' -> t2 ->_x* t2' -> pterm_app t1 t2 ->_x* pterm_app t1' t2'.
Proof.
Admitted.

Lemma lx_star_app_comp: forall t1 t1' t2 t2', t1 ->_lx* t1' -> t2 ->_lx* t2' -> pterm_app t1 t2 ->_lx* pterm_app t1' t2'.
Proof.
Admitted.

Lemma x_star_abs: forall t1 t2 L, (forall x, x \notin L -> t1^x ->_x* t2^x) -> pterm_abs t1 ->_x* pterm_abs t2.
Proof.
Admitted.
  
Lemma lx_star_abs: forall t1 t2 L, (forall x, x \notin L -> t1^x ->_lx* t2^x) -> pterm_abs t1 ->_lx* pterm_abs t2.
Proof.
  intros t1 t2 L Hlx.
  pick_fresh x.
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt2].
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt1].
  apply Hlx in Fr.
  clear Hlx Fvt1 Fvt2.
Admitted.

Lemma x_star_sub: forall t1 t2 t3 L, (forall x, x \notin L -> t1^x ->_x* t2^x) -> term t3 -> pterm_sub t1 t3 ->_x* pterm_sub t2 t3.
Proof.
Admitted.
  
Lemma lx_star_sub: forall t1 t2 t3 L, (forall x, x \notin L -> t1^x ->_lx* t2^x) -> term t3 -> pterm_sub t1 t3 ->_lx* pterm_sub t2 t3.
Proof.
  intros t1 t2 t3 L Hlx Hterm.
  pick_fresh x.
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt3].
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt2].
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt1].
  apply Hlx in Fr.
  clear Fvt1 Fvt2 Fvt3.
Admitted.

Lemma x_star_sub_in: forall t1 t2 t3, body t1 -> t2 ->_x* t3 -> pterm_sub t1 t2 ->_x* pterm_sub t1 t3.
Proof.
Admitted.

Lemma x_star_sub_comp: forall t1 t1' t2 t2' L, (forall x, x \notin L -> t1^x ->_x* t1'^x) -> t2 ->_x* t2' -> pterm_sub t1 t2 ->_x* pterm_sub t1' t2'.
Proof.
Admitted.

Lemma lx_star_sub_in: forall t1 t2 t3, body t1 -> t2 ->_lx* t3 -> pterm_sub t1 t2 ->_lx* pterm_sub t1 t3.
Proof.
  intros t1 t2 t3 Hbody Hlx.
  induction Hlx.
  - apply refl.
  - apply rtrans with (t1 [b]).
    + apply Bx_sub_in; assumption.
    + assumption.
Qed.


Corollary term_regular_lx: term_regular lx.
Proof.
  unfold term_regular.
  intros t t' HBx.
  induction HBx.
  - apply term_regular_b_ctx; assumption.
  - apply term_regular_x_ctx; assumption.
Qed.

Lemma full_comp: forall t u, t[u] ->_x* (t ^^ u).
Proof.
  Admitted.

(*  
Lemma rel_arg_equiv: (forall x y, lx x y = (x_ctx !_! b_ctx) x y) -> lx = x_ctx !_! b_ctx.
Proof.
  Admitted.
*)
