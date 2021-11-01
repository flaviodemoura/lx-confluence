Require Import ZProperty Confluence InfraES LambdaES.
Require Import Lia.

Fixpoint B t :=
  match t with
  | pterm_app t1 t2 => match t1 with
                       | pterm_abs t1' => (B t1') ^^ (B t2)
                       | _ => pterm_app (B t1) (B t2)
                       end
  | pterm_abs t1 => pterm_abs (B t1)
  | pterm_sub t1 t2 => (B t1) [B t2]
  | _ => t
  end.

Fixpoint P t :=
  match t with
  | pterm_app t1 t2 => pterm_app (P t1) (P t2)
  | pterm_abs t1 => pterm_abs (P t1)
  | pterm_sub t1 t2 => (P t1) ^^ (P t2)
  | _ => t
  end.

Lemma llc_at_P: forall t n, llc_at n t -> llc_at n (P t). 
Proof.
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

Lemma lc_at_open_rec_gt: forall t1 t2 i j , i > j -> lc_at i t1 -> lc_at i t2 -> lc_at i ({j ~> t2} t1).
Proof.
  induction t1.
  - intros t2 i j Hgt Hlc1 Hlc2.
    simpl in *.
    destruct (n =? j) eqn:H.
    + assumption.
    + simpl.
      assumption.
  - intros t2 i j Hgt Hlc1 Hlc2.
    simpl in *.
    auto.
  - intros t2 i j Hgt Hlc1 Hlc2.
    simpl in *.
    destruct Hlc1 as [H11 H12]; split.
    + apply IHt1_1; assumption.
    + apply IHt1_2; assumption.
  - intros t2 i j Hgt Hlc1 Hlc2.
    simpl in *.
    apply IHt1.
    + apply Gt.gt_n_S; assumption.
    + assumption.
    + apply lc_at_weaken_ind with i.
      ** assumption.
      ** auto.
  - intros t2 i j Hgt Hlc1 Hlc2.
    simpl in *.
    destruct Hlc1 as [H11 H12]; split.
    + apply IHt1_1.
      * apply Gt.gt_n_S; assumption.
      * assumption.
      * apply lc_at_weaken_ind with i.
        ** assumption.
        ** auto.
    + apply IHt1_2; assumption.
Qed.    

(*
Lemma lc_at_P: forall t n, lc_at n t -> lc_at n (P t): Esta afirmação é falsa. Tome t = 2[x] e n = 2. Neste caso, lc_at 2 (2[x]) é verdadeira enquanto que lc_at 2 (P (2[x])) é falsa.

Lemma test: forall u k, {k ~> u}(pterm_bvar k) = u.
Proof.
  intros u k.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  reflexivity.
Qed.  

Lemma test': forall k x, {k ~> pterm_fvar x}(close_rec k x (pterm_app (pterm_fvar x) (pterm_bvar k))) = pterm_app (pterm_fvar x) (pterm_fvar x).
Proof.
  intros k x.
  simpl.
  repeat rewrite PeanoNat.Nat.eqb_refl.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  reflexivity.
Qed.  
 *)

(*
Lemma lterm_open_rec: forall t1 t2, (forall x, exists L, x \notin L -> lterm (t1^x)) -> lterm t2 -> lterm (t1 ^^ t2).
Proof.
  induction t1 using pterm_size_induction.
  generalize dependent H.
  case t1.
  - intros n IH t2 H Hlterm.
    admit. (* ok *)
  - intros x IH t2 H Hlterm.
    admit. (* ok *)
  - intros t1' t2' IH t2 H Hlterm.
    unfold open in *.
    simpl.
    apply lterm_app.
    + apply IH.
      * admit. (* ok *)
      * intro x.
        specialize (H x).
        inversion H.
        exists x0.
        intro Hx0.
        apply H0 in Hx0.
        simpl in Hx0.
        inversion Hx0; subst.
        assumption.
      * assumption.
    + admit. (* ok *)
  - intros t1' IH t2 H Hlterm.
    unfold open.
    simpl.
    
Lemma lterm_open_rec: forall t1 t2, (forall x, x \notin (fv t1) -> lterm (t1^x)) -> lterm t2 -> lterm (t1 ^^ t2).
Proof.
  induction t1.
  - intros t IH Hlterm.
    generalize dependent IH.
    case n.
    + unfold open.
      intro IH.
      simpl.
      assumption.
    + intros n' IH.
      unfold open in IH.
      pick_fresh x.
      specialize (IH x).
      simpl in IH.
      assert (H: x \notin {}).
      {
        admit. (* ok *)
      }
      apply IH in H.
      inversion H.
  - intros t IH H.
    unfold open.
    simpl.
    apply lterm_var.
  - intros t2 IH H.
    unfold open in *.
    simpl in *.
    apply lterm_app.
    + apply IHt1_1.
      * intros x Hfv.
      *
    +
  -
  -
    
Admitted.

Lemma subst_lemma_test1: forall m n x, {n ~> pterm_fvar x} ({m ~> pterm_bvar n} pterm_app (pterm_bvar n) (pterm_bvar m)) = pterm_app (pterm_fvar x) (pterm_fvar x).
Proof.
  intros m n x.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  destruct (n =? m).
  - simpl.
    rewrite PeanoNat.Nat.eqb_refl.
    reflexivity.
  - simpl.
    rewrite PeanoNat.Nat.eqb_refl.
    reflexivity.
Qed.

Lemma subst_lemma_test2: forall m n x, {m ~> {n ~> pterm_fvar x} pterm_bvar n} ({n ~> pterm_fvar x} pterm_app (pterm_bvar n) (pterm_bvar m)) = pterm_app (pterm_fvar x) (pterm_fvar x).
Proof.
  intros m n x.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl.
  destruct (m =? n).
  - simpl.
    reflexivity.
  - simpl.
    rewrite PeanoNat.Nat.eqb_refl.
    reflexivity.
Qed.

Lemma subst_lemma: forall t1 t2 n m x, n <> m -> term t2 -> {n ~> pterm_fvar x} ({m ~> t2} t1) = {m ~> {n ~> pterm_fvar x} t2} ({S n ~> pterm_fvar x} t1).
Proof.
  induction t1.
  - intros t2 n' m x Hneq.
    simpl ({m ~> t2} pterm_bvar n).
    destruct (n =? m) eqn: H.
    + case (S n' =? n) eqn: H'.
      *  Admitted.

Lemma subst_lemma': forall t1 t2 n m x, n <> m -> {n ~> pterm_fvar x} ({m ~> t2} t1) = {m ~> {n ~> pterm_fvar x} t2} ({n ~> pterm_fvar x} t1).
Proof.
  induction t1.
  - intros t2 n' m x Hneq.
    simpl.
    destruct (n =? m) eqn:H.
    + assert (n =? n' = false).
      { admit. }
      rewrite H0.
      simpl.
      rewrite H.
      reflexivity.
    + destruct (n =? n') eqn:H'.
      * simpl.
        rewrite H'.
        reflexivity.
      * simpl.
        rewrite H'.
        rewrite H.
        reflexivity.
  - intros t2 n m x Hneq.
    simpl.
    reflexivity.
  - intros t2 n m x Hneq.
    simpl.
    rewrite <- IHt1_1.
    + rewrite <- IHt1_2.
      * reflexivity.
      * assumption.
    + assumption.
  - intros t2 n m x Hneq.
    simpl.
Admitted.

Lemma subst_lemma: forall t1 t2 n x, {n ~> pterm_fvar x} ({0 ~> t2} t1) = {0 ~> {n ~> pterm_fvar x} t2} ({S n ~> pterm_fvar x} t1).
Proof.
  induction t1.
  - intros t2 n' x.
    case n.
    + simpl.
      reflexivity.
    + intros n''.
      change ({0 ~> t2} pterm_bvar (S n'')) with (pterm_bvar (S n'')).
      replace  ({0 ~> {n' ~> pterm_fvar x} P t2} ({S n' ~> pterm_fvar x} pterm_bvar (S n''))) with  ({S n' ~> pterm_fvar x} pterm_bvar (S n'')).

(* Este ponto da prova mostra que este lema é falso, e portanto precisamos voltar nas definições para encontrar o erro. *)
        
Lemma subst_lemma: forall t1 t2 n m x, m <> n -> {m ~> {n ~> pterm_fvar x} t2} ({n ~> pterm_fvar x} t1) = {n ~> pterm_fvar x} ({m ~> t2} t1).
Proof.
  induction t1.
  - intros t2 n' m x Hneq.
    simpl.
    destruct (n =? n') eqn: H.
    + destruct (n =? m) eqn: H'.
      * admit. (* ok. contradiction *)
      * admit. (* ok. reflexivity *)
    + destruct (n =? m) eqn: H'.
      * admit. (* ok. reflexivity *)
      * admit. (* ok. reflexivity *)
  - intros t2 n m x Hneq.
    reflexivity.
  - intros t2 n m x Hneq.
    simpl.
    rewrite IHt1_1.
    + rewrite IHt1_2.
      * reflexivity.
      * assumption.
    + assumption.
  - intros t2 n m x Hneq.
    simpl.
Admitted.
    
Lemma subst_lemma: forall t1 t2 t3 i j, i <> j -> term t3 -> {j ~> t3} ({i ~> t2} t1) =  {i ~> {j ~> t3} t2} ({S j ~> t3} t1).
Proof.
  induction t1.
  - intros t2 t3 i j Hle Hterm.
    case (n =? 0) eqn: H.
    + apply EqNat.beq_nat_true in H; subst.
      simpl.
      case (0 =? i) eqn: H.
      * case (0 =? j) eqn:Heq.
        ** admit.
  (*       ** apply EqNat.beq_nat_true in H; subst. *)
  (*         reflexivity. *)
  (*     * case (0 =? j) eqn:Heq. *)
  (*       ** admit. *)
  (*       ** admit. *)
  (*   + apply EqNat.beq_nat_false in H. *)
  (*     simpl. *)
  (*     case (n =? i) eqn:Hleq. *)
  (*     * apply EqNat.beq_nat_true in Hleq; subst. *)
  (*       destruct (n =? j) eqn:Hleq. *)
  (*       ** apply EqNat.beq_nat_true in Hleq; subst. *)
  (*          contradiction. *)
  (*       ** simpl. *)
  (*          rewrite PeanoNat.Nat.eqb_refl. *)
  (*          reflexivity. *)
  (*     * apply EqNat.beq_nat_false in Hleq; subst. *)
  (*       destruct (n =? j) eqn:Heq. *)
  (*       ** apply EqNat.beq_nat_true in Heq; subst. *)
  (*          simpl. *)
  (*          rewrite PeanoNat.Nat.eqb_refl. *)
  (*          admit. *)
  (*       ** apply EqNat.beq_nat_false in Heq; subst. *)
  (*          admit. *)
  (* - intros t2 t3 i j Hneq Hterm. *)
  (*   reflexivity. *)
  (* - admit. *)
  (* - intros t2 t3 i j Hneq Hterm. *)
  (*   simpl. *)
  (*   rewrite IHt1. *)

Lemma subst_lemma: forall t1 t2 t3 i j, i <= j -> term t3 -> {j ~> t3} ({i ~> t2} t1) =  {i ~> {j ~> t3} t2} ({S j ~> t3} t1).
Proof.
  induction t1.
  - intros t2 t3 i j Hle Hterm.
    case (n =? 0) eqn: H.
    + apply EqNat.beq_nat_true in H; subst.
      simpl.
      case (0 =? i) eqn: H.
      * reflexivity.
      * apply EqNat.beq_nat_false in H.
        simpl.
        case (0 =? j) eqn:Heq.
        ** apply EqNat.beq_nat_true in Heq; subst.
           lia.
        ** reflexivity.
    + apply EqNat.beq_nat_false in H.
      case (S j =? n) eqn:Hleq.
      * apply EqNat.beq_nat_true in Hleq; subst.
        simpl.
        rewrite PeanoNat.Nat.eqb_refl.
        destruct (S j =? i) eqn:Hleq.
        ** apply EqNat.beq_nat_true in Hleq; subst.
           pose proof PeanoNat.Nat.nle_succ_diag_l.
           specialize (H0 j).
           contradiction.
        ** Admitted.

Corollary open_rec_nested: forall t1 t2 i j x, i <= j -> {j ~> pterm_fvar x} ({i ~> t2} t1) =  {i ~> {j ~> pterm_fvar x} t2} ({S j ~> pterm_fvar x} t1).
Proof.
  intros t1 t2 i j x H.
  apply subst_lemma.
  - assumption.
  - apply term_var.
Qed.


Corollary open_nested: forall t1 t2 n x,  {n ~> pterm_fvar x} ({0 ~> t2} t1) =  {0 ~> {n ~> pterm_fvar x} t2} ({S n ~> pterm_fvar x} t1).
Proof.
  intros t1 t2 n x.
  apply open_rec_nested.
  lia.
Qed.

Lemma open_rec_P: forall t1 t2 n, P ({n ~> t2} t1) = {n ~> P t2} (P t1).
Proof.
  induction t1.
  (*
 - intros t2 n' Hterm.
   simpl.
   case (n =? n') ; reflexivity.
 - intros t2 n Hterm.
    reflexivity.
 - intros t2 n Hterm.
   inversion Hterm; subst.
    simpl.
    rewrite IHt1_1.
   + rewrite IHt1_2.
     * reflexivity.
     * assumption.
   + assumption.    
 - intros t2 n Hterm.
   simpl.
   rewrite IHt1.
   + reflexivity.
   +
 - intros t2 n.
   simpl.
   unfold open.
   rewrite IHt1_1.
   rewrite IHt1_2.
   pose proof subst_lemma.
   symmetry. *)
Admitted.

Lemma open_rec_P_fvar: forall t x n, {n ~> pterm_fvar x} (P t) = P ({n ~> pterm_fvar x} t).
Proof.
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
Admitted.

Corollary open_P: forall t x, P t ^ x = P (t ^ x).
Proof.
  intros t x.
  unfold open.
  apply open_rec_P_fvar; assumption.
Qed.

Lemma lc_at_to_P: forall t n, lc_at n t -> lc_at n (P t). 
Proof.
Admitted.  

Lemma P_to_lc_at: forall t n, lc_at n (P t) -> lc_at n t.
Proof.                                                 
Admitted.

Corollary lc_at_P: forall t n, lc_at n t <-> lc_at n (P t). 
Proof.    
Admitted.

Lemma open_rec_P: forall t n x, term ({n ~> pterm_fvar x}t) -> P({n ~> pterm_fvar x} t) = {n ~> pterm_fvar x} (P t).
Proof.¯
  induction t.
  - intros n' x Hterm.
    simpl in *.
    destruct (n =? n') eqn:H.
    + reflexivity.
    + inversion Hterm.
  - intros n x Hterm.
    simpl in *.
    reflexivity.
  - intros n x Hterm.
    simpl in *.
    inversion Hterm; subst.
    rewrite IHt1.
    + rewrite IHt2.
      * reflexivity.
      * assumption.
    + assumption.
  - intros n x Hterm.
    simpl in *.
    rewrite IHt.
    + reflexivity.
    + 
      
Lemma open_rec_P: forall t n x, lc_at 0 ({n ~> pterm_fvar x}t) -> P({n ~> pterm_fvar x} t) = {n ~> pterm_fvar x} (P t).
Proof.
  induction t.
  - intros n' x Hlc.
    simpl in Hlc.
    destruct (n =? n') eqn:H.
    + apply EqNat.beq_nat_true in H.
      subst.
      simpl.
      rewrite PeanoNat.Nat.eqb_refl.
      reflexivity.
    + simpl.
      rewrite H.
      reflexivity.
  - intros n x Hlc.
    reflexivity.
  - intros n x Hlc.
    simpl in *.
    destruct Hlc as [H1 H2].
    rewrite IHt1.
    + rewrite IHt2.
      * reflexivity.
      * assumption.
    + assumption.
  - intros n x Hlc.
    simpl in *.
    rewrite IHt.
    + reflexivity.
    + 
    
  induction t using pterm_size_induction.
  case t eqn: Ht.
  - intros n' x.
    simpl.
    destruct (n =? n').
    + reflexivity.
    + simpl.
      reflexivity.
  - intros n x.
    simpl.
    reflexivity.
  - intros n x.
    simpl.
    rewrite H.
    + rewrite H.
      * reflexivity.
      * simpl.
        admit.
    + simpl.
      admit.
  - intros n x.
    simpl.
    rewrite H.
    + reflexivity.
    + admit.
  - intros n x.
    simpl.
    rewrite H.
    + rewrite H.
      * unfold open.
        pick_fresh y.
        pose proof m_sb_intro_open.
        specialize (H0 y).
        replace (P p1 ^^ P p2) with ([y ~> (P p2)] (P p1) ^ y).
        ** simpl.
Admitted. 

Lemma open_P: forall t x, P(t^x) = (P t)^x.
Proof.
  intros t x.
  induction t.
  - admit.
  - admit.
  - admit.
  - Admitted.
      
Lemma term_open_rec: forall t u n, term ({n ~> u} t) -> term u.
Proof.
  Admitted.

Lemma term_P: forall t, term (P t) -> term t.
Proof.
  induction t using pterm_induction.
  - intro H.
    simpl in H.
    inversion H.
  - intro H.
    apply term_var.
  - intro H'.
    inversion H'; subst. clear H'.
    pick_fresh x.
    apply term_abs with (L \u fv t).
    intros x' Hfv.
    apply notin_union in Hfv.
    destruct Hfv as [HL Ht].
    apply H.
    + assumption.
    + reflexivity.
    + rewrite open_P.
      apply H1.
      assumption.
  - intro H.
    simpl in *.
    inversion H; subst.
    apply term_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intro Hterm.
    simpl in *.
    unfold open in *.
    pick_fresh x.
    apply term_sub with (fv t1).
    + intros x' Hfv.
      apply H.
      * assumption.
      * reflexivity.
      * rewrite open_rec_P.
        admit. (* easy *)
    + apply IHt1.
      apply term_open_rec in Hterm; assumption.
Admitted.

Lemma lterm_open_rec: forall t1 t2, (forall x, exists L, x \notin L -> lterm (t1^x)) -> lterm t2 -> lterm (t1 ^^ t2).
Proof.
Admitted.

Lemma llc_at_P: forall t k, llc_at k t = llc_at k (P t). 
Proof.
Admitted.

Lemma lterm_P_open_rec_fvar: forall t n x, lterm (P ({n ~> pterm_fvar x}t)) -> lterm({n ~> pterm_fvar x}(P t)).
Proof.
  induction t using pterm_size_induction.
  generalize dependent H.
  case t.
  - intros n IH n' x Hlterm.
    simpl in *.
    destruct (n =? n').
    + apply lterm_var.
    + simpl in Hlterm.
      inversion Hlterm.
  - intros v IH n x Hlterm.
    simpl.
    apply lterm_var.
  - intros t1 t2 IH n x Hlterm.
    simpl in *.
    inversion Hlterm; subst; clear Hlterm.
    apply lterm_app.
    + apply IH.
      * admit. (* ok *)
      * assumption.
    + apply IH.
      * admit. (* ok *)
      * assumption.
  - intros t' IH n x Hlterm.
    simpl in *.
    apply lterm_to_llc_at in Hlterm.
    simpl in Hlterm.
    apply lterm_abs with (fv t').
    intros x' Hnotin.
    unfold open in *.
    apply llc_at_to_lterm.
    apply llc_at_open_rec.
    + apply lterm_var.
    + rewrite <- llc_at_P_open_rec.
      assumption.
  - intros t1 t2 IH n x H.
    simpl in *.
    unfold open in *.
    
Admitted.

Corollary lterm_P_open: forall t x, lterm (P (t^x)) -> lterm((P t)^x).
Proof.
  intros t x H.
  unfold open in *.
  apply lterm_P_open_rec_fvar.
  assumption.
Qed.

Lemma term_P_lterm: forall t, term t ->  lterm (P t).
Proof.
  induction t using pterm_induction.
  - intro H.
    inversion H.
  - intro H.
    simpl.
    apply lterm_var.
  - intro H'.
    inversion H'; subst.
    simpl.
    apply lterm_abs with (fv t \u L).
    intros x' Hnot.
    apply notin_union in Hnot.
    destruct Hnot as [Hnot Fr].
    unfold open.
    apply lterm_open_rec.
    + intro x.
      exists (L \u fv t).
      intro Hnotin.
      apply notin_union in Hnotin.
      destruct Hnotin as [HL Hfv].
      apply lterm_P_open.
      apply H.
      * assumption.
      * reflexivity.
      * apply H1; assumption.
    + apply lterm_var.       
  - intro H.
    simpl in *.
    inversion H; subst.
    apply lterm_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intro Hterm.
    inversion Hterm; subst.
    simpl.
    unfold open in *.
    apply lterm_open_rec.
    + intro x.
      exists (L \u fv t1).
      intro Hnot.
      apply notin_union in Hnot.
      destruct Hnot as [Hnot Hfv].
      unfold open.
      apply lterm_open_rec.
      * intro x'.
        exists (L \u fv t1).
        intro Hnotin.
        apply notin_union in Hnotin.
        destruct Hnotin as [HL Hfv1].
        apply lterm_P_open.
        apply H.
        ** assumption.
        ** reflexivity.
        ** apply H2; assumption.
      * apply lterm_var.
    + apply IHt1; assumption.
Qed.

Lemma open_rec_P: forall t u n, P({n ~> u} t) = {n ~> P u} (P t).
Proof.
Admitted.

Corollary open_rec_P_fvar: forall t n x, P({S n ~> pterm_fvar x} t) = {S n ~> pterm_fvar x} (P t).
Proof.
Admitted.

Lemma open_rec_eq: forall t u v i, term v -> term ({i ~> v} u) -> {i ~> v} ({i ~> u} t) = {i ~> {i ~> v} u} t.
Proof.
  Admitted.

Lemma lterm_P_open: forall t u x, term u -> term (t ^ x) -> lterm (P (t ^^ u)) -> lterm (P t ^^ P u).
Proof.
  induction t using pterm_size_induction.
  intros u x Hterm1 Hterm2 Hlterm.
  generalize dependent x.
  generalize dependent u.
  generalize dependent t.
  intro t; case t.
  - intro n; case n.
    + intros IH u Hterm1 Hlterm x Hterm2.
      unfold open in *.
      simpl in *.
      assumption.
    + intros n' IH u Hterm1 Hlterm x Hterm2.
      unfold open in *.
      simpl in *.
      inversion Hlterm.
  - intros v IH u Hterm1 Hlterm x Hterm2.
    unfold open.
    simpl.
    apply lterm_var.
  - intros t1 t2 IH u Hterm1 Hlterm x Hterm2.
    unfold open in *.
    simpl in *.
    inversion Hterm2; subst; clear Hterm2.
    inversion Hlterm; subst; clear Hlterm.
    apply lterm_app.
    + apply IH with x.
      * admit. (* ok *)
      * assumption.
      * assumption.
      * assumption.
    + apply IH with x.
      * admit. (* ok *)
      * assumption.
      * assumption.
      * assumption.
  - intros t' IH u Hterm1 Hlterm x Hterm2.
    unfold open in *.
    simpl in *.
    inversion Hterm2; subst; clear Hterm2.
    inversion Hlterm; subst; clear Hlterm.
    apply lterm_abs with (L \u L0).
    intros x' Hnotin.
    apply notin_union in Hnotin.
    destruct Hnotin as [Hnotin Hnotin'].
    unfold open in *.
    rewrite <- open_rec_P.
    specialize (H1 x').
    apply H1; assumption.
  - intros t1 t2 IH u Hterm1 Hlterm x Hterm2.
    unfold open in *.
    simpl in *.
    inversion Hterm2; subst; clear Hterm2.
    apply lterm_open.
    unfold open in *.
    Admitted.
 

(** open_rec não permite a composição da substituição. *)

Lemma open_rec_composition: forall t x y, {0 ~> pterm_fvar x} ({1 ~> pterm_fvar y} t) = {0 ~> ({0 ~> pterm_fvar x} (pterm_fvar y))} ({1 ~> pterm_fvar x} t).
Proof.
  induction t.
  - intros x y.
    case n.
    + simpl.
    + intros n'.
      case n'.
      * simpl.
      *
Admitted.

Lemma open_swap_term'': forall t1 t2 x n, {S n ~> pterm_fvar x} ({0 ~> t2} t1) = {0 ~> ({S n ~> pterm_fvar x} t2)} ({S(S n) ~> pterm_fvar x} t1).
Proof.
Admitted.

Lemma open_rec_P: forall t x, lc_at 1 t -> P ({0 ~> pterm_fvar x} t) = {0 ~> pterm_fvar x} (P t).
Proof.
  intro t.
  generalize dependent 0.
  induction t.
  - intros n' x H.
    simpl in *.
    destruct (n =? n'); reflexivity.
  - intros n x H.
    reflexivity.
  - intros n x H.
    simpl in *.
    destruct H as [H1 H2].
    rewrite IHt1.
    + rewrite IHt2.
      * reflexivity.
      * assumption.
    + assumption.
  - intros n x H.
    simpl in *.
    rewrite IHt.
    + reflexivity.
    + assumption.
  - intros n x H.
    simpl in H.
    destruct H as [H1 H2].
    generalize dependent n.
    intro n; case n.
    + intros H1 H2.
      simpl in *.
      unfold open in *.
      rewrite IHt1.
      * rewrite IHt2.
        ** admit.
        ** assumption.
      * assumption.
Admitted.

Lemma open_rec_P: forall t x n, P ({S n ~> pterm_fvar x} t) = {S n ~> pterm_fvar x} (P t).
Proof.                                                                                    
  induction t.
  - case n.
    + intros x n'.
      simpl.
      reflexivity.
    + intros n' x n''.
      simpl.
      destruct (n' =? n'').
      * reflexivity.
      * reflexivity.
  - intros x n.
    reflexivity.    
  - intros x n.
    simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  - intros x n.
    simpl.
    rewrite IHt.
    reflexivity.
  - intros x n.
    simpl.
    unfold open.
    rewrite IHt1.
    rewrite IHt2.
Admitted.

Lemma lc_at_llc_at: forall t n, lc_at n t -> llc_at n (P t).
Proof.
  intro t; induction t.
  - intros n' Hlc.
    simpl in *.
    assumption.
  - intros n Hlc.
    simpl in *.
    auto.
  - intros n Hlc.
    simpl in *.
    destruct Hlc as [Hlc1 Hlc2].
    split.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros n Hlc.
    simpl in *.
    apply IHt; assumption.
  - intros n Hlc.
    simpl in *.
    destruct Hlc as [Hlc1 Hlc2].
    unfold open.
    generalize dependent n.
    intro n; case n.
    + intros H1 H2.
      apply llc_at_open_rec.
      * apply IHt2 in H2.
        apply llc_at_to_lterm in H2; assumption.
      * apply IHt1; assumption.
    + intros n' H1 H2.
      apply llc_at_open_gen.
      * apply IHt2; assumption.
      * apply IHt1.
Admitted.
  
Lemma term_prop: forall x y n, term ({0 ~> pterm_fvar x} ({2 ~> pterm_fvar y} (pterm_app (pterm_bvar 1) (pterm_bvar (S n))))).
Proof.
  intros x y n.
  simpl.
Admitted.

Lemma open_rec_composition: forall t x y n, {0 ~> pterm_fvar x} ({S n ~> pterm_fvar y} t) = {S n ~> pterm_fvar y} ({1 ~> pterm_fvar x} (&t)).
Proof.
  induction t.
  - intros x y n'.
    case n.
    + reflexivity.
    + intros n''.
      simpl.
      destruct (n'' =? n') eqn: H.
      * apply EqNat.beq_nat_true in H; subst.
        simpl.
        case n''.
        ** simpl.
        **
      * *)
  (* induction t using pterm_size_induction. *)
  (* generalize dependent H. *)
  (* case t. *)
  (* - intro n; case n. *)
  (*   + intros IH x Hlc Hlterm. *)
  (*     unfold open in *. *)
  (*     simpl in *. *)
  (*     apply lterm_var. *)
  (*   + intros n' IH x Hlc Hlterm. *)
  (*     unfold open in *. *)
  (*     simpl in *. *)
  (*     inversion Hlterm. *)
  (* - intros v IH x Hlc Hlterm. *)
  (*   unfold open. *)
  (*   simpl. *)
  (*   apply lterm_var. *)
  (* - intros t1 t2 IH x Hlc Hlterm. *)
  (*   unfold open in *. *)
  (*   simpl in *. *)
  (*   destruct Hlc as [H1 H2]. *)
  (*   inversion Hlterm; subst; clear Hlterm. *)
  (*   apply lterm_app. *)
  (*   + apply IH. *)
  (*     * admit. (* ok *) *)
  (*     * assumption. *)
  (*     * assumption. *)
  (*   + apply IH. *)
  (*     * admit. (* ok *) *)
  (*     * assumption. *)
  (*     * assumption. *)
  (* - intros t1 IH x Hlc Hlterm. *)
  (*   unfold open in *. *)
  (*   simpl in *. *)
  (*   inversion Hlterm; subst; clear Hlterm. *)
  (*   apply lterm_abs with L. *)
  (*   intros x' Hnotin. *)
  (*   unfold open in *. *)
  (*   apply llc_at_P in Hlc. *)
  (*   rewrite <- open_rec_P. *)
  (*   apply H0; assumption.   *)
  (* - Admitted. *)

Lemma llc_at_open_rec_P: forall t x i j, llc_at i ({j ~> pterm_fvar x}(P t)) = llc_at i (P ({j ~> pterm_fvar x} t)). 
Proof.
  induction t using pterm_size_induction.
  generalize dependent H.
  case t.
  - intros n IH x i j.
    simpl.
    destruct (n =? j); reflexivity.
  - intros v IH x i j.
    reflexivity.
  - intros t1 t2 IH x i j.
    simpl.
    rewrite IH.
    + rewrite IH.
      * reflexivity.
      * admit. (* ok *)
    + admit. (* ok *)
  - intros t1 IH x i j.
    simpl.
    rewrite IH.
    + reflexivity.
    + admit. (* ok *)
  - intros t1 t2 IH x i j.
    simpl.
    unfold open.
Admitted.

Lemma lterm_open_fvar_P: forall t x, lterm (P t ^ x) -> lterm (P (t ^ x)).
Proof.
  intros t x H.
  unfold open in *.
  generalize dependent 0.
  generalize dependent x.
  induction t using pterm_size_induction.
  generalize dependent H.
  case t.
  - intros n IH x n' Hlterm.
    simpl in *.
    destruct (n =? n') eqn:Heq.
    + simpl.
      apply lterm_var.
    + inversion Hlterm.
      apply lterm_bvar.
  - intros v IH x n Hlterm.
    simpl.
    apply lterm_var.
  - intros t1 t2 IH x n Hlterm.
    simpl in *.
    inversion Hlterm; subst; clear Hlterm.
    apply lterm_app.
    + apply IH.
      * admit. (* ok *)
      * assumption.
    + apply IH.
      * admit. (* ok *)
      * assumption.
  - intros t1 IH x n Hlterm.
    simpl in *.
    inversion Hlterm; subst; clear Hlterm.
    apply lterm_abs with L.
    intros x' Hnotin.
    unfold open in *.
    apply H0 in Hnotin; clear H0.
    apply lterm_to_llc_at in Hnotin.
    apply llc_at_open_var_rec in Hnotin.
    apply llc_at_to_lterm.
    apply llc_at_open_rec.
    + apply lterm_var.
    + rewrite llc_at_open_rec_P in Hnotin.
      assumption.
  - intros t1 t2 IH x n Hlterm.
    simpl in *.
    unfold open in *.
    apply lterm_to_llc_at in Hlterm.
    apply llc_at_to_lterm.
    apply llc_at_open_rec.
    + apply IH.
      * admit. (* ok *)
      * apply llc_at_to_lterm.
        admit. (* acho ok, mas verificar. *)
    + Admitted. (* problema da composição. *)
    
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
    inversion H; subst; clear H.    
    apply lterm_abs with L.
    intros x' Hnotin.
    unfold open in *.
Admitted. (* composition of the meta-substitution is necessary. *)

Lemma lterm_P_open_rec_fvar: forall t x, lterm (P (t ^ x)) -> lterm (P t ^ x).
Proof.
  induction t using pterm_size_induction.
  generalize dependent H.
  unfold open.
  generalize dependent 0.
  case t.
  - intros n n' IH x Hlterm.
    simpl in *.
    destruct (n =? n') eqn:H.
    + apply lterm_var.
    + simpl in Hlterm.
      inversion Hlterm.
      apply lterm_bvar.
  - intros n n' IH x Hlterm.
    simpl in *.
    destruct (n =? n') eqn:H.
    + apply lterm_var.
    + simpl in Hlterm.
      inversion Hlterm.
      apply lterm_var.
  - intros t1 t2 n IH x Hlterm.
    simpl in *.
    inversion Hlterm; subst; clear Hlterm.
    apply lterm_app.
    + apply IH.
      * lia.
      * assumption.
    + apply IH.
      * lia.
      * assumption.
  - intros t' n IH x Hlterm.
    simpl in *.
    inversion Hlterm; subst; clear Hlterm.
    pick_fresh y.
    apply notin_union in Fr.
    destruct Fr as [Fr Ht'].
    apply notin_union in Fr.
    destruct Fr as [Fr Ht].
    apply notin_union in Fr.
    destruct Fr as [Fr Hx].
    apply notin_union in Fr.
    destruct Fr as [Fr Hn].
    apply H0 in Fr; clear H0.
    apply lterm_abs with L.
    intros x' H.
    unfold open in *.
Admitted.

Lemma llc_at_open_rec: forall t x i j, i < j -> llc_at (S i) ({j ~> pterm_fvar x} t) -> llc_at (S j) t.
Proof.
  induction t.
  - intros x i j Hle Hllc_at.
    simpl in *.
    destruct (n =? j) eqn:Heq.
    + apply EqNat.beq_nat_true in Heq; subst.
      apply PeanoNat.Nat.lt_succ_diag_r.
    + simpl in Hllc_at.
      apply PeanoNat.Nat.lt_le_trans with (S i).
      * assumption.
      * admit. (* ok *)
  - intros x i j Hle Hllc_at.
    simpl; auto.
  - intros x i j Hle Hllc_at.
    simpl in *.
    destruct Hllc_at as [H1 H2]; split.
    + apply IHt1 with x i; assumption.
    + apply IHt2 with x i; assumption.
  - intros x i j Hle Hllc_at.
    simpl in *.
    apply IHt with x (S i).
    + admit. (* ok *)
    + assumption.
  - intros x i j Hle Hllc_at.
    simpl in Hllc_at.
    contradiction.
Admitted. (* ok *)
  
Lemma lterm_to_llc_at: forall t x n, lterm ({n ~> pterm_fvar x} t) -> llc_at (S n) t.
Proof.
  (* induction t using pterm_size_induction.
  generalize dependent H; case t.
  - intros n IH x n' Hlterm.
    simpl in *.
    destruct (n =? n') eqn:Heq.
    + apply EqNat.beq_nat_true in Heq; subst.
      apply PeanoNat.Nat.lt_succ_diag_r.
    + inversion Hlterm.
  - intros v IH x n Hlterm.
    simpl; auto.
  - intros t1 t2 IH x n Hlterm.
    simpl in *.
    inversion Hlterm; subst; clear Hlterm; split.
    + apply IH with x.
      * admit. (* ok *)
      * assumption.
    + apply IH with x.
      * admit. (* ok *)
      * assumption.
  - intros t' IH x n Hlterm.
    simpl in *.
    inversion Hlterm; subst; clear Hlterm.
    pick_fresh x'.
    apply notin_union in Fr.
    destruct Fr as [Fr Ht'].
    apply notin_union in Fr.
    destruct Fr as [Fr Ht].
    apply notin_union in Fr.
    destruct Fr as [Fr Hn].
    apply notin_union in Fr.
    destruct Fr as [Fr Hx].
    apply H0 in Fr; clear H0.
    unfold open in Fr.
    assert (H: pterm_size ({S n ~> pterm_fvar x} t') < S (pterm_size t')).
    + admit. (* ok *)
    + specialize (IH ({S n ~> pterm_fvar x} t')).
      apply IH with x 0 in H.
      * simpl in H.
        apply llc_at_open_rec in H.
        ** assumption.
        ** admit. (* ok *)
      * apply lterm_open_rec_rename with x'; assumption.     
  - intros t1 t2 IH x n Hlterm.
    simpl in Hlterm.
    inversion Hlterm. *)
Admitted. (* ok *)
    
Lemma lterm_to_llc_at_max: forall t x y i j, i < j -> lterm ({i ~> pterm_fvar x} ({j ~> pterm_fvar y} t)) -> llc_at (S j) t.
Proof.
  (* induction t.
  - intros x y i j Hleq Hlterm.
    simpl in Hlterm.
    destruct (n =? j) eqn:Heq.
    + apply EqNat.beq_nat_true in Heq; subst.
      simpl.
      apply PeanoNat.Nat.lt_succ_diag_r.
    + simpl in Hlterm.
      destruct (n =? i) eqn:Heq'.
      * apply EqNat.beq_nat_true in Heq'; subst.
        simpl.
        apply PeanoNat.Nat.le_lt_trans with j.
        ** apply PeanoNat.Nat.lt_le_incl; assumption.
        ** apply PeanoNat.Nat.lt_succ_diag_r.
      * inversion Hlterm.
  - intros x y i j Hle Hlterm.
    simpl.
    auto.
  - intros x y i j Hle Hlterm.
    simpl in *.
    inversion Hlterm; subst; clear Hlterm; split.
    + apply IHt1 with x y i; assumption.
    + apply IHt2 with x y i; assumption.
  - intros x y i j Hle Hlterm.
    inversion Hlterm; subst; clear Hlterm.
    unfold open in *.
    pick_fresh z.
    apply notin_union in Fr.
    destruct Fr as [Fr Ht].
    apply notin_union in Fr.
    destruct Fr as [Fr Hj].
    apply notin_union in Fr.
    destruct Fr as [Fr Hi].
    apply notin_union in Fr.
    destruct Fr as [Fr Hy].
    apply notin_union in Fr.
    destruct Fr as [Fr Hx].
    apply H0 in Fr; clear H0.
    simpl.
    apply lterm_to_llc_at in Fr.
    apply llc_at_open_rec in Fr.
    + apply llc_at_open_rec in Fr.
      * assumption.
      * admit. ok *)
Admitted. (* ok *)

(*
Lemma lterm_to_llc_at: forall t x n, lterm ({n ~> pterm_fvar x} t) -> llc_at (S n) t.
Proof.
  induction t.
  - intros x n' Hlterm.
    simpl in *.
    destruct (n =? n') eqn:Heq.
    + apply EqNat.beq_nat_true in Heq; subst.
      auto.
    + inversion Hlterm.
  - intros x n Hlterm.
    simpl in *.
    auto.
  - intros x n Hlterm.
    simpl in *.
    inversion Hlterm; subst; clear Hlterm; split.
    + apply IHt1 with x; assumption.
    + apply IHt2 with x; assumption.
  - intros x n Hlterm.
    simpl in *.
    inversion Hlterm; subst.
    pick_fresh x'.
    apply notin_union in Fr.
    destruct Fr as [Fr Ht].
    apply notin_union in Fr.
    destruct Fr as [Fr Hn].
    apply notin_union in Fr.
    destruct Fr as [Fr Hx].
    apply H0 in Fr.
    unfold open in Fr.
    apply lterm_to_llc_at_max in Fr.
    + assumption.
    + apply PeanoNat.Nat.le_trans with n.
      * apply le_0_n.
      * apply PeanoNat.Nat.le_succ_diag_r.
  - intros x n Hlterm.
    simpl in *.
    inversion Hlterm.
Qed.
*)   

Lemma term_P_lterm: forall t, lterm (P t).
Proof.
    intro t.
    induction t using pterm_size_induction.
    generalize dependent H.
    case t.
    - intros n t0.
      simpl.
      apply lterm_bvar.
    - intros v IH. 
      simpl.
      apply lterm_var.
  (* intro t.
  induction t using pterm_size_induction.
  generalize dependent H.
  case t0.
  - intros n IH. 
    simpl.
    apply lterm_bvar.
  - intros v IH. 
    simpl.
    apply lterm_var.
  - intros.
  simpl.
    apply lterm_app; assumption.
  - simpl.
    apply lterm_abs with (fv t0).
    intros x Hnotin.
    apply lterm_P_open_rec_fvar.
    apply H0; assumption. 
  - simpl.
    unfold open in *.
    apply lterm_open.
    + pick_fresh x.
      apply notin_union in Fr.
      destruct Fr as [Fr Ht2].
      apply notin_union in Fr.
      destruct Fr as [Fr Ht1].
      apply H0 in Fr.
      apply lterm_P_open_rec_fvar in Fr.
      unfold open in Fr.
      apply lterm_to_llc_at in Fr.
      assumption.
    + assumption. *)
(* Qed.     *)
Admitted.

(*
Lemma term_P_lterm: forall t, term t ->  lterm (P t).
Proof.
  induction t using pterm_induction.
  - intro H.
    inversion H.
  - intro H.
    simpl.
    apply lterm_var.
  - intro H'.
    inversion H'; subst.
    simpl.
    apply lterm_abs with (fv t \u L).
    intros x' Hnot.
    apply notin_union in Hnot.
    destruct Hnot as [Hnot Fr].
    unfold open.
    rewrite open_rec_P_fvar.
    apply H.
    + assumption.
    + reflexivity.
    + apply H1; assumption.
  - intro H.
    simpl in *.
    inversion H; subst.
    apply lterm_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intro Hterm.
    inversion Hterm; subst; clear Hterm.
    simpl.
    unfold open in *.
    apply lterm_open_rec.
    + intro x.
      exists (L \u fv t1).
      intro Hnot.
      apply notin_union in Hnot.
      destruct Hnot as [Hnot Hfv].
      unfold open.
      apply lterm_open_rec.
      * intro x'.
        exists (L \u fv t1).
        intro Hnotin.
        apply notin_union in Hnotin.
        destruct Hnotin as [HL Hfv1].
        unfold open.
        rewrite open_rec_P_fvar.
        apply H.
        ** assumption.
        ** reflexivity.
        ** apply H2; assumption.
      * apply lterm_var.
    + apply IHt1; assumption.
Qed.
 *)

Lemma lterm_P_id: forall t, lterm t -> P t = t.
Proof.
  induction 1.
  - simpl. reflexivity.
  - reflexivity.
  - simpl.
    rewrite IHlterm1.
    rewrite IHlterm2; reflexivity.
  - simpl.
    unfold open in *.
    pick_fresh x.
    apply notin_union in Fr.
    destruct Fr as [Fr H1].
    assert (Fr' := Fr).
    apply H in Fr; clear H.
    apply H0 in Fr'; clear H0.
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
Admitted.

Lemma substitution_equality_with_P: forall t1 t2 n x, P({n ~> pterm_fvar x} t1) = P({n ~> pterm_fvar x} t2) -> P(t1) = P(t2).
Proof. 
  intros.
  
Admitted.

(** Lemma 5.3 item 1 *)
Lemma sys_x_P_eq: forall t1 t2, t1 ->_x t2 -> P t1 = P t2.
Proof.
  intros t1 t2 H.
  induction H.
  - inversion H; subst.
    + simpl.
      reflexivity.
    + simpl. unfold open in *. simpl. apply term_P in H0. 
      rewrite open_rec_term. 
      * reflexivity.
      * assumption.
    + unfold open in *.
      simpl.
      reflexivity.
    + simpl.
      unfold open in *.
      simpl.
      admit. (** problema *)
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
     
Lemma term_to_P: forall t, t ->_x* P t. 
Proof.
  induction t.
  - simpl.
    apply refl.
  - simpl.
    apply refl.
  - admit.
  - admit.
  - Admitted.

Lemma term_to_B: forall t, lterm t -> t ->_lx* B t.
Proof.
Admitted.

Lemma lambda_x_Z_comp: forall t1 t2, t1 ->_B t2 -> t2 ->_lx* B(P t1) /\  B(P t1) ->_lx* B(P t2).
Proof.

Admitted.

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
      * apply term_to_P.
      * split.
        ** intros b a Heq.
          apply term_to_B.
          rewrite -> Heq.
          apply term_P_lterm.
        ** unfold f_is_weak_Z.
          apply lambda_x_Z_comp.
Qed.

Corollary lambda_x_is_confluent: Confl lx.
Proof.
  apply Zprop_implies_Confl_via_SemiConfl.
  apply Z_comp_eq_implies_Z_prop.
  apply lambda_x_Z_comp_eq.
Qed.
