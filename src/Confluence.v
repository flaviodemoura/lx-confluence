Require Import ZProperty.

Definition Confl {A:Type} (R: Rel A) := forall a b c, (refltrans R) a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

Definition SemiConfl {A:Type} (R: Rel A) := forall a b c, R a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

Theorem Z_prop_implies_SemiConfl {A:Type}: forall R: Rel A, Z_prop R -> SemiConfl R.
Proof.
  intros R HZ_prop.
  unfold Z_prop in HZ_prop.
  unfold SemiConfl.
  destruct HZ_prop.
  intros a b c Hrefl Hrefl'.
  assert (Haxa: refltrans R a (x a)).
  { 
    apply rtrans with b.  
    - assumption.  
    - apply H.  
      assumption.  
  }
  apply H in Hrefl.
  destruct Hrefl.
  clear H1.
  generalize dependent b.
  induction Hrefl'.
  - intros.
    exists (x a).
    split; assumption.
  - intros.
    destruct IHHrefl' with b0.
    + apply refltrans_composition with (x a); apply H; assumption.
    + apply refltrans_composition with (x b).
      * apply refltrans_composition with (x a).
        ** assumption.
        ** apply H.
           assumption.
      * apply refl.
    + exists x0.
      assumption.
Qed.

Lemma SemiConfl_imples_Confl{A: Type}: forall R:Rel A, SemiConfl R -> Confl R.
Proof.
  unfold Confl.
  unfold SemiConfl.
  intros.
  generalize dependent c.
  induction H0.
  - intros.
    exists c.
    split.
    * assumption.
    * apply refl.
  - intros.
    specialize (H a b c0).  
    apply H in H0.
    + destruct H0.
      destruct H0.
      apply IHrefltrans in H0.
      destruct H0.
      destruct H0.
      exists x0.
      split.
      * assumption.
      * apply refltrans_composition with x; assumption.
    + assumption.
Qed.

Lemma Confl_imples_SemiConfl{A: Type}: forall R:Rel A, Confl R -> SemiConfl R.
Proof.
  unfold Confl.
  unfold SemiConfl.
  intros.
  apply H with a.
  - apply rtrans with b.
    + assumption.
    + apply refl.
  - assumption.
Qed.

Theorem Semi_equiv_Confl {A: Type}: forall R: Rel A, Confl R <-> SemiConfl R.
Proof.
  intros.
  split.
  - apply Confl_imples_SemiConfl.
  - apply SemiConfl_imples_Confl.
Qed.

Corollary Zprop_implies_Confl_via_SemiConfl {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
Proof. 
  intros. 
  apply Semi_equiv_Confl. 
  apply Z_prop_implies_SemiConfl. 
  assumption.
Qed.

Corollary Z_comp_is_Confl {A}: forall (R: Rel A), Z_comp R -> Confl R.
Proof.
  intros R H.
  apply Z_comp_implies_Z_prop in H.
  apply Zprop_implies_Confl_via_SemiConfl.
  assumption.
Qed.

Corollary Z_comp_eq_is_Confl {A: Type}: forall (R: Rel A), Z_comp_eq R -> Confl R.
Proof.
    intros.
    apply Z_comp_eq_implies_Z_prop in H.
    apply Zprop_implies_Confl_via_SemiConfl.
    assumption.
Qed.