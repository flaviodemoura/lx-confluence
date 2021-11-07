Require Import ZProperty Confluence LambdaES lx CompositionProblemLemmas OpenPoints Lia.

Require Import Arith MSetList Setoid Lia.

Fixpoint llc_at (k:nat) (t:pterm) : Prop :=
  match t with
  | pterm_bvar i    => i < k
  | pterm_fvar x    => True
  | pterm_app t1 t2 => llc_at k t1 /\ llc_at k t2
  | pterm_abs t1    => llc_at (S k) t1
  | pterm_sub t1 t2 => False
  end.

Lemma llc_at_open_var_rec : forall t x k,
  llc_at k (open_rec k x t) -> llc_at (S k) t.
Proof.
  intro t; induction t.
  - intros x k.
    simpl.
    bdall.
  - intros x k H.
    auto.
  - intros x k H.
    simpl in *.
    destruct H as [H1 H2].
    split.
    + apply IHt1 with x; assumption.
    + apply IHt2 with x; assumption.
  - intros x k H.
    simpl in *.
    apply IHt with x; assumption.
  - intros x k H.
    simpl in *.
    auto.
Qed.

Lemma llc_at_weaken_ind : forall k1 k2 t,
  llc_at k1 t -> k1 <= k2 -> llc_at k2 t.
Proof.
  intros k1 k2 t.
  generalize dependent k2.
  generalize dependent k1.
  induction t.
  - intros k1 k2 Hllc_at Hle.
    simpl in *.
    apply Nat.lt_le_trans with k1; assumption.
  - intros k1 k2 Hllc_at Hle.
    simpl; auto.
  - intros k1 k2 Hllc_at Hle.
    simpl in *.
    destruct Hllc_at as [H1 H2].
    split.
    + apply IHt1 with k1; assumption.
    + apply IHt2 with k1; assumption.
  - intros k1 k2 Hllc_at Hle.
    simpl.
    simpl in Hllc_at.
    apply IHt with (S k1).
    + assumption.
    + apply Peano.le_n_S; assumption.
  - intros k1 k2 Hllc_at Hle.
    inversion Hllc_at.
Qed.