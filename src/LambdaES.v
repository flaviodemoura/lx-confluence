Definition var := nat.

Require Import Arith MSetList Setoid Lia ZProperty Confluence.

Declare Module Var_as_OT : UsualOrderedType
  with Definition t := var.
Module Import VarSet := MSetList.Make Var_as_OT.

Definition vars := VarSet.t.

Notation "{}" := (VarSet.empty).
Notation "{{ x }}" := (VarSet.singleton x).
Notation "s [=] t " := (VarSet.Equal s t) (at level 70, no associativity). 
Notation "E \u F" := (VarSet.union E F)  (at level 68, left associativity).
Notation "x \in E" := (VarSet.In x E) (at level 69).
Notation "x \notin E" := (~ VarSet.In x E) (at level 69).
Notation "E << F" := (VarSet.Subset E F) (at level 70, no associativity).
Notation "E \rem F" := (VarSet.remove F E) (at level 70).

Lemma in_eq: forall x y, x \in {{y}} -> x = y.
Proof.
  intros x y H.
  apply VarSet.singleton_spec in H; assumption.
Qed.
  
Lemma notin_neq: forall x y, x \notin {{y}} -> x <> y.
Proof.
  intros x y H.
  intro Hneq.
  apply H.
  subst.
  apply singleton_spec; reflexivity.
Qed.
 
Lemma not_or_equiv_and_not: forall (A B: Prop), ~(A \/ B) <-> ~ A /\ ~ B.
Proof.
  split.
  - intro H.
    split.
    + intro H0.
      destruct H.
      left. 
      assumption.
    + intro H0.
      destruct H.
      right.
      assumption.
  - intros H H0.
    destruct H.
    destruct H0; contradiction.
Qed.


Lemma eq_var_dec : forall x y : var, {x = y} + {x <> y}.
Proof. exact eq_nat_dec. Qed.
Notation "x == y" := (eq_var_dec x y) (at level 67).

Notation  "a =? b" := (Nat.eqb b a) (at level 70) : nat_scope.
Notation  "a >=? b" := (Nat.leb b a) (at level 70) : nat_scope.
Notation  "a >? b"  := (Nat.ltb b a) (at level 70) : nat_scope.

Ltac inv H := inversion H; clear H; subst.

Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT :   P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H; split.
  - intro H'.
    inv H.
    + reflexivity.
    + contradiction.
  - intro H'; subst.
    inv H; assumption.
Qed.

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  split.
  - symmetry.
    apply Nat.eqb_eq; assumption.
  - intro H.
    symmetry in H.
    apply Nat.eqb_eq; assumption.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Ltac bdestruct_guard :=
  match goal with
  | |- context [ if ?X =? ?Y then _ else _ ] => bdestruct (X =? Y)
  | |- context [ if ?X <=? ?Y then _ else _ ] => bdestruct (X <=? Y)
  | |- context [ if ?X <? ?Y then _ else _ ] => bdestruct (X <? Y)
  end.

Ltac bdall :=
  repeat (simpl; bdestruct_guard; try lia; auto).

Lemma notin_union : forall x E F,
  x \notin (E \u F) <-> (x \notin E) /\ (x \notin F).
Proof.
intros x E F.
apply iff_stepl with (~((x \in E) \/ (x \in F))).
- apply not_or_equiv_and_not.
- split; unfold not; intros; destruct H; apply union_spec in H0; assumption.
Qed.

(** Pre-terms are defined according to the following grammar: *)
Inductive pterm : Set :=
  | pterm_bvar : nat -> pterm
  | pterm_fvar : var -> pterm
  | pterm_app  : pterm -> pterm -> pterm
  | pterm_abs  : pterm -> pterm
  | pterm_sub : pterm -> pterm -> pterm.

Notation "t [ u ]" := (pterm_sub t u) (at level 70).

Fixpoint fv (t : pterm) {struct t} : vars :=
  match t with
  | pterm_bvar i    => {}
  | pterm_fvar x    => {{x}}
  | pterm_app t1 t2 => (fv t1) \u (fv t2)
  | pterm_abs t1    => (fv t1)
  | pterm_sub t1 t2 => (fv t1) \u (fv t2)
  end.

Ltac gather_vars_with F :=
  let rec gather V :=
    match goal with
    | H: ?S |- _ =>
      let FH := constr:(F H) in
      match V with
      | {} => gather FH
      | context [FH] => fail 1
      | _ => gather (FH \u V)
      end
    | _ => V
    end in
  let L := gather {} in eval simpl in L.

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => {{ x }}) in
  let D := gather_vars_with (fun x : pterm => fv x) in
  constr:(A \u B \u D).

Ltac beautify_fset V :=
  let rec go Acc E :=
     match E with
     | ?E1 \u ?E2 => let Acc1 := go Acc E1 in
                     go Acc1 E2
     | {}  => Acc
     | ?E1 => match Acc with
              | {} => E1
              | _ => constr:(Acc \u E1)
              end
     end
  in go {} V.

Require Import List.
Open Scope list_scope.

Lemma max_lt_l :
  forall (x y z : nat), x <= y -> x <= max y z.
Proof.
  induction x; auto with arith.
  induction y; induction z; simpl; auto with arith.
Qed.

Lemma finite_nat_list_max : forall (l : list nat),
  { n : nat | forall x, In x l -> x <= n }.
Proof.
  induction l as [ | l ls IHl ].
  - exists 0; intros x H; inversion H.
  - inversion IHl as [x H]; clear IHl.
    exists (max x l).
    intros x' Hin.
    inversion Hin; subst.
    + auto with arith.
    + assert (x' <= x); auto using max_lt_l.
Qed.      

Lemma finite_nat_list_max' : forall (l : list nat),
  { n : nat | ~ In n l }.
Proof.
  intros l. case (finite_nat_list_max l); intros x H.
  exists (S x). intros J. assert (K := H _ J); lia.
Qed.

Definition var_gen (L : vars) : var :=
  proj1_sig (finite_nat_list_max' (elements L)).

Lemma var_gen_spec : forall E, (var_gen E) \notin E.
Proof.
  unfold var_gen. intros E.
  destruct (finite_nat_list_max' (elements E)) as [n pf].
  simpl. intros a. 
  destruct pf.
  apply elements_spec1 in a.
  rewrite InA_alt in a.
  destruct a as [y [H1 H2]].
  subst; assumption.
Qed.
  
Lemma var_fresh : forall (L : vars), { x : var | x \notin L }.
Proof.
  intros L. exists (var_gen L). apply var_gen_spec.
Qed.

Ltac pick_fresh_gen L Y :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  (destruct (var_fresh L) as [Y Fr]).

Ltac pick_fresh Y :=
  let L := gather_vars in (pick_fresh_gen L Y).

(** The open function implements the notion of metasubstitution for deBruijn indexes, in a theory where only deBruijn indexes are substituted. *)
Fixpoint open_rec (k : nat) (u : pterm) (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => if i =? k then u else (pterm_bvar i)
  | pterm_fvar x    => pterm_fvar x
  | pterm_app t1 t2 => pterm_app (open_rec k u t1) (open_rec k u t2)
  | pterm_abs t1    => pterm_abs (open_rec (S k) u t1 )
  | pterm_sub t1 t2 => pterm_sub (open_rec (S k) u t1) (open_rec k u t2)
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67). 
Notation "t ^ x" := (open t (pterm_fvar x)).   

Lemma open_rec_term_core :forall t j v i u, i <> j ->
  {j ~> v}t = {i ~> u}({j ~> v}t) -> t = {i ~> u}t.
Proof.
  intro t; induction t.
  - intros j v i u Hneq H.
    simpl.
    destruct (n =? i) eqn: Heq.
    + simpl in *.
      destruct (n =? j) eqn: Heq'.
      * apply beq_nat_true in Heq', Heq.
        subst.
        contradiction.
      * apply beq_nat_true in Heq.
        subst.
        simpl in H.
        rewrite <- beq_nat_refl in H.
        assumption.
    + reflexivity.
  - intros j v' i u Hneq H.
    reflexivity.
  - intros j v i u Hneq H.
    simpl in *.
    inversion H; subst.
    f_equal.
    + apply IHt1 with j v; assumption.
    + apply IHt2 with j v; assumption.
  - intros j v i u Hneq H.
    simpl in *.
    inversion H; subst.
    f_equal.
    apply IHt with (S j) v.
    + lia.
    + assumption.
  - intros j v i u Hneq H.
    simpl in *.
    inversion H; subst.
    f_equal.
    + apply IHt1 with (S j) v.
      * lia.
      * assumption.
    + apply IHt2 with j v; assumption.
Qed.
      
Fixpoint close_rec  (k : nat) (x : var) (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar x'    => if x' =? x then (pterm_bvar k) else pterm_fvar x'
  | pterm_app t1 t2 => pterm_app (close_rec k x t1) (close_rec k x t2)
  | pterm_abs t1    => pterm_abs (close_rec (S k) x t1)
  | pterm_sub t1 t2 => pterm_sub (close_rec (S k) x t1) (close_rec k x t2)
  end.
Notation "{ k <~ x } t " := (close_rec k x t)(at level 62).

Definition close t x := close_rec 0 x t.

(** Implicit substitution for free names. This is necessary to formalize the renaming of variables. *)
Fixpoint m_sb (z : var) (u : pterm) (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar x    => if x =? z then u else (pterm_fvar x)
  | pterm_abs t1    => pterm_abs (m_sb z u t1)
  | pterm_app t1 t2 => pterm_app (m_sb z u t1) (m_sb z u t2)
  | pterm_sub t1 t2 => pterm_sub (m_sb z u t1) (m_sb z u t2)
  end.
Notation "[ z ~> u ] t" := (m_sb z u t) (at level 62).

(** Substitution for a fresh name is identity. *)
Lemma subst_fresh : forall t x u,   x \notin fv t ->  [x ~> u] t = t.
Proof.
  intro t; induction t.
  - intros x u Hfv.
    reflexivity.
  - intros x u Hfv.
    simpl.
    destruct (v =? x) eqn: H. 
    + apply beq_nat_true in H.
      subst.
      simpl in *.
      unfold not in Hfv.
      destruct Hfv.
      apply singleton_spec; reflexivity.
    + reflexivity.
  - intros x u Hfv.
    simpl in *.
    apply notin_union in Hfv.
    destruct Hfv as [Hfv1 Hfv2].
    specialize (IHt1 x u).
    apply IHt1 in Hfv1.
    rewrite Hfv1.
    specialize (IHt2 x u).
    apply IHt2 in Hfv2.
    rewrite Hfv2.
    reflexivity.
  - intros x u Hfv.
    simpl in *.
    specialize (IHt x u).
    apply IHt in Hfv.
    rewrite Hfv.
    reflexivity.
  - intros x u Hfv.
    simpl in *.
    apply notin_union in Hfv.
    destruct Hfv as [Hfv1 Hfv2].
    specialize (IHt1 x u).
    apply IHt1 in Hfv1.
    rewrite Hfv1.
    specialize (IHt2 x u).
    apply IHt2 in Hfv2.
    rewrite Hfv2.
    reflexivity.
Qed.

Lemma m_sb_intro: forall t u x n, x \notin (fv t) -> [x ~> u] (open_rec n (pterm_fvar x) t)  = open_rec n u t.
Proof.
  intro t; induction t.
  - intros u x n' Hfv.
    assert (H1 := subst_fresh).
    specialize (H1 (pterm_bvar n) x u).
    apply H1 in Hfv. 
    simpl. 
    bdall. 
  - intros u x n' Hfv.
    simpl.
    destruct (v =? x) eqn: H.
    + apply beq_nat_true in H.
      subst.
      simpl in *.
      unfold not in Hfv.
      destruct Hfv.
      apply singleton_spec; reflexivity.
    + reflexivity. 
  - intros u x n' Hfv.
    simpl in *.
    apply notin_union in Hfv.
    destruct Hfv as [Hfv1 Hfv2].
    specialize (IHt1 u x n').
    apply IHt1 in Hfv1.
    rewrite Hfv1.
    specialize (IHt2 u x n').
    apply IHt2 in Hfv2.
    rewrite Hfv2.
    reflexivity.
  - intros u x n Hfv.
    unfold open.
    simpl.
    f_equal.
    apply IHt.
    assumption.
  - intros u x n Hfv.
    simpl in *.
    apply notin_union in Hfv.
    destruct Hfv as [Hfv1 Hfv2].
    specialize (IHt1 u x (S n)).
    apply IHt1 in Hfv1.
    rewrite Hfv1.
    specialize (IHt2 u x n).
    apply IHt2 in Hfv2.
    rewrite Hfv2.
    reflexivity.
Qed.

Corollary m_sb_intro_open: forall x t u, x \notin (fv t) -> [x ~> u] (t ^ x)  = t ^^ u.
Proof.
  intros x t u Hfv.
  apply m_sb_intro; assumption.
Qed.
 
(** ES terms are expressions without dangling deBruijn indexes. *)
Inductive term : pterm -> Prop :=
  | term_bvar : forall x,
      term (pterm_bvar x)
  | term_var : forall x,
      term (pterm_fvar x)
  | term_app : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (pterm_app t1 t2)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) ->
      term (pterm_abs t1)
  | term_sub : forall L t1 t2,
     (forall x, x \notin L -> term (t1 ^ x)) ->
      term t2 -> 
      term (pterm_sub t1 t2).

Definition body t := exists L, forall x, x \notin L -> term (t ^ x).

Fixpoint lc_at (k:nat) (t:pterm) : Prop :=
  match t with
  | pterm_bvar i    => i < k
  | pterm_fvar x    => True
  | pterm_app t1 t2 => lc_at k t1 /\ lc_at k t2
  | pterm_abs t1    => lc_at (S k) t1
  | pterm_sub t1 t2 => (lc_at (S k) t1) /\ lc_at k t2
  end.

Lemma lc_at_weaken_ind: forall k1 k2 t,
  lc_at k1 t -> k1 <= k2 -> lc_at k2 t.
Proof.
  intros k1 k2 t.
  generalize dependent k2.
  generalize dependent k1.
  induction t.
  - intros k1 k2 Hlc_at Hle.
    simpl in *.
    apply Nat.lt_le_trans with k1; assumption.
  - intros k1 k2 Hlc_at Hle.
    simpl. auto.
  - intros k1 k2 Hlc_at Hle.
    simpl in *.
    destruct Hlc_at as [H1 H2].
    split.
    + apply IHt1 with k1; assumption.
    + apply IHt2 with k1; assumption.
  - intros k1 k2 Hlc_at Hle.
    simpl.
    simpl in Hlc_at.
    apply IHt with (S k1).
    + assumption.
    + apply Peano.le_n_S; assumption.
  - intros k1 k2 Hlc_at Hle.
    simpl in *.
    destruct Hlc_at as [H1 H2].
    split.
    + apply IHt1 with (S k1).
      * assumption.
      * apply Peano.le_n_S; assumption.
    + apply IHt2 with k1; assumption.
Qed.

Lemma lc_at_open_var_rec : forall t x k,
  lc_at k (open_rec k x t) -> lc_at (S k) t.
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
    destruct H as [H1 H2].
    split.
    + apply IHt1 with x; assumption.
    + apply IHt2 with x; assumption.
Qed. 

Lemma term_to_lc_at : forall t, term t -> lc_at 0 t.
Proof.
Admitted.

Corollary term_lc_at: forall t n, term t -> lc_at n t.
Proof.
  intros t n H.
  pose proof Nat.eq_0_gt_0_cases n.
  inversion H0; clear H0.
  - subst.
    apply term_to_lc_at; assumption.
  - apply lc_at_weaken_ind with 0.
    + apply term_to_lc_at; assumption.
    + apply Nat.le_0_l.
Qed.
  
Lemma lc_at_open_rec : forall t n u, term u -> lc_at (S n) t -> lc_at n (open_rec n u t).
Proof.
  intro t; induction t.
  - intros n' u Hterm Hlc_at.
    simpl in *.
    bdall.
    + subst.
      apply term_lc_at; assumption.
    + simpl.
      lia.
  - intros n u Hterm Hlc_at.
    simpl in *.
    assumption.
  - intros n u Hterm Hlc_at.
    simpl in *.
    destruct Hlc_at as [H1 H2].
    split.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros n u Hterm Hlc_at.
    simpl in Hlc_at.
    apply IHt; assumption.
  - intros n u Hterm H.
    inversion H; subst; clear H.
    simpl; split.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
Qed.

Corollary lc_at_open : forall n t u, term u -> (lc_at (S n) t <-> lc_at n (open_rec n u t)).
Proof.
  intros n t u; split.
  - apply lc_at_open_rec; assumption. 
  - apply lc_at_open_var_rec.
Qed.

Lemma lc_at_open_rec_leq : forall t n k u, n <= k -> lc_at n t -> lc_at n (open_rec k u t).
Proof.
  intro t; induction t.
  - intros n' k u Hleq Hlc_at. 
    simpl in *.
    bdall.
  - intros n' k u Hleq Hlc_at.
    assumption.
  - intros n' k u Hleq Hlc_at.
    destruct Hlc_at.
    simpl; split.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros n' k u Hleq Hlc_at.
    simpl in *.
    apply IHt.
    + apply le_n_S; assumption.
    + assumption.
  - intros n' k u Hleq Hlc_at.
    destruct Hlc_at.
    simpl in *; split.
    + apply IHt1.
      * apply le_n_S; assumption.
      * assumption.
    + apply IHt2; assumption.
Qed.

Lemma lc_at_open_rec_gt : forall t n k u, n > k -> lc_at n t -> lc_at n u -> lc_at n (open_rec k u t).
Proof.
  intro t; induction t.
  - intros n' k u H Hlc1 Hlc2.
    simpl in *.
    destruct (n =? k) eqn:Heq.
    + assumption.
    + simpl.
      assumption.
  - intros n k u Hgt Hlc1 Hlc2.
    auto.
  - intros n k u Hgt Hlc1 Hlc2.
    simpl in *.
    destruct Hlc1 as [H1 H2]; split.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros n k u Hgt Hlc1 Hlc2.
    simpl in *.
    apply IHt.
    + lia.
    + assumption.
    + apply lc_at_weaken_ind with n.
      * assumption.
      * lia.
  - intros n k u Hgt H1 H2.
    simpl in *.
    destruct H1 as [Hlc1 Hlc2]; split.
    + apply IHt1.
      * lia.
      * assumption.
      * apply lc_at_weaken_ind with n.
        ** assumption.
        ** lia.
    + apply IHt2; assumption.
Qed.   
    
Lemma lc_at_open_gen : forall t n u, lc_at (S n) u -> lc_at (S n) t -> lc_at (S n) (t ^^ u).
Proof.
  intro t.
  unfold open.
  generalize dependent 0.
  induction t.
  - intros n' n'' u H1.
    simpl.
    destruct (n =? n') eqn:H.
    + intro H2.
      assumption.
    + intro H2.
      simpl; assumption.
  - intros n n' u H1 H2.
    auto.
  - intros n n' u H1 H2.
    simpl in *.
    destruct H2 as [Hlc1 Hlc2]; split.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros n n' u Hu Hlc.
    simpl in *.
    apply IHt.
    +  apply lc_at_weaken_ind with (S n').
       * assumption.
       * auto.         
    + assumption.
  - intros n n' u H1 H2.
    simpl in *.
    destruct H2 as [Hlc1 Hlc2]; split.
    + apply IHt1.
      * apply lc_at_weaken_ind with (S n').
       ** assumption.
       ** auto.
      * assumption.
    + apply IHt2; assumption.
Qed.

Lemma lc_at_open_rec_rename: forall t x y m n, lc_at m (open_rec n (pterm_fvar x) t) -> lc_at m (open_rec n (pterm_fvar y) t).
Proof.
  intro t; induction t.
  - intros x y m k.
    simpl.
    bdall.
  - intros x y m n H.
    simpl; auto.
  - intros x y m n H.
    simpl in *.
    inversion H as [H1 H2]; split.
    + apply IHt1 with x; assumption.
    + apply IHt2 with x; assumption.
  - intros x y m n H.
    simpl in *.
    apply IHt with x; assumption.
  - intros x y m n Hlc_at.
    simpl in *.
    destruct Hlc_at as [H1 H2]; split.
    + apply IHt1 with x; assumption.      
    + apply IHt2 with x; assumption.
Qed.

Fixpoint pterm_size (t : pterm) :=
 match t with
 | pterm_bvar i    => 1
 | pterm_fvar x    => 1
 | pterm_abs t1    => 1 + (pterm_size t1)
 | pterm_app t1 t2 => 1 + (pterm_size t1) + (pterm_size t2)
 | pterm_sub t1 t2 => 1 + (pterm_size t1) + (pterm_size t2)
 end.

Lemma pterm_size_positive: forall t, 0 < pterm_size t.
Proof.
  induction t0; simpl; auto with arith.
Qed.
    
Lemma pterm_size_open: forall t x, pterm_size (t^x) = pterm_size t.
Proof.
  unfold open.
  intros t x.
  generalize dependent 0.
  generalize dependent x.
  induction t.
  - unfold open_rec.
    intros x n'.
    bdall.
  - reflexivity.
  - simpl.
    intros x n.
    destruct (IHt1 x n).
    destruct (IHt2 x n).
    reflexivity.
  - simpl.
    intros x n.
    destruct (IHt x (S n)); reflexivity.
  - simpl.
    intros x n.
    destruct (IHt1 x (S n)).
    destruct (IHt2 x n).
    reflexivity.
Qed.

Lemma strong_induction :  forall Q: nat -> Prop,
    (forall n, (forall m, m < n -> Q m) -> Q n) ->
    forall n, Q n.
Proof.
  intros Q IH n.
  assert (H := nat_ind (fun n => (forall m : nat, m < n -> Q m))).
  apply IH.
  apply H.
  - intros m Hlt; inversion Hlt.
  - intros n' H' m Hlt.
    apply IH.
    intros m0 Hlt'.
    apply H'.
    apply lt_n_Sm_le in Hlt.
    apply lt_le_trans with m; assumption.
Qed.

Lemma pterm_size_induction :
 forall P : pterm -> Prop,
 (forall t,
    (forall t', pterm_size t' < pterm_size t ->
    P t') -> P t) ->
 (forall t, P t).
Proof.
  intros P IH t.
  remember (pterm_size t) as n eqn:H.
  assert (HsiInst := strong_induction (fun n => forall t, n = pterm_size t -> P t)).
  generalize dependent t.
  generalize dependent n.
  apply HsiInst.
  intros n' Hind t Hsz.
  apply IH.
  intros t' Hlt.
  apply Hind with (pterm_size t').
  - rewrite Hsz; assumption.  
  - reflexivity.
Qed.

Lemma pterm_induction :
 forall P : pterm -> Prop,
 (forall n, P (pterm_bvar n)) ->
 (forall x, P (pterm_fvar x)) ->
 (forall t1,
    (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 ->
    P (t2 ^ x)) -> P (pterm_abs t1)) ->
 (forall t1 t2, P t1 -> P t2 -> P (pterm_app t1 t2)) ->
 (forall t1 t3, P t3 -> 
    (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 ->
    P (t2 ^ x)) -> P (t1[t3])) -> 
 (forall t, P t).
Proof.
  intros P Hbvar Hfvar Habs Happ Hsub t; induction t using pterm_size_induction.
  generalize dependent t0.
  intro t; case t.
  - intros n IH.
    apply Hbvar.
  - intros v IH.
    apply Hfvar.
  - intros t1 t2 IH.
    apply Happ; apply IH; simpl; lia.
  - intros t1 IH.
    apply Habs.
    intros t1' x Hfv Hsize.
    apply IH.
    simpl.
    rewrite pterm_size_open.
    lia.
  - intros t1 t2 IH.
    apply Hsub.
    + apply IH.
      simpl.
      lia.
    + intros t1' x Hfv Hsize.
      apply IH.
      simpl.
      rewrite pterm_size_open.
      lia.
Qed.
      
Theorem term_equiv_lc_at: forall t, term t <-> lc_at 0 t.
Proof.
  intro t; split.
  - apply term_to_lc_at.
  - induction t using pterm_size_induction.
    induction t0.
    + intro Hlc_at.
      inversion Hlc_at.
    + intro Hlc_at.
      apply term_var.
    + simpl.
      intro Hlc_at.
      destruct Hlc_at as [Hlc1 Hlc2].
      apply term_app.
      * apply H.
        ** simpl.
           apply lt_trans with (pterm_size t0_1 + pterm_size t0_2).
           *** apply Nat.lt_add_pos_r.
               apply pterm_size_positive.
           *** auto.
        ** assumption.
      * apply H.
        ** simpl.
           apply lt_trans with (pterm_size t0_1 + pterm_size t0_2).
           *** apply Nat.lt_add_pos_l.
               apply pterm_size_positive.
           *** auto.
        ** assumption.
    + intro Hlc_at. 
      apply term_abs with (fv t0).
      intros x Hfv.
      apply H.
      * rewrite pterm_size_open.
        simpl; auto.
      * simpl in Hlc_at.
        apply lc_at_open.
        ** apply term_var.
        ** assumption.
    + intro Hlc_at.
      apply term_sub with (fv t0_1).
      * intros x Hfv.
        apply H.
        ** rewrite pterm_size_open.
           simpl; auto with arith.
        ** simpl in Hlc_at.
           apply lc_at_open.
           *** apply term_var.
           *** apply Hlc_at.
      * apply IHt0_2.
        ** intros t H0 H1.
           apply H.
           *** simpl.
               assert (a_lt_ab: forall a b c, a < c -> a < b + c).
               {
                 intros a b c Habc.
                 induction b.
                 auto with arith.
                 assert (S_in_out: S b + c = S (b + c)).
                 {
                   auto with arith.
                 }
                 rewrite S_in_out.
                 auto with arith.
               }
               assert (S_out_in: forall t1 t2, S (pterm_size t2 + pterm_size t1) = pterm_size t2 + S (pterm_size t1)).
               {
                 intros.
                 apply plus_n_Sm.
               }
               rewrite S_out_in.
               apply a_lt_ab.
               auto with arith.
           *** assumption.
        ** simpl in Hlc_at.
           apply Hlc_at.
Qed.

Theorem body_lc_at: forall t, body t <-> lc_at 1 t.
Proof.
  intro t.
  split.
  - intro Hbody.
    unfold body in Hbody.
    destruct Hbody.
    assert (Hlc_at :  forall x0 : elt, x0 \notin x -> lc_at 0 (t ^ x0)).
    {
      intros x' Hnot.
      apply term_equiv_lc_at.
      apply H; assumption.
    }
    clear H.
    unfold open in Hlc_at.
    pick_fresh y.
    apply notin_union in Fr.
    destruct Fr.
    apply Hlc_at in H.
    generalize dependent H.
    apply lc_at_open.
    apply term_var.
  - intro Hlc_at.
    unfold body.
    exists (fv t).
    intros x Hnot.
    apply term_equiv_lc_at.
    unfold open.
    apply lc_at_open.
    + apply term_var.
    + assumption.
Qed.
      

(** bswap replaces 0s by 1s and vice-versa. Any other index is preserved. *)
Fixpoint has_free_index (k:nat) (t:pterm) : Prop :=
  match t with
    | pterm_bvar n => if (k =? n) then True else False
    | pterm_fvar x => False
    | pterm_app t1 t2 => (has_free_index k t1) \/ (has_free_index k t2)
    | pterm_abs t1 => has_free_index (S k) t1
    | pterm_sub t1 t2 => (has_free_index (S k) t1) \/ (has_free_index k t2)
  end.

Lemma has_index: forall i, has_free_index i (pterm_bvar i).
Proof.
  intro i. simpl. bdall.
Qed.

(** The locally nameless framework manipulates expressions that are a representation of the lambda-terms, and not all pre-terms. In this sense, if t reduces to t' then both t and t' are terms: *)
Definition term_regular (R : Rel pterm) :=
  forall t t', R t t' -> term t /\ term t'.

(** Check if y \notin (fv t') is necessary. *)
Definition red_rename (R : Rel pterm) :=
  forall x t t' y,
    x \notin (fv t) ->
    x \notin (fv t') ->
  R (t ^ x) (t' ^ x) -> 
  R (t ^ y) (t' ^ y).

Lemma body_app: forall t1 t2, body (pterm_app t1 t2) -> body t1 /\ body t2.
Proof.
  intros t1 t2 Hbody.
  inversion Hbody; subst.
  unfold body.
  split.
  - exists x.
    intros x0 Hnot.
    apply H in Hnot.
    inversion Hnot; subst.
    assumption.
  - exists x.
    intros x0 Hnot.
    apply H in Hnot.
    inversion Hnot; subst.
    assumption.
Qed.
  
Lemma term_regular_trans: forall R, term_regular R -> term_regular (trans R).
Proof.
unfold term_regular.
intros R H t t' Htrans.
induction Htrans.
- apply H; assumption.
- destruct IHHtrans as [Hb Hc].
  apply H in H0.
  destruct H0 as [Ha Hb'].
  auto.
Qed.
   
Corollary term_open_rename: forall t x y, term (t^x) -> term (t^y).  
Proof.
  intros t x y H.
  apply term_to_lc_at in H.
  apply term_equiv_lc_at.
  unfold open in H.
  apply lc_at_open_rec_rename with x; assumption.
Qed.

Lemma body_to_term: forall t x, x \notin fv t -> body t -> term (t^x).
Proof.
  intros t x Hfc Hbody.
  unfold body in Hbody.
  destruct Hbody as [L H].
  pick_fresh y.
  apply notin_union in Fr.
  destruct Fr as [Fr Hfvt].
  apply notin_union in Fr.
  destruct Fr as [Fr Hfvx].
  apply H in Fr.
  apply term_open_rename with y; assumption.
Qed.

Fixpoint bswap_rec (k : nat) (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => if k =? i then (pterm_bvar (S k))
                       else (if (S k) =? i then (pterm_bvar k) else t)
  | pterm_fvar x    => t
  | pterm_app t1 t2 => pterm_app (bswap_rec k t1) (bswap_rec k t2)
  | pterm_abs t1    => pterm_abs (bswap_rec (S k) t1)
  | pterm_sub t1 t2 => pterm_sub (bswap_rec (S k) t1) (bswap_rec k t2)
  end.
      
Definition bswap t := bswap_rec 0 t.
Notation "& t" := (bswap t) (at level 67).

Lemma lc_at_bswap_rec: forall t k i, k <> (S i) -> lc_at k t -> lc_at k (bswap_rec i t).
Proof.
  intro t; induction t.
  - intros k i Hneq Hlt.
    simpl in *.
    bdall.
    + subst.
      simpl.
      destruct Hlt. 
      * contradiction.
      * auto with arith.
    + bdall.
      destruct n.
      * simpl.
        inversion H0.
      * unfold lc_at.
        inversion H0; subst.
        apply lt_trans with (S n).
        ** apply Nat.lt_succ_diag_r.
        ** assumption.
  - trivial.
  - intros k i Hneq Hlc_at.
    simpl in *.
    destruct Hlc_at as [H1 H2].
    split.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros k i Hneq Hlc_at.
    simpl in *.
    apply IHt.
    + auto.
    + assumption.
  - intros k i Hneq Hlc_at.
    simpl in *.
    destruct Hlc_at as [H1 H2].
    split.
    + apply IHt1. 
      * intro H.
        inversion H.
        contradiction.
      * assumption.
    + apply IHt2; assumption.
Qed.

Corollary lc_at_bswap: forall t k, k <> 1 -> lc_at k t -> lc_at k (& t).
Proof.
  intros t k.
  apply lc_at_bswap_rec.
Qed.
  
Lemma bswap_rec_id : forall t n, bswap_rec n (bswap_rec n t)  = t.
Proof.
 intro t; induction t.
 - intro n'.
   bdall.
   destruct n.
   + subst.
     reflexivity.
   + subst.
     destruct (n =? S n) eqn: H.
     * apply beq_nat_true in H.
       pose proof Nat.neq_succ_diag_l.
       specialize (H1 n).
       contradiction.
     * reflexivity.
 - reflexivity.
 - intro n.
   simpl.
   rewrite (IHt1 n).
   rewrite (IHt2 n).
   reflexivity.
 - intro n.
   simpl.
   rewrite (IHt (S n)).
   reflexivity.
 - intro n.
   simpl.
   rewrite (IHt1 (S n)).
   rewrite (IHt2 n).
   reflexivity.
Qed.

Lemma bswap_idemp : forall t, (& (& t)) = t.
Proof.
  intro t. unfold bswap.
  apply bswap_rec_id.
Qed.

Lemma lc_at_bvar: forall k n, lc_at k (pterm_bvar n) -> n < k.
Proof.
  auto.
Qed.

Lemma lc_at_least_open_rec: forall t k n u, k <= n -> lc_at k t -> {n ~> u} t = t.
Proof.
  intro t; induction t.
  - intros k n' u H H0.
    apply lc_at_bvar in H0.
    unfold open_rec.
    assert (H1: n < n').
    {
      apply Nat.lt_le_trans with k; assumption.
    }
    bdall.
    - reflexivity.
    - intros k n u H H0.
      simpl in *.
      assert (H': k <= n).
      {
        assumption.
      }
      destruct H0 as [H1 H2].
      f_equal.
      + apply IHt1 with k; assumption.
      + apply IHt2 with k; assumption.
    - intros k n u H H0.
      simpl in *.
      f_equal.
      apply IHt with (S k).
      + auto with arith.
      + assumption.
    - intros k n u H H0.
      simpl in *.
      f_equal.
      + apply IHt1 with (S k).
        * auto with arith.
        * apply H0. 
      + apply IHt2 with k.
        * assumption.
        * apply H0.
Qed. 


Lemma open_rec_term: forall t n u,  term t -> {n ~> u} t = t.
Proof.
  intros t n u Hterm.
  apply term_to_lc_at in Hterm.
  generalize dependent Hterm.
  apply lc_at_least_open_rec.
  apply Peano.le_0_n.
Qed.

Lemma open_rec_swap: forall t x x' i j, i <> j -> {j ~> pterm_fvar x'} ({i ~> pterm_fvar x} t) = {i ~> pterm_fvar x}({j ~> pterm_fvar x'} t).
Proof.
  intro t; induction t.
  - intros x x' i j H.
    simpl.
    destruct (n =? i) eqn:Heq.
    + destruct (n =? j) eqn:Heq'.
      * assert (Hij: i = j).
        {
          apply EqNat.beq_nat_true in Heq.
          rewrite Heq.
          apply EqNat.beq_nat_true in Heq'.
          rewrite Heq'.
          reflexivity.
        }
        contradiction.
      * apply EqNat.beq_nat_true in Heq.
        rewrite Heq.
        simpl.
        rewrite PeanoNat.Nat.eqb_refl.
        reflexivity.
    + destruct (n =? j) eqn:Heq'.
      * apply EqNat.beq_nat_true in Heq'.
        rewrite Heq'.
        simpl.
        rewrite PeanoNat.Nat.eqb_refl.
        reflexivity.
      * simpl.
        rewrite Heq.
        rewrite Heq'.
        reflexivity.
  - intros x x' i j H.
    reflexivity.
  - intros x x' i j H.
    simpl.
    f_equal.
    + rewrite IHt1.
      * reflexivity.
      * assumption.
    + rewrite IHt2.
      * reflexivity.
      * assumption.
  - intros x x' i j H.
    simpl.
    rewrite IHt.
    + reflexivity.
    + intro Hfalse.
      apply H.
      inversion Hfalse; reflexivity.
  - intros x x' i j H.
    simpl.
    rewrite IHt1.
    + rewrite IHt2.
      * reflexivity.
      * assumption.
    + intro Hij.
      inversion Hij.
      contradiction.
Qed.    

(*
Lemma open_rec_commute: forall t u v n, term v -> 
(open_rec (S n) u (open_rec n v t)) = (open_rec n u (open_rec (S n) v (bswap_rec n t))).
Proof.
 Admitted.

Lemma open_rec_swap_term: forall t u v n, term v -> {S n ~> u} ({n ~> v} t) = {n ~> u}({S n ~> v} (&t)).
*)

(** Contextual closure of terms. *)
Inductive ES_contextual_closure (R: Rel pterm) : Rel pterm :=
  | ES_redex : forall t s, R t s -> ES_contextual_closure R t s
  | ES_app_left : forall t t' u, ES_contextual_closure R t t' -> term u ->
	  		      ES_contextual_closure R (pterm_app t u) (pterm_app t' u)
  | ES_app_right : forall t u u', ES_contextual_closure R u u' -> term t ->
	  		       ES_contextual_closure R (pterm_app t u) (pterm_app t u')
  | ES_abs_in : forall t t' L, (forall x, x \notin L -> ES_contextual_closure R (t^x) (t'^x)) ->
                               ES_contextual_closure R (pterm_abs t) (pterm_abs t')
  | ES_sub : forall t t' u L, (forall x, x \notin L -> ES_contextual_closure R (t^x) (t'^x)) ->
                         term u -> ES_contextual_closure R  (t [u]) (t' [u])
  | ES_sub_in : forall t u u', ES_contextual_closure R u u' -> body t ->
	  	               ES_contextual_closure R  (t [u]) (t [u']). 

Lemma term_regular_ctx: forall R, term_regular R -> term_regular (ES_contextual_closure R).
Proof.
  intros R Hred.
  unfold term_regular.
  intros t t' Hcc.
  induction Hcc.
  - apply Hred; assumption.
  - split.
    + apply term_app; auto.
      apply IHHcc.
    + apply term_app; auto.
      apply IHHcc.
  - split.
    + apply term_app; auto.
      apply IHHcc.
    + apply term_app; auto.
      apply IHHcc.
  - split.
    + apply term_abs with L.
      apply H0.
    + apply term_abs with L.
      apply H0.
  - split.
    + apply term_sub with L.
      * apply H0.
      * assumption.
    + apply term_sub with L.
      * apply H0.
      * assumption.
  - split.
    + apply term_sub with (fv t0).
      * intros x Hfv.
        apply body_to_term; assumption.
      * apply IHHcc.
    + apply term_sub with (fv t0).
      * intros x Hfv.
        apply body_to_term; assumption.
      * apply IHHcc.
Qed.

(** expressions without explicit substitutions. *)
Inductive lterm : pterm -> Prop :=
  | lterm_bvar : forall n, lterm (pterm_bvar n)
  | lterm_var : forall x,
      lterm (pterm_fvar x)
  | lterm_app : forall t1 t2,
      lterm t1 -> 
      lterm t2 -> 
      lterm (pterm_app t1 t2)
  | lterm_abs : forall t1,
      lterm t1 ->
      lterm (pterm_abs t1).

Lemma lterm_msub : forall t1 t2 n, lterm t1 -> lterm t2 -> lterm ({n ~> t2}t1).
Proof.
  intros.
  generalize dependent n.
  induction t1.
  - intros.
    simpl.
    destruct (n0 =? n).
    + destruct (n =? n0).
      * assumption.
      * assumption.
    + destruct (n =? n0).
      * assumption.
      * assumption.
  - intros.
    simpl.
    apply lterm_var.
  - intros. 
    simpl.
    apply lterm_app.
    + apply IHt1_1.
      inversion H.
      assumption.
    + apply IHt1_2.
      inversion H.
      assumption.
  - intros.
    simpl.
    apply lterm_abs.
    apply IHt1.
    inversion H.
    assumption.
  - inversion H.
Qed.

Definition lbody t := exists L, forall x, x \notin L -> lterm (t ^ x).

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

Lemma lterm_open_rec_rename: forall t x y n, lterm ({n ~> pterm_fvar x} t) -> lterm ({n ~> pterm_fvar y} t).  
Proof.
  intros.
  apply lterm_msub.
  - admit. (** ok **)
  - apply lterm_var.
Admitted.

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


Lemma lc_at_open_rec': forall t u n, lc_at n u -> lc_at (S n) t -> lc_at n (open_rec n t u).
Proof.
  intro t; induction t using pterm_size_induction.
  generalize dependent H.
  case t0.
  - intros n IH u Hu.
    case n.
    + intro Ht.
      unfold open.
      simpl.
Admitted.

Corollary lc_at_open_intro : forall t u, lc_at 0 u -> lc_at 1 t -> lc_at 0 (t ^^ u).
Proof.
Admitted.