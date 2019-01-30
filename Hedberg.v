
(* The eliminator J *)
Definition J_T (A : Type) (x y :A) (p : x = y) (P : forall (x y :A), x = y -> Type) (c : forall (x : A), P x x eq_refl) : P x y p :=
  match p with
  | eq_refl => c x
  end.

Definition J_P (A : Type) (x y :A) (p : x = y) (P : forall (x y :A), x = y -> Prop) (c : forall (x : A), P x x eq_refl) : P x y p :=
  match p with
  | eq_refl => c x
  end.



(* Function Extensionality *)
Definition fun_ext := forall (A B : Type) (f g : A -> B) (x : A), f x = g x -> f = g.

Fixpoint eq_trans {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  induction p. assumption.
Defined.
Notation "p ° q" := (eq_trans p q) (at level 60).

(* eq_trans is defined recursively on the left path *)
Lemma eq_trans_refl_l : forall (A : Type) (x y : A)(p : x = y), eq_refl ° p = p.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma eq_trans_refl_r : forall (A : Type) (x y : A)(p : x = y), p ° eq_refl = p.
Proof.
  intros. subst. simpl. reflexivity.
Qed.

Definition eq_symm {A : Type} {x y : A} (p : x = y) : y = x.
  induction p. reflexivity.
Defined.

Lemma eq_symm_refl : forall (A : Type) (x : A), eq_symm (@eq_refl _ x)  = @eq_refl _ x.
Proof. intros. simpl. reflexivity. Qed.

Lemma eq_symm_involutive : forall (A : Type) (x y : A)(p : x = y), eq_symm (eq_symm p) = p.
Proof.
  intros. apply J_T with (A := A) (x := x) (y := y)(p := p).
  intros. simpl. reflexivity.
Qed.

(* 2: Preliminaries *)
Definition hProp (A : Type) : Prop := forall (x y : A), x = y.
Definition hSet (A : Type) : Prop := forall (x y : A), hProp (x = y).

Lemma hProp_is_hProp : forall (A : Type), hProp (hProp A).
Proof.
  admit.
Admitted.

Lemma hSet_is_hProp : forall (A : Type), hProp (hSet A).
Proof.
  admit.
Admitted.

Definition decidable (A : Type) : Type := A + (A -> False).

Definition discrete (A : Type) : Type := forall (x y : A), decidable (x = y).

Definition constant {A  B : Type}(f : A -> B) : Type :=  forall (x y : A), f x = f y.

Definition collapsible (A : Type) : Type := {f : A -> A & constant f}.

Definition path_collapsible (A : Type) : Type := forall (x y : A), collapsible (x = y).


(* 3 Hedberg's Theorem *)

Lemma hedberg_lemma_1 : forall (A : Type), discrete A -> path_collapsible A.
Proof.
  intros A H_discrete.
  unfold path_collapsible. intros x y.
  pose proof (H_discrete x y) as H_x_y_dec. unfold decidable in H_x_y_dec.
  destruct H_x_y_dec.
  - unfold collapsible.
    exists (fun p => e).
    unfold constant. intros. reflexivity.
  - unfold collapsible.
    exists (fun p => False_rect _ (f p)).
    unfold constant. intros. induction (f x0).
Qed.


Lemma hedberg_lemma_2 : forall (A : Type), path_collapsible A -> hSet A.
Proof.
  intros A H_path_collapsible.
  unfold path_collapsible in *. unfold collapsible in *.
  unfold hSet. unfold hProp.
  intros x y p q.
  assert (H :forall p,  p = ((projT1 (H_path_collapsible x y))p) ° (eq_symm ((projT1 (H_path_collapsible y y)) eq_refl))).
  - intro r. destruct r.
    generalize (projT1 (H_path_collapsible x x) eq_refl).
    intros. pose proof (J_P A x x e).
    apply H with (P := fun x y p => eq_refl = p ° eq_symm p). simpl. reflexivity.
  - rewrite (H p). rewrite (H q).
    pose proof (projT2 (H_path_collapsible x y)). unfold constant in X.
    specialize (X p q). unfold constant. repeat rewrite X. reflexivity.
Qed.

Theorem hedberg : forall (A : Type), discrete A -> hSet A.
Proof.
  intros.
  apply hedberg_lemma_2.
  apply hedberg_lemma_1.
  assumption.
Qed.

Print Assumptions hedberg.

  
  



  


  
  


  



  