(****************************************
Maximiliano Cristia - Ricardo David Katz 
                  2026                   
****************************************)

Set Implicit Arguments.

Require Import Arith List.
Require Import preliminaries terms_constraints list_variables substitution.

(* returns a list containing the depths at which the    
   variable v occurs in the term t when t is a set term *)
Fixpoint depths (v : log_variable) (t : term) : list nat :=
  match t with
  | EmptySet => nil
  | Var (LogV n) => match v with
                   |LogV n' => if (n =? n') then (0 :: nil) else nil
                   end
  | SetC t' EmptySet => map S (depths v t')
  | SetC t' t'' => (map S (depths v t')) ++ (depths v t'')
  | _ => nil
  end.

(* returns a list containing the depths at which the 
   variable v occurs in the term t *)
Fixpoint depthsT (v : log_variable) (t : term) : list nat :=
  match t with
  | Var (LogV n) => match v with
                   |LogV n' => if (n =? n') then (0 :: nil) else nil
                   end
  | SetC t' EmptySet => map S (depthsT v t')
  | SetC t' t'' => (map S (depthsT v t')) ++ (depthsT v t'')
  | OTerm _ l =>
      let depthsT_list :=
        (fix depthsT_list (v : log_variable) (l : list term) {struct l} : list nat :=
           match l with
           | nil => nil
           | t :: lt =>  (depthsT v t) ++ (depthsT_list v lt)
           end) in
       (map S (depthsT_list v l))
  | _ => nil
  end.

(* returns the maximal depth at which EmptySet occurs
   in the term t when t is a set term *)
Fixpoint depth_EmptySet (t : term) : nat :=
  match t with
  | EmptySet => 0
  | SetC t' t'' => Nat.max (S (depth_EmptySet t')) (depth_EmptySet t'')
  | _ => 0
  end.

(* returns the maximal depth of a term t *)
Fixpoint depth_max (t : term) : nat :=
  match t with
  | Var _ => 0
  | SetC t1 t2 => Nat.max (S (depth_max t1)) (depth_max t2)
  | OTerm _ l =>
      let depth_max_list :=
        (fix depth_max_list (l : list term) {struct l} : nat :=
           match l with
           | nil => 0
           | t :: lt => Nat.max (depth_max t) (depth_max_list lt)
           end) in
       S (depth_max_list l)
  | EmptySet => 0
  end.

(* returns a list with the depth at which EmptySet occurs in the term t,
   if t appears in a primitive constraints of the form (Var v \== t)
   in the constraint c *)
Fixpoint ListFindNiNeq (c : constraint) :=
  match c with
  | nil => nil
  | (Var v \== t) :: lpc => (depth_EmptySet t) :: (ListFindNiNeq lpc)
  | _ :: lpc => (ListFindNiNeq lpc)
  end.

(* returns a list with the depth at which EmptySet occurs in the term t,
   if t appears in a primitive constraints of the form (t \:s Var v)
   in the constraint c *)
Fixpoint ListFindNiNin (c : constraint) :=
  match c with
  | nil => nil
  | (t \:s Var v) :: lpc => (depth_EmptySet t) :: (ListFindNiNin lpc)
  | _ :: lpc => (ListFindNiNin lpc)
  end.

(* returns a list containing the depths at which each variable in a list of variables l
   occurs in the term t when t is a set term *)
Fixpoint ListDepthsInTerm (lv : list log_variable) (t : term) :=
  match lv with
  | nil => nil
  | v :: lv' => (depths v t) ++ (ListDepthsInTerm lv' t)
  end.

(* returns a list containing the depths at which each variable in a list of variables lv
   occurs in a term t which appears in a primitive constraints of the form (Var v \== t)
   in the constraint c *)
Fixpoint ListDepthsNeq (lv : list log_variable) (c : constraint) :=
  match c with
  | nil => nil
  | (Var v \== t) :: lpc => (ListDepthsInTerm lv t) ++ (ListDepthsNeq lv lpc)
  | _ :: lpc => (ListDepthsNeq lv lpc)
  end.

(* returns a list containing the depths at which each variable in a list of variables lv
   occurs in a term t which appears in a primitive constraints of the form (t \:s Var v)
   in the constraint c *)
Fixpoint ListDepthsNin (lv : list log_variable) (c : constraint) :=
  match c with
  | nil => nil
  | (t \:s Var v) :: lpc => (ListDepthsInTerm lv t) ++ (ListDepthsNin lv lpc)
  | _ :: lpc => (ListDepthsNin lv lpc)
  end.

(***********************)
(* properties of depth *)
(***********************)

Lemma depth_EmptySet_lt t1 t2 :
  depth_EmptySet t1 < depth_EmptySet ({{t1 | t2}}).
Proof.
simpl; case (depth_EmptySet t2); try now apply Nat.lt_succ_diag_r.
intro n.
apply Nat.lt_le_trans with (m := S (depth_EmptySet t1)); try now apply Nat.lt_succ_diag_r.
apply le_n_S.
now apply Nat.le_max_l.
Qed.

Lemma depth_max_lt t1 t2 :
  depth_max t1 < depth_max ({{t1 | t2}}).
Proof.
simpl; case (depth_max t2); try now apply Nat.lt_succ_diag_r.
intro n.
apply Nat.lt_le_trans with (m := S (depth_max t1)); try now apply Nat.lt_succ_diag_r.
apply le_n_S.
now apply Nat.le_max_l.
Qed.

Lemma list_max_ListDepthsInTerm_SetC v t1 t2 :
  list_max (ListDepthsInTerm (v :: nil) ({{t1 | t2}})) =
    Nat.max (list_max (map S (ListDepthsInTerm (v :: nil) t1))) (list_max (ListDepthsInTerm (v :: nil) t2)).
Proof.
destruct v as [i].
case t2.
- intros [j]; simpl.
  case (j =? i); do 2 rewrite app_nil_r.
  + now rewrite list_max_app.
  + do 2 rewrite app_nil_r.
    now rewrite Nat.max_0_r.
- intros ? ?.
  simpl; do 2 rewrite list_max_app.
  do 2 rewrite app_nil_r.
  now rewrite Nat.max_0_r.
- intros ? ?.
  simpl; do 3 rewrite app_nil_r.
  now rewrite Nat.max_0_r.
- simpl; do 2 rewrite app_nil_r.
  now rewrite Nat.max_0_r.
Qed.

Lemma depth_EmptySet_SetC t1 t2 :
  depth_EmptySet ({{t1 | t2}}) = (Nat.max (S (depth_EmptySet t1)) (depth_EmptySet t2)).
Proof.
trivial.
Qed.

Lemma depth_max_SetC t1 t2 :
  depth_max ({{t1 | t2}}) = (Nat.max (S (depth_max t1)) (depth_max t2)).
Proof.
trivial.
Qed.

Lemma ListDepthsNeq_nil (c : constraint) :
  ListDepthsNeq nil c = nil.
Proof.
elim c; try trivial.
intros pc ? Hind.
case pc.
- now intros; simpl; rewrite Hind.
- intros t1 t2.
  now case t1.
- now intros; simpl; rewrite Hind.
- now intros; simpl; rewrite Hind.
- now simpl; rewrite Hind.
- now intro; simpl; rewrite Hind.
Qed.

Lemma ListDepthsNin_nil (c : constraint) :
  ListDepthsNin nil c = nil.
Proof.
elim c; trivial.
intros pc ? Hind.
case pc.
- now intros; simpl; rewrite Hind.
- now intros; simpl; rewrite Hind.
- now intros; simpl; rewrite Hind.
- intros t1 t2.
  now case t2.
- now simpl; rewrite Hind.
- now intro; simpl; rewrite Hind.
Qed.

Lemma ListDepthsInTerm_listVarInT v t :
  (ListDepthsInTerm (v :: nil) t) <> nil -> In v (listVarInT t).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
  (ListDepthsInTerm (v :: nil) t') <> nil -> In v (listVarInT t'))).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  now absurd (sizet t' <= 0); [apply sizet_gte_1 | assumption].
- destruct v as [i].
  intros t'.
  case t'.
  + intros [j] _ HLdephs.
    case (eq_nat_dec j i) as [-> | Hneq]; try now left.
    assert (Hfalse : (j =? i) = false).
      now apply Nat.eqb_neq.
    simpl in HLdephs.
    now rewrite Hfalse in HLdephs.
  + intros t1 t2 Hsizet HLdephs.
    destruct (sizet_SetC Hsizet) as [Hsizet1 Hsizet2].
    revert HLdephs.
    revert Hsizet2.
    case t2.
    * intros [j] _ HLdepths.
      case (eq_nat_dec j i) as [-> | Hneq].
      -- apply in_or_app.
         now right; apply in_eq.
      -- apply in_or_app.
         left.
         apply Hind; try assumption.
         simpl; rewrite app_nil_r.
         intro HLdepths_t1.
         absurd (map S (depths (LogV i) t1) = nil); try now rewrite HLdepths_t1.
         assert (Hfalse : (j =? i)= false).
           now apply Nat.eqb_neq.
         simpl in HLdepths.
         rewrite Hfalse in HLdepths.
         now do 2 rewrite app_nil_r in HLdepths.
    * intros t3 t4 Hsizet2 Hneq_nil.
      case (list_eq_dec eq_nat_dec (ListDepthsInTerm (LogV i :: nil) t1) nil) as [Heq_nil1 | Hneq_nil1].
      -- assert (Heq_nil2 : (ListDepthsInTerm (LogV i :: nil) ({{t3 | t4}})) <> nil).
           simpl in Hneq_nil.
           simpl in Heq_nil1.
           rewrite app_nil_r in Heq_nil1.
           now rewrite Heq_nil1 in Hneq_nil.
         enough (H : In (LogV i) (listVarInT ({{t3 | t4}})) -> In (LogV i) (listVarInT ({{t1 | {{t3 | t4}}}}))).
           now apply H; apply Hind.
         simpl; intro.
         apply in_app_iff.
         now right.
      -- apply in_or_app; left.
         now apply Hind.
    * intros s lt ?.
      simpl; rewrite app_nil_r.
      intro Hneq_nilS.
      enough (Hneq_nil : (ListDepthsInTerm (LogV i :: nil) t1) <> nil).
        apply in_or_app; left.
        now apply Hind.
      intro Habs.
      absurd (map S (depths (LogV i) t1) = nil); try now rewrite app_nil_r in Hneq_nilS.
      simpl in Habs.
      rewrite app_nil_r in Habs.
      now rewrite Habs.
    * intros _ Hneq_nilS.
      enough (Hneq_nil : (ListDepthsInTerm (LogV i :: nil) t1) <> nil).
        apply in_or_app; left.
        now apply Hind.
      intro Habs.
      absurd (map S (depths (LogV i) t1) = nil).
      -- simpl in Hneq_nilS.
         now rewrite app_nil_r in Hneq_nilS.
      -- simpl in Habs.
         rewrite app_nil_r in Habs.
         now rewrite Habs.
  + intros s lt _ Habs.
    now absurd ((nil : list nat) = nil); [assumption | reflexivity].
  + intros _ Habs.
    now absurd ((nil : list nat) = nil); [assumption | reflexivity].
Qed.

Lemma ListDepthsInTerm_in_incl v lv t :
  In v lv -> incl (ListDepthsInTerm (v :: nil) t) (ListDepthsInTerm lv t).
Proof.
elim lv; try contradiction.
intros v' lv' Hind Hin.
case (in_inv Hin) as [-> | ?].
- simpl; rewrite app_nil_r.
  apply incl_appl.
  now apply incl_refl.
- apply incl_tran with (m := (ListDepthsInTerm lv' t)); try now apply Hind.
  simpl; apply incl_appr.
  now apply incl_refl.
Qed.

Lemma ListDepthsNeq_cons_in_l v lv (c : constraint) :
  In v lv -> incl (ListDepthsNeq (v :: nil) c) (ListDepthsNeq lv c).
Proof.
intro Hin.
elim c; try now apply incl_nil_l.
intros pc ? ?.
case pc; try now intros.
intros t1 t2.
case t1; try now intros.
intro; apply incl_app_app; try assumption.
now apply ListDepthsInTerm_in_incl.
Qed.

Lemma ListDepthsNin_cons_in_l v lv (c : constraint) :
  In v lv -> incl (ListDepthsNin (v :: nil) c) (ListDepthsNin lv c).
Proof.
intro Hin.
elim c; try now apply incl_nil_l.
intros pc ? ?.
case pc; try now intros.
intros t1 t2.
case t2; try now intros.
intro; apply incl_app_app; try assumption.
now apply ListDepthsInTerm_in_incl.
Qed.

Lemma ListDepthsNeq_cons_l v lv (c : constraint) :
  incl (ListDepthsNeq (v :: lv) c) (ListDepthsNeq (v :: nil) c ++ ListDepthsNeq lv c).
Proof.
elim c; try now apply incl_nil_l.
intros pc c' ?.
case pc; try now intros.
intros t1 t2.
case t1; try now intros.
intro; apply incl_app.
- apply incl_app.
  + do 2 apply incl_appl.
    simpl; rewrite app_nil_r.
    now apply incl_refl.
  + apply incl_appr.
    apply incl_appl.
    now apply incl_refl.
- simpl; rewrite app_assoc_reverse.
  apply incl_appr.
  apply incl_tran with (m := (ListDepthsNeq (v :: nil) c' ++ ListDepthsNeq lv c'));
    try assumption.
  apply incl_app_app.
  + now apply incl_refl.
  + apply incl_appr.
    now apply incl_refl.
Qed.

Lemma ListDepthsNin_cons_l v lv (c : constraint) :
  incl (ListDepthsNin (v :: lv) c) (ListDepthsNin (v :: nil) c ++ ListDepthsNin lv c).
Proof.
elim c; try now apply incl_nil_l.
intros pc c' ?.
case pc; try now intros.
intros t1 t2.
case t2; try now intros.
intro; apply incl_app.
- apply incl_app.
  apply incl_appl.
  + apply incl_appl.
    simpl; rewrite app_nil_r.
    now apply incl_refl.
  + apply incl_appr.
    apply incl_appl.
    now apply incl_refl.
- simpl; rewrite app_assoc_reverse.
  apply incl_appr.
  apply incl_tran with (m := (ListDepthsNin (v :: nil) c' ++ ListDepthsNin lv c'));
    try assumption.
  apply incl_app_app.
  + now apply incl_refl.
  + apply incl_appr.
    now apply incl_refl.
Qed.

Lemma in_ListFindNiNeq n l :
  In n (ListFindNiNeq l) <-> exists v t, In (Var v \== t) l /\ depth_EmptySet t = n.
Proof.
split.
- elim l; try contradiction.
  intros pc c Hind.
  case pc.
  + intros t1 t2 Hin.
    destruct (Hind Hin) as [v [t [? ?]]].
    exists v; exists t.
    now split; [right | assumption].
  + intros t1 t2.
    case t1.
    * intros v Hin.
      case Hin as [? | Hin].
      -- exists v; exists t2.
         now split; [apply in_eq | assumption].
      -- destruct (Hind Hin) as [v' [t' [? ?]]].
         exists v'; exists t'.
         now split; [right | assumption].
    * intros t3 t4 Hin.
      destruct (Hind Hin) as [v [t [? ?]]].
      exists v; exists t.
      now split; [right | assumption].
    * intros s lt Hin.
      destruct (Hind Hin) as [v [t [? ?]]].
      exists v; exists t.
      now split; [right | assumption].
    * intros Hin.
      destruct (Hind Hin) as [v [t [? ?]]].
      exists v; exists t.
      now split; [right | assumption].
  + intros t1 t2 Hin.
    destruct (Hind Hin) as [v [t [? ?]]].
    exists v; exists t.
    now split; [right | assumption].
  + intros t1 t2 Hin.
    destruct (Hind Hin) as [v [t [? ?]]].
    exists v; exists t.
    now split; [right | assumption].
  + intros Hin.
    destruct (Hind Hin) as [v [t [? ?]]].
    exists v; exists t.
    now split; [right | assumption].
  + intros t' Hin.
    destruct (Hind Hin) as [v [t [? ?]]].
    exists v; exists t.
    now split; [right | assumption].
- elim l.
  + now intros [? [? [? ?]]].
  + intros pc c Hind.
    intros [v [t [Hin ?]]].
    case Hin.
    * intros ->.
      now left.
    * intro Hin'.
      revert Hin.
      case pc.
      -- intros; apply Hind.
         now exists v; exists t; split.
      -- intros t' ? ?.
         case t'.
         ++ intro; right.
            apply Hind.
            now exists v; exists t; split.
         ++ intros; apply Hind.
            now exists v; exists t; split.
         ++ intros; apply Hind.
            now exists v; exists t; split.
         ++ apply Hind.
            now exists v; exists t; split.
      -- intros; apply Hind.
         now exists v; exists t; split.
      -- intros; apply Hind.
         now exists v; exists t; split.
      -- intro; apply Hind.
         now exists v; exists t; split.
      -- intros; apply Hind.
         now exists v; exists t; split.
Qed.

Lemma in_ListFindNiNin n l :
  In n (ListFindNiNin l) <-> exists v t, In (t \:s Var v) l /\ depth_EmptySet t = n.
Proof.
split.
- elim l; try contradiction.
  intros pc c Hind.
  case pc.
  + intros t1 t2 Hin.
    destruct (Hind Hin) as [v [t [? ?]]].
    exists v; exists t.
    now split; [right | assumption].
  + intros t1 t2 Hin.
    destruct (Hind Hin) as [v [t [? ?]]].
    exists v; exists t.
    now split; [right | assumption].
  + intros t1 t2 Hin.
    destruct (Hind Hin) as [v [t [? ?]]].
    exists v; exists t.
    now split; [right | assumption].
  + intros t1 t2.
    case t2.
    * intros v Hin.
      case Hin as [? | Hin].
      -- exists v; exists t1.
         now split; [apply in_eq | assumption].
      -- destruct (Hind Hin) as [v' [t' [? ?]]].
         exists v'; exists t'.
         now split; [right | assumption].
    * intros t3 t4 Hin.
      destruct (Hind Hin) as [v [t [? ?]]].
      exists v; exists t.
      now split; [right | assumption].
    * intros s lt Hin.
      destruct (Hind Hin) as [v [t [? ?]]].
      exists v; exists t.
      now split; [right | assumption].
    * intros Hin.
      destruct (Hind Hin) as [v [t [? ?]]].
      exists v; exists t.
      now split; [right | assumption].
  + intros Hin.
    destruct (Hind Hin) as [v [t [? ?]]].
    exists v; exists t.
    now split; [right | assumption].
  + intros t' Hin.
    destruct (Hind Hin) as [v [t [? ?]]].
    exists v; exists t.
    now split; [right | assumption].
- elim l.
  + now intros [? [? [? ?]]].
  + intros pc c Hind.
    intros [v [t [Hin ?]]].
    case Hin.
    * intros ->.
      now left.
    * intro Hin'.
      revert Hin.
      case pc.
      -- intros; apply Hind.
         now exists v; exists t; split.
      -- intros; apply Hind.
         now exists v; exists t; split.
      -- intros; apply Hind.
         now exists v; exists t; split.
      -- intros ? t' ?.
         case t'.
         ++ intro; right.
            apply Hind.
            now exists v; exists t; split.
         ++ intros; apply Hind.
            now exists v; exists t; split.
         ++ intros; apply Hind.
            now exists v; exists t; split.
         ++ apply Hind.
            now exists v; exists t; split.
      -- intro; apply Hind.
         now exists v; exists t; split.
      -- intros; apply Hind.
         now exists v; exists t; split.
Qed.

Lemma incl_ListFindNiNeq l1 l2:
  incl l1 l2 -> incl (ListFindNiNeq l1) (ListFindNiNeq l2).
Proof.
intros Hincl n Hin.
assert (Hexists: exists v t, In (Var v \== t) l1 /\ depth_EmptySet t = n).
  now apply in_ListFindNiNeq.
destruct Hexists as [v [t [? ?]]].
apply in_ListFindNiNeq.
exists v; exists t.
split; try assumption.
now apply Hincl.
Qed.

Lemma incl_ListFindNiNin l1 l2:
  incl l1 l2 -> incl (ListFindNiNin l1) (ListFindNiNin l2).
Proof.
intros Hincl n Hin.
assert (Hexists: exists v t, In (t \:s Var v) l1 /\ depth_EmptySet t = n).
  now apply in_ListFindNiNin.
destruct Hexists as [v [t [? ?]]].
apply in_ListFindNiNin.
exists v; exists t.
split; try assumption.
now apply Hincl.
Qed.

Lemma incl_l_ListDepthsNeq c lv1 lv2 :
  incl lv1 lv2 -> incl (ListDepthsNeq lv1 c) (ListDepthsNeq lv2 c).
Proof.
elim lv1.
- intro.
  rewrite ListDepthsNeq_nil.
  now apply incl_nil_l.
- intros v lv Hind Hincl.
  destruct (incl_cons_inv Hincl).
  apply incl_tran with (m := (ListDepthsNeq (v :: nil) c ++ ListDepthsNeq lv c));
    try now apply ListDepthsNeq_cons_l.
  apply incl_app; [now apply ListDepthsNeq_cons_in_l | now apply Hind].
Qed.

Lemma incl_l_ListDepthsNin c lv1 lv2 :
  incl lv1 lv2 -> incl (ListDepthsNin lv1 c) (ListDepthsNin lv2 c).
Proof.
elim lv1.
- intro.
  rewrite ListDepthsNin_nil.
  now apply incl_nil_l.
- intros v lv Hind Hincl.
  destruct (incl_cons_inv Hincl).
  apply incl_tran with (m := (ListDepthsNin (v :: nil) c ++ ListDepthsNin lv c)).
    try now apply ListDepthsNin_cons_l.
  apply incl_app; [now apply ListDepthsNin_cons_in_l | now apply Hind].
Qed.

Lemma in_r_ListDepthsNeq v t lv c :
  In (Var v \== t) c -> incl (ListDepthsInTerm lv t) (ListDepthsNeq lv c).
Proof.
elim c; try contradiction.
intros pc c' Hind Hin.
case Hin as [-> | H]; try now apply incl_appl.
case pc.
- intros; now apply Hind.
- intros t' ?.
  case t'; intros; try now apply Hind.
  apply incl_appr.
  now apply Hind.
- intros; now apply Hind.
- intros; now apply Hind.
- now apply Hind.
- intro; now apply Hind.
Qed.

Lemma incl_r_ListDepthsNeq c1 c2 lv :
  incl c1 c2 -> incl (ListDepthsNeq lv c1) (ListDepthsNeq lv c2).
Proof.
elim c1.
- intro; now apply incl_nil_l.
- intros pc c Hind Hincl.
  destruct (incl_cons_inv Hincl) as [Hinpc Hinclc].
  revert Hinpc.
  case pc.
  + intros; now apply Hind.
  + intros t ?.
    case t; intros; try now apply Hind.
    apply incl_app; [now apply (in_r_ListDepthsNeq _ _ _ _ Hinpc) | now apply Hind].
  + intros; now apply Hind.
  + intros; now apply Hind.
  + intro; now apply Hind.
  + intros; now apply Hind.
Qed.

Lemma in_r_ListDepthsNin v t lv c :
  In (t \:s Var v) c -> incl (ListDepthsInTerm lv t) (ListDepthsNin lv c).
Proof.
elim c; try contradiction.
intros pc c' Hind Hin.
case Hin as [-> | H].
- now apply incl_appl.
- case pc.
  + intros; now apply Hind.
  + intros; now apply Hind.
  + intros; now apply Hind.
  + intros ? t'.
    case t'; intros; try now apply Hind.
    apply incl_appr.
    now apply Hind.
  + now apply Hind.
  + intro; now apply Hind.
Qed.

Lemma incl_r_ListDepthsNin c1 c2 lv :
  incl c1 c2 -> incl (ListDepthsNin lv c1) (ListDepthsNin lv c2).
Proof.
elim c1.
- intro; now apply incl_nil_l.
- intros pc c Hind Hincl.
  destruct (incl_cons_inv Hincl) as [Hinpc Hinclc].
  revert Hinpc.
  case pc.
  + intros; now apply Hind.
  + intros; now apply Hind.
  + intros; now apply Hind.
  + intros ? t.
    case t; intros; try now apply Hind.
    apply incl_app; [now apply (in_r_ListDepthsNin _ _ _ _ Hinpc) | now apply Hind].
  + intro; now apply Hind.
  + intros; now apply Hind.
Qed.

Lemma incl_ListDepthsNeq c1 c2 lv1 lv2:
  incl c1 c2 -> incl lv1 lv2 -> incl (ListDepthsNeq lv1 c1) (ListDepthsNeq lv2 c2).
Proof.
intros.
apply incl_tran with (m := (ListDepthsNeq lv1 c2)); [now apply incl_r_ListDepthsNeq | now apply incl_l_ListDepthsNeq].
Qed.

Lemma incl_ListDepthsNin c1 c2 lv1 lv2:
  incl c1 c2 -> incl lv1 lv2 -> incl (ListDepthsNin lv1 c1) (ListDepthsNin lv2 c2).
Proof.
intros.
apply incl_tran with (m := (ListDepthsNin lv1 c2)); [now apply incl_r_ListDepthsNin | now apply incl_l_ListDepthsNin].
Qed.

Lemma Max_ListFindNiNeq_inv pc (c: constraint):
  In pc c ->
    (list_max (ListFindNiNeq c)) = (list_max (ListFindNiNeq (pc :: (remove eq_primc_dec pc c)))).
Proof.
intro; apply leq_eqn.
- apply incl_listmax.
  apply incl_ListFindNiNeq.
  now apply incl_remove_r.
- apply incl_listmax.
  apply incl_ListFindNiNeq.
  now apply incl_remove_l.
Qed.

Lemma Max_ListFindNiNin_inv pc (c: constraint):
  In pc c ->
    (list_max (ListFindNiNin c)) = (list_max (ListFindNiNin (pc :: (remove eq_primc_dec pc c)))).
Proof.
intro; apply leq_eqn.
- apply incl_listmax.
  apply incl_ListFindNiNin.
  now apply incl_remove_r.
- apply incl_listmax.
  apply incl_ListFindNiNin.
  now apply incl_remove_l.
Qed.

Lemma Max_listVarInC_inv pc (c : constraint):
  In pc c ->
    (list_max (ListDepthsNeq (listVarInC c) c)) = (list_max (ListDepthsNeq (listVarInC (pc :: (remove eq_primc_dec pc c))) (pc :: (remove eq_primc_dec pc c)))).
Proof.
intro; apply leq_eqn.
- apply incl_listmax.
  apply incl_ListDepthsNeq.
  + now apply incl_remove_r.
  + apply incl_ListVarInC.
    now apply incl_remove_r.
- apply incl_listmax.
  apply incl_ListDepthsNeq.
  + now apply incl_remove_l.
  + apply incl_ListVarInC.
    now apply incl_remove_l.
Qed.

Lemma Max_ListDepthsNin_inv pc (c : constraint) :
  In pc c ->
    (list_max (ListDepthsNin (listVarInC c) c)) = (list_max (ListDepthsNin (listVarInC (pc :: (remove eq_primc_dec pc c))) (pc :: (remove eq_primc_dec pc c)))).
Proof.
intro; apply leq_eqn.
- apply incl_listmax.
  apply incl_ListDepthsNin.
  + now apply incl_remove_r.
  + apply incl_ListVarInC.
    now apply incl_remove_r.
- apply incl_listmax.
  apply incl_ListDepthsNin.
  + now apply incl_remove_l.
  + apply incl_ListVarInC.
    now apply incl_remove_l.
Qed.

Lemma depth_EmptySet_le t sigma :
  (depth_EmptySet t <= depth_EmptySet (applySubstitution sigma t)).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
       (depth_EmptySet t' <= depth_EmptySet (applySubstitution sigma t')))).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  absurd (sizet t' <= 0); try assumption.
  now apply sizet_gte_1.
- intros t'.
  case t'.
  + intros; now apply Nat.le_0_l.
  + intros t1 t2 Hsizet.
    destruct (sizet_SetC Hsizet).
    rewrite depth_EmptySet_SetC.
    rewrite applySub_SetC.
    rewrite depth_EmptySet_SetC.
    apply Nat.max_le_compat.
    * apply le_n_S.
      now apply Hind.
    * now apply Hind.
  + intros; now apply Nat.le_0_l.
  + intros; now apply Nat.le_0_l.
Qed.

Lemma depth_max_le t sigma :
  (depth_max t <= depth_max (applySubstitution sigma t)).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
       (depth_max t' <= depth_max (applySubstitution sigma t')))).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  absurd (sizet t' <= 0); try assumption.
  now apply sizet_gte_1.
- intros t'.
  case t'.
  + intros; now apply Nat.le_0_l.
  + intros t1 t2 Hsizet.
    destruct (sizet_SetC Hsizet).
    rewrite depth_max_SetC.
    rewrite applySub_SetC.
    rewrite depth_max_SetC.
    apply Nat.max_le_compat.
    * apply le_n_S.
      now apply Hind.
    * now apply Hind.
  + intros s lt.
    elim lt.
    * now intro; apply le_n.
    * intros t'' lt' Hind' Hsizet.
      simpl; apply le_n_S.
      apply Nat.max_le_compat.
      -- apply Hind.
         simpl in Hsizet.
         rewrite <- plus_Sn_m in Hsizet.
         apply le_S_n.
         now apply (le_add_l _ _ Hsizet).
      -- apply le_S_n.
         apply Hind'.
         apply le_trans with (m := sizet (OTerm s (t'' :: lt'))); try assumption.
         simpl; apply le_n_S.
         now apply le_plus_r.
  + intros; now apply Nat.le_0_l.
Qed.

Lemma depth_EmptySet_list_max_le sigma v t :
  (depths v t) <> nil ->
    (depth_EmptySet (applySubstitution sigma (Var v)) + list_max (depths v t)) 
      <= depth_EmptySet (applySubstitution sigma t).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
  (depths v t') <> nil ->
    (depth_EmptySet (applySubstitution sigma (Var v)) + list_max (depths v t')) 
      <= depth_EmptySet (applySubstitution sigma t'))).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  now absurd (sizet t' <= 0); [apply sizet_gte_1 | assumption].
- destruct v as [i].
  intros t'.
  case t'.
  + intros [j] _ Hdephs.
    assert (Heq : j = i).
      case (eq_nat_dec j i) as [? | Hneq]; try assumption.
      absurd ((nil : list nat) = nil); try reflexivity.
      assert (Hfalse : (j =? i) = false).
        now apply Nat.eqb_neq.
      simpl in Hdephs.
      now rewrite Hfalse in Hdephs.
    rewrite Heq.
    simpl; rewrite Nat.eqb_refl.
    now rewrite <- plus_n_O.
  + intros t1 t2 Hsizet Hneq_nil.
    destruct (sizet_SetC Hsizet) as [Hsizet1 Hsizet2].
    rewrite applySub_SetC.
    rewrite depth_EmptySet_SetC.
    revert Hneq_nil.
    revert Hsizet2.
    case t2.
    * intros [j] _ Hdepths.
      case (eq_nat_dec j i) as [Heq | Hneq].
      -- rewrite Heq.
         case (list_eq_dec eq_nat_dec (depths (LogV i) t1) nil) as [Heq_nil1 | Hneq_nil1].
         ++ assert (Heq0 : list_max (depths (LogV i) ({{t1 | \V i}})) = 0).
              simpl; rewrite Heq_nil1.
              rewrite Nat.eqb_refl.
              now rewrite list_max_app.
            rewrite Heq0.
            rewrite <- plus_n_O.
            now apply Nat.le_max_r.
         ++ assert (Heq_lm : list_max (depths (LogV i) ({{t1 | \V i}})) =
                           list_max (map S (depths (LogV i) t1))).
              simpl; rewrite Nat.eqb_refl.
              rewrite list_max_app.
              now rewrite Nat.max_0_r.
            rewrite Heq_lm.
            apply le_trans with (m := (S (depth_EmptySet (applySubstitution sigma t1))));
              try apply Nat.le_max_l.
            rewrite <- (S_listmax Hneq_nil1).
            rewrite Nat.add_succ_r.
            apply le_n_S.
            now apply Hind.
      -- assert (Hfalse : (j =? i) = false).
           now apply Nat.eqb_neq.
         assert (Hneq_nil1 : (depths (LogV i) t1) <> nil).
           intro Habs.
           revert Hdepths.
           simpl; rewrite Habs.
           now rewrite Hfalse.
         assert (Heq_lm : list_max (depths (LogV i) ({{t1 | \V j}})) = list_max (map S (depths (LogV i) t1))).
           simpl; rewrite Hfalse.
           now rewrite app_nil_r.
         rewrite Heq_lm.
         apply le_trans with (m := (S (depth_EmptySet (applySubstitution sigma t1))));
           try apply Nat.le_max_l.
         rewrite <- (S_listmax Hneq_nil1).
         rewrite Nat.add_succ_r.
         apply le_n_S.
         now apply Hind.
    * intros t3 t4 Hsizet2 Hneq_nil.
      case (list_eq_dec eq_nat_dec (depths (LogV i) t1) nil) as [Heq_nil1 | Hneq_nil1].
      -- assert (Heq_nil2 : depths (LogV i) ({{t3 | t4}}) <> nil).
           simpl in Hneq_nil.
           now rewrite Heq_nil1 in Hneq_nil.
         assert (Heq_lm : list_max (depths (LogV i) ({{t1 | {{t3 | t4}}}})) = list_max (depths (LogV i) ({{t3 | t4}}))).
           now simpl; rewrite Heq_nil1.
         rewrite Heq_lm.
         apply le_trans with (m := (depth_EmptySet (applySubstitution sigma ({{t3 | t4}}))));
           try apply Nat.le_max_r.
         now apply Hind.
      -- assert (Hdepths : (depths (LogV i) ({{t1 | {{t3 | t4}}}})) = (map S (depths (LogV i) t1)) ++ (depths (LogV i) ({{t3 | t4}}))).
           trivial.
         case (list_eq_dec eq_nat_dec (depths (LogV i) ({{t3 | t4}})) nil) as [Heq_nil2 | Hneq_nil2].
         ++ assert (Heq_lm : (depths (LogV i) ({{t1 | {{t3 | t4}}}})) = map S (depths (LogV i) t1)).
              rewrite Hdepths.
              rewrite Heq_nil2.
              now rewrite app_nil_r.
            rewrite Heq_lm.
            apply le_trans with (m := (S (depth_EmptySet (applySubstitution sigma t1))));
              try apply Nat.le_max_l.
            rewrite <- (S_listmax Hneq_nil1).
            rewrite Nat.add_succ_r.
            apply le_n_S.
            now apply Hind.
         ++ rewrite Hdepths.
            rewrite list_max_app.
            case (Nat.max_dec (list_max (map S (depths (LogV i) t1))) (list_max (depths (LogV i) ({{t3 | t4}})))) as [-> | ->].
            ** apply le_trans with (m := (S (depth_EmptySet (applySubstitution sigma t1))));
                 try apply Nat.le_max_l.
               rewrite <- (S_listmax Hneq_nil1).
               rewrite Nat.add_succ_r.
               apply le_n_S.
               now apply Hind.
            ** apply le_trans with (m := (depth_EmptySet (applySubstitution sigma ({{t3 | t4}}))));
                 try apply Nat.le_max_r.
               now apply Hind.
    * intros s lt ?.
      simpl; rewrite app_nil_r.
      intro Hneq_nilS.
      assert (Hneq_nil : (depths (LogV i) t1) <> nil).
        intro Habs.
        absurd (map S (depths (LogV i) t1) = nil); try assumption.
        now rewrite Habs.
      rewrite <- (S_listmax Hneq_nil).
      rewrite Nat.add_succ_r.
      apply le_n_S.
      now apply Hind.
    * intros _ Hneq_nilS.
      assert (Hneq_nil : (depths (LogV i) t1) <> nil).
        intro Habs.
        absurd (map S (depths (LogV i) t1) = nil); try assumption.
        now rewrite Habs.
      simpl; rewrite <- (S_listmax Hneq_nil).
      rewrite Nat.add_succ_r.
      apply le_n_S.
      now apply Hind.
  + intros s lt _ Habs.
    absurd ((nil : list nat) = nil); [assumption | reflexivity].
  + intros _ Habs.
    absurd ((nil : list nat) = nil); [assumption | reflexivity].
Qed.

Lemma occurCheck_depthsT v t :
  occurCheck v t -> (depthsT v t) <> nil.
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
        occurCheck v t' -> (depthsT v t') <> nil)).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  now absurd (sizet t' <= 0); [apply sizet_gte_1 | assumption].
- destruct v as [i].
  intro t'.
  case t'.
  + intros [j] _ Heq.
    inversion Heq.
    simpl; rewrite <- beq_nat_refl.
    intro Habs.
    apply in_nil with (a := 0).
    rewrite <- Habs.
    now apply in_eq.
  + intros t1 t2 Hsizet.
    destruct (sizet_SetC Hsizet) as [Hsizet1 Hsizet2].
    revert Hsizet2.
    case t2.
    * intros [j] ? HoC.
      case HoC as [HoC_t1 | HoC_i_j].
      -- simpl; intro Heq_nil.
         destruct (app_eq_nil _ _ Heq_nil) as [Heq_nil_map _].
         now absurd ((depthsT (LogV i) t1) = nil);
           [apply Hind | apply (map_eq_nil _ _ Heq_nil_map)].
      -- inversion HoC_i_j.
         simpl; rewrite <- beq_nat_refl.
         intro Heq_nil.
         destruct (app_eq_nil _ _ Heq_nil) as [_ Habs].
         apply in_nil with (a := 0).
         rewrite <- Habs.
         now apply in_eq.
    * intros t3 t4 Hsizet34 HoC.
      case HoC as [HoC_t1 | Hoc_t34]; simpl; intro Heq_nil;
         destruct (app_eq_nil _ _ Heq_nil) as [Heq_nil1 Heq_nil34].
      -- now absurd ((depthsT (LogV i) t1) = nil);
           [apply Hind | apply (map_eq_nil _ _ Heq_nil1)].
      -- now absurd ((depthsT (LogV i) ({{t3 | t4}})) = nil); [apply Hind | simpl].
    * intros s lt HsizeOT HoC.
      case HoC as [HoC_t1 | Hoc_OT].
      -- simpl; intro Heq_nil.
         destruct (app_eq_nil _ _ Heq_nil) as [Heq_nil1 _].
         now absurd ((depthsT (LogV i) t1) = nil);
           [apply Hind | apply (map_eq_nil _ _ Heq_nil1)].
      -- simpl; intro Heq_nil.
         destruct (app_eq_nil _ _ Heq_nil) as [_ Heq_nil2].
         absurd ((depthsT (LogV i) (OTerm s lt)) = nil); try assumption.
         now apply Hind.
    * intros _ HoC.
      case HoC as [HoC_t1 | ?]; try contradiction.
      intros Heq_nil_map.
      now absurd ((depthsT (LogV i) t1) = nil);
        [apply Hind | apply (map_eq_nil _ _ Heq_nil_map)].
  + intros s lt.
    elim lt; try contradiction.
    intros t'' lt' Hind' HsizeOT HoC.
    simpl; rewrite map_app.
    intro Heq_nil.
    destruct (app_eq_nil _ _ Heq_nil) as [Heq_nilt'' Heq_nilt'].
    case HoC as [HoC_t'' | HoC_lt'].
    * absurd ((depthsT (LogV i) t'') = nil); try now apply (map_eq_nil _ _ Heq_nilt'').
      apply Hind; try assumption.
      apply (sizet_OTerm HsizeOT).
      now apply in_eq.
    * absurd ((depthsT (LogV i) (OTerm s lt')) = nil); try assumption.
      apply Hind; try assumption.
      apply le_S_n.
      apply le_trans with (m := sizet (OTerm s (t'' :: lt'))); try assumption.
      simpl; apply le_n_S.
      rewrite plus_comm.
      rewrite S_eq.
      apply plus_le_compat; try apply le_n.
      now apply le_1_sizet.
  + contradiction.
Qed.

Lemma depths_occurCheck v t :
  (depths v t) <> nil -> occurCheck v t.
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
        (depths v t') <> nil -> occurCheck v t')).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  now absurd (sizet t' <= 0); [apply sizet_gte_1 | assumption].
- destruct v as [i].
  intro t'.
  case t'.
  + intros [j] _.
    simpl; case (eq_nat_dec j i) as [-> | Hneq]; try reflexivity.
    assert (Hf : (j =? i) = false).
      now apply Nat.eqb_neq.
    rewrite Hf.
    contradiction.
  + intros t1 t2 Hsizet.
    destruct (sizet_SetC Hsizet) as [Hsizet1 Hsizet2].
    revert Hsizet2.
    case t2.
    * intros [j] _ Hnnil.
      simpl; case (eq_nat_dec j i) as [-> | Hneq]; try now right.
      assert (Hf : (j =? i) = false).
        now apply Nat.eqb_neq.
      simpl in Hnnil; rewrite Hf in Hnnil; rewrite app_nil_r in Hnnil.
      left; apply Hind; try assumption.
      intro Hnil.
      rewrite Hnil in Hnnil.
      contradiction.
    * intros t3 t4 Hsizet34 Hnnil.
      assert (Hdepths : (depths (LogV i) ({{t1 | {{t3 | t4}}}})) = (map S (depths (LogV i) t1)) ++ (depths (LogV i) ({{t3 | t4}}))).
        trivial.
      case (list_eq_dec eq_nat_dec (depths (LogV i) ({{t3 | t4}})) nil) as [Heq_nil34 | Hneq_nil2].
      -- assert (Heq_lm : (depths (LogV i) ({{t1 | {{t3 | t4}}}})) = map S (depths (LogV i) t1)).
           rewrite Hdepths.
           rewrite Heq_nil34.
           now rewrite app_nil_r.
         rewrite Heq_lm in Hnnil.
         left; apply Hind; try assumption.
         intro Hnil.
         rewrite Hnil in Hnnil.
         contradiction.
      -- now right; apply Hind.
    * intros s lt _.
      simpl; rewrite app_nil_r; intro Hnnil.
      left; apply Hind; try assumption.
      intro Hnil.
      rewrite Hnil in Hnnil.
      contradiction.
    * simpl; intros _ Hnnil.
      left; apply Hind; try assumption.
      intro Hnil.
      rewrite Hnil in Hnnil.
      contradiction.
  + intros; contradiction.
  + contradiction.
Qed.

Lemma depthsT_occurCheck v t :
  (depthsT v t) <> nil -> occurCheck v t.
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
        (depthsT v t') <> nil -> occurCheck v t')).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  now absurd (sizet t' <= 0); [apply sizet_gte_1 | assumption].
- destruct v as [i].
  intro t'.
  case t'.
  + intros [j] _.
    case (eq_nat_dec j i) as [-> | Hneq]; try reflexivity.
    assert (Hf : (j =? i) = false).
      now apply Nat.eqb_neq.
    simpl; rewrite Hf.
    contradiction.
  + intros t1 t2 Hsizet.
    destruct (sizet_SetC Hsizet) as [Hsizet1 Hsizet2].
    revert Hsizet2.
    case t2.
    * intros [j] _ Hneq_nil.
      simpl; case (eq_nat_dec j i) as [-> | Hneq]; try now right.
      assert (Hf : (j =? i) = false).
        now apply Nat.eqb_neq.
      simpl in Hneq_nil; rewrite Hf in Hneq_nil; rewrite app_nil_r in Hneq_nil.
      left; apply Hind; try assumption.
      intro Heq_nil.
      rewrite Heq_nil in Hneq_nil.
      contradiction.
    * intros t3 t4 Hsizet34 Hneq_nil.
      assert (HdepthsT : (depthsT (LogV i) ({{t1 | {{t3 | t4}}}})) = (map S (depthsT (LogV i) t1)) ++ (depthsT (LogV i) ({{t3 | t4}}))).
        trivial.
      case (list_eq_dec eq_nat_dec (depthsT (LogV i) ({{t3 | t4}})) nil) as [Heq_nil34 | Hneq_nil2].
      -- assert (Heq_lm : (depthsT (LogV i) ({{t1 | {{t3 | t4}}}})) = map S (depthsT (LogV i) t1)).
           rewrite HdepthsT.
           rewrite Heq_nil34.
           now rewrite app_nil_r.
         rewrite Heq_lm in Hneq_nil.
         left; apply Hind; try assumption.
         intro Heq_nil.
         rewrite Heq_nil in Hneq_nil.
         contradiction.
      -- now right; apply Hind.
    * intros s lt HsizeOT Hneq_nil.
      assert (HdepthsT : (depthsT (LogV i) ({{t1 | OTerm s lt}})) = (map S (depthsT (LogV i) t1)) ++ (depthsT (LogV i) (OTerm s lt))).
        trivial.
      case (list_eq_dec eq_nat_dec (depthsT (LogV i) (OTerm s lt)) nil) as [Heq_nilOT | Hneq_nilOT].
      -- assert (Heq_lm : (depthsT (LogV i) ({{t1 | OTerm s lt}})) = map S (depthsT (LogV i) t1)).
           rewrite HdepthsT.
           rewrite Heq_nilOT.
           now rewrite app_nil_r.
         rewrite Heq_lm in Hneq_nil.
         left; apply Hind; try assumption.
         intro Heq_nil.
         rewrite Heq_nil in Hneq_nil.
         contradiction.
      -- now right; apply Hind.
    * simpl; intros _ Hneq_nil.
      left; apply Hind; try assumption.
      intro Heq_nil.
      rewrite Heq_nil in Hneq_nil.
      contradiction.
  + intros s lt.
    elim lt; try contradiction.
    intros t'' lt' Hind' HsizeOT Hneq_nil.
    case (list_eq_dec eq_nat_dec (depthsT (LogV i) t'') nil) as [Heq_nil1 | Hneq_nil1].
    * assert (Heq_nil2 : depthsT (LogV i) (OTerm s lt') <> nil).
      simpl in Hneq_nil.
      now rewrite Heq_nil1 in Hneq_nil.
      right; apply Hind'; try assumption.
      apply le_trans with (m := sizet (OTerm s (t'' :: lt'))); try assumption.
      apply le_n_S.
      now apply le_plus_r.
    * left; apply Hind; try assumption.
      apply (sizet_OTerm HsizeOT).
      now apply in_eq.
  + contradiction.
Qed.

Lemma depth_max_list_max_le sigma v t :
  occurCheck v t ->
    (depth_max (applySubstitution sigma (Var v)) + list_max (depthsT v t)) 
      <= depth_max (applySubstitution sigma t).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
  occurCheck v t' ->
    (depth_max (applySubstitution sigma (Var v)) + list_max (depthsT v t')) 
      <= depth_max (applySubstitution sigma t'))).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  now absurd (sizet t' <= 0); [apply sizet_gte_1 | assumption].
- destruct v as [i].
  intros t'.
  case t'.
  + intros [j] _ HoC.
    inversion HoC.
    simpl; rewrite Nat.eqb_refl.
    now rewrite <- plus_n_O.
  + intros t1 t2 Hsizet HoC.
    destruct (sizet_SetC Hsizet) as [Hsizet1 Hsizet2].
    rewrite applySub_SetC.
    rewrite depth_max_SetC.
    revert HoC.
    revert Hsizet2.
    case t2.
    * intros [j] _ HoC.
      case (eq_nat_dec j i) as [Heq | Hneq].
      -- rewrite Heq.
         case (list_eq_dec eq_nat_dec (depthsT (LogV i) t1) nil) as [Heq_nil1 | Hneq_nil1].
         ++ assert (Heq0 : list_max (depthsT (LogV i) ({{t1 | \V i}})) = 0).
              simpl; rewrite Heq_nil1.
              rewrite Nat.eqb_refl.
              now rewrite list_max_app.
            rewrite Heq0.
            rewrite <- plus_n_O.
            now apply Nat.le_max_r.
         ++ assert (Heq_lm : list_max (depthsT (LogV i) ({{t1 | \V i}})) =
                           list_max (map S (depthsT (LogV i) t1))).
              simpl; rewrite Nat.eqb_refl.
              rewrite list_max_app.
              now rewrite Nat.max_0_r.
            rewrite Heq_lm.
            apply le_trans with (m := (S (depth_max (applySubstitution sigma t1))));
              try apply Nat.le_max_l.
            rewrite <- (S_listmax Hneq_nil1).
            rewrite Nat.add_succ_r.
            apply le_n_S.
            apply Hind; try assumption.
            now apply depthsT_occurCheck.
      -- assert (Hfalse : (j =? i) = false).
           now apply Nat.eqb_neq.
         assert (Hneq_nil1 : (depthsT (LogV i) t1) <> nil).
           apply occurCheck_depthsT.
           case HoC; try trivial.
           intro H; revert Hneq.
           now inversion H.
         assert (Heq_lm : list_max (depthsT (LogV i) ({{t1 | \V j}})) = list_max (map S (depthsT (LogV i) t1))).
           simpl; rewrite Hfalse.
           now rewrite app_nil_r.
         rewrite Heq_lm.
         apply le_trans with (m := (S (depth_max (applySubstitution sigma t1))));
           try apply Nat.le_max_l.
         rewrite <- (S_listmax Hneq_nil1).
         rewrite Nat.add_succ_r.
         apply le_n_S.
         apply Hind; try assumption.
         now apply depthsT_occurCheck.
    * intros t3 t4 Hsizet2 Hoc.
      assert (Hneq_nil : (depthsT (LogV i) ({{t1 | {{t3 | t4}}}})) <> nil).
        now apply occurCheck_depthsT.
      case (list_eq_dec eq_nat_dec (depthsT (LogV i) t1) nil) as [Heq_nil1 | Hneq_nil1].
      -- assert (Heq_nil2 : depthsT (LogV i) ({{t3 | t4}}) <> nil).
           simpl in Hneq_nil.
           now rewrite Heq_nil1 in Hneq_nil.
         assert (Heq_lm : list_max (depthsT (LogV i) ({{t1 | {{t3 | t4}}}})) = list_max (depthsT (LogV i) ({{t3 | t4}}))).
           now simpl; rewrite Heq_nil1.
         rewrite Heq_lm.
         apply le_trans with (m := (depth_max (applySubstitution sigma ({{t3 | t4}}))));
           try apply Nat.le_max_r.
         apply Hind; try assumption.
         now apply depthsT_occurCheck.
      -- assert (HdepthsT : (depthsT (LogV i) ({{t1 | {{t3 | t4}}}})) = (map S (depthsT (LogV i) t1)) ++ (depthsT (LogV i) ({{t3 | t4}}))).
           trivial.
         case (list_eq_dec eq_nat_dec (depthsT (LogV i) ({{t3 | t4}})) nil) as [Heq_nil2 | Hneq_nil2].
         ++ assert (Heq_lm : (depthsT (LogV i) ({{t1 | {{t3 | t4}}}})) = map S (depthsT (LogV i) t1)).
              rewrite HdepthsT.
              rewrite Heq_nil2.
              now rewrite app_nil_r.
            rewrite Heq_lm.
            apply le_trans with (m := (S (depth_max (applySubstitution sigma t1))));
              try apply Nat.le_max_l.
            rewrite <- (S_listmax Hneq_nil1).
            rewrite Nat.add_succ_r.
            apply le_n_S.
            apply Hind; try assumption.
            now apply depthsT_occurCheck.
         ++ rewrite HdepthsT.
            rewrite list_max_app.
            case (Nat.max_dec (list_max (map S (depthsT (LogV i) t1))) (list_max (depthsT (LogV i) ({{t3 | t4}})))) as [-> | ->].
            ** apply le_trans with (m := (S (depth_max (applySubstitution sigma t1))));
                 try apply Nat.le_max_l.
               rewrite <- (S_listmax Hneq_nil1).
               rewrite Nat.add_succ_r.
               apply le_n_S.
               apply Hind; try assumption.
               now apply depthsT_occurCheck.
            ** apply le_trans with (m := (depth_max (applySubstitution sigma ({{t3 | t4}}))));
                 try apply Nat.le_max_r.
               apply Hind; try assumption.
               now apply depthsT_occurCheck.
    * intros s lt HsizetOT HoC.
      assert (Hneq_nil : (depthsT (LogV i) ({{t1 | OTerm s lt}})) <> nil).
        now apply occurCheck_depthsT.
      case (list_eq_dec eq_nat_dec (depthsT (LogV i) t1) nil) as [Heq_nil1 | Hneq_nil1].
      -- assert (Heq_nil2 : depthsT (LogV i) (OTerm s lt) <> nil).
           simpl in Hneq_nil.
           now rewrite Heq_nil1 in Hneq_nil.
         assert (Heq_lm : list_max (depthsT (LogV i) ({{t1 | OTerm s lt}})) = list_max (depthsT (LogV i) (OTerm s lt))).
           simpl; now rewrite Heq_nil1.
         rewrite Heq_lm.
         apply le_trans with (m := (depth_max (applySubstitution sigma (OTerm s lt))));
           try apply Nat.le_max_r.
         apply Hind; try assumption.
         now apply depthsT_occurCheck.
     -- assert (HdepthsT : (depthsT (LogV i) ({{t1 | OTerm s lt}})) = (map S (depthsT (LogV i) t1)) ++ (depthsT (LogV i) (OTerm s lt))).
          trivial.
        case (list_eq_dec eq_nat_dec (depthsT (LogV i) (OTerm s lt)) nil) as [Heq_nil2 | Hneq_nil2].
        ++ assert (Heq_lm : (depthsT (LogV i) ({{t1 | OTerm s lt}})) = map S (depthsT (LogV i) t1)).
             rewrite HdepthsT.
             rewrite Heq_nil2.
             now rewrite app_nil_r.
           rewrite Heq_lm.
           apply le_trans with (m := (S (depth_max (applySubstitution sigma t1))));
             try apply Nat.le_max_l.
           rewrite <- (S_listmax Hneq_nil1).
           rewrite Nat.add_succ_r.
           apply le_n_S.
           apply Hind; try assumption.
           now apply depthsT_occurCheck.
        ++ rewrite HdepthsT.
           rewrite list_max_app.
           case (Nat.max_dec (list_max (map S (depthsT (LogV i) t1))) (list_max (depthsT (LogV i) (OTerm s lt)))) as [-> | ->].
           ** apply le_trans with (m := (S (depth_max (applySubstitution sigma t1))));
                try apply Nat.le_max_l.
              rewrite <- (S_listmax Hneq_nil1).
              rewrite Nat.add_succ_r.
              apply le_n_S.
              apply Hind; try assumption.
              now apply depthsT_occurCheck.
           ** apply le_trans with (m := (depth_max (applySubstitution sigma (OTerm s lt))));
                try apply Nat.le_max_r.
              apply Hind; try assumption.
              now apply depthsT_occurCheck.
    * intros _ HoC.
      case HoC as [HoC_t1 | ?]; try contradiction.
      assert (Hneq_nil : (depthsT (LogV i) t1) <> nil).
        now apply occurCheck_depthsT.
      simpl; rewrite <- (S_listmax Hneq_nil).
      rewrite Nat.add_succ_r.
      apply le_n_S.
      now apply Hind.
  + intros s lt.
    elim lt; try contradiction.
    intros t'' lt' Hind' HsizeOT HoC.
    assert (Hneq_nil : (depthsT (LogV i) (OTerm s (t'' :: lt'))) <> nil).
      now apply occurCheck_depthsT.
    assert (HsizeOT' : sizet (OTerm s lt') <= n).
      apply le_S_n.
      apply le_trans with (m := sizet (OTerm s (t'' :: lt'))); try assumption.
      simpl; apply le_n_S.
      rewrite S_eq.
      rewrite plus_comm.
      apply plus_le_compat; try apply le_n.
      now apply le_1_sizet.
    case (list_eq_dec eq_nat_dec (depthsT (LogV i) t'') nil) as [Heq_nil1 | Hneq_nil1].
    * assert (Heq_nil2 : depthsT (LogV i) (OTerm s lt') <> nil).
        simpl in Hneq_nil.
        now rewrite Heq_nil1 in Hneq_nil.
      assert (Heq_lm : list_max (depthsT (LogV i) (OTerm s (t'' :: lt'))) = list_max (depthsT (LogV i) (OTerm s lt'))).
        now simpl; rewrite Heq_nil1.
      rewrite Heq_lm.
      apply le_trans with (m := (depth_max (applySubstitution sigma (OTerm s lt')))).
      -- apply Hind; try assumption.
         now apply depthsT_occurCheck.
      -- apply le_n_S.
         now apply Nat.le_max_r.
    * assert (HdepthsT : (depthsT (LogV i) (OTerm s (t'' :: lt'))) = (map S (depthsT (LogV i) t'')) ++ (depthsT (LogV i) (OTerm s lt'))).
        now simpl; rewrite map_app.
      assert (Hsizet'' : sizet t'' <= n).
        apply (sizet_OTerm HsizeOT).
        now apply in_eq.
      case (list_eq_dec eq_nat_dec (depthsT (LogV i) (OTerm s lt')) nil) as [Heq_nil2 | Hneq_nil2].
      -- assert (Heq_lm : (depthsT (LogV i) (OTerm s (t'' :: lt'))) = map S (depthsT (LogV i) t'')).
           rewrite HdepthsT.
           rewrite Heq_nil2.
           now rewrite app_nil_r.
         rewrite Heq_lm.
         apply le_trans with (m := (S (depth_max (applySubstitution sigma t'')))).
         ++ rewrite <- (S_listmax Hneq_nil1).
            rewrite Nat.add_succ_r.
            apply le_n_S.
            apply Hind; try assumption.
            now apply depthsT_occurCheck.
         ++ apply le_n_S.
            now apply Nat.le_max_l.
      -- rewrite HdepthsT.
         rewrite list_max_app.
         case (Nat.max_dec (list_max (map S (depthsT (LogV i) t''))) (list_max (depthsT (LogV i) (OTerm s lt')))) as [-> | ->].
         ++ apply le_trans with (m := (S (depth_max (applySubstitution sigma t'')))).
            ** rewrite <- (S_listmax Hneq_nil1).
               rewrite Nat.add_succ_r.
               apply le_n_S.
               apply Hind; try assumption.
               now apply depthsT_occurCheck.
            ** apply le_n_S.
               now apply Nat.le_max_l.
         ++ apply le_trans with (m := (depth_max (applySubstitution sigma (OTerm s lt')))).
            ** apply Hind; try assumption.
               now apply depthsT_occurCheck.
            ** apply le_n_S.
               now apply Nat.le_max_r.
  + intros; contradiction.
Qed.

Lemma depth_EmptySet_lt_exists t sigma :
  (depth_EmptySet t < depth_EmptySet (applySubstitution sigma t)) ->
    (exists v, (ListDepthsInTerm (v :: nil) t) <> nil /\ depth_EmptySet (applySubstitution sigma t) =
      depth_EmptySet (applySubstitution sigma (Var v)) + list_max (ListDepthsInTerm (v :: nil) t)).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
  (depth_EmptySet t' < depth_EmptySet (applySubstitution sigma t')) ->
    (exists v, (ListDepthsInTerm (v :: nil) t') <> nil /\ depth_EmptySet (applySubstitution sigma t') =
      depth_EmptySet (applySubstitution sigma (Var v)) + list_max (ListDepthsInTerm (v :: nil) t')))).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  now absurd (sizet t' <= 0); [apply sizet_gte_1 | assumption].
- intros t'.
  case t'.
  + intros [m] _ _.
    exists (LogV m).
    split.
    * simpl; rewrite Nat.eqb_refl.
      rewrite app_nil_r.
      apply hd_error_some_nil with (a := 0).
      now apply hd_error_cons.
    * enough (Heq : list_max (ListDepthsInTerm (LogV m :: nil) (\V m)) = 0).
        rewrite Heq.
        now rewrite <- plus_n_O.
      now simpl; rewrite Nat.eqb_refl.
  + intros t1 t2 Hsizet Hd_lt.
    destruct (sizet_SetC Hsizet) as [Hsizet1 Hsizet2].
    set (d1 := (S (depth_EmptySet (applySubstitution sigma t1)))).
    set (d2 := (depth_EmptySet (applySubstitution sigma t2))).
    case (Nat.max_dec d1 d2) as [Hmax_eq | Hmax_eq].
    * assert (Hd_lt1 : depth_EmptySet t1 < depth_EmptySet (applySubstitution sigma t1)).
        rewrite applySub_SetC in Hd_lt.
        do 2 rewrite depth_EmptySet_SetC in Hd_lt.
        unfold d1 in Hmax_eq; unfold d2 in Hmax_eq.
        rewrite Hmax_eq in Hd_lt.
        apply lt_S_n.
        enough (H : (S (depth_EmptySet t1)) < S (depth_EmptySet (applySubstitution sigma t1))
                   /\ (depth_EmptySet t2) < S (depth_EmptySet (applySubstitution sigma t1))).
          now destruct H.
        now apply Nat.max_lub_lt_iff.
      destruct (Hind _ Hsizet1 Hd_lt1) as [v [Hneq_nil Heq]].
      exists v.
      simpl in Hneq_nil.
      rewrite app_nil_r in Hneq_nil.
      rewrite applySub_SetC.
      rewrite depth_EmptySet_SetC.
      split.
      -- assert (Hneq_nilS : (map S (depths v t1)) <> nil).
           intro Habs.
           now absurd (depths v t1 = nil); [assumption | destruct (map_eq_nil _ _ Habs)].
         simpl; case t2.
         ++ intros ? Habs.
            rewrite app_nil_r in Habs.
            now absurd (map S (depths v t1) = nil); [assumption | destruct (app_eq_nil _ _ Habs)].
         ++ intros ? ? Habs.
            rewrite app_nil_r in Habs.
            now absurd (map S (depths v t1) = nil); [assumption | destruct (app_eq_nil _ _ Habs)].
         ++ intros ? ? Habs.
            rewrite app_nil_r in Habs.
            now absurd (map S (depths v t1) = nil); [assumption | destruct (app_eq_nil _ _ Habs)].
         ++ now rewrite app_nil_r.
      -- unfold d1 in Hmax_eq; unfold d2 in Hmax_eq.
         case (list_eq_dec eq_nat_dec (depths v t2) nil) as [Heq_nil2 | Hneq_nil2].
         ++ rewrite Hmax_eq.
            rewrite (list_max_ListDepthsInTerm_SetC).
            assert (H : list_max (ListDepthsInTerm (v :: nil) t2) = 0).
              simpl; rewrite app_nil_r.
              now rewrite Heq_nil2.
            rewrite H.
            rewrite Nat.max_0_r.
            simpl; rewrite app_nil_r.
            rewrite <- (S_listmax Hneq_nil).
            rewrite Nat.add_succ_r.
            apply eq_S.
            rewrite Heq.
            now simpl; rewrite app_nil_r.
         ++ assert (Haux : (depth_EmptySet (applySubstitution sigma t2)) <=
                            S (depth_EmptySet (applySubstitution sigma t1))).
              apply Nat.max_lub_r with (n := d1).
              now rewrite <- Hmax_eq.
            rewrite Heq in Haux.
            rewrite S_eq in Haux.
            rewrite Hmax_eq.
            rewrite Heq.
            rewrite S_eq.
            rewrite (list_max_ListDepthsInTerm_SetC).
            rewrite plus_assoc_reverse.
            apply Nat.add_cancel_l.
            rewrite <- S_eq.
            apply eq_sym.
            simpl; do 2 rewrite app_nil_r.
            rewrite (S_listmax Hneq_nil).
            apply Nat.max_l.
            apply Nat.add_le_mono_l with (p := depth_EmptySet (applySubstitution sigma (Var v))).
            rewrite <- (S_listmax Hneq_nil).
            rewrite S_eq.
            rewrite <- plus_assoc_reverse.
            simpl in Haux.
            rewrite app_nil_r in Haux.
            apply Nat.le_trans with (m := depth_EmptySet (applySubstitution sigma t2)); try assumption.
            now apply depth_EmptySet_list_max_le.
    * assert (Hd_lt2 : depth_EmptySet t2 < depth_EmptySet (applySubstitution sigma t2)).
        rewrite applySub_SetC in Hd_lt.
        do 2 rewrite depth_EmptySet_SetC in Hd_lt.
        unfold d1 in Hmax_eq; unfold d2 in Hmax_eq.
        rewrite Hmax_eq in Hd_lt.
        enough (H : (S (depth_EmptySet t1)) < (depth_EmptySet (applySubstitution sigma t2))
                    /\ (depth_EmptySet t2) < (depth_EmptySet (applySubstitution sigma t2))).
          now destruct H.
        now apply Nat.max_lub_lt_iff.
      destruct (Hind _ Hsizet2 Hd_lt2) as [v [Hneq_nil Heq]].
      exists v.
      rewrite applySub_SetC.
      rewrite depth_EmptySet_SetC.
      split.
      -- revert Hneq_nil.
         simpl; do 2 rewrite app_nil_r.
         case t2.
         ++ intros u Hneq_nil Habs.
            now absurd ((depths v (Var u)) = nil); [assumption | destruct (app_eq_nil _ _ Habs)].
         ++ intros t3 t4 Hneq_nil Habs.
            now absurd ((depths v ({{t3 | t4}})) = nil); [assumption | destruct (app_eq_nil _ _ Habs)].
         ++ intros s l Hneq_nil Habs.
            now absurd ((depths v (OTerm s l)) = nil); [assumption | destruct (app_eq_nil _ _ Habs)].
         ++ intro.
            absurd ((nil : list nat) = nil); [assumption | reflexivity].
      -- unfold d1 in Hmax_eq; unfold d2 in Hmax_eq.
         case (list_eq_dec eq_nat_dec (depths v t1) nil) as [Heq_nil1 | Hneq_nil1].
         ++ rewrite Hmax_eq.
            rewrite (list_max_ListDepthsInTerm_SetC).
            enough (H : list_max (map S (ListDepthsInTerm (v :: nil) t1)) = 0).
              now rewrite H.
            simpl; rewrite app_nil_r.
            now rewrite Heq_nil1.
         ++ assert (Haux : (S (depth_EmptySet (applySubstitution sigma t1))) <=
                        depth_EmptySet (applySubstitution sigma t2)).
              apply Nat.max_lub_l with (m := d2).
              now rewrite <- Hmax_eq.
            rewrite Heq in Haux.
            rewrite S_eq in Haux.
            rewrite Hmax_eq.
            rewrite Heq.
            rewrite (list_max_ListDepthsInTerm_SetC).
            apply Nat.add_cancel_l.
            apply eq_sym.
            simpl; do 2 rewrite app_nil_r.
            rewrite Nat.max_r; try reflexivity.
            apply Nat.add_le_mono_l with (p := depth_EmptySet (applySubstitution sigma (Var v))).
            simpl in Haux.
            rewrite app_nil_r in Haux.
            apply Nat.le_trans with (m := depth_EmptySet (applySubstitution sigma t1) + 1); try assumption.
            apply Nat.le_trans with (m := depth_EmptySet (applySubstitution sigma (Var v)) + list_max (depths v t1) +1).
            ** rewrite <- (S_listmax Hneq_nil1).
               rewrite S_eq.
               rewrite plus_assoc_reverse.
               now apply le_n.
            ** apply plus_le_compat_r.
               now apply depth_EmptySet_list_max_le.
  + intros ? ? _ ?.
    now absurd (0 < 0); [apply Nat.lt_irrefl | assumption].
  + intros _ ?.
    now absurd (0 < 0); [apply Nat.lt_irrefl | assumption].
Qed.

Lemma listElements_depth_EmptySet t1 t2 :
  (In t1 (listElements t2)) -> ((depth_EmptySet t1) < (depth_EmptySet t2)).
Proof.
set (P := fun (n : nat) => (forall t, ((sizet t) <= n) -> In t1 (listElements t) -> depth_EmptySet t1 < depth_EmptySet t)).
enough (H : (forall n, (P n))).
  apply (H (sizet t2)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t ? _.
  absurd (sizet t <= 0); try assumption.
  now apply sizet_gte_1.
- intros t.
  case t.
  + intros; contradiction.
  + intros t3 t4 Hsizet HIn.
    case HIn as [-> | HIn].
    * now apply depth_EmptySet_lt.
    * assert (Hlt : depth_EmptySet t1 < depth_EmptySet t4).
        apply Hind; try assumption.
        now destruct (sizet_SetC Hsizet).
      assert (Hexists : exists m, depth_EmptySet t4 = S m).
        exists (Init.Nat.pred (depth_EmptySet t4)).
        now apply S_pred with (m := depth_EmptySet t1).
      destruct Hexists as [m Heq].
      simpl; rewrite Heq.
      apply Nat.lt_le_trans with (m := S m); try now rewrite <- Heq.
      apply le_n_S.
      now apply Nat.le_max_r.
  + intros; contradiction.
  + intros; contradiction.
Qed.

Lemma listElements_depth_max t1 t2 :
  (In t1 (listElements t2)) -> ((depth_max t1) < (depth_max t2)).
Proof.
set (P := fun (n : nat) => (forall t, ((sizet t) <= n) -> In t1 (listElements t) -> depth_max t1 < depth_max t)).
enough (H : (forall n, (P n))).
  apply (H (sizet t2)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t ? _.
  absurd (sizet t <= 0); try assumption.
  now apply sizet_gte_1.
- intros t.
  case t.
  + intros; contradiction.
  + intros t3 t4 Hsizet HIn.
    case HIn as [-> | HIn].
    * now apply depth_max_lt.
    * assert (Hlt : depth_max t1 < depth_max t4).
        apply Hind; try assumption.
        now destruct (sizet_SetC Hsizet).
      assert (Hexists : exists m, depth_max t4 = S m).
        exists (Init.Nat.pred (depth_max t4)).
        now apply S_pred with (m := depth_max t1).
      destruct Hexists as [m Heq].
      simpl; rewrite Heq.
      apply Nat.lt_le_trans with (m := S m); try now rewrite <- Heq.
      apply le_n_S.
      now apply Nat.le_max_r.
  + intros; contradiction.
  + intros; contradiction.
Qed.

