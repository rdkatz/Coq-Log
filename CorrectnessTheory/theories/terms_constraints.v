(*****************************************************
Catherine Dubois - Sulyvan Weppe                      
ENSIIE - Samovar -                                    
2016-2018                                             
                                                      
Modified by Maximiliano Cristia and Ricardo David Katz
2026                                                  
*****************************************************)

Set Implicit Arguments.

Require Import Arith List Decidable.

Require Import preliminaries.

(*************************************************)
(*                symbol and variable            *)
(*************************************************)

Definition index_set := nat.
Inductive log_symbol : Set := |LogS : index_set -> log_symbol.
Inductive log_variable : Set := |LogV : index_set -> log_variable.

Lemma eq_symbol_dec :
  forall s1 s2 : log_symbol, {s1 = s2} + {s1 <> s2}.
Proof.
decide equality; apply eq_nat_dec.
Qed.

Lemma eq_variable_dec :
  forall v1 v2 : log_variable, {v1 = v2} + {v1 <> v2}.
Proof.
decide equality; apply eq_nat_dec.
Qed.

(*******************************************)
(*                Term                     *)
(*******************************************)

Inductive term : Set :=
  | Var : log_variable -> term
  | SetC : term -> term -> term
  | OTerm : log_symbol -> list term -> term
  | EmptySet : term.

Definition Const s := OTerm s nil.

Notation "{{ x | r }}" := (SetC x r) (at level 80).
Notation "\V i" := (Var (LogV i)) (at level 80).
Notation "\S i" := (LogS i) (at level 80).
Notation "\C i" := (Const (LogS i)) (at level 80).

Lemma eq_const_dec :
  forall (s1 s2 : log_symbol), {(Const s1) = (Const s2)} + {(Const s1) <> (Const s2)}.
Proof.
intros s1 s2.
case (eq_symbol_dec s1 s2).
- intros ->; now left.
- intro; right; intro S_eq; inversion S_eq; contradiction.
Qed.

Fixpoint sizet (t : term) : nat :=
  match t with
  | Var _ => 1
  | SetC t1 t2 => 1 + (sizet t1) + (sizet t2)
  | OTerm _ l =>
      let size_list :=
        (fix size_list (l : list term) {struct l} : nat :=
           match l with
           | nil => 0
           | t :: lt => sizet t + size_list lt
           end) in
       1 + size_list l
  | EmptySet => 1
  end.

Lemma sizet_gte_1 t :
   ~ (sizet t <= 0).
Proof.
case t; intros; simpl; apply lt_not_le; apply neq_0_lt; apply O_S.
Qed.

Lemma le_1_sizet t :
  1 <= sizet t.
Proof.
case t; intros.
- apply le_n.
- apply le_n_S; apply le_0_n.
- apply le_n_S; apply le_0_n.
- apply le_n.
Qed.

Lemma sizet_OTerm s lt n :
  sizet (OTerm s lt) <= S n ->
    (forall t, In t lt -> (sizet t) <= n).
Proof.
elim lt; try contradiction.
intros t lt' Hind Hleq t' Hin.
simpl in Hleq.
case Hin as [-> | Hin].
- rewrite <- plus_Sn_m in Hleq.
  apply le_S_n.
  now apply (le_add_l _ _ Hleq).
- apply Hind; try assumption.
  rewrite plus_n_Sm in Hleq.
  now apply (le_add_r _ _ Hleq).
Qed.

Lemma sizet_SetC t1 t2 n :
  sizet (SetC t1 t2) <= S n ->
    (sizet t1 <= n) /\ (sizet t2 <= n).
Proof.
intro Hsizet.
simpl in Hsizet.
split; apply le_S_n.
- rewrite <- plus_Sn_m in Hsizet.
  now apply (le_add_l _ _ Hsizet).
- rewrite plus_n_Sm in Hsizet.
  now apply (le_add_r _ _ Hsizet).
Qed.

Lemma OTerm_eq_iff s1 s2 lt1 lt2 :
   (OTerm s1 lt1 = OTerm s2 lt2) <-> ((s1 = s2) /\ (lt1 = lt2)).
Proof.
split; intro H.
- inversion H.
  auto.
- destruct H as [-> ->].
  reflexivity.
Qed.

Lemma eq_term_dec :
  forall (t1 t2 : term), {t1 = t2} + {t1 <> t2}.
Proof.
Ltac intros_right := intros; right.
intros t1' t2'.
set (P := fun (n : nat) => (forall t1 t2, (((sizet t1) + (sizet t2)) <= n) -> ({t1 = t2} + {t1 <> t2}))).
enough (H : (forall n, (P n))).
  apply (H (sizet t1' + sizet t2')).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t1 t2 Hsizet_plus.
  absurd (sizet t1 <= 0); try now apply sizet_gte_1.
  now apply (le_add_l _ _ (Hsizet_plus)).
- intros t1 t2.
  case t1.
  + intro v1; simpl.
    case t2; try now intros_right.
    intros v2 ?.
    case (eq_variable_dec v1 v2).
    * intros ->; now left.
    * intro; right; unfold not; intros V_eq; inversion V_eq; contradiction.
  + intros t3 t4; simpl.
    case t2; try now intros_right.
    intros t5 t6; simpl; intro Hsize.
    assert ((sizet t3 + sizet t4 + (sizet t5 + sizet t6)) <= n).
      apply le_Sn_le; rewrite plus_n_Sm; apply le_S_n; assumption.
    assert (Ht3t5: ({t3 = t5} + {t3 <> t5})).
      apply Hind.
      apply (le_add_r (sizet t4)).
      rewrite Nat.add_assoc.
      apply (le_add_l _ (sizet t6)).
      assert (Hsumeq: (sizet t3 + sizet t4 + (sizet t5 + sizet t6))= (sizet t4 + sizet t3 + sizet t5 + sizet t6)).
        ring.
      rewrite <- Hsumeq; assumption.
    assert (Ht4t6: ({t4 = t6} + {t4 <> t6})).
      apply Hind.
      apply (le_add_r (sizet t3)).
      rewrite Nat.add_assoc.
      apply (le_add_l _ (sizet t5)).
      assert (Hsumeq: (sizet t3 + sizet t4 + (sizet t5 + sizet t6))= (sizet t3 + sizet t4 + sizet t6 + sizet t5)).
        ring.
      rewrite <- Hsumeq; assumption.
    case Ht3t5 as [-> | ?].
    * case Ht4t6 as [-> | ?]; try now left.
      right.
      now intro Heq; inversion Heq.
    * right.
      now intro Heq; inversion Heq.
  + intros s lt.
    case t2; try now intros_right.
    intros s' lt'.
    elim lt.
    * now elim lt'; intros; [apply eq_const_dec | right].
    * elim lt'.
      -- intros; now right.
      -- intros a l _ a' l' _ Hsizet.
         case s; intro i.
         case s'; intro i'.
         case (eq_nat_dec i i') as [<- | ?].
         ++ assert (Heq_dec : ({a' = a} + {a' <> a})).
              apply Hind; apply le_S_n; rewrite <- plus_Sn_m.
              apply Nat.le_trans with (m := sizet (OTerm (\S i) (a' :: l')) + sizet (OTerm (\S i) (a :: l))); try assumption.
              now apply plus_le_compat; simpl; [apply le_n_S | apply le_S]; apply le_plus_l.
            case Heq_dec as [-> |  ].
            ** assert (eq_OTerm_dec : ({OTerm (\S i) l' = OTerm (\S i) l} + {OTerm (\S i) l' <> OTerm (\S i) l})).
                 apply Hind; apply le_S_n; rewrite <- plus_Sn_m.
                 apply Nat.le_trans with (m := sizet (OTerm s (a :: l')) + sizet (OTerm s' (a :: l))); try assumption.
                 now apply plus_le_compat; simpl; [apply le_n_S | apply le_S]; rewrite Nat.add_comm; rewrite S_eq;
                 apply plus_le_compat; [apply le_n | apply le_1_sizet | apply le_n | apply le_1_sizet].
               case eq_OTerm_dec as [OTerm_eq | OTerm_neq].
               --- now left; inversion OTerm_eq.
               --- right.
                   intro OTerm_eq; inversion OTerm_eq as [Heq].
                   now rewrite Heq in OTerm_neq.
            ** now right; intro HOTerm_eq; inversion HOTerm_eq.
         ++ now right; intro HOTerm_eq; inversion HOTerm_eq.
  + case t2; intros; try now right.
    now left.
Qed.

(*****************************)
(**      Constraints        **)
(*****************************)

Inductive primitiveConstraint : Type :=
  | Eq : term -> term -> primitiveConstraint
  | Neq : term -> term -> primitiveConstraint
  | Mem : term -> term -> primitiveConstraint
  | Nmem : term -> term -> primitiveConstraint
  | FalseC : primitiveConstraint
  | IsSet : term -> primitiveConstraint.

Infix "==" := Eq (at level 60, right associativity).
Infix "\==" := Neq (at level 60, right associativity).
Infix ":s" := Mem (at level 60, right associativity).
Infix "\:s" := Nmem (at level 60, right associativity).

Lemma eq_primc_dec :
  forall (t t0 : primitiveConstraint), {t = t0} + {~t = t0}.
Proof.
decide equality; apply eq_term_dec.
Qed.

Definition constraint := list primitiveConstraint.

Lemma eq_constraint_dec :
  forall (t t0 : constraint), {t = t0} + {~t = t0}.
Proof.
decide equality; apply eq_primc_dec.
Qed.

(*****************************)
(**       OccurCheck        **)
(*****************************)

(*returns True if variable v occurs in term t*)
Fixpoint occurCheck (v : log_variable) (t : term) : Prop :=
  match t with
  | Var vA => v = vA
  | SetC t1 t2 => (occurCheck v t1) \/ (occurCheck v t2)
  | OTerm _ l =>
     let occurCheckList :=
     (fix occurCheckList (v: log_variable) (l: list term) {struct l}:Prop:=
       match l with
       | nil => False
       | t :: lt => (occurCheck v t) \/ (occurCheckList v lt)
     end) in
     occurCheckList v l
  | EmptySet => False
  end.

(*returns True if variable v occurs in at least one of the term of l, False otherwise*)
Fixpoint occurCheckList (v : log_variable) (l : list term) {struct l} : Prop :=
  match l with
  | nil => False
  | t :: lt => (occurCheck v t) \/ (occurCheckList v lt)
  end.

(*returns True if variable v occurs in the primitive constraint pc, False otherwise*)
Definition occurCheckPC (v : log_variable) (pc : primitiveConstraint) : Prop :=
  match pc with
  | t1 == t2 => (occurCheck v t1) \/ (occurCheck v t2)
  | t1 \== t2 => (occurCheck v t1) \/ (occurCheck v t2)
  | t1 :s t2 => (occurCheck v t1) \/ (occurCheck v t2)
  | t1 \:s t2 => (occurCheck v t1) \/ (occurCheck v t2)
  | FalseC => False
  | IsSet t => occurCheck v t
  end.

(*returns True if variable v occurs in constraint c, False ohterwise*)
Fixpoint occurCheckC (v : log_variable) (c : constraint) : Prop :=
  match c with
  | nil => False
  | t :: q => (occurCheckPC v t) \/( occurCheckC v q)
  end.

(*boolean version of occurCheck*)
Fixpoint boccurCheck (v : log_variable) (t : term) : bool :=
  match t with
  | Var vA => if (eq_variable_dec v vA)
              then true
              else false
  | SetC t1 t2 => if boccurCheck v t1
                  then true
                  else boccurCheck v t2
  | OTerm _ l =>
     let boccurCheckList :=
     (fix boccurCheckList (v : log_variable) (l : list term) {struct l} : bool :=
      match l with
      | nil => false
      | t :: lt => if boccurCheck v t
                   then true
                   else boccurCheckList v lt
      end) in
      boccurCheckList v l
  | EmptySet => false
  end.

Fixpoint boccurCheckList (v : log_variable) (l : list term) {struct l} : bool :=
      match l with
      | nil => false
      | t :: lt => if boccurCheck v t
                   then true
                   else boccurCheckList v lt
      end.

Lemma in_occurCheckC v pc c :
  In pc c -> occurCheckPC v pc ->
    occurCheckC v c.
Proof.
elim c; try contradiction.
intros pc' c' Hind Hin Hocc.
case Hin as [-> | ?]; try now left.
right.
now apply Hind.
Qed.

Lemma incl_occurCheckC v c1 c2 :
  incl c1 c2 -> occurCheckC v c1 ->
    occurCheckC v c2.
Proof.
elim c1; try contradiction.
intros pc c' Hind Hincl Hocc.
destruct (incl_cons_inv Hincl) as [Hin ?].
now case Hocc as [? |]; [apply (in_occurCheckC _ _ _ Hin) | apply Hind].
Qed.

Lemma occurCheckC_exists v c :
  occurCheckC v c <-> exists pc, In pc c /\ occurCheckPC v pc.
Proof.
elim c.
- split; try contradiction.
  now intros [? [? ?]]; contradiction.
- intros pc c' Hind.
  split.
  + intro HoC.
    case HoC as [? | H'].
    * exists pc.
      now split; [left | assumption].
    * assert (Hexists : exists pc : primitiveConstraint, In pc c' /\ occurCheckPC v pc).
        now apply Hind.
      destruct Hexists as [pc' [? ?]].
      exists pc'.
      now split; [right | assumption].
  + intros [pc' [Hin ?]].
    case Hin as [-> | ?]; try now left.
    right; apply Hind.
    exists pc'.
    now split.
Qed.

Lemma occurCheckList_exists v lt :
  occurCheckList v lt <-> exists t, In t lt /\ occurCheck v t.
Proof.
elim lt.
- split; try contradiction.
  now intros [? [? ?]]; contradiction.
- intros t lt' Hind.
  split.
  + intro HoC.
    case HoC as [? | H'].
    * exists t.
      now split; [left | assumption].
    * assert (Hexists : exists t, In t lt' /\ occurCheck v t).
        now apply Hind.
      destruct Hexists as [t' [? ?]].
      exists t'.
      now split; [right | assumption].
  + intros [t' [Hin ?]].
    case Hin as [-> | ?]; try now left.
    right; apply Hind.
    exists t'.
    now split.
Qed.

Lemma occurCheck_dec v t :
   {occurCheck v t} + {~ occurCheck v t}.
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) -> {occurCheck v t'} + {~ occurCheck v t'})).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  now absurd (sizet t' <= 0); [apply sizet_gte_1 | assumption].
- intro t'.
  case t'.
  + intros v' _.
    now apply eq_variable_dec.
  + intros t1 t2 Hsizet.
    destruct (sizet_SetC Hsizet).
    assert (Hor1 : {occurCheck v t1} + {~ occurCheck v t1}).
      now apply Hind.
    assert (Hor2 : {occurCheck v t2} + {~ occurCheck v t2}).
      now apply Hind.
    simpl.
    case Hor1 as [? | ?]; try now left; left.
    case Hor2 as [? | ?]; try now left; right.
    right.
    intros Hor.
    now case Hor.
  + intros s lt.
    elim lt; try now intro; right.
    intros t'' lt' Hind' Hsizet.
    assert (Hor : {occurCheck v t''} + {~ occurCheck v t''}).
      apply Hind.
      apply (sizet_OTerm Hsizet).
      now apply in_eq.
    assert (Hor' : {occurCheck v (OTerm s lt')} + {~ occurCheck v (OTerm s lt')}).
      apply Hind.
      apply le_S_n.
      apply le_trans with (m := sizet (OTerm s (t'' :: lt'))); try assumption.
      simpl; apply le_n_S.
      rewrite plus_comm.
      rewrite S_eq.
      apply plus_le_compat; try apply le_n.
      now apply le_1_sizet.
      case Hor as [? | ?]; try now left; left.
      case Hor' as [? | ?]; try now left; right.
      right; intros Hor''.
      now case Hor'' as [? | ?]; contradiction.
  + now intro; right.
Qed.

Lemma occurCheckList_dec v lt :
   {occurCheckList v lt} + {~ occurCheckList v lt}.
Proof.
elim lt; try now right.
intros t' lt' Hor.
case (occurCheck_dec v t') as [? | ?]; try now left; left.
case Hor as [? | ?]; try now left; right.
right.
intros Hor'.
now case Hor' as [? | ?]; contradiction.
Qed.

(*****************************)
(**    Useful functions     **)
(*****************************)

(*returns True if t is a variable, False otherwise*)
Definition isVariable (t : term) : Prop :=
  match t with
  | Var v => True
  | _ => False
  end.

(*returns True if t is the EmptySet, False otherwise*)
Definition isEmpty (t : term) : Prop :=
  match t with
  | EmptySet => True
  | _ => False
  end.

(*returns True if t is a constant, False otherwise*)
Definition isConstant (t : term) : Prop :=
  match t with
  | OTerm f nil => True
  | _ => False
  end.

(*returns True if t is a set Term, False otherwise*)
Fixpoint setTerm (t : term) {struct t} : Prop :=
  match t with
  | Var v => False
  | SetC t1 t2 => setTerm t2
  | OTerm f l => False
  | EmptySet => True
  end.

(*returns true if IsSet(Var(v)) belongs to c*)
Definition isSetInC (v : log_variable) (c : constraint) :=
  In (IsSet (Var v)) c.

(*same as map but works on two lists*)
Fixpoint map2 (A B C : Type) (f : A -> B -> C) (l1 : list A) (l2 : list B) : list C :=
  match l1 with
  | nil => nil
  | a1 :: t1 =>
                match l2 with
                | nil => nil (*not supposed to happend*)
                | a2 :: t2 => (f a1 a2) :: (map2 f t1 t2)
                end
  end.

(*returns the Eq primitivConstraint build on terms t1 and t2*)
Definition buildEq (t1 t2 : term) := t1 == t2.

(*returns the tail from term t, and None when this one doesn't exist*)
Fixpoint tail (t : term) : option(term) :=
  match t with
  | Var v => Some (Var v)
  | SetC _ t1 => tail t1
  | OTerm _ _ => None
  | EmptySet => Some EmptySet
  end.

(*returns list of terms in t without its tail and when it's a SetC*)
Fixpoint listElements (t : term) : list term :=
  match t with
  | Var v => nil
  | SetC t_1 t_2 => t_1 :: (listElements t_2)
  | OTerm f l => nil
  | EmptySet => nil
  end.

(*returns the list needed to use listSetC from (SetC t1 t2)*)
Definition SetCToList (t1 t2 : term) : list term :=
  let lAux := listElements t2 in t1 :: lAux.

(*returns the last element from t which must be the second term of a SetC*)
Fixpoint LastFromSetC (t : term) : term :=
  match t with
  | Var v => Var v
  | SetC t1 t2 => LastFromSetC t2
  | OTerm f l => OTerm f l
  | EmptySet => EmptySet
  end.

(*build the term obtained by inserting each term from l into t*)
Fixpoint listSetC (l : list term) (t : term) : term :=
  match l with
  | nil => t
  | t' :: lt => (SetC t' (listSetC lt t))
  end.

Lemma sizet_in_listSetC t t' lt :
  In t' lt -> sizet t' < sizet (listSetC lt t).
Proof.
elim lt; try contradiction.
intros t'' lt''.
simpl; elim lt''.
- intros _ Hor.
  case Hor as [-> | ?]; try contradiction.
  simpl; apply le_lt_n_Sm.
  apply le_plus_l.
- intros t''' lt''' _ Hind Hor.
  case Hor as [-> | ?].
  + simpl; apply le_lt_n_Sm.
    apply le_plus_l.
  + simpl; apply le_lt_n_Sm.
    rewrite Nat.add_comm.
    apply le_plus_trans.
    apply Nat.lt_le_incl.
    now apply Hind.
Qed.

Lemma listSetC_listElements_LastFromSetC t1 t2 :
  SetC t1 t2 = listSetC (listElements (SetC t1 t2)) (LastFromSetC t2).
Proof.
set (P := fun (n : nat) => (forall t1 t2, (((sizet t1) + (sizet t2)) <= n) ->
  SetC t1 t2 = listSetC (listElements (SetC t1 t2)) (LastFromSetC t2))).
enough (H : (forall n, (P n))).
  apply (H (sizet t1 + sizet t2)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t1' t2' Hsizet_plus.
  absurd (sizet t1' <= 0); try now apply sizet_gte_1.
  now apply (le_add_l _ _ (Hsizet_plus)).
- intros t1' t2'.
  case t2'; try trivial.
  intros t3 t4 Hsizet.
  enough (Heq : SetC t3 t4 = listSetC (listElements (SetC t3 t4)) (LastFromSetC t4)).
    now simpl; rewrite Heq.
  apply Hind.
  apply le_S_n.
  apply le_trans with (m := sizet t1' + sizet ({{t3 | t4}})); try assumption.
  now apply le_plus_r.
Qed.

(*returns list l where element in position j has been deleted*)
Fixpoint deleteElmntj (A : Type) (j : nat) (l : list A) {struct l} : list A :=
  match j with
  | 0 =>
         match l with
         | nil => nil
         | t :: q => q
         end
  | S m =>
           match l with
           | nil => nil
           | t :: q => t :: (deleteElmntj m q)
           end
  end.

Lemma setTerm_listSetC t lt :
  lt <> nil ->
    setTerm (listSetC lt t) = (setTerm t).
Proof.
set (P := fun (n : nat) => (forall lt', forall t', (length lt' <= n) -> lt' <> nil ->
                             setTerm (listSetC lt' t') = (setTerm t'))).
enough (H : (forall n, (P n))).
  apply (H (length lt)).
  now apply le_n.
intro n.
induction n as [ | n Hind]; intros lt1 t1.
- intro Hlength.
  enough (He : lt1 = nil).
    now rewrite He; contradiction.
  apply length_zero_iff_nil.
  now apply Nat.le_0_r.
- elim lt1; try contradiction.
  intros t2 lt2.
  elim lt2; try reflexivity.
  intros t3 lt3 _ _ Hlength _.
  enough (He : setTerm (listSetC (t3 :: lt3) t1) = setTerm t1).
    now simpl; rewrite <- He.
  apply Hind; try now apply le_S_n.
  now apply cons_neq_nil.
Qed.

Lemma listElements_listSetC t lt :
  lt <> nil ->
    listElements (listSetC lt t) = lt ++ (listElements t).
Proof.
set (P := fun (n : nat) => (forall lt', forall t', (length lt' <= n) -> lt' <> nil ->
                             listElements (listSetC lt' t') = lt' ++ (listElements t'))).
enough (H : (forall n, (P n))).
  apply (H (length lt)).
  now apply le_n.
intro n.
induction n as [ | n Hind]; intros lt1 t1.
- intro Hlength.
  enough (He : lt1 = nil).
    now rewrite He; contradiction.
  apply length_zero_iff_nil.
  now apply Nat.le_0_r.
- elim lt1; try contradiction.
  intros t2 lt2.
  elim lt2; try reflexivity.
  intros t3 lt3 _ _ Hlength _.
  enough (He : listElements (listSetC (t3 :: lt3) t1) = t3 :: lt3 ++ listElements t1).
    now simpl; rewrite <- He.
  apply Hind; try now apply le_S_n.
  now apply cons_neq_nil.
Qed.

Lemma listElements_listSetC_EmptySet   lt :
  listElements (listSetC lt EmptySet) = lt.
Proof.
case lt; try trivial.
intros t' lt'.
rewrite listElements_listSetC; try now trivial.
now rewrite app_nil_r.
Qed.

Lemma deleteElmntj_incl  (A : Type) (j : nat) (l : list A) :
  incl (deleteElmntj j l) l.
Proof.
set (P := fun (n : nat) => (forall l' : list A, forall j', (length l' <= n) -> incl (deleteElmntj j' l') l')).
enough (H : (forall n, (P n))).
  apply (H (length l)).
  now apply le_n.
intro n.
induction n as [ | n Hind]; intros l' j'.
- intro Hlength.
  assert (Hnil : l' = nil).
    apply length_zero_iff_nil.
    now apply Nat.le_0_r.
  rewrite Hnil.
  now elim j'; [ | intros n _]; apply incl_nil_l.
- elim l'.
  + elim j'; try now intros; apply incl_nil_l.
  + intros a' l'' _ Hlength.
    elim j'; try now apply incl_tl.
    intros ? _.
    apply incl_cons; try now apply in_eq.
    apply incl_tl.
    apply Hind.
    now apply le_S_n.
Qed.

Lemma deleteElmntj_eq_nil (A : Type) (j : nat) (l : list A) (a : A) :
  nth_error l j = Some a -> (deleteElmntj j l) = nil ->
    l = a :: nil.
Proof.
elim l.
- intro Hnth_error.
  absurd (In a nil); try now apply in_nil.
  now apply nth_error_In with (n := j).
- intros a' l'.
  elim j.
  + simpl; intros _ Hsome ->.
    now inversion Hsome.
  + intros ? _ _ _ Habs.
    absurd (In a' nil); try now apply in_nil.
    rewrite <- Habs.
    now apply in_eq.
Qed.

Lemma deleteElmntj_in_or (A : Type) (j : nat) (l : list A) (a a' : A) :
  nth_error l j = Some a' -> In a l ->
    (a = a') \/ (In a (deleteElmntj j l)).
Proof.
set (P := fun (n : nat) => (forall l' : list A, forall j', (length l' <= n) ->
              nth_error l' j' = Some a' -> In a l' -> (a = a') \/ (In a (deleteElmntj j' l')))).
enough (H : (forall n, (P n))).
  apply (H (length l)).
  now apply le_n.
intro n.
induction n as [ | n Hind]; intros l' j'.
- elim j'.
  + elim l'; try contradiction.
    intros ? ? _ Habs.
    inversion Habs.
  + intros m _.
    elim l'; try contradiction.
    intros a'' l'' _ Habs.
    inversion Habs.
- elim l'; try contradiction.
  intros a'' l'' _. simpl.
  elim j'.
  + intros _ Hsome Hor.
    inversion Hsome as [Heq].
    case Hor as [Heq' | ?]; try now right.
    now left; rewrite <- Heq'.
  + intros m.
    intros ? ? ? Hor.
    case Hor as [? | ?]; try now right; left.
    assert (Hor :  a = a' \/ In a (deleteElmntj m l'')).
      apply Hind; try assumption.
      now apply le_S_n.
    case Hor as [? | ?]; try now left.
    now do 2 right.
Qed.

Lemma incl_deleteElmntj (A : Type) (j : nat) (l : list A) (a : A) :
  nth_error l j = Some a ->
    incl l (a :: (deleteElmntj j l)).
Proof.
intros Hnth a' HIn.
case (deleteElmntj_in_or _ _ _ Hnth HIn) as [-> | ?]; try now apply in_eq.
now apply in_cons.
Qed.

Lemma sizet_listSetC t lt :
  forall t', sizet t < sizet (listSetC (t' :: lt) t).
Proof.
elim lt.
- intro t'; simpl; apply le_lt_n_Sm.
  now apply le_plus_r.
- intros t'' lt' H.
  intro t'; simpl; apply le_lt_n_Sm.
  rewrite Nat.add_comm.
  apply le_plus_trans.
  apply Nat.lt_le_incl.
  now apply H.
Qed.

Lemma listSetC_neq t1 t2 lt :
  (listSetC (t1 :: lt) t2) <> t2.
Proof.
intro Habs.
absurd (sizet t2 < sizet (listSetC (t1 :: lt) t2)); try now apply sizet_listSetC.
rewrite Habs.
now apply Nat.lt_irrefl.
Qed.

Lemma listSetC_cons t1 t2 lt :
  lt <> nil -> (listSetC (t1 :: lt) t2) = SetC t1 (listSetC lt t2).
Proof.
elim lt; try contradiction.
now intros t' lt' _ _.
Qed.

Lemma listSetC_app t lt1 lt2 :
  lt1 <> nil -> lt2 <> nil ->
    (listSetC (lt1 ++ lt2) t) = listSetC lt1 (listSetC lt2 t).
Proof.
set (P := fun (n : nat) => (forall lt1' lt2', ((length lt1' + length lt2') <= n) ->
                                              lt1' <> nil -> lt2' <> nil ->
                                  (listSetC (lt1' ++ lt2') t) = listSetC lt1' (listSetC lt2' t))).
enough (H : (forall n, (P n))).
  apply (H (length lt1 + length lt2)).
  now apply le_n.
intro n.
induction n as [ | n Hind]; intros lt1' lt2'.
- intros Hle0 Hlength.
  assert (Heq0 : length lt1' + length lt2' = 0).
    now apply Nat.le_0_r.
  absurd (lt1' = nil); try assumption.
  apply length_zero_iff_nil.
  now destruct (plus_is_O _ _ Heq0).
- elim lt1'; try contradiction.
  intros t3 lt3.
  elim lt2'; try contradiction.
  intros t4 lt4 _ _.
  elim lt3; try reflexivity.
  intros t5 lt5 _ Hlength _ _.
  rewrite listSetC_cons; try now apply cons_neq_nil.
  assert (Heq : (t3 :: t5 :: lt5) ++ t4 :: lt4 = t3 :: (t5 :: lt5 ++ t4 :: lt4)).
    trivial.
  rewrite Heq.
  rewrite listSetC_cons; try now apply cons_neq_nil.
  enough (He : listSetC (t5 :: lt5 ++ t4 :: lt4) t = listSetC (t5 :: lt5) (listSetC (t4 :: lt4) t)).
    now rewrite He.
  apply Hind with (lt1' := t5 :: lt5); try now apply cons_neq_nil.
  now apply le_S_n.
Qed.

Lemma listSetC_app_EmptySet lt1 lt2 :
  lt1 <> nil -> (listSetC (lt1 ++ lt2) EmptySet) = listSetC lt1 (listSetC lt2 EmptySet).
Proof.
intro Hlt1_neq_nil.
case (list_eq_dec eq_term_dec lt2 nil) as [-> | Hlt2_neq_nil]; try now rewrite app_nil_r.
now apply listSetC_app.
Qed.

Lemma listSetC_eq_l t lt1 lt2 :
  listSetC lt1 t = listSetC lt2 t -> lt1 = lt2.
Proof.
set (P := fun (n : nat) => (forall lt1' lt2' t', ((length lt1') +
(length lt2') <= n) -> listSetC lt1' t' = listSetC lt2' t' -> lt1' =
lt2')).
enough (H : (forall n, (P n))).
  apply (H ((length lt1) + (length lt2))).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros lt1' lt2' t' Hlength.
  assert (Hnil : lt1' = nil).
    apply length_zero_iff_nil.
    apply Nat.le_0_r.
    now apply le_add_l with (m := length lt2').
  rewrite Hnil.
  elim lt2'; try reflexivity.
  intros t'' lt' _ Habs.
  absurd (sizet t' = sizet (listSetC (t'' :: lt') t'));
    try now rewrite <- Habs.
  apply Nat.lt_neq.
  now apply sizet_listSetC.
- intros lt1' lt2' t'.
  elim lt1'.
  + elim lt2'; try reflexivity.
    intros t2 lt2'' _ _ Habs.
    absurd (sizet t' = sizet (listSetC (t2 :: lt2'') t'));
      try now rewrite <- Habs.
    apply Nat.lt_neq.
    now apply sizet_listSetC.
  + intros t1 lt1'' _.
    elim lt2'.
    * intros  _ Habs.
      absurd (sizet t' = sizet (listSetC (t1 :: lt1'') t'));
        try now rewrite Habs.
      apply Nat.lt_neq.
      now apply sizet_listSetC.
    * intros t2 lt2'' _.
      elim lt1''.
      -- elim lt2''.
          ++ intros _ H.
            now inversion H.
          ++ intros t'' lt'' ? ? H.
             inversion H.
             absurd (sizet t' = sizet (listSetC (t'' :: lt'') t')).
             ** apply Nat.lt_neq.
                now apply sizet_listSetC.
             ** assert (He : ({{t'' | listSetC lt'' t'}}) = listSetC (t'' :: lt'') t').
                  trivial.
                rewrite <- He.
                now rewrite <- H4.
      -- intros t1' lt1''' _ .
         elim lt2''.
         ++ intros _ H.
            inversion H.
            absurd (sizet t' = sizet (listSetC (t1' :: lt1''') t')).
            ** apply Nat.lt_neq.
               now apply sizet_listSetC.
            ** assert (He : ({{t1' | listSetC lt1''' t'}}) = listSetC (t1' :: lt1''') t').
                 trivial.
               rewrite <- He.
               now rewrite H2.
         ++ intros t2' lt2''' _ Hlength H.
            inversion H.
            enough (He : t1' :: lt1''' = t2' :: lt2''').
              rewrite <- He.
              now rewrite H2.
            apply Hind with (t' := t'); try assumption.
            apply le_S_n.
            apply le_trans with (m := length (t1 :: t1' :: lt1''') + length (t2 :: t2' :: lt2''')); try assumption.
            do 2 apply le_n_S.
            apply Nat.add_le_mono_l.
            now apply Nat.le_succ_diag_r.
            rewrite H2.
            now simpl; rewrite H3.
Qed.

Lemma listSetC_Var_eq_list v1 v2 lt1 lt2 :
  listSetC lt1 (Var v1) = listSetC lt2 (Var v2) ->
    lt1 = lt2.
Proof.
set (P := fun (n : nat) => (forall lt1' lt2', ((length lt1') + (length lt2') <= n) -> listSetC lt1' (Var v1) = listSetC lt2' (Var v2) -> lt1' = lt2')).
enough (H : (forall n, (P n))).
  apply (H ((length lt1) + (length lt2))).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros lt1' lt2' Hlength.
  assert (Hnil : lt1' = nil).
    apply length_zero_iff_nil.
    apply Nat.le_0_r.
    now apply le_add_l with (m := length lt2').
  rewrite Hnil.
  elim lt2'; try reflexivity.
  intros t'' lt' _.
  elim lt'; discriminate.
- intros lt1' lt2'.
  elim lt1'.
  + elim lt2'; try trivial.
    intros t2 lt2'' _ _.
    now elim lt2''; intros Habs; inversion Habs.
  + intros t1 lt1''.
    elim lt2'; try now intros _; elim lt1''; intros Habs; inversion Habs.
    intros t2 lt2'' _ _ Hlength Heq.
    enough (He : t1 = t2 /\ listSetC lt1'' (Var v1) = listSetC lt2'' (Var v2)).
      destruct He as [-> H].
      enough (He : lt1'' = lt2'').
        now rewrite He.
      apply Hind; try assumption.
      apply le_S_n.
      apply le_trans with (m := length (t2 :: lt1'') + length (t2 :: lt2'')); try assumption.
      apply le_n_S.
      apply Nat.add_le_mono_l.
      now apply Nat.le_succ_diag_r.
    revert Heq.
    elim lt1''; elim lt2''; try now intros ? lt _; elim lt.
      * now intros H; inversion H.
      * intros ? ? ? ? ? _ H'.
        now simpl; inversion H'.
Qed.

Lemma setTerm_exists_listSetC t :
  setTerm t -> exists lt, t = listSetC lt EmptySet.
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) -> setTerm t' -> exists lt, t' = listSetC lt EmptySet)).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  now absurd (sizet t' <= 0); [apply sizet_gte_1 | assumption].
- intro t'.
  case t'.
  + intro; contradiction.
  + intros t1 t2 Hsizet HsetTerm.
    assert (Hexists : exists lt', t2 = listSetC lt' EmptySet).
      apply Hind; try assumption.
      now destruct (sizet_SetC Hsizet).
    destruct Hexists as [lt' Heq].
    exists (t1 :: lt').
    rewrite Heq.
    now elim lt'; reflexivity.
  + now intros; contradiction.
  + intros.
    now exists nil.
Qed.

Lemma dec_setTerm t :
  decidable (setTerm t).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) -> decidable (setTerm t'))).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  now absurd (sizet t' <= 0); [apply sizet_gte_1 | assumption].
- intro t'.
  case t'.
  + now intros; apply dec_False.
  + intros t1 t2 Hsizet.
    simpl; apply Hind.
    now destruct (sizet_SetC Hsizet).
  + now intros; apply dec_False.
  + now intros; apply dec_True.
Qed.

Lemma isVariable_dec t :
  (isVariable t) \/ (~isVariable t).
Proof.
case t; try now right.
now intro; left.
Qed.

Lemma isVariable_exists t :
  isVariable t ->
    exists v, t = Var v.
Proof.
case t; try now intros.
now intros v _; exists v.
Qed.

Lemma tail_EmptySet_exists t1 t2 :
  tail t2 = Some EmptySet ->
    exists lt, SetC t1 t2 = listSetC lt EmptySet.
Proof.
set (P := fun (n : nat) => (forall t1' t2', ((sizet t2') <= n) ->
  tail t2' = Some EmptySet ->
    exists lt, SetC t1' t2' = listSetC lt EmptySet)).
enough (H : (forall n, (P n))).
  apply (H (sizet t2)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t1' t2' ?.
  now absurd (sizet t2' <= 0); [apply sizet_gte_1 | assumption].
- intros t1' t2'.
  case t2'.
  + intros ?; discriminate.
  + intros t3 t4 Hsizet Htail.
    destruct (sizet_SetC Hsizet) as [_ ?].
    assert (Hexists : exists lt, {{t3 | t4}} = listSetC lt EmptySet).
      try now apply Hind; destruct (sizet_SetC Hsizet) as [_ ?].
    destruct Hexists as [lt ->].
    exists (t1' :: lt).
    now case lt.
  + now intros ? ?; discriminate.
  + now intros _ _; exists (t1' :: nil).
Qed.

Lemma tail_Var_exists v t1 t2 :
  tail t2 = Some (Var v) ->
    exists lt, lt <> nil /\ SetC t1 t2 = listSetC lt (Var v).
Proof.
set (P := fun (n : nat) => (forall t1' t2', ((sizet t2') <= n) ->
  tail t2' = Some (Var v) ->
    exists lt, lt <> nil /\ SetC t1' t2' = listSetC lt (Var v))).
enough (H : (forall n, (P n))).
  apply (H (sizet t2)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t1' t2' ?.
  now absurd (sizet t2' <= 0); [apply sizet_gte_1 | assumption].
- intros t1' t2'.
  case t2'.
  + intros ? _ Heq.
    inversion Heq.
    now exists (t1' :: nil).
  + intros t3 t4 Hsizet Htail.
    destruct (sizet_SetC Hsizet) as [_ ?].
    assert (Hexists : exists lt, lt <> nil /\ {{t3 | t4}} = listSetC lt (Var v)).
      try now apply Hind; destruct (sizet_SetC Hsizet) as [_ ?].
    destruct Hexists as [lt [Hneq_nil ->]].
    now exists (t1' :: lt).
  + now intros ? ?; discriminate.
  + intros _ Heq.
    now inversion Heq.
Qed.

Lemma tail_listSetC_Var lt v :
  lt <> nil -> tail (listSetC lt (Var v)) = Some (Var v).
Proof.
elim lt; try contradiction.
intros t' lt'.
case lt'; try trivial.
intros t'' lt'' Hind _.
assert (Heq : tail (listSetC (t' :: t'' :: lt'') (Var v)) = tail (listSetC (t'' :: lt'') (Var v))).
  trivial.
rewrite Heq.
now apply Hind.
Qed.

Lemma listSetC_SetCToList t1 t2 lt v :
  ({{t1 | t2}}) = listSetC lt (Var v) ->
    (SetCToList t1 t2) = lt.
Proof.
set (P := fun (n : nat) => (forall t1' t2' lt', ((sizet t2') <= n) ->
  ({{t1' | t2'}}) = listSetC lt' (Var v) -> (SetCToList t1' t2') = lt')).
enough (H : (forall n, (P n))).
  apply (H (sizet t2)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t1' t2' lt' ?.
  now absurd (sizet t2' <= 0); [apply sizet_gte_1 | assumption].
- intros t1' t2' lt'.
  case t2'.
  + intros ? ? Heq.
    assert (Heq1 : ({{t1' | Var l}}) = listSetC (t1' :: nil) (Var l)).
      trivial.
    assert (Heq2 : t1' :: nil = lt').
      rewrite Heq1 in Heq.
      now apply (listSetC_Var_eq_list _ _ _ _ Heq).
    now rewrite <- Heq2.
  + intros t3 t4 Hsizet.
    elim lt'; try discriminate.
    intros t lt'' _ Heq.
    assert (Heq1 : {{t3 | t4}} = listSetC lt'' (Var v)).
      revert Heq.
      elim lt''; try now intro H; inversion H.
      now intros ? ? _ H; inversion H.
    assert (Heq2 : SetCToList t3 t4 = lt'').
      apply Hind; try assumption.
      now destruct (sizet_SetC Hsizet).
    unfold SetCToList.
    unfold SetCToList in Heq2.
    simpl; rewrite Heq2.
    assert (Heq3 : listSetC (t :: lt'') (Var v) = ({{t | listSetC lt'' (Var v)}})).
      revert Heq1.
      now elim lt''; try intro Heq; inversion Heq.
    rewrite Heq3 in Heq.
    now inversion Heq.
  + intros s lt'' Hsizet Heq.
    assert (Htail1 : tail (listSetC lt' (Var v)) = None).
      now rewrite <- Heq.
    assert (Htail2 : tail (listSetC lt' (Var v)) = Some (Var v)).
      apply tail_listSetC_Var.
      intro Habs.
      now rewrite Habs in Heq.
    now rewrite Htail1 in Htail2.
  + intros _ Heq.
    assert (Htail1 : tail (listSetC lt' (Var v)) = Some EmptySet).
      now rewrite <- Heq.
    assert (Htail2 : tail (listSetC lt' (Var v)) = Some (Var v)).
      apply tail_listSetC_Var.
      intro Habs.
      now rewrite Habs in Heq.
    now rewrite Htail1 in Htail2.
Qed.

Lemma tail_listSetC_EmptySet lt :
  tail (listSetC lt EmptySet) = Some EmptySet.
Proof.
now elim lt.
Qed.

Lemma tail_setTerm t :
  setTerm t -> tail t = Some EmptySet.
Proof.
intro HsetTerm.
destruct (setTerm_exists_listSetC _ HsetTerm) as [lt ->].
now apply tail_listSetC_EmptySet.
Qed.

Lemma occurCheckList_listElements v t :
  occurCheck v t -> ~ occurCheck v (LastFromSetC t) ->
    occurCheckList v (listElements t).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
             occurCheck v t' -> ~ occurCheck v (LastFromSetC t') ->
             occurCheckList v (listElements t'))).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  now absurd (sizet t' <= 0); [apply sizet_gte_1 | assumption].
- intro t'.
  case t'.
  + now intros v' _ ->; simpl; contradiction.
  + intros t1 t2 Hsizet Hor ?.
    case Hor as [? | ?]; try now left.
    right.
    apply Hind; try assumption.
    now destruct (sizet_SetC Hsizet).
  + now intros ? ? ?; contradiction.
  + now intro.
Qed.

(*******************************************************************)
(**                      Fresh variables                           *)
(*******************************************************************)

(*returns True if N is a fresh variable in c, i,e., N doesn't appear in c, False otherwise*)
Definition isFreshC (N : log_variable) (c : constraint) : Prop :=
  ~(occurCheckC N c).

(*returns True if N is a fresh variable in l, i.e., N doesn't appear in any term of l, False otherwise*)
Definition isFreshL (N : log_variable) (l : list term) : Prop :=
  ~(occurCheckList N l).

Definition isFreshT (N : log_variable) (t : term) :=
  ~(occurCheck N t).

(*returns True if pc is a primitivConstraint of the form Nmem, False otherwise*)
Definition isNmemPC (pc : primitiveConstraint) :=
  match pc with
  | t1 \:s t2 => True
  | _ => False
  end.

Lemma incl_isFreshC v c1 c2 :
  incl c1 c2 -> isFreshC v c2 -> isFreshC v c1.
Proof.
intros Hincl HisFresh2 Habs.
absurd (occurCheckC v c2); try assumption.
now apply incl_occurCheckC with (c1 := c1).
Qed.

Lemma isFreshT_SetC_isFreshL v t1 t2 :
  isFreshT v (SetC t1 t2) -> isFreshL v (SetCToList t1 t2).
Proof.
set (P := fun (n : nat) => (forall t1' t2', ((sizet t2') <= n) ->
  isFreshT v (SetC t1' t2') -> isFreshL v (SetCToList t1' t2'))).
enough (H : (forall n, (P n))).
  apply (H (sizet t2)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t1' t2' ?.
  now absurd (sizet t2' <= 0); [apply sizet_gte_1 | assumption].
- intros t1' t2'.
  case t2'.
  + intros ? _.
    intros H Hor.
    case Hor as [? | ?]; try trivial.
    absurd (occurCheck v t1' \/ v = l); try assumption.
    now left.
  + intros t3 t4 Hsizet.
    intros Hnor Hor.
    case Hor as [H1 | H2].
    * absurd (occurCheck v t1' \/ occurCheck v t3 \/ occurCheck v t4); try assumption.
      now left.
    * destruct (not_or _ _ Hnor) as [_ H].
      absurd (occurCheck v t3 \/ occurCheckList v (listElements t4)); try assumption.
      apply Hind; try assumption.
      now destruct (sizet_SetC Hsizet).
  + intros s lt _.
    intros H Hor.
    case Hor as [? | ?]; try trivial.
    absurd (occurCheck v t1' \/ occurCheck v (OTerm s lt)); try assumption.
    now left.
  + now intros _.
Qed.

(*******************************************************************)
(*                       Solved Form                               *)
(*******************************************************************)

Definition isInSFPC (pc : primitiveConstraint) (c : constraint) :=
  match pc with
  | Var v == t => ((~(occurCheck v t)) /\ (~(occurCheckC v (remove eq_primc_dec pc c))))
  | Var v \== t => (~(occurCheck v t))
  | t \:s (Var v) => (~(occurCheck v t))
  | IsSet (Var X) => True
  | _ => False
  end.

Definition isInSFC (c : constraint) :=
  forall cp, In cp c -> isInSFPC cp c.

Lemma incl_isInSFPC pc c1 c2 :
  incl c1 c2 -> isInSFPC pc c2 ->
    isInSFPC pc c1.
Proof.
intros Hincl.
case pc; try contradiction.
- intros ? ?; simpl.
  case t; try contradiction.
  intros ? [? ?].
  split; try assumption.
  intro.
  absurd (occurCheckC l (remove eq_primc_dec (Var l == t0) c2));
    try assumption.
  apply incl_occurCheckC with (c1 := (remove eq_primc_dec (Var l == t0) c1)); try assumption.
  now apply remove_incl.
- intros ? ?; simpl.
  now case t; try contradiction.
- intros ? t; simpl.
  now case t; intro; try contradiction.
- intro; simpl.
  now case t; try contradiction.
Qed.

Lemma incl_isInSFC c1 c2 :
  incl c1 c2 -> isInSFC c2 ->
    isInSFC c1.
Proof.
intros Hincl HisInSFC pc Hin.
apply (incl_isInSFPC _ Hincl).
apply HisInSFC.
now apply Hincl.
Qed.

Lemma isInSFPC_inv pc1 pc2 c :
  In pc1 c -> isInSFPC pc2 c ->
    isInSFPC pc2 (pc1 :: remove eq_primc_dec pc1 c).
Proof.
intro.
case pc2; try trivial.
intros t1 t2.
case t1; try trivial.
intros v [? ?].
split; try assumption.
intro.
assert (Hexists : exists pc3,
        In pc3 (remove eq_primc_dec (Var v == t2) (pc1 :: remove eq_primc_dec pc1 c)) /\ occurCheckPC v pc3).
  now apply occurCheckC_exists.
destruct Hexists as [pc3 [Hinpc3 ?]].
enough (occurCheckC v (remove eq_primc_dec (Var v == t2) c)).
  contradiction.
apply occurCheckC_exists.
exists pc3.
split; try assumption.
destruct (in_remove eq_primc_dec _ _ _ Hinpc3) as [Hinpc3' ?].
apply in_in_remove; try assumption.
case Hinpc3' as [<- | ?]; try assumption.
now apply (incl_remove eq_primc_dec pc1).
Qed.

Lemma isInSFC_inv pc c :
  In pc c ->
    isInSFC c -> isInSFC (pc :: remove eq_primc_dec pc c).
Proof.
intros ? HinSFC ? Hin.
apply isInSFPC_inv; try assumption.
apply HinSFC.
case (in_inv Hin) as [-> | ?]; try assumption.
now apply (incl_remove eq_primc_dec pc c).
Qed.


