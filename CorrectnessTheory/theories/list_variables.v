(****************************************
Maximiliano Cristia - Ricardo David Katz 
                  2026                   
****************************************)

Set Implicit Arguments.

Require Import Arith List Recdef Decidable.
Require Import Bool.
Require Import preliminaries terms_constraints substitution.

(*****************************************)
(* different kinds of lists of variables *)
(*****************************************)

(*returns a list with the variables in a term*)
Fixpoint listVarInT (t : term) {struct t} : list log_variable :=
  match t with
  | Var v => v :: nil
  | SetC t1 t2 => (listVarInT t1) ++ (listVarInT t2)
  | OTerm _ l =>
      let listVarInList :=
      (fix listVarInList (l : list term) {struct l} : list log_variable :=
        match l with
        | nil => nil
        | t :: lt => (listVarInT t) ++ (listVarInList lt)
     end) in
    listVarInList l
  |EmptySet => nil
  end.

(*returns a list with the variables in a list of terms*)
Fixpoint listVarInListT (l : list term) {struct l} : list log_variable :=
  match l with
  | nil => nil
  | t :: lt => (listVarInT t) ++ (listVarInListT lt)
  end.

(*returns a list with the variables in a primitive constraint pc*)
Definition listVarInPC (pc : primitiveConstraint) : list log_variable :=
  match pc with
  | t1 == t2 => (listVarInT t1) ++ (listVarInT t2)
  | t1 \== t2 => (listVarInT t1) ++ (listVarInT t2)
  | t1 :s t2 => (listVarInT t1) ++ (listVarInT t2)
  | t1 \:s t2 => (listVarInT t1) ++ (listVarInT t2)
  | FalseC => nil
  | IsSet t => listVarInT t
  end.

(*returns a list with the variables in a constraint c*)
Fixpoint listVarInC (c : constraint) : list log_variable :=
  match c with
  | nil => nil
  | pc :: lpc => (listVarInPC pc) ++ (listVarInC lpc)
  end.

(*returns a list with the variables that occur in the left-hand side of equalities of the form Var v == t in a constraint*)
Fixpoint listVarInEqLHS (c : constraint) : list log_variable :=
  match c with
  | nil => nil
  | (Var v == t) :: lpc => v :: (listVarInEqLHS lpc)
  | _ :: lpc => (listVarInEqLHS lpc)
  end.

(* returns true if a variable occurs in a list and false otherwise*)
Fixpoint In_list_log_variable (v : log_variable) (l : list log_variable) :=
  match l with
  | nil => false
  | LogV n :: lv => match v with
                    | LogV n' => if (n =? n') then true else (In_list_log_variable v lv)
                    end
  end.

(*returns a list with the variables that occur in constraint but do not occur 
in the left-hand side of equalities of the form Var v == t in that constraint*)
Definition listVarNotInEqLHS (c : constraint) :=
  remove_list eq_variable_dec (listVarInEqLHS c) (listVarInC c).

(************************************)
(* properties of lists of variables *)
(************************************)

Lemma In_listVarInPC_listVarInC v pc c :
  In v (listVarInPC pc) -> In pc c ->
    In v (listVarInC c).
Proof.
intro HIn.
elim c; try contradiction.
intros pc' c' Hind HIn'.
case HIn' as [-> | ?].
- now apply in_or_app; left.
- apply in_or_app; right.
  now apply Hind.
Qed.

Lemma listVarInListT_eq_nil lt :
  (listVarInListT lt = nil) <-> (forall t, In t lt -> (listVarInT t) = nil).
Proof.
split.
- elim lt; try contradiction.
  intros t' lt' Hind Hnil t'' HIn.
  destruct (app_eq_nil _ _ Hnil).
  now case HIn as [<- | HIn]; [assumption | apply Hind].
- elim lt; try trivial.
  intros t' lt' Hind H.
  enough (He : listVarInT t' = nil /\ listVarInListT lt' = nil).
    simpl; now destruct He as [-> ->].
  split.
  + apply H.
    now apply in_eq.
  + apply Hind.
    intros pc'' HIn.
    apply H.
    now apply in_cons.
Qed.

Lemma listVarInPC_listVarInC_nil pc c :
  listVarInC c = nil -> In pc c ->
    listVarInPC pc = nil.
Proof.
elim c; try contradiction.
intros cp' c' Hind Hnil HIn.
simpl in Hnil; destruct (app_eq_nil _ _ Hnil).
case HIn as [-> | ?]; try assumption.
now apply Hind.
Qed.

Lemma In_listVarInT_OTerm v s lt :
  In v (listVarInT (OTerm s lt)) <-> (exists t, In t lt /\ In v (listVarInT t)).
Proof.
split.
- elim lt; try contradiction.
  intros t lt' Hind HIn.
  simpl in HIn; case (in_app_or _ _ _ HIn) as [HInt | HInOT].
  + exists t.
    split; try assumption.
    apply in_eq.
  + destruct (Hind HInOT) as [t' [? ?]].
    exists t'.
    split; try assumption.
    now apply in_cons.
- intros [t [HInt HInv]].
  revert HInt.
  elim lt; try contradiction.
  intros t' lt' Hind HInt.
  simpl; apply in_or_app.
  case HInt as [-> | HInOT]; try now left.
  now right; apply Hind.
Qed.

Lemma In_listVarInT_occurCheck v t :
  In v (listVarInT t) -> occurCheck v t.
Proof.
set (P := fun (n : nat) => (forall t, ((sizet t) <= n) -> In v (listVarInT t) -> occurCheck v t)).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' Hsizet_plus.
  absurd (sizet t' <= 0); try assumption.
  now apply sizet_gte_1.
- intro t'.
  case t'.
  + intros v' Hsize Hor.
    case Hor as [-> | ]; [reflexivity | contradiction].
  + intros t1 t2 Hsizet Hin.
    destruct (sizet_SetC Hsizet).
    simpl in Hin.
    case (in_app_or _ _ _ Hin) as [Hint1 | Hint2];
      [left | right]; now apply Hind.
  + intros ? lt.
    elim lt; try trivial.
    intros t'' lt' Hind' Hsizet Hin.
    simpl in Hsizet.
    simpl in  Hin.
    case (in_app_or _ _ _ Hin) as [Hint1 | Hint2]; [left | right].
    * apply Hind; try assumption.
      rewrite <- plus_Sn_m in Hsizet.
      apply le_S_n.
      now apply (le_add_l _ _ Hsizet).
    * apply Hind'; try assumption.
      rewrite plus_n_Sm in Hsizet.
      now apply (le_add_r _ _ Hsizet).
  + trivial.
Qed.

Lemma In_listVarInPC_occurCheckPC v pc :
  In v (listVarInPC pc) -> occurCheckPC v pc.
Proof.
case pc.
- intros ? ? Hin.
  now case (in_app_or _ _ _ Hin) as [? | ?]; [left | right]; apply In_listVarInT_occurCheck.
- intros ? ? Hin.
  now case (in_app_or _ _ _ Hin) as [? | ?]; [left | right]; apply In_listVarInT_occurCheck.
- intros ? ? Hin.
  now case (in_app_or _ _ _ Hin) as [? | ?]; [left | right]; apply In_listVarInT_occurCheck.
- intros ? ? Hin.
  now case (in_app_or _ _ _ Hin) as [? | ?]; [left | right]; apply In_listVarInT_occurCheck.
- trivial.
- intro.
  now apply In_listVarInT_occurCheck.
Qed.

Lemma In_listVarInC_occurCheckC v c :
  In v (listVarInC c) -> occurCheckC v c.
Proof.
elim c; try trivial.
intros pc c' Hind Hin.
case (in_app_or _ _ _ Hin) as [Hint1 | Hint2]; [left | right].
- now apply In_listVarInPC_occurCheckPC.
- now apply Hind.
Qed.

Lemma listVarInEqLHSEq v t c:
  (listVarInEqLHS ((Var v == t) :: c)) = (v :: (listVarInEqLHS c)).
Proof.
trivial.
Qed.

Lemma listVarInT_nil_applySub sigma t :
  (listVarInT t = nil) -> applySubstitution sigma t = t.
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) -> (listVarInT t' = nil) -> applySubstitution sigma t' = t')).
enough (H : (forall n, (P n))).
  now apply (H (sizet t)).
intro n.
induction n as [ | n Hind].
- intros t' Hsizet_plus _.
  absurd (sizet t' <= 0); try assumption.
  now apply sizet_gte_1.
- intros t'.
  case t'.
  + intros v ? ?.
    absurd (nil = v :: nil); try apply nil_cons.
    now apply eq_sym.
  + intros t1 t2 Hsizet Hlistnil; simpl.
    enough (H : (applySubstitution sigma t1 = t1) /\ (applySubstitution sigma t2 = t2)).
       now inversion H as [->  ->].
    assert (H : incl (listVarInT t1) nil /\ incl (listVarInT t2) nil).
      apply incl_app_inv.
      simpl in Hlistnil; rewrite Hlistnil.
      now apply incl_nil_l.
    destruct H as [? ?].
    destruct (sizet_SetC Hsizet) as [? ?].
    split; apply Hind; try assumption.
    * now apply incl_l_nil.
    * now apply incl_l_nil.
  + intros s lt.
    elim lt; try trivial.
    intros t'' lt' Hind' Hsizet Hlistnil.
    assert (Hincl : incl (listVarInT t'') nil /\ incl (listVarInT (OTerm s lt')) nil).
      apply incl_app_inv.
      simpl; simpl in Hlistnil; rewrite Hlistnil.
      now apply incl_nil_l.
    destruct Hincl as [H1 H2].
    enough (H' : (applySubstitution sigma t'' = t'') /\ map (applySubstitution sigma) lt' = lt').
      simpl; now inversion H' as [->  ->].
    split.
    * apply Hind; try now apply incl_l_nil.
      apply (sizet_OTerm Hsizet).
      now apply in_eq.
    * enough (H : (s = s) /\ (map (applySubstitution sigma) lt' = lt')).
        now destruct H.
      apply OTerm_eq_iff.
      apply Hind'; try now apply incl_l_nil.
      simpl in Hsizet.
      rewrite plus_n_Sm in Hsizet.
      now apply (le_add_r _ _ Hsizet).
  + trivial.
Qed.

Lemma nIn_listVarInT_applySubstitution v t t' :
  ~ (In v (listVarInT t)) ->
    (applySubstitution ((v, t') :: nil) t) = t.
Proof.
set (P := fun (n : nat) => (forall t'', ((sizet t'') <= n) -> 
 ~ (In v (listVarInT t'')) -> (applySubstitution ((v, t') :: nil) t'' = t''))).
enough (H : (forall n, (P n))).
  now apply (H (sizet t)).
intro n.
induction n as [ | n Hind].
- intros t'' Hsizet_plus _.
  absurd (sizet t'' <= 0); try assumption.
  now apply sizet_gte_1.
- intros t''.
  case t''.
  + intros v' _.
    simpl; case (eq_variable_dec v' v) as [-> | ?]; try trivial.
    intro Hneg.
    now destruct (not_or _ _ Hneg).
  + intros t1 t2 Hsizet HnIn.
    destruct (sizet_SetC Hsizet) as [? ?].
    simpl in HnIn; destruct (neg_in_app _ _ _ HnIn) as [HnIn1 HnIn2].
    assert (Heq1 : applySubstitution ((v, t') :: nil) t1 = t1).
      now apply Hind.
    assert (Heq2 : applySubstitution ((v, t') :: nil) t2 = t2).
      now apply Hind.
    simpl; rewrite Heq1.
    now rewrite Heq2.
  + intros s lt.
    elim lt; try trivial.
    intros t''' lt' Hind' Hsizet HnIn.
    simpl in HnIn; destruct (neg_in_app _ _ _ HnIn) as [HnIn' HnIn''].
    assert (He : applySubstitution ((v, t') :: nil) t''' = t''').
      apply Hind; try assumption.
      apply (sizet_OTerm Hsizet).
      now apply in_eq.
    simpl; rewrite He.
    enough (He' : s = s /\ map (applySubstitution ((v, t') :: nil)) lt' = lt').
      now destruct He' as [_ ->].
    apply OTerm_eq_iff.
    enough (He' : applySubstitution ((v, t') :: nil) (OTerm s lt') = (OTerm s lt')).
      trivial.
    apply Hind'; try assumption.
    simpl in Hsizet.
    rewrite plus_n_Sm in Hsizet.
    now apply (le_add_r _ _ Hsizet).
  + trivial.
Qed.

Lemma InlistVarInEqLHScons v pc c :
  (In_list_log_variable v (listVarInEqLHS c) = true) ->
    In_list_log_variable v (listVarInEqLHS (pc :: c)) = true.
Proof.
intro Hin.
Ltac intros_H H := intros; exact H.
simpl.
case pc; try (intros_H Hin).
intros t1 t2.
case t1; try (intros_H Hin).
intros [j].
simpl; destruct v as [i].
now case (j =? i); [trivial | exact Hin].
Qed.

Lemma InlistVarInEqLHS v t c :
  In (Var v == t) c -> (In_list_log_variable v (listVarInEqLHS c) = true).
Proof.
induction c as [ | ? ? Hind]; try contradiction.
intro Hin.
case Hin as [-> | ?].
- rewrite listVarInEqLHSEq.
  destruct v as [i].
  simpl; now rewrite <- (beq_nat_refl i).
- apply InlistVarInEqLHScons.
  now apply Hind.
Qed.

Lemma listVarInC_app c1 c2 :
  listVarInC (c1 ++ c2) = listVarInC c1 ++ listVarInC c2.
Proof.
elim c1; try trivial.
intros ? ? Hind.
simpl; rewrite Hind.
now rewrite app_assoc.
Qed.

Lemma incl_ListVarInC (c1 c2 : constraint) :
  incl c1 c2 -> incl (listVarInC c1) (listVarInC c2).
Proof.
elim c1.
- intro; now apply incl_nil_l.
- intros pc c Hind Hincl.
  destruct (incl_cons_inv Hincl).
  apply incl_app; try now apply Hind.
  assert (Hc2eq: exists c1' c2', c2 = c1' ++ pc :: c2').
    apply in_split; apply Hincl; apply in_eq.
  destruct Hc2eq as [c1' [c2' Hc2eq]].
  rewrite Hc2eq.
  rewrite listVarInC_app.
  apply incl_appr.
  apply incl_appl.
  now apply incl_refl.
Qed.

Lemma In_listVarInEqLHS v c :
  In v (listVarInEqLHS c) <-> exists t, In (Var v == t) c.
Proof.
split.
- elim c; try contradiction.
  intros pc c' Hind.
  case pc.
  intros t1 t2.
    case t1.
    * intros v' Hin.
      case Hin as [<- | Hin].
      -- exists t2.
         now apply in_eq.
      -- destruct (Hind Hin) as [t ?].
         exists t; now right.
    * intros t3 t4 Hin.
      destruct (Hind Hin) as [t ?].
      exists t; now right.
    * intros s lt Hin.
      destruct (Hind Hin) as [t ?].
      exists t; now right.
    * intros Hin.
      destruct (Hind Hin) as [t ?].
      exists t; now right.
    * intros t1 t2 Hin.
      destruct (Hind Hin) as [t ?].
      exists t; now right.
    * intros t1 t2 Hin.
      destruct (Hind Hin) as [t ?].
      exists t; now right.
    * intros t1 t2 Hin.
      destruct (Hind Hin) as [t ?].
      exists t; now right.
    * intros Hin.
      destruct (Hind Hin) as [t ?].
      exists t; now right.
    * intros t' Hin.
      destruct (Hind Hin) as [t ?].
      exists t; now right.
- elim c.
  + intros [? ?].
    contradiction.
  + intros pc c' Hind.
    intros [t Hin].
    case Hin.
    * intros ->.
      simpl.
      now left.
    * intro Hinc'.
      simpl.
      case pc.
      -- intros t' ?.
         case t'; intros; try now apply Hind; exists t.
         right; now apply Hind; exists t.
      -- intros.
         now apply Hind; exists t.
      -- intros.
         now apply Hind; exists t.
      -- intros.
         now apply Hind; exists t.
      -- now apply Hind; exists t.
      -- intro.
         now apply Hind; exists t.
Qed.

Lemma incl_listVarInEqLHS c1 c2 :
  incl c1 c2 -> incl (listVarInEqLHS c1) (listVarInEqLHS c2).
Proof.
elim c1.
- intro; now apply incl_nil_l.
- intros pc c Hind Hincl.
  destruct (incl_cons_inv Hincl).
  simpl.
  revert H.
  case pc.
  + intros t1 t2.
    case t1; intros; try now apply Hind.
    apply incl_cons.
    * apply In_listVarInEqLHS.
      now exists t2.
    * now apply Hind.
  + intros; now apply Hind.
  + intros; now apply Hind.
  + intros; now apply Hind.
  + intro; now apply Hind.
  + intros; now apply Hind.
Qed.

Lemma incl_listVarNotInEqLHS_remove_r pc c :
  In pc c -> incl (listVarNotInEqLHS c) (listVarNotInEqLHS (pc :: remove eq_primc_dec pc c)).
Proof.
intro Hin.
apply incl_tran with (m := (remove_list eq_variable_dec (listVarInEqLHS (pc :: remove eq_primc_dec pc c)) (listVarInC c))).
- apply incl_remove_list_r.
  apply incl_listVarInEqLHS.
  now apply incl_remove_l.
- apply incl_remove_list_l.
  apply incl_ListVarInC.
  now apply incl_remove_r.
Qed.

Lemma incl_listVarNotInEqLHS_remove_l pc c :
  In pc c -> incl (listVarNotInEqLHS (pc :: remove eq_primc_dec pc c)) (listVarNotInEqLHS c).
Proof.
intro Hin.
unfold listVarNotInEqLHS.
apply incl_tran with (m := (remove_list eq_variable_dec (listVarInEqLHS (pc :: remove eq_primc_dec pc c)) (listVarInC c))).
- apply incl_remove_list_l.
  apply incl_ListVarInC.
  now apply incl_remove_l.
- apply incl_remove_list_r.
  apply incl_listVarInEqLHS.
  now apply incl_remove_r.
Qed.

Lemma nodup_listVarInC_eq v t c :
  isInSFPC (Var v == t) c ->
    nodup eq_variable_dec (listVarInC ((Var v == t) :: remove eq_primc_dec (Var v == t) c)) =
      v :: (nodup eq_variable_dec (listVarInT t ++ listVarInC (remove eq_primc_dec (Var v == t) c))).
Proof.
intro HinSFPC.
simpl.
case (in_dec eq_variable_dec v (listVarInT t ++ listVarInC (remove eq_primc_dec (Var v == t) c))).
- intro Hin.
  destruct HinSFPC as [Hnint Hninremove].
  case (in_app_or _ _ v Hin) as [Hin' | Hin'].
  + absurd (occurCheck v t); try assumption.
    now apply In_listVarInT_occurCheck.
  + absurd (occurCheckC v (remove eq_primc_dec (Var v == t) c)); try assumption.
    now apply In_listVarInC_occurCheckC.
- reflexivity.
Qed.

Lemma In_listVarNotInEqLHS v pc c :
  isInSFC c -> In pc c -> In v (listVarNotInEqLHS (pc :: nil)) ->
    In v (listVarNotInEqLHS c).
Proof.
intros HisInSFC HInpcc Hinvpc.
apply (incl_listVarNotInEqLHS_remove_l _ _ HInpcc).
apply in_remove_list.
assert (Hand : In v (listVarInC (pc :: nil)) /\ ~ In v (listVarInEqLHS (pc :: nil))).
  now apply (in_remove_list eq_variable_dec).
destruct Hand as [HIn HnIn].
assert (Hor : In v (listVarInPC pc) \/ In v nil).
  now apply in_app_iff.
split.
- apply in_or_app; left.
  case Hor; [trivial | contradiction].
- intro HIn2.
  assert (Hexists : (exists t : term, In (Var v == t) (pc :: remove eq_primc_dec pc c))).
    now apply In_listVarInEqLHS.
  destruct Hexists as [t HIn3].
  case (in_inv HIn3) as [Hpc_eq | HIn4].
  + rewrite Hpc_eq in HnIn.
    now destruct (not_or _ _ HnIn).
  + destruct (in_remove eq_primc_dec _ _ _ HIn4) as [? Hneq].
    assert (HisInSFPC : isInSFPC (Var v == t) c).
      now apply HisInSFC.
    destruct HisInSFPC.
    assert (In pc (remove eq_primc_dec (Var v == t) c)).
      apply in_in_remove; try assumption.
      intro Heq.
      rewrite Heq in Hneq.
      contradiction.
    enough (occurCheckC v (remove eq_primc_dec (Var v == t) c)).
      contradiction.
    apply in_occurCheckC with (pc:= pc); try assumption.
    apply In_listVarInPC_occurCheckPC.
    case Hor; [trivial | contradiction].
Qed.

Lemma listVarInT_remove_list t sigma :
  (forall t', In t' (map snd sigma) -> listVarInT t' = nil) ->
    listVarInT (applySubstitution sigma t) = remove_list eq_variable_dec (map fst sigma) (listVarInT t).
Proof.
intro HVarNil.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
    listVarInT (applySubstitution sigma t') = remove_list eq_variable_dec (map fst sigma) (listVarInT t'))).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  absurd (sizet t' <= 0); try assumption.
  now apply sizet_gte_1.
- intro t'.
  case t'.
  + intros v Hsize.
    simpl.
    case (in_dec eq_variable_dec v (map fst sigma)) as [HIn | HnIn].
    * destruct (find_exists_some eq_variable_dec _ _ HIn) as [t'' [HInt'' ->]].
      rewrite (HVarNil _ HInt'').
      apply eq_sym.
      apply remove_list_eq_nil.
      intros v' HInv'.
      enough (Heq : v' = v).
        now rewrite Heq.
      now case (in_inv HInv') as [-> | Habs]; [reflexivity | contradiction].
    * rewrite (find_none _ _ _ HnIn).
      apply eq_sym.
      now rewrite (remove_list_length_1 eq_variable_dec _ _ HnIn).
  + intros t1 t2 Hsizet.
    destruct (sizet_SetC Hsizet) as [Hsizet1 Hsizet2].
    simpl; rewrite (Hind _ Hsizet1).
    rewrite (Hind _ Hsizet2).
    now rewrite remove_list_app.
  + intros s lt.
    elim lt.
    -- intros ?.
       now rewrite remove_list_nil.
    -- intros t'' lt' Hind' HsizetOT.
       simpl; rewrite remove_list_app.
       assert (Hsizet'' : sizet t'' <= n).
         simpl in HsizetOT.
         rewrite <- plus_Sn_m in HsizetOT.
         apply le_S_n.
         now apply (le_add_l _ _ HsizetOT).
       rewrite (Hind _ Hsizet'').
       enough (H : listVarInT (applySubstitution sigma (OTerm s lt')) =
                   remove_list eq_variable_dec (map fst sigma) (listVarInT (OTerm s lt'))).
         simpl in H.
         now rewrite H.
       apply Hind.
       simpl; rewrite S_eq.
       apply le_S_n.
       apply le_trans with (m := sizet (OTerm s (t'' :: lt'))); try assumption.
       simpl; apply le_n_S.
       rewrite Nat.add_comm.
       apply plus_le_compat; [apply le_1_sizet | apply le_n].
  + now simpl; rewrite remove_list_nil.
Qed.

Lemma listVarInT_remove_list_r t sigma :
  (forall p, In p sigma -> In (fst p) (listVarInT t) -> listVarInT (snd p) = nil) ->
    listVarInT (applySubstitution sigma t)
    = remove_list eq_variable_dec (map fst sigma) (listVarInT t).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
    (forall p, In p sigma -> In (fst p) (listVarInT t') -> listVarInT (snd p) = nil) ->
    listVarInT (applySubstitution sigma t') = remove_list eq_variable_dec (map fst sigma) (listVarInT t'))).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  absurd (sizet t' <= 0); try assumption.
  now apply sizet_gte_1.
- intro t'.
  case t'.
  + intros v Hsize HVarnil.
    simpl; case (in_dec eq_variable_dec v (map fst sigma)) as [HIn | HnIn].
    * destruct (find_exists_some_r eq_variable_dec _ _ HIn) as [[v' t''] [HpIn [Heq ->]]].
      rewrite HVarnil; try assumption.
      apply eq_sym.
      apply remove_list_eq_nil.
      now apply incl_cons; [assumption | apply incl_nil_l].
      now rewrite Heq; left.
    * rewrite (find_none eq_variable_dec _ _ HnIn).
      revert HnIn.
      elim sigma; try trivial.
      intros p sigma' Hind' HnIn.
      simpl in HnIn.
      destruct (not_or _ _ HnIn) as [Hneq HnIn'].
      simpl; rewrite <- (Hind' HnIn').
      now simpl; case (eq_variable_dec (fst p) v); [contradiction | reflexivity].
  + intros t1 t2 Hsizet HVarnil.
    destruct (sizet_SetC Hsizet) as [Hsizet1 Hsizet2].
    simpl; rewrite (Hind _ Hsizet1).
    rewrite (Hind _ Hsizet2).
    now rewrite remove_list_app.
    intros p HIn HInfst.
    apply HVarnil; try assumption.
    now apply in_app_iff; right.
    intros p HIn HInfst.
    apply HVarnil; try assumption.
    now apply in_app_iff; left.
  + intros s lt.
    elim lt.
    * now rewrite remove_list_nil.
    * intros t'' lt' Hind' HsizetOT HVarnil.
      simpl; rewrite remove_list_app.
      assert (Hsizet'' : sizet t'' <= n).
        simpl in HsizetOT.
        rewrite <- plus_Sn_m in HsizetOT.
        apply le_S_n.
        now apply (le_add_l _ _ HsizetOT).
      rewrite (Hind _ Hsizet'').
      enough (H : listVarInT (applySubstitution sigma (OTerm s lt')) =
                   remove_list eq_variable_dec (map fst sigma) (listVarInT (OTerm s lt'))).
        simpl in H.
        now rewrite H.
      apply Hind.
      simpl; rewrite S_eq.
      apply le_S_n.
      apply le_trans with (m := sizet (OTerm s (t'' :: lt'))); try assumption.
      simpl; apply le_n_S.
      rewrite Nat.add_comm.
      apply plus_le_compat; [apply le_1_sizet | apply le_n].
      intros p HIn HInfst.
      apply HVarnil; try assumption.
      now apply in_app_iff; right.
      intros p HIn HInfst.
      apply HVarnil; try assumption.
      now apply in_app_iff; left.
  + now rewrite remove_list_nil.
Qed.

Lemma listVarInPC_remove_list pc sigma :
  (forall t', In t' (map snd sigma) -> listVarInT t' = nil) ->
    listVarInPC (applySubstitutionToPC sigma pc)
    = remove_list eq_variable_dec (map fst sigma) (listVarInPC pc).
Proof.
intro HVarNil.
case pc; intros; simpl; try do 2 rewrite (listVarInT_remove_list _ _ HVarNil).
- now rewrite remove_list_app.
- now rewrite remove_list_app.
- now rewrite remove_list_app.
- now rewrite remove_list_app.
- now rewrite remove_list_nil.
- now rewrite (listVarInT_remove_list _ _ HVarNil).
Qed.

Lemma listVarInC_remove_list c sigma :
  (forall t', In t' (map snd sigma) -> listVarInT t' = nil) ->
    listVarInC (applySubstitutionToC sigma c)
    = remove_list eq_variable_dec (map fst sigma) (listVarInC c).
Proof.
intro HVarNil.
elim c.
- simpl; now rewrite remove_list_nil.
- intros pc c' Hind.
  simpl; rewrite Hind.
  rewrite remove_list_app.
  now rewrite (listVarInPC_remove_list _ _ HVarNil).
Qed.

Lemma neq_listVarInT_applySub v t1 t2 sigma :
  ~ In v (listVarInT t2) ->
    applySubstitution ((v, t1) :: sigma) t2 = applySubstitution sigma t2.
Proof.
intro HnIn.
set (P := fun (n : nat) => (forall t, ((sizet t) <= n) ->
  ~ In v (listVarInT t) ->
    applySubstitution ((v, t1) :: sigma) t = applySubstitution sigma t)).
enough (H : (forall n, (P n))).
  apply (H (sizet t2)); try assumption.
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t ? ?.
  absurd (sizet t <= 0); try assumption.
  now apply sizet_gte_1.
- intros t.
  case t.
  + intros v' Hsizet HnIn'.
    simpl in HnIn'.
    destruct (not_or _ _ HnIn') as [Hneq _].
    now simpl; case (eq_variable_dec v' v) as [Heq | Hneq']; [contradiction | reflexivity].
  + intros t3 t4 Hsizet HnIn'.
    destruct (sizet_SetC Hsizet) as [Hsizet3 Hsizet4].
    destruct (neg_in_app _ _ _ HnIn') as [HnIn3 HnIn4].
    simpl; rewrite (Hind _ Hsizet3 HnIn3).
    now rewrite (Hind _ Hsizet4 HnIn4).
  + intros s lt.
    elim lt; try reflexivity.
    intros t' lt' Hind' Hsizet HnIn'.
    assert (Hsizet' : sizet t' <= n).
      simpl in Hsizet.
      rewrite <- plus_Sn_m in Hsizet.
      apply le_S_n.
      now apply (le_add_l _ _ Hsizet).
    assert (Hsizelt' : sizet (OTerm s lt') <= S n).
      apply le_trans with (m := sizet (OTerm s (t' :: lt'))); try assumption.
      simpl; apply le_n_S.
      now apply le_plus_r.
    destruct (neg_in_app _ _ _ HnIn') as [HnInt' HnInlt'].
    simpl; rewrite (Hind _ Hsizet' HnInt').
    enough (H : applySubstitution ((v, t1) :: sigma) (OTerm s lt') =
        applySubstitution sigma (OTerm s lt')).
      simpl in H.
      now inversion H.
    now rewrite (Hind' Hsizelt' HnInlt').
  + reflexivity.
Qed.

Lemma neq_listVarInPC_applySub v t pc sigma :
  ~ In v (listVarInPC pc) ->
    applySubstitutionToPC ((v, t) :: sigma) pc = applySubstitutionToPC sigma pc.
Proof.
case pc.
- intros t1 t2 HnIn.
  destruct (neg_in_app _ _ _ HnIn) as [HnIn1 HnIn2].
  simpl; rewrite (neq_listVarInT_applySub _ _ _ _ HnIn1).
  now rewrite (neq_listVarInT_applySub _ _ _ _ HnIn2).
- intros t1 t2 HnIn.
  destruct (neg_in_app _ _ _ HnIn) as [HnIn1 HnIn2].
  simpl; rewrite (neq_listVarInT_applySub _ _ _ _ HnIn1).
  now rewrite (neq_listVarInT_applySub _ _ _ _ HnIn2).
- intros t1 t2 HnIn.
  destruct (neg_in_app _ _ _ HnIn) as [HnIn1 HnIn2].
  simpl; rewrite (neq_listVarInT_applySub _ _ _ _ HnIn1).
  now rewrite (neq_listVarInT_applySub _ _ _ _ HnIn2).
- intros t1 t2 HnIn.
  destruct (neg_in_app _ _ _ HnIn) as [HnIn1 HnIn2].
  simpl; rewrite (neq_listVarInT_applySub _ _ _ _ HnIn1).
  now rewrite (neq_listVarInT_applySub _ _ _ _ HnIn2).
- now intros HnIn; simpl.
- intros t' HnIn; simpl.
  now rewrite neq_listVarInT_applySub; [reflexivity | assumption].
Qed.

Lemma neq_listVarInC_applySub v t c sigma :
  ~ In v (listVarInC c) ->
    applySubstitutionToC ((v, t) :: sigma) c = applySubstitutionToC sigma c.
Proof.
elim c; try reflexivity.
intros pc c' Hind HnIn.
destruct (neg_in_app _ _ _ HnIn) as [HnInpc HnInc'].
simpl; rewrite (neq_listVarInPC_applySub _ _ _ _ HnInpc).
now rewrite (Hind HnInc').
Qed.

Lemma listVarInT_applySub_nil t sigma :
  listVarInT (applySubstitution sigma t) = nil ->
    (forall v, In v (listVarInT t) -> listVarInT (applySubstitution sigma (Var v)) = nil).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
  listVarInT (applySubstitution sigma t') = nil ->
    (forall v, In v (listVarInT t') -> listVarInT (applySubstitution sigma (Var v)) = nil))).
enough (H : (forall n, (P n))).
  apply (H (sizet t)); try assumption.
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ? ?.
  absurd (sizet t' <= 0); try assumption.
  now apply sizet_gte_1.
- intros t'.
  case t'.
  + intros v ? ? v' Hin.
    now case Hin as [-> | ?]; [assumption | contradiction].
  + intros t1 t2 Hsizet Hnil v HIn.
    destruct (sizet_SetC Hsizet) as [Hsizet1 Hsizet2].
    simpl in Hnil.
    destruct (app_eq_nil _ _ Hnil) as [Hnil1 Hnil2].
    simpl in HIn.
    now case (in_app_or _ _ _ HIn) as [Hin1 | Hin2]; [apply (Hind t1) | apply (Hind t2)].
  + intros s lt.
    elim lt; try contradiction.
    intros t'' lt' Hind' Hsizet Hnil v HIn.
    simpl in Hnil.
    destruct (app_eq_nil _ _ Hnil) as [Hnil'' Hnil'].
    simpl in HIn.
    case (in_app_or _ _ _ HIn) as [Hin'' | Hin'].
    * apply (Hind t''); try assumption.
      simpl in Hsizet.
      rewrite <- plus_Sn_m in Hsizet.
      apply le_S_n.
      now apply (le_add_l _ _ Hsizet).
    * apply (Hind (OTerm s lt')); try assumption.
      simpl; rewrite S_eq.
      apply le_S_n.
      apply le_trans with (m := sizet (OTerm s (t'' :: lt'))); try assumption.
      simpl; apply le_n_S.
      rewrite Nat.add_comm.
      now apply plus_le_compat; [apply le_1_sizet | apply le_n].
  + contradiction.
Qed.

Lemma listVarInPC_applySub_nil pc sigma :
  listVarInPC (applySubstitutionToPC sigma pc) = nil ->
    (forall v, In v (listVarInPC pc) -> listVarInT (applySubstitution sigma (Var v)) = nil).
Proof.
case pc.
- intros t1 t2 Hnil v HIn.
  simpl in Hnil.
  destruct (app_eq_nil _ _ Hnil) as [Hnil1 Hnil2].
  simpl in HIn.
  now case (in_app_or _ _ _ HIn) as [HIn1 | HIn2];
    [apply (listVarInT_applySub_nil _ _ Hnil1) | apply (listVarInT_applySub_nil _ _ Hnil2)].
- intros t1 t2 Hnil v HIn.
  simpl in Hnil.
  destruct (app_eq_nil _ _ Hnil) as [Hnil1 Hnil2].
  simpl in HIn.
  now case (in_app_or _ _ _ HIn) as [HIn1 | HIn2];
    [apply (listVarInT_applySub_nil _ _ Hnil1) | apply (listVarInT_applySub_nil _ _ Hnil2)].
- intros t1 t2 Hnil v HIn.
  simpl in Hnil.
  destruct (app_eq_nil _ _ Hnil) as [Hnil1 Hnil2].
  simpl in HIn.
  now case (in_app_or _ _ _ HIn) as [HIn1 | HIn2];
    [apply (listVarInT_applySub_nil _ _ Hnil1) | apply (listVarInT_applySub_nil _ _ Hnil2)].
- intros t1 t2 Hnil v HIn.
  simpl in Hnil.
  destruct (app_eq_nil _ _ Hnil) as [Hnil1 Hnil2].
  simpl in HIn.
  now case (in_app_or _ _ _ HIn) as [HIn1 | HIn2];
    [apply (listVarInT_applySub_nil _ _ Hnil1) | apply (listVarInT_applySub_nil _ _ Hnil2)].
- intros _ v.
  contradiction.
- intros ? Hnil ? ?.
  now apply (listVarInT_applySub_nil _ _ Hnil).
Qed.

Lemma listVarInC_applySub_nil c sigma :
  listVarInC (applySubstitutionToC sigma c) = nil ->
    (forall v, In v (listVarInC c) -> listVarInT (applySubstitution sigma (Var v)) = nil).
Proof.
elim c.
- intros _ v.
  contradiction.
- intros pc c' Hind Neqnil v HIn.
  simpl in Neqnil.
  destruct (app_eq_nil _ _ Neqnil) as [Hpc H'].
  simpl in HIn.
  case (in_app_or _ _ _ HIn) as [? | ?].
  + now apply (listVarInPC_applySub_nil _ _ Hpc).
  + now apply Hind.
Qed.

Lemma app_applySub sigma1 sigma2 t :
  incl (listVarInT t) (map fst sigma1) ->
    (applySubstitution (sigma1 ++ sigma2) t) = (applySubstitution sigma1 t).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
  incl (listVarInT t') (map fst sigma1) ->
    (applySubstitution (sigma1 ++ sigma2) t') = (applySubstitution sigma1 t'))).
enough (H : (forall n, (P n))).
  now apply (H (sizet t)); try assumption.
intro n.
induction n as [ | n Hind].
- intros t' ? ?.
  absurd (sizet t' <= 0); try assumption.
  now apply sizet_gte_1.
- intros t1.
  case t1.
  + intros v Hsizet Hincl.
    simpl in Hincl.
    destruct (incl_cons_inv Hincl) as [HIn _].
    revert HIn.
    elim sigma1; try contradiction.
    intros p sigma Hind1 HIn.
    destruct p as [v1 ?].
    simpl in HIn.
    case HIn as [-> | HIn].
    * simpl; now case (eq_variable_dec v v); [reflexivity | contradiction].
    * simpl; case (eq_variable_dec v v1) as [_ | _]; try reflexivity.
      enough (He : applySubstitution (sigma ++ sigma2) (Var v) = applySubstitution sigma (Var v)).
        now simpl in He.
      now rewrite Hind1.
  + intros t2 t3 Hsizet Hincl.
    destruct (sizet_SetC Hsizet) as [Hsizet2 Hsizet3].
    simpl in Hincl.
    destruct (incl_app_inv _ _ Hincl) as [Hincl2 Hincl3].
    simpl; rewrite (Hind _ Hsizet2 Hincl2).
    now rewrite (Hind _ Hsizet3 Hincl3).
  + intros s lt.
    elim lt; try reflexivity.
    intros t2 lt2 Hind2 Hsizet Hincl.
    simpl in Hincl.
    destruct (incl_app_inv _ _ Hincl) as [Hincl2 Hinclt2].
    assert (Hsizet2 : sizet t2 <= n).
      simpl in Hsizet.
      rewrite <- plus_Sn_m in Hsizet.
      apply le_S_n.
      now apply (le_add_l _ _ Hsizet).
    simpl; rewrite (Hind _ Hsizet2 Hincl2).
    enough (He : map (applySubstitution (sigma1 ++ sigma2)) lt2 = map (applySubstitution sigma1) lt2).
      now rewrite He.
    apply map_ext_in_iff.
    intros t3 HIn.
    rewrite Hind; try reflexivity.
    * apply (sizet_OTerm Hsizet).
      now apply in_cons.
    * revert HIn Hinclt2.
      elim lt2; try contradiction.
      intros t4 lt4 Hind4 HIn Hincl4.
      destruct (incl_app_inv _ _ Hincl4) as [? ?].
      case HIn as [-> | ?]; try assumption.
      now apply Hind4.
  + reflexivity.
Qed.

Lemma app_applySubToPC sigma1 sigma2 pc :
  incl (listVarInPC pc) (map fst sigma1) ->
    (applySubstitutionToPC (sigma1 ++ sigma2) pc) = (applySubstitutionToPC sigma1 pc).
Proof.
case pc.
- intros t1 t2 Hincl.
  simpl in Hincl.
  destruct (incl_app_inv _ _ Hincl) as [Hincl1 Hincl2].
  simpl; rewrite (app_applySub _ _ _ Hincl1).
  now rewrite (app_applySub _ _ _ Hincl2).
- intros t1 t2 Hincl.
  simpl in Hincl.
  destruct (incl_app_inv _ _ Hincl) as [Hincl1 Hincl2].
  simpl; rewrite (app_applySub _ _ _ Hincl1).
  now rewrite (app_applySub _ _ _ Hincl2).
- intros t1 t2 Hincl.
  simpl in Hincl.
  destruct (incl_app_inv _ _ Hincl) as [Hincl1 Hincl2].
  simpl; rewrite (app_applySub _ _ _ Hincl1).
  now rewrite (app_applySub _ _ _ Hincl2).
- intros t1 t2 Hincl.
  simpl in Hincl.
  destruct (incl_app_inv _ _ Hincl) as [Hincl1 Hincl2].
  simpl; rewrite (app_applySub _ _ _ Hincl1).
  now rewrite (app_applySub _ _ _ Hincl2).
- reflexivity.
- intros t Hincl.
  now simpl; rewrite (app_applySub _ _ _ Hincl).
Qed.

Lemma app_applySubToC sigma1 sigma2 c :
  incl (listVarInC c) (map fst sigma1) ->
    (applySubstitutionToC (sigma1 ++ sigma2) c) = (applySubstitutionToC sigma1 c).
Proof.
elim c; try reflexivity.
intros pc c' Hind Hincl.
simpl in Hincl; destruct (incl_app_inv _ _ Hincl) as [Hincl1 Hincl2].
simpl; rewrite (Hind Hincl2).
now rewrite (app_applySubToPC _ _ _ Hincl1).
Qed.

Lemma listVar_applySub_incl sigma t :
  (listVarInT (applySubstitution sigma t)) = nil ->
    incl (listVarInT t) (map fst sigma).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
  (listVarInT (applySubstitution sigma t')) = nil ->
    incl (listVarInT t') (map fst sigma))).
enough (H : (forall n, (P n))).
  now apply (H (sizet t)); try assumption.
intro n.
induction n as [ | n Hind].
- intros t' ? ?.
  absurd (sizet t' <= 0); try assumption.
  now apply sizet_gte_1.
- intros t1.
  case t1.
  + intros v Hsizet.
    elim sigma.
    * simpl; intros ->.
      now apply incl_refl.
    * intros [v2 t2] sigma' Hind'.
      simpl; case (eq_variable_dec v v2) as [-> | _].
      -- intros _ v3 HIn.
         case HIn as [-> |]; try contradiction.
         now left.
      -- intros Hnil.
         apply incl_tl.
         now apply Hind'.
  + intros t2 t3 Hsizet Hnil.
    destruct (sizet_SetC Hsizet) as [Hsizet2 Hsizet3].
    simpl in Hnil.
    destruct (app_eq_nil _ _ Hnil) as [Hnil2 Hnil3].
    apply incl_app; [apply (Hind _ Hsizet2 Hnil2) | apply (Hind _ Hsizet3 Hnil3)].
  + intros s lt.
    elim lt.
    * now intros; apply incl_nil_l.
    * intros t2 lt2 Hind2 Hsizet Hnil.
      simpl in Hnil.
      destruct (app_eq_nil _ _ Hnil) as [Hnil2 Hnilt2].
      assert (Hsizet2 : sizet t2 <= n).
      simpl in Hsizet.
      rewrite <- plus_Sn_m in Hsizet.
      apply le_S_n.
      now apply (le_add_l _ _ Hsizet).
      simpl; apply incl_app; try now apply (Hind _ Hsizet2 Hnil2).
      apply Hind2; try now simpl.
      apply le_trans with (m := sizet (OTerm s (t2 :: lt2))); try assumption.
      simpl; apply le_n_S.
      now apply le_plus_r.
  + now intros; apply incl_nil_l.
Qed.

Lemma listVar_applySubToPC_incl sigma pc :
  (listVarInPC (applySubstitutionToPC sigma pc)) = nil ->
    incl (listVarInPC pc) (map fst sigma).
Proof.
case pc.
- intros t1 t2 Hnil.
  simpl in Hnil.
  destruct (app_eq_nil _ _ Hnil) as [Hnil1 Hnil2].
  now simpl; apply incl_app; try apply listVar_applySub_incl.
- intros t1 t2 Hnil.
  simpl in Hnil.
  destruct (app_eq_nil _ _ Hnil) as [Hnil1 Hnil2].
  now simpl; apply incl_app; try apply listVar_applySub_incl.
- intros t1 t2 Hnil.
  simpl in Hnil.
  destruct (app_eq_nil _ _ Hnil) as [Hnil1 Hnil2].
  now simpl; apply incl_app; try apply listVar_applySub_incl.
- intros t1 t2 Hnil.
  simpl in Hnil.
  destruct (app_eq_nil _ _ Hnil) as [Hnil1 Hnil2].
  now simpl; apply incl_app; try apply listVar_applySub_incl.
- intro; now apply incl_nil_l.
- intros t.
  now apply listVar_applySub_incl.
Qed.

Lemma listVar_applySubToC_incl sigma c :
  (listVarInC (applySubstitutionToC sigma c)) = nil ->
    incl (listVarInC c) (map fst sigma).
Proof.
elim c.
- intro; now apply incl_nil_l.
- intros pc c' Hind Hnil.
  simpl in Hnil;
  destruct (app_eq_nil _ _ Hnil) as [Hnilpc Hnilc'].
  simpl; apply incl_app.
  + now apply listVar_applySubToPC_incl.
  + now apply Hind.
Qed.

Lemma listVar_applySub_nil t sigma :
  NoDup (map fst sigma) -> listVarInT (applySubstitution sigma t) = nil ->
    (forall p, In p sigma -> In (fst p) (listVarInT t) -> listVarInT (snd p) = nil).
Proof.
intro HNoDup.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
  (listVarInT (applySubstitution sigma t')) = nil ->
    (forall p, In p sigma -> In (fst p) (listVarInT t') -> listVarInT (snd p) = nil))).
enough (H : (forall n, (P n))).
  now apply (H (sizet t)); try assumption.
intro n.
induction n as [ | n Hind].
- intros t' ? ?.
  now absurd (sizet t' <= 0); [apply sizet_gte_1 | assumption].
- intros t1.
  case t1.
  + intros v Hsizet Hnil p HInp HInfst.
    case HInfst as [Hfst_eq |]; try contradiction.
    enough (He : applySubstitution sigma (Var v) = snd p).
      now rewrite <- He.
    assert (Hexist : exists sigma1 sigma2, sigma = sigma1 ++ p :: sigma2).
      now apply in_split.
    destruct p as [v' t'].
    simpl in Hfst_eq.
    destruct Hexist as [sigma1 [sigma2 ->]].
    rewrite Hfst_eq.
    now simpl; rewrite NoDup_find.
  + intros t2 t3 Hsizet Hnil p HInp HInfst.
    destruct (sizet_SetC Hsizet) as [Hsizet2 Hsizet3].
    simpl in Hnil.
    destruct (app_eq_nil _ _ Hnil) as [Hnil2 Hnil3].
    simpl in HInfst.
    case (in_app_or _ _ _ HInfst) as [HIn2 | HIn3].
    * now apply (Hind t2).
    * now apply (Hind t3).
  + intros s lt.
    elim lt.
    * contradiction.
    * intros t2 lt2 Hind2 Hsizet Hnil p HInp HInfst.
      simpl in Hnil.
      destruct (app_eq_nil _ _ Hnil) as [Hnil2 Hnilt2].
      simpl in HInfst.
      case (in_app_or _ _ _ HInfst) as [HIn2 | HInlt2].
      -- apply (Hind t2); try assumption.
         simpl in Hsizet.
         rewrite <- plus_Sn_m in Hsizet.
         apply le_S_n.
         now apply (le_add_l _ _ Hsizet).
      -- apply (Hind (OTerm s lt2)); try assumption.
         simpl; rewrite S_eq.
         apply le_S_n.
         apply le_trans with (m := sizet (OTerm s (t2 :: lt2))); try assumption.
         simpl; apply le_n_S.
         rewrite Nat.add_comm.
         apply plus_le_compat; [apply le_1_sizet | apply le_n].
  + contradiction.
Qed.

Lemma listVar_applySubToPC_nil pc sigma :
  NoDup (map fst sigma) -> listVarInPC (applySubstitutionToPC sigma pc) = nil ->
    (forall p, In p sigma -> In (fst p) (listVarInPC pc) -> listVarInT (snd p) = nil).
Proof.
intro HNoDup.
case pc.
- intros t1 t2 HlistVnil p HInp HInfst.
  simpl in HlistVnil.
  destruct (app_eq_nil _ _ HlistVnil) as [Hnil1 Hnil2].
  simpl in HInfst.
  case (in_app_or _ _ _ HInfst) as [HIn1 | HIn2].
  + now apply (listVar_applySub_nil t1 sigma).
  + now apply (listVar_applySub_nil t2 sigma).
- intros t1 t2 HlistVnil p HInp HInfst.
  simpl in HlistVnil.
  destruct (app_eq_nil _ _ HlistVnil) as [Hnil1 Hnil2].
  simpl in HInfst.
  case (in_app_or _ _ _ HInfst) as [HIn1 | HIn2].
  + now apply (listVar_applySub_nil t1 sigma).
  + now apply (listVar_applySub_nil t2 sigma).
- intros t1 t2 HlistVnil p HInp HInfst.
  simpl in HlistVnil.
  destruct (app_eq_nil _ _ HlistVnil) as [Hnil1 Hnil2].
  simpl in HInfst.
  case (in_app_or _ _ _ HInfst) as [HIn1 | HIn2].
  + now apply (listVar_applySub_nil t1 sigma).
  + now apply (listVar_applySub_nil t2 sigma).
- intros t1 t2 HlistVnil p HInp HInfst.
  simpl in HlistVnil.
  destruct (app_eq_nil _ _ HlistVnil) as [Hnil1 Hnil2].
  simpl in HInfst.
  case (in_app_or _ _ _ HInfst) as [HIn1 | HIn2].
  + now apply (listVar_applySub_nil t1 sigma).
  + now apply (listVar_applySub_nil t2 sigma).
- contradiction.
- intros t HlistVnil p HInp HInfst.
  now apply (listVar_applySub_nil t sigma).
Qed.

Lemma listVar_applySubToC_nil c sigma :
  NoDup (map fst sigma) -> listVarInC (applySubstitutionToC sigma c) = nil ->
    (forall p, In p sigma -> In (fst p) (listVarInC c) -> listVarInT (snd p) = nil).
Proof.
intro HNoDup.
elim c; try contradiction.
intros pc c' Hind HlistVnil p HInp HInfst.
simpl in HlistVnil.
destruct (app_eq_nil _ _ HlistVnil) as [Hpcnil Hc'nil].
simpl in HInfst.
case (in_app_or _ _ _ HInfst) as [HInpc | HInc'].
- now apply (listVar_applySubToPC_nil _ _ HNoDup Hpcnil).
- now apply Hind.
Qed.

Lemma listVarInT_listSetC t lt :
  lt <> nil -> incl (listVarInT t) (listVarInT (listSetC lt t)).
Proof.
set (P := fun (n : nat) => (forall t1 lt1, ((length lt1) <= n) ->
                            lt1 <> nil -> incl (listVarInT t1) (listVarInT (listSetC lt1 t1)))).
enough (H : (forall n, (P n))).
  now apply (H (length lt)); try assumption.
intro n.
induction n as [ | n Hind]; intros t1 lt1.
- intros Hlength Hneq_nil.
  absurd (lt1 = nil); try assumption.
  apply length_zero_iff_nil.
  now apply Nat.le_0_r.
- elim lt1; try contradiction.
  intros t2 lt2.
  simpl.
  elim lt2.
  + intros ? ? _.
    now apply incl_appr.
  + intros t3 lt3 ? ? ? _.
    apply incl_appr.
    apply Hind; try now apply le_S_n.
    intro Habs.
    absurd (nil = t3 :: lt3); try now apply eq_sym.
    now apply nil_cons.
Qed.

Lemma listVarInListT_listSetC lt t :
  lt <> nil -> incl (listVarInListT lt) (listVarInT (listSetC lt t)).
Proof.
set (P := fun (n : nat) => (forall t1 lt1, ((length lt1) <= n) ->
                            lt1 <> nil -> incl (listVarInListT lt1) (listVarInT (listSetC lt1 t1)))).
enough (H : (forall n, (P n))).
  now apply (H (length lt)); try assumption.
intro n.
induction n as [ | n Hind]; intros t1 lt1.
- intros Hlength Hneq_nil.
  absurd (lt1 = nil); try assumption.
  apply length_zero_iff_nil.
  now apply Nat.le_0_r.
- elim lt1; try contradiction.
  intros t2 lt2.
  simpl; elim lt2.
  + intros ? ? _.
    rewrite app_nil_r.
    now apply incl_appl.
  + intros t3 lt3 ? ? ? _.
    apply incl_app_app; try now apply incl_refl.
    apply Hind; try now apply le_S_n.
    intro Habs.
    absurd (nil = t3 :: lt3); try now apply eq_sym.
    now apply nil_cons.
Qed.

Lemma listSetC_listVarInListT lt t :
  incl (listVarInT (listSetC lt t)) (listVarInListT lt ++ listVarInT t).
Proof.
set (P := fun (n : nat) => (forall t1 lt1, ((length lt1) <= n) ->
                            incl (listVarInT (listSetC lt1 t1)) (listVarInListT lt1 ++ listVarInT t1))).
enough (H : (forall n, (P n))).
  now apply (H (length lt)); try assumption.
intro n.
induction n as [ | n Hind]; intros t1 lt1.
- intros Hlength.
  assert (Heq_nil : lt1 = nil).
    apply length_zero_iff_nil.
    now apply Nat.le_0_r.
  now rewrite Heq_nil.
- elim lt1; try now intro; apply incl_nil_l.
  intros t2 lt2.
  simpl; elim lt2; try now intros ? ?.
  intros t3 lt3 ? ?.
  simpl; rewrite app_assoc_reverse.
  apply incl_app_app; try now apply incl_refl.
  apply Hind.
  now apply le_S_n.
Qed.

Lemma listVarIn_listSetC_nil lt t :
  lt <> nil ->
    listVarInT (listSetC lt t) = nil <-> ((forall t', In t' lt -> listVarInT t' = nil) /\
                                          (listVarInT t = nil)).
Proof.
intro Hneq_nil.
split.
- intro Hnil.
  split.
  + apply listVarInListT_eq_nil.
    apply incl_l_nil.
    apply incl_tran with (m := (listVarInT (listSetC lt t))); try now apply listVarInListT_listSetC.
    now rewrite Hnil.
  + apply incl_l_nil.
    apply incl_tran with (m := (listVarInT (listSetC lt t))); try now apply listVarInT_listSetC.
    now rewrite Hnil.
- intros [Hforall Hnil_t].
  apply incl_l_nil.
  apply incl_tran with (m := (listVarInListT lt ++ listVarInT t)); try now apply listSetC_listVarInListT.
  rewrite Hnil_t.
  rewrite app_nil_r.
  enough (He : (listVarInListT lt) = nil).
    now rewrite He.
  now apply listVarInListT_eq_nil.
Qed.

Lemma listVarIn_OTerm s lt1 lt2 sigma :
  length lt1 = length lt2 ->
    incl (listVarInPC (applySubstitutionToPC sigma (OTerm s lt1 == OTerm s lt2)))
         (listVarInC (applySubstitutionToC sigma (map2 buildEq lt1 lt2))).
Proof.
set (P := fun (n : nat) => (forall lt1' lt2', ((length lt1') <= n) ->
    length lt1' = length lt2' ->
      incl (listVarInPC (applySubstitutionToPC sigma (OTerm s lt1' == OTerm s lt2')))
         (listVarInC (applySubstitutionToC sigma (map2 buildEq lt1' lt2'))))).
enough (H : (forall n, (P n))).
  apply (H (length lt1)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros lt1' lt2' Hlength_lt Hlength_eq.
  enough (Hnil : (lt1' = nil) /\ (lt2' = nil)).
    destruct Hnil as [-> ->].
    now apply incl_refl.
  split; apply length_zero_iff_nil; try now apply Nat.le_0_r.
  rewrite <- Hlength_eq.
  now apply Nat.le_0_r.
- intros lt1' lt2'.
  elim lt1'.
  + intros _ Hlength_eq.
    enough (Hnil : lt2' = nil).
      rewrite Hnil.
      now apply incl_refl.
    apply length_zero_iff_nil.
    now rewrite <- Hlength_eq.
  + intros t1 lt1''.
    elim lt2'.
    * intros _ _ Habs.
      absurd (S (length lt1'') = 0); try assumption.
      now apply Nat.neq_succ_0.
    * intros t2 lt2'' _ _ ? ?.
      assert (Hincl : incl (listVarInPC (applySubstitutionToPC sigma (OTerm s lt1'' == OTerm s lt2'')))
                           (listVarInC (applySubstitutionToC sigma (map2 buildEq lt1'' lt2'')))).
        now apply Hind; [apply le_S_n | apply eq_add_S].
      destruct (incl_app_inv _ _ Hincl).
      simpl; apply incl_app.
      -- apply incl_app; try now do 2 apply incl_appl.
         now apply incl_appr.
      -- apply incl_app; try now apply incl_appl; apply incl_appr.
         now apply incl_appr.
Qed.

Lemma neg_neg_listVar_applySub v t1 t2 :
  ~ In v (listVarInT t1) -> ~ In v (listVarInT (applySubstitution ((v, t1) :: nil) t2)).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
    ~ In v (listVarInT t1) -> ~ In v (listVarInT (applySubstitution ((v, t1) :: nil) t')))).
enough (H : (forall n, (P n))).
  now apply (H (sizet t2)); try assumption.
intro n.
induction n as [ | n Hind].
- intros t' ? ?.
  now absurd (sizet t' <= 0); [apply sizet_gte_1 | assumption].
- intros t'.
  case t'.
  + intros v' _ ?.
    simpl; case (eq_variable_dec v' v) as [? | ?]; try assumption.
    intro Hor.
    now case Hor.
  + intros ? ? Hsizet ? HIn.
    destruct (sizet_SetC Hsizet) as [? ?].
    now case (in_app_or _ _ _ HIn); apply Hind.
  + intros s lt.
    elim lt.
    * intros _ ? ?; contradiction.
    * intros t'' lt' Hind' Hsizet ? HIn.
      case (in_app_or _ _ _ HIn).
      -- apply Hind; try assumption.
         apply (sizet_OTerm Hsizet).
         now apply in_eq.
      -- apply Hind'; try assumption.
         apply le_trans with (m := sizet (OTerm s (t'' :: lt'))); try assumption.
         apply le_n_S.
         now apply le_plus_r.
  + now intros _ ? ?; contradiction.
Qed.

Lemma neg_neg_listVar_applySubPC v t pc :
  ~ In v (listVarInT t) -> ~ In v (listVarInPC (applySubstitutionToPC ((v, t) :: nil) pc)).
Proof.
case pc; try now intros ? ? ? HIn;
  now case (in_app_or _ _ _ HIn); apply neg_neg_listVar_applySub.
- intros ? ?; contradiction.
- now intros ? ?; apply neg_neg_listVar_applySub.
Qed.

Lemma neg_neg_listVar_applySubC v t c :
  ~ In v (listVarInT t) -> ~ In v (listVarInC (applySubstitutionToC ((v, t) :: nil) c)).
Proof.
elim c.
- now intros ? ?; contradiction.
- intros pc c' Hind Hneq HIn.
  now case (in_app_or _ _ _ HIn); [apply neg_neg_listVar_applySubPC | apply Hind].
Qed.

Lemma listVarIn_buildEq lt1 lt2 sigma :
  incl (listVarInC (applySubstitutionToC sigma (map2 buildEq lt1 lt2)))
    (listVarInListT (map (applySubstitution sigma) lt1) ++ listVarInListT (map (applySubstitution sigma) lt2)).
Proof.
set (P := fun (n : nat) => (forall lt1' lt2', ((length lt1') <= n) ->
incl (listVarInC (applySubstitutionToC sigma (map2 buildEq lt1' lt2')))
    (listVarInListT (map (applySubstitution sigma) lt1') ++ listVarInListT (map (applySubstitution sigma) lt2')))).
enough (H : (forall n, (P n))).
  now apply (H (length lt1)).
intro n.
induction n as [ | n Hind]; intros lt1' lt2'.
- intros Hlength.
  assert (Heq_nil : lt1' = nil).
    apply length_zero_iff_nil.
    now apply Nat.le_0_r.
  now rewrite Heq_nil.
- elim lt1'; try now intros _; apply incl_nil_l.
  intros t1 lt1'' ? Hlength.
  elim lt2'; try now intros; apply incl_nil_l.
  intros t2 lt2'' ?.
  simpl. do 2 rewrite <- app_assoc.
  apply incl_app_app; try now apply incl_refl.
  apply incl_app.
  + apply incl_appr.
    apply incl_appl.
    now apply incl_refl.
  + apply incl_tran with (m := (listVarInListT (map (applySubstitution sigma) lt1'') ++ listVarInListT (map (applySubstitution sigma) lt2''))).
    * apply Hind.
      now apply le_S_n.
    * apply incl_app_app; try now apply incl_refl.
      now apply incl_appr.
Qed.

Lemma listVarInT_applySub_Var sigma v t t' :
  listVarInT (applySubstitution sigma t) = nil ->
    listVarInT (applySubstitution sigma t') = nil ->
      listVarInT (applySubstitution ((v, applySubstitution sigma t) :: sigma) t') = nil.
Proof.
intro Hnilt.
set (P := fun (n : nat) => (forall t'', ((sizet t'') <= n) ->
          listVarInT (applySubstitution sigma t'') = nil ->
      listVarInT (applySubstitution ((v, applySubstitution sigma t) :: sigma) t'') = nil)).
enough (H : (forall n, (P n))).
  now apply (H (sizet t')); try assumption.
intro n.
induction n as [ | n Hind].
- intros t'' ? ?.
  now absurd (sizet t'' <= 0); [apply sizet_gte_1 | assumption].
- intros t''.
  case t''.
  + intros v' _.
    now simpl; case (eq_variable_dec v' v) as [-> | ?].
  + intros t1 t2 Hsizet Hnilt1t2.
    simpl in Hnilt1t2; destruct (app_eq_nil _ _ Hnilt1t2) as [Hnilt1 Hnilt2].
    destruct (sizet_SetC Hsizet) as [Hsizet1 Hsizet2].
    assert (Hnil1 : listVarInT (applySubstitution ((v, applySubstitution sigma t) :: sigma) t1) = nil).
      now apply Hind.
    assert (Hnil2 : listVarInT (applySubstitution ((v, applySubstitution sigma t) :: sigma) t2) = nil).
      now apply Hind.
    simpl; rewrite Hnil1.
    now rewrite Hnil2.
  + intros s lt.
    elim lt; try trivial.
    intros t''' lt' H Hsizet Hniltlt.
    simpl in Hniltlt; destruct (app_eq_nil _ _ Hniltlt) as [Hnilt' Hnillt].
    assert (Hnilt''' : listVarInT (applySubstitution ((v, applySubstitution sigma t) :: sigma) t''') = nil).
      apply Hind; try assumption.
      apply (sizet_OTerm Hsizet).
      now apply in_eq.
    simpl; rewrite Hnilt'''.
    enough (He : listVarInT (applySubstitution ((v, applySubstitution sigma t) :: sigma) (OTerm s lt')) = nil).
      trivial.
    apply Hind; try assumption.
    apply le_S_n.
    apply le_trans with (m := sizet (OTerm s (t''' :: lt'))); try assumption.
    simpl; apply le_n_S.
    rewrite Nat.add_comm.
    rewrite S_eq.
    apply plus_le_compat_l.
    now apply le_1_sizet.
  + now trivial.
Qed.

Lemma listVarInPC_applySub_Var sigma v t pc :
  listVarInT (applySubstitution sigma t) = nil ->
    listVarInPC (applySubstitutionToPC sigma pc) = nil ->
      listVarInPC (applySubstitutionToPC ((v, applySubstitution sigma t) :: sigma) pc) = nil.
Proof.
intro Hnilt.
case pc; try now intros t1 t2 Hnilt1t2;
  destruct (app_eq_nil _ _ Hnilt1t2) as [Hnilt1 Hnilt2];
  simpl; rewrite (listVarInT_applySub_Var _ _ _ _ Hnilt Hnilt1);
  now rewrite (listVarInT_applySub_Var _ _ _ _ Hnilt Hnilt2).
- trivial.
- intros ? ?.
  now apply listVarInT_applySub_Var.
Qed.

Lemma listVarInC_applySub_Var sigma v t c :
  listVarInT (applySubstitution sigma t) = nil ->
    listVarInC (applySubstitutionToC sigma c) = nil ->
      listVarInC (applySubstitutionToC ((v, applySubstitution sigma t) :: sigma) c) = nil.
Proof.
intro H1.
elim c; try trivial.
intros pc c' Hind H2.
simpl in H2; destruct (app_eq_nil _ _ H2) as [? ?].
assert (H3 : listVarInC (applySubstitutionToC ((v, applySubstitution sigma t) :: sigma) c') = nil).
  now apply Hind.
assert (H4 : listVarInPC (applySubstitutionToPC ((v, applySubstitution sigma t) :: sigma) pc) = nil).
  now apply listVarInPC_applySub_Var.
simpl; rewrite H3.
now rewrite H4.
Qed.

Lemma occurCheck_In_listVarInT v t :
  occurCheck v t -> In v (listVarInT t).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) -> occurCheck v t' -> In v (listVarInT t'))).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' Hsizet_plus.
  absurd (sizet t' <= 0); try assumption.
  now apply sizet_gte_1.
- intro t'.
  case t'.
  + now intros v' _ <-; left.
  + intros t1 t2 Hsizet Hocc.
    destruct (sizet_SetC Hsizet).
    try now case Hocc as [? | ?]; apply in_or_app; [left | right]; apply Hind.
  + intros ? lt.
    elim lt; try trivial.
    intros t'' lt' Hind' Hsizet Hocc.
    simpl in Hsizet.
    case Hocc as [? | ?]; apply in_or_app; [left | right].
    * apply Hind; try assumption.
      rewrite <- plus_Sn_m in Hsizet.
      apply le_S_n.
      now apply (le_add_l _ _ Hsizet).
    * apply Hind'; try assumption.
      rewrite plus_n_Sm in Hsizet.
      now apply (le_add_r _ _ Hsizet).
  + trivial.
Qed.

Lemma occurCheckPC_In_listVarInPC v pc :
  occurCheckPC v pc -> In v (listVarInPC pc).
Proof.
case pc.
- intros ? ? Hocc.
  now case Hocc as [? | ?]; apply in_or_app; [left | right]; apply occurCheck_In_listVarInT.
- intros ? ? Hocc.
  now case Hocc as [? | ?]; apply in_or_app; [left | right]; apply occurCheck_In_listVarInT.
- intros ? ? Hocc.
  now case Hocc as [? | ?]; apply in_or_app; [left | right]; apply occurCheck_In_listVarInT.
- intros ? ? Hocc.
  now case Hocc as [? | ?]; apply in_or_app; [left | right]; apply occurCheck_In_listVarInT.
- trivial.
- intro.
  now apply occurCheck_In_listVarInT.
Qed.

Lemma occurCheckC_In_listVarInC v c :
  occurCheckC v c -> In v (listVarInC c).
Proof.
elim c; try trivial.
intros pc c' Hind Hocc.
case Hocc as [Hint1 | Hint2]; apply in_or_app; [left | right].
- now apply occurCheckPC_In_listVarInPC.
- now apply Hind.
Qed.

Lemma incl_listVar_listElements t :
  incl (listVarInListT (listElements t)) (listVarInT t).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
                             incl (listVarInListT (listElements t')) (listVarInT t'))).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  absurd (sizet t' <= 0); try assumption.
  now apply sizet_gte_1.
- intro t'.
  case t'; try now intros.
  intros ? ? Hsizet.
  apply incl_app_app; try now trivial.
  apply Hind.
  now destruct (sizet_SetC Hsizet).
Qed.

Lemma incl_listVarInT_listVarInListT t lt :
  In t lt -> incl (listVarInT t) (listVarInListT lt).
Proof.
elim lt; try contradiction.
intros t' lt' Hind HIn.
case HIn as [-> | ?]; try now apply incl_appl.
apply incl_appr.
now apply Hind.
Qed.

Lemma in_listVarInListT v lt :
  In v (listVarInListT lt) <-> exists t, In t lt /\ In v (listVarInT t).
Proof.
elim lt.
- split; try contradiction.
  intros [t [? ?]].
  now contradiction.
- intros t' lt' Hind.
  split.
  + intro HIn.
    case (in_app_or _ _ _ HIn) as [? | ?].
    * exists t'.
      split; try assumption.
      now apply in_eq.
    * assert (Hexists : exists t, In t lt' /\ In v (listVarInT t)).
        now apply Hind.
      destruct Hexists as [t [? ?]].
      exists t.
      split; try assumption.
      now apply in_cons.
  + intros [t [HIn ?]].
    case HIn as [-> | ?].
    * apply in_or_app.
      now left.
    * simpl; apply in_or_app.
      right.
      apply Hind.
      now exists t.
Qed.

Lemma incl_listVarInListT lt1 lt2 :
  incl lt1 lt2 -> incl (listVarInListT lt1) (listVarInListT lt2).
Proof.
intros Hincl v HIn.
assert (Hexists : exists t, In t lt1 /\ In v (listVarInT t)).
  now apply in_listVarInListT.
destruct Hexists as [t [? ?]].
apply in_listVarInListT.
exists t.
split; try assumption.
now apply Hincl.
Qed.

(*********************************************************************************)
(* function returning the maximum of a list of indexes and one of its properties *)
(*********************************************************************************)

Fixpoint MaxListInd (li : list index_set) :=
                     match li with
                     |nil => 0
                     |i :: lit => Nat.max i (MaxListInd lit)
                     end.

Lemma MaxListInd_le j (li : list index_set)  :
  In j li -> j <= (MaxListInd li).
Proof.
elim li; try contradiction.
intros ? ? Hind HIn.
case HIn as [-> | ?]; try now apply Nat.le_max_l.
apply Nat.max_le_iff.
now right; apply Hind.
Qed.

(******************************************************************************)
(*  a function returning a fresh variable and the proof of its correctness    *)
(******************************************************************************)

(* returns a list with the indexes of the variables in a term *)
Fixpoint listIndVarInT (t : term) {struct t} : list index_set :=
  match t with
  | Var (LogV i) => i :: nil
  | SetC t1 t2 => (listIndVarInT t1) ++ (listIndVarInT t2)
  | OTerm _ l =>
    let listIndVarInList :=
    (fix listIndVarInList (l : list term) {struct l} : list index_set :=
      match l with
      |nil => nil
      |t :: lt => (listIndVarInT t) ++ (listIndVarInList lt)
    end) in
    listIndVarInList l
  | EmptySet => nil
  end.

(* returns a list with the indexes of the variables in a primitive constraint pc *)
Definition listIndVarInPC (pc : primitiveConstraint) : list index_set :=
  match pc with
  | t1 == t2 => (listIndVarInT t1) ++ (listIndVarInT t2)
  | t1 \== t2 => (listIndVarInT t1) ++ (listIndVarInT t2)
  | t1 :s t2 => (listIndVarInT t1) ++ (listIndVarInT t2)
  | t1 \:s t2 => (listIndVarInT t1) ++ (listIndVarInT t2)
  | FalseC => nil
  | IsSet t => listIndVarInT t
  end.

(* returns a list with the indexes of the variables in a constraint c *)
Fixpoint listIndVarInC (c : constraint) : list index_set :=
  match c with
  | nil => nil
  | pc :: lpc => (listIndVarInPC pc) ++ (listIndVarInC lpc)
  end.

(* a function returning a fresh variable in a constraint *)
Definition FreshVarFun c :=
  LogV (S (MaxListInd ((listIndVarInC c)))).

Lemma occurCheck_In_listIndVarInT i t :
  occurCheck (LogV i) t -> In i (listIndVarInT t).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) -> occurCheck (LogV i) t' -> In i (listIndVarInT t'))).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' Hsizet_plus.
  absurd (sizet t' <= 0); try assumption.
  now apply sizet_gte_1.
- intro t'.
  case t'.
  + now intros v _ <-; left.
  + intros t1 t2 Hsizet Hocc.
    destruct (sizet_SetC Hsizet).
    try now case Hocc as [? | ?]; apply in_or_app; [left | right]; apply Hind.
  + intros ? lt.
    elim lt; try trivial.
    intros t'' lt' Hind' Hsizet Hocc.
    simpl in Hsizet.
    case Hocc as [? | ?]; apply in_or_app; [left | right].
    * apply Hind; try assumption.
      rewrite <- plus_Sn_m in Hsizet.
      apply le_S_n.
      now apply (le_add_l _ _ Hsizet).
    * apply Hind'; try assumption.
      rewrite plus_n_Sm in Hsizet.
      now apply (le_add_r _ _ Hsizet).
  + trivial.
Qed.

Lemma occurCheckPC_In_listIndVarInPC i pc :
  occurCheckPC (LogV i) pc -> In i (listIndVarInPC pc).
Proof.
case pc.
- intros ? ? Hocc.
  now case Hocc as [? | ?]; apply in_or_app; [left | right]; apply occurCheck_In_listIndVarInT.
- intros ? ? Hocc.
  now case Hocc as [? | ?]; apply in_or_app; [left | right]; apply occurCheck_In_listIndVarInT.
- intros ? ? Hocc.
  now case Hocc as [? | ?]; apply in_or_app; [left | right]; apply occurCheck_In_listIndVarInT.
- intros ? ? Hocc.
  now case Hocc as [? | ?]; apply in_or_app; [left | right]; apply occurCheck_In_listIndVarInT.
- trivial.
- intro.
  now apply occurCheck_In_listIndVarInT.
Qed.

Lemma occurCheckC_In_listIndVarInC i c :
  occurCheckC (LogV i) c -> In i (listIndVarInC c).
Proof.
elim c; try trivial.
intros pc c' Hind Hocc.
case Hocc as [Hint1 | Hint2]; apply in_or_app; [left | right].
- now apply occurCheckPC_In_listIndVarInPC.
- now apply Hind.
Qed.

Lemma FreshVarFun_isFresh c :
  isFreshC (FreshVarFun c) c.
Proof.
assert (Hforall : forall i, (In i (listIndVarInC c) -> ((FreshVarFun c) <> (LogV i)))).
  intros ? ? Heq.
  assert (Habs : i <= (MaxListInd (listIndVarInC c))).
    now apply MaxListInd_le.
  inversion Heq as [Heq'].
  rewrite <- Heq' in Habs.
  revert Habs.
  now apply Nat.nle_succ_diag_l.
intro Hocc.
enough (Habs : FreshVarFun c <> LogV (S (MaxListInd ((listIndVarInC c))))).
  contradiction.
apply Hforall.
now apply occurCheckC_In_listIndVarInC.
Qed.

