(****************************************
Maximiliano Cristia - Ricardo David Katz 
                  2026                   
****************************************)

Set Implicit Arguments.

Require Import Arith List Recdef Decidable.
Require Import Bool.
Require Import preliminaries terms_constraints list_variables depths substitution.


(* a function returning a set of the form {---{\emptyset}...} *)
Fixpoint EmptysetNi (n : nat) :=
  match n with
  | O => EmptySet
  | S n' => SetC (EmptysetNi n') EmptySet
  end.

(* a function returning a sufficiently large natural number to be used in the satisfiability result *)
Definition stepNi (c : constraint) :=
  S (S (list_max ((list_max (ListFindNiNeq c)) :: ((list_max (ListFindNiNin c)) :: 
     ((list_max (ListDepthsNeq (listVarInC c) c)) :: ((list_max (ListDepthsNin (listVarInC c) c)) :: nil)))))).

(* returns some t if the primitive constraint Var v == t occurs in c and None otherwise *)
Fixpoint FindEqTerm (v : log_variable) (c : constraint) :=
  match c with
  | nil => None
  | (Var v' == t) :: lpc => if (eq_variable_dec v' v) then (Some t) else FindEqTerm v lpc
  | _ :: lpc => FindEqTerm v lpc
  end.

(* a function returning the valuation of variable v used in the satisfiability result 
   if v occurs in listVarNotInEqLHS c *)
Definition sat_partial_sub_var (c : constraint) (v : log_variable) :=
  match v with
  | LogV n => (v, EmptysetNi ((S n) * stepNi c))
  end.

(* the extension of the previous function to a list of variables *)
Definition sat_partial_sub_list (c : constraint) lv : substitution :=
  map (sat_partial_sub_var c) lv.

(* a function returning the substitution applied to the variables that occur in
     listVarNotInEqLHS c which is used in the satisfiability result *)
Definition sat_partial_sub (c : constraint) : substitution :=
  sat_partial_sub_list c (nodup eq_variable_dec (listVarNotInEqLHS c)).

(* a function returning the valuation of variable v used in the satisfiability result *)
Definition sat_sub_var (c : constraint) (v : log_variable) :=
  if (in_dec eq_variable_dec v (listVarInEqLHS c)) then
     match (FindEqTerm v c) with
     | Some t => (v, applySubstitution (sat_partial_sub c) t)
     | None => (v, EmptysetNi 0)
     end
  else
     match v with
     | (LogV n) => (v, EmptysetNi ((S n) * (stepNi c)))
     end.

(* the extension of the previous function to a list of variables *)
Definition sat_sub_list (c : constraint) (lv : list log_variable) : substitution :=
  map (sat_sub_var c) lv.

(* a function returning the substitution used in the satisfiability result *)
Definition sat_sub (c : constraint) : substitution :=
  sat_sub_list c (nodup eq_variable_dec (listVarInC c)).

(************************************************)
(* properties of the functions introduced above *)
(************************************************)

Lemma le_2_stepNi c :
  2 <= stepNi c.
Proof.
apply le_n_S.
apply le_n_S.
now apply Nat.le_0_l.
Qed.

Lemma EmptysetNi0 :
  EmptysetNi 0 = EmptySet.
Proof.
trivial.
Qed.

Lemma depth_EmptySet_EmptysetNi n :
  depth_EmptySet (EmptysetNi n) = n.
Proof.
induction n as [ | n Hind]; try trivial.
simpl; now rewrite Hind.
Qed.

Lemma listElements_EmptysetNi n :
  (listElements (EmptysetNi (S n))) = ((EmptysetNi n) :: nil).
Proof.
trivial.
Qed.

Lemma listVarInT_EmptysetNi n :
  listVarInT (EmptysetNi n) = nil.
Proof.
elim n; try trivial.
simpl; intros m ->.
now rewrite app_nil_l.
Qed.

Lemma EmptysetNi_inj n1 n2 :
  (EmptysetNi n1) = (EmptysetNi n2) -> n1 = n2.
Proof.
set (P := fun (n : nat) => (forall n1 n2, ((Nat.max n1 n2) <= n) -> (EmptysetNi n1 = EmptysetNi n2 -> n1 = n2))).
enough (H : (forall n, (P n))).
  apply (H (Nat.max n1 n2)).
  now apply le_n.
intros n.
elim n.
- intros n1' n2' Hleq0 _.
  assert (Heqn1' : 0 = n1').
    apply le_n_0_eq.
    now apply (Nat.max_lub_l _ _ _ Hleq0).
  assert (Heqn2' : 0 = n2').
    apply le_n_0_eq.
    now apply (Nat.max_lub_r _ _ _ Hleq0).
  rewrite <- Heqn1'.
  now rewrite <- Heqn2'.
- intros n' Hind n1' n2' Hleq Heq.
  assert (Hor : ((Nat.max n1' n2') <= n') \/ ((Nat.max n1' n2') = S n')).
    now apply Nat.le_succ_r.
  case Hor as [? | Heq']; try now apply Hind.
  case (Nat.max_dec n1' n2') as [Heqn1' | Heqn2'].
  + rewrite <- Heqn1' in Heq.
    rewrite Heq' in Heq.
    simpl in Heq.
    revert Heq.
    case (Nat.zero_or_succ n2') as [-> | [m Heqn2']]; try discriminate.
    rewrite Heqn2'.
    intro H.
    inversion H.
    rewrite <- Heqn1'.
    rewrite Heq'.
    apply eq_S.
    apply Hind; try assumption.
    apply Nat.max_lub; try trivial.
    apply le_S_n.
    rewrite <- Heq'.
    rewrite <- Heqn2'.
    now apply Nat.le_max_r.
  + rewrite <- Heqn2' in Heq.
    rewrite Heq' in Heq.
    simpl in Heq.
    revert Heq.
    case (Nat.zero_or_succ n1') as [-> | [m Heqn1']]; try discriminate.
    rewrite Heqn1'.
    intro H.
    inversion H.
    rewrite <- Heqn2'.
    rewrite Heq'.
    apply eq_S.
    apply Hind; try assumption.
    apply Nat.max_lub; try trivial.
    apply le_S_n.
    rewrite <- Heq'.
    rewrite <- Heqn1'.
    now apply Nat.le_max_l.
Qed.

Lemma fst_sat_partial_sub_list_eq c lv :
  (map fst (sat_partial_sub_list c lv)) = lv.
Proof.
elim lv; try trivial.
intros [n] lv' Hind.
now simpl; rewrite Hind.
Qed.

Lemma nodup_fst_sat_partial_sub_list c lv :
  NoDup lv -> NoDup (map fst (sat_partial_sub_list c lv)).
Proof.
now rewrite fst_sat_partial_sub_list_eq.
Qed.

Lemma fst_sat_sub_list_eq c lv :
  (map fst (sat_sub_list c lv)) = lv.
Proof.
elim lv; try trivial.
intros [n] lv' Hind.
simpl; unfold sat_sub_var.
case (in_dec eq_variable_dec (LogV n) (listVarInEqLHS c)) as [Hin | Hnin].
- now case (FindEqTerm (LogV n) c) as [? | ]; simpl; rewrite Hind.
- now simpl; rewrite Hind.
Qed.

Lemma nodup_fst_sat_sub_list c lv :
  NoDup lv -> NoDup (map fst (sat_sub_list c lv)).
Proof.
now rewrite fst_sat_sub_list_eq.
Qed.

Lemma sat_partial_sub_list_fst_incl c lv :
  incl (map fst (sat_partial_sub_list c lv)) lv.
Proof.
now rewrite fst_sat_partial_sub_list_eq.
Qed.

Lemma incl_fst_sat_partial_sub_list c lv :
  incl lv (map fst (sat_partial_sub_list c lv)).
Proof.
now rewrite fst_sat_partial_sub_list_eq.
Qed.

Lemma incl_fst_sat_sub_list c lv :
  incl lv (map fst (sat_sub_list c lv)).
Proof.
now rewrite fst_sat_sub_list_eq.
Qed.

Lemma sat_sub_list_fst_incl c lv :
  incl (map fst (sat_sub_list c lv)) lv.
Proof.
now rewrite fst_sat_sub_list_eq.
Qed.

Lemma incl_sat_partial_sub_list l1 l2 c :
  incl l1 l2 -> incl (sat_partial_sub_list c l1) (sat_partial_sub_list c l2).
Proof.
intros Hincl p Hinp.
assert (Hexists : exists v : log_variable, sat_partial_sub_var c v = p /\ In v l1).
  now apply in_map_iff.
destruct Hexists as [v [Heq Hin]].
apply in_map_iff.
exists v.
split; [assumption | now apply Hincl].
Qed.

Lemma stepNi_inv pc (c : constraint) :
  In pc c ->
    (stepNi c) = (stepNi (pc :: (remove eq_primc_dec pc c))).
Proof.
intro Hin.
unfold stepNi.
rewrite <- (Max_ListFindNiNeq_inv _ _ Hin).
rewrite <- (Max_ListFindNiNin_inv _ _ Hin).
rewrite <- (Max_listVarInC_inv _ _ Hin).
now rewrite <- (Max_ListDepthsNin_inv _ _ Hin).
Qed.

Lemma sat_partial_sub_list_inv lv pc (c : constraint) :
  In pc c ->
    (sat_partial_sub_list c lv) = (sat_partial_sub_list (pc :: (remove eq_primc_dec pc c)) lv).
Proof.
induction lv as [ | v lv' Hind]; try reflexivity.
intro Hin.
destruct v; simpl.
rewrite (Hind Hin).
rewrite (stepNi_inv pc _ Hin).
rewrite (Max_ListDepthsNin_inv pc _ Hin).
rewrite (Max_listVarInC_inv pc _ Hin).
rewrite (Max_ListFindNiNeq_inv pc _ Hin).
rewrite (Max_ListFindNiNin_inv pc _ Hin).
reflexivity.
Qed.

Lemma find_sat_partial_sub_inv v pc (c : constraint) :
  In pc c ->
    find eq_variable_dec v (sat_partial_sub c) = find eq_variable_dec v (sat_partial_sub (pc :: (remove eq_primc_dec pc c))).
Proof.
intros Hin.
unfold sat_partial_sub.
rewrite <- (sat_partial_sub_list_inv _ _ _ Hin).
case (in_dec eq_variable_dec v (listVarNotInEqLHS c)) as [HinList | HneqInList].
- apply NoDup_incl_find.
  + apply nodup_fst_sat_partial_sub_list.
    now apply NoDup_nodup.
  + intros p Hinp.
    enough (H : incl (sat_partial_sub_list c (nodup eq_variable_dec (listVarNotInEqLHS c))) 
                     (sat_partial_sub_list c (nodup eq_variable_dec (listVarNotInEqLHS (pc :: remove eq_primc_dec pc c))))).
      now apply H.
    apply incl_sat_partial_sub_list.
    apply nodup_incl.
    now apply incl_tran with (m := (listVarNotInEqLHS c));
      [apply incl_nodup | now apply incl_listVarNotInEqLHS_remove_r].
  + apply incl_fst_sat_partial_sub_list.
    enough (H: incl (listVarNotInEqLHS c) (nodup eq_variable_dec (listVarNotInEqLHS c))).
      now apply H.
    apply nodup_incl.
    now apply incl_refl.
- assert (H: ~ In v (map fst (sat_partial_sub_list c (nodup eq_variable_dec (listVarNotInEqLHS (pc :: remove eq_primc_dec pc c)))))).
    intro.
    enough (In v (listVarNotInEqLHS c)).
      contradiction.
    assert (H' : incl (nodup eq_variable_dec (listVarNotInEqLHS (pc :: remove eq_primc_dec pc c))) (listVarNotInEqLHS c)).
      now apply incl_tran with (m := (listVarNotInEqLHS (pc :: remove eq_primc_dec pc c)));
        [apply incl_nodup | apply incl_listVarNotInEqLHS_remove_l].
    apply (H' v).
    now apply (sat_partial_sub_list_fst_incl c _ v).
  rewrite (find_none eq_variable_dec _ v H).
  apply find_none.
  intro.
  enough (HIn : In v (map fst (sat_partial_sub_list c (nodup eq_variable_dec (listVarNotInEqLHS (pc :: remove eq_primc_dec pc c)))))).
    contradiction.
  assert (Hexists : exists x : log_variable * term, fst x = v /\
                                In x (sat_partial_sub_list c (nodup eq_variable_dec (listVarNotInEqLHS c)))).
    now apply in_map_iff.
  destruct Hexists as [v' [? ?]].
  apply in_map_iff.
  exists v'.
  split; try assumption.
  enough (Hincl : incl (nodup eq_variable_dec (listVarNotInEqLHS c)) (nodup eq_variable_dec (listVarNotInEqLHS (pc :: remove eq_primc_dec pc c)))).
    now apply (incl_sat_partial_sub_list _ Hincl).
  apply nodup_incl.
  now apply incl_tran with (m:= (listVarNotInEqLHS c)); [apply incl_nodup | apply incl_listVarNotInEqLHS_remove_r].
Qed.

Lemma sat_partial_sub_inv pc (c : constraint) :
  In pc c -> (forall t,
    (applySubstitution (sat_partial_sub c) t) = (applySubstitution (sat_partial_sub (pc :: (remove eq_primc_dec pc c))) t)).
Proof.
intro Hin.
set (P := fun (n : nat) => (forall t, ((sizet t) <= n) ->
                             (applySubstitution (sat_partial_sub c) t) = (applySubstitution (sat_partial_sub (pc :: (remove eq_primc_dec pc c))) t))).
enough (H : (forall n, (P n))).
  intro t.
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t ?.
  now absurd (sizet t <= 0); [apply sizet_gte_1 | assumption].
- intro t.
  case t.
  + intros ? ?.
    now simpl; rewrite (find_sat_partial_sub_inv _ _ _ Hin).
  + intros t1 t2 Hsizet.
    destruct (sizet_SetC Hsizet) as [Hsizet1 Hsizet2].
    simpl; rewrite (Hind _ Hsizet1).
    now rewrite (Hind _ Hsizet2).
  + intros s lt Hsizet.
    enough (H : (map (applySubstitution (sat_partial_sub c)) lt) =
                (map (applySubstitution (sat_partial_sub (pc :: remove eq_primc_dec pc c))) lt)).
      now simpl; rewrite H.
    apply map_ext_in.
    intros t' Hint'.
    apply Hind.
    now apply (sizet_OTerm Hsizet).
   + trivial.
Qed.

Lemma FindEqTerm_None v c :
  (FindEqTerm v c = None) <-> (~ In v (listVarInEqLHS c)).
Proof.
elim c; try now split.
intros pc c' Hind.
case pc; try now intros; apply Hind.
intros t1 t2.
case t1; try now intros; apply Hind.
intro v'; simpl.
case (eq_variable_dec v' v) as [Heq | Hneq].
- split.
  + intro H.
    inversion H.
  + rewrite Heq.
    intro H.
    now absurd (v = v); [destruct (not_or _ _ H) | reflexivity].
- split.
  + intro; unfold not; intro Hor.
    case Hor; [contradiction | now apply Hind].
  + intro H.
    apply Hind.
    now destruct (not_or _ _ H).
Qed.

Lemma FindEqTerm_Some v t c :
  isInSFC c ->
    (FindEqTerm v c = Some t) <-> (In ((Var v) == t) c).
Proof.
intro HinSFC.
split.
- elim c.
  + intro H; inversion H.
  + intros pc c' Hind.
    case pc; try now intros; right; apply Hind.
    intros t1 t2.
    case t1; try now intros; right; apply Hind.
    intro v'; simpl.
    case (eq_variable_dec v' v).
    * intros -> Heq.
      inversion Heq.
      now left; reflexivity.
    * intros; right; now apply Hind.
- revert HinSFC.
  elim c; try contradiction.
  intros pc c' Hind HinSFC Hin.
  case Hin as [-> | Hin].
  + simpl; case (eq_variable_dec v v); try reflexivity.
    intro; now apply Hind.
  + assert (isInSFC c').
      now apply incl_isInSFC with (c2 := (pc :: c')); [apply incl_tl | assumption].
    revert HinSFC.
    case pc; try now intros; apply Hind.
    intros t1 t2.
    case t1; try now intros; apply Hind.
    intro v'; simpl.
    case (eq_variable_dec v' v); try now intros; apply Hind.
    intros -> HinSFC.
    case (eq_term_dec t2 t); try now intros ->.
    intro Hneq.
    assert (HisInSFPC : isInSFPC (Var v == t) ((Var v == t2) :: c')).
      apply HinSFC.
      now apply in_cons.
    destruct HisInSFPC as [H1 H2].
    assert (Hremove : (remove eq_primc_dec (Var v == t) ((Var v == t2) :: c')) =
                                 (Var v == t2) :: (remove eq_primc_dec (Var v == t) c')).
      simpl; case (eq_primc_dec (Var v == t) (Var v == t2)) as [Heq | ?]; try reflexivity.
      inversion Heq as [Heq'].
      now rewrite Heq' in Hneq.
    rewrite Hremove in H2.
    simpl in H2.
    destruct (not_or _ _ H2) as [H3 ?].
    now destruct (not_or _ _ H3) as [H4 ?].
Qed.

Lemma FindEqTerm_inv v pc c :
  In pc c -> isInSFC c ->
    (FindEqTerm v c = FindEqTerm v (pc :: remove eq_primc_dec pc c)).
Proof.
intros Hinpc HinSFC.
case (in_dec eq_variable_dec v (listVarInEqLHS c)) as [Hinv | Hninv].
- assert (Hexists : exists t : term, In (Var v == t) c).
    now apply In_listVarInEqLHS.
  destruct Hexists as [t Hin].
  assert (Heq: FindEqTerm v c = Some t).
    now apply FindEqTerm_Some.
  rewrite Heq.
  apply eq_sym.
  apply FindEqTerm_Some; try now apply isInSFC_inv.
  case (eq_primc_dec (Var v == t) pc) as [-> | H]; try now apply in_eq.
  apply in_cons.
  now apply in_in_remove.
- assert (Heq: FindEqTerm v c = None).
    now apply FindEqTerm_None.
  rewrite Heq.
  apply eq_sym.
  apply FindEqTerm_None.
  intro.
  assert (Hexists: exists t : term, In (Var v == t) (pc :: remove eq_primc_dec pc c)).
    now apply In_listVarInEqLHS.
  destruct Hexists as [t Hin].
  enough (In v (listVarInEqLHS c)).
    contradiction.
  apply In_listVarInEqLHS.
  exists t.
  now apply (incl_remove_l eq_primc_dec _ Hinpc).
Qed.

Lemma incl_sat_sub_remove pc (c: constraint):
  In pc c -> isInSFC c ->
    incl (sat_sub c) (sat_sub (pc :: remove eq_primc_dec pc c)).
Proof.
intros Hinpc HisInSF p Hinp.
unfold sat_sub.
unfold sat_sub_list.
assert (Hexists: exists v : log_variable, sat_sub_var c v = p /\ In v (nodup eq_variable_dec (listVarInC c))).
  now apply in_map_iff.
destruct Hexists as [v [Heq Hinv]].
apply in_map_iff.
exists v.
split.
- revert Heq.
  unfold sat_sub_var.
  case (in_dec eq_variable_dec v (listVarInEqLHS c)).
  + case (in_dec eq_variable_dec v (listVarInEqLHS (pc :: remove eq_primc_dec pc c))).
    * intros Hin Hin'.
      rewrite <- (FindEqTerm_inv v pc Hinpc HisInSF).
      case (FindEqTerm v c); try trivial.
      intro t.
      now rewrite (sat_partial_sub_inv pc c Hinpc t).
    * intros Hnin Hin.
      enough (In v (listVarInEqLHS (pc :: remove eq_primc_dec pc c))).
        contradiction.
      enough (Hincl: incl (listVarInEqLHS c) (listVarInEqLHS (pc :: remove eq_primc_dec pc c))).
        now apply Hincl.
      apply incl_listVarInEqLHS.
      now apply incl_remove_r.
  + case (in_dec eq_variable_dec v (listVarInEqLHS (pc :: remove eq_primc_dec pc c))).
    * intros Hin Hnin.
      enough (In v (listVarInEqLHS c)).
        contradiction.
      enough (Hincl: incl (listVarInEqLHS (pc :: remove eq_primc_dec pc c)) (listVarInEqLHS c)).
        now apply Hincl.
      apply incl_listVarInEqLHS.
      now apply incl_remove_l.
    * intros Hin Hin'.
      now rewrite (stepNi_inv pc c Hinpc).
- enough (H : incl (nodup eq_variable_dec (listVarInC c)) (nodup eq_variable_dec (listVarInC (pc :: remove eq_primc_dec pc c)))).
    now apply H.
  apply incl_incl_nodup.
  apply incl_ListVarInC.
  now apply incl_remove_r.
Qed.

Lemma find_sat_sub_inv v pc (c: constraint):
  In pc c -> isInSFC c ->
    find eq_variable_dec v (sat_sub c) = find eq_variable_dec v (sat_sub (pc :: (remove eq_primc_dec pc c))).
Proof.
intros Hin HisInSF.
case (in_dec eq_variable_dec v (nodup eq_variable_dec (listVarInC c))) as [HinList | HneqInList].
- apply NoDup_incl_find.
  + apply nodup_fst_sat_sub_list.
    now apply NoDup_nodup.
  + now apply incl_sat_sub_remove.
  + now apply incl_fst_sat_sub_list.
- assert (HnIn: ~ In v (map fst (sat_sub (pc :: remove eq_primc_dec pc c)))).
    unfold sat_sub.
    rewrite fst_sat_sub_list_eq.
    intro HIn.
    absurd (In v (nodup eq_variable_dec (listVarInC c))); try assumption.
      enough (Hincl: incl (nodup eq_variable_dec (listVarInC (pc :: remove eq_primc_dec pc c)))
                            (nodup eq_variable_dec (listVarInC c))).
        now apply Hincl.
    apply incl_incl_nodup.
    apply incl_ListVarInC.
    apply (incl_cons Hin).
    now apply incl_remove.
  rewrite (find_none eq_variable_dec _ v HnIn).
  apply find_none.
  intro HIn.
  absurd (In v (nodup eq_variable_dec (listVarInC c))); try assumption.
  unfold sat_sub in HIn.
  now rewrite fst_sat_sub_list_eq in HIn.
Qed.

Lemma InLHSEq v t (c : constraint) :
  In (Var v == t) c -> isInSFC c ->
    find eq_variable_dec v (sat_sub c) = Some (applySubstitution (sat_partial_sub c) t).
Proof.
intros Hinc HinSF.
rewrite (find_sat_sub_inv v _  Hinc HinSF).
rewrite (sat_partial_sub_inv _ _ Hinc).
unfold sat_sub.
unfold sat_sub_list.
assert (HinSFPC: isInSFPC (Var v == t) c).
  now apply HinSF.
rewrite (nodup_listVarInC_eq HinSFPC).
assert (Heq: (sat_sub_var ((Var v == t) :: remove eq_primc_dec (Var v == t) c) v) = 
         (v, (applySubstitution (sat_partial_sub ((Var v == t) :: remove eq_primc_dec (Var v == t) c)) t))).
  unfold sat_sub_var.
  simpl; case (eq_variable_dec v v); [reflexivity | contradiction].
simpl; rewrite Heq.
case (eq_variable_dec v v); [reflexivity | contradiction].
Qed.

Lemma In_listVarNotInEqLHS_find_eq v (c : constraint) :
  In v (listVarNotInEqLHS c) ->
    find eq_variable_dec v (sat_partial_sub c) = find eq_variable_dec v (sat_sub c).
Proof.
intro HInp.
apply NoDup_incl_find.
- apply nodup_fst_sat_sub_list.
  now apply NoDup_nodup.
- intros p Hin.
  assert (Hexists: exists y, sat_partial_sub_var c y = p /\ 
                     In y (nodup eq_variable_dec (listVarNotInEqLHS c))).
    now apply in_map_iff.
  destruct Hexists as [y [? HIny]].
  apply in_map_iff.
  exists y.
  split.
  + unfold sat_sub_var; unfold sat_partial_sub_var in H.
    case (in_dec eq_variable_dec y (listVarInEqLHS c)); try now intro.
    intro Hiny'.
    absurd (In y (listVarInEqLHS c)); try assumption.
    unfold listVarNotInEqLHS in HIny.
    apply in_remove_list with (l2 := listVarInC c) (eq_dec := eq_variable_dec).
    now apply (nodup_In eq_variable_dec).
  + apply nodup_In.
    unfold listVarNotInEqLHS in HIny.
    apply (incl_remove_list eq_variable_dec (listVarInEqLHS c)).
    now apply (nodup_In eq_variable_dec).
- unfold sat_partial_sub.
  rewrite fst_sat_partial_sub_list_eq.
  now apply nodup_In.
Qed.

Lemma incl_listVarInT_applySubstitutiont_eq t (c : constraint) :
  incl (listVarInT t) (listVarNotInEqLHS c) ->
    applySubstitution (sat_sub c) t = applySubstitution (sat_partial_sub c) t.
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) -> (incl (listVarInT t') (listVarNotInEqLHS c) ->
      applySubstitution (sat_sub c) t' = applySubstitution (sat_partial_sub c) t'))).
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
  + intros v _ Hincl.
    destruct (incl_cons_inv Hincl) as [Hin ?].
    now simpl; rewrite (In_listVarNotInEqLHS_find_eq _ _ Hin).
  + intros t1 t2 Hsizet Hincl.
    destruct (sizet_SetC Hsizet) as [Hsizet1 Hsizet2].
    simpl in  Hincl.
    destruct (incl_app_inv _ _ Hincl) as [Hincl1 Hincl2].
    simpl; rewrite (Hind _ Hsizet1 Hincl1).
    now rewrite (Hind _ Hsizet2 Hincl2).
  + intros ? lt.
    elim lt; try trivial.
    intros t'' lt' Hind' Hsizet Hincl.
    simpl in Hsizet.
    simpl in  Hincl.
    destruct (incl_app_inv _ _ Hincl) as [Hincl1 Hincl2].
    assert (Heq1 : applySubstitution (sat_sub c) t'' =
                  applySubstitution (sat_partial_sub c) t'').
      apply Hind; try assumption.
      rewrite <- plus_Sn_m in Hsizet.
      apply le_S_n.
      now apply (le_add_l _ _ Hsizet).
    enough (Heq2 : (map (applySubstitution (sat_sub c)) lt') =
                  (map (applySubstitution (sat_partial_sub c)) lt')).
      now simpl;rewrite Heq1; rewrite Heq2.
    enough (H : applySubstitution (sat_sub c) (OTerm l lt') =
               applySubstitution (sat_partial_sub c) (OTerm l lt')).
      simpl in H.
      now inversion H.
    apply Hind'; try assumption.
    rewrite plus_n_Sm in Hsizet.
    now apply (le_add_r _ _ Hsizet).
  + trivial.
Qed.

Lemma applySubstitution_InEq_eq t1 t2 (c : constraint) :
  In (t1 == t2) c -> isInSFC c ->
    applySubstitutionToPC (sat_sub c) (t1 == t2) =
      (applySubstitution (sat_sub c) t1 == applySubstitution (sat_partial_sub c) t2).
Proof.
intros Hin HisInSFC.
enough (Hincl : incl (listVarInT t2) (listVarNotInEqLHS c)).
  simpl; now rewrite (incl_listVarInT_applySubstitutiont_eq _ _ Hincl).
intros v Hinv.
apply in_remove_list.
split.
- assert (Hincl : incl ((t1 == t2) :: nil) c).
    apply incl_cons; try assumption.
    now apply incl_nil_l.
  apply (incl_ListVarInC Hincl).
  apply in_or_app.
  left.
  apply in_or_app.
  now right.
- intro Hinv'.
  assert (Hexists : exists t : term, In (Var v == t) c).
    now apply In_listVarInEqLHS.
  destruct Hexists as [t Hin'].
  assert (HisInSFPC : isInSFPC (Var v == t) c).
    apply (HisInSFC _ Hin').
  destruct HisInSFPC as [H1 H2].
  case (eq_primc_dec (t1 == t2) (Var v == t)) as [Heq | Hneq].
  + enough (occurCheck v t).
      contradiction.
    apply In_listVarInT_occurCheck.
    inversion Heq as [[H' H]].
    now rewrite <- H.
  + enough (occurCheckC v (remove eq_primc_dec (Var v == t) c)).
      contradiction.
    apply occurCheckC_exists.
    exists (t1 == t2).
    split.
    * now apply in_in_remove.
    * now right; apply In_listVarInT_occurCheck.
Qed.

Lemma sat_partial_sub_eq i c :
  In (LogV i) (listVarNotInEqLHS c) ->
    (applySubstitution (sat_partial_sub c) (\V i)) = EmptysetNi ((S i) * stepNi c).
Proof.
intro HIn.
unfold sat_partial_sub.
simpl.
enough (Hfind : (find eq_variable_dec (LogV i) ((LogV i, EmptysetNi ((S i) * stepNi c)) :: nil)) =
                 find eq_variable_dec (LogV i) (sat_partial_sub_list c (nodup eq_variable_dec (listVarNotInEqLHS c)))).
  rewrite <- Hfind.
  simpl; case (eq_variable_dec (LogV i) (LogV i)); try reflexivity.
  contradiction.
apply NoDup_incl_find; try now left.
- rewrite fst_sat_partial_sub_list_eq.
  now apply NoDup_nodup.
- apply incl_cons.
  + apply in_map_iff.
    exists (LogV i).
    now split; [trivial | apply nodup_In].
  + apply incl_nil_l.
Qed.

Lemma fst_sat_sub_aux c lv :
  (map fst (sat_sub_list c lv)) = lv.
Proof.
elim lv; try trivial.
intros v lv' Hind.
simpl; rewrite Hind.
unfold sat_sub_var.
now case (in_dec eq_variable_dec v (listVarInEqLHS c)) as [? | ?];
  [case (FindEqTerm v c) | destruct v].
Qed.

Lemma sat_partial_sub_listVar_nil t c :
  incl (listVarInT t) (listVarNotInEqLHS c) ->
    listVarInT (applySubstitution (sat_partial_sub c) t) = nil.
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
  (incl (listVarInT t') (listVarNotInEqLHS c) ->
    listVarInT (applySubstitution (sat_partial_sub c) t') = nil))).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' Hsizet_plus.
  now absurd (sizet t' <= 0); [apply sizet_gte_1 | assumption].
- intro t'.
  case t'.
  + intros v _ Hincl.
    assert (HInv : In v (map fst (sat_partial_sub c))).
      unfold sat_partial_sub.
      rewrite fst_sat_partial_sub_list_eq.
      apply nodup_In.
      apply Hincl.
      now left.
    simpl; destruct (find_exists_some eq_variable_dec _ _ HInv) as [t'' [HInt'' ->]].
    assert (Hexists : exists pc, (snd pc = t'') /\ (In pc (sat_partial_sub c))).
      now apply in_map_iff.
    destruct Hexists as [pc [Hsnd_eq HInpc]].
    unfold sat_partial_sub in HInpc.
    unfold sat_partial_sub_list in HInpc.
    assert (Hexists : exists v, ((sat_partial_sub_var c) v = pc) /\ (In v (nodup eq_variable_dec (listVarNotInEqLHS c)))).
      now apply in_map_iff.
    destruct Hexists as [v' [Hpc_eq HInv']].
    rewrite <- Hsnd_eq.
    rewrite <- Hpc_eq.
    destruct v'.
    simpl; do 2 rewrite app_nil_r.
    now rewrite listVarInT_EmptysetNi.
  + intros t1 t2 Hsizet.
    simpl; intro Hincl.
    destruct (incl_app_inv _ _ Hincl) as [Hincl1 Hincl2].
    destruct (sizet_SetC Hsizet) as [Hsizet1 Hsizet2].
    rewrite (Hind _ Hsizet1 Hincl1).
    rewrite (Hind _ Hsizet2 Hincl2).
    now rewrite app_nil_l.
  + intros s lt.
    elim lt; try trivial.
    intros t'' lt' Hind'.
    simpl; intros HsizetOT Hincl.
    assert (Hsizet'' : sizet t'' <= n).
      rewrite <- plus_Sn_m in HsizetOT.
      apply le_S_n.
      now apply (le_add_l _ _ HsizetOT).
    destruct (incl_app_inv _ _ Hincl) as [Hincl'' Hincl'].
    rewrite (Hind _ Hsizet'' Hincl'').
    rewrite app_nil_l.
    apply Hind'; try assumption.
    apply le_S.
    simpl; rewrite S_eq.
    apply le_S_n.
    apply le_trans with (m:= sizet (OTerm s (t'' :: lt'))); try assumption.
    simpl; apply le_n_S.
    rewrite Nat.add_comm.
    now apply plus_le_compat; [apply le_1_sizet | apply le_n].
  + trivial.
Qed.

Lemma snd_sat_sub_listVar_nil t c :
  isInSFC c -> In t (map snd (sat_sub c)) ->
    listVarInT t = nil.
Proof.
intros HisInSFC HInt.
assert (Hexists : exists pc, (snd pc = t) /\ (In pc (sat_sub c))).
  now apply in_map_iff.
destruct Hexists as [pc [Hsnd_eq HInpc]].
unfold sat_sub in HInpc.
unfold sat_sub_list in HInpc.
assert (Hexists : exists v, ((sat_sub_var c) v = pc) /\ (In v (nodup eq_variable_dec (listVarInC c)))).
  now apply in_map_iff.
destruct Hexists as [v [Hpc_eq HInv]].
rewrite <- Hsnd_eq.
rewrite <- Hpc_eq.
unfold sat_sub_var.
case (in_dec eq_variable_dec v (listVarInEqLHS c)) as [? | ?].
- assert (Hexists : exists t' : term, In (Var v == t') c).
    now apply In_listVarInEqLHS.
  destruct Hexists as [t' HIn].
  assert (H : FindEqTerm v c = Some t').
    now apply FindEqTerm_Some.
  rewrite H.
  apply sat_partial_sub_listVar_nil.
  intros v' HInv'.
  apply (In_listVarNotInEqLHS _ _ HisInSFC HIn).
  apply in_remove_list.
  split; simpl.
  + right.
    now rewrite app_nil_r.
  + intro Hor.
    case Hor as [Heq | ?]; try contradiction.
    assert (Habs : isInSFPC (Var v == t') c).
      now apply HisInSFC.
    absurd (occurCheck v t').
    * now destruct Habs.
    * apply In_listVarInT_occurCheck.
      now rewrite Heq.
- destruct v.
  simpl; do 2 rewrite app_nil_r.
  now rewrite listVarInT_EmptysetNi.
Qed.

