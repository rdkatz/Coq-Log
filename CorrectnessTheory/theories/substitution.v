(****************************************
Maximiliano Cristia - Ricardo David Katz 
                  2026                   

Some parts were taken from the work of   
Catherine Dubois - Sulyvan Weppe         
ENSIIE - Samovar -                       
2016-2018                                
****************************************)

Set Implicit Arguments.

Require Import List Decidable Recdef Arith.

Require Import preliminaries terms_constraints.

(*****************************)
(*          Find             *)
(*****************************)

(*returns the value associated with the key a in the list of pairs l according to eq_A_dec equality*)
Function find (A B : Set) (eq_A_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2})
              (a : A) (l : list (A * B)) {struct l} : option (B) :=
  match l with
  | nil => None
  | (a1,b1) :: l =>
     if (eq_A_dec a a1)
     then Some b1
     else find eq_A_dec a l
  end.

(*****************************)
(*    properties of find     *)
(*****************************)

Lemma find_none (A B : Set) (eq_A_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2})
                (l : list (A * B)) (a : A) :
  ~ In a (map fst l) -> find eq_A_dec a l = None.
Proof.
elim l; try trivial.
intros p ? Hind Hnin.
destruct p as [a' b'].
simpl in Hnin.
destruct (not_or _ _ Hnin).
simpl.
now case (eq_A_dec a a') as [-> | ?]; [contradiction | apply Hind].
Qed.

Lemma find_exists_some (A B : Set) (eq_A_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2})
                       (l : list (A * B)) (a : A) :
  In a (map fst l) ->
    exists b, (In b (map snd l)) /\ (find eq_A_dec a l = Some b).
Proof.
elim l; try contradiction.
intros p lp Hind HIn.
destruct p as [a' b'].
case HIn as [<- | HIn].
- exists b'.
  split.
  + apply in_map_iff.
    exists (a', b').
    split; try reflexivity.
    now apply in_eq.
  + simpl.
    case (eq_A_dec a' a'); [reflexivity | contradiction].
- case (eq_A_dec a a') as [-> | Hneq].
  + exists b'.
    split; simpl; try now left.
    now case (eq_A_dec a' a'); [reflexivity | contradiction].
  + destruct (Hind HIn) as [b [? Hfind]].
    exists b.
    split; try now apply in_cons.
    simpl.
    case (eq_A_dec a a') as [Heq | _]; try contradiction.
    now rewrite Hfind.
Qed.

Lemma find_exists_some_r (A B : Set) (eq_A_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2})
                       (sigma : list (A * B)) (a : A) :
  In a (map fst sigma) ->
    exists p, (In p sigma) /\ (fst p = a) /\ (find eq_A_dec a sigma = Some (snd p)).
Proof.
elim sigma; try contradiction.
intros p lp Hind HIn.
destruct p as [a' b'].
simpl in HIn.
case (eq_A_dec a' a) as [Heq | Hneq].
- exists (a', b').
  split; try apply in_eq.
  split; try now rewrite Heq.
  simpl; rewrite Heq.
  now case (eq_A_dec a a); [reflexivity | contradiction].
- case HIn as [? | HIn]; try contradiction.
  destruct (Hind HIn) as [p' [? [Hfst Hfind]]].
  exists p'.
  split; try now apply in_cons.
  split; try assumption.
  simpl.
  case (eq_A_dec a a') as [Heq | _]; try assumption.
  rewrite Heq in Hneq.
  contradiction.
Qed.

Lemma NoDup_find (A B : Set) (eq_A_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2})
                 (l1 l2 : list (A * B)) (a : A) (b : B) :
  NoDup (map fst (l1 ++ (a,b) :: l2)) -> find eq_A_dec a (l1 ++ (a,b) :: l2) = Some b.
Proof.
elim l1.
- simpl; case (eq_A_dec a a); [reflexivity | contradiction].
- intros p lp Hind HNDup.
  destruct p as [a' b'].
  case (eq_A_dec a a') as [-> | Hneq].
  + assert (Hand: ~In a' (map fst (lp ++ (a', b) :: l2)) /\ NoDup (map fst (lp ++ (a', b) :: l2))).
      now apply NoDup_cons_iff.
    destruct Hand as [? ?].
    absurd (In a' (map fst (lp ++ (a', b) :: l2))); try assumption.
    rewrite map_app.
    apply in_or_app; right.
    now left.
  + simpl; case (eq_A_dec a a') as [ | _]; try contradiction.
    apply Hind.
    assert (Heql: (((a', b') :: lp) ++ (a, b) :: l2) =  (a', b') :: (lp ++ (a, b) :: l2)).
      trivial.
    rewrite Heql in HNDup.
    rewrite map_cons in HNDup.
    assert (Hand: (~ In (fst (a', b')) (map fst (lp ++ (a, b) :: l2))) /\ (NoDup (map fst (lp ++ (a, b) :: l2)))).
      now apply NoDup_cons_iff.
    now destruct Hand.
Qed.

Lemma NoDup_incl_find (A B : Set) (eq_A_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2})
                      (l1 l2 : list (A * B)) (a : A) :
  NoDup (map fst l2) -> incl l1 l2 -> In a (map fst l1) ->
    find eq_A_dec a l1 = find eq_A_dec a l2.
Proof.
elim l1; try contradiction.
intros p lp Hind HNoDup Hincl Hin.
destruct p as (a', b').
assert (Hl2eq: exists l1' l2', l2 = l1' ++ (a' ,b') :: l2').
  apply in_split; apply Hincl; apply in_eq.
destruct Hl2eq as [l1' [l2' Hl2eq]].
case Hin.
- simpl; intros ->.
  case (eq_A_dec a a) as [ | ?]; try contradiction.
  rewrite Hl2eq.
  rewrite Hl2eq in HNoDup.
  now rewrite <- (NoDup_find eq_A_dec l1' _ a b' HNoDup).
- intro Hinflp; simpl.
  case (eq_A_dec a a') as [Ha_eq_a' | Hneq].
  + rewrite Hl2eq.
    rewrite <- Ha_eq_a'.
    rewrite NoDup_find; try reflexivity.
    rewrite Ha_eq_a'.
    now rewrite <- Hl2eq.
  + apply Hind; try assumption.
    apply incl_tran with (m := (a', b') :: lp); try assumption.
    apply incl_tl.
    now apply incl_refl.
Qed.

(*****************************)
(*       Substitution        *)
(*****************************)

Definition substitution := list (log_variable * term).

(*applies a substitution to a term*)
Fixpoint applySubstitution (sigma : substitution) (t : term) {struct t} : term :=
  match t with
  | Var v =>
            match find eq_variable_dec v sigma with
            | None => t
            | Some vSigma => vSigma
            end
  | SetC t1 t2 => SetC (applySubstitution sigma t1) (applySubstitution sigma t2)
  | OTerm f l => OTerm f (map (applySubstitution sigma) l)
  | EmptySet => EmptySet
  end.

(*applies a substitution to a primitiveConstraint*)
Definition applySubstitutionToPC (sigma : substitution) (pc : primitiveConstraint) : primitiveConstraint :=
  match pc with
  | Eq t1 t2 => Eq (applySubstitution sigma t1) (applySubstitution sigma t2)
  | Neq t1 t2 => Neq (applySubstitution sigma t1) (applySubstitution sigma t2)
  | Mem t1 t2 => Mem (applySubstitution sigma t1) (applySubstitution sigma t2)
  | Nmem t1 t2 => Nmem (applySubstitution sigma t1) (applySubstitution sigma t2)
  | FalseC => FalseC
  | IsSet t => IsSet (applySubstitution sigma t)
  end.

(*applies a substitution to a constraint*)
Definition applySubstitutionToC (sigma : substitution) (c : constraint) : constraint :=
  map (applySubstitutionToPC sigma) c.

(*******************************************************)
(*              properties of substitution             *)
(*******************************************************)

Lemma applySub_SetC sigma t1 t2 :
  (applySubstitution sigma ({{t1 | t2}})) =
                 {{applySubstitution sigma t1 | applySubstitution sigma t2}}.
Proof.
trivial.
Qed.

Lemma applySubToC_app sigma c1 c2 :
  (applySubstitutionToC sigma (c1 ++ c2)) =
                 (applySubstitutionToC sigma c1) ++ (applySubstitutionToC sigma c2).
Proof.
unfold applySubstitutionToC.
now rewrite map_app.
Qed.

Lemma In_applySubstitution pc c sigma :
  In pc (applySubstitutionToC sigma c) ->
    exists pc', (In pc' c) /\ (pc = applySubstitutionToPC sigma pc').
Proof.
elim c; try contradiction.
intros pc' c' Hind HIn.
case HIn as [<- | HIn].
- exists pc'.
  split; try reflexivity.
  now apply in_eq.
- destruct (Hind HIn) as [pc'' [? Heq]].
  exists pc''.
  split; try assumption.
  now apply in_cons.
Qed.

Lemma applySubstitution_nil t :
  (applySubstitution nil t) = t.
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) -> (applySubstitution nil t') = t')).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind]; intros t'.
- intro.
  absurd (sizet t' <= 0); try assumption.
  now apply sizet_gte_1.
- case t'; try now intros.
  + intros t1 t2 Hsizet.
    destruct (sizet_SetC Hsizet) as [Hsizet1 Hsizet2].
    simpl; rewrite (Hind _ Hsizet1).
    now rewrite (Hind _ Hsizet2).
  + intros s lt.
    elim lt; try trivial.
    intros t'' lt' Hind' HsizetOT.
    assert (Hsizet'' : sizet t'' <= n).
      apply sizet_OTerm with (s := s) (lt := (t'' :: lt')); try assumption.
      now apply in_eq.
    simpl; rewrite (Hind _ Hsizet'').
    enough (H : (s = s) /\ (map (applySubstitution nil) lt' = lt')).
      now destruct H as [_ ->].
    apply OTerm_eq_iff.
    simpl; apply Hind'.
    simpl; apply le_n_S.
    simpl in HsizetOT.
    rewrite plus_n_Sm in HsizetOT.
    apply le_S_n.
    now apply (le_add_r _ _ HsizetOT).
Qed.

Lemma applySubstitutionToPC_nil pc :
  (applySubstitutionToPC nil pc) = pc.
Proof.
unfold applySubstitutionToPC.
case pc; intros; try now do 2 rewrite applySubstitution_nil.
- reflexivity.
- now rewrite applySubstitution_nil.
Qed.

Lemma applySubstitutionToC_nil c :
  (applySubstitutionToC nil c) = c.
Proof.
elim c; try trivial.
intros pc c' Hind.
simpl; rewrite applySubstitutionToPC_nil.
now rewrite Hind.
Qed.

Lemma applySub_listElements sigma t1 t2 :
  In t1 (listElements t2) ->
     In (applySubstitution sigma t1) (listElements (applySubstitution sigma t2)).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) -> In t1 (listElements t') ->
          In (applySubstitution sigma t1) (listElements (applySubstitution sigma t')))).
enough (H : (forall n, (P n))).
  apply (H (sizet t2)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' ?.
  now absurd (sizet t' <= 0); [apply sizet_gte_1 | assumption].
- intro t'.
  case t'.
  + intro; contradiction.
  + intros t3 t4 Hsizet HIn.
    rewrite applySub_SetC.
    case HIn as [-> | HIn34]; try now left.
    right; apply Hind; try assumption.
    now destruct (sizet_SetC Hsizet).
  + intros; contradiction.
  + intro; contradiction.
Qed.

Lemma applySub_cons v t1 t2 sigma :
  (applySubstitution sigma (applySubstitution ((v, t1) :: nil) t2)) =
    (applySubstitution ((v, (applySubstitution sigma t1)) :: sigma) t2).
Proof.
set (P := fun (n : nat) => (forall t, ((sizet t) <= n) ->
  (applySubstitution sigma (applySubstitution ((v, t1) :: nil) t)) =
    (applySubstitution ((v, (applySubstitution sigma t1)) :: sigma) t))).
enough (H : (forall n, (P n))).
  apply (H (sizet t2)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t ?.
  now absurd (sizet t <= 0); [apply sizet_gte_1 | assumption].
- intro t.
  case t.
  + intros v' Hsizet.
    now simpl; case (eq_variable_dec v' v).
  + intros t3 t4 Hsizet.
    destruct (sizet_SetC Hsizet) as [Hsizet3 Hsizet4].
    simpl; rewrite (Hind _ Hsizet3).
    now rewrite (Hind _ Hsizet4).
  + intros s lt Hsizet.
    simpl; apply OTerm_eq_iff.
    split; try reflexivity.
    rewrite map_map.
    apply map_ext_in.
    intros t' HIn.
    rewrite (Hind t'); try reflexivity.
    now apply (sizet_OTerm Hsizet).
  + reflexivity.
Qed.

Lemma applySubToPC_cons v t sigma pc :
  (applySubstitutionToPC sigma (applySubstitutionToPC ((v, t) :: nil) pc)) =
    (applySubstitutionToPC ((v, (applySubstitution sigma t)) :: sigma) pc).
Proof.
case pc; try now intros; simpl; do 2 rewrite applySub_cons.
- reflexivity.
- now intro; simpl; rewrite applySub_cons.
Qed.

Lemma applySubToC_cons v t sigma c :
  (applySubstitutionToC sigma (applySubstitutionToC ((v, t) :: nil) c)) =
    (applySubstitutionToC ((v, (applySubstitution sigma t)) :: sigma) c).
Proof.
unfold applySubstitutionToC.
rewrite map_map.
apply map_ext.
intro pc.
now apply applySubToPC_cons.
Qed.

Lemma applySub_listSetC t lt sigma :
  applySubstitution sigma (listSetC lt t) = listSetC (map (applySubstitution sigma) lt) (applySubstitution sigma t).
Proof.
set (P := fun (n : nat) => (forall t1 lt1, ((length lt1) <= n) ->
  applySubstitution sigma (listSetC lt1 t1) = listSetC (map (applySubstitution sigma) lt1) (applySubstitution sigma t1))).
enough (H : (forall n, (P n))).
  now apply (H (length lt)); try assumption.
intro n.
induction n as [ | n Hind]; intros t1 lt1.
- intros Hlength.
  assert (Heq_nil : lt1 = nil).
    apply length_zero_iff_nil.
    now apply PeanoNat.Nat.le_0_r.
  now rewrite Heq_nil.
- elim lt1; try reflexivity.
  intros t2 lt2.
  elim lt2; try reflexivity.
  intros t3 lt3 ? ? ?.
  enough (He : applySubstitution sigma (listSetC (t3 :: lt3) t1) =
               listSetC (map (applySubstitution sigma) (t3 :: lt3)) (applySubstitution sigma t1)).
    simpl in He.
    now simpl; rewrite <- He.
  apply Hind.
  now apply le_S_n.
Qed.

Lemma setTerm_applySub t sigma :
  setTerm t -> setTerm (applySubstitution sigma t).
Proof.
intro HsetTerm.
destruct (setTerm_exists_listSetC _ HsetTerm) as [lt ->].
rewrite applySub_listSetC.
case (list_eq_dec eq_term_dec (map (applySubstitution sigma) lt) nil) as [-> | Hneq]; try now trivial.
now rewrite setTerm_listSetC.
Qed.

Lemma applySub_EmptySet v sigma t :
  applySubstitution sigma (Var v) = EmptySet ->
    applySubstitution ((v, EmptySet) :: sigma) t = applySubstitution sigma t.
Proof.
intro Heq.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) ->
    applySubstitution ((v, EmptySet) :: sigma) t' = applySubstitution sigma t')).
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
    now simpl; case (eq_variable_dec v' v) as [-> | ?].
  + intros t1 t2 Hsizet.
    destruct (sizet_SetC Hsizet) as [? ?].
    assert (Heq1 : applySubstitution ((v, EmptySet) :: sigma) t1 = applySubstitution sigma t1).
      now apply Hind.
    assert (Heq2 : applySubstitution ((v, EmptySet) :: sigma) t2 = applySubstitution sigma t2).
      now apply Hind.
    simpl; rewrite Heq1.
    now rewrite Heq2.
  + intros s lt.
    elim lt; try now intro.
    intros t'' lt' Hind' Hsizet.
    assert (Heq1 : applySubstitution ((v, EmptySet) :: sigma) t'' = applySubstitution sigma t'').
      apply Hind.
      apply sizet_OTerm with (s := s) (lt := (t'' :: lt')); try assumption.
      now apply in_eq.
    assert (Heq2 : applySubstitution ((v, EmptySet) :: sigma) (OTerm s lt') = applySubstitution sigma (OTerm s lt')).
      apply Hind'.
      simpl; apply le_n_S.
      simpl in Hsizet.
      rewrite plus_n_Sm in Hsizet.
      apply le_S_n.
      now apply (le_add_r _ _ Hsizet).
    simpl; rewrite Heq1.
    now inversion Heq2.
  + now intro.
Qed.

Lemma applySubPC_EmptySet v sigma pc :
  applySubstitution sigma (Var v) = EmptySet ->
    applySubstitutionToPC ((v, EmptySet) :: sigma) pc = applySubstitutionToPC sigma pc.
Proof.
intro Heq.
case pc; try now intros ? ?; simpl; do 2 rewrite (applySub_EmptySet _ _ _ Heq).
- now trivial.
- now intro; simpl; rewrite (applySub_EmptySet _ _ _ Heq).
Qed.

Lemma applySubC_EmptySet v sigma c :
  applySubstitution sigma (Var v) = EmptySet ->
    applySubstitutionToC ((v, EmptySet) :: sigma) c = applySubstitutionToC sigma c.
Proof.
intro Heq.
elim c; try trivial.
intros pc c' Hind.
simpl; rewrite Hind.
now rewrite applySubPC_EmptySet.
Qed.

Lemma listElements_applySub_map t sigma :
  ~ isVariable (LastFromSetC t) ->
    listElements (applySubstitution sigma t) = map (applySubstitution sigma) (listElements t).
Proof.
set (P := fun (n : nat) => (forall t', ((sizet t') <= n) -> ~ isVariable (LastFromSetC t') ->
            listElements (applySubstitution sigma t') = map (applySubstitution sigma) (listElements t'))).
enough (H : (forall n, (P n))).
  apply (H (sizet t)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t' Hsizet.
  now absurd (sizet t' <= 0); [apply sizet_gte_1 | assumption].
- intro t'.
  case t'; try now intros.
  + now intros ?; simpl; contradiction.
  + intros t1 t2.
    case t2; try now intros.
    * now intros v' ?; simpl; contradiction.
    * intros t3 t4 Hsizet HneqVar.
      enough (He : listElements (applySubstitution sigma t4) = map (applySubstitution sigma) (listElements t4)).
        now simpl; rewrite He.
      apply Hind; try assumption.
      destruct (sizet_SetC Hsizet) as [_ Hsizet'].
      apply le_trans with (m := sizet ({{t3 | t4}})); try assumption.
      simpl; apply le_S.
      now apply le_plus_r.
Qed.

Lemma setTerm_negsetTerm_tail_exists_Var t1 t2 sigma :
  setTerm (applySubstitution sigma ({{t1 | t2}})) ->
    ~ setTerm t2 ->
      exists v, tail t2 = Some (Var v).
Proof.
set (P := fun (n : nat) => (forall t1' t2', ((sizet t2') <= n) -> 
      setTerm (applySubstitution sigma ({{t1' | t2'}})) ->
    ~ setTerm t2' -> exists v, tail t2' = Some (Var v))).
enough (H : (forall n, (P n))).
  apply (H (sizet t2)).
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros t1' t2' Hsizet.
  now absurd (sizet t2' <= 0); [apply sizet_gte_1 | assumption].
- intros t1' t2'.
  case t2'.
  + intros u _ _ _.
    now exists u.
  + intros t3' t4' Hsizet.
    enough (He : setTerm (applySubstitution sigma ({{t3' | t4'}})) ->
                  ~ setTerm t4' -> exists v : log_variable, tail t4' = Some (Var v)).
      trivial.
    apply Hind.
    now destruct (sizet_SetC Hsizet).
  + now intros s lt _; contradiction.
  + now intros _ _; simpl; contradiction.
Qed.

