(****************************************
Maximiliano Cristia - Ricardo David Katz 
                  2026                   
****************************************)

Set Implicit Arguments.

Require Import Arith List Decidable.
Require Import preliminaries terms_constraints list_variables depths substitution valuation interpretation.

Definition satisfies (sigma : substitution) (c : constraint) : Prop :=
  interpretC (applySubstitutionToC sigma c) /\
  listVarInC (applySubstitutionToC sigma c) = nil.

Definition satisfiable (c : constraint) : Prop :=
  exists sigma, satisfies sigma c.

Lemma satisfiable_simple_sub (c : constraint) :
  satisfiable c -> exists sigma, ((incl (map fst sigma) (listVarInC c)) /\ (NoDup (map fst sigma)) /\
    ((interpretC (applySubstitutionToC sigma c)) /\ (listVarInC (applySubstitutionToC sigma c)) = nil)).
Proof.
intros [sigma [Hinterp Hnil]].
set (sigma_fun := fun (v : log_variable) => (v, match (find eq_variable_dec v sigma) with 
                                                | (Some t) => t 
                                                | None => Var v
                                                end )).
assert (Hfst : forall lv, (map fst (map sigma_fun lv)) = lv).
  intro lv.
  elim lv; try reflexivity.
  intros v' lv' Hind.
  now simpl; rewrite Hind.
set (sigma' := (map sigma_fun (nodup eq_variable_dec (listVarInC c)))).
assert (Hfst_sigma' : map fst sigma' = (nodup eq_variable_dec (listVarInC c))).
  now apply Hfst.
enough (He : forall c', incl (listVarInC c') (listVarInC c) ->
                        (applySubstitutionToC sigma' c') = (applySubstitutionToC sigma c')).
  exists sigma'.
  split.
  - rewrite Hfst_sigma'.
    now apply incl_nodup.
  - split.
    + rewrite Hfst_sigma'.
      now apply NoDup_nodup.
    + split.
      * now rewrite (He c); [assumption | apply incl_refl].
      * enough (Heq : (applySubstitutionToC sigma' c) = (applySubstitutionToC sigma c)).
          now rewrite Heq.
        apply He.
        now apply incl_refl.
- intros c'.
  elim c'; try reflexivity.
  intros pc c1 Hind Hincl.
  simpl in Hincl.
  destruct (incl_app_inv _ _ Hincl) as [Hinclpc Hinclc1].
  simpl; rewrite (Hind Hinclc1).
  enough (He : forall pc, incl (listVarInPC pc) (listVarInC c) ->
                          applySubstitutionToPC sigma' pc = applySubstitutionToPC sigma pc).
    now rewrite (He pc).
  assert (He' : forall t, incl (listVarInT t) (listVarInC c) ->
                          applySubstitution sigma' t = applySubstitution sigma t).
    set (P := fun (n : nat) => (forall t', ((sizet t') <= n) -> incl (listVarInT t') (listVarInC c) ->
                               applySubstitution sigma' t' = applySubstitution sigma t')).
    enough (H : (forall n, (P n))).
      now intro t; apply (H (sizet t)).
    intro n.
    induction n as [ | n Hind'].
    + intros t' Hsizet_plus.
      absurd (sizet t' <= 0); try assumption.
      now apply sizet_gte_1.
    + intros t'.
      case t'.
      * intros v _ Hincl'.
        simpl in Hincl'.
        simpl.
        assert (HIn : In v (map fst sigma')).
          rewrite Hfst_sigma'.
          apply nodup_In.
          apply Hincl'.
          apply in_eq.
        destruct (find_exists_some_r eq_variable_dec _ _ HIn) as [p [HInp [Hfstp ->]]].
        unfold sigma' in HInp.
        assert (Hexists : exists v', sigma_fun v' = p /\ In v' (nodup eq_variable_dec (listVarInC c))).
          now apply in_map_iff.
        destruct Hexists as [v' [Heq' HInv']].
        unfold sigma_fun in Heq'.
        rewrite <- Heq' in Hfstp.
        simpl in Hfstp.
        rewrite <- Heq'.
        now simpl; rewrite Hfstp.
      * intros t1 t2 Hsizet Hincl12.
        destruct (sizet_SetC Hsizet) as [Hsizet1 Hsizet2].
        destruct (incl_app_inv _ _ Hincl12) as [Hincl1 Hincl2].
        simpl; rewrite (Hind' _ Hsizet1); try assumption.
        now rewrite (Hind' _ Hsizet2).
      * intros s lt.
        elim lt; try reflexivity.
        intros t2 lt2 Hind2 HsizetOT HinclOT.
        simpl in HinclOT.
        destruct (incl_app_inv _ _ HinclOT) as [Hincl2 HinclOT2].
        assert (Hsizet2 : sizet t2 <= n).
          simpl in HsizetOT.
          rewrite <- plus_Sn_m in HsizetOT.
          apply le_S_n.
          now apply (le_add_l _ _ HsizetOT).
        simpl; rewrite (Hind' _ Hsizet2 Hincl2).
        enough (He : applySubstitution sigma' (OTerm s lt2) = applySubstitution sigma (OTerm s lt2)).
          now inversion He.
        apply Hind2; try assumption.
        apply le_trans with (m := sizet (OTerm s (t2 :: lt2))); try assumption.
        simpl; apply le_n_S.
        now apply le_plus_r.
      * reflexivity.
    + intro pc'.
      case pc'.
      * intros t1 t2 HinclPC.
        destruct (incl_app_inv _ _ HinclPC) as [Hincl1 Hincl2].
        simpl; rewrite (He' t1); try assumption.
        now rewrite (He' t2).
      * intros t1 t2 HinclPC.
        destruct (incl_app_inv _ _ HinclPC) as [Hincl1 Hincl2].
        simpl; rewrite (He' t1); try assumption.
        now rewrite (He' t2).
      * intros t1 t2 HinclPC.
        destruct (incl_app_inv _ _ HinclPC) as [Hincl1 Hincl2].
        simpl; rewrite (He' t1); try assumption.
        now rewrite (He' t2).
      * intros t1 t2 HinclPC.
        destruct (incl_app_inv _ _ HinclPC) as [Hincl1 Hincl2].
        simpl; rewrite (He' t1); try assumption.
        now rewrite (He' t2).
      * reflexivity.
      * intros t ?.
        now simpl; rewrite (He' t).
Qed.

(* Theorem 9.4 of Dovier et al 2000 *)
Theorem satisfiability (c : constraint) :
  isInSFC c -> satisfiable c.
Proof.
intro HisInSFC.
exists (sat_sub c).
split.
- assert (HstepNi : 0 < stepNi c).
    apply Nat.lt_le_trans with (m := 2); [apply Nat.lt_0_2 | apply le_2_stepNi].
  apply interpretC_iff.
  intros pc HInpc.
  destruct (In_applySubstitution _ _ _ HInpc) as [pc' [HInpc' ->]].
  assert (HisInSFPC: isInSFPC pc' c).
    now apply HisInSFC.
  revert HisInSFPC.
  revert HInpc'.
  case pc'.
  + intros t1 t2.
    case t1; try now intros; apply False_ind.
    intro v.
    now case t2; intros; rewrite (applySubstitution_InEq_eq _ _ HInpc' HisInSFC);
      simpl; rewrite (InLHSEq _ _ HInpc' HisInSFC); apply clos_rel_term_refl.
  + intros t1 t2.
    case t1.
    * intros [i].
      case t2.
      -- intros [j] HInc HisInSFPC Hequiv.
         assert (Hincl_i : incl (listVarInT (\V i)) (listVarNotInEqLHS c)).
           intros ? HIn.
           apply (In_listVarNotInEqLHS _ _ HisInSFC HInc).
           case HIn as [? | ?]; [now left | contradiction].
         assert (HiIn : In (LogV i) (listVarNotInEqLHS c)).
           now apply Hincl_i; left.
         assert (Hincl_j : incl (listVarInT (\V j)) (listVarNotInEqLHS c)).
           intros ? HIn.
           apply (In_listVarNotInEqLHS _ _ HisInSFC HInc).
           case HIn as [? | ?]; [right; now left | contradiction].
         assert (HjIn : In (LogV j) (listVarNotInEqLHS c)).
           now apply Hincl_j; left.
         rewrite (incl_listVarInT_applySubstitutiont_eq _ _ Hincl_i) in Hequiv.
         rewrite (incl_listVarInT_applySubstitutiont_eq _ _ Hincl_j) in Hequiv.
         rewrite (sat_partial_sub_eq _ _ HiIn) in Hequiv.
         rewrite (sat_partial_sub_eq _ _ HjIn) in Hequiv.
         assert (Heq : i = j).
           apply eq_add_S.
           apply Nat.mul_cancel_r with (p := stepNi c).
           now apply Nat.neq_0_lt_0.
           now apply clos_rel_term_EmptysetNi.
         rewrite Heq in HisInSFPC.
         now simpl in HisInSFPC.
      -- intros t3 t4 HInc ? Hequiv.
         assert (Hincl_i : incl (listVarInT (\V i)) (listVarNotInEqLHS c)).
           intros ? HIn.
           apply (In_listVarNotInEqLHS _ _ HisInSFC HInc).
           case HIn as [-> | ?]; try contradiction.
           now left.
         assert (HiIn : In (LogV i) (listVarNotInEqLHS c)).
           now apply Hincl_i; left.
         rewrite (incl_listVarInT_applySubstitutiont_eq _ _ Hincl_i) in Hequiv.
         rewrite (sat_partial_sub_eq _ _ HiIn) in Hequiv.
         case (le_lt_or_eq _ _ (depth_EmptySet_le ({{t3 | t4}}) (sat_sub c))) as [Hlt | Heq].
         ++ assert (HdES : (S i * stepNi c) = depth_EmptySet (applySubstitution (sat_sub c) ({{t3 | t4}}))).
              rewrite <- depth_EmptySet_EmptysetNi with (n := S i * stepNi c).
              now apply clos_rel_term_depth_EmptySet.
            destruct (depth_EmptySet_lt_exists _ _ Hlt) as [[j] [Hneq_nil Heq]].
            assert (HjInlistVarInT : In (LogV j) (listVarInT ({{t3 | t4}}))).
              now apply ListDepthsInTerm_listVarInT.
            assert (HjIn : In (LogV j) (listVarNotInEqLHS c)).
              apply In_listVarNotInEqLHS with (pc := ((\V i) \== ({{t3 | t4}}))); try assumption.
              right; apply in_app_iff.
              left; apply in_app_iff.
              now right.
            assert (Hincl_j : incl (listVarInT (\V j)) (listVarNotInEqLHS c)).
              intros ? HIn.
              case HIn as [<- | ?]; [assumption | contradiction].
            revert HdES.
            rewrite Heq.
            rewrite (incl_listVarInT_applySubstitutiont_eq _ _ Hincl_j).
            rewrite (sat_partial_sub_eq _ _ HjIn).
            rewrite depth_EmptySet_EmptysetNi.
            intro Habs.
            case (Nat.lt_trichotomy i j) as [H_i_lt_j | Hor].
            ** enough (Hlt' : S i * stepNi c < S j * stepNi c + list_max (ListDepthsInTerm (LogV j :: nil) ({{t3 | t4}}))).
                 rewrite <- Habs in Hlt'.
                 absurd (S i * stepNi c < S i * stepNi c); try assumption.
                 now apply Nat.lt_irrefl.
               apply lt_plus_trans.
               apply mult_lt_compat_r; try assumption.
               now apply lt_n_S.
            ** case Hor as [H_i_eq_j | H_i_lt_j].
               --- simpl in HisInSFPC.
                   simpl in HjInlistVarInT.
                   assert (Hand : ~ occurCheck (LogV j) t3 /\ ~ occurCheck (LogV j) t4).
                     rewrite <- H_i_eq_j.
                     now apply not_or.
                   destruct Hand.
                   case (in_app_or _ _ _ HjInlistVarInT) as [? | ?].
                   +++ now absurd (occurCheck (LogV j) t3);
                        [assumption | apply In_listVarInT_occurCheck].
                   +++ now absurd (occurCheck (LogV j) t4);
                        [assumption | apply In_listVarInT_occurCheck].
               --- assert (Habs' : list_max (ListDepthsInTerm ((LogV j) :: nil) ({{t3 | t4}})) = (S i - S j) * stepNi c).
                     rewrite Nat.mul_sub_distr_r.
                     now apply plus_minus.
                   enough (Hineq : list_max (ListDepthsInTerm ((LogV j) :: nil) ({{t3 | t4}})) < stepNi c).
                     rewrite Habs' in Hineq.
                     rewrite <- Nat.mul_1_l with (n := stepNi c) in Hineq.
                     rewrite <- mult_assoc_reverse in Hineq.
                     rewrite Nat.mul_1_r in Hineq.
                     absurd (j < i); try assumption.
                     apply le_not_lt.
                     apply le_S_n.
                     apply Nat.sub_0_le.
                     apply Nat.lt_1_r.
                     now apply (Nat.mul_lt_mono_pos_r _ _ _ HstepNi).
                   apply Nat.lt_lt_succ_r.
                   apply le_lt_n_Sm.
                   apply exists_listmax.
                   exists (list_max (ListDepthsNeq (listVarInC c) c)).
                   split.
                   +++ do 2 apply in_cons.
                       now apply in_eq.
                   +++ apply incl_listmax.
                       assert (HListeq : (ListDepthsInTerm (LogV j :: nil) ({{t3 | t4}})) =
                                         (ListDepthsNeq (LogV j :: nil) (((\V i) \== ({{t3 | t4}})) :: nil))).
                         now simpl; do 2 rewrite app_nil_r.
                       rewrite HListeq.
                       apply incl_ListDepthsNeq.
                       *** now apply incl_cons; [assumption | apply incl_nil_l].
                       *** apply incl_cons; try now apply incl_nil_l.
                           now apply incl_remove_list with (l1 := listVarInEqLHS c) (eq_dec := eq_variable_dec).
         ++ assert (Habs : (S i * stepNi c) = depth_EmptySet ({{t3 | t4}})).
              rewrite <- depth_EmptySet_EmptysetNi with (n := (S i * stepNi c)).
              rewrite Heq.
              now apply clos_rel_term_depth_EmptySet.
            enough (Hineq : depth_EmptySet ({{t3 | t4}}) < stepNi c).
              rewrite <- Habs in Hineq.
              rewrite <- Nat.mul_1_l with (n := stepNi c) in Hineq.
              rewrite <- mult_assoc_reverse in Hineq.
              rewrite Nat.mul_1_r in Hineq.
              absurd (i < 0); try apply Nat.nlt_0_r.
              apply lt_S_n.
              now apply Nat.mul_lt_mono_pos_r with (p := stepNi c).
            apply le_lt_n_Sm.
            apply le_S.
            apply exists_listmax.
            exists (list_max (ListFindNiNeq c)).
            split; try now apply in_eq.
            apply exists_listmax.
            exists (depth_EmptySet ({{t3 | t4}})).
            split; try apply le_n.
            apply in_ListFindNiNeq.
            exists (LogV i).
            exists ({{t3 | t4}}).
            now split.
      -- intros s l' HInc _ Hequiv.
         assert (Hincl_i : incl (listVarInT (\V i)) (listVarNotInEqLHS c)).
           intros ? HIn.
           apply (In_listVarNotInEqLHS _ _ HisInSFC HInc).
           apply in_or_app; left.
           case HIn as [? | ?]; try contradiction.
           now left.
         assert (HiIn : In (LogV i) (listVarNotInEqLHS c)).
           now apply Hincl_i; left.
         rewrite (incl_listVarInT_applySubstitutiont_eq _ _ Hincl_i) in Hequiv.
         rewrite (sat_partial_sub_eq _ _ HiIn) in Hequiv.
         simpl in Hequiv.
         enough (setTerm (OTerm s (map (applySubstitution (sat_sub c)) l'))).
           contradiction.
         apply (clos_rel_term_setTerm Hequiv).
         now case (stepNi c + i * stepNi c).
      -- intros Hinc _ Hequiv.
         assert (Hincl_i : incl (listVarInT (\V i)) (listVarNotInEqLHS c)).
           intros ? HIn.
           apply (In_listVarNotInEqLHS _ _ HisInSFC Hinc).
           case HIn as [? | ?]; [now left | contradiction].
         assert (HiIn : In (LogV i) (listVarNotInEqLHS c)).
           now apply Hincl_i; left.
         rewrite (incl_listVarInT_applySubstitutiont_eq _ _ Hincl_i) in Hequiv.
         rewrite (sat_partial_sub_eq _ _ HiIn) in Hequiv.
         assert (Heq : EmptysetNi (S i * stepNi c) = EmptySet).
           now apply clos_rel_term_EmptySet.
         enough (Hpred : (S i * stepNi c) = S (Nat.pred (S i * stepNi c))).
           rewrite Hpred in Heq.
           discriminate.
         apply S_pred with (m := 0).
         apply Nat.mul_pos_pos; try assumption.
         now apply Nat.lt_0_succ.
    * intros; now apply False_ind.
    * intros; now apply False_ind.
    * case t2; intros; try now apply False_ind.
  + intros t ?.
    case t; intros; try now apply False_ind.
  + intros t1 t2.
    case t1.
    * intros [i].
      case t2; try now intros; apply False_ind.
      intros [j] HInc HisInSFPC.
      assert (Hincl_i : incl (listVarInT (\V i)) (listVarNotInEqLHS c)).
        intros ? HIn.
        apply (In_listVarNotInEqLHS _ _ HisInSFC HInc).
        case HIn as [? | ?]; [now left | contradiction].
      assert (Hincl_j : incl (listVarInT (\V j)) (listVarNotInEqLHS c)).
        intros ? HIn.
        apply (In_listVarNotInEqLHS _ _ HisInSFC HInc).
        case HIn as [? | ?]; [right; now left | contradiction].
      assert (HiIn : In (LogV i) (listVarNotInEqLHS c)).
        now apply Hincl_i; left.
      assert (HjIn : In (LogV j) (listVarNotInEqLHS c)).
        now apply Hincl_j; left.
      unfold applySubstitutionToPC.
      rewrite (incl_listVarInT_applySubstitutiont_eq _ _ Hincl_i).
      rewrite (incl_listVarInT_applySubstitutiont_eq _ _ Hincl_j).
      rewrite (sat_partial_sub_eq _ _ HiIn).
      rewrite (sat_partial_sub_eq _ _ HjIn).
      intros [_ [t [Hequiv HtIn]]].
      assert (Heq : t = (EmptysetNi ((S j * stepNi c) - 1))).
        revert HtIn.
        case (S j * stepNi c); try contradiction.
        intros ?; rewrite listElements_EmptysetNi; intro Hor.
        case Hor as [? | ?]; try contradiction.
        apply eq_sym.
        rewrite Nat.sub_1_r.
        now rewrite Nat.pred_succ.
      rewrite Heq in Hequiv.
      assert (Heq' : ((S j) * stepNi c - 1) = ((S i) * stepNi c)).
        now apply clos_rel_term_EmptysetNi.
      rewrite Nat.sub_1_r in Heq'.
      assert (H' : (j - i) = 1 /\ stepNi c = 1).
        apply mult_is_one.
        apply eq_sym.
        rewrite Nat.mul_sub_distr_r.
        apply plus_minus.
        rewrite <- S_eq.
        apply Nat.add_cancel_r with (p := stepNi c).
        rewrite plus_Sn_m.
        rewrite <- Nat.mul_succ_l.
        rewrite <- Nat.mul_succ_l.
        rewrite S_pred with (n := (S j * stepNi c)) (m := 0).
        now apply eq_S.
        apply Nat.mul_pos_pos; try assumption.
        now apply Nat.lt_0_succ.
      destruct H' as [_ Habs].
      absurd (2 <= 1); try apply Nat.nle_succ_diag_l.
      assert (HstepNi' : 2 <= stepNi c).
        now apply le_2_stepNi.
      now rewrite <- Habs.
    * intros t3 t4.
      case t2.
      -- intros [i] HInc HisInSFPC.
         assert (Hpos : 0 < (S i) * (stepNi c)).
           apply Nat.mul_pos_pos; try assumption.
           now apply Nat.lt_0_succ.
         assert (Hincl_i : incl (listVarInT (\V i)) (listVarNotInEqLHS c)).
           intros ? HIn.
           apply (In_listVarNotInEqLHS _ _ HisInSFC HInc).
           case HIn as [-> | ?]; try contradiction.
           apply in_or_app; left.
           apply in_or_app; right.
           now left.
         assert (HiIn : In (LogV i) (listVarNotInEqLHS c)).
           apply Hincl_i.
           now left.
         unfold applySubstitutionToPC.
         rewrite (incl_listVarInT_applySubstitutiont_eq _ _ Hincl_i).
         rewrite (sat_partial_sub_eq _ _ HiIn).
         intros [_ [t [Hequiv HtIn]]].
         assert (Hteq : t = (EmptysetNi ((S i * stepNi c) - 1))).
           revert HtIn.
           case (S i * stepNi c); try contradiction.
           intros ?; rewrite listElements_EmptysetNi; intro Hor.
           case Hor as [? | ?]; try contradiction.
           apply eq_sym.
           rewrite Nat.sub_1_r.
           now rewrite Nat.pred_succ.
         rewrite Hteq in Hequiv.
         case (le_lt_or_eq _ _ (depth_EmptySet_le ({{t3 | t4}}) (sat_sub c))) as [Hlt | Heq].
         ++ assert (HdES : (S i * stepNi c - 1) = depth_EmptySet (applySubstitution (sat_sub c) ({{t3 | t4}}))).
              rewrite <- depth_EmptySet_EmptysetNi with (n := S i * stepNi c - 1).
              now apply clos_rel_term_depth_EmptySet.
            destruct (depth_EmptySet_lt_exists _ _ Hlt) as [[j] [Hneq_nil Heq]].
            assert (HjInlistVarInT : In (LogV j) (listVarInT ({{t3 | t4}}))).
              now apply ListDepthsInTerm_listVarInT.
            assert (HjIn : In (LogV j) (listVarNotInEqLHS c)).
              apply In_listVarNotInEqLHS with (pc := (({{t3 | t4}}) \:s (\V i))); try assumption.
              apply in_remove_list; split; try now apply FindEqTerm_None.
              apply in_app_iff; left.
              now apply in_app_iff; left.
            assert (Hincl_j : incl (listVarInT (\V j)) (listVarNotInEqLHS c)).
              intros ? HIn.
              now case HIn as [<- | ?]; [assumption | contradiction].
            revert HdES.
            rewrite Heq.
            rewrite (incl_listVarInT_applySubstitutiont_eq _ _ Hincl_j).
            rewrite (sat_partial_sub_eq _ _ HjIn).
            rewrite depth_EmptySet_EmptysetNi.
            intro Habs.
            case (Nat.lt_trichotomy i j) as [H_i_lt_j | Hor].
            ** enough (Hlt' : S i * stepNi c - 1 < S j * stepNi c + list_max (ListDepthsInTerm (LogV j :: nil) ({{t3 | t4}}))).
                 rewrite <- Habs in Hlt'.
                 absurd (S i * stepNi c - 1 < S i * stepNi c - 1); try assumption.
                 now apply Nat.lt_irrefl.
               rewrite <- pred_of_minus.
               apply Nat.lt_lt_pred.
               apply lt_plus_trans.
               apply mult_lt_compat_r; try assumption.
               now apply lt_n_S.
            ** case Hor as [H_i_eq_j | H_i_lt_j].
               --- simpl in HisInSFPC.
                   simpl in HjInlistVarInT.
                   assert (Hand : ~ occurCheck (LogV j) t3 /\ ~ occurCheck (LogV j) t4).
                     rewrite <- H_i_eq_j.
                     now apply not_or.
                   destruct Hand.
                   case (in_app_or _ _ _ HjInlistVarInT) as [? | ?].
                   +++ now absurd (occurCheck (LogV j) t3);
                         [assumption | apply In_listVarInT_occurCheck].
                   +++ now absurd (occurCheck (LogV j) t4);
                         [assumption | apply In_listVarInT_occurCheck].
               --- assert (Hpos' : 0 < (S i - S j) * (stepNi c)).
                     apply Nat.mul_pos_pos; try assumption.
                     rewrite Nat.sub_succ.
                     apply Nat.lt_add_lt_sub_r.
                     now rewrite plus_O_n.
                   assert (Habs' : S (list_max (ListDepthsInTerm ((LogV j) :: nil) ({{t3 | t4}}))) = (S i - S j) * (stepNi c)).
                     rewrite <- (Nat.succ_pred_pos _ Hpos').
                     apply eq_S.
                     rewrite Nat.mul_sub_distr_r.
                     rewrite pred_of_minus.
                     rewrite <- Nat.sub_add_distr.
                     rewrite plus_comm.
                     rewrite Nat.sub_add_distr.
                     rewrite Habs.
                     now rewrite minus_plus.
                   enough (Hineq : S (list_max (ListDepthsInTerm ((LogV j) :: nil) ({{t3 | t4}}))) < stepNi c).
                     rewrite Habs' in Hineq.
                     rewrite <- Nat.mul_1_l with (n := stepNi c) in Hineq.
                     rewrite <- mult_assoc_reverse in Hineq.
                     rewrite Nat.mul_1_r in Hineq.
                     absurd (j < i); try assumption.
                     apply le_not_lt.
                     apply le_S_n.
                     apply Nat.sub_0_le.
                     apply Nat.lt_1_r.
                     now apply (Nat.mul_lt_mono_pos_r _ _ _ HstepNi).
                   apply lt_n_S.
                   apply le_lt_n_Sm.
                   apply exists_listmax.
                   exists (list_max (ListDepthsNin (listVarInC c) c)).
                   split.
                   +++ do 3 apply in_cons.
                       now apply in_eq.
                   +++ apply incl_listmax.
                       assert (HListeq : (ListDepthsInTerm (LogV j :: nil) ({{t3 | t4}})) =
                                         (ListDepthsNin (LogV j :: nil) ((({{t3 | t4}}) \:s (\V i)) :: nil))).
                         now simpl; do 2 rewrite app_nil_r.
                       rewrite HListeq.
                       apply incl_ListDepthsNin.
                       *** now apply incl_cons; [assumption | apply incl_nil_l].
                       *** apply incl_cons; try now apply incl_nil_l.
                           now apply incl_remove_list with (l1 := listVarInEqLHS c) (eq_dec := eq_variable_dec).
         ++ assert (Habs : S i * stepNi c = S (depth_EmptySet ({{t3 | t4}}))).
              rewrite <- (Nat.succ_pred_pos _ Hpos).
              apply eq_S.
              rewrite pred_of_minus.
              rewrite <- depth_EmptySet_EmptysetNi with (n := (S i * stepNi c - 1)).
              rewrite Heq.
              now apply clos_rel_term_depth_EmptySet.
            enough (Hineq : S (depth_EmptySet ({{t3 | t4}})) < stepNi c).
              rewrite <- Habs in Hineq.
              rewrite <- Nat.mul_1_l with (n := stepNi c) in Hineq.
              rewrite <- mult_assoc_reverse in Hineq.
              rewrite Nat.mul_1_r in Hineq.
              absurd (i < 0); try apply Nat.nlt_0_r.
              apply lt_S_n.
              now apply Nat.mul_lt_mono_pos_r with (p := stepNi c).
            apply lt_n_S.
            apply le_lt_n_Sm.
            apply exists_listmax.
            exists (list_max (ListFindNiNin c)).
            split.
            ** apply in_cons.
               now apply in_eq.
            ** apply exists_listmax.
               exists (depth_EmptySet ({{t3 | t4}})).
               split; try apply le_n.
               apply in_ListFindNiNin.
               exists (LogV i).
               exists ({{t3 | t4}}).
               now split.
      -- intros; now apply False_ind.
      -- intros; now apply False_ind.
      -- intros; now apply False_ind.
    * intros s l.
      case t2; try now intros; apply False_ind.
      intros [i] HInc _.
      assert (Hincl_i : incl (listVarInT (\V i)) (listVarNotInEqLHS c)).
        intros ? ?.
        apply (In_listVarNotInEqLHS _ _ HisInSFC HInc).
        apply in_or_app; left.
        now apply in_or_app; right.
      unfold applySubstitutionToPC.
      rewrite (incl_listVarInT_applySubstitutiont_eq _ _ Hincl_i).
      assert (HiIn : In (LogV i) (listVarNotInEqLHS c)).
        now apply Hincl_i; left.
      rewrite (sat_partial_sub_eq _ _ HiIn).
      intros [_ [t [Hequiv HtIn]]].
      revert HtIn.
      case (S i * stepNi c); try contradiction.
      intros j HtIn.
      case HtIn; try contradiction.
      intro Heqt.
      rewrite <- Heqt in Hequiv.
      enough (setTerm (OTerm s (map (applySubstitution (sat_sub c)) l))).
        contradiction.
      apply (clos_rel_term_setTerm Hequiv).
      now case j.
    * case t2; try now intros; apply False_ind.
      intros [i] HInc _.
      assert (Hpos : 0 < (S i) * (stepNi c)).
        apply Nat.mul_pos_pos; try assumption.
        now apply Nat.lt_0_succ.
      assert (Hpos' : 0 < Nat.pred ((S i) * (stepNi c))).
        apply lt_pred.
        rewrite Nat.mul_comm.
        apply Nat.lt_1_mul_pos; try apply Nat.lt_0_succ.
        now apply Nat.lt_le_trans with (m := 2); [apply Nat.lt_1_2 | apply le_2_stepNi].
      assert (Hincl_i : incl (listVarInT (\V i)) (listVarNotInEqLHS c)).
        intros [j] HjIn.
        apply (In_listVarNotInEqLHS _ _ HisInSFC HInc).
        now case HjIn.
      assert (HIn : In (LogV i) (listVarNotInEqLHS c)).
        now apply Hincl_i; left.
      unfold applySubstitutionToPC.
      rewrite (incl_listVarInT_applySubstitutiont_eq _ _ Hincl_i).
      rewrite (sat_partial_sub_eq _ _ HIn).
      intros [_ [t [Hequiv HtIn]]].
      assert (Hexists : exists h, (S i * stepNi c) = S (S h)).
        exists (Nat.pred (Nat.pred (S i * stepNi c))).
        rewrite <- (S_pred _ _ Hpos').
        now rewrite <- (S_pred _ _ Hpos).
      destruct Hexists as [h Heq].
      rewrite Heq in HtIn.
      rewrite listElements_EmptysetNi in HtIn.
      case HtIn; try contradiction.
      intro Heq'.
      assert (Heq'' : EmptysetNi (S h) = EmptySet).
        apply clos_rel_term_EmptySet.
        now rewrite Heq'.
      discriminate.
  + intros; now apply False_ind.
  + intro t.
    case t; try now intros; apply False_ind.
    intros [i] HInc _.
    assert (Hincl_i : incl (listVarInT (\V i)) (listVarNotInEqLHS c)).
      apply incl_cons; try now apply incl_nil_l.
      apply (In_listVarNotInEqLHS _ _ HisInSFC HInc).
      now left.
    assert (HiIn : In (LogV i) (listVarNotInEqLHS c)).
      now apply Hincl_i; left.
    unfold applySubstitutionToPC.
    rewrite (incl_listVarInT_applySubstitutiont_eq _ _ Hincl_i).
    rewrite (sat_partial_sub_eq _ _ HiIn).
    now case (S i * stepNi c).
- rewrite listVarInC_remove_list.
  + unfold sat_sub; rewrite fst_sat_sub_aux.
    now rewrite remove_list_nodup.
  + intro; now apply snd_sat_sub_listVar_nil.
Qed.

