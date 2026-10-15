(****************************************
Maximiliano Cristia - Ricardo David Katz 
                  2026                   
****************************************)

Set Implicit Arguments.

Require Import Arith List.

Require Import RelationClasses.
Require Import Relations.
Require Import Transitive_Closure.
Require Import preliminaries terms_constraints rewritings list_variables depths substitution interpretation satisfiability sort_complete.

(* Coq version of item (1) of Theorem 10.11 (or one implication of Lemma 14.7) of Dovier et al. 2000 *)
Theorem soundness c1 c2 :
  stepStar c1 c2 -> sort_complete c1 -> satisfiable c2 -> 
    satisfiable c1.
Proof.
intros HstepStar Hsort_c Hsatisfiable_p2.
set (P := fun c1' c2' : constraint => sort_complete c1' -> satisfiable c2' -> satisfiable c1').
enough (H : forall c1' c2', stepStar c1' c2' -> P c1' c2').
  now apply (H c1 c2).
apply clos_refl_trans_ind.
- intros p3 p4 Hstep.
  case Hstep; intros p3' p4'.
  + intro HstepEq.
    case HstepEq.
    * intros t c c3 c4 Hdecom Hsort Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      simpl in Hinter.
      rewrite applySubToC_app in Hinter.
      assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
        now apply interpretC_app.
      destruct Hand as [H1 H2].
      rewrite (decompose_eq Hdecom).
      case t.
      -- intro v.
         case (in_dec eq_variable_dec v (listVarInC (c3 ++ c4))) as [HIn | HnIn].
         ++ exists sigma.
            split; simpl; rewrite applySubToC_app.
            ** apply interpretC_app.
               split; try assumption.
               split; try assumption.
               now apply clos_rel_term_refl.
            ** rewrite listVarInC_app.
               simpl; destruct (app_eq_nil _ _ H_lVar_nil) as [-> ->].
               rewrite app_nil_r.
               rewrite app_nil_l.
               enough (He : listVarInT (applySubstitution sigma (Var v)) = nil).
                 simpl in He; now rewrite He.
               apply listVarInC_applySub_nil with (c := c3 ++ c4); try assumption.
               rewrite applySubToC_app.
               now rewrite listVarInC_app.
         ++ rewrite listVarInC_app in HnIn.
            simpl in HnIn.
            destruct (neg_in_app _ _ _ HnIn) as [HnIn1 HnIn2].
            exists ((v, EmptySet) :: sigma).
            split; simpl; rewrite applySubToC_app; simpl;
              case (eq_variable_dec v v) as [_ | ?]; try contradiction.
            ** apply interpretC_app.
               split; try now rewrite neq_listVarInC_applySub.
               split; try now apply clos_rel_term_refl.
               now rewrite neq_listVarInC_applySub.
            ** rewrite listVarInC_app.
               simpl; rewrite neq_listVarInC_applySub; try assumption.
               now rewrite neq_listVarInC_applySub.
      -- intros t1 t2.
         set (l := remove_list eq_variable_dec (listVarInC (c3 ++ c4)) (listVarInT ({{t1 | t2}}))).
         set (EmptySet_fun := fun (v : log_variable) => (v, EmptySet)).
         set (sigma' := sigma ++ (map EmptySet_fun l)).
         destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil3 Hnil4].
         assert (Hincl : incl ((listVarInC c3) ++ (listVarInC c4)) (map fst sigma)).
           now apply incl_app; apply listVar_applySubToC_incl.
         destruct (incl_app_inv _ _ Hincl) as [Hincl3 Hincl4].
         assert (Heq3: (applySubstitutionToC sigma' c3) = (applySubstitutionToC sigma c3)).
           unfold sigma'; now rewrite app_applySubToC.
         assert (Heq4: (applySubstitutionToC sigma' c4) = (applySubstitutionToC sigma c4)).
           unfold sigma'; now rewrite app_applySubToC.
         exists sigma'.
         split.
         ++ simpl; rewrite applySubToC_app.
            apply interpretC_app; split; try now rewrite Heq3.
            split; try apply clos_rel_term_refl.
            now rewrite Heq4.
         ++ simpl; rewrite applySubToC_app.
            rewrite listVarInC_app.
            rewrite Heq3.
            rewrite Hnil3.
            rewrite app_nil_l.
            simpl; rewrite Heq4.
            rewrite Hnil4.
            rewrite app_nil_r.
            enough (Heq : listVarInT ((applySubstitution sigma') ({{t1 | t2}})) = nil).
              now simpl in Heq; rewrite Heq.
            rewrite listVarInT_remove_list_r.
            ** apply remove_list_eq_nil.
               unfold sigma'.
               rewrite map_app.
               intros v HIn.
               case (in_dec eq_variable_dec v (listVarInC (c3 ++ c4))) as [HIn' | HnIn].
               --- apply in_or_app; left.
                   rewrite listVarInC_app in HIn'.
                   now case (in_app_or _ _ _ HIn') as [? | ?];
                     [apply (listVar_applySubToC_incl sigma _ Hnil3) | apply (listVar_applySubToC_incl sigma _ Hnil4)].
               --- apply in_or_app; right.
                   apply in_map_iff.
                   exists (v, EmptySet).
                   split; try reflexivity.
                   assert (Heq : (v, EmptySet) = EmptySet_fun v); trivial.
                   rewrite Heq.
                   apply in_map.
                   apply in_remove_list.
                   now split.
            ** intros [v t'] HIn HIn'.
               unfold sigma' in HIn.
               case (in_app_or _ _ _ HIn) as [HIn'' | HIn''].
               --- apply (listVar_applySubToC_nil (c3 ++ c4) sigma); try assumption.
                   +++ rewrite applySubToC_app.
                       rewrite listVarInC_app.
                       rewrite Hnil3.
                       now rewrite Hnil4.
                   +++ simpl in HlVar_incl.
                       apply HlVar_incl.
                       now apply in_map.
               --- assert (Hexists : exists v', EmptySet_fun v' = (v, t') /\ In v' l).
                     now apply in_map_iff.
                   now destruct Hexists as [v' [<- ?]].
      -- intros s lt.
         set (l := remove_list eq_variable_dec (listVarInC (c3 ++ c4)) (listVarInT (OTerm s lt))).
         set (EmptySet_fun := fun (v : log_variable) => (v, EmptySet)).
         set (sigma' := sigma ++ (map EmptySet_fun l)).
         destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil3 Hnil4].
         assert (Hincl : incl ((listVarInC c3) ++ (listVarInC c4)) (map fst sigma)).
           now apply incl_app; apply listVar_applySubToC_incl.
         destruct (incl_app_inv _ _ Hincl) as [Hincl3 Hincl4].
         assert (Heq3: (applySubstitutionToC sigma' c3) = (applySubstitutionToC sigma c3)).
           unfold sigma'; now rewrite app_applySubToC.
         assert (Heq4: (applySubstitutionToC sigma' c4) = (applySubstitutionToC sigma c4)).
           unfold sigma'; now rewrite app_applySubToC.
         exists sigma'.
         split.
         ++ simpl; rewrite applySubToC_app.
            apply interpretC_app; split; try now rewrite Heq3.
            split; try apply clos_rel_term_refl.
            now rewrite Heq4.
         ++ simpl; rewrite applySubToC_app.
            rewrite listVarInC_app.
            rewrite Heq3.
            rewrite Hnil3.
            rewrite app_nil_l.
            simpl; rewrite Heq4.
            rewrite Hnil4.
            rewrite app_nil_r.
            enough (Heq : listVarInT ((applySubstitution sigma') (OTerm s lt)) = nil).
              now simpl in Heq; rewrite Heq.
            rewrite listVarInT_remove_list_r.
            ** apply remove_list_eq_nil.
               unfold sigma'.
               rewrite map_app.
               intros v HIn.
               case (in_dec eq_variable_dec v (listVarInC (c3 ++ c4))) as [HIn' | HnIn].
               --- apply in_or_app; left.
                   rewrite listVarInC_app in HIn'.
                   now case (in_app_or _ _ _ HIn') as [? | ?];
                     [apply (listVar_applySubToC_incl sigma _ Hnil3) | apply (listVar_applySubToC_incl sigma _ Hnil4)].
               --- apply in_or_app; right.
                   apply in_map_iff.
                   exists (v, EmptySet).
                   split; try reflexivity.
                   assert (Heq : (v, EmptySet) = EmptySet_fun v); trivial.
                   rewrite Heq.
                   apply in_map.
                   apply in_remove_list.
                   now split.
            ** intros [v t'] HIn HIn'.
               unfold sigma' in HIn.
               case (in_app_or _ _ _ HIn) as [HIn'' | HIn''].
               --- apply (listVar_applySubToC_nil (c3 ++ c4) sigma); try assumption.
                   +++ rewrite applySubToC_app.
                       rewrite listVarInC_app.
                       rewrite Hnil3.
                       now rewrite Hnil4.
                   +++ simpl in HlVar_incl.
                       apply HlVar_incl.
                       now apply in_map.
               --- assert (Hexists : exists v', EmptySet_fun v' = (v, t') /\ In v' l).
                     now apply in_map_iff.
                   now destruct Hexists as [v' [<- ?]].
      -- exists sigma.
         split.
         ++ simpl; rewrite applySubToC_app.
            apply interpretC_iff.
            intros pc HIn.
            assert (Hinter' : forall pc, In pc (applySubstitutionToC sigma (c3 ++ c4)) -> interpretPC pc).
              apply interpretC_iff.
              now rewrite applySubToC_app.
            case (in_app_or _ _ _ HIn) as [?| HIn'].
            ** apply Hinter'.
               rewrite applySubToC_app.
               now apply in_or_app; left.
            ** case HIn' as [<- | HIn'']; try now apply clos_rel_term_refl.
               apply Hinter'.
               rewrite applySubToC_app.
               now apply in_or_app; right.
         ++ simpl; rewrite applySubToC_app.
            now rewrite listVarInC_app.
    * intros t v c c3 c4 Hdecom HneqVar Hsort Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      destruct (app_eq_nil _ _ H_lVar_nil) as [H_lVar_nil_vt H_lVar_nil34].
      destruct Hinter as [Hinter_vt Hinter_34].
      simpl in Hinter_34.
      rewrite applySubToC_app in Hinter_34.
      assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
        now apply interpretC_app.
      destruct Hand as [Hinter3 Hinter4].
      rewrite (decompose_eq Hdecom).
      exists sigma; split; simpl; rewrite applySubToC_app.
      -- apply interpretC_app; split; try assumption.
         split; try assumption.
         now apply clos_rel_term_sym.
      -- rewrite listVarInC_app; simpl.
         destruct (app_eq_nil _ _ H_lVar_nil34) as [-> ->].
         rewrite app_nil_l.
         rewrite app_nil_r.
         now destruct (app_eq_nil _ _ H_lVar_nil_vt) as [-> ->].
    * intros ? ? ? ? ? ? ? ? _ [? [Hinter ?]].
      destruct Hinter as [HFalse HTrue].
      contradiction.
    * intros ? ? ? ? ? ? ? ? ? ? _ [? [Hinter ?]].
      destruct Hinter as [HFalse HTrue].
      contradiction.
    * intros v t c c3 c4 Hdecom HnOcc Hor _ Hsort Hsat.
      assert (HnInvt : ~ In v (listVarInT t)).
        intro HIn'.
        absurd (occurCheck v t); try assumption.
        now apply In_listVarInT_occurCheck.
      unfold P in Hsat; simpl in Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      rewrite (decompose_eq Hdecom).
      exists ((v, applySubstitution sigma t) :: sigma); split; simpl; rewrite applySubToC_app.
         ++ simpl in Hinter.
            rewrite applySubToC_cons in Hinter.
            rewrite applySubToC_app in Hinter.
            destruct Hinter as [? Hinter].
            assert (Hand : interpretC (applySubstitutionToC ((v, applySubstitution sigma t) :: sigma) c3) /\ interpretC (applySubstitutionToC ((v, applySubstitution sigma t) :: sigma) c4)).
              now apply interpretC_app.
            destruct Hand as [Hinter3 Hinter4].
            apply interpretC_app.
            split; try assumption.
            split; try assumption.
            simpl; case (eq_variable_dec v v) as [_ | Hneq]; try contradiction.
            rewrite (neq_listVarInT_applySub _ _ _ _ HnInvt).
            now apply clos_rel_term_refl.
         ++ simpl in H_lVar_nil.
            rewrite applySubToC_cons in H_lVar_nil.
            destruct (app_eq_nil _ _ H_lVar_nil) as [Hnilvt Hnil34].
            destruct (app_eq_nil _ _ Hnilvt) as [Hnilv Hnilt].
            assert (Heq : (applySubstitution sigma t) = (applySubstitution ((v, applySubstitution sigma t) :: sigma) (Var v))).
              now simpl; case (eq_variable_dec v v).
            rewrite applySubToC_app in Hnil34.
            rewrite listVarInC_app in Hnil34.
            rewrite listVarInC_app; simpl.
            destruct (app_eq_nil _ _ Hnil34) as [-> ->].
            rewrite app_nil_l.
            rewrite app_nil_r.
            case (eq_variable_dec v v) as [_ | Hneq]; try contradiction.
            rewrite <- applySub_cons.
            rewrite (neq_listVarInT_applySub _ _ _ _ HnInvt).
            rewrite applySubstitution_nil.
            now rewrite Hnilt.
    * intros v1 t1 t2 c v2 c3 c4 Hdecom ? ? ? ? ? Hsort Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [[Hinter [HinterSetTerm Hinter34]] H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil_v1_v2 Hnil_v2_34].
      rewrite (decompose_eq Hdecom).
      exists sigma; split; simpl; rewrite applySubToC_app.
      -- destruct (app_eq_nil _ _ Hnil_v1_v2) as [? ?].
         simpl in Hinter34.
         rewrite applySubToC_app in Hinter34.
         assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
           now apply interpretC_app.
         destruct Hand as [Hinter3 Hinter4].
         apply interpretC_app; split; try assumption.
         split; try assumption.
         apply t_trans with (y := applySubstitution sigma (listSetC (SetCToList t1 t2) (Var v2))); try assumption.
         apply t_trans with (y := applySubstitution sigma (listSetC (SetCToList t1 t2) (Var v1))).
         ++ apply t_trans with (y := applySubstitution sigma (listSetC (SetCToList t1 t2) (applySubstitution sigma (Var v1)))).
            ** apply t_trans with (y := applySubstitution sigma (listSetC (SetCToList t1 t2) (applySubstitution sigma (listSetC (SetCToList t1 t2) (Var v2))))).
               --- apply t_trans with (y := applySubstitution sigma (listSetC (SetCToList t1 t2) (listSetC (SetCToList t1 t2) (Var v2)))).
                   +++ apply applySub_clos_rel_term.
                       now apply clos_rel_term_listSetC_listSetC.
                   +++ apply applySub_listSetC_applySub.
                       now apply listVarInT_applySub_nil.
               --- apply applySub_listSetC_clos_rel_term.
                   now apply clos_rel_term_sym.
            ** apply clos_rel_term_sym.
               apply applySub_listSetC_applySub.
               now apply listVarInT_applySub_nil.
         ++ apply clos_rel_term_sym.
            now apply tail_applySub_listSetC_SetCToList.
      -- rewrite listVarInC_app; simpl.
         destruct (app_eq_nil _ _ Hnil_v2_34) as [Hnil_v2 Hnil_34].
         destruct (app_eq_nil _ _ Hnil_34) as [-> ->].
         rewrite app_nil_l.
         rewrite app_nil_r.
         destruct (app_eq_nil _ _ Hnil_v1_v2) as [-> Hnil].
         simpl in Hnil.
         rewrite app_nil_l.
         assert (Hnil_1 : listVarInT (applySubstitution sigma t1) = nil). 
           revert Hnil.
           elim (listElements t2).
           ++ simpl; intro Hnil.
              now destruct (app_eq_nil _ _ Hnil).
           ++ intros ? l _ Hnil.
              now destruct (app_eq_nil _ _ Hnil).
         ++ rewrite Hnil_1.
            rewrite app_nil_l.
            rewrite listVarInT_remove_list.
            ** apply remove_list_eq_nil.
               apply incl_tran with (m := listVarInT (listSetC (SetCToList t1 t2) (Var v1))).
               --- apply incl_tran with (m := listVarInT ({{t1 | t2}})); try now apply incl_appr.
                   apply listVarInT_clos_rel_term.
                   now apply tail_listSetC_SetCToList.
               --- apply listVar_applySub_incl.
                   rewrite applySub_listSetC.
                   apply incl_l_nil.
                   apply incl_tran with (m := listVarInListT (map (applySubstitution sigma) (SetCToList t1 t2)) ++ listVarInT (applySubstitution sigma (Var v1)));
                     try now apply listSetC_listVarInListT.
                   apply incl_app.
                   +++ apply incl_tran with (m := listVarInT (applySubstitution sigma (listSetC (SetCToList t1 t2) (Var v2))));
                         try now simpl; rewrite Hnil.
                       case (list_eq_dec eq_term_dec (SetCToList t1 t2) nil) as [-> | Hneq_nil]; try now trivial.
                       rewrite applySub_listSetC.
                       apply listVarInListT_listSetC.
                       intro Habs.
                       absurd ((SetCToList t1 t2) = nil); try assumption.
                       exact (map_eq_nil _ _ Habs).
                   +++ apply incl_tran with (m := listVarInT (applySubstitution sigma (listSetC (SetCToList t1 t2) (Var v2))));
                         try now apply listVarInT_clos_rel_term.
                       now simpl; rewrite Hnil.
            ** intros t HIn_t.
               assert (Hexists : exists p, snd p = t /\ In p sigma).
                 now apply in_map_iff.
               destruct Hexists as [p [<- HIn_p]].
               apply listVar_applySubToC_nil with (c := ((Var v1 == listSetC (SetCToList t1 t2) (Var v2)) :: IsSet (Var v2) :: nil) ++ c3 ++ c4)
                                                 (sigma := sigma); try assumption.
               --- simpl; rewrite applySubToC_app.
                   now rewrite listVarInC_app.
               --- apply HlVar_incl.
                   now apply in_map.
    * intros ? ? ? ? ? ? ? ? ? _ [? [Hinter ?]].
      destruct Hinter as [HFalse HTrue].
      contradiction.
    * intros s lt1 lt2 c c3 c4 Hdecom Hlength Hsort Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      rewrite (decompose_eq Hdecom).
      exists sigma; split; simpl; rewrite applySubToC_app.
      -- simpl in Hinter.
         rewrite applySubToC_app in Hinter.
         assert (Hand : interpretC (applySubstitutionToC sigma (map2 buildEq lt1 lt2)) /\ interpretC (applySubstitutionToC sigma (c3 ++ c4))).
           now apply interpretC_app.
         destruct Hand as [Hinterlt Hinter34].
         rewrite applySubToC_app in Hinter34.
         assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
           now apply interpretC_app.
         destruct Hand as [Hinter3 Hinter4].
         apply interpretC_app; split; try assumption.
         split; try assumption.
         now apply interpret_OTerm.
      -- simpl in H_lVar_nil.
         rewrite applySubToC_app in H_lVar_nil.
         rewrite listVarInC_app in H_lVar_nil.
         destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil_lt Hnil_34].
         rewrite applySubToC_app in Hnil_34.
         rewrite listVarInC_app in Hnil_34.
         rewrite listVarInC_app; simpl.
         destruct (app_eq_nil _ _ Hnil_34) as [-> ->].
         rewrite app_nil_l.
         rewrite app_nil_r.
         apply incl_l_nil.
         apply incl_tran with (m := listVarInC (applySubstitutionToC sigma (map2 buildEq lt1 lt2)));
           try now rewrite Hnil_lt.
         now apply listVarIn_OTerm with (s := s).
    * intros t1 t2 t3 t4 c c3 c4 Hdecom ? _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      rewrite (decompose_eq Hdecom).
      exists sigma; split; simpl; rewrite applySubToC_app.
      -- simpl in Hinter.
         destruct Hinter as [Hinter_t12 Hinter_tc34].
         destruct Hinter_tc34 as [Hinter_t34 Hinter_c34].
         rewrite applySubToC_app in Hinter_c34.
         assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
           now apply interpretC_app.
         destruct Hand as [Hinter_c3 Hinter_c4].
         apply interpretC_app; split; try assumption.
         split; try assumption.
         now simpl; apply SetC_rel_term.
      -- simpl in H_lVar_nil.
         destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil_t12 Hnil_tc34].
         destruct (app_eq_nil _ _ Hnil_tc34) as [Hnil_t34 Hnil_c34].
         rewrite applySubToC_app in Hnil_c34.
         rewrite listVarInC_app in Hnil_c34.
         rewrite listVarInC_app; simpl.
         destruct (app_eq_nil _ _ Hnil_c34) as [-> ->].
         destruct (app_eq_nil _ _ Hnil_t34) as [-> ->].
         now destruct (app_eq_nil _ _ Hnil_t12) as [-> ->].
    * intros t1 t2 t3 t4 c c3 c4 Hdecom Hcondition_Eq_9 _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      rewrite (decompose_eq Hdecom).
      exists sigma; split; simpl; rewrite applySubToC_app.
      -- simpl in Hinter.
         destruct Hinter as [Hinter_t12 Hinter_t134_c34].
         destruct Hinter_t134_c34 as [Hinter_t134 Hinter_c34].
         rewrite applySubToC_app in Hinter_c34.
         assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
           now apply interpretC_app.
         destruct Hand as [Hinter_c3 Hinter_c4].
         apply interpretC_app; split; try assumption.
         split; try assumption.
         simpl.
         apply t_trans with (y := ({{applySubstitution sigma t2 | ({{applySubstitution sigma t1 | applySubstitution sigma t3}})}}));
           try now apply SetC_rel_term_r.
         apply clos_rel_term_sym.
         apply axiom_Ab_clos_rel_term.
         now apply clos_rel_term_sym.
      -- simpl in H_lVar_nil.
         destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil_t12 Hnil_t134_c34].
         destruct (app_eq_nil _ _ Hnil_t134_c34) as [Hnil_t134 Hnil_c34].
         rewrite applySubToC_app in Hnil_c34.
         rewrite listVarInC_app in Hnil_c34.
         rewrite listVarInC_app; simpl.
         destruct (app_eq_nil _ _ Hnil_c34) as [-> ->].
         destruct (app_eq_nil _ _ Hnil_t12) as [-> ->].
         destruct (app_eq_nil _ _ Hnil_t134) as [Hnil_t13 ->].
         now destruct (app_eq_nil _ _ Hnil_t13) as [_ ->].
    * intros t1 t2 t3 t4 c c3 c4 Hdecom Hcondition_Eq_9 _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      rewrite (decompose_eq Hdecom).
      exists sigma; split; simpl; rewrite applySubToC_app.
      -- simpl in Hinter.
         destruct Hinter as [Hinter_t12 Hinter_t124_c34].
         destruct Hinter_t124_c34 as [Hinter_t124 Hinter_c34].
         rewrite applySubToC_app in Hinter_c34.
         assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
           now apply interpretC_app.
         destruct Hand as [Hinter_c3 Hinter_c4].
         apply interpretC_app; split; try assumption.
         split; try assumption.
         simpl.
         apply t_trans with (y := ({{applySubstitution sigma t1 | ({{applySubstitution sigma t2 | applySubstitution sigma t4}})}}));
           try now apply SetC_rel_term_r.
         now apply axiom_Ab_clos_rel_term.
      -- simpl in H_lVar_nil.
         destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil_t12 Hnil_t234_c34].
         destruct (app_eq_nil _ _ Hnil_t234_c34) as [Hnil_t234 Hnil_c34].
         rewrite applySubToC_app in Hnil_c34.
         rewrite listVarInC_app in Hnil_c34.
         rewrite listVarInC_app; simpl.
         destruct (app_eq_nil _ _ Hnil_c34) as [-> ->].
         destruct (app_eq_nil _ _ Hnil_t12) as [-> ->].
         destruct (app_eq_nil _ _ Hnil_t234) as [-> Hnil_t24].
         now destruct (app_eq_nil _ _ Hnil_t24) as [_ ->].
    * intros t1 t2 t3 t4 c v c3 c4 Hdecom ? ? ? ? _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      rewrite (decompose_eq Hdecom).
      exists sigma; split; simpl; rewrite applySubToC_app.
      -- simpl in Hinter.
         destruct Hinter as [Hinter_t23_v Hinter_t14_v_c34].
         destruct Hinter_t14_v_c34 as [Hinter_t14_v Hinter_v_c34].
         destruct Hinter_v_c34 as [Hinter_v Hinter_c34].
         rewrite applySubToC_app in Hinter_c34.
         assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
           now apply interpretC_app.
         destruct Hand as [Hinter_c3 Hinter_c4].
         apply interpretC_app; split; try assumption.
         split; try assumption.
         simpl.
         apply t_trans with (y := ({{applySubstitution sigma t1 | ({{applySubstitution sigma t2 | applySubstitution sigma (Var v)}})}}));
           try now apply SetC_rel_term_r.
         apply t_trans with (y := ({{applySubstitution sigma t2 | ({{applySubstitution sigma t1 | applySubstitution sigma (Var v)}})}}));
           try now apply SetC_rel_term_r.
         apply axiom_Cl.
      -- simpl in H_lVar_nil.
         destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil_t23_v Hnil_t14_v_c34].
         destruct (app_eq_nil _ _ Hnil_t14_v_c34) as [Hnil_t14_v Hnil_v_c34].
         destruct (app_eq_nil _ _ Hnil_v_c34) as [Hnil_v Hnil_c34].
         rewrite applySubToC_app in Hnil_c34.
         rewrite listVarInC_app in Hnil_c34.
         rewrite listVarInC_app; simpl.
         destruct (app_eq_nil _ _ Hnil_c34) as [-> ->].
         destruct (app_eq_nil _ _ Hnil_t14_v) as [Hnil_t1_v ->].
         destruct (app_eq_nil _ _ Hnil_t1_v) as [-> _].
         destruct (app_eq_nil _ _ Hnil_t23_v) as [-> Hnil_t2_v].
         now destruct (app_eq_nil _ _ Hnil_t2_v) as [-> _].
    * intros lt1 lt2 v c j t0 tj c3 c4 Hdecom Hnth_error_t0 Hnth_error_tj Hsort Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      revert Hsort.
      simpl; rewrite (decompose_eq Hdecom).
      intro Hsort.
      assert (Hneq_nil1 : map (applySubstitution sigma) lt1 <> nil).
        intro Habs.
        absurd (In t0 nil); try now apply in_nil.
          rewrite <- (map_eq_nil _ _ Habs).
          now apply nth_error_In with (n := 0).
      assert (Hneq_nil2 : map (applySubstitution sigma) lt2 <> nil).
        intro Habs.
        absurd (In tj nil); try now apply in_nil.
          rewrite <- (map_eq_nil _ _ Habs).
          now apply nth_error_In with (n := j).
      assert (HIn : In (IsSet (Var v)) (c3 ++ (listSetC lt1 (Var v) == listSetC lt2 (Var v)) :: c4)).
        assert (He : incl (set_inferPC (listSetC lt1 (Var v) == listSetC lt2 (Var v))) (c3 ++ (listSetC lt1 (Var v) == listSetC lt2 (Var v)) :: c4)).
          now apply (sort_complete_set_infer Hsort); apply in_elt.
        apply He.
        apply in_or_app; left.
        apply find_set_listSetC_Var.
        intro Habs.
        rewrite Habs in Hneq_nil1.
        contradiction.
      assert (HIsSet : In (IsSet (Var v)) (c3 ++ c4)).
        apply in_or_app.
        case (in_app_or _ _ _ HIn) as [? | HIn']; try now left.
        now case HIn' as [? | ?]; try right.
      exists sigma; split; simpl; rewrite applySubToC_app.
      -- simpl in Hinter.
         rewrite applySubToC_app in Hinter.
         rewrite interpretC_app in Hinter.
         destruct Hinter as [Hinter3 Hinter4_t].
         rewrite applySubToC_app in Hinter4_t.
         rewrite interpretC_app in Hinter4_t.
         destruct Hinter4_t as [Hinter4 [Hintert [Hinter _]]].
         apply interpretC_app; split; try assumption.
         split; try assumption.
         simpl; do 2 rewrite applySub_listSetC.
         assert (Hforall : (forall pc, In pc (applySubstitutionToC sigma (c3 ++ c4)) -> interpretPC pc)).
           apply interpretC_iff.
           rewrite applySubToC_app.
           rewrite interpretC_app.
           now split.
         assert (He : interpretPC (applySubstitutionToPC sigma (IsSet (Var v)))).
           apply Hforall.
           apply in_map_iff.
           exists (IsSet (Var v)).
           now split.
         destruct (setTerm_exists_listSetC _ He) as [lt Heq].
         simpl in Hinter.
         rewrite Heq.
         case (list_eq_dec eq_term_dec (map (applySubstitution sigma) (deleteElmntj 0 lt1)) nil) as [Hlt1_eq_nil | Hlt1_neq_nil].
         ++ case (list_eq_dec eq_term_dec (map (applySubstitution sigma) (deleteElmntj j lt2)) nil) as [Hlt2_eq_nil | Hlt2_neq_nil].
            ** assert (Hlt1_eq : lt1 = t0 :: nil).
                 apply (deleteElmntj_eq_nil _ _ Hnth_error_t0).
                 exact (map_eq_nil _ _ Hlt1_eq_nil).
               assert (Hlt2_eq : lt2 = tj :: nil).
                 apply (deleteElmntj_eq_nil _ _ Hnth_error_tj).
                 exact (map_eq_nil _ _ Hlt2_eq_nil).
               rewrite Hlt1_eq.
               rewrite Hlt2_eq.
               now apply SetC_rel_term_l.
            ** assert (Hlt2_neq_nil' : (deleteElmntj j lt2) <> nil).
                 intro Habs.
                 now rewrite Habs in Hlt2_neq_nil.
               rewrite (map_eq_nil (applySubstitution sigma) _ Hlt1_eq_nil) in Hinter.
               assert (Heqv : listSetC nil (Var v) = Var v).
                 trivial.
               rewrite Heqv in Hinter.
               rewrite applySub_listSetC in Hinter.
               rewrite Heq in Hinter.
               rewrite <- listSetC_app_EmptySet in Hinter; try assumption.
               assert (Hii : (incl_interpret lt (map (applySubstitution sigma) (deleteElmntj j lt2) ++ lt)) /\
                               (incl_interpret (map (applySubstitution sigma) (deleteElmntj j lt2) ++ lt) lt)).
                 split; apply clos_rel_term_listSetC_incl_interpret_EmptySet; try assumption.
                 now apply clos_rel_term_sym.
               destruct Hii as [Hi1 Hi2].
               rewrite <- listSetC_app_EmptySet; try assumption.
               rewrite <- listSetC_app_EmptySet; try assumption.
               apply incl_interpret_listSetC_clos_rel_term; intros t HIn_map.
               --- case (in_app_or _ _ _ HIn_map) as [HIn_map' | HIn_lt].
                   +++ assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt1).
                         now apply in_map_iff.
                       destruct Hexists as [t' [Heq' HIn']].
                       case (deleteElmntj_in_or _ _ _ Hnth_error_t0 HIn') as [Heq'' | HIn'']; try now rewrite (map_eq_nil _ _ Hlt1_eq_nil) in HIn''.
                       exists (applySubstitution sigma tj).
                       split; try now rewrite <- Heq'; rewrite Heq''; apply clos_rel_term_sym.
                       apply in_or_app; left.
                       apply in_map_iff; exists tj.
                       split; try reflexivity.
                       now apply nth_error_In with (n := j).
                   +++ assert (HInt : In t (map (applySubstitution sigma) (deleteElmntj 0 lt1) ++ lt)).
                         now apply in_or_app; right.
                       destruct (Hi1 _ HIn_lt) as [t'' [? HorIn]].
                       exists t''; split; try assumption.
                       apply in_or_app.
                       case (in_app_or _ _ _ HorIn) as [? | ?]; try now right.
                       now left; apply (incl_map (applySubstitution sigma) (deleteElmntj_incl j lt2)).
               --- case (in_app_or _ _ _ HIn_map) as [HIn_map' | HIn_lt].
                   +++ assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt2).
                         now apply in_map_iff.
                       destruct Hexists as [t' [Heq' HIn']].
                       case (deleteElmntj_in_or _ _ _ Hnth_error_tj HIn') as [Heq'' | HIn''].
                       *** exists (applySubstitution sigma t0).
                           split; try now rewrite <- Heq'; rewrite Heq''.
                           apply in_or_app; left.
                           apply in_map_iff; exists t0.
                           split; try reflexivity.
                           now apply nth_error_In with (n := 0).
                       *** assert (HInt : In t (map (applySubstitution sigma) (deleteElmntj j lt2) ++ lt)).
                             rewrite <- Heq'.
                             apply in_or_app; left.
                             apply in_map_iff; exists t'.
                             now split; [reflexivity | assumption].
                           destruct (Hi2 _ HInt) as [t'' [? HorIn]].
                           exists t''; split; try assumption.
                           apply in_or_app.
                           now right.
                   +++ assert (HInt : In t (map (applySubstitution sigma) (deleteElmntj j lt2) ++ lt)).
                         now apply in_or_app; right.
                       destruct (Hi2 _ HInt) as [t'' [? HorIn]].
                       exists t''; split; try assumption.
                       apply in_or_app.
                       now right.
         ++ case (list_eq_dec eq_term_dec (map (applySubstitution sigma) (deleteElmntj j lt2)) nil) as [Hlt2_eq_nil | Hlt2_neq_nil].
            ** assert (Hlt1_neq_nil' : (deleteElmntj 0 lt1) <> nil).
                 intro Habs.
                 now rewrite Habs in Hlt1_neq_nil.
               rewrite (map_eq_nil (applySubstitution sigma) _ Hlt2_eq_nil) in Hinter.
               assert (Heqv : listSetC nil (Var v) = Var v).
                 trivial.
               rewrite Heqv in Hinter.
               rewrite applySub_listSetC in Hinter.
               rewrite Heq in Hinter.
               rewrite <- listSetC_app_EmptySet in Hinter; try assumption.
               assert (Hii : (incl_interpret (map (applySubstitution sigma) (deleteElmntj 0 lt1) ++ lt) lt) /\
                               (incl_interpret lt (map (applySubstitution sigma) (deleteElmntj 0 lt1) ++ lt))).
                 split; apply clos_rel_term_listSetC_incl_interpret_EmptySet; try assumption.
                 now apply clos_rel_term_sym.
               destruct Hii as [Hi1 Hi2].
               rewrite <- listSetC_app_EmptySet; try assumption.
               rewrite <- listSetC_app_EmptySet; try assumption.
               apply incl_interpret_listSetC_clos_rel_term; intros t HIn_map.
               --- case (in_app_or _ _ _ HIn_map) as [HIn_map' | HIn_lt].
                   +++ assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt1).
                         now apply in_map_iff.
                       destruct Hexists as [t' [Heq' HIn']].
                       case (deleteElmntj_in_or _ _ _ Hnth_error_t0 HIn') as [Heq'' | HIn''].
                       *** exists (applySubstitution sigma tj).
                           split; try now rewrite <- Heq'; rewrite Heq''; apply clos_rel_term_sym.
                           apply in_or_app; left.
                           apply in_map_iff; exists tj.
                           split; try reflexivity.
                           now apply nth_error_In with (n := j).
                       *** assert (HInt : In t (map (applySubstitution sigma) (deleteElmntj 0 lt1) ++ lt)).
                             apply in_or_app; left.
                             rewrite <- Heq'.
                             now apply in_map.
                           destruct (Hi1 _ HInt) as [t'' [? HtIn]].
                           exists t''; split; try assumption.
                           now apply in_or_app; right.
                   +++ exists t.
                       split; try now apply clos_rel_term_refl.
                       now apply in_or_app; right.
               --- case (in_app_or _ _ _ HIn_map) as [HIn_map' | HIn_lt].
                   +++ assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt2).
                         now apply in_map_iff.
                       destruct Hexists as [t' [Heq' HIn']].
                       case (deleteElmntj_in_or _ _ _ Hnth_error_tj HIn') as [Heq'' | HIn'']; try now rewrite (map_eq_nil _ _ Hlt2_eq_nil) in HIn''.
                       exists (applySubstitution sigma t0).
                       split; try now rewrite <- Heq'; rewrite Heq''.
                       apply in_or_app; left.
                       apply in_map_iff; exists t0.
                       split; try reflexivity.
                       now apply nth_error_In with (n := 0).
                   +++ exists t.
                       split; try now apply clos_rel_term_refl.
                       now apply in_or_app; right.
            ** assert (Hlt1_neq_nil' : (deleteElmntj 0 lt1) <> nil).
                 intro Habs.
                 now rewrite Habs in Hlt1_neq_nil.
               assert (Hlt2_neq_nil' : (deleteElmntj j lt2) <> nil).
                 intro Habs.
                 now rewrite Habs in Hlt2_neq_nil.
               do 2 rewrite applySub_listSetC in Hinter.
               rewrite Heq in Hinter.
               do 2 rewrite <- listSetC_app_EmptySet in Hinter; try assumption.
               assert (Hii : (incl_interpret (map (applySubstitution sigma) (deleteElmntj 0 lt1) ++ lt) (map (applySubstitution sigma) (deleteElmntj j lt2) ++ lt)) /\
                               (incl_interpret (map (applySubstitution sigma) (deleteElmntj j lt2) ++ lt) (map (applySubstitution sigma) (deleteElmntj 0 lt1) ++ lt))).
                 split; apply clos_rel_term_listSetC_incl_interpret_EmptySet; try assumption.
                 now apply clos_rel_term_sym.
               destruct Hii as [Hi1 Hi2].
               rewrite <- listSetC_app_EmptySet; try assumption.
               rewrite <- listSetC_app_EmptySet; try assumption.
               apply incl_interpret_listSetC_clos_rel_term; intros t HIn_map.
               --- case (in_app_or _ _ _ HIn_map) as [HIn_map' | HIn_lt].
                   +++ assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt1).
                         now apply in_map_iff.
                       destruct Hexists as [t' [Heq' HIn']].
                       case (deleteElmntj_in_or _ _ _ Hnth_error_t0 HIn') as [Heq'' | HIn''].
                       *** exists (applySubstitution sigma tj).
                           split; try now rewrite <- Heq'; rewrite Heq''; apply clos_rel_term_sym.
                           apply in_or_app; left.
                           apply in_map_iff; exists tj.
                           split; try reflexivity.
                           now apply nth_error_In with (n := j).
                       *** assert (HInt: In t (map (applySubstitution sigma) (deleteElmntj 0 lt1) ++ lt)).
                             rewrite <- Heq'.
                             apply in_or_app; left.
                             apply in_map_iff; exists t'.
                             now split; [reflexivity | assumption].
                           destruct (Hi1 _ HInt) as [t'' [? HorIn]].
                           exists t''; split; try assumption.
                           apply in_or_app.
                           case (in_app_or _ _ _ HorIn) as [? | ?]; try now right.
                           now left; apply (incl_map (applySubstitution sigma) (deleteElmntj_incl j lt2)).
                   +++ assert (HInt : In t (map (applySubstitution sigma) (deleteElmntj 0 lt1) ++ lt)).
                         now apply in_or_app; right.
                       destruct (Hi1 _ HInt) as [t'' [? HorIn]].
                       exists t''; split; try assumption.
                       apply in_or_app.
                       case (in_app_or _ _ _ HorIn) as [? | ?]; try now right.
                       now left; apply (incl_map (applySubstitution sigma) (deleteElmntj_incl j lt2)).
               --- case (in_app_or _ _ _ HIn_map) as [HIn_map' | HIn_lt].
                   +++ assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt2).
                         now apply in_map_iff.
                       destruct Hexists as [t' [Heq' HIn']].
                       case (deleteElmntj_in_or _ _ _ Hnth_error_tj HIn') as [Heq'' | HIn''].
                       *** exists (applySubstitution sigma t0).
                           split; try now rewrite <- Heq'; rewrite Heq''.
                           apply in_or_app; left.
                           apply in_map_iff; exists t0.
                           split; try reflexivity.
                           now apply nth_error_In with (n := 0).
                       *** assert (HInt : In t (map (applySubstitution sigma) (deleteElmntj j lt2) ++ lt)).
                             rewrite <- Heq'.
                             apply in_or_app; left.
                             apply in_map_iff; exists t'.
                             now split; [reflexivity | assumption].
                           destruct (Hi2 _ HInt) as [t'' [? HorIn]].
                           exists t''; split; try assumption.
                           apply in_or_app.
                           case (in_app_or _ _ _ HorIn) as [? | ?]; try now right.
                           now left; apply (incl_map (applySubstitution sigma) (deleteElmntj_incl 0 lt1)).
                   +++ assert (HInt : In t (map (applySubstitution sigma) (deleteElmntj j lt2) ++ lt)).
                         now apply in_or_app; right.
                       destruct (Hi2 _ HInt) as [t'' [? HorIn]].
                       exists t''; split; try assumption.
                       apply in_or_app.
                       case (in_app_or _ _ _ HorIn) as [? | ?]; try now right.
                       now left; apply (incl_map (applySubstitution sigma) (deleteElmntj_incl 0 lt1)).
      -- rewrite listVarInC_app; simpl.
         simpl in H_lVar_nil.
         do 2 rewrite applySubToC_app in H_lVar_nil.
         do 2 rewrite listVarInC_app in H_lVar_nil.
         destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil_c3 Hnil4_0j].
         rewrite Hnil_c3.
         rewrite app_nil_l.
         destruct (app_eq_nil _ _ Hnil4_0j) as [Hnil_c4 Hnil0j_lt].
         rewrite Hnil_c4.
         rewrite app_nil_r.
         assert (Hnil_var : listVarInPC (applySubstitutionToPC sigma (IsSet (Var v))) = nil).
           apply listVarInPC_listVarInC_nil with (c := applySubstitutionToC sigma (c3 ++ c4));
             try now rewrite applySubToC_app; rewrite listVarInC_app; rewrite Hnil_c3; rewrite Hnil_c4.
           apply in_map_iff.
           exists (IsSet (Var v)).
           now split.
         destruct (app_eq_nil _ _ Hnil0j_lt) as [Hnil_0j Hnil_lt].
         destruct (app_eq_nil _ _ Hnil_0j) as [Hnil0 Hnilj].
         destruct (app_eq_nil _ _ Hnil_lt) as [Hnil_lt12 _].
         destruct (app_eq_nil _ _ Hnil_lt12) as [Hnil_lt1 Hnil_lt2].
         enough (He : listVarInT (applySubstitution sigma (listSetC lt1 (Var v))) = nil
                      /\ listVarInT (applySubstitution sigma (listSetC lt2 (Var v))) = nil).
           now destruct He as [-> ->].
         split; rewrite applySub_listSetC; apply listVarIn_listSetC_nil; try assumption.
         ++ case (list_eq_dec eq_term_dec (map (applySubstitution sigma) (deleteElmntj 0 lt1)) nil) as [Hlt1_eq_nil | Hlt1_neq_nil]; split; try assumption.
            ** assert (Hlt1_eq : lt1 = t0 :: nil).
                 apply (deleteElmntj_eq_nil _ _ Hnth_error_t0).
                 exact (map_eq_nil _ _ Hlt1_eq_nil).
               rewrite Hlt1_eq.
               intros t HInt.
               now case HInt as [<- | ?]; [assumption | contradiction].
            ** intros t HInt.
               assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt1).
                 now apply in_map_iff.
               destruct Hexists as [t' [<- HIn']].
               case (deleteElmntj_in_or _ _ _ Hnth_error_t0 HIn') as [-> | HIn'']; try assumption.
               assert (Hlt1_neq_nil' : (deleteElmntj 0 lt1) <> nil).
                 intro Habs.
                 now rewrite Habs in Hlt1_neq_nil.
               rewrite applySub_listSetC in Hnil_lt1.
               assert (Hnil1 : (forall  t, In t (map (applySubstitution sigma) (deleteElmntj 0 lt1)) -> listVarInT t = nil)
                               /\ (listVarInT (applySubstitution sigma (Var v)) = nil)).
                 now apply listVarIn_listSetC_nil.
               destruct Hnil1 as [Hforall _].
               apply Hforall.
               apply in_map_iff; exists t'.
               now split.
         ++ case (list_eq_dec eq_term_dec (map (applySubstitution sigma) (deleteElmntj j lt2)) nil) as [Hlt2_eq_nil | Hlt2_neq_nil]; split; try assumption.
            ** assert (Hlt2_eq : lt2 = tj :: nil).
                 apply (deleteElmntj_eq_nil _ _ Hnth_error_tj).
                 exact (map_eq_nil _ _ Hlt2_eq_nil).
               rewrite Hlt2_eq.
               intros t HInt.
               now case HInt as [<- | ?]; [assumption | contradiction].
            ** intros t HInt.
               assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt2).
                 now apply in_map_iff.
               destruct Hexists as [t' [<- HIn']].
               case (deleteElmntj_in_or _ _ _ Hnth_error_tj HIn') as [-> | HIn'']; try assumption.
               assert (Hlt2_neq_nil' : (deleteElmntj j lt2) <> nil).
                 intro Habs.
                 now rewrite Habs in Hlt2_neq_nil.
               rewrite applySub_listSetC in Hnil_lt2.
               assert (Hnil2 : (forall  t, In t (map (applySubstitution sigma) (deleteElmntj j lt2)) -> listVarInT t = nil)
                                /\ (listVarInT (applySubstitution sigma (Var v)) = nil)).
                 now apply listVarIn_listSetC_nil.
               destruct Hnil2 as [Hforall _].
               apply Hforall.
               apply in_map_iff; exists t'.
               now split.
    * intros lt1 lt2 v c j t0 tj c3 c4 Hdecom Hnth_error_t0 Hnth_error_tj Hsort Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      revert Hsort.
      simpl; rewrite (decompose_eq Hdecom).
      intro Hsort.
      assert (Hneq_nil1 : map (applySubstitution sigma) lt1 <> nil).
        intro Habs.
        absurd (In t0 nil); try now apply in_nil.
          rewrite <- (map_eq_nil _ _ Habs).
          now apply nth_error_In with (n := 0).
      assert (Hneq_nil2 : map (applySubstitution sigma) lt2 <> nil).
        intro Habs.
        absurd (In tj nil); try now apply in_nil.
          rewrite <- (map_eq_nil _ _ Habs).
          now apply nth_error_In with (n := j).
      assert (HIn : In (IsSet (Var v)) (c3 ++ (listSetC lt1 (Var v) == listSetC lt2 (Var v)) :: c4)).
        assert (He : incl (set_inferPC (listSetC lt1 (Var v) == listSetC lt2 (Var v))) (c3 ++ (listSetC lt1 (Var v) == listSetC lt2 (Var v)) :: c4)).
          now apply (sort_complete_set_infer Hsort); apply in_elt.
        apply He.
        apply in_or_app; left.
        apply find_set_listSetC_Var.
        intro Habs.
        rewrite Habs in Hneq_nil1.
        contradiction.
      assert (HIsSet : In (IsSet (Var v)) (c3 ++ c4)).
        apply in_or_app.
        case (in_app_or _ _ _ HIn) as [? | HIn']; try now left.
        now case HIn' as [? | ?]; try right.
      simpl in Hinter.
      rewrite applySubToC_app in Hinter.
      rewrite interpretC_app in Hinter.
      destruct Hinter as [Hinter3 Hinter].
      rewrite applySubToC_app in Hinter.
      rewrite interpretC_app in Hinter.
      destruct Hinter as [Hinter4 [Hinter0j [Hinter _]]].
      assert (Hforall : (forall pc, In pc (applySubstitutionToC sigma (c3 ++ c4)) -> interpretPC pc)).
        apply interpretC_iff.
        rewrite applySubToC_app.
        rewrite interpretC_app.
        now split.
      assert (He : interpretPC (applySubstitutionToPC sigma (IsSet (Var v)))).
        apply Hforall.
        apply in_map_iff.
        exists (IsSet (Var v)).
        now split.
      destruct (setTerm_exists_listSetC _ He) as [lt Heq].
      simpl in Hinter.
      case (list_eq_dec eq_term_dec (map (applySubstitution sigma) (deleteElmntj j lt2)) nil) as [Hlt2_eq_nil | Hlt2_neq_nil].
      -- exists sigma; split; simpl; rewrite applySubToC_app.
         ++ apply interpretC_app; split; try assumption.
            split; try assumption.
            rewrite (map_eq_nil (applySubstitution sigma) _ Hlt2_eq_nil) in Hinter.
            assert (Heqt : listSetC nil (Var v) = Var v).
              trivial.
            rewrite Heqt in Hinter.
            rewrite applySub_listSetC in Hinter.
            rewrite Heq in Hinter.
            simpl; do 2 rewrite applySub_listSetC.
            rewrite Heq.
            rewrite <- listSetC_app_EmptySet in Hinter; try assumption.
            assert (Hii : (incl_interpret (map (applySubstitution sigma) lt1 ++ lt) lt)
                             /\ (incl_interpret lt (map (applySubstitution sigma) lt1 ++ lt))).
              split; apply clos_rel_term_listSetC_incl_interpret_EmptySet; try assumption.
              now apply clos_rel_term_sym.
            destruct Hii as [Hi1 Hi2].
            rewrite <- listSetC_app_EmptySet; try assumption.
            rewrite <- listSetC_app_EmptySet; try assumption.
            apply incl_interpret_listSetC_clos_rel_term; intros t HIn_map.
            ** destruct (Hi1 _ HIn_map) as [t' [? HorIn]].
               exists t'; split; try assumption.
               now apply in_or_app; right.
            ** case (in_app_or _ _ _ HIn_map) as [HIn_map' | HIn_lt].
               --- assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt2).
                     now apply in_map_iff.
                   destruct Hexists as [t' [Heq' HIn']].
                   case (deleteElmntj_in_or _ _ _ Hnth_error_tj HIn') as [Heq'' | HIn'']; try now rewrite (map_eq_nil (applySubstitution sigma) _ Hlt2_eq_nil) in HIn''.
                   exists (applySubstitution sigma t0); split; try now rewrite <- Heq'; rewrite Heq''.
                   apply in_or_app; left.
                   apply in_map_iff; exists t0.
                   split; try reflexivity.
                   now apply nth_error_In with (n := 0).
               --- exists t.
                   split; try now apply clos_rel_term_refl.
                   now apply in_or_app; right.
         ++ rewrite listVarInC_app; simpl.
            simpl in H_lVar_nil.
            do 2 rewrite applySubToC_app in H_lVar_nil.
            do 2 rewrite listVarInC_app in H_lVar_nil.
            destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil_c3 Hnil].
            rewrite Hnil_c3.
            rewrite app_nil_l.
            destruct (app_eq_nil _ _ Hnil) as [Hnil_c4 Hnilt].
            rewrite Hnil_c4.
            rewrite app_nil_r.
            assert (Hnil_var : listVarInPC (applySubstitutionToPC sigma (IsSet (Var v))) = nil).
              apply listVarInPC_listVarInC_nil with (c := applySubstitutionToC sigma (c3 ++ c4));
              try now rewrite applySubToC_app; rewrite listVarInC_app; rewrite Hnil_c3; rewrite Hnil_c4.
              apply in_map_iff.
              exists (IsSet (Var v)).
              now split.
            destruct (app_eq_nil _ _ Hnilt) as [Hnil_0j Hnil_lt].
            destruct (app_eq_nil _ _ Hnil_0j) as [Hnil_0 Hnil_j].
            destruct (app_eq_nil _ _ Hnil_lt) as [Hnil_lt12 _].
            destruct (app_eq_nil _ _ Hnil_lt12) as [Hnil_lt1 Hnil_lt2].
            rewrite applySub_listSetC in Hnil_lt1.
            enough (H : listVarInT (applySubstitution sigma (listSetC lt1 (Var v))) = nil
                        /\ listVarInT (applySubstitution sigma (listSetC lt2 (Var v))) = nil).
              now destruct H as [-> ->].
            do 2 rewrite applySub_listSetC.
            split; apply listVarIn_listSetC_nil; try assumption.
            ** split; try assumption.
               intros t HInt.
               assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt1).
                 now apply in_map_iff.
               destruct Hexists as [t' [<- HIn']].
               case (deleteElmntj_in_or _ _ _ Hnth_error_t0 HIn') as [-> | HIn'']; try assumption.
               assert (Hnil1 : (forall  t, In t (map (applySubstitution sigma) lt1) -> listVarInT t = nil)
                                        /\ (listVarInT (applySubstitution sigma (Var v)) = nil)).
                 now apply listVarIn_listSetC_nil.
               destruct Hnil1 as [Hforall' _].
               apply Hforall'.
               apply in_map_iff; exists t'.
               now split.
            ** split; try assumption.
               intros t HInt.
               assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt2).
                 now apply in_map_iff.
               destruct Hexists as [t' [<- HIn']].
               case (deleteElmntj_in_or _ _ _ Hnth_error_tj HIn') as [-> | HIn'']; try assumption.
               now rewrite (map_eq_nil (applySubstitution sigma) _ Hlt2_eq_nil) in HIn''.
      -- assert (Hlt2_neq_nil' : (deleteElmntj j lt2) <> nil).
           intro Habs.
           now rewrite Habs in Hlt2_neq_nil.
         exists sigma; split; simpl; rewrite applySubToC_app.
         ++ apply interpretC_app; split; try assumption.
            split; try assumption.
            do 2 rewrite applySub_listSetC in Hinter.
            rewrite Heq in Hinter.
            simpl; do 2 rewrite applySub_listSetC.
            rewrite Heq.
            do 2 rewrite <- listSetC_app_EmptySet in Hinter; try assumption.
            assert (Hii : (incl_interpret (map (applySubstitution sigma) lt1 ++ lt) (map (applySubstitution sigma) (deleteElmntj j lt2) ++ lt))
                             /\ (incl_interpret (map (applySubstitution sigma) (deleteElmntj j lt2) ++ lt) (map (applySubstitution sigma) lt1 ++ lt))).
              split; apply clos_rel_term_listSetC_incl_interpret_EmptySet; try assumption.
              now apply clos_rel_term_sym.
            destruct Hii as [Hi1 Hi2].
            rewrite <- listSetC_app_EmptySet; try assumption.
            rewrite <- listSetC_app_EmptySet; try assumption.
            apply incl_interpret_listSetC_clos_rel_term; intros t HIn_map.
            ** destruct (Hi1 _ HIn_map) as [t' [? HorIn]].
               exists t'; split; try assumption.
               case (in_app_or _ _ _ HorIn) as [? | ?]; try now apply in_or_app; right.
               apply in_or_app; left.
               assert (Hexists : exists t'', applySubstitution sigma t'' = t' /\ In t'' (deleteElmntj j lt2)).
                 now apply in_map_iff.
               destruct Hexists as [t'' [? ?]].
               apply in_map_iff; exists t''.
               split; try assumption.
               now apply deleteElmntj_incl with (j := j).
            ** case (in_app_or _ _ _ HIn_map) as [HIn_map' | HIn_lt].
               --- assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt2).
                     now apply in_map_iff.
                   destruct Hexists as [t' [Heq' HIn']].
                   case (deleteElmntj_in_or _ _ _ Hnth_error_tj HIn') as [Heq'' | HIn''].
                   +++ exists (applySubstitution sigma t0); split; try now rewrite <- Heq'; rewrite Heq''.
                       apply in_or_app; left.
                       apply in_map_iff; exists t0.
                       split; try reflexivity.
                       now apply nth_error_In with (n := 0).
                   +++ assert (HInt : In t (map (applySubstitution sigma) (deleteElmntj j lt2) ++ lt)).
                         rewrite <- Heq'.
                         apply in_or_app; left.
                         apply in_map_iff; exists t'.
                         now split; [reflexivity | assumption].
                       destruct (Hi2 _ HInt) as [t'' [? ?]].
                       now exists t''; split.
               --- assert (HInt : In t (map (applySubstitution sigma) (deleteElmntj j lt2) ++ lt)).
                     now apply in_or_app; right.
                   destruct (Hi2 _ HInt) as [t'' [? ?]].
                   now exists t''; split.
         ++ rewrite listVarInC_app; simpl.
            simpl in H_lVar_nil.
            do 2 rewrite applySubToC_app in H_lVar_nil.
            do 2 rewrite listVarInC_app in H_lVar_nil.
            destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil_c3 Hnil].
            rewrite Hnil_c3.
            rewrite app_nil_l.
            destruct (app_eq_nil _ _ Hnil) as [Hnil_c4 Hnilt].
            rewrite Hnil_c4.
            rewrite app_nil_r.
            assert (Hnil_var : listVarInPC (applySubstitutionToPC sigma (IsSet (Var v))) = nil).
              apply listVarInPC_listVarInC_nil with (c := applySubstitutionToC sigma (c3 ++ c4));
              try now rewrite applySubToC_app; rewrite listVarInC_app; rewrite Hnil_c3; rewrite Hnil_c4.
              apply in_map_iff.
              exists (IsSet (Var v)).
              now split.
            destruct (app_eq_nil _ _ Hnilt) as [Hnil_0j Hnil_lt].
            destruct (app_eq_nil _ _ Hnil_0j) as [Hnil_0 Hnil_j].
            destruct (app_eq_nil _ _ Hnil_lt) as [Hnil_lt12 _].
            destruct (app_eq_nil _ _ Hnil_lt12) as [Hnil_lt1 Hnil_lt2].
            rewrite applySub_listSetC in Hnil_lt1.
            rewrite applySub_listSetC in Hnil_lt2.
            enough (H : listVarInT (applySubstitution sigma (listSetC lt1 (Var v))) = nil
                        /\ listVarInT (applySubstitution sigma (listSetC lt2 (Var v))) = nil).
              now destruct H as [-> ->].
            do 2 rewrite applySub_listSetC.
            split; apply listVarIn_listSetC_nil; try assumption.
            ** split; try assumption.
               intros t HInt.
               assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt1).
                 now apply in_map_iff.
               destruct Hexists as [t' [<- HIn']].
               case (deleteElmntj_in_or _ _ _ Hnth_error_t0 HIn') as [-> | HIn'']; try assumption.
               assert (Hnil1 : (forall  t, In t (map (applySubstitution sigma) lt1) -> listVarInT t = nil)
                                        /\ (listVarInT (applySubstitution sigma (Var v)) = nil)).
                 now apply listVarIn_listSetC_nil.
               destruct Hnil1 as [Hforall' _].
               apply Hforall'.
               apply in_map_iff; exists t'.
               now split.
            ** split; try assumption.
               intros t HInt.
               assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt2).
                 now apply in_map_iff.
               destruct Hexists as [t' [<- HIn']].
               case (deleteElmntj_in_or _ _ _ Hnth_error_tj HIn') as [-> | HIn'']; try assumption.
               assert (Hnil2 : (forall  t, In t (map (applySubstitution sigma) (deleteElmntj j lt2)) -> listVarInT t = nil)
                                        /\ (listVarInT (applySubstitution sigma (Var v)) = nil)).
                 now apply listVarIn_listSetC_nil.
               destruct Hnil2 as [Hforall' _].
               apply Hforall'.
               apply in_map_iff; exists t'.
               now split.
    * intros lt1 lt2 v c j t0 tj c3 c4 Hdecom Hnth_error_t0 Hnth_error_tj Hsort Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      revert Hsort.
      simpl; rewrite (decompose_eq Hdecom).
      intro Hsort.
      assert (Hneq_nil1 : map (applySubstitution sigma) lt1 <> nil).
        intro Habs.
        absurd (In t0 nil); try now apply in_nil.
          rewrite <- (map_eq_nil _ _ Habs).
          now apply nth_error_In with (n := 0).
      assert (Hneq_nil2 : map (applySubstitution sigma) lt2 <> nil).
        intro Habs.
        absurd (In tj nil); try now apply in_nil.
          rewrite <- (map_eq_nil _ _ Habs).
          now apply nth_error_In with (n := j).
      assert (HIn : In (IsSet (Var v)) (c3 ++ (listSetC lt1 (Var v) == listSetC lt2 (Var v)) :: c4)).
        assert (He : incl (set_inferPC (listSetC lt1 (Var v) == listSetC lt2 (Var v))) (c3 ++ (listSetC lt1 (Var v) == listSetC lt2 (Var v)) :: c4)).
          now apply (sort_complete_set_infer Hsort); apply in_elt.
        apply He.
        apply in_or_app; left.
        apply find_set_listSetC_Var.
        intro Habs.
        rewrite Habs in Hneq_nil1.
        contradiction.
      assert (HIsSet : In (IsSet (Var v)) (c3 ++ c4)).
        apply in_or_app.
        case (in_app_or _ _ _ HIn) as [? | HIn']; try now left.
        now case HIn' as [? | ?]; try right.
      simpl in Hinter.
      rewrite applySubToC_app in Hinter.
      rewrite interpretC_app in Hinter.
      destruct Hinter as [Hinter3 Hinter].
      rewrite applySubToC_app in Hinter.
      rewrite interpretC_app in Hinter.
      destruct Hinter as [Hinter4 [Hinter0j [Hinter _]]].
      assert (Hforall : (forall pc, In pc (applySubstitutionToC sigma (c3 ++ c4)) -> interpretPC pc)).
        apply interpretC_iff.
        rewrite applySubToC_app.
        rewrite interpretC_app.
        now split.
      assert (He : interpretPC (applySubstitutionToPC sigma (IsSet (Var v)))).
        apply Hforall.
        apply in_map_iff.
        exists (IsSet (Var v)).
        now split.
      destruct (setTerm_exists_listSetC _ He) as [lt Heq].
      simpl in Hinter.
      case (list_eq_dec eq_term_dec (map (applySubstitution sigma) (deleteElmntj 0 lt1)) nil) as [Hlt1_eq_nil | Hlt1_neq_nil].
      -- exists sigma; split; simpl; rewrite applySubToC_app.
         ++ apply interpretC_app; split; try assumption.
            split; try assumption.
            rewrite (map_eq_nil (applySubstitution sigma) _ Hlt1_eq_nil) in Hinter.
            assert (Heqt : listSetC nil (Var v) = Var v).
              trivial.
            rewrite Heqt in Hinter.
            rewrite applySub_listSetC in Hinter.
            rewrite Heq in Hinter.
            simpl; do 2 rewrite applySub_listSetC.
            rewrite Heq.
            rewrite <- listSetC_app_EmptySet in Hinter; try assumption.
            assert (Hii : (incl_interpret lt (map (applySubstitution sigma) lt2 ++ lt))
                             /\ (incl_interpret (map (applySubstitution sigma) lt2 ++ lt) lt)).
              split; apply clos_rel_term_listSetC_incl_interpret_EmptySet; try assumption.
              now apply clos_rel_term_sym.
            destruct Hii as [Hi1 Hi2].
            rewrite <- listSetC_app_EmptySet; try assumption.
            rewrite <- listSetC_app_EmptySet; try assumption.
            apply incl_interpret_listSetC_clos_rel_term; intros t HIn_map.
            ** case (in_app_or _ _ _ HIn_map) as [HIn_map' | HIn_lt].
               --- assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt1).
                     now apply in_map_iff.
                   destruct Hexists as [t' [Heq' HIn']].
                   case (deleteElmntj_in_or _ _ _ Hnth_error_t0 HIn') as [Heq'' | HIn'']; try now rewrite (map_eq_nil (applySubstitution sigma) _ Hlt1_eq_nil) in HIn''.
                   exists (applySubstitution sigma tj); split; try now rewrite <- Heq'; rewrite Heq''; apply clos_rel_term_sym.
                   apply in_or_app; left.
                   apply in_map_iff; exists tj.
                   split; try reflexivity.
                   now apply nth_error_In with (n := j).
               --- exists t.
                   split; try now apply clos_rel_term_refl.
                   now apply in_or_app; right.
            ** destruct (Hi2 _ HIn_map) as [t' [? HorIn]].
               exists t'; split; try assumption.
               now apply in_or_app; right.
         ++ rewrite listVarInC_app; simpl.
            simpl in H_lVar_nil.
            do 2 rewrite applySubToC_app in H_lVar_nil.
            do 2 rewrite listVarInC_app in H_lVar_nil.
            destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil_c3 Hnil].
            rewrite Hnil_c3.
            rewrite app_nil_l.
            destruct (app_eq_nil _ _ Hnil) as [Hnil_c4 Hnilt].
            rewrite Hnil_c4.
            rewrite app_nil_r.
            assert (Hnil_var : listVarInPC (applySubstitutionToPC sigma (IsSet (Var v))) = nil).
              apply listVarInPC_listVarInC_nil with (c := applySubstitutionToC sigma (c3 ++ c4));
              try now rewrite applySubToC_app; rewrite listVarInC_app; rewrite Hnil_c3; rewrite Hnil_c4.
              apply in_map_iff.
              exists (IsSet (Var v)).
              now split.
            destruct (app_eq_nil _ _ Hnilt) as [Hnil_0j Hnil_lt].
            destruct (app_eq_nil _ _ Hnil_0j) as [Hnil_0 Hnil_j].
            destruct (app_eq_nil _ _ Hnil_lt) as [Hnil_lt12 _].
            destruct (app_eq_nil _ _ Hnil_lt12) as [Hnil_lt1 Hnil_lt2].
            rewrite applySub_listSetC in Hnil_lt2.
            enough (H : listVarInT (applySubstitution sigma (listSetC lt1 (Var v))) = nil
                        /\ listVarInT (applySubstitution sigma (listSetC lt2 (Var v))) = nil).
              now destruct H as [-> ->].
            do 2 rewrite applySub_listSetC.
            split; apply listVarIn_listSetC_nil; try assumption.
            ** split; try assumption.
               intros t HInt.
               assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt1).
                 now apply in_map_iff.
               destruct Hexists as [t' [<- HIn']].
               case (deleteElmntj_in_or _ _ _ Hnth_error_t0 HIn') as [-> | HIn'']; try assumption.
               now rewrite (map_eq_nil (applySubstitution sigma) _ Hlt1_eq_nil) in HIn''.
            ** split; try assumption.
               intros t HInt.
               assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt2).
                 now apply in_map_iff.
               destruct Hexists as [t' [<- HIn']].
               case (deleteElmntj_in_or _ _ _ Hnth_error_tj HIn') as [-> | HIn'']; try assumption.
               assert (Hnil2 : (forall  t, In t (map (applySubstitution sigma) lt2) -> listVarInT t = nil)
                                        /\ (listVarInT (applySubstitution sigma (Var v)) = nil)).
                 now apply listVarIn_listSetC_nil.
               destruct Hnil2 as [Hforall' _].
               apply Hforall'.
               apply in_map_iff; exists t'.
               now split.
      -- assert (Hlt1_neq_nil' : (deleteElmntj 0 lt1) <> nil).
           intro Habs.
           now rewrite Habs in Hlt1_neq_nil.
         exists sigma; split; simpl; rewrite applySubToC_app.
         ++ apply interpretC_app; split; try assumption.
            split; try assumption.
            do 2 rewrite applySub_listSetC in Hinter.
            rewrite Heq in Hinter.
            simpl; do 2 rewrite applySub_listSetC.
            rewrite Heq.
            do 2 rewrite <- listSetC_app_EmptySet in Hinter; try assumption.
            assert (Hii : (incl_interpret (map (applySubstitution sigma) (deleteElmntj 0 lt1) ++ lt) (map (applySubstitution sigma) lt2 ++ lt))
                             /\ (incl_interpret (map (applySubstitution sigma) lt2 ++ lt) (map (applySubstitution sigma) (deleteElmntj 0 lt1) ++ lt))).
              split; apply clos_rel_term_listSetC_incl_interpret_EmptySet; try assumption.
              now apply clos_rel_term_sym.
            destruct Hii as [Hi1 Hi2].
            rewrite <- listSetC_app_EmptySet; try assumption.
            rewrite <- listSetC_app_EmptySet; try assumption.
            apply incl_interpret_listSetC_clos_rel_term; intros t HIn_map.
            ** case (in_app_or _ _ _ HIn_map) as [HIn_map' | HIn_lt].
               --- assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt1).
                     now apply in_map_iff.
                   destruct Hexists as [t' [Heq' HIn']].
                   case (deleteElmntj_in_or _ _ _ Hnth_error_t0 HIn') as [Heq'' | HIn''].
                   +++ exists (applySubstitution sigma tj); split; try now rewrite <- Heq'; rewrite Heq''; apply clos_rel_term_sym.
                       apply in_or_app; left.
                       apply in_map_iff; exists tj.
                       split; try reflexivity.
                       now apply nth_error_In with (n := j).
                   +++ assert (HInt : In t (map (applySubstitution sigma) (deleteElmntj 0 lt1) ++ lt)).
                         rewrite <- Heq'.
                         apply in_or_app; left.
                         apply in_map_iff; exists t'.
                         now split; [reflexivity | assumption].
                       destruct (Hi1 _ HInt) as [t'' [? ?]].
                       now exists t''; split.
               --- assert (HInt : In t (map (applySubstitution sigma) (deleteElmntj 0 lt1) ++ lt)).
                     now apply in_or_app; right.
                   destruct (Hi1 _ HInt) as [t'' [? ?]].
                   now exists t''; split.
            ** destruct (Hi2 _ HIn_map) as [t' [? HorIn]].
               exists t'; split; try assumption.
               case (in_app_or _ _ _ HorIn) as [? | ?]; try now apply in_or_app; right.
               apply in_or_app; left.
               assert (Hexists : exists t'', applySubstitution sigma t'' = t' /\ In t'' (deleteElmntj 0 lt1)).
                 now apply in_map_iff.
               destruct Hexists as [t'' [? ?]].
               apply in_map_iff; exists t''.
               split; try assumption.
               now apply deleteElmntj_incl with (j := 0).
         ++ rewrite listVarInC_app; simpl.
            simpl in H_lVar_nil.
            do 2 rewrite applySubToC_app in H_lVar_nil.
            do 2 rewrite listVarInC_app in H_lVar_nil.
            destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil_c3 Hnil].
            rewrite Hnil_c3.
            rewrite app_nil_l.
            destruct (app_eq_nil _ _ Hnil) as [Hnil_c4 Hnilt].
            rewrite Hnil_c4.
            rewrite app_nil_r.
            assert (Hnil_var : listVarInPC (applySubstitutionToPC sigma (IsSet (Var v))) = nil).
              apply listVarInPC_listVarInC_nil with (c := applySubstitutionToC sigma (c3 ++ c4));
              try now rewrite applySubToC_app; rewrite listVarInC_app; rewrite Hnil_c3; rewrite Hnil_c4.
              apply in_map_iff.
              exists (IsSet (Var v)).
              now split.
            destruct (app_eq_nil _ _ Hnilt) as [Hnil_0j Hnil_lt].
            destruct (app_eq_nil _ _ Hnil_0j) as [Hnil_0 Hnil_j].
            destruct (app_eq_nil _ _ Hnil_lt) as [Hnil_lt12 _].
            destruct (app_eq_nil _ _ Hnil_lt12) as [Hnil_lt1 Hnil_lt2].
            rewrite applySub_listSetC in Hnil_lt1.
            rewrite applySub_listSetC in Hnil_lt2.
            enough (H : listVarInT (applySubstitution sigma (listSetC lt1 (Var v))) = nil
                        /\ listVarInT (applySubstitution sigma (listSetC lt2 (Var v))) = nil).
              now destruct H as [-> ->].
            do 2 rewrite applySub_listSetC.
            split; apply listVarIn_listSetC_nil; try assumption.
            ** split; try assumption.
               intros t HInt.
               assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt1).
                 now apply in_map_iff.
               destruct Hexists as [t' [<- HIn']].
               case (deleteElmntj_in_or _ _ _ Hnth_error_t0 HIn') as [-> | HIn'']; try assumption.
               assert (Hnil1 : (forall  t, In t (map (applySubstitution sigma) (deleteElmntj 0 lt1)) -> listVarInT t = nil)
                                        /\ (listVarInT (applySubstitution sigma (Var v)) = nil)).
                 now apply listVarIn_listSetC_nil.
               destruct Hnil1 as [Hforall' _].
               apply Hforall'.
               apply in_map_iff; exists t'.
               now split.
            ** split; try assumption.
               intros t HInt.
               assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt2).
                 now apply in_map_iff.
               destruct Hexists as [t' [<- HIn']].
               case (deleteElmntj_in_or _ _ _ Hnth_error_tj HIn') as [-> | HIn'']; try assumption.
               assert (Hnil2 : (forall  t, In t (map (applySubstitution sigma) lt2) -> listVarInT t = nil)
                                        /\ (listVarInT (applySubstitution sigma (Var v)) = nil)).
                 now apply listVarIn_listSetC_nil.
               destruct Hnil2 as [Hforall' _].
               apply Hforall'.
               apply in_map_iff; exists t'.
               now split.
    * intros lt1 lt2 v c j t0 tj w c3 c4 Hdecom Hnth_error_t0 Hnth_error_tj ? ? ? ? _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      rewrite (decompose_eq Hdecom).
      assert (Hneq_nil1 : map (applySubstitution sigma) lt1 <> nil).
        intro Habs.
        absurd (In t0 nil); try now apply in_nil.
          rewrite <- (map_eq_nil _ _ Habs).
          now apply nth_error_In with (n := 0).
      assert (Hneq_nil2 : map (applySubstitution sigma) lt2 <> nil).
        intro Habs.
        absurd (In tj nil); try now apply in_nil.
          rewrite <- (map_eq_nil _ _ Habs).
          now apply nth_error_In with (n := j).
      simpl in Hinter.
      case (list_eq_dec eq_term_dec (map (applySubstitution sigma) (deleteElmntj 0 lt1)) nil) as [Hlt1_eq_nil | Hlt1_neq_nil].
      -- do 2 rewrite applySubToC_app in Hinter.
         do 2 rewrite interpretC_app in Hinter.
         destruct Hinter as [Hinter_c3 [Hinter_c4 Hinter]].
         destruct Hinter as [Hinter_vw [Hinter_lt Hinter_w]].
         destruct Hinter_w as [HsetTerm_w _].
         rewrite (map_eq_nil (applySubstitution sigma) _ Hlt1_eq_nil) in Hinter_lt.
         exists sigma; split; simpl; rewrite applySubToC_app.
         ++ apply interpretC_app; split; try assumption.
            split; try assumption.
            simpl; do 2 rewrite applySub_listSetC.
            assert (HsetTerm_v : setTerm (applySubstitution sigma (Var v))).
              apply clos_rel_term_setTerm with (t1 := applySubstitution sigma ({{t0 | Var w}})); try assumption.
              now apply clos_rel_term_sym.
            destruct (setTerm_exists_listSetC _ HsetTerm_v) as [lt_v Heq_v].
            destruct (setTerm_exists_listSetC _ HsetTerm_w) as [lt_w Heq_w].
            assert (Hinter_vw' : listSetC lt_v EmptySet ===  listSetC ((applySubstitution sigma t0) :: lt_w) EmptySet).
              simpl in Hinter_vw.
              simpl in Heq_w.
              rewrite Heq_w in Hinter_vw.
              rewrite <- Heq_v.
              revert Hinter_vw.
              now elim lt_w.
            assert (Hinter_vw'' : listSetC (applySubstitution sigma t0 :: lt_w) EmptySet === listSetC lt_v EmptySet).
              now apply clos_rel_term_sym.
            simpl in Hinter_lt; rewrite applySub_listSetC in Hinter_lt.
            rewrite Heq_w in Hinter_lt.
            simpl in Heq_w; rewrite Heq_w in Hinter_lt.
            rewrite <- listSetC_app_EmptySet in Hinter_lt; try assumption.
            assert (Hii : (incl_interpret lt_w (map (applySubstitution sigma) lt2 ++ lt_w))
                           /\ (incl_interpret (map (applySubstitution sigma) lt2 ++ lt_w) lt_w)).
              split; apply clos_rel_term_listSetC_incl_interpret_EmptySet; try assumption.
              now apply clos_rel_term_sym.
            destruct Hii as [Hi1 Hi2].
            rewrite Heq_v.
            case (list_eq_dec eq_term_dec lt_v nil) as [Hlt_v_eq_nil | Hlt_v_neq_nil].
            ** rewrite Hlt_v_eq_nil in Hinter_vw''.
               absurd (listSetC (applySubstitution sigma t0 :: lt_w) EmptySet = EmptySet); try now apply listSetC_neq.
               now apply clos_rel_term_EmptySet.
            ** rewrite <- listSetC_app; try assumption.
               rewrite <- listSetC_app; try assumption.
               apply incl_interpret_listSetC_clos_rel_term; intros t HIn_map.
               --- case (in_app_or _ _ _ HIn_map) as [HIn_map' | HIn_lt_v].
                   +++ assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt1).
                         now apply in_map_iff.
                       destruct Hexists as [t' [Heq' HIn]].
                       case (deleteElmntj_in_or _ _ _ Hnth_error_t0 HIn) as [Heq'' | HIn']; try now rewrite (map_eq_nil (applySubstitution sigma) _ Hlt1_eq_nil) in HIn'.
                       assert (HIn' : In t (applySubstitution sigma t0 :: lt_w)).
                         now left; rewrite <- Heq''.
                       destruct ((clos_rel_term_listSetC_incl_interpret_EmptySet _ _ Hinter_vw'') _ HIn') as [t'' [? ?]].
                       exists t''.
                       split; try assumption.
                       now apply in_or_app; right.
                   +++ exists t.
                       split; try now apply clos_rel_term_refl.
                       now apply in_or_app; right.
               --- case (in_app_or _ _ _ HIn_map) as [HIn_map' | HIn_lt_v].
                   +++ assert (HIn : In t (map (applySubstitution sigma) lt2 ++ lt_w)).
                         now apply in_or_app; left.
                       destruct (Hi2 _ HIn) as [t' [? HorIn]].
                       assert (HIn' : In t' (applySubstitution sigma t0 :: lt_w)).
                         now apply in_cons.
                       destruct ((clos_rel_term_listSetC_incl_interpret_EmptySet _ _ Hinter_vw'') _ HIn') as [t'' [? ?]].
                       exists t''.
                       split; try now apply in_or_app; right.
                       now apply t_trans with (y := t').
                   +++ exists t.
                       split; try now apply clos_rel_term_refl.
                       now apply in_or_app; right.
         ++ rewrite listVarInC_app; simpl.
            simpl in H_lVar_nil.
            do 2 rewrite applySubToC_app in H_lVar_nil.
            do 2 rewrite listVarInC_app in H_lVar_nil.
            destruct (app_eq_nil _ _ H_lVar_nil) as [-> Hnil].
            rewrite app_nil_l.
            destruct (app_eq_nil _ _ Hnil) as [-> Hnilx34].
            rewrite app_nil_r.
            destruct (app_eq_nil _ _ Hnilx34) as [Hnilvw Hnil34].
            destruct (app_eq_nil _ _ Hnil34) as [Hnil' Hnil''].
            destruct (app_eq_nil _ _ Hnil'') as [Hnilw _].
            destruct (app_eq_nil _ _ Hnil') as [Hnil0lt1 Hnillt2].
            destruct (app_eq_nil _ _ Hnilvw) as [Hnilv Hnil0w].
            rewrite (map_eq_nil (applySubstitution sigma) _ Hlt1_eq_nil) in Hnil0lt1.
            rewrite applySub_listSetC in Hnillt2.
            assert (Hnil_lt2 : listVarInListT (map (applySubstitution sigma) lt2) = nil).
              apply incl_l_nil.
              apply incl_tran with (m := listVarInListT (map (applySubstitution sigma) lt2) ++ listVarInT (applySubstitution sigma (Var w)));
                try now apply incl_appl.
              simpl in Hnilw.
              apply incl_app; simpl; try now rewrite Hnilw.
              apply incl_tran with (m := listVarInT (listSetC (map (applySubstitution sigma) lt2) (applySubstitution sigma (Var w))));
                try now rewrite Hnillt2.
              now apply listVarInListT_listSetC.
            assert (Hnil_v : listVarInT (applySubstitution sigma (Var v)) = nil).
              now destruct (app_eq_nil _ _ Hnilvw).
            enough (He : listVarInT (applySubstitution sigma (listSetC lt1 (Var v))) = nil
                         /\ listVarInT (applySubstitution sigma (listSetC lt2 (Var v))) = nil).
              now destruct He as [-> ->].
            split; apply incl_l_nil; rewrite applySub_listSetC.
            ** apply incl_tran with (m := listVarInListT (map (applySubstitution sigma) lt1) ++ listVarInT (applySubstitution sigma (Var v))); try now apply listSetC_listVarInListT.
               apply incl_app; try now rewrite Hnil_v.
               assert (Hlt1_eq : lt1 = t0 :: nil).
                 apply (deleteElmntj_eq_nil _ _ Hnth_error_t0).
                 exact (map_eq_nil _ _ Hlt1_eq_nil).
               rewrite Hlt1_eq. 
               simpl in Hnil0w.
               now simpl; destruct (app_eq_nil _ _ Hnil0w) as [-> _].
            ** apply incl_tran with (m := listVarInListT (map (applySubstitution sigma) lt2) ++ listVarInT (applySubstitution sigma (Var v))); try now apply listSetC_listVarInListT.
               now apply incl_app; [rewrite Hnil_lt2 | rewrite Hnil_v].
      -- assert (Hlt1_neq_nil' : (deleteElmntj 0 lt1) <> nil).
           intro Habs.
           now rewrite Habs in Hlt1_neq_nil.
         do 2 rewrite applySubToC_app in Hinter.
         do 2 rewrite interpretC_app in Hinter.
         destruct Hinter as [Hinter_c3 [Hinter_c4 Hinter]].
         destruct Hinter as [Hinter_vw [Hinter_lt Hinter_w]].
         destruct Hinter_w as [HsetTerm_w _].
         exists sigma; split; simpl; rewrite applySubToC_app.
         ++ apply interpretC_app; split; try assumption.
            split; try assumption.
            simpl; do 2 rewrite applySub_listSetC.
            assert (HsetTerm_v : setTerm (applySubstitution sigma (Var v))).
              apply clos_rel_term_setTerm with (t1 := applySubstitution sigma ({{t0 | Var w}})); try assumption.
              now apply clos_rel_term_sym.
            destruct (setTerm_exists_listSetC _ HsetTerm_v) as [lt_v Heq_v].
            destruct (setTerm_exists_listSetC _ HsetTerm_w) as [lt_w Heq_w].
            assert (Hinter_vw' : listSetC lt_v EmptySet ===  listSetC ((applySubstitution sigma t0) :: lt_w) EmptySet).
              simpl in Hinter_vw.
              simpl in Heq_w.
              rewrite Heq_w in Hinter_vw.
              rewrite <- Heq_v.
              revert Hinter_vw.
              now elim lt_w.
            assert (Hinter_vw'' : listSetC (applySubstitution sigma t0 :: lt_w) EmptySet === listSetC lt_v EmptySet).
              now apply clos_rel_term_sym.
            simpl in Hinter_lt.
            do 2 rewrite applySub_listSetC in Hinter_lt.
            rewrite Heq_w in Hinter_lt.
            do 2 rewrite <- listSetC_app_EmptySet in Hinter_lt; try assumption.
            assert (Hii : (incl_interpret (map (applySubstitution sigma) (deleteElmntj 0 lt1) ++ lt_w) (map (applySubstitution sigma) lt2 ++ lt_w))
                           /\ (incl_interpret (map (applySubstitution sigma) lt2 ++ lt_w) (map (applySubstitution sigma) (deleteElmntj 0 lt1) ++ lt_w))).
              split; apply clos_rel_term_listSetC_incl_interpret_EmptySet; try assumption.
              now apply clos_rel_term_sym.
            destruct Hii as [Hi1 Hi2].
            rewrite Heq_v.
            case (list_eq_dec eq_term_dec lt_v nil) as [Hlt_v_eq_nil | Hlt_v_neq_nil].
            ** rewrite Hlt_v_eq_nil in Hinter_vw''.
               absurd (listSetC (applySubstitution sigma t0 :: lt_w) EmptySet = EmptySet); try now apply listSetC_neq.
               now apply clos_rel_term_EmptySet.
            ** rewrite <- listSetC_app; try assumption.
               rewrite <- listSetC_app; try assumption.
               apply incl_interpret_listSetC_clos_rel_term; intros t HIn_map.
               --- case (in_app_or _ _ _ HIn_map) as [HIn_map' | HIn_lt_v].
                   +++ assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt1).
                         now apply in_map_iff.
                       destruct Hexists as [t' [Heq' HIn]].
                       case (deleteElmntj_in_or _ _ _ Hnth_error_t0 HIn) as [Heq'' | HIn'].
                       *** assert (HIn' : In t (applySubstitution sigma t0 :: lt_w)).
                             now left; rewrite <- Heq''.
                           destruct ((clos_rel_term_listSetC_incl_interpret_EmptySet _ _ Hinter_vw'') _ HIn') as [t'' [? ?]].
                           exists t''.
                           split; try assumption.
                           now apply in_or_app; right.
                       *** assert (HIn'' : In t (map (applySubstitution sigma) (deleteElmntj 0 lt1) ++ lt_w)).
                             rewrite <- Heq'.
                             apply in_or_app; left.
                             apply in_map_iff; exists t'.
                             now split; [reflexivity | assumption].
                           destruct (Hi1 _ HIn'') as [t'' [? HorIn]].
                           case (in_app_or _ _ _ HorIn) as [? | ?].
                           ---- exists t''.
                                split; try assumption.
                                now apply in_or_app; left.
                           ---- assert (HIn''' : In t'' (applySubstitution sigma t0 :: lt_w)).
                                  now apply in_cons.
                                destruct ((clos_rel_term_listSetC_incl_interpret_EmptySet _ _ Hinter_vw'') _ HIn''') as [t''' [? ?]].
                                exists t'''.
                                split; try now apply in_or_app; right.
                                now apply t_trans with (y := t'').
                   +++ exists t.
                       split; try now apply clos_rel_term_refl.
                       now apply in_or_app; right.
                --- case (in_app_or _ _ _ HIn_map) as [HIn_map' | HIn_lt_v].
                    +++ assert (HIn : In t (map (applySubstitution sigma) lt2 ++ lt_w)).
                          now apply in_or_app; left.
                        destruct (Hi2 _ HIn) as [t' [? HorIn]].
                        case (in_app_or _ _ _ HorIn) as [HIn_map'' | HIn_lt_v].
                        *** exists t'.
                            split; try assumption.
                            apply in_or_app; left.
                            assert (Hexists : exists t'', applySubstitution sigma t'' = t' /\ In t'' (deleteElmntj 0 lt1)).
                              now apply in_map_iff.
                            destruct Hexists as [t'' [? ?]].
                            apply in_map_iff; exists t''.
                            split; try assumption.
                            now apply deleteElmntj_incl with (j := 0).
                        *** assert (HIn' : In t' (applySubstitution sigma t0 :: lt_w)).
                              now apply in_cons.
                            destruct ((clos_rel_term_listSetC_incl_interpret_EmptySet _ _ Hinter_vw'') _ HIn') as [t'' [? ?]].
                            exists t''.
                            split; try now apply in_or_app; right.
                            now apply t_trans with (y := t').
                    +++ exists t.
                        split; try now apply clos_rel_term_refl.
                        now apply in_or_app; right.
         ++ rewrite listVarInC_app; simpl.
            simpl in H_lVar_nil.
            do 2 rewrite applySubToC_app in H_lVar_nil.
            do 2 rewrite listVarInC_app in H_lVar_nil.
            destruct (app_eq_nil _ _ H_lVar_nil) as [-> Hnil].
            rewrite app_nil_l.
            destruct (app_eq_nil _ _ Hnil) as [-> Hnilx34].
            rewrite app_nil_r.
            destruct (app_eq_nil _ _ Hnilx34) as [Hnilvw Hnil34].
            destruct (app_eq_nil _ _ Hnil34) as [Hnil' Hnil''].
            destruct (app_eq_nil _ _ Hnil'') as [Hnilw _].
            destruct (app_eq_nil _ _ Hnil') as [Hnil0lt1 Hnillt2].
            destruct (app_eq_nil _ _ Hnilvw) as [Hnilv Hnil0w].
            rewrite applySub_listSetC in Hnil0lt1.
            rewrite applySub_listSetC in Hnillt2.
            assert (Hnil_0lt1 : forall t, In t (map (applySubstitution sigma) (deleteElmntj 0 lt1)) -> listVarInT t = nil).
              apply listVarInListT_eq_nil.
              apply incl_l_nil.
              apply incl_tran with (m := listVarInListT (map (applySubstitution sigma) (deleteElmntj 0 lt1)) ++ listVarInT (applySubstitution sigma (Var w)));
                try now apply incl_appl.
              simpl in Hnilw.
              apply incl_app; simpl; try now rewrite Hnilw.
              apply incl_tran with (m := listVarInT (listSetC (map (applySubstitution sigma) (deleteElmntj 0 lt1)) (applySubstitution sigma (Var w))));
                try now rewrite Hnil0lt1.
              now apply listVarInListT_listSetC.
            assert (Hnil_lt1 : listVarInListT (map (applySubstitution sigma) lt1) = nil).
              apply listVarInListT_eq_nil.
              intros t HIn.
              assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' lt1).
                now apply in_map_iff.
              destruct Hexists as [t' [<- HIn']].
              case (deleteElmntj_in_or _ _ _ Hnth_error_t0 HIn') as [-> | HIn'']; try now destruct (app_eq_nil _ _ Hnil0w).
              apply Hnil_0lt1.
              apply in_map_iff.
              now exists t'; split.
            assert (Hnil_lt2 : listVarInListT (map (applySubstitution sigma) lt2) = nil).
              apply incl_l_nil.
              apply incl_tran with (m := listVarInListT (map (applySubstitution sigma) lt2) ++ listVarInT (applySubstitution sigma (Var w)));
                try now apply incl_appl.
              simpl in Hnilw.
              apply incl_app; simpl; try now rewrite Hnilw.
              apply incl_tran with (m := listVarInT (listSetC (map (applySubstitution sigma) lt2) (applySubstitution sigma (Var w))));
                try now rewrite Hnillt2.
              now apply listVarInListT_listSetC.
            assert (Hnil_v : listVarInT (applySubstitution sigma (Var v)) = nil).
              now destruct (app_eq_nil _ _ Hnilvw).
            enough (He : listVarInT (applySubstitution sigma (listSetC lt1 (Var v))) = nil
                         /\ listVarInT (applySubstitution sigma (listSetC lt2 (Var v))) = nil).
              now destruct He as [-> ->].
            split; apply incl_l_nil; rewrite applySub_listSetC.
            ** apply incl_tran with (m := listVarInListT (map (applySubstitution sigma) lt1) ++ listVarInT (applySubstitution sigma (Var v))); try now apply listSetC_listVarInListT.
               now apply incl_app; [rewrite Hnil_lt1 | rewrite Hnil_v].
            ** apply incl_tran with (m := listVarInListT (map (applySubstitution sigma) lt2) ++ listVarInT (applySubstitution sigma (Var v))); try now apply listSetC_listVarInListT.
               now apply incl_app; [rewrite Hnil_lt2 | rewrite Hnil_v].
    * intros ? ? ? ? ? ? ? ? _ [? [Hinter ?]].
      destruct Hinter as [HFalse HTrue].
      contradiction.
  + intro HstepMem.
    case HstepMem.
    * intros ? ? ? ? ? _ [? [Hinter ?]].
      destruct Hinter as [HFalse HTrue].
      contradiction.
    * intros r s t c c3 c4 Hdecom Hsort Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      destruct (app_eq_nil _ _ H_lVar_nil) as [H1 H2].
      destruct (app_eq_nil _ _ H1) as [Hnilr Hnils].
      destruct (app_eq_nil _ _ H2) as [Hnil3 Hnil4].
      simpl in Hinter.
      rewrite applySubToC_app in Hinter.
      rewrite interpretC_app in Hinter.
      destruct Hinter as [Hinter_rs [Hinter3 Hinter4]].
      set (l := remove_list eq_variable_dec (listVarInC ((r == s) :: c3 ++ c4)) (listVarInT t)).
      set (EmptySet_fun := fun (v : log_variable) => (v, EmptySet)).
      set (sigma' := sigma ++ (map EmptySet_fun l)).
      assert (Hincl : incl ((listVarInC c3) ++ (listVarInC c4)) (map fst sigma)).
        now apply incl_app; apply listVar_applySubToC_incl.
      destruct (incl_app_inv _ _ Hincl) as [Hincl3 Hincl4].
      assert (Heq3: (applySubstitutionToC sigma' c3) = (applySubstitutionToC sigma c3)).
        unfold sigma'; now rewrite app_applySubToC.
      assert (Heq4: (applySubstitutionToC sigma' c4) = (applySubstitutionToC sigma c4)).
        unfold sigma'; now rewrite app_applySubToC.
      assert (Hinclrs : incl ((listVarInC ((r == s) :: nil))) (map fst sigma)).
        apply listVar_applySubToC_incl.
        simpl; rewrite Hnilr.
        now rewrite Hnils.
      assert (Heqrs: (applySubstitutionToC sigma' ((r == s) :: nil)) = (applySubstitutionToC sigma ((r == s) :: nil))).
        unfold sigma'; now rewrite app_applySubToC.
      inversion Heqrs.
      revert Hsort.
      simpl; rewrite (decompose_eq Hdecom).
      intro Hsort.
      exists sigma'.
      split.
      -- simpl; rewrite applySubToC_app.
         apply interpretC_app; split; try now rewrite Heq3.
         split; try now rewrite Heq4.
         split.
         ++ case (dec_setTerm ({{s | t}})) as [HsetTerm | HnsetTerm].
            ** destruct (setTerm_exists_listSetC _ HsetTerm) as [lt ->].
               rewrite applySub_listSetC.
               case (list_eq_dec eq_term_dec (map (applySubstitution sigma') lt) nil) as [-> | Hneq]; try now trivial.
               now rewrite setTerm_listSetC.
            ** assert (Hforall : forall pc, In pc (applySubstitutionToC sigma' (c3 ++ c4)) -> interpretPC pc).
                 apply interpretC_iff.
                 rewrite applySubToC_app.
                 rewrite interpretC_app.
                 now split; [rewrite Heq3 | rewrite Heq4].
               destruct (find_set_SetC_exist s t) as [t' [? Heq]]; try now trivial.
               enough (He : interpretPC (applySubstitutionToPC sigma' (IsSet ({{s | t}})))).
                 trivial.
               rewrite (Heq sigma').
               apply Hforall.
               apply in_map_iff.
               exists (IsSet t'); split; try trivial.
               enough (HIn: In (IsSet t') (c3 ++ (r :s ({{s | t}})) :: c4)).
                 case (in_app_or _ _ _ HIn) as [? | Hor]; try now apply in_or_app; left.
                 case Hor as [? | ?]; try now apply in_or_app; right.
               assert (He : incl (set_inferPC (r :s ({{s | t}}))) (c3 ++ (r :s ({{s | t}})) :: c4)).
                 now apply (sort_complete_set_infer Hsort); apply in_elt.
               apply He.
               now apply in_or_app; right.
         ++ exists (applySubstitution sigma' s).
            split.
            ** rewrite H0.
               rewrite H3.
               now apply clos_rel_term_sym.
            ** now left.
      -- simpl; rewrite applySubToC_app.
         rewrite listVarInC_app.
         rewrite Heq3.
         rewrite Hnil3.
         rewrite app_nil_l.
         simpl; rewrite Heq4.
         rewrite Hnil4.
         rewrite app_nil_r.
         rewrite H0.
         rewrite Hnilr.
         rewrite H3.
         rewrite Hnils.
         do 2 rewrite app_nil_l.
         rewrite listVarInT_remove_list_r.
         ++ apply remove_list_eq_nil.
            unfold sigma'.
            rewrite map_app.
            intros v HInv.
            case (in_dec eq_variable_dec v (listVarInC ((r == s) :: c3 ++ c4))) as [HIn' | HnIn].
            ** apply in_or_app; left.
               simpl in HIn'; rewrite listVarInC_app in HIn'.
               case (in_app_or _ _ _ HIn') as [HIn2 | HIn3].
               --- apply Hinclrs.
                   apply in_or_app.
                   now left.
               --- now case (in_app_or _ _ _ HIn3) as [? | ?];
                     [apply (listVar_applySubToC_incl sigma _ Hnil3) | apply (listVar_applySubToC_incl sigma _ Hnil4)].
            ** apply in_or_app; right.
               apply in_map_iff.
               exists (v, EmptySet).
               split; try reflexivity.
               assert (Heq : (v, EmptySet) = EmptySet_fun v).
                 trivial.
               rewrite Heq.
               apply in_map.
               apply in_remove_list.
               now split.
         ++ intros [v t'] HIn' HIn''.
            unfold sigma' in HIn'.
            case (in_app_or _ _ _ HIn') as [? | ?].
            ** apply (listVar_applySubToC_nil ((r == s) :: c3 ++ c4) sigma); try assumption.
               --- simpl; rewrite applySubToC_app.
                   rewrite listVarInC_app.
                   rewrite Hnil3.
                   rewrite Hnil4.
                   now rewrite app_nil_r.
               --- simpl in HlVar_incl.
                   apply HlVar_incl.
                   now apply in_map.
            ** assert (Hexists : exists v', EmptySet_fun v' = (v, t') /\ In v' l).
                 now apply in_map_iff.
               now destruct Hexists as [v' [<- ?]].
    * intros r s t c c3 c4 Hdecom _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      destruct (app_eq_nil _ _ H_lVar_nil) as [H1 H2].
      destruct (app_eq_nil _ _ H1) as [Hnilr Hnilt].
      destruct (app_eq_nil _ _ H2) as [Hnil3 Hnil4].
      simpl in Hinter.
      rewrite applySubToC_app in Hinter.
      rewrite interpretC_app in Hinter.
      destruct Hinter as [[HsetT [t' [Ht' HInt']]] [Hinter3 Hinter4]].
      set (l := remove_list eq_variable_dec (listVarInC ((r :s t) :: c3 ++ c4)) (listVarInT s)).
      set (EmptySet_fun := fun (v : log_variable) => (v, EmptySet)).
      set (sigma' := sigma ++ (map EmptySet_fun l)).
      assert (Hincl : incl ((listVarInC c3) ++ (listVarInC c4)) (map fst sigma)).
        now apply incl_app; apply listVar_applySubToC_incl.
      destruct (incl_app_inv _ _ Hincl) as [Hincl3 Hincl4].
      assert (Heq3: (applySubstitutionToC sigma' c3) = (applySubstitutionToC sigma c3)).
        unfold sigma'; now rewrite app_applySubToC.
      assert (Heq4: (applySubstitutionToC sigma' c4) = (applySubstitutionToC sigma c4)).
        unfold sigma'; now rewrite app_applySubToC.
      assert (Hinclrt : incl ((listVarInC ((r :s t) :: nil))) (map fst sigma)).
        apply listVar_applySubToC_incl.
        simpl; rewrite Hnilr.
        now rewrite Hnilt.
      assert (Heqrs: (applySubstitutionToC sigma' ((r :s t) :: nil)) = (applySubstitutionToC sigma ((r :s t) :: nil))).
        unfold sigma'; now rewrite app_applySubToC.
      inversion Heqrs.
      rewrite (decompose_eq Hdecom).
      exists sigma'.
      split.
      -- simpl; rewrite applySubToC_app.
         apply interpretC_app; split; try now rewrite Heq3.
         split; try now rewrite Heq4.
         split.
         ++ simpl; now rewrite H3.
         ++ exists t'.
            split; try now rewrite H0.
            right; now rewrite H3.
      -- simpl; rewrite applySubToC_app.
         rewrite listVarInC_app.
         rewrite Heq3.
         rewrite Hnil3.
         rewrite app_nil_l.
         simpl; rewrite Heq4.
         rewrite Hnil4.
         rewrite app_nil_r.
         rewrite H0.
         rewrite Hnilr.
         rewrite H3.
         rewrite Hnilt.
         rewrite app_nil_l.
         rewrite app_nil_r.
         rewrite listVarInT_remove_list_r.
         ++ apply remove_list_eq_nil.
            unfold sigma'.
            rewrite map_app.
            intros v HIn.
            case (in_dec eq_variable_dec v (listVarInC ((r :s t) :: c3 ++ c4))) as [HIn' | HnIn].
            ** apply in_or_app; left.
               simpl in HIn'; rewrite listVarInC_app in HIn'.
               case (in_app_or _ _ _ HIn') as [HIn2 | HIn3].
               --- apply Hinclrt.
                   apply in_or_app.
                   now left.
               --- now case (in_app_or _ _ _ HIn3) as [? | ?];
                     [apply (listVar_applySubToC_incl sigma _ Hnil3) | apply (listVar_applySubToC_incl sigma _ Hnil4)].
            ** apply in_or_app; right.
               apply in_map_iff.
               exists (v, EmptySet).
               split; try reflexivity.
               assert (Heq : (v, EmptySet) = EmptySet_fun v); trivial.
               rewrite Heq.
               apply in_map.
               apply in_remove_list.
               now split.
         ++ intros [v t''] HIn HIn'.
            unfold sigma' in HIn.
            case (in_app_or _ _ _ HIn) as [HIn'' | HIn''].
            ** apply (listVar_applySubToC_nil ((r :s t) :: c3 ++ c4) sigma); try assumption.
               --- simpl; rewrite applySubToC_app.
                   rewrite listVarInC_app.
                   rewrite Hnil3.
                   rewrite Hnil4.
                   now rewrite app_nil_r.
               --- simpl in HlVar_incl.
                   apply HlVar_incl.
                   now apply in_map.
            ** assert (Hexists : exists v', EmptySet_fun v' = (v, t'') /\ In v' l).
                 now apply in_map_iff.
               now destruct Hexists as [v' [<- ?]].
    * intros t v1 v2 c c3 c4 ? ? Hneq Hdecom _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      rewrite (decompose_eq Hdecom).
      exists sigma; split; simpl; rewrite applySubToC_app.
      -- simpl in Hinter.
         rewrite applySubToC_app in Hinter.
         assert (Hand : interpretC (applySubstitutionToC sigma (c3 ++ c4)) /\ interpretC (applySubstitutionToC sigma ((Var v1 == ({{t | Var v2}})) :: IsSet (Var v2) :: nil))).
           now apply interpretC_app.
         destruct Hand as [Hinter34 Hintertv12].
         rewrite applySubToC_app in Hinter34.
         assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
           now apply interpretC_app.
         destruct Hand as [Hinter3 Hintert4].
         apply interpretC_app; split; try assumption.
         split; try assumption.
         destruct Hintertv12 as [Hinterv1 Hinterv2].
         split.
         ++ now apply clos_rel_term_setTerm with (t1 := (applySubstitution sigma ({{t | Var v2}})));
              [now apply clos_rel_term_sym | destruct Hinterv2].
         ++ now apply clos_rel_term_listElements with (t1 := (applySubstitution sigma ({{t | Var v2}})));
              [apply clos_rel_term_sym | left].
      -- simpl in H_lVar_nil.
         rewrite applySubToC_app in H_lVar_nil.
         rewrite listVarInC_app in H_lVar_nil.
         destruct (app_eq_nil _ _ H_lVar_nil) as [H_lVar_nil34 H_lVar_niltv12].
         rewrite applySubToC_app in H_lVar_nil34.
         rewrite listVarInC_app in H_lVar_nil34.
         simpl in H_lVar_niltv12.
         rewrite app_nil_r in H_lVar_niltv12.
         destruct (app_eq_nil _ _ H_lVar_niltv12) as [H_lVar_niltv1 _].
         destruct (app_eq_nil _ _ H_lVar_niltv1) as [H_lVar_nilv1 H_lVar_niltv2].
         rewrite listVarInC_app; simpl.
         destruct (app_eq_nil _ _ H_lVar_nil34) as [-> ->].
         rewrite app_nil_l.
         rewrite app_nil_r.
         rewrite H_lVar_nilv1.
         rewrite app_nil_r.
         now destruct (app_eq_nil _ _ H_lVar_niltv2).
  + intro HstepNeq.
    case HstepNeq.
    * intros t1 t2 c c3 c4 Hdecom Hor _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil3 Hnil4].
      simpl in Hinter.
      rewrite applySubToC_app in Hinter.
      rewrite interpretC_app in Hinter.
      destruct Hinter as [Hinter3 Hinter4].
      assert (Hincl : incl ((listVarInC c3) ++ (listVarInC c4)) (map fst sigma)).
        now apply incl_app; apply listVar_applySubToC_incl.
      destruct (incl_app_inv _ _ Hincl) as [Hincl3 Hincl4].
      rewrite (decompose_eq Hdecom).
      set (l := remove_list eq_variable_dec (listVarInC (c3 ++ c4)) (listVarInPC (t1 \== t2))).
      set (EmptySet_fun := fun (v : log_variable) => (v, EmptySet)).
      set (sigma' := sigma ++ (map EmptySet_fun l)).
      assert (Heq3: (applySubstitutionToC sigma' c3) = (applySubstitutionToC sigma c3)).
        unfold sigma'; now rewrite app_applySubToC.
      assert (Heq4: (applySubstitutionToC sigma' c4) = (applySubstitutionToC sigma c4)).
        unfold sigma'; now rewrite app_applySubToC.
      exists sigma'.
      split.
      -- simpl; rewrite applySubToC_app.
         apply interpretC_app; split; try now rewrite Heq3.
         split; try now rewrite Heq4.
         case Hor as [[s1 [lt1 [s2 [lt2 [-> [-> Hneq]]]]]] | Hor]; simpl; intro HinterOT.
         ++ case Hneq as [? | ?].
            ** absurd (s1 = s2); try assumption.
               now apply (clos_rel_term_OTerm_symbol HinterOT).
            ** absurd (length (map (applySubstitution sigma') lt1) = length (map (applySubstitution sigma') lt2));
                 try now do 2 rewrite map_length.
               now apply (clos_rel_term_OTerm_length HinterOT).
         ++ case Hor as [[-> [s [lt ->]]] | Hor].
            ** absurd (OTerm s (map (applySubstitution sigma') lt) = EmptySet); try discriminate.
               apply clos_rel_term_EmptySet.
               now apply clos_rel_term_sym.
            ** case Hor as [[[s [lt ->]] ->] | Hor].
               --- absurd (OTerm s (map (applySubstitution sigma') lt) = EmptySet); try discriminate.
                   now apply clos_rel_term_EmptySet.
               --- case Hor as [[[t3 [t4 ->]] [s [lt ->]]] | Hor].
                   +++ absurd (OTerm s (map (applySubstitution sigma') lt) === ({{applySubstitution sigma' t3 | applySubstitution sigma' t4}}));
                         try now apply clos_rel_term_SetC_OTerm.
                       now apply clos_rel_term_sym.
                   +++ case Hor as [[[s [lt ->]] [t3 [t4 ->]]] | Hor].
                       *** absurd (OTerm s (map (applySubstitution sigma') lt) === ({{applySubstitution sigma' t3 | applySubstitution sigma' t4}}));
                             try assumption.
                           now apply clos_rel_term_SetC_OTerm.
                       *** case Hor as [[-> [t3 [t4 ->]]] | [[t3 [t4 ->]] ->]];
                             absurd (applySubstitution sigma' ({{t3 | t4}}) = EmptySet); try discriminate.
                           ---- apply clos_rel_term_EmptySet.
                                now apply clos_rel_term_sym.
                           ---- now apply clos_rel_term_EmptySet.
      -- simpl; rewrite applySubToC_app.
         rewrite listVarInC_app.
         rewrite Heq3.
         rewrite Hnil3.
         rewrite app_nil_l.
         simpl; rewrite Heq4.
         rewrite Hnil4.
         rewrite app_nil_r.
         enough (He : listVarInC (applySubstitutionToC sigma' ((t1 \== t2) :: nil)) = nil).
           now simpl in He; rewrite app_nil_r in He.
         enough (He : listVarInT (applySubstitution sigma' t1) = nil /\ listVarInT (applySubstitution sigma' t2) = nil).
           simpl in He.
           now simpl; destruct He as [-> ->].
         split; rewrite listVarInT_remove_list_r.
         ++ apply remove_list_eq_nil.
            unfold sigma'.
            rewrite map_app.
            intros v HIn.
            case (in_dec eq_variable_dec v (listVarInC (c3 ++ c4))) as [HIn' | HnIn].
            ** apply in_or_app; left.
               simpl in HIn'; rewrite listVarInC_app in HIn'.
               now case (in_app_or _ _ _ HIn') as [? | ?];
                 [apply (listVar_applySubToC_incl sigma _ Hnil3) | apply (listVar_applySubToC_incl sigma _ Hnil4)].
            ** apply in_or_app; right.
               apply in_map_iff.
               exists (v, EmptySet).
               split; try reflexivity.
               assert (Heq : (v, EmptySet) = EmptySet_fun v); trivial.
               rewrite Heq.
               apply in_map.
               apply in_remove_list.
               split; try assumption.
               now apply in_or_app; left.
         ++ intros [v t''] HIn HIn'.
            unfold sigma' in HIn.
            case (in_app_or _ _ _ HIn) as [HIn'' | HIn''].
            ** apply (listVar_applySubToC_nil (c3 ++ c4) sigma); try assumption.
               --- simpl; rewrite applySubToC_app.
                   rewrite listVarInC_app.
                   rewrite Hnil3.
                   now rewrite Hnil4.
               --- simpl in HlVar_incl.
                   apply HlVar_incl.
                   now apply in_map.
            ** assert (Hexists : exists v', EmptySet_fun v' = (v, t'') /\ In v' l).
                 now apply in_map_iff.
               now destruct Hexists as [v' [<- ?]].
         ++ apply remove_list_eq_nil.
            unfold sigma'.
            rewrite map_app.
            intros v HIn.
            case (in_dec eq_variable_dec v (listVarInC (c3 ++ c4))) as [HIn' | HnIn].
            ** apply in_or_app; left.
               simpl in HIn'; rewrite listVarInC_app in HIn'.
               now case (in_app_or _ _ _ HIn') as [? | ?];
                 [apply (listVar_applySubToC_incl sigma _ Hnil3) | apply (listVar_applySubToC_incl sigma _ Hnil4)].
            ** apply in_or_app; right.
               apply in_map_iff.
               exists (v, EmptySet).
               split; try reflexivity.
               assert (Heq : (v, EmptySet) = EmptySet_fun v); trivial.
               rewrite Heq.
               apply in_map.
               apply in_remove_list.
               split; try assumption.
               now apply in_or_app; right.
         ++ intros [v t''] HIn HIn'.
            unfold sigma' in HIn.
            case (in_app_or _ _ _ HIn) as [HIn'' | HIn''].
            ** apply (listVar_applySubToC_nil (c3 ++ c4) sigma); try assumption.
               --- simpl; rewrite applySubToC_app.
                   rewrite listVarInC_app.
                   rewrite Hnil3.
                   now rewrite Hnil4.
               --- simpl in HlVar_incl.
                   apply HlVar_incl.
                   now apply in_map.
            ** assert (Hexists : exists v', EmptySet_fun v' = (v, t'') /\ In v' l).
                 now apply in_map_iff.
               now destruct Hexists as [v' [<- ?]].
    * intros s lt1 lt2 c j t1 t2 c3 c4 Hdecom ? ? _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil12 Hnil34].
      destruct (app_eq_nil _ _ Hnil12) as [Hnil1 Hnil2].
      destruct (app_eq_nil _ _ Hnil34) as [Hnil3 Hnil4].
      destruct Hinter as [Hinter12 Hinter34].
      rewrite applySubToC_app in Hinter34.
      assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
        now apply interpretC_app.
      destruct Hand as [Hinter3 Hinter4].
      set (l := remove_list eq_variable_dec (listVarInC ((t1 \== t2) ::c3 ++ c4)) (listVarInPC (OTerm s lt1 \== OTerm s lt2))).
      set (EmptySet_fun := fun (v : log_variable) => (v, EmptySet)).
      set (sigma' := sigma ++ (map EmptySet_fun l)).
      assert (Hincl : incl ((listVarInC c3) ++ (listVarInC c4)) (map fst sigma)).
        now apply incl_app; apply listVar_applySubToC_incl.
      destruct (incl_app_inv _ _ Hincl) as [Hincl3 Hincl4].
      assert (Heq3: (applySubstitutionToC sigma' c3) = (applySubstitutionToC sigma c3)).
        unfold sigma'; now rewrite app_applySubToC.
      assert (Heq4: (applySubstitutionToC sigma' c4) = (applySubstitutionToC sigma c4)).
        unfold sigma'; now rewrite app_applySubToC.
      rewrite (decompose_eq Hdecom).
      exists sigma'.
      split.
      -- simpl; rewrite applySubToC_app.
         apply interpretC_app; split; try now rewrite Heq3.
         split; try now rewrite Heq4.
         intro Hinter.
         simpl in Hinter.
         assert (Habs : s = s /\ length (map (applySubstitution sigma') lt1) = length (map (applySubstitution sigma') lt2)
                         /\ (forall n : nat, nth n (map (applySubstitution sigma') lt1) EmptySet === nth n (map (applySubstitution sigma') lt2) EmptySet)).
           now apply clos_rel_term_OTerm.
         assert (Hmap_EmptySet : (applySubstitution sigma') EmptySet = EmptySet); trivial.
         assert (Hnth1 : nth j lt1 EmptySet = t1).
           now apply nth_error_nth.
         assert (Hnth1map : (nth j (map (applySubstitution sigma') lt1) EmptySet) = (applySubstitution sigma') t1).
           rewrite <- Hmap_EmptySet.
           rewrite map_nth.
           now rewrite Hnth1.
         assert (Hnth2 : nth j lt2 EmptySet = t2).
           now apply nth_error_nth.
         assert (Hnth2map : (nth j (map (applySubstitution sigma') lt2) EmptySet) = (applySubstitution sigma') t2).
           rewrite <- Hmap_EmptySet.
           rewrite map_nth.
           now rewrite Hnth2.
         destruct Habs as [_ [_ Hforall]].
         assert (Heq1 : (applySubstitution sigma' t1) = (applySubstitution sigma t1)).
           unfold sigma'; rewrite app_applySub; try reflexivity.
           now apply listVar_applySub_incl.
         assert (Heq2 : (applySubstitution sigma' t2) = (applySubstitution sigma t2)).
           unfold sigma'; rewrite app_applySub; try reflexivity.
           now apply listVar_applySub_incl.
         absurd (applySubstitution sigma t1 === applySubstitution sigma t2); try assumption.
         rewrite <- Heq1.
         rewrite <- Heq2.
         rewrite <- Hnth1map.
         rewrite <- Hnth2map.
         now apply Hforall.
      -- simpl; rewrite applySubToC_app.
         rewrite listVarInC_app.
         rewrite Heq3.
         rewrite Hnil3.
         rewrite app_nil_l.
         simpl; rewrite Heq4.
         rewrite Hnil4.
         rewrite app_nil_r.
         enough (He : listVarInC (applySubstitutionToC sigma' ((OTerm s lt1 \== OTerm s lt2) :: nil)) = nil).
           now simpl in He; rewrite app_nil_r in He.
         enough (He : listVarInT (applySubstitution sigma' (OTerm s lt1)) = nil /\ listVarInT (applySubstitution sigma' (OTerm s lt2)) = nil).
           simpl in He.
           now simpl; destruct He as [-> ->].
         split; rewrite listVarInT_remove_list_r.
         ++ apply remove_list_eq_nil.
            unfold sigma'.
            rewrite map_app.
            intros v HIn.
            case (in_dec eq_variable_dec v (listVarInC ((t1 \== t2) :: c3 ++ c4))) as [HIn' | HnIn].
            ** apply in_or_app; left.
               simpl in HIn'; rewrite listVarInC_app in HIn'.
               case (in_app_or _ _ _ HIn') as [? | HIn''].
               --- now apply (listVar_applySubToC_incl sigma ((t1 \== t2) :: nil));
                     [simpl; rewrite app_nil_r | apply in_or_app; left].
               --- now case (in_app_or _ _ _ HIn'') as [? | ?];
                     [apply (listVar_applySubToC_incl sigma _ Hnil3) | apply (listVar_applySubToC_incl sigma _ Hnil4)].
            ** apply in_or_app; right.
               apply in_map_iff.
               exists (v, EmptySet).
               split; try reflexivity.
               assert (Heq : (v, EmptySet) = EmptySet_fun v); trivial.
               rewrite Heq.
               apply in_map.
               apply in_remove_list.
               split; try assumption.
               now apply in_or_app; left.
         ++ intros [v t'] HIn HIn'.
            unfold sigma' in HIn.
            case (in_app_or _ _ _ HIn) as [HIn'' | HIn''].
            ** apply (listVar_applySubToC_nil ((t1 \== t2) :: c3 ++ c4) sigma); try assumption.
               --- simpl; rewrite applySubToC_app.
                   rewrite listVarInC_app.
                   rewrite Hnil3.
                   rewrite Hnil4.
                   now rewrite app_nil_r.
               --- simpl in HlVar_incl.
                   apply HlVar_incl.
                   now apply in_map.
            ** assert (Hexists : exists v', EmptySet_fun v' = (v, t') /\ In v' l).
                 now apply in_map_iff.
               now destruct Hexists as [v' [<- ?]].
         ++ apply remove_list_eq_nil.
            unfold sigma'.
            rewrite map_app.
            intros v HIn.
            case (in_dec eq_variable_dec v (listVarInC ((t1 \== t2) :: c3 ++ c4))) as [HIn' | HnIn].
            ** apply in_or_app; left.
               simpl in HIn'; rewrite listVarInC_app in HIn'.
               case (in_app_or _ _ _ HIn') as [? | HIn''].
               --- now apply (listVar_applySubToC_incl sigma ((t1 \== t2) :: nil));
                     [simpl; rewrite app_nil_r | apply in_or_app; left].
               --- now case (in_app_or _ _ _ HIn'') as [? | ?];
                     [apply (listVar_applySubToC_incl sigma _ Hnil3) | apply (listVar_applySubToC_incl sigma _ Hnil4)].
            ** apply in_or_app; right.
               apply in_map_iff.
               exists (v, EmptySet).
               split; try reflexivity.
               assert (Heq : (v, EmptySet) = EmptySet_fun v); trivial.
               rewrite Heq.
               apply in_map.
               apply in_remove_list.
               split; try assumption.
               now apply in_or_app; right.
         ++ intros [v t'] HIn HIn'.
            unfold sigma' in HIn.
            case (in_app_or _ _ _ HIn) as [HIn'' | HIn''].
            ** apply (listVar_applySubToC_nil ((t1 \== t2) :: c3 ++ c4) sigma); try assumption.
               --- simpl; rewrite applySubToC_app.
                   rewrite listVarInC_app.
                   rewrite Hnil3.
                   rewrite Hnil4.
                   now rewrite app_nil_r.
               --- simpl in HlVar_incl.
                   apply HlVar_incl.
                   now apply in_map.
            ** assert (Hexists : exists v', EmptySet_fun v' = (v, t') /\ In v' l).
                 now apply in_map_iff.
               now destruct Hexists as [v' [<- ?]].
    * intros ? ? ? ? ? ? _ [? [Hinter ?]].
      destruct Hinter as [HFalse HTrue].
      contradiction.
    * intros v t c c3 c4 Hdecom _ _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      destruct (app_eq_nil _ _ H_lVar_nil) as [H_lVar_nilvt H_lVar_nil34].
      destruct Hinter as [Hinter_vt Hinter_34].
      simpl in Hinter_34.
      rewrite applySubToC_app in Hinter_34.
      assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
        now apply interpretC_app.
      destruct Hand as [Hinter3 Hinter4].
      rewrite (decompose_eq Hdecom).
      exists sigma; split; simpl; rewrite applySubToC_app.
      -- apply interpretC_app; split; try assumption.
         split; try assumption.
         intro Hinter.
         absurd (applySubstitution sigma (Var v) === applySubstitution sigma t); try assumption.
         now apply clos_rel_term_sym.
      -- rewrite listVarInC_app; simpl.
         destruct (app_eq_nil _ _ H_lVar_nil34) as [-> ->].
         rewrite app_nil_l.
         rewrite app_nil_r.
         now destruct (app_eq_nil _ _ H_lVar_nilvt) as [-> ->].
    * intros v lt s c c3 c4 Hdecom HoccCheck _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil3 Hnil4].
      simpl in Hinter.
      rewrite applySubToC_app in Hinter.
      assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
        now apply interpretC_app.
      destruct Hand as [Hinter3 Hinter4].
      set (l := remove_list eq_variable_dec (listVarInC (c3 ++ c4)) (listVarInPC (Var v \== OTerm s lt))).
      set (EmptySet_fun := fun (v : log_variable) => (v, EmptySet)).
      set (sigma' := sigma ++ (map EmptySet_fun l)).
      assert (Hincl : incl ((listVarInC c3) ++ (listVarInC c4)) (map fst sigma)).
        now apply incl_app; apply listVar_applySubToC_incl.
      destruct (incl_app_inv _ _ Hincl) as [Hincl3 Hincl4].
      assert (Heq3: (applySubstitutionToC sigma' c3) = (applySubstitutionToC sigma c3)).
        unfold sigma'; now rewrite app_applySubToC.
      assert (Heq4: (applySubstitutionToC sigma' c4) = (applySubstitutionToC sigma c4)).
        unfold sigma'; now rewrite app_applySubToC.
      rewrite (decompose_eq Hdecom).
      exists sigma'.
      split.
      -- simpl; rewrite applySubToC_app.
         apply interpretC_app; split; try now rewrite Heq3.
         split; try now rewrite Heq4.
         now apply interpret_neq_OTerm.
      -- simpl; rewrite applySubToC_app.
         rewrite listVarInC_app.
         rewrite Heq3.
         rewrite Hnil3.
         rewrite app_nil_l.
         simpl; rewrite Heq4.
         rewrite Hnil4.
         rewrite app_nil_r.
         enough (He : listVarInC (applySubstitutionToC sigma' ((Var v \== OTerm s lt) :: nil)) = nil).
           now simpl in He; rewrite app_nil_r in He.
         enough (He : listVarInT (applySubstitution sigma' (Var v)) = nil /\ listVarInT (applySubstitution sigma' (OTerm s lt)) = nil).
           simpl in He.
           now simpl; destruct He as [-> ->].
         split; rewrite listVarInT_remove_list_r.
         ++ apply remove_list_eq_nil.
            unfold sigma'.
            rewrite map_app.
            intros v' HIn.
            case (in_dec eq_variable_dec v' (listVarInC (c3 ++ c4))) as [HIn' | HnIn].
            ** apply in_or_app; left.
               simpl in HIn'; rewrite listVarInC_app in HIn'.
               now case (in_app_or _ _ _ HIn') as [? | ?];
                 [apply (listVar_applySubToC_incl sigma _ Hnil3) | apply (listVar_applySubToC_incl sigma _ Hnil4)].
            ** apply in_or_app; right.
               apply in_map_iff.
               exists (v', EmptySet).
               split; try reflexivity.
               assert (Heq : (v', EmptySet) = EmptySet_fun v'); trivial.
               rewrite Heq.
               apply in_map.
               apply in_remove_list.
               split; try assumption.
               now apply in_or_app; left.
         ++ intros [v' t'] HIn HIn'.
            unfold sigma' in HIn.
            case (in_app_or _ _ _ HIn) as [HIn'' | HIn''].
            ** apply (listVar_applySubToC_nil (c3 ++ c4) sigma); try assumption.
               --- simpl; rewrite applySubToC_app.
                   rewrite listVarInC_app.
                   rewrite Hnil3.
                   rewrite Hnil4.
                   now rewrite app_nil_r.
               --- simpl in HlVar_incl.
                   apply HlVar_incl.
                   now apply in_map.
            ** assert (Hexists : exists v'', EmptySet_fun v'' = (v', t') /\ In v'' l).
                 now apply in_map_iff.
               now destruct Hexists as [v'' [<- ?]].
         ++ apply remove_list_eq_nil.
            unfold sigma'.
            rewrite map_app.
            intros v' HIn.
            case (in_dec eq_variable_dec v' (listVarInC (c3 ++ c4))) as [HIn' | HnIn].
            ** apply in_or_app; left.
               simpl in HIn'; rewrite listVarInC_app in HIn'.
               now case (in_app_or _ _ _ HIn') as [? | ?];
                 [apply (listVar_applySubToC_incl sigma _ Hnil3) | apply (listVar_applySubToC_incl sigma _ Hnil4)].
            ** apply in_or_app; right.
               apply in_map_iff.
               exists (v', EmptySet).
               split; try reflexivity.
               assert (Heq : (v', EmptySet) = EmptySet_fun v'); trivial.
               rewrite Heq.
               apply in_map.
               apply in_remove_list.
               split; try assumption.
               now apply in_or_app; right.
         ++ intros [v' t'] HIn HIn'.
            unfold sigma' in HIn.
            case (in_app_or _ _ _ HIn) as [HIn'' | HIn''].
            ** apply (listVar_applySubToC_nil (c3 ++ c4) sigma); try assumption.
               --- simpl; rewrite applySubToC_app.
                   rewrite listVarInC_app.
                   rewrite Hnil3.
                   now rewrite Hnil4.
               --- simpl in HlVar_incl.
                   apply HlVar_incl.
                   now apply in_map.
            ** assert (Hexists : exists v'', EmptySet_fun v'' = (v', t') /\ In v'' l).
                 now apply in_map_iff.
               now destruct Hexists as [v'' [<- ?]].
    * intros v t1 t2 c c3 c4 Hdecom HoC _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil3 Hnil4].
      simpl in Hinter.
      rewrite applySubToC_app in Hinter.
      assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
        now apply interpretC_app.
      destruct Hand as [Hinter3 Hinter4].
      set (l := remove_list eq_variable_dec (listVarInC (c3 ++ c4)) (listVarInPC (Var v \== ({{t1 | t2}})))).
      set (EmptySet_fun := fun (v : log_variable) => (v, EmptySet)).
      set (sigma' := sigma ++ (map EmptySet_fun l)).
      assert (Hincl : incl ((listVarInC c3) ++ (listVarInC c4)) (map fst sigma)).
        now apply incl_app; apply listVar_applySubToC_incl.
      destruct (incl_app_inv _ _ Hincl) as [Hincl3 Hincl4].
      assert (Heq3: (applySubstitutionToC sigma' c3) = (applySubstitutionToC sigma c3)).
        unfold sigma'; now rewrite app_applySubToC.
      assert (Heq4: (applySubstitutionToC sigma' c4) = (applySubstitutionToC sigma c4)).
        unfold sigma'; now rewrite app_applySubToC.
      rewrite (decompose_eq Hdecom).
      exists sigma'.
      split.
      -- simpl; rewrite applySubToC_app.
         apply interpretC_app; split; try now rewrite Heq3.
         split; try now rewrite Heq4.
         now apply interpret_neq_SetC.
      -- simpl; rewrite applySubToC_app.
         rewrite listVarInC_app.
         rewrite Heq3.
         rewrite Hnil3.
         rewrite app_nil_l.
         simpl; rewrite Heq4.
         rewrite Hnil4.
         rewrite app_nil_r.
         enough (He : listVarInC (applySubstitutionToC sigma' ((Var v \== ({{t1 | t2}})) :: nil)) = nil).
           now simpl in He; rewrite app_nil_r in He.
         enough (He : listVarInT (applySubstitution sigma' (Var v)) = nil /\ listVarInT (applySubstitution sigma' ({{t1 | t2}})) = nil).
           simpl in He.
           now simpl; destruct He as [-> ->].
         split; rewrite listVarInT_remove_list_r.
         ++ apply remove_list_eq_nil.
            unfold sigma'.
            rewrite map_app.
            intros v' HIn.
            case (in_dec eq_variable_dec v' (listVarInC (c3 ++ c4))) as [HIn' | HnIn].
            ** apply in_or_app; left.
               simpl in HIn'; rewrite listVarInC_app in HIn'.
               now case (in_app_or _ _ _ HIn') as [? | ?];
                 [apply (listVar_applySubToC_incl sigma _ Hnil3) | apply (listVar_applySubToC_incl sigma _ Hnil4)].
            ** apply in_or_app; right.
               apply in_map_iff.
               exists (v', EmptySet).
               split; try reflexivity.
               assert (Heq : (v', EmptySet) = EmptySet_fun v'); trivial.
               rewrite Heq.
               apply in_map.
               apply in_remove_list.
               split; try assumption.
               now apply in_or_app; left.
         ++ intros [v' t'] HIn HIn'.
            unfold sigma' in HIn.
            case (in_app_or _ _ _ HIn) as [HIn'' | HIn''].
            ** apply (listVar_applySubToC_nil (c3 ++ c4) sigma); try assumption.
               --- simpl; rewrite applySubToC_app.
                   rewrite listVarInC_app.
                   rewrite Hnil3.
                   rewrite Hnil4.
                   now rewrite app_nil_r.
               --- simpl in HlVar_incl.
                   apply HlVar_incl.
                   now apply in_map.
            ** assert (Hexists : exists v'', EmptySet_fun v'' = (v', t') /\ In v'' l).
                 now apply in_map_iff.
               now destruct Hexists as [v'' [<- ?]].
         ++ apply remove_list_eq_nil.
            unfold sigma'.
            rewrite map_app.
            intros v' HIn.
            case (in_dec eq_variable_dec v' (listVarInC (c3 ++ c4))) as [HIn' | HnIn].
            ** apply in_or_app; left.
               simpl in HIn'; rewrite listVarInC_app in HIn'.
               now case (in_app_or _ _ _ HIn') as [? | ?];
                 [apply (listVar_applySubToC_incl sigma _ Hnil3) | apply (listVar_applySubToC_incl sigma _ Hnil4)].
            ** apply in_or_app; right.
               apply in_map_iff.
               exists (v', EmptySet).
               split; try reflexivity.
               assert (Heq : (v', EmptySet) = EmptySet_fun v'); trivial.
               rewrite Heq.
               apply in_map.
               apply in_remove_list.
               split; try assumption.
               now apply in_or_app; right.
         ++ intros [v' t'] HIn HIn'.
            unfold sigma' in HIn.
            case (in_app_or _ _ _ HIn) as [HIn'' | HIn''].
            ** apply (listVar_applySubToC_nil (c3 ++ c4) sigma); try assumption.
               --- simpl; rewrite applySubToC_app.
                   rewrite listVarInC_app.
                   rewrite Hnil3.
                   now rewrite Hnil4.
               --- simpl in HlVar_incl.
                   apply HlVar_incl.
                   now apply in_map.
            ** assert (Hexists : exists v'', EmptySet_fun v'' = (v', t') /\ In v'' l).
                 now apply in_map_iff.
               now destruct Hexists as [v'' [<- ?]].
    * intros v lt c j tj c3 c4 Hdecom Hnth_error ? Hsort Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil_tj_v Hnil34].
      destruct (app_eq_nil _ _ Hnil34) as [Hnil3 Hnil4].
      destruct (app_eq_nil _ _ Hnil_tj_v) as [Hnil_tj Hnil_v].
      simpl in Hinter.
      rewrite applySubToC_app in Hinter.
      assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
        now apply interpretC_app.
      destruct Hand as [Hinter3 Hinter4].
      set (l := remove_list eq_variable_dec (listVarInC ((tj \:s Var v) :: (c3 ++ c4))) (listVarInPC (Var v \== listSetC lt (Var v)))).
      set (EmptySet_fun := fun (v : log_variable) => (v, EmptySet)).
      set (sigma' := sigma ++ (map EmptySet_fun l)).
      assert (Hneq_nil : map (applySubstitution sigma') lt <> nil).
        intro Habs.
        absurd (In tj nil); try now apply in_nil.
          rewrite <- (map_eq_nil _ _ Habs).
          exact (nth_error_In _ _ Hnth_error).
      assert (Hincl : incl ((listVarInC c3) ++ (listVarInC c4)) (map fst sigma)).
        now apply incl_app; apply listVar_applySubToC_incl.
      destruct (incl_app_inv _ _ Hincl) as [Hincl3 Hincl4].
      assert (Heq3 : (applySubstitutionToC sigma' c3) = (applySubstitutionToC sigma c3)).
        unfold sigma'; now rewrite app_applySubToC.
      assert (Heq4: (applySubstitutionToC sigma' c4) = (applySubstitutionToC sigma c4)).
        unfold sigma'; now rewrite app_applySubToC.
      assert (Heqv : (applySubstitution sigma' (Var v)) = (applySubstitution sigma (Var v))).
        unfold sigma'; rewrite app_applySub; try reflexivity.
        now apply listVar_applySub_incl.
      assert (Heqtj : (applySubstitution sigma' tj) = (applySubstitution sigma tj)).
        unfold sigma'; rewrite app_applySub; try reflexivity.
        now apply listVar_applySub_incl.
      assert (Hincltjv : incl ((listVarInC ((tj \:s Var v) :: nil))) (map fst sigma)).
        apply listVar_applySubToC_incl.
        simpl; rewrite Hnil_tj.
        now rewrite Hnil_v.
      assert (Heqrs: (applySubstitutionToC sigma' ((tj \:s Var v) :: nil)) = (applySubstitutionToC sigma ((tj \:s Var v) :: nil))).
        unfold sigma'; now rewrite app_applySubToC.
      revert Hsort.
      simpl; rewrite (decompose_eq Hdecom).
      intro Hsort.
      assert (HIn : In (IsSet (Var v)) (c3 ++ (Var v \== listSetC lt (Var v)) :: c4)).
        assert (He : incl (set_inferPC  (Var v \== listSetC lt (Var v))) (c3 ++  (Var v \== listSetC lt (Var v)) :: c4)).
          now apply (sort_complete_set_infer Hsort); apply in_elt.
        apply He.
        apply in_or_app; right.
        apply find_set_listSetC_Var.
        intro Habs.
        absurd (In tj nil); try now apply in_nil.
          rewrite <- Habs.
          now apply nth_error_In with (n := j).
      assert (HIsSet : In (IsSet (Var v)) (c3 ++ c4)).
        apply in_or_app.
        case (in_app_or _ _ _ HIn) as [? | HIn']; try now left.
        now case HIn' as [? | ?]; try right.
      exists sigma'; split; simpl; rewrite applySubToC_app.
      -- apply interpretC_app; split; try now rewrite Heq3.
         split; try now rewrite Heq4.
         apply mem_neg_rel_term with (t := applySubstitution sigma tj); try now rewrite Heqv.
         rewrite <- Heqtj.
         rewrite applySub_listSetC.
         split.
         ++ rewrite setTerm_listSetC; try assumption.
            assert (Hforall : (forall pc, In pc (applySubstitutionToC sigma (c3 ++ c4)) -> interpretPC pc)).
              apply interpretC_iff.
              rewrite applySubToC_app.
              rewrite interpretC_app.
              now split.
            assert (He : interpretPC (applySubstitutionToPC sigma (IsSet (Var v)))).
              apply Hforall.
              apply in_map_iff.
              exists (IsSet (Var v)).
              now split.
            now rewrite Heqv.
         ++ exists (applySubstitution sigma' tj).
            split; try apply clos_rel_term_refl.
            rewrite listElements_listSetC; try assumption.
            apply in_or_app; left.
            apply in_map_iff; exists tj.
            split; try reflexivity.
            exact (nth_error_In _ _ Hnth_error).
      -- rewrite listVarInC_app.
         rewrite Heq3.
         rewrite Hnil3.
         rewrite app_nil_l.
         simpl; rewrite Heq4.
         rewrite Hnil4.
         rewrite app_nil_r.
         simpl in Heqv.
         rewrite Heqv.
         rewrite Hnil_v.
         rewrite app_nil_l.
         rewrite listVarInT_remove_list_r.
         ++ apply remove_list_eq_nil.
            unfold sigma'.
            rewrite map_app.
            intros w HInw.
            case (in_dec eq_variable_dec w (listVarInC ((tj \:s Var v) :: c3 ++ c4))) as [HIn' | HnIn].
            ** apply in_or_app; left.
               simpl in HIn'; rewrite listVarInC_app in HIn'.
               case (in_app_or _ _ _ HIn') as [HIn2 | HIn3].
               --- apply Hincltjv.
                   apply in_or_app.
                   now left.
               --- now case (in_app_or _ _ _ HIn3) as [? | ?];
                     [apply (listVar_applySubToC_incl sigma _ Hnil3) | apply (listVar_applySubToC_incl sigma _ Hnil4)].
            ** apply in_or_app; right.
               apply in_map_iff.
               exists (w, EmptySet).
               split; try reflexivity.
               assert (Heq : (w, EmptySet) = EmptySet_fun w); trivial.
               rewrite Heq.
               apply in_map.
               apply in_remove_list.
               split; try assumption.
               now right.
         ++ intros [w t'] HIn' ?.
            unfold sigma' in HIn'.
            case (in_app_or _ _ _ HIn') as [? | ?].
            ** apply (listVar_applySubToC_nil ((tj \:s Var v) :: c3 ++ c4) sigma); try assumption.
               --- simpl; rewrite applySubToC_app.
                   rewrite listVarInC_app.
                   rewrite Hnil3.
                   rewrite Hnil4.
                   now rewrite app_nil_r.
               --- simpl in HlVar_incl.
                   apply HlVar_incl.
                   now apply in_map.
            ** assert (Hexists : exists v', EmptySet_fun v' = (w, t') /\ In v' l).
                 now apply in_map_iff.
               now destruct Hexists as [v' [<- ?]].
    * intros t1 s1 t2 s2 c v c3 c4 Hdecom _ _ _ _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      destruct (app_eq_nil _ _ H_lVar_nil) as [H_lVar_nilv1 H_lVar_nilv34].
      destruct (app_eq_nil _ _ H_lVar_nilv1) as [H_lVar_nilv H_lVar_nil1].
      destruct (app_eq_nil _ _ H_lVar_nilv34) as [H_lVar_nilv2 H_lVar_nil34].
      destruct (app_eq_nil _ _ H_lVar_nilv2) as [_ H_lVar_nil2].
      destruct Hinter as [Hinter_v1 Hinter_v2_34].
      destruct Hinter_v2_34 as [Hinter_v2 Hinter_34].
      rewrite applySubToC_app in Hinter_34.
      assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
        now apply interpretC_app.
      destruct Hand as [Hinter3 Hinter4].
      rewrite (decompose_eq Hdecom).
      exists sigma; split; simpl; rewrite applySubToC_app.
      -- apply interpretC_app; split; try assumption.
         split; try assumption.
         apply (complement_Symmetric clos_rel_term_sym).
         now apply mem_neg_rel_term with (t := (applySubstitution sigma (Var v))).
      -- rewrite listVarInC_app; simpl.
         destruct (app_eq_nil _ _ H_lVar_nil34) as [-> ->].
         rewrite app_nil_l.
         rewrite app_nil_r.
         now destruct (app_eq_nil _ _ H_lVar_nil1) as [-> ->].
    * intros t1 t2 t3 t4 c v c3 c4 Hdecom _ _ _ _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      rewrite (decompose_eq Hdecom).
      exists sigma; split; simpl; rewrite applySubToC_app.
      -- destruct Hinter as [Hinter_vt34 Hinter_vt12_34].
         destruct Hinter_vt12_34 as [Hinter_vt12 Hinter_34].
         rewrite applySubToC_app in Hinter_34.
         assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
           now apply interpretC_app.
         destruct Hand as [Hinter3 Hinter4].
         apply interpretC_app; split; try assumption.
         split; try assumption.
         now apply mem_neg_rel_term with (t := applySubstitution sigma (Var v)).
      -- rewrite listVarInC_app; simpl.
         simpl in H_lVar_nil.
         destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil_vt34 Hnil_vt12_34].
         destruct (app_eq_nil _ _ Hnil_vt12_34) as [Hnil_vt12 Hnil_34].
         rewrite applySubToC_app in Hnil_34.
         rewrite listVarInC_app in Hnil_34.
         destruct (app_eq_nil _ _ Hnil_34) as [-> ->].
         rewrite app_nil_l.
         rewrite app_nil_r.
         destruct (app_eq_nil _ _ Hnil_vt12) as [_ Hnil_t12].
         destruct (app_eq_nil _ _ Hnil_t12) as [-> ->].
         rewrite app_nil_l.
         now destruct (app_eq_nil _ _ Hnil_vt34).
  + intro HstepNmem.
    case HstepNmem.
    * intros t c c3 c4 Hdecom _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil3 Hnil4].
      simpl in Hinter.
      rewrite applySubToC_app in Hinter.
      assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
        now apply interpretC_app.
      destruct Hand as [Hinter3 Hinter4].
      set (l := remove_list eq_variable_dec (listVarInC (c3 ++ c4)) (listVarInT t)).
      set (EmptySet_fun := fun (v : log_variable) => (v, EmptySet)).
      set (sigma' := sigma ++ (map EmptySet_fun l)).
      assert (Hincl : incl ((listVarInC c3) ++ (listVarInC c4)) (map fst sigma)).
        now apply incl_app; apply listVar_applySubToC_incl.
      destruct (incl_app_inv _ _ Hincl) as [Hincl3 Hincl4].
      assert (Heq3: (applySubstitutionToC sigma' c3) = (applySubstitutionToC sigma c3)).
        unfold sigma'; now rewrite app_applySubToC.
      assert (Heq4: (applySubstitutionToC sigma' c4) = (applySubstitutionToC sigma c4)).
        unfold sigma'; now rewrite app_applySubToC.
      rewrite (decompose_eq Hdecom).
      exists sigma'.
      split.
      -- simpl; rewrite applySubToC_app.
         apply interpretC_app; split; try now rewrite Heq3.
         split; try now rewrite Heq4.
         now intros [_ [? [_ ?]]].
      -- simpl; rewrite applySubToC_app.
         rewrite listVarInC_app.
         rewrite Heq3.
         rewrite Hnil3.
         rewrite app_nil_l.
         simpl; rewrite Heq4.
         rewrite Hnil4.
         rewrite app_nil_r.
         enough (Heq : listVarInT ((applySubstitution sigma') t) = nil).
           now simpl in Heq; rewrite Heq.
         rewrite listVarInT_remove_list_r.
         ++ apply remove_list_eq_nil.
            unfold sigma'.
            rewrite map_app.
            intros v HIn.
            case (in_dec eq_variable_dec v (listVarInC (c3 ++ c4))) as [HIn' | HnIn].
            ** apply in_or_app; left.
               rewrite listVarInC_app in HIn'.
               now case (in_app_or _ _ _ HIn') as [? | ?];
                 [apply (listVar_applySubToC_incl sigma _ Hnil3) | apply (listVar_applySubToC_incl sigma _ Hnil4)].
            ** apply in_or_app; right.
               apply in_map_iff.
               exists (v, EmptySet).
               split; try reflexivity.
               assert (Heq : (v, EmptySet) = EmptySet_fun v); trivial.
               rewrite Heq.
               apply in_map.
               apply in_remove_list.
               now split.
         ++ intros [v t'] HIn HIn'.
            unfold sigma' in HIn.
            case (in_app_or _ _ _ HIn) as [HIn'' | HIn''].
            ** apply (listVar_applySubToC_nil (c3 ++ c4) sigma); try assumption.
               --- rewrite applySubToC_app.
                   rewrite listVarInC_app.
                   rewrite Hnil3.
                   now rewrite Hnil4.
               --- simpl in HlVar_incl.
                   apply HlVar_incl.
                   now apply in_map.
            ** assert (Hexists : exists v', EmptySet_fun v' = (v, t') /\ In v' l).
                 now apply in_map_iff.
               now destruct Hexists as [v' [<- ?]].
    * intros r s t c c3 c4 Hdecom _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      destruct (app_eq_nil _ _ H_lVar_nil) as [Hnilrt Hnil].
      destruct (app_eq_nil _ _ Hnilrt) as [Hnilr Hnilt].
      destruct (app_eq_nil _ _ Hnil) as [Hnilrs Hnil34].
      destruct (app_eq_nil _ _ Hnilrs) as [_ Hnils].
      destruct (app_eq_nil _ _ Hnil34) as [Hnil3 Hnil4].
      simpl in Hinter.
      destruct Hinter as [Hninter Hinter'].
      destruct Hinter' as [Hinter Hinter34].
      rewrite applySubToC_app in Hinter34.
      assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
        now apply interpretC_app.
      destruct Hand as [Hinter3 Hinter4].
      rewrite (decompose_eq Hdecom).
      exists sigma.
      split; simpl; rewrite applySubToC_app.
      -- apply interpretC_app; split; try assumption.
         split; try assumption.
         intros [? [t' [? H]]].
         simpl in H.
         case H as [Heqt' | HInt'].
         ++ assert (applySubstitution sigma r === applySubstitution sigma t).
              apply clos_rel_term_sym.
              now rewrite Heqt'.
            contradiction.
         ++ absurd (setTerm (applySubstitution sigma s) /\ (exists t : term,
               t === applySubstitution sigma r /\ In t (listElements (applySubstitution sigma s)))); try assumption.
            split; try assumption.
            now exists t'.
      -- rewrite listVarInC_app.
         rewrite Hnil3.
         rewrite app_nil_l.
         simpl; rewrite Hnil4.
         rewrite app_nil_r.
         rewrite Hnilr.
         rewrite app_nil_l.
         rewrite Hnilt.
         now rewrite Hnils.
    * intros t c v c3 c4 Hdecom HoccCheck _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil3 Hnil4].
      simpl in Hinter.
      rewrite applySubToC_app in Hinter.
      rewrite interpretC_app in Hinter.
      destruct Hinter as [Hinter3 Hinter4].
      set (l := remove_list eq_variable_dec (listVarInC (c3 ++ c4)) (listVarInPC (t \:s Var v))).
      set (EmptySet_fun := fun (v : log_variable) => (v, EmptySet)).
      set (sigma' := sigma ++ (map EmptySet_fun l)).
      assert (Hincl : incl ((listVarInC c3) ++ (listVarInC c4)) (map fst sigma)).
        now apply incl_app; apply listVar_applySubToC_incl.
      destruct (incl_app_inv _ _ Hincl) as [Hincl3 Hincl4].
      assert (Heq3: (applySubstitutionToC sigma' c3) = (applySubstitutionToC sigma c3)).
        unfold sigma'; now rewrite app_applySubToC.
      assert (Heq4: (applySubstitutionToC sigma' c4) = (applySubstitutionToC sigma c4)).
        unfold sigma'; now rewrite app_applySubToC.
      rewrite (decompose_eq Hdecom).
      exists sigma'.
      split.
      -- simpl; rewrite applySubToC_app.
         apply interpretC_app; split; try now rewrite Heq3.
         split; try now rewrite Heq4.
         now apply interpret_nmem.
      -- simpl; rewrite applySubToC_app.
         rewrite listVarInC_app.
         rewrite Heq3.
         rewrite Hnil3.
         rewrite app_nil_l.
         simpl; rewrite Heq4.
         rewrite Hnil4.
         rewrite app_nil_r.
         enough (He : listVarInC (applySubstitutionToC sigma' ((t \:s Var v) :: nil)) = nil).
           now simpl in He; rewrite app_nil_r in He.
         enough (He : listVarInT (applySubstitution sigma' t) = nil /\ listVarInT (applySubstitution sigma' (Var v)) = nil).
           simpl in He.
           now simpl; destruct He as [-> ->].
         split; rewrite listVarInT_remove_list_r.
         ++ apply remove_list_eq_nil.
            unfold sigma'.
            rewrite map_app.
            intros v' HIn.
            case (in_dec eq_variable_dec v' (listVarInC (c3 ++ c4))) as [HIn' | HnIn].
            ** apply in_or_app; left.
               simpl in HIn'; rewrite listVarInC_app in HIn'.
               now case (in_app_or _ _ _ HIn') as [? | ?];
                 [apply (listVar_applySubToC_incl sigma _ Hnil3) | apply (listVar_applySubToC_incl sigma _ Hnil4)].
            ** apply in_or_app; right.
               apply in_map_iff.
               exists (v', EmptySet).
               split; try reflexivity.
               assert (Heq : (v', EmptySet) = EmptySet_fun v'); trivial.
               rewrite Heq.
               apply in_map.
               apply in_remove_list.
               split; try assumption.
               now apply in_or_app; left.
         ++ intros [v' t''] HIn HIn'.
            unfold sigma' in HIn.
            case (in_app_or _ _ _ HIn) as [HIn'' | HIn''].
            ** apply (listVar_applySubToC_nil (c3 ++ c4) sigma); try assumption.
               --- simpl; rewrite applySubToC_app.
                   rewrite listVarInC_app.
                   rewrite Hnil3.
                   now rewrite Hnil4.
               --- simpl in HlVar_incl.
                   apply HlVar_incl.
                   now apply in_map.
            ** assert (Hexists : exists v'', EmptySet_fun v'' = (v', t'') /\ In v'' l).
                 now apply in_map_iff.
               now destruct Hexists as [v'' [<- ?]].
         ++ apply remove_list_eq_nil.
            unfold sigma'.
            rewrite map_app.
            intros v' HIn.
            case (in_dec eq_variable_dec v' (listVarInC (c3 ++ c4))) as [HIn' | HnIn].
            ** apply in_or_app; left.
               simpl in HIn'; rewrite listVarInC_app in HIn'.
               now case (in_app_or _ _ _ HIn') as [? | ?];
                 [apply (listVar_applySubToC_incl sigma _ Hnil3) | apply (listVar_applySubToC_incl sigma _ Hnil4)].
            ** apply in_or_app; right.
               apply in_map_iff.
               exists (v', EmptySet).
               split; try reflexivity.
               assert (Heq : (v', EmptySet) = EmptySet_fun v'); trivial.
               rewrite Heq.
               apply in_map.
               apply in_remove_list.
               split; try assumption.
               now apply in_or_app; right.
         ++ intros [v' t''] HIn HIn'.
            unfold sigma' in HIn.
            case (in_app_or _ _ _ HIn) as [HIn'' | HIn''].
            ** apply (listVar_applySubToC_nil (c3 ++ c4) sigma); try assumption.
               --- simpl; rewrite applySubToC_app.
                   rewrite listVarInC_app.
                   rewrite Hnil3.
                   now rewrite Hnil4.
               --- simpl in HlVar_incl.
                   apply HlVar_incl.
                   now apply in_map.
            ** assert (Hexists : exists v'', EmptySet_fun v'' = (v', t'') /\ In v'' l).
                 now apply in_map_iff.
               now destruct Hexists as [v'' [<- ?]].
  + intro HstepSC.
    case HstepSC.
    * intros c c3 c4 Hdecom _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      simpl in Hinter.
      rewrite applySubToC_app in Hinter.
      assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma c4)).
        now apply interpretC_app.
      destruct Hand as [Hinter3 Hinter4].
      rewrite (decompose_eq Hdecom).
      exists sigma; split; simpl; rewrite applySubToC_app.
      -- apply interpretC_app; split; try assumption.
         now split.
      -- now rewrite listVarInC_app.
    * intros s t c c3 c4 Hdecom _ Hsat.
      destruct (satisfiable_simple_sub Hsat) as [sigma [HlVar_incl [HNoDup [Hinter H_lVar_nil]]]].
      simpl in H_lVar_nil.
      rewrite applySubToC_app in H_lVar_nil.
      rewrite listVarInC_app in H_lVar_nil.
      destruct (app_eq_nil _ _ H_lVar_nil) as [Hnil3 Hnil].
      simpl in Hnil.
      destruct (app_eq_nil _ _ Hnil) as [Hnilt Hnil4].
      simpl in Hinter.
      rewrite applySubToC_app in Hinter.
      assert (Hand : interpretC (applySubstitutionToC sigma c3) /\ interpretC (applySubstitutionToC sigma (IsSet t :: c4))).
        now apply interpretC_app.
      destruct Hand as [Hinter3 Hintert4].
      destruct Hintert4 as [Hintert Hinter4].
      set (l := remove_list eq_variable_dec (listVarInC (c3 ++ (IsSet t :: nil) ++ c4)) (listVarInT s)).
      set (EmptySet_fun := fun (v : log_variable) => (v, EmptySet)).
      set (sigma' := sigma ++ (map EmptySet_fun l)).
      assert (Hincl : incl ((listVarInC c3) ++ (listVarInC c4)) (map fst sigma)).
        now apply incl_app; apply listVar_applySubToC_incl.
      destruct (incl_app_inv _ _ Hincl) as [Hincl3 Hincl4].
      assert (Heq3: (applySubstitutionToC sigma' c3) = (applySubstitutionToC sigma c3)).
        unfold sigma'; now rewrite app_applySubToC.
      assert (Heq4: (applySubstitutionToC sigma' c4) = (applySubstitutionToC sigma c4)).
        unfold sigma'; now rewrite app_applySubToC.
      assert (Hinclrt : incl (listVarInC (IsSet t :: nil)) (map fst sigma)).
        apply listVar_applySubToC_incl.
        simpl; now rewrite Hnilt.
      assert (Heqt: (applySubstitutionToC sigma' (IsSet t :: nil)) = (applySubstitutionToC sigma (IsSet t :: nil))).
        unfold sigma'; now rewrite app_applySubToC.
      inversion Heqt as [Heqt'].
      rewrite (decompose_eq Hdecom).
      exists sigma'.
      split.
      -- simpl; rewrite applySubToC_app.
         apply interpretC_app; split; try now rewrite Heq3.
         split; try now rewrite Heq4.
         simpl; now rewrite Heqt'.
      -- simpl; rewrite applySubToC_app.
         rewrite listVarInC_app.
         rewrite Heq3.
         rewrite Hnil3.
         rewrite app_nil_l.
         simpl; rewrite Heq4.
         rewrite Hnil4.
         rewrite app_nil_r.
         rewrite Heqt'.
         rewrite Hnilt.
         rewrite app_nil_r.
         rewrite listVarInT_remove_list_r.
         ++ apply remove_list_eq_nil.
            unfold sigma'.
            rewrite map_app.
            intros v HIn.
            case (in_dec eq_variable_dec v (listVarInC (c3 ++ (IsSet t :: nil) ++ c4))) as [HIn' | HnIn].
            ** apply in_or_app; left.
               rewrite listVarInC_app in HIn'.
               case (in_app_or _ _ _ HIn') as [? | HIn'']; try now apply (listVar_applySubToC_incl sigma _ Hnil3).
               case (in_app_or _ _ _ HIn'') as [? | ?]; try now apply (listVar_applySubToC_incl sigma _ Hnil4).
               apply (listVar_applySubToC_incl sigma (IsSet t :: nil)).
               --- now simpl; rewrite Hnilt.
               --- now apply in_or_app; left.
            ** apply in_or_app; right.
               apply in_map_iff.
               exists (v, EmptySet).
               split; try reflexivity.
               assert (Heq : (v, EmptySet) = EmptySet_fun v); trivial.
               rewrite Heq.
               apply in_map.
               apply in_remove_list.
               now split.
         ++ intros [v t'] HIn HIn'.
            unfold sigma' in HIn.
            case (in_app_or _ _ _ HIn) as [HIn'' | HIn''].
            ** apply (listVar_applySubToC_nil (c3 ++ (IsSet t :: nil) ++ c4) sigma); try assumption.
               --- rewrite applySubToC_app.
                   rewrite listVarInC_app.
                   rewrite Hnil3.
                   simpl; rewrite Hnil4.
                   now rewrite Hnilt.
               --- simpl in HlVar_incl.
                   apply HlVar_incl.
                   now apply in_map.
            ** assert (Hexists : exists v', EmptySet_fun v' = (v, t') /\ In v' l).
                 now apply in_map_iff.
               now destruct Hexists as [v' [<- ?]].
    * intros ? ? ? ? ? ? _ [? [Hinter ?]].
      destruct Hinter as [HFalse HTrue].
      contradiction.
- now intros ? ?.
- intros p3 p4 p5 Hcrt34 HP34 Hcrt45 HP45 Hsort_c3 Hsat5.
  apply HP34; try assumption.
  apply HP45; try assumption.
  now apply (sort_completeness_preservation Hcrt34).
Qed.

Theorem satisfiability_preservation c1 :
  (exists pc, In pc c1 /\ ~ (isInSFPC pc c1)) ->
    sort_complete c1 -> satisfiable c1 ->
      exists c2, step c1 c2 /\ satisfiable c2.
Proof.
intros Hexists Hsort Hsat.
destruct Hexists as [pc [HIn HnSF]].
revert HIn.
revert HnSF.
case pc.
- intros t1 t2.
  case t1.
  + intros v ?.
    revert HnSF.
    case t2.
    * intros v' HnSF.
      case (eq_variable_dec v v') as [<- | Hneq].
      -- intros HIn.
         destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
         exists (c1'++c2').
         split.
         ++ apply step1.
            apply stepEq1 with (t := Var v).
            now apply eq_decompose.
         ++ rewrite Heq in Hsat.
            destruct Hsat as [sigma [Hinter Hvar]].
            exists sigma.
            rewrite applySubToC_app in Hinter.
            assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v == Var v) :: c2'))).
              now apply interpretC_app.
            destruct Hand as [Hinter1 Hinterv2].
            rewrite applySubToC_app in Hvar.
            destruct Hinterv2 as [Hinterv Hinter2].
            rewrite listVarInC_app in Hvar.
            unfold satisfies; simpl.
            rewrite applySubToC_app.
            split.
            ** now apply interpretC_app.
            ** rewrite listVarInC_app.
               destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
               simpl in Hvar'.
               now destruct (app_eq_nil _ _ Hvar') as [_ ->].
      -- intros HIn.
         destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
         exists ((Var v == Var v') :: (applySubstitutionToC ((v,Var v') :: nil) (c1'++c2'))).
         split.
         ++ apply step1.
            apply stepEq5; try now simpl.
            ** now apply eq_decompose.
            ** right; right.
               now exists v'.
            ** now rewrite Heq in HnSF.
         ++ rewrite Heq in Hsat.
            destruct Hsat as [sigma [Hinter Hvar]].
            rewrite applySubToC_app in Hinter.
            assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v == Var v') :: c2'))).
              now apply interpretC_app.
            destruct Hand as [Hinter1 HinterOT2].
            destruct HinterOT2 as [HinterOT Hinter2].
            exists sigma; split.
            ** split; try assumption.
               case (eq_term_dec (applySubstitution sigma (Var v')) EmptySet) as [HeqE | ?];
                 rewrite applySubToC_cons.
               --- assert (applySubstitution sigma (Var v) = EmptySet).
                     apply clos_rel_term_EmptySet.
                     now rewrite <- HeqE.
                   rewrite applySubToC_app.
                   rewrite HeqE.
                   rewrite applySubC_EmptySet; try assumption.
                   rewrite applySubC_EmptySet; try assumption.
                   now apply interpretC_app.
               --- apply interpret_applySubC_Var; try assumption.
                   rewrite applySubToC_app.
                   now apply interpretC_app.
            ** rewrite applySubToC_app in Hvar.
               rewrite listVarInC_app in Hvar.
               destruct (app_eq_nil _ _ Hvar) as [Hnil1 Hvar'].
               simpl in Hvar'.
               simpl; destruct (app_eq_nil _ _ Hvar') as [HnilV Hnil2].
               rewrite HnilV.
               simpl; rewrite applySubToC_cons.
               destruct (app_eq_nil _ _ HnilV) as [? ?].
               apply listVarInC_applySub_Var; try assumption.
               rewrite applySubToC_app.
               rewrite listVarInC_app.
               rewrite Hnil1.
               now rewrite Hnil2.
    * intros t3 t4 HnSF HIn; simpl in HnSF.
      assert (Hor_tail : tail t4 = Some EmptySet \/ exists u, tail t4 = Some (Var u)).
        case (dec_setTerm t4) as [HsetTerm | Hneg_setTerm];
          try now left; destruct (setTerm_exists_listSetC _ HsetTerm) as [lt ->]; apply tail_listSetC_EmptySet.
        destruct (find_set_SetC_exist t3 _ Hneg_setTerm) as [t [HIn' Hforall]].
        assert (Hincl : incl (set_inferPC (Var v == ({{t3 | t4}}))) c1).
          now apply sort_complete_set_infer.
        assert (HIn'' : In (IsSet t) c1).
          apply Hincl.
          apply in_or_app.
          now right.
        destruct (in_split _ _ HIn'') as [c1' [c2' Heq]].
        rewrite Heq in Hsat.
        destruct Hsat as [sigma [Hinter _]].
        rewrite applySubToC_app in Hinter.
        assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma (IsSet t :: c2'))).
          now apply interpretC_app.
        destruct Hand as [_ Hintert2].
        destruct Hintert2 as [Hintert _].
        rewrite <- Hforall in Hintert.
        now right; apply setTerm_negsetTerm_tail_exists_Var with (t1 := t3) (sigma := sigma).
      case Hor_tail as [Htail | [v' Htail]].
      -- case (occurCheck_dec v ({{t3 | t4}})) as [Hocc | ?].
         ++ destruct (tail_EmptySet_exists t3 _ Htail) as [lt Heq].
            rewrite Heq in Hocc.
            rewrite Heq in HIn.
            destruct (in_split _ _ HIn) as [c1' [c2' Heq']].
            rewrite Heq' in Hsat.
            destruct Hsat as [sigma [Hinter _]].
            rewrite applySubToC_app in Hinter.
            assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v == listSetC lt EmptySet) :: c2'))).
              now apply interpretC_app.
            destruct Hand as [_ Hinterv2].
            destruct Hinterv2 as [Hinterv _].
            case (axiomFS_3 _ _ _ Hinterv Hocc) as [Habs | [lt' [Habs [_ Hneg_nil]]]].
            ** revert Habs.
               now elim lt.
            ** absurd (Some EmptySet = Some (Var v)); try discriminate.
               rewrite <- tail_listSetC_EmptySet with (lt := lt).
               rewrite <- tail_listSetC_Var with (lt := lt'); try assumption.
               now rewrite Habs.
         ++ assert (HsetTerm : setTerm ({{t3 | t4}})).
              destruct (tail_EmptySet_exists t3 _ Htail) as [lt ->].
              now elim lt.
            destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
            exists ((Var v == {{t3 | t4}}) :: (applySubstitutionToC ((v,{{t3 | t4}}) :: nil) (c1'++c2'))).
            split.
            ** apply step1.
               apply stepEq5; try now simpl.
               --- now apply eq_decompose.
               --- now left.
               --- now rewrite Heq in HnSF.
            ** rewrite Heq in Hsat.
               destruct Hsat as [sigma [Hinter Hvar]].
               exists sigma.
               rewrite applySubToC_app in Hinter.
               assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v == {{t3 | t4}}) :: c2'))).
                 now apply interpretC_app.
               destruct Hand as [Hinter1 HinterS2].
               destruct HinterS2 as [HinterS Hinter2].
               rewrite applySubToC_app in Hvar.
               rewrite listVarInC_app in Hvar.
               unfold satisfies; simpl.
               rewrite applySubToC_cons.
               rewrite applySubToC_app.
               split.
               --- split; try assumption.
                   apply interpretC_app.
                   now split; apply interpret_applySubC_Var.
               --- rewrite listVarInC_app.
                   destruct (app_eq_nil _ _ Hvar) as [? Hvar'].
                   simpl in Hvar'.
                   destruct (app_eq_nil _ _ Hvar') as [Hvar'' ?].
                   destruct (app_eq_nil _ _ Hvar') as [Hvar3 ?].
                   destruct (app_eq_nil _ _ Hvar3) as [-> Hvar4].
                   destruct (app_eq_nil _ _ Hvar4) as [-> ->].
                   rewrite listVarInC_applySub_Var; try assumption.
                   now rewrite listVarInC_applySub_Var.
      -- case (occurCheck_dec v ({{t3 | t4}})) as [Hocc | ?].
         ++ case (eq_variable_dec v v') as [<- | Hneq].
            ** case (occurCheckList_dec v (SetCToList t3 t4)) as [? | ?].
               --- destruct (tail_Var_exists t3 _ Htail) as [lt [? Heq]].
                   rewrite Heq in Hocc.
                   rewrite Heq in HIn.
                   destruct (in_split _ _ HIn) as [c1' [c2' Heq']].
                   rewrite Heq' in Hsat.
                   destruct Hsat as [sigma [Hinter _]].
                   rewrite applySubToC_app in Hinter.
                   assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v == listSetC lt (Var v)) :: c2'))).
                     now apply interpretC_app.
                   destruct Hand as [_ Hinterv2].
                   destruct Hinterv2 as [Hinterv _].
                   case (axiomFS_3 _ _ _ Hinterv Hocc) as [Habs | [lt' [Habs [HoccL Hneq_nil]]]];
                     try now rewrite Habs in Heq; discriminate.
                   rewrite Habs in Heq.
                   now rewrite <- (listSetC_SetCToList _ _ Heq) in HoccL.
               --- pose (u := FreshVarFun c1).
                   destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
                   assert (HisFfst : isFreshC u c1).
                     now apply FreshVarFun_isFresh.
                   assert (HisFSt3t4 : isFreshL u (SetCToList t3 t4)).
                     apply isFreshT_SetC_isFreshL.
                     intro Habs.
                     absurd (occurCheckC u c1); try assumption.
                     apply in_occurCheckC with (pc := (Var v == ({{t3 | t4}}))); try now right.
                     rewrite Heq.
                     apply in_or_app; right.
                     now apply in_eq.
                   assert (HnegIn2 : ~ In u (listVarInC c2')).
                     intro HIn'.
                     absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                     apply incl_occurCheckC with (c1 := c2'); try now apply In_listVarInC_occurCheckC.
                     rewrite Heq.
                     apply incl_appr.
                     now apply incl_tl.
                   assert (HnegIn3 : ~ In u (listVarInT t3)).
                     intro Habs.
                     absurd (occurCheckList u (SetCToList t3 t4)); try assumption.
                     left.
                     now apply In_listVarInT_occurCheck.
                   assert (HnegIn4 : ~ In u (listVarInC c1')).
                     intro HIn'.
                     absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                     apply incl_occurCheckC with (c1 := c1'); try now apply In_listVarInC_occurCheckC.
                     rewrite Heq.
                     now apply incl_appl.
                   assert (Hneq : u <> v).
                     intro Habs.
                     absurd (occurCheckC u c1); try assumption.
                     apply In_listVarInC_occurCheckC.
                     rewrite Habs.
                     rewrite Heq.
                     rewrite listVarInC_app.
                     apply in_or_app; right.
                     now left.
                   rewrite Heq in Hsat.
                   destruct Hsat as [sigma [Hinter Hvar]].
                   rewrite applySubToC_app in Hinter.
                   assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v == ({{t3 | t4}})) :: c2'))).
                     now apply interpretC_app.
                   destruct Hand as [Hinter1 HinterS2].
                   destruct HinterS2 as [HinterS Hinter2].
                   exists ((((Var v) == (listSetC (SetCToList t3 t4) (Var u))) :: ((IsSet (Var u)) :: nil)) ++ (c1'++c2')).
                   split.
                   +++ apply step1.
                       apply stepEq6; try assumption.
                       now apply eq_decompose.
                   +++ exists ((u, applySubstitution sigma (Var v)) :: sigma).
                       split.
                       *** split.
                           ---- apply t_trans with (y := applySubstitution sigma ({{t3 | t4}})).
                                ++++ rewrite neq_listVarInT_applySub; try assumption.
                                     intro Hor.
                                     now case Hor as [Heq' | ?]; [rewrite Heq' in Hneq | trivial].
                                ++++ apply t_trans with (y := applySubstitution sigma (listSetC (SetCToList t3 t4) (Var v))); try now apply tail_applySub_listSetC_SetCToList.
                                     do 2 rewrite applySub_listSetC.
                                     assert (Heq' : applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma) (Var u) = applySubstitution sigma (Var v)).
                                       now simpl; case (eq_variable_dec u u) as [_ | ?]; try now trivial.
                                     rewrite Heq'.
                                     apply incl_interpret_listSetC_clos_rel_term.
                                     **** intros t HInt.
                                          assert (Hexists : exists t', applySubstitution sigma t' = t /\ In t' (SetCToList t3 t4)).
                                            now apply in_map_iff.
                                          destruct Hexists as [t' [<- ?]].
                                          exists (applySubstitution sigma t').
                                          split; try now apply clos_rel_term_refl.
                                          rewrite <- neq_listVarInT_applySub with (v := u) (t1 := applySubstitution sigma (Var v)); try now apply in_map.
                                          intro Habs.
                                          absurd (occurCheckList u (SetCToList t3 t4)); try assumption.
                                          apply occurCheckList_exists.
                                          exists t'.
                                          split; try assumption.
                                          now apply In_listVarInT_occurCheck.
                                     **** intros t HInt.
                                          assert (Hexists : exists t', applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma) t' = t /\ In t' (SetCToList t3 t4)).
                                            now apply in_map_iff.
                                          destruct Hexists as [t' [<- ?]].
                                          rewrite neq_listVarInT_applySub;
                                          try now exists (applySubstitution sigma t');
                                          split; [apply clos_rel_term_refl | apply in_map].
                                          intro Habs.
                                          absurd (occurCheckList u (SetCToList t3 t4)); try assumption.
                                          apply occurCheckList_exists.
                                          exists t'.
                                          split; try assumption.
                                          now apply In_listVarInT_occurCheck.
                           ---- do 2 rewrite applySubToC_app.
                                split.
                                ++++ simpl; case (eq_variable_dec u u) as [_ | ?]; try now trivial.
                                     apply clos_rel_term_setTerm with (t1 := applySubstitution sigma ({{t3 | t4}}));
                                       try now apply clos_rel_term_sym.
                                     assert (Hneg_setTerm : ~ setTerm t4).
                                       intro HsetTerm.
                                       destruct (setTerm_exists_listSetC _ HsetTerm) as [lt ->].
                                       revert Htail.
                                       elim lt; try discriminate.
                                       intros ? lt'.
                                       now case lt'.
                                     destruct (find_set_SetC_exist t3 _ Hneg_setTerm) as [t [HIn' Hforall]].
                                     assert (H' : interpretPC (applySubstitutionToPC sigma (IsSet ({{t3 | t4}}))) = interpretPC (applySubstitutionToPC sigma (IsSet t))).
                                       now apply Hforall.
                                     simpl in H'.
                                     simpl; rewrite H'.
                                     assert (Hincl : incl (set_inferPC (Var v == ({{t3 | t4}}))) c1).
                                       now apply sort_complete_set_infer.
                                     assert (HIn'' : In (IsSet t) c1).
                                       apply Hincl.
                                       apply in_or_app.
                                       now right.
                                     apply IsSet_interpretC_setTerm with (c := c1); try assumption.
                                     rewrite Heq.
                                     rewrite applySubToC_app.
                                     apply interpretC_app; split; try assumption.
                                     now split.
                                ++++ apply interpretC_app; split; try now trivial.
                                     apply interpretC_app; split; rewrite <- applySubToC_cons; rewrite neq_listVarInC_applySub; try rewrite applySubstitutionToC_nil; assumption.
                       *** simpl; rewrite applySubToC_app.
                           rewrite listVarInC_app.
                           rewrite applySubToC_app in Hvar.
                           rewrite listVarInC_app in Hvar.
                           destruct (app_eq_nil _ _ Hvar) as [Hvar1 HvarvS2].
                           rewrite <- neq_listVarInC_applySub with (v := u) (t := applySubstitution sigma (Var v)) in Hvar1; try assumption.
                           simpl in Hvar1.
                           rewrite Hvar1.
                           simpl in HvarvS2.
                           destruct (app_eq_nil _ _ HvarvS2) as [HvarvS Hvar2].
                           rewrite <- neq_listVarInC_applySub with (v := u) (t := applySubstitution sigma (Var v)) in Hvar2; try assumption.
                           simpl in Hvar2.
                           rewrite Hvar2.
                           case (eq_variable_dec u u) as [_ | ?]; try contradiction.
                           case (eq_variable_dec v u) as [Heq' | ?]; try now rewrite Heq' in Hneq.
                           destruct (app_eq_nil _ _ HvarvS) as [-> _].
                           enough (He : listVarInT (applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma) (listSetC (SetCToList t3 t4) (Var u))) = nil).
                             now simpl in He; rewrite He.
                           rewrite applySub_listSetC.
                           enough (He : listVarInListT (map (applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma)) (SetCToList t3 t4)) ++
                                        listVarInT (applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma) (Var u)) = nil).
                             now apply incl_l_nil; rewrite <- He; apply listSetC_listVarInListT.
                           simpl.
                           case (eq_variable_dec u u) as [_ | ?]; try contradiction.
                           destruct (app_eq_nil _ _ HvarvS) as [-> Hvar34].
                           rewrite neq_listVarInT_applySub; try assumption.
                           destruct (app_eq_nil _ _ Hvar34) as [-> ?].
                           simpl; rewrite app_nil_r.
                           apply listVarInListT_eq_nil.
                           intros t HInt.
                           assert (Hexists : exists t', applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma) t' = t /\ In t' (listElements t4)).
                             now apply in_map_iff.
                           destruct Hexists as [t' [<- HInt']].
                           assert (Hneg_in : ~ In u (listVarInT t')).
                             intro Habs.
                             absurd (occurCheckList u (SetCToList t3 t4)); try assumption.
                             right.
                             apply occurCheckList_exists.
                             exists t'.
                             split; try assumption.
                             now apply In_listVarInT_occurCheck.
                           rewrite neq_listVarInT_applySub; try assumption.
                           apply incl_l_nil.
                           rewrite <- H.
                           apply incl_tran with (m := listVarInListT (listElements (applySubstitution sigma t4)));
                             try now apply incl_listVar_listElements.
                           apply incl_listVarInT_listVarInListT.
                           now apply applySub_listElements.
            ** destruct (tail_Var_exists t3 _ Htail) as [lt [? Heq']].
               rewrite Heq' in Hocc.
               rewrite Heq' in HIn.
               destruct (in_split _ _ HIn) as [c1' [c2' Heq'']].
               rewrite Heq'' in Hsat.
               destruct Hsat as [sigma [Hinter _]].
               rewrite applySubToC_app in Hinter.
               assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v == listSetC lt (Var v')) :: c2'))).
                 now apply interpretC_app.
               destruct Hand as [_ Hinterv2].
               destruct Hinterv2 as [Hinterv _].
               case (axiomFS_3 _ _ _ Hinterv Hocc) as [Habs | [lt' [Habs [HoccL ?]]]].
               --- revert Habs.
                   elim lt.
                   +++ intro Habs.
                       revert Hneq.
                       now inversion Habs.
                   +++ intros t' lt'.
                       now case lt'.
               --- absurd (Some (Var v) = Some (Var v')); try now intro Habs'; inversion Habs'.
                   rewrite <- tail_listSetC_Var with (lt := lt'); try assumption.
                   rewrite <- tail_listSetC_Var with (lt := lt); try assumption.
                   now rewrite Habs.
         ++ case (in_dec eq_primc_dec (IsSet (Var v)) c1) as [? | ?].
            ** destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
               exists ((Var v == {{t3 | t4}}) :: (applySubstitutionToC ((v,{{t3 | t4}}) :: nil) (c1'++c2'))).
               split.
               --- apply step1.
                   apply stepEq5; try now simpl.
                   +++ now apply eq_decompose.
                   +++ right; right.
                       now exists v'.
                   +++ now rewrite Heq in HnSF.
               --- rewrite Heq in Hsat.
                   destruct Hsat as [sigma [Hinter Hvar]].
                   exists sigma.
                   rewrite applySubToC_app in Hinter.
                   assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v == {{t3 | t4}}) :: c2'))).
                     now apply interpretC_app.
                   destruct Hand as [Hinter1 HinterS2].
                   destruct HinterS2 as [HinterE Hinter2].
                   rewrite applySubToC_app in Hvar.
                   rewrite listVarInC_app in Hvar.
                   unfold satisfies; simpl.
                   rewrite applySubToC_cons.
                   rewrite applySubToC_app.
                   split.
                   +++ split; try assumption.
                       apply interpretC_app.
                       now split; apply interpret_applySubC_Var.
                   +++ rewrite listVarInC_app.
                       destruct (app_eq_nil _ _ Hvar) as [? Hvar'].
                       destruct (app_eq_nil _ _ Hvar') as [Hvar'' ?].
                       destruct (app_eq_nil _ _ Hvar') as [Hvar3 ?].
                       simpl in Hvar3.
                       destruct (app_eq_nil _ _ Hvar3) as [-> Hvar4].
                       destruct (app_eq_nil _ _ Hvar4) as [-> ->].
                       rewrite listVarInC_applySub_Var; try assumption.
                       now rewrite listVarInC_applySub_Var.
            ** destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
               exists ((Var v == {{t3 | t4}}) :: (applySubstitutionToC ((v,{{t3 | t4}}) :: nil) (c1'++c2'))).
               split.
               --- apply step1.
                   apply stepEq5; try now simpl.
                   +++ now apply eq_decompose.
                   +++ now right; left.
                   +++ now rewrite Heq in HnSF.
               --- rewrite Heq in Hsat.
                   destruct Hsat as [sigma [Hinter Hvar]].
                   exists sigma.
                   rewrite applySubToC_app in Hinter.
                   assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v == {{t3 | t4}}) :: c2'))).
                     now apply interpretC_app.
                   destruct Hand as [Hinter1 HinterS2].
                   destruct HinterS2 as [HinterE Hinter2].
                   rewrite applySubToC_app in Hvar.
                   rewrite listVarInC_app in Hvar.
                   unfold satisfies; simpl.
                   rewrite applySubToC_cons.
                   rewrite applySubToC_app.
                   split.
                   +++ split; try assumption.
                       apply interpretC_app.
                       now split; apply interpret_applySubC_Var.
                   +++ rewrite listVarInC_app.
                       destruct (app_eq_nil _ _ Hvar) as [? Hvar'].
                       simpl in Hvar'.
                       destruct (app_eq_nil _ _ Hvar') as [Hvar'' ?].
                       destruct (app_eq_nil _ _ Hvar') as [Hvar3 ?].
                       destruct (app_eq_nil _ _ Hvar3) as [-> Hvar4].
                       destruct (app_eq_nil _ _ Hvar4) as [-> ->].
                       rewrite listVarInC_applySub_Var; try assumption.
                       now rewrite listVarInC_applySub_Var.
    * intros s lt HnSF HIn.
      case (occurCheckList_dec v lt) as [Hocc | ?].
      -- destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
         rewrite Heq in Hsat.
         destruct Hsat as [sigma [Hinter Hvar]].
         rewrite applySubToC_app in Hinter.
         assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v == OTerm s lt) :: c2'))).
           now apply interpretC_app.
         destruct Hand as [Hinter1 HinterOT2].
         destruct HinterOT2 as [HinterOT Hinter2].
         case (axiomFS_3 _ _ _ HinterOT Hocc) as [Habs | [lt' [Habs HoccL]]];
           try discriminate.
         revert Habs.
         now case lt'.
      -- case (in_dec eq_primc_dec (IsSet (Var v)) c1) as [? | ?].
         ++ destruct Hsat as [sigma [Hinter Hvar]].
            assert (Hforall : forall pc, In pc (applySubstitutionToC sigma c1) -> interpretPC pc).
              now apply interpretC_iff.
            assert (HsetTerm : interpretPC (applySubstitutionToPC sigma (IsSet (Var v)))).
              apply Hforall.
              now apply in_map.
            assert (Habs : setTerm (applySubstitution sigma (OTerm s lt))).
              apply clos_rel_term_setTerm with (t1 := applySubstitution sigma (Var v)); try assumption.
              apply (Hforall (applySubstitutionToPC sigma (Var v == OTerm s lt))).
              now apply in_map.
            contradiction.
         ++ destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
            rewrite Heq in Hsat.
            destruct Hsat as [sigma [Hinter Hvar]].
            rewrite applySubToC_app in Hinter.
            assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v == OTerm s lt) :: c2'))).
              now apply interpretC_app.
            destruct Hand as [Hinter1 HinterOT2].
            destruct HinterOT2 as [HinterOT Hinter2].
            exists ((Var v == OTerm s lt) :: (applySubstitutionToC ((v,OTerm s lt) :: nil) (c1'++c2'))).
            split.
            ** apply step1.
               apply stepEq5; try now simpl.
               --- now apply eq_decompose.
               --- now right; left.
               --- now rewrite Heq in HnSF.
            ** exists sigma.
               rewrite applySubToC_app in Hvar.
               rewrite listVarInC_app in Hvar.
               unfold satisfies; simpl.
               rewrite applySubToC_cons.
               rewrite applySubToC_app.
               split.
               --- split; try assumption.
                   apply interpretC_app.
                   now split; apply interpret_applySubC_Var.
               --- rewrite listVarInC_app.
                   destruct (app_eq_nil _ _ Hvar) as [? Hvar'].
                   simpl in Hvar'.
                   destruct (app_eq_nil _ _ Hvar') as [Hvar'' ?].
                   destruct (app_eq_nil _ _ Hvar') as [Hvar3 ?].
                   destruct (app_eq_nil _ _ Hvar3) as [-> HvarOT].
                   rewrite listVarInC_applySub_Var; try assumption.
                   rewrite listVarInC_applySub_Var; try assumption.
                   now rewrite HvarOT.
    * intros HnSF HIn.
      unfold isInSFPC in HnSF; simpl in HnSF.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      exists ((Var v == EmptySet) :: (applySubstitutionToC ((v,EmptySet) :: nil) (c1'++c2'))).
      split.
      -- apply step1.
         apply stepEq5; try now simpl.
         ++ now apply eq_decompose.
         ++ now left.
         ++ now rewrite Heq in HnSF.
      -- rewrite Heq in Hsat.
         destruct Hsat as [sigma [Hinter Hvar]].
         exists sigma.
         rewrite applySubToC_app in Hinter.
         assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v == EmptySet) :: c2'))).
           now apply interpretC_app.
         destruct Hand as [Hinter1 HinterE2].
         destruct HinterE2 as [HinterE Hinter2].
         assert (Hsub_eq : applySubstitution sigma (Var v) = EmptySet).
           now apply clos_rel_term_EmptySet.
         rewrite applySubToC_app in Hvar.
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_cons.
         rewrite (applySubC_EmptySet _ _ _ Hsub_eq).
         rewrite applySubToC_app.
         split.
         ++ split; try assumption.
            now apply interpretC_app.
         ++ rewrite listVarInC_app.
            destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
            simpl in Hvar'.
            now destruct (app_eq_nil _ _ Hvar') as [-> ->].
  + intros t3 t4.
    case t2.
    * intros v _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      exists ((Var v == ({{t3 | t4}})) :: (c1' ++ c2')).
      split.
      -- apply step1.
         apply stepEq2; try now trivial.
         now apply eq_decompose.
      -- rewrite Heq in Hsat.
         destruct Hsat as [sigma [Hinter Hvar]].
         exists sigma.
         rewrite applySubToC_app in Hinter.
         rewrite applySubToC_app in Hvar.
         assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((({{t3 | t4}}) == Var v) :: c2'))).
           now apply interpretC_app.
         destruct Hand as [Hinter1 HinterS2].
         destruct HinterS2 as [HinterS Hinter2].
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_app.
         split.
         ++ split; try now apply interpretC_app.
            now apply clos_rel_term_sym.
         ++ rewrite listVarInC_app.
            destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
            simpl in Hvar'.
            destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
            destruct (app_eq_nil _ _ Hvar'') as [Hvar''' ->].
            now destruct (app_eq_nil _ _ Hvar''') as [-> ->].
    * intros t5 t6 _ HIn.
      case (dec_setTerm t4) as [HsetTerm4 | HnsetTerm4].
      -- case (dec_setTerm t6) as [HsetTerm6 | HnsetTerm6].
         ++ destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
            rewrite Heq in Hsat.
            destruct Hsat as [sigma [Hinter Hvar]].
            rewrite applySubToC_app in Hinter.
            rewrite applySubToC_app in Hvar.
            rewrite listVarInC_app in Hvar.
            assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((({{t3 | t4}}) == ({{t5 | t6}})) :: c2'))).
              now apply interpretC_app.
            destruct Hand as [Hinter1 HinterS2].
            destruct HinterS2 as [HinterS Hinter2].
            case (clos_rel_term_dec (applySubstitution sigma t3) (applySubstitution sigma t5)) as [? | Hneq_equiv].
            ** case (clos_rel_term_dec (applySubstitution sigma t4) (applySubstitution sigma t6)) as [? | ?].
               --- exists ((t3 == t5)::((t4 == t6):: (c1' ++ c2'))).
                   split.
                   +++ apply step1.
                       apply stepEq9_1; try now apply eq_decompose.
                       rewrite (tail_setTerm _ HsetTerm4).
                       now rewrite (tail_setTerm _ HsetTerm6).
                   +++ exists sigma.
                       split.
                       *** split; try assumption.
                           split; try assumption.
                           rewrite applySubToC_app.
                           now rewrite interpretC_app.
                       *** simpl; rewrite applySubToC_app.
                           rewrite listVarInC_app.
                           destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
                           simpl in Hvar'.
                           destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
                           destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
                           destruct (app_eq_nil _ _ Hvar34) as [-> ->].
                           now destruct (app_eq_nil _ _ Hvar56) as [-> ->].
               --- case (clos_rel_term_dec (applySubstitution sigma ({{t3 | t4}})) (applySubstitution sigma t6)) as [? | ?].
                   +++ exists ((t3 == t5)::((({{t3 | t4}}) == t6):: (c1' ++ c2'))).
                       split.
                       *** apply step1.
                           apply stepEq9_2; try now apply eq_decompose.
                           rewrite (tail_setTerm _ HsetTerm4).
                           now rewrite (tail_setTerm _ HsetTerm6).
                       *** exists sigma.
                           split.
                           ---- split; try assumption.
                                split; try assumption.
                                rewrite applySubToC_app.
                                now rewrite interpretC_app.
                           ---- simpl; rewrite applySubToC_app.
                                rewrite listVarInC_app.
                                destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
                                simpl in Hvar'.
                                destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
                                destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
                                destruct (app_eq_nil _ _ Hvar34) as [-> ->].
                                now destruct (app_eq_nil _ _ Hvar56) as [-> ->].
                   +++ case (clos_rel_term_dec (applySubstitution sigma t4) (applySubstitution sigma ({{t5 | t6}}))) as [? | ?].
                       *** exists ((t3 == t5)::((t4 == ({{t5 | t6}})):: (c1' ++ c2'))).
                           split.
                           ---- apply step1.
                                apply stepEq9_3; try now apply eq_decompose.
                                rewrite (tail_setTerm _ HsetTerm4).
                                now rewrite (tail_setTerm _ HsetTerm6).
                           ---- exists sigma.
                                split.
                                ++++ split; try assumption.
                                     split; try assumption.
                                     rewrite applySubToC_app.
                                     now rewrite interpretC_app.
                                ++++ simpl; rewrite applySubToC_app.
                                     rewrite listVarInC_app.
                                     destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
                                     simpl in Hvar'.
                                     destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
                                     destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
                                     destruct (app_eq_nil _ _ Hvar34) as [-> ->].
                                     now destruct (app_eq_nil _ _ Hvar56) as [-> ->].
                       *** assert (setTerm (applySubstitution sigma t4)).
                             now apply setTerm_applySub.
                           assert (setTerm (applySubstitution sigma t6)).
                             now apply setTerm_applySub.
                           absurd (applySubstitution sigma ({{t3 | t4}}) === applySubstitution sigma ({{t5 | t6}})); try assumption. 
                             now apply neg_inter_set.
            ** destruct (neg_inter_first_elem_exists (setTerm_applySub _ _ HsetTerm4) (setTerm_applySub _ _ HsetTerm6) Hneq_equiv HinterS) as [t [? ?]].
               pose (u := FreshVarFun c1).
               assert (Hfreshfstp1 : isFreshC u c1).
                 now apply FreshVarFun_isFresh.
               assert (HnegIn34 : ~ In u (listVarInT ({{t3 | t4}}))).
                 intro Habs.
                 absurd (occurCheckC u c1); try assumption.
                 apply in_occurCheckC with (pc := ({{t3 | t4}}) == ({{t5 | t6}}));
                   try now left; apply In_listVarInT_occurCheck with (t := {{t3 | t4}}).
                 rewrite Heq.
                 apply in_or_app; right.
                 now apply in_eq.
               assert (HnegIn56 : ~ In u (listVarInT ({{t5 | t6}}))).
                 intro Habs.
                 absurd (occurCheckC u c1); try assumption.
                 apply in_occurCheckC with (pc := ({{t3 | t4}}) == ({{t5 | t6}}));
                   try now right; apply In_listVarInT_occurCheck with (t := {{t5 | t6}}).
                 rewrite Heq.
                 apply in_or_app; right.
                 now apply in_eq.
               assert (HnegIn3 : ~ In u (listVarInT t3)).
                 intros Habs.
                 absurd (In u (listVarInT ({{t3 | t4}}))); try assumption.
                 now apply in_or_app; left.
               assert (HnegIn4 : ~ In u (listVarInT t4)).
                 intros Habs.
                 absurd (In u (listVarInT ({{t3 | t4}}))); try assumption.
                 now apply in_or_app; right.
               assert (HnegIn5 : ~ In u (listVarInT t5)).
                 intros Habs.
                 absurd (In u (listVarInT ({{t5 | t6}}))); try assumption.
                 now apply in_or_app; left.
               assert (HnegIn6 : ~ In u (listVarInT t6)).
                 intros Habs.
                 absurd (In u (listVarInT ({{t5 | t6}}))); try assumption.
                 now apply in_or_app; right.
               assert (HfreshL34 : isFreshL u (t4 :: t3 :: nil)).
                 intro Habs.
                 case Habs as [? | Habs'];
                   try now absurd (In u (listVarInT t4)); [assumption | apply occurCheck_In_listVarInT].
                 case Habs' as [? | ?]; try trivial.
                 now absurd (In u (listVarInT t3)); [assumption | apply occurCheck_In_listVarInT].
               assert (HfreshL56 : isFreshL u (t6 :: t5 :: nil)).
                 intro Habs.
                 case Habs as [? | Habs'];
                   try now absurd (In u (listVarInT t6)); [assumption | apply occurCheck_In_listVarInT].
                 case Habs' as [? | ?]; try trivial.
                 now absurd (In u (listVarInT t5)); [assumption | apply occurCheck_In_listVarInT].
               assert (HnegIn2 : ~ In u (listVarInC c2')).
                 intro HIn'.
                 absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                 apply incl_occurCheckC with (c1 := c2'); try now apply In_listVarInC_occurCheckC.
                 rewrite Heq.
                 apply incl_appr.
                 now apply incl_tl.
               assert (HnegIn12 : ~ In u (listVarInC (c1' ++ c2'))).
                 intro HIn'.
                 absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                 apply incl_occurCheckC with (c1 := c1' ++ c2'); try now apply In_listVarInC_occurCheckC.
                 rewrite Heq.
                 apply incl_app_app; try now apply incl_refl.
                 now apply incl_tl.
               assert (HnegIn1' : ~ In u (listVarInC c1')).
                 intro HIn'.
                 absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                 apply incl_occurCheckC with (c1 := c1'); try now apply In_listVarInC_occurCheckC.
                 rewrite Heq.
                 now apply incl_appl.
               exists ((t4 == (SetC t5 (Var u))) :: ((SetC t3 (Var u)) == t6):: (IsSet (Var u))::(c1'++c2')).
               split.
               --- apply step1.
                   apply stepEq9_4; try assumption.
                   +++ now apply eq_decompose.
                   +++ rewrite (tail_setTerm _ HsetTerm4).
                       now rewrite (tail_setTerm _ HsetTerm6).
               --- exists ((u, t) :: sigma).
                   split.
                   +++ split.
                       *** simpl; rewrite neq_listVarInT_applySub; try assumption.
                           rewrite neq_listVarInT_applySub; try assumption.
                           now case (eq_variable_dec u u).
                       *** split.
                           ---- simpl; rewrite neq_listVarInT_applySub; try assumption.
                                rewrite neq_listVarInT_applySub; try assumption.
                                apply clos_rel_term_sym.
                                now case (eq_variable_dec u u).
                           ---- split.
                                ++++ simpl; case (eq_variable_dec u u) as [_ | ?]; try contradiction.
                                     enough (setTerm  ({{applySubstitution sigma t5 | t}})).
                                       trivial.
                                     apply clos_rel_term_setTerm with (t1 := applySubstitution sigma t4); try assumption.
                                     now apply setTerm_applySub.
                                ++++ rewrite neq_listVarInC_applySub; try assumption.
                                     rewrite applySubToC_app.
                                     now apply interpretC_app.
                   +++ destruct (app_eq_nil _ _ Hvar) as [Hvar1 Hvar'].
                       simpl in Hvar'.
                       destruct (app_eq_nil _ _ Hvar') as [Hvar'' Hvar2].
                       destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
                       assert (Hnil : listVarInT t = nil).
                         apply incl_l_nil.
                         destruct (app_eq_nil _ _ Hvar34) as [_ <-].
                         apply incl_tran with (m := listVarInT ({{applySubstitution sigma t5 | t}}));
                           try now apply incl_appr.
                         apply listVarInT_clos_rel_term.
                         now apply clos_rel_term_sym.
                       simpl; rewrite applySubToC_app.
                       rewrite listVarInC_app.
                       rewrite neq_listVarInT_applySub; try assumption.
                       rewrite neq_listVarInT_applySub; try assumption.
                       rewrite neq_listVarInT_applySub; try assumption.
                       rewrite neq_listVarInT_applySub; try assumption.
                       rewrite neq_listVarInC_applySub; try assumption.
                       rewrite neq_listVarInC_applySub; try assumption.
                       case (eq_variable_dec u u) as [_ | ?]; try contradiction.
                       rewrite Hvar1.
                       rewrite Hvar2.
                       destruct (app_eq_nil _ _ Hvar34) as [-> ->].
                       destruct (app_eq_nil _ _ Hvar56) as [-> ->].
                       now rewrite Hnil.
         ++ assert (Hincl : incl (set_inferPC (({{t3 | t4}}) == ({{t5 | t6}}))) c1).
              now apply sort_complete_set_infer.
            destruct Hsat as [sigma [Hinter Hvar]].
            assert (HsetTerm6 : setTerm (applySubstitution sigma ({{t5 | t6}}))).
              simpl in HnsetTerm6.
              destruct (find_set_SetC_exist t5 _ HnsetTerm6) as [t [HIn' Hforall_eq]].
              enough (He : interpretPC (applySubstitutionToPC sigma (IsSet ({{t5 | t6}})))).
                now trivial.
              rewrite Hforall_eq.
              assert (HIn'' : In (IsSet t) c1).
                now apply Hincl; apply in_or_app; right.
              destruct (in_split _ _ HIn'') as [c1' [c2' Heq]].
              rewrite Heq in Hinter.
              rewrite applySubToC_app in Hinter.
              assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ (interpretC (applySubstitutionToC sigma ((IsSet t) :: c2')))).
                now apply interpretC_app.
              destruct Hand as [_ HinterS2].
              now destruct HinterS2 as [? _].
            destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
            assert (Hexists : exists v, tail t6 = Some (Var v)).
              now apply setTerm_negsetTerm_tail_exists_Var with (t1 := t5) (sigma := sigma).
            rewrite Heq in Hinter.
            rewrite Heq in Hvar.
            rewrite applySubToC_app in Hinter.
            rewrite applySubToC_app in Hvar.
            rewrite listVarInC_app in Hvar.
            assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((({{t3 | t4}}) == ({{t5 | t6}})) :: c2'))).
              now apply interpretC_app.
            destruct Hand as [Hinter1 HinterS2].
            destruct HinterS2 as [HinterS Hinter2].
            case (clos_rel_term_dec (applySubstitution sigma t3) (applySubstitution sigma t5)) as [? | Hneq_equiv].
            ** case (clos_rel_term_dec (applySubstitution sigma t4) (applySubstitution sigma t6)) as [? | ?].
               --- exists ((t3 == t5)::((t4 == t6):: (c1' ++ c2'))).
                   split.
                   +++ apply step1.
                       apply stepEq9_1; try now apply eq_decompose.
                       rewrite (tail_setTerm _ HsetTerm4).
                       now destruct Hexists as [? ->].
                   +++ exists sigma.
                       split.
                       *** split; try assumption.
                           split; try assumption.
                           rewrite applySubToC_app.
                           now rewrite interpretC_app.
                       *** simpl; rewrite applySubToC_app.
                           rewrite listVarInC_app.
                           destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
                           simpl in Hvar'.
                           destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
                           destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
                           destruct (app_eq_nil _ _ Hvar34) as [-> ->].
                           now destruct (app_eq_nil _ _ Hvar56) as [-> ->].
               --- case (clos_rel_term_dec (applySubstitution sigma ({{t3 | t4}})) (applySubstitution sigma t6)) as [? | ?].
                   +++ exists ((t3 == t5)::((({{t3 | t4}}) == t6):: (c1' ++ c2'))).
                       split.
                       *** apply step1.
                           apply stepEq9_2; try now apply eq_decompose.
                           rewrite (tail_setTerm _ HsetTerm4).
                           now destruct Hexists as [? ->].
                       *** exists sigma.
                           split.
                           ---- split; try assumption.
                                split; try assumption.
                                rewrite applySubToC_app.
                                now rewrite interpretC_app.
                           ---- simpl; rewrite applySubToC_app.
                                rewrite listVarInC_app.
                                destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
                                simpl in Hvar'.
                                destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
                                destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
                                destruct (app_eq_nil _ _ Hvar34) as [-> ->].
                                now destruct (app_eq_nil _ _ Hvar56) as [-> ->].
                   +++ case (clos_rel_term_dec (applySubstitution sigma t4) (applySubstitution sigma ({{t5 | t6}}))) as [? | ?].
                       *** exists ((t3 == t5)::((t4 == ({{t5 | t6}})):: (c1' ++ c2'))).
                           split.
                           ---- apply step1.
                                apply stepEq9_3; try now apply eq_decompose.
                                rewrite (tail_setTerm _ HsetTerm4).
                                now destruct Hexists as [? ->].
                           ---- exists sigma.
                                split.
                                ++++ split; try assumption.
                                     split; try assumption.
                                     rewrite applySubToC_app.
                                     now rewrite interpretC_app.
                                ++++ simpl; rewrite applySubToC_app.
                                     rewrite listVarInC_app.
                                     destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
                                     simpl in Hvar'.
                                     destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
                                     destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
                                     destruct (app_eq_nil _ _ Hvar34) as [-> ->].
                                     now destruct (app_eq_nil _ _ Hvar56) as [-> ->].
                       *** assert (setTerm (applySubstitution sigma t4)).
                             now apply setTerm_applySub.
                           absurd (applySubstitution sigma ({{t3 | t4}}) === applySubstitution sigma ({{t5 | t6}})); try assumption. 
                             now apply neg_inter_set.
            ** assert (HsetTerm6' : setTerm (applySubstitution sigma t6)).
                 trivial.
               destruct (neg_inter_first_elem_exists (setTerm_applySub _ _ HsetTerm4) HsetTerm6' Hneq_equiv HinterS) as [t [? ?]].
               pose (u := FreshVarFun c1).
               assert (Hfreshfstp1 : isFreshC u c1).
                 now apply FreshVarFun_isFresh.
               assert (HnegIn34 : ~ In u (listVarInT ({{t3 | t4}}))).
                 intro Habs.
                 absurd (occurCheckC u c1); try assumption.
                 apply in_occurCheckC with (pc := ({{t3 | t4}}) == ({{t5 | t6}}));
                   try now left; apply In_listVarInT_occurCheck with (t := {{t3 | t4}}).
                 rewrite Heq.
                 apply in_or_app; right.
                 now apply in_eq.
               assert (HnegIn56 : ~ In u (listVarInT ({{t5 | t6}}))).
                 intro Habs.
                 absurd (occurCheckC u c1); try assumption.
                 apply in_occurCheckC with (pc := ({{t3 | t4}}) == ({{t5 | t6}}));
                   try now right; apply In_listVarInT_occurCheck with (t := {{t5 | t6}}).
                 rewrite Heq.
                 apply in_or_app; right.
                 now apply in_eq.
               assert (HnegIn3 : ~ In u (listVarInT t3)).
                 intros Habs.
                 absurd (In u (listVarInT ({{t3 | t4}}))); try assumption.
                 now apply in_or_app; left.
               assert (HnegIn4 : ~ In u (listVarInT t4)).
                 intros Habs.
                 absurd (In u (listVarInT ({{t3 | t4}}))); try assumption.
                 now apply in_or_app; right.
               assert (HnegIn5 : ~ In u (listVarInT t5)).
                 intros Habs.
                 absurd (In u (listVarInT ({{t5 | t6}}))); try assumption.
                 now apply in_or_app; left.
               assert (HnegIn6 : ~ In u (listVarInT t6)).
                 intros Habs.
                 absurd (In u (listVarInT ({{t5 | t6}}))); try assumption.
                 now apply in_or_app; right.
               assert (HfreshL34 : isFreshL u (t4 :: t3 :: nil)).
                 intro Habs.
                 case Habs as [? | Habs'];
                   try now absurd (In u (listVarInT t4)); [assumption | apply occurCheck_In_listVarInT].
                 case Habs' as [? | ?]; try trivial.
                 now absurd (In u (listVarInT t3)); [assumption | apply occurCheck_In_listVarInT].
               assert (HfreshL56 : isFreshL u (t6 :: t5 :: nil)).
                 intro Habs.
                 case Habs as [? | Habs'];
                   try now absurd (In u (listVarInT t6)); [assumption | apply occurCheck_In_listVarInT].
                 case Habs' as [? | ?]; try trivial.
                 now absurd (In u (listVarInT t5)); [assumption | apply occurCheck_In_listVarInT].
               assert (HnegIn2 : ~ In u (listVarInC c2')).
                 intro HIn'.
                 absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                 apply incl_occurCheckC with (c1 := c2'); try now apply In_listVarInC_occurCheckC.
                 rewrite Heq.
                 apply incl_appr.
                 now apply incl_tl.
               assert (HnegIn1' : ~ In u (listVarInC c1')).
                 intro HIn'.
                 absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                 apply incl_occurCheckC with (c1 := c1'); try now apply In_listVarInC_occurCheckC.
                 rewrite Heq.
                 now apply incl_appl.
               assert (HnegIn12 : ~ In u (listVarInC (c1' ++ c2'))).
                 intro HIn'.
                 absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                 apply incl_occurCheckC with (c1 := c1' ++ c2'); try now apply In_listVarInC_occurCheckC.
                 rewrite Heq.
                 apply incl_app_app; try now apply incl_refl.
                 now apply incl_tl.
               exists ((t4 == (SetC t5 (Var u))) :: ((SetC t3 (Var u)) == t6):: (IsSet (Var u))::(c1'++c2')).
               split.
               --- apply step1.
                   apply stepEq9_4; try assumption.
                   +++ now apply eq_decompose.
                   +++ rewrite (tail_setTerm _ HsetTerm4).
                       now destruct Hexists as [? ->].
               --- exists ((u, t) :: sigma).
                   split.
                   +++ split.
                       *** simpl; rewrite neq_listVarInT_applySub; try assumption.
                           rewrite neq_listVarInT_applySub; try assumption.
                           now case (eq_variable_dec u u).
                       *** split.
                           ---- simpl; rewrite neq_listVarInT_applySub; try assumption.
                                rewrite neq_listVarInT_applySub; try assumption.
                                apply clos_rel_term_sym.
                                now case (eq_variable_dec u u).
                           ---- split.
                                ++++ simpl; case (eq_variable_dec u u) as [_ | ?]; try contradiction.
                                     enough (setTerm  ({{applySubstitution sigma t5 | t}})).
                                       trivial.
                                     apply clos_rel_term_setTerm with (t1 := applySubstitution sigma t4); try assumption.
                                     now apply setTerm_applySub.
                                ++++ rewrite neq_listVarInC_applySub; try assumption.
                                     rewrite applySubToC_app.
                                     now apply interpretC_app.
                   +++ destruct (app_eq_nil _ _ Hvar) as [Hvar1 Hvar'].
                       simpl in Hvar'.
                       destruct (app_eq_nil _ _ Hvar') as [Hvar'' Hvar2].
                       destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
                       assert (Hnil : listVarInT t = nil).
                         apply incl_l_nil.
                         destruct (app_eq_nil _ _ Hvar34) as [_ <-].
                         apply incl_tran with (m := listVarInT ({{applySubstitution sigma t5 | t}}));
                           try now apply incl_appr.
                         apply listVarInT_clos_rel_term.
                         now apply clos_rel_term_sym.
                       simpl; rewrite applySubToC_app.
                       rewrite listVarInC_app.
                       rewrite neq_listVarInT_applySub; try assumption.
                       rewrite neq_listVarInT_applySub; try assumption.
                       rewrite neq_listVarInT_applySub; try assumption.
                       rewrite neq_listVarInT_applySub; try assumption.
                       rewrite neq_listVarInC_applySub; try assumption.
                       rewrite neq_listVarInC_applySub; try assumption.
                       case (eq_variable_dec u u) as [_ | ?]; try contradiction.
                       rewrite Hvar1.
                       rewrite Hvar2.
                       destruct (app_eq_nil _ _ Hvar34) as [-> ->].
                       destruct (app_eq_nil _ _ Hvar56) as [-> ->].
                       now rewrite Hnil.
      -- case (dec_setTerm t6) as [HsetTerm6 | HnsetTerm6].
         ++ assert (Hincl : incl (set_inferPC (({{t3 | t4}}) == ({{t5 | t6}}))) c1).
              now apply sort_complete_set_infer.
            destruct Hsat as [sigma [Hinter Hvar]].
            assert (HsetTerm4 : setTerm (applySubstitution sigma ({{t3 | t4}}))).
              simpl in HnsetTerm4.
              destruct (find_set_SetC_exist t3 _ HnsetTerm4) as [t [HIn' Hforall_eq]].
              enough (He : interpretPC (applySubstitutionToPC sigma (IsSet ({{t3 | t4}})))).
                now trivial.
              rewrite Hforall_eq.
              assert (HIn'' : In (IsSet t) c1).
                now apply Hincl; apply in_or_app; left.
              destruct (in_split _ _ HIn'') as [c1' [c2' Heq]].
              rewrite Heq in Hinter.
              rewrite applySubToC_app in Hinter.
              assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ (interpretC (applySubstitutionToC sigma ((IsSet t) :: c2')))).
                now apply interpretC_app.
              destruct Hand as [_ HinterS2].
              now destruct HinterS2 as [? _].
            destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
            assert (Hexists : exists v, tail t4 = Some (Var v)).
              now apply setTerm_negsetTerm_tail_exists_Var with (t1 := t3) (sigma := sigma).
            rewrite Heq in Hinter.
            rewrite Heq in Hvar.
            rewrite applySubToC_app in Hinter.
            rewrite applySubToC_app in Hvar.
            rewrite listVarInC_app in Hvar.
            assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((({{t3 | t4}}) == ({{t5 | t6}})) :: c2'))).
              now apply interpretC_app.
            destruct Hand as [Hinter1 HinterS2].
            destruct HinterS2 as [HinterS Hinter2].
            case (clos_rel_term_dec (applySubstitution sigma t3) (applySubstitution sigma t5)) as [? | Hneq_equiv].
            ** case (clos_rel_term_dec (applySubstitution sigma t4) (applySubstitution sigma t6)) as [? | ?].
               --- exists ((t3 == t5)::((t4 == t6):: (c1' ++ c2'))).
                   split.
                   +++ apply step1.
                       apply stepEq9_1; try now apply eq_decompose.
                       rewrite (tail_setTerm _ HsetTerm6).
                       now destruct Hexists as [? ->].
                   +++ exists sigma.
                       split.
                       *** split; try assumption.
                           split; try assumption.
                           rewrite applySubToC_app.
                           now rewrite interpretC_app.
                       *** simpl; rewrite applySubToC_app.
                           rewrite listVarInC_app.
                           destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
                           simpl in Hvar'.
                           destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
                           destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
                           destruct (app_eq_nil _ _ Hvar34) as [-> ->].
                           now destruct (app_eq_nil _ _ Hvar56) as [-> ->].
               --- case (clos_rel_term_dec (applySubstitution sigma ({{t3 | t4}})) (applySubstitution sigma t6)) as [? | ?].
                   +++ exists ((t3 == t5)::((({{t3 | t4}}) == t6):: (c1' ++ c2'))).
                       split.
                       *** apply step1.
                           apply stepEq9_2; try now apply eq_decompose.
                           rewrite (tail_setTerm _ HsetTerm6).
                           now destruct Hexists as [? ->].
                       *** exists sigma.
                           split.
                           ---- split; try assumption.
                                split; try assumption.
                                rewrite applySubToC_app.
                                now rewrite interpretC_app.
                           ---- simpl; rewrite applySubToC_app.
                                rewrite listVarInC_app.
                                destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
                                simpl in Hvar'.
                                destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
                                destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
                                destruct (app_eq_nil _ _ Hvar34) as [-> ->].
                                now destruct (app_eq_nil _ _ Hvar56) as [-> ->].
                   +++ case (clos_rel_term_dec (applySubstitution sigma t4) (applySubstitution sigma ({{t5 | t6}}))) as [? | ?].
                       *** exists ((t3 == t5)::((t4 == ({{t5 | t6}})):: (c1' ++ c2'))).
                           split.
                           ---- apply step1.
                                apply stepEq9_3; try now apply eq_decompose.
                                rewrite (tail_setTerm _ HsetTerm6).
                                now destruct Hexists as [? ->].
                           ---- exists sigma.
                                split.
                                ++++ split; try assumption.
                                     split; try assumption.
                                     rewrite applySubToC_app.
                                     now rewrite interpretC_app.
                                ++++ simpl; rewrite applySubToC_app.
                                     rewrite listVarInC_app.
                                     destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
                                     simpl in Hvar'.
                                     destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
                                     destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
                                     destruct (app_eq_nil _ _ Hvar34) as [-> ->].
                                     now destruct (app_eq_nil _ _ Hvar56) as [-> ->].
                       *** assert (setTerm (applySubstitution sigma t6)).
                             now apply setTerm_applySub.
                           absurd (applySubstitution sigma ({{t3 | t4}}) === applySubstitution sigma ({{t5 | t6}})); try assumption.
                             now apply neg_inter_set.
            ** assert (HsetTerm4' : setTerm (applySubstitution sigma t4)).
                 trivial.
               destruct (neg_inter_first_elem_exists HsetTerm4' (setTerm_applySub _ _ HsetTerm6) Hneq_equiv HinterS) as [t [? ?]].
               pose (u := FreshVarFun c1).
               assert (Hfreshfstp1 : isFreshC u c1).
                 now apply FreshVarFun_isFresh.
               assert (HnegIn34 : ~ In u (listVarInT ({{t3 | t4}}))).
                 intro Habs.
                 absurd (occurCheckC u c1); try assumption.
                 apply in_occurCheckC with (pc := ({{t3 | t4}}) == ({{t5 | t6}}));
                   try now left; apply In_listVarInT_occurCheck with (t := {{t3 | t4}}).
                 rewrite Heq.
                 apply in_or_app; right.
                 now apply in_eq.
               assert (HnegIn56 : ~ In u (listVarInT ({{t5 | t6}}))).
                 intro Habs.
                 absurd (occurCheckC u c1); try assumption.
                 apply in_occurCheckC with (pc := ({{t3 | t4}}) == ({{t5 | t6}}));
                   try now right; apply In_listVarInT_occurCheck with (t := {{t5 | t6}}).
                 rewrite Heq.
                 apply in_or_app; right.
                 now apply in_eq.
               assert (HnegIn3 : ~ In u (listVarInT t3)).
                 intros Habs.
                 absurd (In u (listVarInT ({{t3 | t4}}))); try assumption.
                 now apply in_or_app; left.
               assert (HnegIn4 : ~ In u (listVarInT t4)).
                 intros Habs.
                 absurd (In u (listVarInT ({{t3 | t4}}))); try assumption.
                 now apply in_or_app; right.
               assert (HnegIn5 : ~ In u (listVarInT t5)).
                 intros Habs.
                 absurd (In u (listVarInT ({{t5 | t6}}))); try assumption.
                 now apply in_or_app; left.
               assert (HnegIn6 : ~ In u (listVarInT t6)).
                 intros Habs.
                 absurd (In u (listVarInT ({{t5 | t6}}))); try assumption.
                 now apply in_or_app; right.
               assert (HfreshL34 : isFreshL u (t4 :: t3 :: nil)).
                 intro Habs.
                 case Habs as [? | Habs'];
                   try now absurd (In u (listVarInT t4)); [assumption | apply occurCheck_In_listVarInT].
                 case Habs' as [? | ?]; try trivial.
                 now absurd (In u (listVarInT t3)); [assumption | apply occurCheck_In_listVarInT].
               assert (HfreshL56 : isFreshL u (t6 :: t5 :: nil)).
                 intro Habs.
                 case Habs as [? | Habs'];
                   try now absurd (In u (listVarInT t6)); [assumption | apply occurCheck_In_listVarInT].
                 case Habs' as [? | ?]; try trivial.
                 now absurd (In u (listVarInT t5)); [assumption | apply occurCheck_In_listVarInT].
               assert (HnegIn1 : ~ In u (listVarInC c1')).
                 intro HIn'.
                 absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                 apply incl_occurCheckC with (c1 := c1'); try now apply In_listVarInC_occurCheckC.
                 rewrite Heq.
                 now apply incl_appl.
               assert (HnegIn2 : ~ In u (listVarInC c2')).
                 intro HIn'.
                 absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                 apply incl_occurCheckC with (c1 := c2'); try now apply In_listVarInC_occurCheckC.
                 rewrite Heq.
                 apply incl_appr.
                 now apply incl_tl.
               assert (HnegIn12 : ~ In u (listVarInC (c1' ++ c2'))).
                 intro HIn'.
                 absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                 apply incl_occurCheckC with (c1 := c1' ++ c2'); try now apply In_listVarInC_occurCheckC.
                 rewrite Heq.
                 apply incl_app_app; try now apply incl_refl.
                 now apply incl_tl.
               exists (((t4 == (SetC t5 (Var u))) :: ((SetC t3 (Var u)) == t6):: (IsSet (Var u))::(c1'++c2'))).
               split.
               --- apply step1.
                   apply stepEq9_4; try assumption.
                   +++ now apply eq_decompose.
                   +++ rewrite (tail_setTerm _ HsetTerm6).
                       now destruct Hexists as [? ->].
               --- exists ((u, t) :: sigma).
                   split.
                   +++ split.
                       *** simpl; rewrite neq_listVarInT_applySub; try assumption.
                           rewrite neq_listVarInT_applySub; try assumption.
                           now case (eq_variable_dec u u).
                       *** split.
                           ---- simpl; rewrite neq_listVarInT_applySub; try assumption.
                                rewrite neq_listVarInT_applySub; try assumption.
                                apply clos_rel_term_sym.
                                now case (eq_variable_dec u u).
                           ---- split.
                                ++++ simpl; case (eq_variable_dec u u) as [_ | ?]; try contradiction.
                                     enough (setTerm  ({{applySubstitution sigma t5 | t}})).
                                       trivial.
                                     now apply clos_rel_term_setTerm with (t1 := applySubstitution sigma t4).
                                ++++ rewrite neq_listVarInC_applySub; try assumption.
                                     rewrite applySubToC_app.
                                     now apply interpretC_app.
                   +++ destruct (app_eq_nil _ _ Hvar) as [Hvar1 Hvar'].
                       simpl in Hvar'.
                       destruct (app_eq_nil _ _ Hvar') as [Hvar'' Hvar2].
                       destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
                       assert (Hnil : listVarInT t = nil).
                         apply incl_l_nil.
                         destruct (app_eq_nil _ _ Hvar34) as [_ <-].
                         apply incl_tran with (m := listVarInT ({{applySubstitution sigma t5 | t}}));
                           try now apply incl_appr.
                         apply listVarInT_clos_rel_term.
                         now apply clos_rel_term_sym.
                       simpl; rewrite applySubToC_app.
                       rewrite listVarInC_app.
                       rewrite neq_listVarInT_applySub; try assumption.
                       rewrite neq_listVarInT_applySub; try assumption.
                       rewrite neq_listVarInT_applySub; try assumption.
                       rewrite neq_listVarInT_applySub; try assumption.
                       rewrite neq_listVarInC_applySub; try assumption.
                       rewrite neq_listVarInC_applySub; try assumption.
                       case (eq_variable_dec u u) as [_ | ?]; try contradiction.
                       rewrite Hvar1.
                       rewrite Hvar2.
                       destruct (app_eq_nil _ _ Hvar34) as [-> ->].
                       destruct (app_eq_nil _ _ Hvar56) as [-> ->].
                       now rewrite Hnil.
         ++ destruct Hsat as [sigma [Hinter Hvar]].
            assert (Hincl : incl (set_inferPC (({{t3 | t4}}) == ({{t5 | t6}}))) c1).
              now apply sort_complete_set_infer.
            assert (HsetTerm4 : setTerm (applySubstitution sigma ({{t3 | t4}}))).
              simpl in HnsetTerm4.
              destruct (find_set_SetC_exist t3 _ HnsetTerm4) as [t [HIn' Hforall_eq]].
              enough (He : interpretPC (applySubstitutionToPC sigma (IsSet ({{t3 | t4}})))).
                now trivial.
              rewrite Hforall_eq.
              assert (HIn'' : In (IsSet t) c1).
                now apply Hincl; apply in_or_app; left.
              destruct (in_split _ _ HIn'') as [c1' [c2' Heq]].
              rewrite Heq in Hinter.
              rewrite applySubToC_app in Hinter.
              assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ (interpretC (applySubstitutionToC sigma ((IsSet t) :: c2')))).
                now apply interpretC_app.
              destruct Hand as [_ HinterS2].
              now destruct HinterS2 as [? _].
            assert (HsetTerm6 : setTerm (applySubstitution sigma ({{t5 | t6}}))).
              simpl in HnsetTerm6.
              destruct (find_set_SetC_exist t5 _ HnsetTerm6) as [t [HIn' Hforall_eq]].
              enough (He : interpretPC (applySubstitutionToPC sigma (IsSet ({{t5 | t6}})))).
                now trivial.
              rewrite Hforall_eq.
              assert (HIn'' : In (IsSet t) c1).
                now apply Hincl; apply in_or_app; right.
              destruct (in_split _ _ HIn'') as [c1' [c2' Heq]].
              rewrite Heq in Hinter.
              rewrite applySubToC_app in Hinter.
              assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ (interpretC (applySubstitutionToC sigma ((IsSet t) :: c2')))).
                now apply interpretC_app.
              destruct Hand as [_ HinterS2].
              now destruct HinterS2 as [? _].
            destruct (setTerm_negsetTerm_tail_exists_Var _ _ _ HsetTerm4) as [v Heqt4]; try assumption.
            destruct (setTerm_negsetTerm_tail_exists_Var _ _ _ HsetTerm6) as [v' Heqt6]; try assumption.
            case (eq_variable_dec v v') as [Heqv | Hneqv].
            ** destruct (tail_Var_exists t3 _ Heqt4) as [lt [Hneq_nil Heq34]].
               destruct (tail_Var_exists t5 _ Heqt6) as [lt' [Hneq_nil' Heq56]].
               assert (Hlt : 0 < length lt).
                 apply Lt.neq_0_lt.
                 intro Habs.
                 absurd (lt = nil); try assumption.
                 now apply length_zero_iff_nil.
               assert (Hnth0 : nth_error lt 0 = Some (nth 0 lt EmptySet)).
                 now apply nth_error_nth'.
               rewrite Heq34 in HIn.
               rewrite Heq56 in HIn.
               rewrite <- Heqv in HIn.
               destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
               rewrite Heq in Hinter.
               rewrite Heq in Hvar.
               rewrite applySubToC_app in Hinter.
               rewrite applySubToC_app in Hvar.
               rewrite listVarInC_app in Hvar.
               destruct (app_eq_nil _ _ Hvar) as [Hvarc1 Hvar'].
               simpl in Hvar'.
               destruct (app_eq_nil _ _ Hvar') as [Hvar'' Hvarc2].
               destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
               assert (Hneq_nil_map : map (applySubstitution sigma) lt <> nil).
                 intro Habs.
                 absurd (lt = nil); try assumption.
                 now apply map_eq_nil with (f := applySubstitution sigma).
               assert (Hvarv : listVarInT ((applySubstitution sigma) (Var v)) = nil).
                 apply incl_l_nil.
                 rewrite <- Hvar34.
                 rewrite applySub_listSetC.
                 now apply listVarInT_listSetC.
               assert (Hvarlt : listVarInListT (map (applySubstitution sigma) lt) = nil).
                 apply incl_l_nil.
                 rewrite <- Hvar34.
                 rewrite applySub_listSetC.
                 now apply listVarInListT_listSetC.
               assert (Hvar0lt : listVarInT (applySubstitution sigma (nth 0 lt EmptySet)) = nil).
                 apply incl_l_nil.
                 rewrite <- Hvarlt.
                 apply incl_listVarInT_listVarInListT.
                 apply in_map.
                 now apply nth_In.
               assert (Hvard0lt : listVarInT (applySubstitution sigma (listSetC (deleteElmntj 0 lt) (Var v))) = nil).
                 apply incl_l_nil.
                 apply incl_tran with (m := listVarInListT (map (applySubstitution sigma) (deleteElmntj 0 lt)) ++ listVarInT (applySubstitution sigma (Var v)));
                   try now rewrite applySub_listSetC; apply listSetC_listVarInListT.
                 rewrite Hvarv.
                 rewrite app_nil_r.
                 rewrite <- Hvarlt.
                 apply incl_listVarInListT.
                 apply incl_map.
                 now apply deleteElmntj_incl.
               assert (Hneq_nil_map' : map (applySubstitution sigma) lt' <> nil).
                 intro Habs.
                 absurd (lt' = nil); try assumption.
                 now apply map_eq_nil with (f := applySubstitution sigma).
               assert (Hvarlt' : listVarInListT (map (applySubstitution sigma) lt') = nil).
                 apply incl_l_nil.
                 rewrite <- Hvar56.
                 rewrite applySub_listSetC.
                 now apply listVarInListT_listSetC.
               assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma (((listSetC lt (Var v)) == (listSetC lt' (Var v))) :: c2'))).
                 now apply interpretC_app.
               destruct Hand as [Hinter1 HinterS2].
               destruct HinterS2 as [HinterS Hinter2].
               case (dec_incl_interpret ((applySubstitution sigma (nth 0 lt EmptySet)) :: nil) (map (applySubstitution sigma) lt')) as [Hincl_i | ?].
               --- assert (Hexists : exists t, applySubstitution sigma t === applySubstitution sigma (nth 0 lt EmptySet) /\ In t lt').
                     assert (Hexists' : exists t', t' === applySubstitution sigma (nth 0 lt EmptySet) /\ In t' (map (applySubstitution sigma) lt')).
                       apply Hincl_i.
                       now apply in_eq.
                     destruct Hexists' as [tj' [? HInj']].
                     assert (Hexists'': exists t'', applySubstitution sigma t'' = tj' /\ In t'' lt').
                       now apply in_map_iff.
                     destruct Hexists'' as [tj [Htj HInj]].
                     exists tj.
                     split; try assumption.
                     now rewrite Htj.
                   destruct Hexists as [tj [Htj HInj]].
                   destruct (In_nth_error _ _ HInj) as [j Htjeq].
                   assert (Hvarjlt' : listVarInT (applySubstitution sigma tj) = nil).
                     apply incl_l_nil.
                     rewrite <- Hvarlt'.
                     apply incl_listVarInT_listVarInListT.
                     now apply in_map.
                   assert (Hvardjlt' : listVarInT (applySubstitution sigma (listSetC (deleteElmntj j lt') (Var v))) = nil).
                     apply incl_l_nil.
                     apply incl_tran with (m := listVarInListT (map (applySubstitution sigma) (deleteElmntj j lt')) ++ listVarInT (applySubstitution sigma (Var v)));
                       try now rewrite applySub_listSetC; apply listSetC_listVarInListT.
                     rewrite Hvarv.
                     rewrite app_nil_r.
                     rewrite <- Hvarlt'.
                     apply incl_listVarInListT.
                     apply incl_map.
                     now apply deleteElmntj_incl.
                   case (list_eq_dec eq_term_dec (deleteElmntj 0 lt) nil) as [Hd0_nil | Hneqd0_nil].
                   +++ case (list_eq_dec eq_term_dec (deleteElmntj j lt') nil) as [Hdj_nil | Hneqdj_nil].
                       *** case (clos_rel_term_dec (applySubstitution sigma (Var v)) (applySubstitution sigma (Var v))) as [? | ?].
                           ---- exists (c1'++c2' ++ ((Eq (nth 0 lt EmptySet) tj) ::
                                       (Eq (listSetC (deleteElmntj 0 lt) (Var v)) (listSetC (deleteElmntj j lt') (Var v))) :: nil)).
                                split.
                                ++++ apply step1.
                                     apply stepEq10_1; try assumption.
                                     now apply eq_decompose.
                                ++++ exists sigma.
                                     split.
                                     **** simpl; do 2 rewrite applySubToC_app.
                                          rewrite interpretC_app.
                                          split; try assumption.
                                          rewrite interpretC_app.
                                          split; try assumption.
                                          split; try now apply clos_rel_term_sym.
                                          rewrite Hd0_nil.
                                          rewrite Hdj_nil.
                                          now split.
                                     **** simpl; do 2 rewrite applySubToC_app.
                                          do 2 rewrite listVarInC_app.
                                          rewrite Hvarc1.
                                          rewrite Hvarc2.
                                          simpl; rewrite Hvar0lt.
                                          rewrite Hvarjlt'.
                                          rewrite Hd0_nil.
                                          rewrite Hdj_nil.
                                          assert (Ht : listSetC nil (Var v) = Var v).
                                            trivial.
                                          rewrite Ht.
                                          now rewrite Hvarv.
                           ---- case (clos_rel_term_dec (applySubstitution sigma (listSetC lt (Var v))) (applySubstitution sigma (Var v))) as [? | ?].
                                ++++ exists (c1'++c2' ++ ((Eq (nth 0 lt EmptySet) tj) ::
                                              (Eq (listSetC lt (Var v)) (listSetC (deleteElmntj j lt') (Var v))) :: nil)).
                                     split.
                                     **** apply step1.
                                          apply stepEq10_2; try assumption.
                                          now apply eq_decompose.
                                     **** exists sigma.
                                          split.
                                          ----- simpl; do 2 rewrite applySubToC_app.
                                                rewrite interpretC_app.
                                                split; try assumption.
                                                rewrite interpretC_app.
                                                split; try assumption.
                                                split; try now apply clos_rel_term_sym.
                                                now rewrite Hdj_nil.
                                          ----- simpl; do 2 rewrite applySubToC_app.
                                                do 2 rewrite listVarInC_app.
                                                rewrite Hvarc1.
                                                rewrite Hvarc2.
                                                simpl; rewrite Hvar0lt.
                                                rewrite Hvarjlt'.
                                                rewrite Hvar34.
                                                rewrite Hdj_nil.
                                                assert (Ht : listSetC nil (Var v) = Var v).
                                                  trivial.
                                                rewrite Ht.
                                                now rewrite Hvarv.
                                ++++ case (clos_rel_term_dec (applySubstitution sigma (Var v)) (applySubstitution sigma (listSetC lt' (Var v)))) as [? | ?].
                                     **** exists (c1'++c2' ++ ((Eq (nth 0 lt EmptySet) tj) :: (Eq (listSetC (deleteElmntj 0 lt) (Var v)) (listSetC lt' (Var v))) :: nil)).
                                          split.
                                          ----- apply step1.
                                                apply stepEq10_3 with (j := j); try assumption.
                                                now apply eq_decompose.
                                          ----- exists sigma.
                                                split.
                                                +++++ simpl; do 2 rewrite applySubToC_app.
                                                      rewrite interpretC_app.
                                                      split; try assumption.
                                                      rewrite interpretC_app.
                                                      split; try assumption.
                                                      split; try now apply clos_rel_term_sym.
                                                      split; try now trivial.
                                                      now rewrite Hd0_nil.
                                                +++++ simpl; do 2 rewrite applySubToC_app.
                                                      do 2 rewrite listVarInC_app.
                                                      rewrite Hvarc1.
                                                      rewrite Hvarc2.
                                                      simpl; rewrite Hvar0lt.
                                                      rewrite Hvarjlt'.
                                                      rewrite Hvar56.
                                                      rewrite Hd0_nil.
                                                      assert (Ht : listSetC nil (Var v) = Var v).
                                                        trivial.
                                                      rewrite Ht.
                                                      now rewrite Hvarv.
                                     **** assert (Hequiv34 : applySubstitution sigma ({{t3 | t4}}) === applySubstitution sigma ({{nth 0 lt EmptySet | Var v}})).
                                            rewrite Heq34.
                                            rewrite (deleteElmntj_eq_nil _ _ Hnth0 Hd0_nil).
                                            now apply clos_rel_term_refl.
                                          assert (Hequiv56 : applySubstitution sigma ({{t5 | t6}}) === applySubstitution sigma ({{tj | (Var v)}})).
                                            rewrite Heq56.
                                            rewrite (deleteElmntj_eq_nil _ _ Htjeq Hdj_nil).
                                            rewrite Heqv.
                                            now apply clos_rel_term_refl.
                                          absurd (applySubstitution sigma ({{nth 0 lt EmptySet | Var v}}) === applySubstitution sigma ({{tj | Var v}})).
                                          ----- simpl; apply neg_inter_set; try assumption.
                                                +++++ now apply (clos_rel_term_setTerm Hequiv34).
                                                +++++ now apply (clos_rel_term_setTerm Hequiv56).
                                                +++++ now apply clos_rel_term_sym.
                                                +++++ intro Habs.
                                                      absurd (applySubstitution sigma (listSetC lt (Var v)) === applySubstitution sigma (Var v)); try assumption.
                                                      apply t_trans with (y := ({{applySubstitution sigma (nth 0 lt EmptySet) | applySubstitution sigma (Var v)}})); try assumption.
                                                      now rewrite <- Heq34.
                                                +++++ intro Habs.
                                                      absurd (applySubstitution sigma (Var v) === applySubstitution sigma (listSetC lt' (Var v))); try assumption.
                                                      apply t_trans with (y := applySubstitution sigma ({{tj | Var v}})); try assumption.
                                                      rewrite <- Heqv in Heq56.
                                                      rewrite <- Heq56.
                                                      now apply clos_rel_term_sym.
                                          ----- apply t_trans with (y := applySubstitution sigma ({{t3 | t4}})); try now apply clos_rel_term_sym.
                                                apply t_trans with (y := applySubstitution sigma ({{t5 | t6}})); try assumption.
                                                rewrite Heq34.
                                                rewrite Heq56.
                                                now rewrite <- Heqv.
                       *** case (clos_rel_term_dec (applySubstitution sigma (Var v)) (applySubstitution sigma (listSetC (deleteElmntj j lt') (Var v)))) as [? | ?].
                           ---- exists (c1'++c2' ++ ((Eq (nth 0 lt EmptySet) tj) ::
                                      (Eq (listSetC (deleteElmntj 0 lt) (Var v)) (listSetC (deleteElmntj j lt') (Var v))) :: nil)).
                                split.
                                ++++ apply step1.
                                     apply stepEq10_1; try assumption.
                                     now apply eq_decompose.
                                ++++ exists sigma.
                                     split.
                                     **** simpl; do 2 rewrite applySubToC_app.
                                          rewrite interpretC_app.
                                          split; try assumption.
                                          rewrite interpretC_app.
                                          split; try assumption.
                                          split; try now apply clos_rel_term_sym.
                                          rewrite Hd0_nil.
                                          now split.
                                     **** simpl; do 2 rewrite applySubToC_app.
                                          do 2 rewrite listVarInC_app.
                                          rewrite Hvarc1.
                                          rewrite Hvarc2.
                                          simpl; rewrite Hvar0lt.
                                          rewrite Hvarjlt'.
                                          rewrite Hvardjlt'.
                                          rewrite Hd0_nil.
                                          assert (Ht : listSetC nil (Var v) = Var v).
                                            trivial.
                                          rewrite Ht.
                                          now rewrite Hvarv.
                           ---- case (clos_rel_term_dec (applySubstitution sigma (listSetC lt (Var v))) (applySubstitution sigma (listSetC (deleteElmntj j lt') (Var v)))) as [? | ?].
                                ++++ exists (c1'++c2' ++ ((Eq (nth 0 lt EmptySet) tj) ::
                                              (Eq (listSetC lt (Var v)) (listSetC (deleteElmntj j lt') (Var v))) :: nil)).
                                     split.
                                     **** apply step1.
                                          apply stepEq10_2; try assumption.
                                          now apply eq_decompose.
                                     **** exists sigma.
                                          split.
                                          ----- simpl; do 2 rewrite applySubToC_app.
                                                rewrite interpretC_app.
                                                split; try assumption.
                                                rewrite interpretC_app.
                                                split; try assumption.
                                                split; try now apply clos_rel_term_sym.
                                                now split.
                                          ----- simpl; do 2 rewrite applySubToC_app.
                                                do 2 rewrite listVarInC_app.
                                                rewrite Hvarc1.
                                                rewrite Hvarc2.
                                                simpl; rewrite Hvar0lt.
                                                rewrite Hvarjlt'.
                                                rewrite Hvar34.
                                                now rewrite Hvardjlt'.
                                ++++ case (clos_rel_term_dec (applySubstitution sigma (Var v)) (applySubstitution sigma (listSetC lt' (Var v)))) as [? | ?].
                                     **** exists (c1'++c2' ++ ((Eq (nth 0 lt EmptySet) tj) :: (Eq (listSetC (deleteElmntj 0 lt) (Var v)) (listSetC lt' (Var v))) :: nil)).
                                          split.
                                          ----- apply step1.
                                                apply stepEq10_3 with (j := j); try assumption.
                                                now apply eq_decompose.
                                          ----- exists sigma.
                                                split.
                                                +++++ simpl; do 2 rewrite applySubToC_app.
                                                      rewrite interpretC_app.
                                                      split; try assumption.
                                                      rewrite interpretC_app.
                                                      split; try assumption.
                                                      split; try now apply clos_rel_term_sym.
                                                      split; try now trivial.
                                                      now rewrite Hd0_nil.
                                                +++++ simpl; do 2 rewrite applySubToC_app.
                                                      do 2 rewrite listVarInC_app.
                                                      rewrite Hvarc1.
                                                      rewrite Hvarc2.
                                                      simpl; rewrite Hvar0lt.
                                                      rewrite Hvarjlt'.
                                                      rewrite Hvar56.
                                                      rewrite Hd0_nil.
                                                      assert (Ht : listSetC nil (Var v) = Var v).
                                                        trivial.
                                                      rewrite Ht.
                                                      now rewrite Hvarv.
                                     **** assert (Hequiv34 : applySubstitution sigma ({{t3 | t4}}) === applySubstitution sigma ({{nth 0 lt EmptySet | Var v}})).
                                            rewrite Heq34.
                                            rewrite (deleteElmntj_eq_nil _ _ Hnth0 Hd0_nil).
                                            now apply clos_rel_term_refl.
                                          assert (Hequiv56 : applySubstitution sigma ({{t5 | t6}}) === applySubstitution sigma ({{tj | listSetC (deleteElmntj j lt') (Var v)}})).
                                            rewrite Heq56.
                                            rewrite Heqv.
                                            now apply applySub_listSetC_deleteElmntj.
                                          absurd (applySubstitution sigma ({{nth 0 lt EmptySet | Var v}}) === applySubstitution sigma ({{tj | listSetC (deleteElmntj j lt') (Var v)}})).
                                          ----- simpl; apply neg_inter_set; try assumption.
                                                +++++ now apply (clos_rel_term_setTerm Hequiv34).
                                                +++++ now apply (clos_rel_term_setTerm Hequiv56).
                                                +++++ now apply clos_rel_term_sym.
                                                +++++ intro Habs.
                                                      absurd (applySubstitution sigma (listSetC lt (Var v)) === applySubstitution sigma (listSetC (deleteElmntj j lt') (Var v))); try assumption.
                                                      apply t_trans with (y := ({{applySubstitution sigma (nth 0 lt EmptySet) | applySubstitution sigma (Var v)}})); try assumption.
                                                      now rewrite <- Heq34.
                                                +++++ intro Habs.
                                                      absurd (applySubstitution sigma (Var v) === applySubstitution sigma (listSetC lt' (Var v))); try assumption.
                                                      apply t_trans with (y := applySubstitution sigma ({{tj | (listSetC (deleteElmntj j lt') (Var v))}})); try assumption.
                                                      apply clos_rel_term_sym.
                                                      now apply applySub_listSetC_deleteElmntj.
                                          ----- apply t_trans with (y := applySubstitution sigma ({{t3 | t4}})); try now apply clos_rel_term_sym.
                                                apply t_trans with (y := applySubstitution sigma ({{t5 | t6}})); try assumption.
                                                rewrite Heq34.
                                                rewrite Heq56.
                                                now rewrite <- Heqv.
                   +++ case (list_eq_dec eq_term_dec (deleteElmntj j lt') nil) as [Hdj_nil | Hneqdj_nil].
                       *** case (clos_rel_term_dec (applySubstitution sigma (listSetC (deleteElmntj 0 lt) (Var v))) (applySubstitution sigma (Var v))) as [? | ?].
                           ---- exists (c1'++c2' ++ ((Eq (nth 0 lt EmptySet) tj) ::
                                      (Eq (listSetC (deleteElmntj 0 lt) (Var v)) (listSetC (deleteElmntj j lt') (Var v))) :: nil)).
                                split.
                                ++++ apply step1.
                                     apply stepEq10_1; try assumption.
                                     now apply eq_decompose.
                                ++++ exists sigma.
                                     split.
                                     **** simpl; do 2 rewrite applySubToC_app.
                                          rewrite interpretC_app.
                                          split; try assumption.
                                          rewrite interpretC_app.
                                          split; try assumption.
                                          split; try now apply clos_rel_term_sym.
                                          rewrite Hdj_nil.
                                          now split.
                                     **** simpl; do 2 rewrite applySubToC_app.
                                          do 2 rewrite listVarInC_app.
                                          rewrite Hvarc1.
                                          rewrite Hvarc2.
                                          simpl; rewrite Hvar0lt.
                                          rewrite Hvarjlt'.
                                          rewrite Hvard0lt.
                                          rewrite Hdj_nil.
                                          assert (Ht : listSetC nil (Var v) = Var v).
                                            trivial.
                                          rewrite Ht.
                                          now rewrite Hvarv.
                           ---- case (clos_rel_term_dec (applySubstitution sigma (listSetC (deleteElmntj 0 lt) (Var v))) (applySubstitution sigma (listSetC lt' (Var v)))) as [? | ?].
                                ++++ exists (c1'++c2' ++ ((Eq (nth 0 lt EmptySet) tj) :: (Eq (listSetC (deleteElmntj 0 lt) (Var v)) (listSetC lt' (Var v))) :: nil)).
                                     split.
                                     **** apply step1.
                                          apply stepEq10_3 with (j := j); try assumption.
                                          now apply eq_decompose.
                                     **** exists sigma.
                                          split.
                                          ----- simpl; do 2 rewrite applySubToC_app.
                                                rewrite interpretC_app.
                                                split; try assumption.
                                                rewrite interpretC_app.
                                                split; try assumption.
                                                split; try now apply clos_rel_term_sym.
                                                now split.
                                          ----- simpl; do 2 rewrite applySubToC_app.
                                                do 2 rewrite listVarInC_app.
                                                rewrite Hvarc1.
                                                rewrite Hvarc2.
                                                simpl; rewrite Hvar0lt.
                                                rewrite Hvarjlt'.
                                                rewrite Hvar56.
                                                now rewrite Hvard0lt.
                               ++++ case (clos_rel_term_dec (applySubstitution sigma (listSetC lt (Var v))) (applySubstitution sigma (Var v))) as [? | ?].
                                    **** exists (c1'++c2' ++ ((Eq (nth 0 lt EmptySet) tj) ::
                                              (Eq (listSetC lt (Var v)) (listSetC (deleteElmntj j lt') (Var v))) :: nil)).
                                         split.
                                         ----- apply step1.
                                               apply stepEq10_2; try assumption.
                                               now apply eq_decompose.
                                         ----- exists sigma.
                                               split.
                                               +++++ simpl; do 2 rewrite applySubToC_app.
                                                     rewrite interpretC_app.
                                                     split; try assumption.
                                                     rewrite interpretC_app.
                                                     split; try assumption.
                                                     split; try now apply clos_rel_term_sym.
                                                     now rewrite Hdj_nil.
                                               +++++ simpl; do 2 rewrite applySubToC_app.
                                                     do 2 rewrite listVarInC_app.
                                                     rewrite Hvarc1.
                                                     rewrite Hvarc2.
                                                     simpl; rewrite Hvar0lt.
                                                     rewrite Hvarjlt'.
                                                     rewrite Hvar34.
                                                     rewrite Hdj_nil.
                                                     assert (Ht : listSetC nil (Var v) = Var v).
                                                       trivial.
                                                     rewrite Ht.
                                                     now rewrite Hvarv.
                                    **** assert (Hequiv34 : applySubstitution sigma ({{t3 | t4}}) === applySubstitution sigma ({{nth 0 lt EmptySet | listSetC (deleteElmntj 0 lt) (Var v)}})).
                                           rewrite Heq34.
                                           now apply applySub_listSetC_deleteElmntj.
                                         assert (Hequiv56 : applySubstitution sigma ({{t5 | t6}}) === applySubstitution sigma ({{tj | Var v}})).
                                           rewrite Heq56.
                                           rewrite (deleteElmntj_eq_nil _ _ Htjeq Hdj_nil).
                                           rewrite Heqv.
                                           now apply clos_rel_term_refl.
                                         absurd (applySubstitution sigma ({{nth 0 lt EmptySet | listSetC (deleteElmntj 0 lt) (Var v)}}) === applySubstitution sigma ({{tj | Var v}})).
                                         ----- simpl; apply neg_inter_set; try assumption.
                                               +++++ now apply (clos_rel_term_setTerm Hequiv34).
                                               +++++ now apply (clos_rel_term_setTerm Hequiv56).
                                               +++++ now apply clos_rel_term_sym.
                                               +++++ intro Habs.
                                                     absurd (applySubstitution sigma (listSetC lt (Var v)) === applySubstitution sigma (Var v)); try assumption.
                                                     apply t_trans with (y := ({{applySubstitution sigma (nth 0 lt EmptySet) | applySubstitution sigma (listSetC (deleteElmntj 0 lt) (Var v))}})); try assumption.
                                                     now apply applySub_listSetC_deleteElmntj.
                                               +++++ intro Habs.
                                                     absurd (applySubstitution sigma (listSetC (deleteElmntj 0 lt) (Var v)) === applySubstitution sigma (listSetC lt' (Var v))); try assumption.
                                                       apply t_trans with (y := applySubstitution sigma ({{tj | Var v}})); try assumption.
                                                       apply clos_rel_term_sym.
                                                       rewrite <- Heqv in Heq56.
                                                       now rewrite <- Heq56.
                                          ----- apply t_trans with (y := applySubstitution sigma ({{t3 | t4}})); try now apply clos_rel_term_sym.
                                                apply t_trans with (y := applySubstitution sigma ({{t5 | t6}})); try assumption.
                                                rewrite Heq34.
                                                rewrite Heq56.
                                                now rewrite <- Heqv.
                       *** case (clos_rel_term_dec (applySubstitution sigma (listSetC (deleteElmntj 0 lt) (Var v))) (applySubstitution sigma (listSetC (deleteElmntj j lt') (Var v)))) as [? | ?].
                           ---- exists (c1'++c2' ++ ((Eq (nth 0 lt EmptySet) tj) ::
                                      (Eq (listSetC (deleteElmntj 0 lt) (Var v)) (listSetC (deleteElmntj j lt') (Var v))) :: nil)).
                                split.
                                ++++ apply step1.
                                     apply stepEq10_1; try assumption.
                                     now apply eq_decompose.
                                ++++ exists sigma.
                                     split.
                                     **** simpl; do 2 rewrite applySubToC_app.
                                          rewrite interpretC_app.
                                          split; try assumption.
                                          rewrite interpretC_app.
                                          split; try assumption.
                                          split; try now split.
                                          now apply clos_rel_term_sym.
                                     **** simpl; do 2 rewrite applySubToC_app.
                                          do 2 rewrite listVarInC_app.
                                          rewrite Hvarc1.
                                          rewrite Hvarc2.
                                          simpl; rewrite Hvar0lt.
                                          rewrite Hvarjlt'.
                                          rewrite Hvard0lt.
                                          now rewrite Hvardjlt'.
                           ---- case (clos_rel_term_dec (applySubstitution sigma (listSetC lt (Var v))) (applySubstitution sigma (listSetC (deleteElmntj j lt') (Var v)))) as [? | ?].
                                ++++ exists (c1'++c2' ++ ((Eq (nth 0 lt EmptySet) tj) ::
                                              (Eq (listSetC lt (Var v)) (listSetC (deleteElmntj j lt') (Var v))) :: nil)).
                                     split.
                                     **** apply step1.
                                          apply stepEq10_2; try assumption.
                                          now apply eq_decompose.
                                     **** exists sigma.
                                          split.
                                          ----- simpl; do 2 rewrite applySubToC_app.
                                                rewrite interpretC_app.
                                                split; try assumption.
                                                rewrite interpretC_app.
                                                split; try assumption.
                                                split; try now split.
                                                now apply clos_rel_term_sym.
                                          ----- simpl; do 2 rewrite applySubToC_app.
                                                do 2 rewrite listVarInC_app.
                                                rewrite Hvarc1.
                                                rewrite Hvarc2.
                                                simpl; rewrite Hvar0lt.
                                                rewrite Hvarjlt'.
                                                rewrite Hvar34.
                                                now rewrite Hvardjlt'.
                                ++++ case (clos_rel_term_dec (applySubstitution sigma (listSetC (deleteElmntj 0 lt) (Var v))) (applySubstitution sigma (listSetC lt' (Var v)))) as [? | ?].
                                     **** exists (c1'++c2' ++ ((Eq (nth 0 lt EmptySet) tj) :: (Eq (listSetC (deleteElmntj 0 lt) (Var v)) (listSetC lt' (Var v))) :: nil)).
                                          split.
                                          ----- apply step1.
                                                apply stepEq10_3 with (j := j); try assumption.
                                                now apply eq_decompose.
                                          ----- exists sigma.
                                                split.
                                                +++++ simpl; do 2 rewrite applySubToC_app.
                                                      rewrite interpretC_app.
                                                      split; try assumption.
                                                      rewrite interpretC_app.
                                                      split; try assumption.
                                                      split; try now split.
                                                      now apply clos_rel_term_sym.
                                                +++++ simpl; do 2 rewrite applySubToC_app.
                                                      do 2 rewrite listVarInC_app.
                                                      rewrite Hvarc1.
                                                      rewrite Hvarc2.
                                                      simpl; rewrite Hvar0lt.
                                                      rewrite Hvarjlt'.
                                                      rewrite Hvard0lt.
                                                      now rewrite Hvar56.
                                     **** assert (Hequiv34 : applySubstitution sigma ({{t3 | t4}}) === applySubstitution sigma ({{nth 0 lt EmptySet | listSetC (deleteElmntj 0 lt) (Var v)}})).
                                            rewrite Heq34.
                                            now apply applySub_listSetC_deleteElmntj.
                                          assert (Hequiv56 : applySubstitution sigma ({{t5 | t6}}) === applySubstitution sigma ({{tj | listSetC (deleteElmntj j lt') (Var v)}})).
                                            rewrite Heq56.
                                            rewrite Heqv.
                                            now apply applySub_listSetC_deleteElmntj.
                                          absurd (applySubstitution sigma ({{nth 0 lt EmptySet | listSetC (deleteElmntj 0 lt) (Var v)}}) === applySubstitution sigma ({{tj | listSetC (deleteElmntj j lt') (Var v)}})).
                                          ----- simpl; apply neg_inter_set; try assumption.
                                                +++++ now apply (clos_rel_term_setTerm Hequiv34).
                                                +++++ now apply (clos_rel_term_setTerm Hequiv56).
                                                +++++ now apply clos_rel_term_sym.
                                                +++++ intro Habs.
                                                      absurd (applySubstitution sigma (listSetC lt (Var v)) === applySubstitution sigma (listSetC (deleteElmntj j lt') (Var v))); try assumption.
                                                      apply t_trans with (y := ({{applySubstitution sigma (nth 0 lt EmptySet) | applySubstitution sigma (listSetC (deleteElmntj 0 lt) (Var v))}})); try assumption.
                                                      now apply applySub_listSetC_deleteElmntj.
                                                +++++ intro Habs.
                                                      absurd (applySubstitution sigma (listSetC (deleteElmntj 0 lt) (Var v)) === applySubstitution sigma (listSetC lt' (Var v))); try assumption.
                                                      apply t_trans with (y := applySubstitution sigma ({{tj | (listSetC (deleteElmntj j lt') (Var v))}})); try assumption.
                                                      apply clos_rel_term_sym.
                                                      now apply applySub_listSetC_deleteElmntj.
                                          ----- apply t_trans with (y := applySubstitution sigma ({{t3 | t4}})); try now apply clos_rel_term_sym.
                                                apply t_trans with (y := applySubstitution sigma ({{t5 | t6}})); try assumption.
                                                rewrite Heq34.
                                                rewrite Heq56.
                                                now rewrite <- Heqv.
               --- pose (u := FreshVarFun c1).
                   assert (HsetTermv : setTerm (applySubstitution sigma (Var v))).
                     rewrite Heq34 in HsetTerm4.
                     rewrite applySub_listSetC in HsetTerm4.
                     now rewrite setTerm_listSetC in HsetTerm4.
                   assert (Hfreshfstp1 : isFreshC u c1).
                     now apply FreshVarFun_isFresh.
                   assert (HnegIn34 : ~ In u (listVarInT (listSetC lt (Var v)))).
                     intro Habs.
                     absurd (occurCheckC u c1); try assumption.
                     apply in_occurCheckC with (pc := (listSetC lt (Var v)) == (listSetC lt' (Var v)));
                       try now left; apply In_listVarInT_occurCheck with (t := listSetC lt (Var v)).
                     rewrite Heq.
                     apply in_or_app; right.
                     now apply in_eq.
                   assert (HnegIn56 : ~ In u (listVarInT (listSetC lt' (Var v)))).
                     intro Habs.
                     absurd (occurCheckC u c1); try assumption.
                     apply in_occurCheckC with (pc := (listSetC lt (Var v)) == (listSetC lt' (Var v)));
                       try now right; apply In_listVarInT_occurCheck with (t := listSetC lt' (Var v)).
                     rewrite Heq.
                     apply in_or_app; right.
                     now apply in_eq.
                   assert (HnegInnth0 : ~ In u (listVarInT (nth 0 lt EmptySet))).
                     intros Habs.
                     absurd (In u (listVarInT (listSetC lt (Var v)))); try assumption.
                     apply listVarInListT_listSetC; try assumption.
                     apply incl_listVarInT_listVarInListT with (t := nth 0 lt EmptySet); try assumption.
                     now apply nth_In.
                   assert (HnegIn1 : ~ In u (listVarInC c1')).
                     intro HIn'.
                     absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                     apply incl_occurCheckC with (c1 := c1'); try now apply In_listVarInC_occurCheckC.
                     rewrite Heq.
                     now apply incl_appl.
                   assert (HnegIn2 : ~ In u (listVarInC c2')).
                     intro HIn'.
                     absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                     apply incl_occurCheckC with (c1 := c2'); try now apply In_listVarInC_occurCheckC.
                     rewrite Heq.
                     apply incl_appr.
                     now apply incl_tl.
                   assert (HnegIn12 : ~ In u (listVarInC (c1' ++ c2'))).
                     intro HIn'.
                     absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                     apply incl_occurCheckC with (c1 := c1' ++ c2'); try now apply In_listVarInC_occurCheckC.
                     rewrite Heq.
                     apply incl_app_app; try now apply incl_refl.
                     now apply incl_tl.
                   assert (Hneq : v <> u).
                     intro Habs.
                     absurd (occurCheckC u c1); try assumption.
                     apply In_listVarInC_occurCheckC.
                     rewrite <- Habs.
                     rewrite Heq.
                     rewrite listVarInC_app.
                     apply in_or_app; right.
                     apply in_or_app; left.
                     apply in_or_app; left.
                     apply listVarInT_listSetC; try assumption.
                     now left.
                   case (list_eq_dec eq_term_dec (deleteElmntj 0 lt) nil) as [Hd0_nil | Hneqd0_nil].
                   +++ exists (c1' ++ c2' ++ ((Var v == SetC (nth 0 lt EmptySet) (Var u)) :: ((listSetC (deleteElmntj 0 lt) (Var u) == listSetC lt' (Var u)) :: ((IsSet (Var u))::nil)))).
                       split.
                       *** apply step1.
                           apply stepEq10_4 with (j := 0) (tj := nth 0 lt' EmptySet); try assumption.
                           ---- now apply eq_decompose.
                           ---- apply nth_error_nth'.
                                apply Lt.neq_0_lt.
                                intro Habs.
                                absurd (lt' = nil); try assumption.
                                apply length_zero_iff_nil.
                                now rewrite Habs.
                           ---- rewrite <- (listSetC_SetCToList _ _ Heq34).
                                apply isFreshT_SetC_isFreshL.
                                rewrite Heq34.
                                intro Habs.
                                absurd (In u (listVarInT (listSetC lt (Var v)))); try assumption.
                                now apply occurCheck_In_listVarInT.
                           ---- rewrite <- (listSetC_SetCToList _ _ Heq56).
                                apply isFreshT_SetC_isFreshL.
                                rewrite Heq56.
                                rewrite <- Heqv.
                                intro Habs.
                                absurd (In u (listVarInT (listSetC lt' (Var v)))); try assumption.
                                now apply occurCheck_In_listVarInT.
                       *** exists ((u, applySubstitution sigma (Var v)) :: sigma).
                           split.
                           ---- simpl; do 2 rewrite applySubToC_app.
                                do 2 rewrite interpretC_app.
                                split; try now rewrite neq_listVarInC_applySub.
                                split; try now rewrite neq_listVarInC_applySub.
                                split.
                                ++++ simpl; case (eq_variable_dec v u) as [? | ?]; try contradiction.
                                     case (eq_variable_dec u u) as [_ | ?]; try contradiction.
                                     apply inset_eqset.
                                     rewrite neq_listVarInT_applySub; try assumption.
                                     enough (Hor : interpretPC ((applySubstitution sigma (nth 0 lt EmptySet)) :s (applySubstitution sigma (Var v))) 
                                                    \/ incl_interpret ((applySubstitution sigma (nth 0 lt EmptySet)) :: nil) (map (applySubstitution sigma) lt')).
                                       now case Hor as [? | ?].
                                     apply axiomW_listSetC_w; try assumption.
                                     rewrite <- applySub_listSetC.
                                     apply (clos_rel_term_set_Mem _ HinterS).
                                     rewrite applySub_listSetC.
                                     apply axiomW_listSetC_w; try assumption.
                                     right; intros t HInt.
                                     case HInt as [<- | ?]; try contradiction.
                                     exists (applySubstitution sigma (nth 0 lt EmptySet)).
                                     split; try now apply clos_rel_term_refl.
                                     apply in_map.
                                     now apply nth_In.
                                ++++ split.
                                     **** assert (map (applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma)) lt' <> nil).
                                            intro Habs.
                                            absurd (lt' = nil); try assumption.
                                            now apply map_eq_nil with (f := applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma)).
                                          rewrite Hd0_nil.
                                          simpl; rewrite applySub_listSetC.
                                          simpl; case (eq_variable_dec u u) as [? | ?]; try contradiction.
                                          simpl in HinterS; do 2 rewrite applySub_listSetC in HinterS.
                                          destruct (setTerm_exists_listSetC _ HsetTermv) as [lt'' Heq''].
                                          rewrite Heq'' in HinterS.
                                          simpl in Heq''.
                                          rewrite Heq''.
                                          rewrite <- listSetC_app_EmptySet; try now rewrite <- Heq''.
                                          apply incl_interpret_listSetC_clos_rel_term; intros t HInt.
                                           ----- exists t.
                                                 split; try now apply clos_rel_term_refl.
                                                 now apply in_or_app; right.
                                           ----- case (in_app_or _ _ _ HInt) as [HInt' | ?].
                                                 +++++ assert (Hexists : exists t', applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma) t' = t /\ In t' lt').
                                                         rewrite <- Heq'' in HInt'.
                                                         now apply in_map_iff.
                                                       destruct Hexists as [t' [<- ?]].
                                                       assert (~ In u (listVarInT t')).
                                                         intro Habs.
                                                         absurd (In u (listVarInT (listSetC lt' (Var v)))); try assumption.
                                                         apply listVarInListT_listSetC; try assumption.
                                                         now apply incl_listVarInT_listVarInListT with (t := t').
                                                       assert (Hincl_inter : incl_interpret ((map (applySubstitution sigma) lt') ++ lt'') ((map (applySubstitution sigma) lt) ++ lt'')).
                                                         apply clos_rel_term_listSetC_incl_interpret_EmptySet.
                                                         rewrite listSetC_app_EmptySet; try assumption.
                                                         rewrite listSetC_app_EmptySet; try assumption.
                                                         now apply clos_rel_term_sym.
                                                       assert (H' : In (applySubstitution sigma t') ((map (applySubstitution sigma) lt') ++ lt'')).
                                                         apply in_or_app; left.
                                                         now apply in_map.
                                                       destruct (Hincl_inter _ H') as [t'' [? HIn'']].
                                                       case (in_app_or _ _ _ HIn'') as [? | ?].
                                                       ***** exists t''.
                                                             split; try now rewrite neq_listVarInT_applySub.
                                                             assert (Hexists : exists t, applySubstitution sigma t = t'' /\ In t lt).
                                                               now apply in_map_iff.
                                                             destruct Hexists as [t''' [Heq' HInt''']].
                                                             rewrite (deleteElmntj_eq_nil _ _ Hnth0 Hd0_nil) in HInt'''.
                                                             case HInt''' as [<- | ?]; try contradiction.
                                                             absurd (incl_interpret (applySubstitution sigma (nth 0 lt EmptySet) :: nil) (map (applySubstitution sigma) lt')); try assumption.
                                                             intros t''' Hor.
                                                             case Hor as [<- | ?]; try contradiction.
                                                             exists (applySubstitution sigma t').
                                                             split; try now apply in_map.
                                                             apply t_trans with (y := t''); try now apply clos_rel_term_sym.
                                                             rewrite Heq'.
                                                             now apply clos_rel_term_refl.
                                                       ***** exists t''.
                                                             split; try assumption.
                                                             now rewrite neq_listVarInT_applySub.
                                                 +++++ exists t.
                                                       split; try assumption.
                                                       now apply clos_rel_term_refl.
                                      **** now simpl; case (eq_variable_dec u u) as [? | ?].
                           ---- simpl; do 2 rewrite applySubToC_app.
                                do 2 rewrite listVarInC_app.
                                rewrite neq_listVarInC_applySub; try assumption.
                                rewrite Hvarc1.
                                rewrite neq_listVarInC_applySub; try assumption.
                                rewrite Hvarc2.
                                rewrite Hd0_nil.
                                simpl; rewrite applySub_listSetC.
                                simpl; case (eq_variable_dec u u) as [? | ?]; try contradiction.
                                rewrite neq_listVarInT_applySub; try assumption.
                                rewrite Hvar0lt.
                                simpl; case (eq_variable_dec v u) as [? | ?]; try contradiction.
                                simpl in Hvarv; rewrite Hvarv.
                                simpl; rewrite app_nil_r.
                                apply incl_l_nil.
                                apply incl_tran with (m := listVarInListT (map (applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma)) lt')  ++ listVarInT (applySubstitution sigma (Var v)));
                                  try now apply listSetC_listVarInListT.
                                apply incl_app; try now simpl; rewrite Hvarv.
                                enough (He : listVarInListT (map (applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma)) lt') = nil).
                                  now rewrite He.
                                apply listVarInListT_eq_nil.
                                intros t HInt.
                                assert (Hexists : exists t', applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma) t' = t /\ In t' lt').
                                  now apply in_map_iff.
                                destruct Hexists as [t' [<- ?]].
                                assert (~ In u (listVarInT t')).
                                intro Habs.
                                absurd (In u (listVarInT (listSetC lt' (Var v)))); try assumption.
                                apply listVarInListT_listSetC; try assumption.
                                now apply incl_listVarInT_listVarInListT with (t := t').
                                assert (Hforall : forall t, In t (map (applySubstitution sigma) lt') -> listVarInT t = nil).
                                  now apply listVarInListT_eq_nil.
                                rewrite neq_listVarInT_applySub; try assumption.
                                apply Hforall.
                                now apply in_map.
                   +++ exists (c1' ++ c2' ++ ((Var v == SetC (nth 0 lt EmptySet) (Var u)) :: ((listSetC (deleteElmntj 0 lt) (Var u) == listSetC lt' (Var u)) :: ((IsSet (Var u))::nil)))).
                       split.
                       *** apply step1.
                           apply stepEq10_4 with (j := 0) (tj := nth 0 lt' EmptySet); try assumption.
                           ---- now apply eq_decompose.
                           ---- apply nth_error_nth'.
                                apply Lt.neq_0_lt.
                                intro Habs.
                                absurd (lt' = nil); try assumption.
                                apply length_zero_iff_nil.
                                now rewrite Habs.
                           ---- rewrite <- (listSetC_SetCToList _ _ Heq34).
                                apply isFreshT_SetC_isFreshL.
                                rewrite Heq34.
                                intro Habs.
                                absurd (In u (listVarInT (listSetC lt (Var v)))); try assumption.
                                now apply occurCheck_In_listVarInT.
                           ---- rewrite <- (listSetC_SetCToList _ _ Heq56).
                                apply isFreshT_SetC_isFreshL.
                                rewrite Heq56.
                                rewrite <- Heqv.
                                intro Habs.
                                absurd (In u (listVarInT (listSetC lt' (Var v)))); try assumption.
                                now apply occurCheck_In_listVarInT.
                       *** exists ((u, applySubstitution sigma (Var v)) :: sigma).
                           split.
                           ---- simpl; do 2 rewrite applySubToC_app.
                                do 2 rewrite interpretC_app.
                                split; try now rewrite neq_listVarInC_applySub.
                                split; try now rewrite neq_listVarInC_applySub.
                                split.
                                ++++ simpl; case (eq_variable_dec v u) as [? | ?]; try contradiction.
                                     case (eq_variable_dec u u) as [_ | ?]; try contradiction.
                                     apply inset_eqset.
                                     rewrite neq_listVarInT_applySub; try assumption.
                                     enough (Hor : interpretPC ((applySubstitution sigma (nth 0 lt EmptySet)) :s (applySubstitution sigma (Var v)))
                                                    \/ incl_interpret ((applySubstitution sigma (nth 0 lt EmptySet)) :: nil) (map (applySubstitution sigma) lt')).
                                       now case Hor as [? | ?].
                                     apply axiomW_listSetC_w; try assumption.
                                     rewrite <- applySub_listSetC.
                                     apply (clos_rel_term_set_Mem _ HinterS).
                                     rewrite applySub_listSetC.
                                     apply axiomW_listSetC_w; try assumption.
                                     right; intros t HInt.
                                     case HInt as [<- | ?]; try contradiction.
                                     exists (applySubstitution sigma (nth 0 lt EmptySet)).
                                     split; try now apply clos_rel_term_refl.
                                     apply in_map.
                                     now apply nth_In.
                                 ++++ split.
                                      **** assert (map (applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma)) (deleteElmntj 0 lt) <> nil).
                                           intro Habs.
                                           absurd (deleteElmntj 0 lt = nil); try assumption.
                                           now apply map_eq_nil with (f := applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma)).
                                           assert (map (applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma)) lt' <> nil).
                                             intro Habs.
                                             absurd (lt' = nil); try assumption.
                                             now apply map_eq_nil with (f := applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma)).
                                           simpl; do 2 rewrite applySub_listSetC.
                                           simpl; case (eq_variable_dec u u) as [? | ?]; try contradiction.
                                           simpl in HinterS; do 2 rewrite applySub_listSetC in HinterS.
                                           destruct (setTerm_exists_listSetC _ HsetTermv) as [lt'' Heq''].
                                           rewrite Heq'' in HinterS.
                                           simpl in Heq''.
                                           rewrite Heq''.
                                           rewrite <- listSetC_app_EmptySet; try now rewrite <- Heq''.
                                           rewrite <- listSetC_app_EmptySet; try now rewrite <- Heq''.
                                           apply incl_interpret_listSetC_clos_rel_term; intros t HInt.
                                           ----- case (in_app_or _ _ _ HInt) as [HInt' | ?].
                                                 +++++ assert (Hexists : exists t', applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma) t' = t /\ In t' (deleteElmntj 0 lt)).
                                                         rewrite <- Heq'' in HInt'.
                                                         now apply in_map_iff.
                                                       destruct Hexists as [t' [<- ?]].
                                                       assert (~ In u (listVarInT t')).
                                                         intro Habs.
                                                         absurd (In u (listVarInT (listSetC lt (Var v)))); try assumption.
                                                         apply listVarInListT_listSetC; try assumption.
                                                         apply incl_listVarInT_listVarInListT with (t := t'); try assumption.
                                                         now apply deleteElmntj_incl with (j := 0).
                                                       assert (Hincl_inter : incl_interpret ((map (applySubstitution sigma) lt) ++ lt'') ((map (applySubstitution sigma) lt') ++ lt'')).
                                                         apply clos_rel_term_listSetC_incl_interpret_EmptySet.
                                                         rewrite listSetC_app_EmptySet; try assumption.
                                                         now rewrite listSetC_app_EmptySet.
                                                       assert (H' : In (applySubstitution sigma t') ((map (applySubstitution sigma) lt) ++ lt'')).
                                                         apply in_or_app; left.
                                                         apply in_map.
                                                         now apply deleteElmntj_incl with (j := 0).
                                                       destruct (Hincl_inter _ H') as [t'' [? HIn'']].
                                                       case (in_app_or _ _ _ HIn'') as [? | ?].
                                                       ***** exists t''.
                                                             split; try now rewrite neq_listVarInT_applySub.
                                                             assert (Hexists : exists t, applySubstitution sigma t = t'' /\ In t lt').
                                                               now apply in_map_iff.
                                                             destruct Hexists as [t''' [? ?]].
                                                             apply in_or_app; left.
                                                             apply in_map_iff.
                                                             exists t'''.
                                                             split; try assumption.
                                                             rewrite neq_listVarInT_applySub; try assumption.
                                                             intro Habs.
                                                             absurd (In u (listVarInT (listSetC lt' (Var v)))); try assumption.
                                                             apply listVarInListT_listSetC; try assumption.
                                                             now apply incl_listVarInT_listVarInListT with (t := t''').
                                                       ***** exists t''.
                                                             split; try now apply in_or_app; right.
                                                             now rewrite neq_listVarInT_applySub.
                                                 +++++ exists t.
                                                       split; try now apply clos_rel_term_refl.
                                                       apply in_or_app.
                                                       now right.
                                           ----- case (in_app_or _ _ _ HInt) as [HInt' | ?].
                                                 +++++ assert (Hexists : exists t', applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma) t' = t /\ In t' lt').
                                                         rewrite <- Heq'' in HInt'.
                                                         now apply in_map_iff.
                                                       destruct Hexists as [t' [<- ?]].
                                                       assert (~ In u (listVarInT t')).
                                                         intro Habs.
                                                         absurd (In u (listVarInT (listSetC lt' (Var v)))); try assumption.
                                                         apply listVarInListT_listSetC; try assumption.
                                                         now apply incl_listVarInT_listVarInListT with (t := t').
                                                       assert (Hincl_inter : incl_interpret ((map (applySubstitution sigma) lt') ++ lt'') ((map (applySubstitution sigma) lt) ++ lt'')).
                                                         apply clos_rel_term_listSetC_incl_interpret_EmptySet.
                                                         rewrite listSetC_app_EmptySet; try assumption.
                                                         rewrite listSetC_app_EmptySet; try assumption.
                                                         now apply clos_rel_term_sym.
                                                       assert (H' : In (applySubstitution sigma t') ((map (applySubstitution sigma) lt') ++ lt'')).
                                                         apply in_or_app; left.
                                                         now apply in_map.
                                                       destruct (Hincl_inter _ H') as [t'' [? HIn'']].
                                                       case (in_app_or _ _ _ HIn'') as [? | ?].
                                                       ***** exists t''.
                                                             split; try now rewrite neq_listVarInT_applySub.
                                                             assert (Hexists : exists t, applySubstitution sigma t = t'' /\ In t lt).
                                                               now apply in_map_iff.
                                                             destruct Hexists as [t''' [Heq' HInt''']].
                                                             apply in_or_app; left.
                                                             apply in_map_iff.
                                                             case (eq_term_dec t''' (nth 0 lt EmptySet)) as [-> | ?].
                                                             ------ absurd (incl_interpret (applySubstitution sigma (nth 0 lt EmptySet) :: nil) (map (applySubstitution sigma) lt')); try assumption.
                                                                    intros t''' Hor.
                                                                    case Hor as [<- | ?]; try contradiction.
                                                                    exists (applySubstitution sigma t').
                                                                    split; try now apply in_map.
                                                                    apply t_trans with (y := t''); try now apply clos_rel_term_sym.
                                                                    rewrite Heq'.
                                                                    now apply clos_rel_term_refl.
                                                             ------ exists t'''.
                                                                    split; try now case (deleteElmntj_in_or _ _ _ Hnth0 HInt''') as [? | ?].
                                                                    rewrite neq_listVarInT_applySub; try assumption.
                                                                    intro Habs.
                                                                    absurd (In u (listVarInT (listSetC lt (Var v)))); try assumption.
                                                                    apply listVarInListT_listSetC; try assumption.
                                                                    now apply incl_listVarInT_listVarInListT with (t := t''').
                                                       ***** exists t''.
                                                             split; try now apply in_or_app; right.
                                                             now rewrite neq_listVarInT_applySub.
                                                 +++++ exists t.
                                                       split; try now apply clos_rel_term_refl.
                                                       now apply in_or_app; right.
                                      **** now simpl; case (eq_variable_dec u u) as [? | ?].
                           ---- simpl; do 2 rewrite applySubToC_app.
                                do 2 rewrite listVarInC_app.
                                rewrite neq_listVarInC_applySub; try assumption.
                                rewrite Hvarc1.
                                rewrite neq_listVarInC_applySub; try assumption.
                                rewrite Hvarc2.
                                simpl; do 2 rewrite applySub_listSetC.
                                simpl; case (eq_variable_dec u u) as [? | ?]; try contradiction.
                                rewrite neq_listVarInT_applySub; try assumption.
                                rewrite Hvar0lt.
                                simpl; case (eq_variable_dec v u) as [? | ?]; try contradiction.
                                simpl in Hvarv; rewrite Hvarv.
                                simpl; rewrite app_nil_r.
                                apply incl_l_nil.
                                apply incl_app.
                                ++++ apply incl_tran with (m := listVarInListT (map (applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma)) (deleteElmntj 0 lt))  ++ listVarInT (applySubstitution sigma (Var v)));
                                       try now apply listSetC_listVarInListT.
                                     apply incl_app; try now simpl; rewrite Hvarv.
                                     enough (He : listVarInListT (map (applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma)) (deleteElmntj 0 lt)) = nil).
                                       now rewrite He.
                                     apply listVarInListT_eq_nil.
                                     intros t HInt.
                                     assert (Hexists : exists t', applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma) t' = t /\ In t' (deleteElmntj 0 lt)).
                                       now apply in_map_iff.
                                     destruct Hexists as [t' [<- ?]].
                                     assert (~ In u (listVarInT t')).
                                       intro Habs.
                                       absurd (In u (listVarInT (listSetC lt (Var v)))); try assumption.
                                       apply listVarInListT_listSetC; try assumption.
                                       apply incl_listVarInT_listVarInListT with (t := t'); try assumption.
                                       now apply deleteElmntj_incl with (j := 0).
                                     assert (Hforall : forall t, In t (map (applySubstitution sigma) lt) -> listVarInT t = nil).
                                       now apply listVarInListT_eq_nil.
                                     rewrite neq_listVarInT_applySub; try assumption.
                                     apply Hforall.
                                     apply in_map.
                                     now apply deleteElmntj_incl with (j := 0).
                                ++++ apply incl_tran with (m := listVarInListT (map (applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma)) lt')  ++ listVarInT (applySubstitution sigma (Var v)));
                                       try now apply listSetC_listVarInListT.
                                     apply incl_app; try now simpl; rewrite Hvarv.
                                     enough (He : listVarInListT (map (applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma)) lt') = nil).
                                       now rewrite He.
                                     apply listVarInListT_eq_nil.
                                     intros t HInt.
                                     assert (Hexists : exists t', applySubstitution ((u, applySubstitution sigma (Var v)) :: sigma) t' = t /\ In t' lt').
                                       now apply in_map_iff.
                                     destruct Hexists as [t' [<- ?]].
                                     assert (~ In u (listVarInT t')).
                                       intro Habs.
                                       absurd (In u (listVarInT (listSetC lt' (Var v)))); try assumption.
                                       apply listVarInListT_listSetC; try assumption.
                                       now apply incl_listVarInT_listVarInListT with (t := t').
                                     assert (Hforall : forall t, In t (map (applySubstitution sigma) lt') -> listVarInT t = nil).
                                       now apply listVarInListT_eq_nil.
                                     rewrite neq_listVarInT_applySub; try assumption.
                                     apply Hforall.
                                     now apply in_map.
            ** destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
               rewrite Heq in Hinter.
               rewrite Heq in Hvar.
               rewrite applySubToC_app in Hinter.
               rewrite applySubToC_app in Hvar.
               rewrite listVarInC_app in Hvar.
               assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((({{t3 | t4}}) == ({{t5 | t6}})) :: c2'))).
                 now apply interpretC_app.
               destruct Hand as [Hinter1 HinterS2].
               destruct HinterS2 as [HinterS Hinter2].
               case (clos_rel_term_dec (applySubstitution sigma t3) (applySubstitution sigma t5)) as [? | Hneq_equiv].
               --- case (clos_rel_term_dec (applySubstitution sigma t4) (applySubstitution sigma t6)) as [? | ?].
                   +++ exists ((t3 == t5)::((t4 == t6):: (c1' ++ c2'))).
                       split.
                       *** apply step1.
                           apply stepEq9_1; try now apply eq_decompose.
                           rewrite Heqt4.
                           rewrite Heqt6.
                           now apply var_var.
                       *** exists sigma.
                           split.
                           ---- split; try assumption.
                                split; try assumption.
                                rewrite applySubToC_app.
                                now rewrite interpretC_app.
                           ---- simpl; rewrite applySubToC_app.
                                rewrite listVarInC_app.
                                destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
                                simpl in Hvar'.
                                destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
                                destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
                                destruct (app_eq_nil _ _ Hvar34) as [-> ->].
                                now destruct (app_eq_nil _ _ Hvar56) as [-> ->].
                   +++ case (clos_rel_term_dec (applySubstitution sigma ({{t3 | t4}})) (applySubstitution sigma t6)) as [? | ?].
                       *** exists ((t3 == t5)::((({{t3 | t4}}) == t6):: (c1' ++ c2'))).
                           split.
                           ---- apply step1.
                                apply stepEq9_2; try now apply eq_decompose.
                                rewrite Heqt4.
                                rewrite Heqt6.
                                now apply var_var.
                           ---- exists sigma.
                                split.
                                ++++ split; try assumption.
                                     split; try assumption.
                                     rewrite applySubToC_app.
                                     now rewrite interpretC_app.
                                ++++ simpl; rewrite applySubToC_app.
                                     rewrite listVarInC_app.
                                     destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
                                     simpl in Hvar'.
                                     destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
                                     destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
                                     destruct (app_eq_nil _ _ Hvar34) as [-> ->].
                                     now destruct (app_eq_nil _ _ Hvar56) as [-> ->].
                       *** case (clos_rel_term_dec (applySubstitution sigma t4) (applySubstitution sigma ({{t5 | t6}}))) as [? | ?].
                           ---- exists ((t3 == t5)::((t4 == ({{t5 | t6}})):: (c1' ++ c2'))).
                                split.
                                ++++ apply step1.
                                     apply stepEq9_3; try now apply eq_decompose.
                                     rewrite Heqt4.
                                     rewrite Heqt6.
                                     now apply var_var.
                                ++++ exists sigma.
                                     split.
                                     **** split; try assumption.
                                          split; try assumption.
                                          rewrite applySubToC_app.
                                          now rewrite interpretC_app.
                                     **** simpl; rewrite applySubToC_app.
                                          rewrite listVarInC_app.
                                          destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
                                          simpl in Hvar'.
                                          destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
                                          destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
                                          destruct (app_eq_nil _ _ Hvar34) as [-> ->].
                                          now destruct (app_eq_nil _ _ Hvar56) as [-> ->].
                           ---- absurd (applySubstitution sigma ({{t3 | t4}}) === applySubstitution sigma ({{t5 | t6}})); try assumption.
                                  now apply neg_inter_set.
               --- assert (HsetTerm6' : setTerm (applySubstitution sigma t6)).
                     trivial.
                   assert (HsetTerm4' : setTerm (applySubstitution sigma t4)).
                     trivial.
                   destruct (neg_inter_first_elem_exists HsetTerm4' HsetTerm6' Hneq_equiv HinterS) as [t [? ?]].
                   pose (u := FreshVarFun c1).
                   assert (Hfreshfstp1 : isFreshC u c1).
                     now apply FreshVarFun_isFresh.
                   assert (HnegIn34 : ~ In u (listVarInT ({{t3 | t4}}))).
                     intro Habs.
                     absurd (occurCheckC u c1); try assumption.
                     apply in_occurCheckC with (pc := ({{t3 | t4}}) == ({{t5 | t6}}));
                       try now left; apply In_listVarInT_occurCheck with (t := {{t3 | t4}}).
                     rewrite Heq.
                     apply in_or_app; right.
                     now apply in_eq.
                   assert (HnegIn56 : ~ In u (listVarInT ({{t5 | t6}}))).
                     intro Habs.
                     absurd (occurCheckC u c1); try assumption.
                     apply in_occurCheckC with (pc := ({{t3 | t4}}) == ({{t5 | t6}}));
                       try now right; apply In_listVarInT_occurCheck with (t := {{t5 | t6}}).
                     rewrite Heq.
                     apply in_or_app; right.
                     now apply in_eq.
                   assert (HnegIn3 : ~ In u (listVarInT t3)).
                     intros Habs.
                     absurd (In u (listVarInT ({{t3 | t4}}))); try assumption.
                     now apply in_or_app; left.
                   assert (HnegIn4 : ~ In u (listVarInT t4)).
                     intros Habs.
                     absurd (In u (listVarInT ({{t3 | t4}}))); try assumption.
                     now apply in_or_app; right.
                   assert (HnegIn5 : ~ In u (listVarInT t5)).
                     intros Habs.
                     absurd (In u (listVarInT ({{t5 | t6}}))); try assumption.
                     now apply in_or_app; left.
                   assert (HnegIn6 : ~ In u (listVarInT t6)).
                     intros Habs.
                     absurd (In u (listVarInT ({{t5 | t6}}))); try assumption.
                     now apply in_or_app; right.
                   assert (HfreshL34 : isFreshL u (t4 :: t3 :: nil)).
                     intro Habs.
                     case Habs as [? | Habs'];
                       try now absurd (In u (listVarInT t4)); [assumption | apply occurCheck_In_listVarInT].
                     case Habs' as [? | ?]; try trivial.
                     now absurd (In u (listVarInT t3)); [assumption | apply occurCheck_In_listVarInT].
                   assert (HfreshL56 : isFreshL u (t6 :: t5 :: nil)).
                     intro Habs.
                     case Habs as [? | Habs'];
                       try now absurd (In u (listVarInT t6)); [assumption | apply occurCheck_In_listVarInT].
                     case Habs' as [? | ?]; try trivial.
                     now absurd (In u (listVarInT t5)); [assumption | apply occurCheck_In_listVarInT].
                   assert (HnegIn1 : ~ In u (listVarInC c1')).
                     intro HIn'.
                     absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                     apply incl_occurCheckC with (c1 := c1'); try now apply In_listVarInC_occurCheckC.
                     rewrite Heq.
                     now apply incl_appl.
                   assert (HnegIn2 : ~ In u (listVarInC c2')).
                     intro HIn'.
                     absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                     apply incl_occurCheckC with (c1 := c2'); try now apply In_listVarInC_occurCheckC.
                     rewrite Heq.
                     apply incl_appr.
                     now apply incl_tl.
                   assert (HnegIn12 : ~ In u (listVarInC (c1' ++ c2'))).
                     intro HIn'.
                     absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
                     apply incl_occurCheckC with (c1 := c1' ++ c2'); try now apply In_listVarInC_occurCheckC.
                     rewrite Heq.
                     apply incl_app_app; try now apply incl_refl.
                     now apply incl_tl.
                   exists ((t4 == (SetC t5 (Var u))) :: ((SetC t3 (Var u)) == t6):: (IsSet (Var u))::(c1'++c2')).
                   split.
                   +++ apply step1.
                       apply stepEq9_4; try assumption.
                       *** now apply eq_decompose.
                       *** rewrite Heqt4.
                           rewrite Heqt6.
                           now apply var_var.
                   +++ exists ((u, t) :: sigma).
                       split.
                       *** split.
                           ---- simpl; rewrite neq_listVarInT_applySub; try assumption.
                                rewrite neq_listVarInT_applySub; try assumption.
                                now case (eq_variable_dec u u).
                           ---- split.
                                ++++ simpl; rewrite neq_listVarInT_applySub; try assumption.
                                     rewrite neq_listVarInT_applySub; try assumption.
                                     apply clos_rel_term_sym.
                                     now case (eq_variable_dec u u).
                                ++++ split.
                                     **** simpl; case (eq_variable_dec u u) as [_ | ?]; try contradiction.
                                          enough (setTerm  ({{applySubstitution sigma t5 | t}})).
                                            trivial.
                                          now apply clos_rel_term_setTerm with (t1 := applySubstitution sigma t4).
                                     **** rewrite neq_listVarInC_applySub; try assumption.
                                          rewrite applySubToC_app.
                                          now apply interpretC_app.
                       *** destruct (app_eq_nil _ _ Hvar) as [Hvar1 Hvar'].
                           simpl in Hvar'.
                           destruct (app_eq_nil _ _ Hvar') as [Hvar'' Hvar2].
                           destruct (app_eq_nil _ _ Hvar'') as [Hvar34 Hvar56].
                           assert (Hnil : listVarInT t = nil).
                             apply incl_l_nil.
                             destruct (app_eq_nil _ _ Hvar34) as [_ <-].
                             apply incl_tran with (m := listVarInT ({{applySubstitution sigma t5 | t}}));
                               try now apply incl_appr.
                             apply listVarInT_clos_rel_term.
                             now apply clos_rel_term_sym.
                           simpl; rewrite applySubToC_app.
                           rewrite listVarInC_app.
                           rewrite neq_listVarInT_applySub; try assumption.
                           rewrite neq_listVarInT_applySub; try assumption.
                           rewrite neq_listVarInT_applySub; try assumption.
                           rewrite neq_listVarInT_applySub; try assumption.
                           rewrite neq_listVarInC_applySub; try assumption.
                           rewrite neq_listVarInC_applySub; try assumption.
                           case (eq_variable_dec u u) as [_ | ?]; try contradiction.
                           rewrite Hvar1.
                           rewrite Hvar2.
                           destruct (app_eq_nil _ _ Hvar34) as [-> ->].
                           destruct (app_eq_nil _ _ Hvar56) as [-> ->].
                           now rewrite Hnil.
    * intros s lt _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      rewrite Heq in Hsat.
      destruct Hsat as [sigma [Hinter _]].
      rewrite applySubToC_app in Hinter.
      assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((({{t3 | t4}}) == OTerm s lt) :: c2'))).
        now apply interpretC_app.
      destruct Hand as [_ HinterOT2].
      destruct HinterOT2 as [HinterOT _].
      absurd (interpretPC (applySubstitutionToPC sigma (OTerm s lt == ({{t3 | t4}}))));
        try now apply clos_rel_term_sym.
      now apply clos_rel_term_SetC_OTerm.
    * intros _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      rewrite Heq in Hsat.
      destruct Hsat as [sigma [Hinter _]].
      rewrite applySubToC_app in Hinter.
      assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((({{t3 | t4}}) == EmptySet) :: c2'))).
        now apply interpretC_app.
      destruct Hand as [_ HinterE2].
      destruct HinterE2 as [HinterE _].
      assert (Habs: ({{applySubstitution sigma t3 | applySubstitution sigma t4}}) = EmptySet).
        now apply clos_rel_term_EmptySet.
      discriminate Habs.
  + intros s lt.
    case t2.
    * intros v _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      exists ((Var v == OTerm s lt) :: (c1' ++ c2')).
      split.
      -- apply step1.
         apply stepEq2; try now trivial.
         now apply eq_decompose.
      -- rewrite Heq in Hsat.
         destruct Hsat as [sigma [Hinter Hvar]].
         exists sigma.
         rewrite applySubToC_app in Hinter.
         rewrite applySubToC_app in Hvar.
         assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((OTerm s lt == Var v) :: c2'))).
           now apply interpretC_app.
         destruct Hand as [Hinter1 HinterOT2].
         destruct HinterOT2 as [HinterOT Hinter2].
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_app.
         split.
         ++ split; try now apply interpretC_app.
            now apply clos_rel_term_sym.
         ++ rewrite listVarInC_app.
            destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
            simpl in Hvar'.
            destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
            now destruct (app_eq_nil _ _ Hvar'') as [-> ->].
    * intros t3 t4 _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      rewrite Heq in Hsat.
      destruct Hsat as [sigma [Hinter _]].
      rewrite applySubToC_app in Hinter.
      assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((OTerm s lt == ({{t3 | t4}})) :: c2'))).
        now apply interpretC_app.
      destruct Hand as [_ HinterOT2].
      destruct HinterOT2 as [HinterOT _].
      absurd (interpretPC (applySubstitutionToPC sigma (OTerm s lt == ({{t3 | t4}}))));
        try assumption.
      now apply clos_rel_term_SetC_OTerm.
    * intros s' lt' _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      rewrite Heq in Hsat.
      destruct Hsat as [sigma [Hinter Hvar]].
      rewrite applySubToC_app in Hinter.
      assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((OTerm s lt == OTerm s' lt') :: c2'))).
        now apply interpretC_app.
      destruct Hand as [Hinter1 HinterOT2].
      destruct HinterOT2 as [HinterOT Hinter2].
      case (eq_symbol_dec s s') as [Hseq | Hnseq].
      -- rewrite <- Hseq in HinterOT.
         rewrite <- Hseq in HIn.
         rewrite <- Hseq in Heq.
         exists (((map2 buildEq lt lt') ++ (c1' ++ c2'))).
         split.
         ++ apply step1.
            apply stepEq8 with (f := s); try now apply eq_decompose.
            rewrite <- map_length with (f := (applySubstitution sigma)).
            rewrite <- map_length with (f := (applySubstitution sigma)) (l := lt').
            now apply (clos_rel_term_OTerm_length HinterOT).
         ++ exists sigma.
            unfold satisfies; simpl.
            do 2 rewrite applySubToC_app.
            split.
            ** apply interpretC_app.
               split; try now apply interpretC_app.
               apply interpret_buildEq with (s := s); try assumption.
               rewrite <- map_length with (f := applySubstitution sigma).
               rewrite <- map_length with (f := applySubstitution sigma) (l := lt').
               now apply clos_rel_term_OTerm_length with (s1 := s) (s2 := s).
            ** do 2 rewrite listVarInC_app.
               rewrite applySubToC_app in Hvar.
               rewrite listVarInC_app in Hvar.
               destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
               simpl in Hvar'.
               destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
               rewrite app_nil_r.
               apply incl_l_nil.
               rewrite <- Hvar''.
               now apply listVarIn_buildEq.
      -- absurd (s = s'); try assumption.
         now apply (clos_rel_term_OTerm_symbol HinterOT).
    * intros _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      rewrite Heq in Hsat.
      destruct Hsat as [sigma [Hinter _]].
      rewrite applySubToC_app in Hinter.
      assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((OTerm s lt == EmptySet) :: c2'))).
        now apply interpretC_app.
      destruct Hand as [_ HinterOT2].
      destruct HinterOT2 as [HinterOT _].
      assert (Habs: OTerm s (map (applySubstitution sigma) lt)  = EmptySet).
        now apply clos_rel_term_EmptySet.
      discriminate Habs.
  + case t2.
    * intros v _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      exists ((Var v == EmptySet) :: (c1' ++ c2')).
      split.
      -- apply step1.
         apply stepEq2; try now trivial.
         now apply eq_decompose.
      -- rewrite Heq in Hsat.
         destruct Hsat as [sigma [Hinter Hvar]].
         exists sigma.
         rewrite applySubToC_app in Hinter.
         rewrite applySubToC_app in Hvar.
         assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((EmptySet == Var v) :: c2'))).
           now apply interpretC_app.
         destruct Hand as [Hinter1 HinterE2].
         destruct HinterE2 as [HinterE Hinter2].
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_app.
         split.
         ++ split; try now apply interpretC_app.
            now apply clos_rel_term_sym.
         ++ rewrite listVarInC_app.
            destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
            simpl in Hvar'.
            now destruct (app_eq_nil _ _ Hvar') as [-> ->].
    * intros t3 t4 _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      rewrite Heq in Hsat.
      destruct Hsat as [sigma [Hinter _]].
      rewrite applySubToC_app in Hinter.
      assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((EmptySet == ({{t3 | t4}})) :: c2'))).
        now apply interpretC_app.
      destruct Hand as [_ HinterE2].
      destruct HinterE2 as [HinterE _].
      assert (Habs: {{applySubstitution sigma t3 | applySubstitution sigma t4}} = EmptySet).
        apply clos_rel_term_EmptySet.
        now apply clos_rel_term_sym.
      discriminate Habs.
    * intros s lt _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      rewrite Heq in Hsat.
      destruct Hsat as [sigma [Hinter _]].
      rewrite applySubToC_app in Hinter.
      assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((EmptySet == OTerm s lt) :: c2'))).
        now apply interpretC_app.
      destruct Hand as [_ HinterOT2].
      destruct HinterOT2 as [HinterOT _].
      assert (Habs: OTerm s (map (applySubstitution sigma) lt) = EmptySet).
        apply clos_rel_term_EmptySet.
        now apply clos_rel_term_sym.
      discriminate Habs.
    * intros _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      exists (c1'++c2').
      split.
      -- apply step1.
         apply stepEq1 with (t := EmptySet).
         now apply eq_decompose.
      -- rewrite Heq in Hsat.
         destruct Hsat as [sigma [Hinter Hvar]].
         exists sigma.
         rewrite applySubToC_app in Hinter.
         assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((EmptySet == EmptySet) :: c2'))).
           now apply interpretC_app.
         destruct Hand as [Hinter1 HinterE2].
         rewrite applySubToC_app in Hvar.
         destruct HinterE2 as [_ Hinter2].
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_app.
         split.
         ++ now apply interpretC_app.
         ++ rewrite listVarInC_app.
            simpl in Hvar.
            now destruct (app_eq_nil _ _ Hvar) as [-> ->].
- intros t1 t2.
  case t1.
  + intro v.
    case t2.
    * intros v' HnSF.
      case (eq_variable_dec v v') as [<- | ?]; try contradiction.
      intro HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      rewrite Heq in Hsat.
      destruct Hsat as [sigma [Hinter _]].
      rewrite applySubToC_app in Hinter.
      assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v \== Var v) :: c2'))).
        now apply interpretC_app.
      destruct Hand as [_ Hinterneq2].
      destruct Hinterneq2 as [Hinterneq _].
      absurd (applySubstitution sigma (Var v) === applySubstitution sigma (Var v));
        try assumption. 
      now apply clos_rel_term_refl.
    * intros t3 t4 HnSF HIn.
      case (occurCheck_dec v (LastFromSetC t4)) as [Hocc | Hnocc].
      -- case (dec_setTerm ({{t3 | t4}})) as [HsetTerm | HnsetTerm].
         ++ absurd (occurCheck v (LastFromSetC ({{t3 | t4}}))); try assumption.
            destruct (setTerm_exists_listSetC _ HsetTerm) as [lt ->].
            now elim lt.
         ++ destruct Hsat as [sigma [Hinter Hvar]].
            assert (Hincl : incl (set_inferPC (Var v \== ({{t3 | t4}}))) c1).
              now apply sort_complete_set_infer.
            assert (HsetTerm : setTerm (applySubstitution sigma ({{t3 | t4}}))).
              simpl in HnsetTerm.
              destruct (find_set_SetC_exist t3 _ HnsetTerm) as [t [HIn' Hforall_eq]].
              enough (He : interpretPC (applySubstitutionToPC sigma (IsSet ({{t3 | t4}})))).
                now trivial.
              rewrite Hforall_eq.
              assert (HIn'' : In (IsSet t) c1).
                now apply Hincl; apply in_or_app; right.
              destruct (in_split _ _ HIn'') as [c1' [c2' Heq]].
              rewrite Heq in Hinter.
              rewrite applySubToC_app in Hinter.
              assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ (interpretC (applySubstitutionToC sigma ((IsSet t) :: c2')))).
                now apply interpretC_app.
              destruct Hand as [_ HinterS2].
              now destruct HinterS2 as [? _].
            destruct (setTerm_negsetTerm_tail_exists_Var _ _ _ HsetTerm) as [v' Heq']; try assumption.
            destruct (tail_Var_exists t3 _ Heq') as [lt [Hneq_nil Heq2]].
            case (occurCheckList_dec v lt) as [? | ?].
            ** destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
               exists (c1'++c2').
               split.
               --- apply step3.
                   apply stepNeq6 with (X := v) (t := t3) (s := t4);
                     try now apply eq_decompose.
                   now rewrite (listSetC_SetCToList _ _ Heq2).
               --- rewrite Heq in Hinter.
                   rewrite Heq in Hvar.
                   rewrite applySubToC_app in Hinter.
                   assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v \== ({{t3 | t4}})) :: c2'))).
                     now apply interpretC_app.
                   destruct Hand as [Hinter1 HinterE2].
                   rewrite applySubToC_app in Hvar.
                   destruct HinterE2 as [_ Hinter2].
                   rewrite listVarInC_app in Hvar.
                   exists sigma.
                   unfold satisfies; simpl.
                   rewrite applySubToC_app.
                   split; try now apply interpretC_app.
                   rewrite listVarInC_app.
                   simpl in Hvar.
                   destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
                   now destruct (app_eq_nil _ _ Hvar') as [_ ->].
            ** assert (Hlast : LastFromSetC ({{t3 | t4}}) = Var v').
                 rewrite Heq2.
                 revert Hneq_nil.
                 elim lt; try contradiction.
                 intros t' lt'.
                 case lt'; try trivial.
                 intros ? ? Hind ?.
                 apply Hind.
                 now apply cons_neq_nil.
               simpl in Hlast.
               rewrite Hlast in Hocc.
               simpl in Hocc.
               rewrite <- Hocc in Heq2.
               rewrite Heq2 in HIn.
               destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
               rewrite Heq in Hinter.
               rewrite Heq in Hvar.
               rewrite applySubToC_app in Hinter.
               assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v \== listSetC lt (Var v)) :: c2'))).
                 now apply interpretC_app.
               destruct Hand as [Hinter1 HinterE2].
               rewrite applySubToC_app in Hvar.
               destruct HinterE2 as [HinterE Hinter2].
               rewrite listVarInC_app in Hvar.
               assert (Hneq_nil' : map (applySubstitution sigma) lt <> nil).
                 intro Habs.
                 absurd (lt = nil); try assumption.
                 now apply (map_eq_nil _ _ Habs).
               assert (HexistsIn : exists t, In t (map (applySubstitution sigma) lt) /\ interpretPC ((t \:s applySubstitution sigma (Var v)))).
                 apply Exists_exists.
                 apply (Exists_Forall_neg _ _ (dec_mem (applySubstitution sigma (Var v)))).
                 intro Hforall.
                 absurd (interpretPC (applySubstitutionToPC sigma (Var v == listSetC lt (Var v)))); try assumption.
                   simpl; rewrite applySub_listSetC.
                   apply inset_eqlistSetC; try assumption.
                   now apply Forall_forall.
               destruct HexistsIn as [mtj [HIn' ?]].
               assert (Hexists : exists tj, (applySubstitution sigma) tj = mtj /\ In tj lt).
                 now apply in_map_iff.
               destruct Hexists as [tj [Heq3 HIn'']].
               rewrite <- Heq3 in H.
               exists ((tj \:s (Var v)) :: (c1'++c2')).
               split.
               --- apply step3.
                   destruct (In_nth_error _ _ HIn'') as [j ?].
                   apply stepNeq7 with (lt := lt) (j := j); try assumption.
                   now apply eq_decompose.
               --- exists sigma.
                   split; simpl; rewrite applySubToC_app.
                   +++ split; try assumption.
                       now apply interpretC_app.
                   +++ rewrite listVarInC_app.
                       destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
                       simpl in Hvar'.
                       destruct (app_eq_nil _ _ Hvar') as [Hvarvlt ->].
                       destruct (app_eq_nil _ _ Hvarvlt) as [-> Hvarlt].
                       do 2 rewrite app_nil_r.
                       rewrite applySub_listSetC in Hvarlt.
                       assert (Hand : (forall t' : term, In t' (map (applySubstitution sigma) lt) -> listVarInT t' = nil) /\ listVarInT (applySubstitution sigma (Var v)) = nil).
                         now apply (listVarIn_listSetC_nil _ Hneq_nil').
                       destruct Hand as [Hforall _].
                       apply Hforall.
                       now apply in_map.
      -- destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
         exists (c1'++c2').
         split.
         ++ apply step3.
            apply stepNeq6 with (X := v) (t := t3) (s := t4);
              try now apply eq_decompose.
            assert (Hor : occurCheck v t3 \/ occurCheck v t4).
              apply Decidable.not_not; try assumption.
              now apply Decidable.dec_or;
                 [case (occurCheck_dec v t3) as [? | ?]; [left | right] |
                  case (occurCheck_dec v t4) as [? | ?]; [left | right]].
            case Hor as [? | Hocc4]; try now left.
            now right; apply occurCheckList_listElements.
         ++ rewrite Heq in Hsat.
            destruct Hsat as [sigma [Hinter Hvar]].
            exists sigma.
            rewrite applySubToC_app in Hinter.
            assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v \== ({{t3 | t4}})) :: c2'))).
              now apply interpretC_app.
            destruct Hand as [Hinter1 HinterE2].
            rewrite applySubToC_app in Hvar.
            destruct HinterE2 as [_ Hinter2].
            rewrite listVarInC_app in Hvar.
            unfold satisfies; simpl.
            rewrite applySubToC_app.
            split.
            ** now apply interpretC_app.
            ** rewrite listVarInC_app.
               simpl in Hvar.
               destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
               now destruct (app_eq_nil _ _ Hvar') as [_ ->].
    * intros s lt HnSF HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      exists (c1'++c2').
      split.
      -- apply step3.
         apply stepNeq5 with (X := v) (f := s) (l := lt);
           try now apply eq_decompose.
         apply Decidable.not_not; try assumption.
         now case (occurCheckList_dec v lt) as [? | ?]; [left | right].
      -- rewrite Heq in Hsat.
         destruct Hsat as [sigma [Hinter Hvar]].
         exists sigma.
         rewrite applySubToC_app in Hinter.
         assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((Var v \== OTerm s lt) :: c2'))).
           now apply interpretC_app.
         destruct Hand as [Hinter1 HinterOT2].
         rewrite applySubToC_app in Hvar.
         destruct HinterOT2 as [_ Hinter2].
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_app.
         split.
         ++ now apply interpretC_app.
         ++ rewrite listVarInC_app.
            simpl in Hvar.
            destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
            now destruct (app_eq_nil _ _ Hvar') as [_ ->].
    * intros ?.
      absurd (~ False); try assumption.
      intro; contradiction.
  + intros t3 t4 _.
    case t2.
    * intros v HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      exists ((Var v \== ({{t3 | t4}})) :: (c1' ++ c2')).
      split.
      -- apply step3.
         apply stepNeq4; try now trivial.
         now apply eq_decompose.
      -- rewrite Heq in Hsat.
         destruct Hsat as [sigma [Hinter Hvar]].
         exists sigma.
         rewrite applySubToC_app in Hinter.
         rewrite applySubToC_app in Hvar.
         assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((({{t3 | t4}}) \== Var v) :: c2'))).
           now apply interpretC_app.
         destruct Hand as [Hinter1 HinterS2].
         destruct HinterS2 as [HinterS Hinter2].
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_app.
         split.
         ++ split; try now apply interpretC_app.
            intro Habs.
            absurd (interpretPC (applySubstitutionToPC sigma (({{t3 | t4}}) == Var v)));
              try assumption.
            now apply clos_rel_term_sym.
         ++ rewrite listVarInC_app.
            destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
            simpl in Hvar'.
            destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
            now destruct (app_eq_nil _ _ Hvar'') as [-> ->].
    * intros t5 t6 HIn.
      assert (Hincl : incl (set_inferPC (({{t3 | t4}}) \== ({{t5 | t6}}))) c1).
        now apply sort_complete_set_infer.
      destruct Hsat as [sigma [Hinter Hvar]].
      assert (HsetTerm4 : setTerm (applySubstitution sigma t4)).
        case (dec_setTerm t4) as [? | HnsetTerm]; try now apply setTerm_applySub.
        destruct (find_set_SetC_exist t3 _ HnsetTerm) as [t [HIn' Hforall_eq]].
        enough (He : interpretPC (applySubstitutionToPC sigma (IsSet ({{t3 | t4}})))).
          now trivial.
        rewrite Hforall_eq.
        assert (HIn'' : In (IsSet t) c1).
          apply Hincl.
          apply in_or_app.
          now left.
        destruct (in_split _ _ HIn'') as [c1' [c2' Heq]].
        rewrite Heq in Hinter.
        rewrite applySubToC_app in Hinter.
        assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ (interpretC (applySubstitutionToC sigma ((IsSet t) :: c2')))).
          now apply interpretC_app.
        destruct Hand as [_ HinterS2].
        now destruct HinterS2 as [? _].
      assert (HsetTerm6 : setTerm (applySubstitution sigma t6)).
        case (dec_setTerm t6) as [? | HnsetTerm]; try now apply setTerm_applySub.
        destruct (find_set_SetC_exist t5 _ HnsetTerm) as [t [HIn' Hforall_eq]].
        enough (He : interpretPC (applySubstitutionToPC sigma (IsSet ({{t5 | t6}})))).
          now trivial.
        rewrite Hforall_eq.
        assert (HIn'' : In (IsSet t) c1).
          apply Hincl.
          apply in_or_app.
          now right.
        destruct (in_split _ _ HIn'') as [c1' [c2' Heq]].
        rewrite Heq in Hinter.
        rewrite applySubToC_app in Hinter.
        assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ (interpretC (applySubstitutionToC sigma ((IsSet t) :: c2')))).
          now apply interpretC_app.
        destruct Hand as [_ HinterS2].
        now destruct HinterS2 as [? _].
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      rewrite Heq in Hinter.
      rewrite Heq in Hvar.
      rewrite applySubToC_app in Hinter.
      rewrite applySubToC_app in Hvar.
      assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((({{t3 | t4}}) \== ({{t5 | t6}})) :: c2'))).
        now apply interpretC_app.
      destruct Hand as [Hinter1 HinterS2].
      destruct HinterS2 as [HinterS Hinter2].
      simpl in HinterS.
      assert (HsetTerm4' : setTerm ({{applySubstitution sigma t3 | applySubstitution sigma t4}})).
        trivial.
      assert (HsetTerm6' : setTerm ({{applySubstitution sigma t5 | applySubstitution sigma t6}})).
        trivial.
      destruct (neq_set_exists HsetTerm4' HsetTerm6' HinterS) as [t Hor].
      pose (u := FreshVarFun c1).
      assert (Hfreshfstp1 : isFreshC u c1).
        now apply FreshVarFun_isFresh.
      assert (HnegIn34 : ~ In u (listVarInT ({{t3 | t4}}))).
        intro Habs.
        absurd (occurCheckC u c1); try assumption.
        apply in_occurCheckC with (pc := ({{t3 | t4}}) \== ({{t5 | t6}}));
          try now left; apply In_listVarInT_occurCheck with (t := {{t3 | t4}}).
        rewrite Heq.
        apply in_or_app; right.
        now apply in_eq.
      assert (HnegIn56 : ~ In u (listVarInT ({{t5 | t6}}))).
        intro Habs.
        absurd (occurCheckC u c1); try assumption.
        apply in_occurCheckC with (pc := ({{t3 | t4}}) \== ({{t5 | t6}}));
          try now right; apply In_listVarInT_occurCheck with (t := {{t5 | t6}}).
        rewrite Heq.
        apply in_or_app; right.
        now apply in_eq.
      assert (HnegIn3 : ~ In u (listVarInT t3)).
        intros Habs.
        absurd (In u (listVarInT ({{t3 | t4}}))); try assumption.
        now apply in_or_app; left.
      assert (HnegIn4 : ~ In u (listVarInT t4)).
        intros Habs.
        absurd (In u (listVarInT ({{t3 | t4}}))); try assumption.
        now apply in_or_app; right.
      assert (HnegIn5 : ~ In u (listVarInT t5)).
        intros Habs.
        absurd (In u (listVarInT ({{t5 | t6}}))); try assumption.
        now apply in_or_app; left.
      assert (HnegIn6 : ~ In u (listVarInT t6)).
        intros Habs.
        absurd (In u (listVarInT ({{t5 | t6}}))); try assumption.
        now apply in_or_app; right.
      assert (HfreshL34 : isFreshL u (t4 :: t3 :: nil)).
        intro Habs.
        case Habs as [? | Habs'];
          try now absurd (In u (listVarInT t4)); [assumption | apply occurCheck_In_listVarInT].
        case Habs' as [? | ?]; try trivial.
        now absurd (In u (listVarInT t3)); [assumption | apply occurCheck_In_listVarInT].
      assert (HfreshL56 : isFreshL u (t6 :: t5 :: nil)).
        intro Habs.
        case Habs as [? | Habs'];
          try now absurd (In u (listVarInT t6)); [assumption | apply occurCheck_In_listVarInT].
        case Habs' as [? | ?]; try trivial.
        now absurd (In u (listVarInT t5)); [assumption | apply occurCheck_In_listVarInT].
      assert (HnegIn1 : ~ In u (listVarInC c1')).
        intro HIn'.
        absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
        apply incl_occurCheckC with (c1 := c1'); try now apply In_listVarInC_occurCheckC.
        rewrite Heq.
        now apply incl_appl.
      assert (HnegIn2 : ~ In u (listVarInC c2')).
        intro HIn'.
        absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
        apply incl_occurCheckC with (c1 := c2'); try now apply In_listVarInC_occurCheckC.
        rewrite Heq.
        apply incl_appr.
        now apply incl_tl.
      assert (HnegIn12 : ~ In u (listVarInC (c1' ++ c2'))).
        intro HIn'.
        absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
        apply incl_occurCheckC with (c1 := c1' ++ c2'); try now apply In_listVarInC_occurCheckC.
        rewrite Heq.
        apply incl_app_app; try now apply incl_refl.
        now apply incl_tl.
      case Hor as [Hand | Hand]; destruct Hand as [[? [t' [? ?]]] ?].
      -- rewrite listVarInC_app in Hvar.
         destruct (app_eq_nil _ _ Hvar) as [Hvar1 Hvar'].
         simpl in Hvar'.
         destruct (app_eq_nil _ _ Hvar') as [Hvar'' Hvar2].
         assert (Hnil : listVarInT (applySubstitution sigma ({{t3 | t4}})) = nil).
           destruct (app_eq_nil _ _ Hvar'') as [Hnil _].
           now simpl; destruct (app_eq_nil _ _ Hnil) as [-> ->].
         assert (Hnil' : listVarInT t' = nil).
           apply listVarInListT_eq_nil with (lt := (listElements (applySubstitution sigma ({{t3 | t4}})))); try assumption.
           apply incl_l_nil.
           rewrite <- Hnil.
           now apply incl_listVar_listElements.
         assert (Hnil'' : listVarInT t = nil).
           apply incl_l_nil.
           rewrite <- Hnil'.
           apply listVarInT_clos_rel_term.
           now apply clos_rel_term_sym.
         assert (Heq' : applySubstitution ((u, t) :: sigma) (Var u) = t).
           rewrite <- (listVarInT_nil_applySub sigma _ Hnil'').
           rewrite <- applySub_cons.
           now simpl; case (eq_variable_dec u u).
         exists (((Var u) :s (SetC t3 t4))::((Var u) \:s (SetC t5 t6))::(c1' ++ c2')).
         split.
         ++ apply step3.
            apply stepNeq8_1; try assumption.
            now apply eq_decompose.
         ++ exists ((u, t) :: sigma).
            split.
            ** split.
               --- split; try now rewrite neq_listVarInT_applySub.
                   exists t'.
                   split; try now rewrite Heq'.
                   now rewrite neq_listVarInT_applySub.
               --- split.
                   +++ intros [Habs [t'' Habs']].
                       absurd (interpretPC (t :s applySubstitution sigma ({{t5 | t6}}))); try assumption.
                       split; try now rewrite neq_listVarInT_applySub in Habs.
                       exists t''.
                       rewrite Heq' in Habs'.
                       now rewrite neq_listVarInT_applySub in Habs'.
                   +++ rewrite neq_listVarInC_applySub; try assumption.
                       rewrite applySubToC_app.
                       now apply interpretC_app.
            ** simpl; rewrite applySubToC_app.
               rewrite listVarInC_app.
               rewrite neq_listVarInT_applySub; try assumption.
               rewrite neq_listVarInT_applySub; try assumption.
               rewrite neq_listVarInT_applySub; try assumption.
               rewrite neq_listVarInT_applySub; try assumption.
               rewrite neq_listVarInC_applySub; try assumption.
               rewrite neq_listVarInC_applySub; try assumption.
               destruct (app_eq_nil _ _ Hvar'') as [-> ->].
               case (eq_variable_dec u u) as [? | ?]; try contradiction.
               rewrite Hvar1.
               rewrite Hvar2.
               now rewrite Hnil''.
      -- rewrite listVarInC_app in Hvar.
         destruct (app_eq_nil _ _ Hvar) as [Hvar1 Hvar'].
         simpl in Hvar'.
         destruct (app_eq_nil _ _ Hvar') as [Hvar'' Hvar2].
         assert (Hnil : listVarInT (applySubstitution sigma ({{t5 | t6}})) = nil).
           destruct (app_eq_nil _ _ Hvar'') as [_ Hnil].
           now simpl; destruct (app_eq_nil _ _ Hnil) as [-> ->].
         assert (Hnil' : listVarInT t' = nil).
           apply listVarInListT_eq_nil with (lt := (listElements (applySubstitution sigma ({{t5 | t6}})))); try assumption.
           apply incl_l_nil.
           rewrite <- Hnil.
           now apply incl_listVar_listElements.
         assert (Hnil'' : listVarInT t = nil).
           apply incl_l_nil.
           rewrite <- Hnil'.
           apply listVarInT_clos_rel_term.
           now apply clos_rel_term_sym.
         assert (Heq' : applySubstitution ((u, t) :: sigma) (Var u) = t).
           rewrite <- (listVarInT_nil_applySub sigma _ Hnil'').
           rewrite <- applySub_cons.
           now simpl; case (eq_variable_dec u u).
         exists (((Var u) :s (SetC t5 t6))::((Var u) \:s (SetC t3 t4))::(c1' ++ c2')).
         split.
         ++ apply step3.
            apply stepNeq8_2; try try assumption.
            now apply eq_decompose.
         ++ exists ((u, t) :: sigma).
            split.
            ** split.
               --- split; try now rewrite neq_listVarInT_applySub.
                   exists t'.
                   split; try now rewrite Heq'.
                   now rewrite neq_listVarInT_applySub.
               --- split.
                   +++ intros [Habs [t'' Habs']].
                       absurd (interpretPC (t :s applySubstitution sigma ({{t3 | t4}}))); try assumption.
                       split; try now rewrite neq_listVarInT_applySub in Habs.
                       exists t''.
                       rewrite Heq' in Habs'.
                       now rewrite neq_listVarInT_applySub in Habs'.
                   +++ rewrite neq_listVarInC_applySub; try assumption.
                       rewrite applySubToC_app.
                       now apply interpretC_app.
            ** simpl; rewrite applySubToC_app.
               rewrite listVarInC_app.
               rewrite neq_listVarInT_applySub; try assumption.
               rewrite neq_listVarInT_applySub; try assumption.
               rewrite neq_listVarInT_applySub; try assumption.
               rewrite neq_listVarInT_applySub; try assumption.
               rewrite neq_listVarInC_applySub; try assumption.
               rewrite neq_listVarInC_applySub; try assumption.
               destruct (app_eq_nil _ _ Hvar'') as [-> ->].
               case (eq_variable_dec u u) as [? | ?]; try contradiction.
               rewrite Hvar1.
               rewrite Hvar2.
               now rewrite Hnil''.
    * intros s lt HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      exists (c1'++c2').
      split.
      -- apply step3.
         apply stepNeq1 with (t2 := OTerm s lt) (t1 := ({{t3 | t4}}));
           try now apply eq_decompose.
         right; right; right; left.
         split.
         ++ now exists t3; exists t4.
         ++ now exists s; exists lt.
      -- rewrite Heq in Hsat.
         destruct Hsat as [sigma [Hinter Hvar]].
         exists sigma.
         rewrite applySubToC_app in Hinter.
         assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((({{t3 | t4}}) \== OTerm s lt) :: c2'))).
           now apply interpretC_app.
         destruct Hand as [Hinter1 HinterOT2].
         rewrite applySubToC_app in Hvar.
         destruct HinterOT2 as [_ Hinter2].
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_app.
         split.
         ++ now apply interpretC_app.
         ++ rewrite listVarInC_app.
            simpl in Hvar.
            destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
            now destruct (app_eq_nil _ _ Hvar') as [_ ->].
    * intros HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      exists (c1'++c2').
      split.
      -- apply step3.
         apply stepNeq1 with (t2 := EmptySet) (t1 := ({{t3 | t4}}));
           try now apply eq_decompose.
         right; right; right; right; right; right.
         split; try trivial.
         now exists t3; exists t4.
      -- rewrite Heq in Hsat.
         destruct Hsat as [sigma [Hinter Hvar]].
         exists sigma.
         rewrite applySubToC_app in Hinter.
         assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((({{t3 | t4}}) \== EmptySet) :: c2'))).
           now apply interpretC_app.
         destruct Hand as [Hinter1 HinterOT2].
         rewrite applySubToC_app in Hvar.
         destruct HinterOT2 as [_ Hinter2].
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_app.
         split.
         ++ now apply interpretC_app.
         ++ rewrite listVarInC_app.
            simpl in Hvar.
            destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
            now destruct (app_eq_nil _ _ Hvar') as [_ ->].
  + intros s lt.
    case t2.
    * intros v _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      exists ((Var v \== OTerm s lt) :: (c1' ++ c2')).
      split.
      -- apply step3.
         apply stepNeq4; try now trivial.
         now apply eq_decompose.
      -- rewrite Heq in Hsat.
         destruct Hsat as [sigma [Hinter Hvar]].
         exists sigma.
         rewrite applySubToC_app in Hinter.
         rewrite applySubToC_app in Hvar.
         assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((OTerm s lt \== Var v) :: c2'))).
           now apply interpretC_app.
         destruct Hand as [Hinter1 HinterOT2].
         destruct HinterOT2 as [HinterOT Hinter2].
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_app.
         split.
         ++ split; try now apply interpretC_app.
            intro Habs.
            absurd (interpretPC (applySubstitutionToPC sigma (OTerm s lt == Var v)));
              try assumption.
            now apply clos_rel_term_sym.
         ++ rewrite listVarInC_app.
            destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
            simpl in Hvar'.
            destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
            now destruct (app_eq_nil _ _ Hvar'') as [-> ->].
    * intros t3 t4  _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      exists (c1'++c2').
      split.
      -- apply step3.
         apply stepNeq1 with (t1 := OTerm s lt) (t2 := ({{t3 | t4}}));
           try now apply eq_decompose.
         right; right; right; right; left.
         split.
         ++ now exists s; exists lt.
         ++ now exists t3; exists t4.
      -- rewrite Heq in Hsat.
         destruct Hsat as [sigma [Hinter Hvar]].
         exists sigma.
         rewrite applySubToC_app in Hinter.
         assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((OTerm s lt \== ({{t3 | t4}})) :: c2'))).
           now apply interpretC_app.
         destruct Hand as [Hinter1 HinterOT2].
         rewrite applySubToC_app in Hvar.
         destruct HinterOT2 as [_ Hinter2].
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_app.
         split; try now apply interpretC_app.
         rewrite listVarInC_app.
         simpl in Hvar.
         destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
         now destruct (app_eq_nil _ _ Hvar') as [_ ->].
    * intros s' lt' _.
      case (eq_symbol_dec s s') as [<- | Hneqs]; intro HIn.
      -- case (eq_nat_dec (length lt) (length lt')) as [Heq_l | ?].
         ++ destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
            rewrite Heq in Hsat.
            destruct Hsat as [sigma [Hinter Hvar]].
            rewrite applySubToC_app in Hinter.
            assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((OTerm s lt \== OTerm s lt') :: c2'))).
              now apply interpretC_app.
            destruct Hand as [Hinter1 HinterOT2].
            destruct HinterOT2 as [? Hinter2].
            assert (Hexists : exists j, j < length (map (applySubstitution sigma) lt) /\ interpretPC ((nth j (map (applySubstitution sigma) lt) EmptySet) \==  (nth j (map (applySubstitution sigma) lt') EmptySet))).
              apply neg_inter_OTerm_exists with (s := s); try assumption.
              now do 2 rewrite map_length.
            destruct Hexists as [j [Hlength HinterPC]].
            rewrite map_length in Hlength.
            exists ((nth j lt EmptySet \== nth j lt' EmptySet) :: c1' ++ c2').
            split.
            ** apply step3.
               apply stepNeq2 with (f := s) (l1 := lt) (l2 := lt') (j := j);
                 try now apply eq_decompose.
               --- now apply nth_error_nth'.
               --- apply nth_error_nth'.
                   now rewrite <- Heq_l.
            ** exists sigma.
               unfold satisfies; simpl.
               rewrite applySubToC_app.
               split.
               --- split; try now apply interpretC_app.
                   rewrite <- map_nth.
                   now rewrite <- map_nth with (l := lt').
               --- rewrite applySubToC_app in Hvar.
                   rewrite listVarInC_app in Hvar.
                   rewrite listVarInC_app.
                   simpl in Hvar.
                   destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
                   destruct (app_eq_nil _ _ Hvar') as [Hvarlt ->].
                   destruct (app_eq_nil _ _ Hvarlt) as [Hvarl Hvarl'].
                   enough (He : listVarInT (applySubstitution sigma (nth j lt EmptySet)) = nil
                            /\ listVarInT (applySubstitution sigma (nth j lt' EmptySet)) = nil).
                     now destruct He as [-> ->].
                   split; apply incl_l_nil.
                   +++ apply incl_tran with (m := listVarInListT (map (applySubstitution sigma) lt)); try now rewrite <- Hvarl.
                       apply incl_listVarInT_listVarInListT.
                       apply in_map.
                       now apply nth_In.
                   +++ apply incl_tran with (m := listVarInListT (map (applySubstitution sigma) lt')); try now rewrite <- Hvarl'.
                       apply incl_listVarInT_listVarInListT.
                       apply in_map.
                       apply nth_In.
                       now rewrite <- Heq_l.
         ++ destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
            exists (c1'++c2').
            split.
            ** apply step3.
               apply stepNeq1 with (t1 := OTerm s lt) (t2 := OTerm s lt');
                 try now apply eq_decompose.
               left.
               exists s; exists lt; exists s; exists lt'.
               split; try trivial.
               split; try trivial.
               now right.
            ** rewrite Heq in Hsat.
               destruct Hsat as [sigma [Hinter Hvar]].
               exists sigma.
               rewrite applySubToC_app in Hinter.
               assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((OTerm s lt \== OTerm s lt') :: c2'))).
                 now apply interpretC_app.
               destruct Hand as [Hinter1 HinterOT2].
               rewrite applySubToC_app in Hvar.
               destruct HinterOT2 as [_ Hinter2].
               rewrite listVarInC_app in Hvar.
               unfold satisfies; simpl.
               rewrite applySubToC_app.
               split.
               --- now apply interpretC_app.
               --- rewrite listVarInC_app.
                   simpl in Hvar.
                   destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
                   now destruct (app_eq_nil _ _ Hvar') as [_ ->].
      -- destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
         exists (c1'++c2').
         split.
         ++ apply step3.
            apply stepNeq1 with (t1 := OTerm s lt) (t2 := OTerm s' lt');
              try now apply eq_decompose.
            left.
            exists s; exists lt; exists s'; exists lt'.
            split; try trivial.
            split; try trivial.
            now left.
         ++ rewrite Heq in Hsat.
            destruct Hsat as [sigma [Hinter Hvar]].
            exists sigma.
            rewrite applySubToC_app in Hinter.
            assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((OTerm s lt \== OTerm s' lt') :: c2'))).
              now apply interpretC_app.
            destruct Hand as [Hinter1 HinterOT2].
            rewrite applySubToC_app in Hvar.
            destruct HinterOT2 as [_ Hinter2].
            rewrite listVarInC_app in Hvar.
            unfold satisfies; simpl.
            rewrite applySubToC_app.
            split; try now apply interpretC_app.
            rewrite listVarInC_app.
            simpl in Hvar.
            destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
            now destruct (app_eq_nil _ _ Hvar') as [_ ->].
    * intros _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      exists (c1'++c2').
      split.
      -- apply step3.
         apply stepNeq1 with (t2 := EmptySet) (t1 := OTerm s lt);
           try now apply eq_decompose.
         right; right; left.
         split; try trivial.
         now exists s; exists lt.
      -- rewrite Heq in Hsat.
         destruct Hsat as [sigma [Hinter Hvar]].
         exists sigma.
         rewrite applySubToC_app in Hinter.
         assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((OTerm s lt \== EmptySet) :: c2'))).
           now apply interpretC_app.
         destruct Hand as [Hinter1 HinterOT2].
         rewrite applySubToC_app in Hvar.
         destruct HinterOT2 as [_ Hinter2].
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_app.
         split; try now apply interpretC_app.
         rewrite listVarInC_app.
         simpl in Hvar.
         destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
         now destruct (app_eq_nil _ _ Hvar') as [_ ->].
  + case t2.
    * intros v _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      exists ((Var v \== EmptySet) :: (c1' ++ c2')).
      split.
      -- apply step3.
         apply stepNeq4; try now trivial.
         now apply eq_decompose.
      -- rewrite Heq in Hsat.
         destruct Hsat as [sigma [Hinter Hvar]].
         exists sigma.
         rewrite applySubToC_app in Hinter.
         rewrite applySubToC_app in Hvar.
         assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((EmptySet \== Var v) :: c2'))).
           now apply interpretC_app.
         destruct Hand as [Hinter1 HinterE2].
         destruct HinterE2 as [HinterE Hinter2].
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_app.
         split.
         ++ split; try now apply interpretC_app.
            intro Habs.
            absurd (interpretPC (applySubstitutionToPC sigma (EmptySet == Var v)));
              try assumption.
            now apply clos_rel_term_sym.
         ++ rewrite listVarInC_app.
            destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
            simpl in Hvar'.
            now destruct (app_eq_nil _ _ Hvar') as [-> ->].
    * intros t3 t4 _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      exists (c1'++c2').
      split.
      -- apply step3.
         apply stepNeq1 with (t1 := EmptySet) (t2 := ({{t3 | t4}}));
           try now apply eq_decompose.
         right; right; right; right; right; left.
         split; try trivial.
         now exists t3; exists t4.
      -- rewrite Heq in Hsat.
         destruct Hsat as [sigma [Hinter Hvar]].
         exists sigma.
         rewrite applySubToC_app in Hinter.
         assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((EmptySet \== ({{t3 | t4}})) :: c2'))).
           now apply interpretC_app.
         destruct Hand as [Hinter1 HinterOT2].
         rewrite applySubToC_app in Hvar.
         destruct HinterOT2 as [_ Hinter2].
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_app.
         split; try now apply interpretC_app.
         rewrite listVarInC_app.
         simpl in Hvar.
         destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
         now destruct (app_eq_nil _ _ Hvar') as [_ ->].
    * intros s lt _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      exists (c1'++c2').
      split.
      -- apply step3.
         apply stepNeq1 with (t1 := EmptySet) (t2 := OTerm s lt);
           try now apply eq_decompose.
         right; left.
         split; try trivial.
         now exists s; exists lt.
      -- rewrite Heq in Hsat.
         destruct Hsat as [sigma [Hinter Hvar]].
         exists sigma.
         rewrite applySubToC_app in Hinter.
         assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((EmptySet \== OTerm s lt) :: c2'))).
           now apply interpretC_app.
         destruct Hand as [Hinter1 HinterOT2].
         rewrite applySubToC_app in Hvar.
         destruct HinterOT2 as [_ Hinter2].
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_app.
         split; try now apply interpretC_app.
         rewrite listVarInC_app.
         simpl in Hvar.
         destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
         now destruct (app_eq_nil _ _ Hvar') as [_ ->].
    * intros _ HIn.
      destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
      rewrite Heq in Hsat.
      destruct Hsat as [sigma [Hinter _]].
      rewrite applySubToC_app in Hinter.
      assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((EmptySet \== EmptySet) :: c2'))).
        now apply interpretC_app.
      destruct Hand as [_ Hinterneq2].
      destruct Hinterneq2 as [Hinterneq _].
      absurd (applySubstitution sigma EmptySet === applySubstitution sigma EmptySet);
        try assumption.
      now apply clos_rel_term_refl.
- intros t1 t2.
  case t2.
  + intros v _ HIn.
    pose (u := FreshVarFun c1).
    assert (isFreshC u c1).
      now apply FreshVarFun_isFresh.
    destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
    assert (isFreshT u t1).
      intro Habs.
      absurd (occurCheckC u c1); try assumption.
      apply in_occurCheckC with (pc := t1 :s Var v); try now left.
      rewrite Heq.
      apply in_or_app; right.
      now apply in_eq.
    assert (Hneq : u <> v).
      intro Habs.
      absurd (occurCheckC u c1); try assumption.
      apply In_listVarInC_occurCheckC.
      rewrite Habs.
      rewrite Heq.
      rewrite listVarInC_app.
      apply in_or_app; right.
      apply in_or_app; left.
      apply in_or_app; right.
      now apply in_eq.
    assert (~ In u (listVarInC c1')).
      intro HIn'.
      absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
      apply incl_occurCheckC with (c1 := c1'); try now apply In_listVarInC_occurCheckC.
      rewrite Heq.
      now apply incl_appl.
    assert (~ In u (listVarInC c2')).
      intro HIn'.
      absurd (occurCheckC u c1); try now apply FreshVarFun_isFresh.
      apply incl_occurCheckC with (c1 := c2'); try now apply In_listVarInC_occurCheckC.
      rewrite Heq.
      apply incl_appr.
      now apply incl_tl.
    assert (~ In u (listVarInT t1)).
      intro Habs.
      absurd (occurCheck u t1); try assumption.
      now apply In_listVarInT_occurCheck.
    rewrite Heq in Hsat.
    exists ((c1' ++ c2') ++ ((Var v == SetC t1 (Var u)) :: (IsSet (Var u)) :: nil)).
    split.
    * apply step2.
      apply stepMem3; try assumption.
      now apply eq_decompose.
    * destruct Hsat as [sigma [Hinter Hvar]].
      rewrite applySubToC_app in Hinter.
      rewrite applySubToC_app in Hvar.
      assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((t1 :s Var v) :: c2'))).
        now apply interpretC_app.
      destruct Hand as [Hinter1 HinterMem2].
      destruct HinterMem2 as [HinterMem Hinter2].
      destruct HinterMem as [? ?].
      rewrite listVarInC_app in Hvar.
      exists ((u , applySubstitution sigma (Var v)) :: sigma).
      unfold satisfies; simpl.
      rewrite applySubToC_app.
      split.
      -- rewrite applySubToC_app.
         apply interpretC_app.
         split.
         ++ apply interpretC_app.
            split; rewrite neq_listVarInC_applySub; try assumption.
         ++ simpl; case (eq_variable_dec v u) as [Heq' | ?]; try now rewrite Heq' in Hneq.
            split.
            ** case (eq_variable_dec u u) as [? | ?]; try contradiction.
               rewrite neq_listVarInT_applySub; try assumption.
               now apply inset_eqset.
            ** split; try trivial.
               now case (eq_variable_dec u u) as [? | ?].
      -- rewrite listVarInC_app.
         rewrite applySubToC_app.
         rewrite neq_listVarInC_applySub; try assumption.
         rewrite neq_listVarInC_applySub; try assumption.
         rewrite listVarInC_app.
         destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
         simpl in Hvar'.
         destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
         simpl; rewrite neq_listVarInT_applySub; try assumption.
         case (eq_variable_dec v u) as [Heq' | ?]; try now rewrite Heq' in Hneq.
         now case (eq_variable_dec u u) as [? | ?]; try destruct (app_eq_nil _ _ Hvar'') as [-> ->].
  + intros t3 t4 _ HIn.
    destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
    rewrite Heq in Hsat.
    destruct Hsat as [sigma [Hinter Hvar]].
    rewrite applySubToC_app in Hinter.
    assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((t1 :s ({{t3 | t4}})) :: c2'))).
      now apply interpretC_app.
    destruct Hand as [Hinter1 Hintermem2].
    destruct Hintermem2 as [Hintermem Hinter2].
    assert (HsetTerm : setTerm (applySubstitution sigma t4)).
      now destruct Hintermem.
    assert (Hor : interpretPC (applySubstitutionToPC sigma (t1 :s t4)) \/
                  interpretPC (applySubstitutionToPC sigma (t1 == t3))).
      now apply axiomW.
    case Hor as [Hmeminter | Heqinter].
    * exists ((t1 :s t4)::(c1'++c2')).
      split.
      -- apply step2.
         apply stepMem2_2 with (s := t3).
         now apply eq_decompose.
      -- exists sigma.
         rewrite applySubToC_app in Hvar.
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_app.
         split.
         ++ split; try assumption.
            now apply interpretC_app.
         ++ rewrite listVarInC_app.
            destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
            simpl in Hvar'.
            destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
            destruct (app_eq_nil _ _ Hvar'') as [-> Hvar'''].
            now destruct (app_eq_nil _ _ Hvar''') as [_ ->].
    * exists ((t1 == t3) :: (c1'++c2')).
      split.
      -- apply step2.
         apply stepMem2_1 with (t := t4).
         now apply eq_decompose.
      -- exists sigma.
         rewrite applySubToC_app in Hvar.
         rewrite listVarInC_app in Hvar.
         unfold satisfies; simpl.
         rewrite applySubToC_app.
         split.
         ++ split; try assumption.
            now apply interpretC_app.
         ++ rewrite listVarInC_app.
            destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
            simpl in Hvar'.
            destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
            destruct (app_eq_nil _ _ Hvar'') as [-> Hvar'''].
            now destruct (app_eq_nil _ _ Hvar''') as [-> _].
  + intros s lt _ HIn.
    destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
    rewrite Heq in Hsat.
    destruct Hsat as [sigma [Hinter _]].
    rewrite applySubToC_app in Hinter.
    assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((t1 :s OTerm s lt) :: c2'))).
      now apply interpretC_app.
    destruct Hand as [_ Hintermem2].
    destruct Hintermem2 as [Hintermem _].
    now destruct Hintermem as [? _].
  + intros _ HIn.
    destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
    rewrite Heq in Hsat.
    destruct Hsat as [sigma [Hinter _]].
    rewrite applySubToC_app in Hinter.
    assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((t1 :s EmptySet) :: c2'))).
      now apply interpretC_app.
    destruct Hand as [_ Hintermem2].
    destruct Hintermem2 as [Hintermem _].
    now destruct Hintermem as [_ [? [_ ?]]].
- intros t1 t2.
  case t2.
  + intros v Hocc HIn.
    destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
    exists (c1' ++ c2').
    split.
    * apply step4.
      apply stepNmem3 with (X:= v) (t:= t1); try now apply eq_decompose.
      apply Decidable.not_not; try assumption.
      now case (occurCheck_dec v t1) as [? | ?]; [left | right].
    * rewrite Heq in Hsat.
      destruct Hsat as [sigma [Hinter Hvar]].
      exists sigma.
      rewrite applySubToC_app in Hinter.
      rewrite applySubToC_app in Hvar.
      assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((t1 \:s Var v) :: c2'))).
        now apply interpretC_app.
      destruct Hand as [Hinter1 HinternMem2].
      destruct HinternMem2 as [HinternMem Hinter2].
      rewrite listVarInC_app in Hvar.
      unfold satisfies; simpl.
      rewrite applySubToC_app.
      split.
      -- now apply interpretC_app.
      -- rewrite listVarInC_app.
         destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
         simpl in Hvar'.
         now destruct (app_eq_nil _ _ Hvar') as [_ ->].
  + intros t3 t4 _ HIn.
    destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
    exists ((t1 \== t3):: ((t1 \:s t4) :: (c1' ++ c2'))).
    split.
    * apply step4.
      apply stepNmem2.
      now apply eq_decompose.
    * rewrite Heq in Hsat.
      destruct Hsat as [sigma [Hinter Hvar]].
      exists sigma.
      assert (Hincl : incl (set_inferPC (t1 \:s ({{t3 | t4}}))) c1).
        now apply sort_complete_set_infer.
      rewrite applySubToC_app in Hinter.
      rewrite applySubToC_app in Hvar.
      assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((t1 \:s ({{t3 | t4}})) :: c2'))).
        now apply interpretC_app.
      destruct Hand as [Hinter1 HinternMem2].
      destruct HinternMem2 as [HinternMem Hinter2].
      rewrite listVarInC_app in Hvar.
      split.
      -- enough (He : ~ (interpretPC (applySubstitutionToPC sigma (t1 :s t4))) /\ ~ ((applySubstitution sigma t1) === (applySubstitution sigma t3))).
           destruct He.
           split; try assumption.
           split; try assumption.
           rewrite applySubToC_app.
           now apply interpretC_app.
         apply Decidable.not_or.
         intro Habs.
         absurd (interpretPC (applySubstitutionToPC sigma (t1 :s ({{t3 | t4}})))); try assumption.
         apply axiomW; try assumption.
         case (dec_setTerm t4) as [HsetTerm | HnsetTerm]; try now apply setTerm_applySub.
         destruct (find_set_SetC_exist t3 _ HnsetTerm) as [t [? Hforall]].
         assert (HIn' : In (IsSet t) c1).
           apply Hincl.
           apply in_or_app.
           now right.
         rewrite <- applySubToC_app in Hinter.
         rewrite <- Heq in Hinter.
         destruct (in_split _ _ HIn') as [c1'' [c2'' Heq']].
         rewrite Heq' in Hinter.
         rewrite applySubToC_app in Hinter.
         assert (Hand : interpretC (applySubstitutionToC sigma c1'') /\ interpretC (applySubstitutionToC sigma ((IsSet t) :: c2''))).
           now apply interpretC_app.
         destruct Hand as [_ HinterS2].
         destruct HinterS2 as [HinterS _].
         now rewrite <- Hforall in HinterS.
      -- simpl; rewrite applySubToC_app.
         rewrite listVarInC_app.
         destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
         simpl in Hvar'.
         destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
         destruct (app_eq_nil _ _ Hvar'') as [-> Hvar34].
         now destruct (app_eq_nil _ _ Hvar34) as [-> ->].
  + intros s lt _ HIn.
    assert (Hincl : incl (set_inferPC (t1 \:s OTerm s lt)) c1).
      now apply sort_complete_set_infer.
    assert (HIn' : In (IsSet (OTerm s lt)) c1).
      apply Hincl.
      apply in_or_app; right.
      apply in_or_app; right.
      now apply in_eq.
    destruct (in_split _ _ HIn') as [c1' [c2' Heq]].
    rewrite Heq in Hsat.
    destruct Hsat as [sigma [Hinter _]].
    rewrite applySubToC_app in Hinter.
    assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma (IsSet (OTerm s lt) :: c2'))).
      now apply interpretC_app.
    destruct Hand as [_ HinterOT2].
    now destruct HinterOT2 as [? _].
  + intros _ HIn.
    destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
    exists (c1' ++ c2').
    split.
    * apply step4.
      apply stepNmem1 with (t:= t1).
      now apply eq_decompose.
    * rewrite Heq in Hsat.
      destruct Hsat as [sigma [Hinter Hvar]].
      exists sigma.
      rewrite applySubToC_app in Hinter.
      rewrite applySubToC_app in Hvar.
      assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((t1 \:s EmptySet) :: c2'))).
        now apply interpretC_app.
      destruct Hand as [Hinter1 HinternMem2].
      destruct HinternMem2 as [HinternMem Hinter2].
      rewrite listVarInC_app in Hvar.
      unfold satisfies; simpl.
      rewrite applySubToC_app.
      split.
      -- now apply interpretC_app.
      -- rewrite listVarInC_app.
         destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
         simpl in Hvar'.
         now destruct (app_eq_nil _ _ Hvar') as [_ ->].
- intros _ HIn.
  destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
  rewrite Heq in Hsat.
  destruct Hsat as [sigma [Hinter _]].
  rewrite applySubToC_app in Hinter.
  assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma (FalseC :: c2'))).
    now apply interpretC_app.
  destruct Hand as [_ HinterF2].
  now destruct HinterF2 as [? _].
- intros t.
  case t.
  + try intros ?; simpl; contradiction.
  + intros t1 t2 _ HIn.
    destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
    exists (c1' ++ (IsSet t2) :: c2').
    split.
    * apply step5.
      apply stepSC2 with (t:= t1).
      now apply eq_decompose.
    * rewrite Heq in Hsat.
      destruct Hsat as [sigma [Hinter Hvar]].
      exists sigma.
      rewrite applySubToC_app in Hinter.
      rewrite applySubToC_app in Hvar.
      assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma ((IsSet ({{t1 | t2}})) :: c2'))).
        now apply interpretC_app.
      destruct Hand as [Hinter1 HinterS2].
      destruct HinterS2 as [HinterS Hinter2].
      rewrite listVarInC_app in Hvar.
      unfold satisfies; simpl.
      rewrite applySubToC_app.
      split.
      -- apply interpretC_app; split; try assumption.
         now split.
      -- rewrite listVarInC_app; simpl.
         destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
         simpl in Hvar'.
         destruct (app_eq_nil _ _ Hvar') as [Hvar'' ->].
         now destruct (app_eq_nil _ _ Hvar'') as [_ ->].
  + intros s lt _ HIn.
    destruct (in_split _ _ HIn) as [c1' [c2' Heq]].
    rewrite Heq in Hsat.
    destruct Hsat as [sigma [Hinter _]].
    rewrite applySubToC_app in Hinter.
    assert (Hand : interpretC (applySubstitutionToC sigma c1') /\ interpretC (applySubstitutionToC sigma (IsSet (OTerm s lt) :: c2'))).
      now apply interpretC_app.
    destruct Hand as [_ HinterS2].
    now destruct HinterS2 as [HinterS _].
  + intros _ HIn.
    destruct (in_split _ _ HIn) as [l1 [l2 Heq]].
    exists (l1 ++ l2).
    split.
    * apply step5.
      apply stepSC1.
      now apply eq_decompose.
    * rewrite Heq in Hsat.
      destruct Hsat as [sigma [Hinter Hvar]].
      exists sigma.
      rewrite applySubToC_app in Hinter.
      rewrite applySubToC_app in Hvar.
      assert (Hand : interpretC (applySubstitutionToC sigma l1) /\ interpretC (applySubstitutionToC sigma (IsSet EmptySet :: l2))).
        now apply interpretC_app.
      destruct Hand as [Hinter1 HinterE2].
      destruct HinterE2 as [HinterE Hinter2].
      rewrite listVarInC_app in Hvar.
      unfold satisfies; simpl.
      rewrite applySubToC_app.
      split; try now apply interpretC_app.
      rewrite listVarInC_app.
      destruct (app_eq_nil _ _ Hvar) as [-> Hvar'].
      simpl in Hvar'.
      now rewrite Hvar'.
Qed.

