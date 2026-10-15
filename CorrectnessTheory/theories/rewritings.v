(*****************************************************
Catherine Dubois - Sulyvan Weppe                      
ENSIIE - Samovar -                                    
2016-2018                                             
                                                      
Modified by Maximiliano Cristia and Ricardo David Katz
2026                                                  
*****************************************************)

Set Implicit Arguments.
Require Import Arith List Recdef Decidable.
Require Import Bool.

Import ListNotations.

Require Import terms_constraints substitution.

(*****************************************)
(*              Decompose                *)
(*****************************************)

Inductive decompose: primitiveConstraint -> constraint -> constraint -> constraint -> Prop :=
  | dec_hd : forall pc c, decompose pc (pc :: c) nil c
  | dec_tl : forall pc pc' c c1 c2,
             decompose pc c c1 c2 ->
               decompose pc (pc' :: c) (pc' :: c1) c2.
Hint Constructors decompose : core.

(*****************************************)
(*       properties of decompose         *)
(*****************************************)

Lemma decompose_eq pc c c1 c2 :
  (decompose pc c c1 c2) -> c = c1 ++ (pc :: c2).
Proof.
intro Hdecompose.
set (P := fun (pc' : primitiveConstraint) (c' c1' c2' : constraint) => c' = c1' ++ (pc' :: c2')).
apply (decompose_ind P); unfold P.
- intros; rewrite app_nil_l; reflexivity.
- intros  ? ? ? ? ? ? ->; reflexivity.
- assumption.
Qed.

Lemma eq_decompose pc c1 c2 :
  forall c, c = c1 ++ pc :: c2 -> decompose pc c c1 c2.
Proof.
elim c1.
- intros ? ->.
  now apply dec_hd.
- intros pc' c' Hind c'' Heq.
  rewrite Heq.
  apply dec_tl.
  now apply Hind.
Qed.

(************************************************)
(** rewriting procedure for equality constraint *)
(************************************************)

Inductive condition_Eq_9: option term -> option term -> Prop :=
  | empty_empty : condition_Eq_9 (Some EmptySet) (Some EmptySet)
  | empty_var : forall X, condition_Eq_9 (Some EmptySet) (Some (Var X))
  | var_empty : forall X, condition_Eq_9 (Some (Var X)) (Some EmptySet)
  | var_var : forall X Y, X <> Y -> condition_Eq_9 (Some (Var X)) (Some (Var Y)).
Hint Constructors condition_Eq_9 : core.

Inductive stepEq : constraint -> constraint -> Prop :=
  | stepEq1 : forall t c l1 l2,
              decompose (t == t) c l1 l2 ->
                stepEq c (l1++l2)
  
  | stepEq2 : forall t X c l1 l2,
              decompose (t == (Var X)) c l1 l2 ->
              ~(isVariable t)->
                stepEq c (((Var X) == t) :: (l1++l2))
  
  | stepEq3 : forall X f l c l1 l2,
              decompose ((Var X) == (OTerm f l)) c l1 l2 ->
              (occurCheckList X l)->
                stepEq c [FalseC]
  
  | stepEq4 : forall X t1 t2 c v l1 l2,
              decompose (Var X == (SetC t1 t2)) c l1 l2 ->
              (tail t2) = Some EmptySet \/ (tail t2) = Some (Var v) ->
              (occurCheckList X (SetCToList t1 t2)) ->
                stepEq c [FalseC]
  
  | stepEq5 : forall X t c l1 l2,
              decompose (Var X == t) c l1 l2 ->
              ~(occurCheck X t)-> ((setTerm t) \/ ~(isSetInC X c) \/ (exists Y, tail t = Some (Var Y))) ->
              ~(isInSFPC (Var X == t) (l1 ++ (Var X == t) :: l2)) -> (* condition added *)
                stepEq c  ((Var X == t) :: (applySubstitutionToC [(X,t)] (l1++l2)))
  
  | stepEq6 : forall X t1 t2 c N l1 l2,
              decompose (Eq (Var X) (SetC t1 t2)) c l1 l2 ->
              ~(occurCheckList X (SetCToList t1 t2)) ->
              ((tail t2) = (Some (Var X))) ->
              (isFreshL N (SetCToList t1 t2)) ->
              (isFreshC N c) ->
              N <> X ->
                stepEq c ([(Var X) == (listSetC (SetCToList t1 t2) (Var N )) ; (IsSet (Var N))] ++ (l1++l2))
  
  | stepEq7 : forall f lf g lg c l1 l2,
              decompose ((OTerm f lf) == (OTerm g lg)) c l1 l2 ->
              ~(f=g) ->
                stepEq c [FalseC]
  
  | stepEq8 : forall f l1 l2 c ll1 ll2,
              decompose ((OTerm f l1) == (OTerm f l2)) c ll1 ll2 ->
              length l1 = length l2 -> (* condition added *)
                stepEq c ((map2 buildEq l1 l2)++(ll1 ++ ll2))
  
  | stepEq9_1 : forall t t' s s' c l1 l2,
                decompose ((SetC t s) == (SetC t' s')) c l1 l2 ->
                condition_Eq_9 (tail s) (tail s') ->
                  stepEq c ((t == t')::(( s == s')::(l1++l2)))
  
  | stepEq9_2 : forall t t' s s' c l1 l2,
                decompose ((SetC t s) == (SetC t' s')) c l1 l2 ->
                condition_Eq_9 (tail s) (tail s') ->
                  stepEq c ((t == t')::(((SetC t s) == s')::(l1++l2)))
  
  | stepEq9_3 : forall t t' s s' c l1 l2,
                decompose ((SetC t s) == (SetC t' s')) c l1 l2 ->
                condition_Eq_9 (tail s) (tail s') ->
                  stepEq c ((t == t')::(( s == (SetC t' s')) :: (l1++l2)))
  
  | stepEq9_4 : forall t t' s s' c N l1 l2,
                decompose ((SetC t s) == (SetC t' s')) c l1 l2 ->
                condition_Eq_9 (tail s) (tail s') ->
                (isFreshL N (s::t::nil)) ->
                (isFreshL N (s'::t'::nil)) ->
                (isFreshC N c) -> (*indicates that N is fresh*)
                  stepEq c ((s == (SetC t' (Var N))) :: ((SetC t (Var N)) == s'):: (IsSet (Var N))::(l1++l2))
  
  | stepEq10_1 : forall lt1 lt2 v c j t0 tj l1 l2,
                 decompose ((listSetC lt1 (Var v)) == (listSetC lt2 (Var v))) c l1 l2 ->
                 nth_error lt1 0 = Some t0 ->
                 nth_error lt2 j = Some tj ->
                   stepEq c (l1++l2 ++ ((Eq t0 tj) ::
                               (Eq (listSetC (deleteElmntj 0 lt1) (Var v)) (listSetC (deleteElmntj j lt2) (Var v))) :: nil))
  
  | stepEq10_2 : forall lt1 lt2 v c j t0 tj l1 l2,
                 decompose ((listSetC lt1 (Var v)) == (listSetC lt2 (Var v))) c l1 l2 ->
                 nth_error lt1 0 = Some t0 ->
                 nth_error lt2 j = Some tj ->
                 stepEq c (l1++l2++((Eq t0 tj) ::
                               (Eq (listSetC lt1 (Var v)) (listSetC (deleteElmntj j lt2) (Var v))) :: nil))
  
  | stepEq10_3 : forall lt1 lt2 v c j t0 tj l1 l2,
                 decompose ((listSetC lt1 (Var v)) == (listSetC lt2 (Var v))) c l1 l2 ->
                 nth_error lt1 0 = Some t0 ->
                 nth_error lt2 j = Some tj ->
                   stepEq c (l1++l2++((Eq t0 tj) ::
                                   (Eq (listSetC (deleteElmntj 0 lt1) (Var v)) (listSetC lt2 (Var v))) :: nil ))
  
  | stepEq10_4 : forall lt1 lt2 v c j t0 tj w l1 l2,
                 decompose ((listSetC lt1 (Var v)) == (listSetC lt2 (Var v))) c l1 l2 ->
                 nth_error lt1 0 = Some t0 ->
                 nth_error lt2 j = Some tj ->
                 (isFreshL w lt1)-> (isFreshL w lt2) ->
                 (isFreshC w c) ->
                 v <> w -> (*indicates that w is fresh*)
                   stepEq c (l1++l2++(( (Var v) == (SetC t0 (Var w))) ::
                              (Eq (listSetC (deleteElmntj 0 lt1) (Var w)) (listSetC lt2 (Var w))) ::
                                 (IsSet (Var w)) :: nil))
  
  | stepEq11 : forall X f l1 c ll1 ll2,
               decompose ((Var X) == (OTerm f l1)) c ll1 ll2 ->
               (isSetInC X c) ->
                 stepEq c [FalseC].

(**************************************************)
(** rewriting procedure for membership constraint *)
(**************************************************)

Inductive stepMem  : constraint -> constraint -> Prop :=
  | stepMem1 : forall t c l1 l2,
               decompose (t :s EmptySet) c l1 l2 ->
                 stepMem c [FalseC]
  
  | stepMem2_1 : forall r s t c l1 l2,
                 decompose (r :s (SetC s t)) c l1 l2 ->
                   stepMem c ((r == s)::(l1++l2))
  
  | stepMem2_2 : forall r s t c l1 l2,
                 decompose (r :s (SetC s t)) c l1 l2 ->
                   stepMem c ((r :s t)::(l1++l2))
  
  | stepMem3 : forall t X N c l1 l2,
               isFreshC N c ->
               isFreshT N t ->
               N <> X ->
               decompose (t :s (Var X)) c l1 l2 ->
                 stepMem c ((l1++l2) ++ [Var X == (SetC t (Var N)) ;  IsSet (Var N)]).

(***************************************************)
(** rewriting procedure for disequality constraint *)
(***************************************************)

Inductive stepNeq  : constraint -> constraint -> Prop :=
  | stepNeq1 : forall  t1 t2 c ll1 ll2,
               decompose (t1 \== t2) c ll1 ll2 ->
               (exists f, exists l1, exists g, exists l2, t1 = (OTerm f l1) /\ t2 = (OTerm g l2) /\ ((f <> g) \/ (length l1 <> length l2)))
               \/ ( t1 = EmptySet /\ (exists f, exists l, t2 = OTerm f l))
               \/ ( (exists f, exists l, t1 = OTerm f l) /\ t2 = EmptySet)
               \/ ( (exists t3, exists t4, t1 = SetC t3 t4) /\ (exists f, exists l, t2 = OTerm f l))
               \/ ( (exists f, exists l, t1 = OTerm f l) /\ (exists t3, exists t4, t2 = SetC t3 t4))
               \/ ( (t1 = EmptySet) /\ (exists t3, exists t4, t2 = SetC t3 t4))
               \/ ( (exists t3, exists t4, t1 = SetC t3 t4) /\ (t2 = EmptySet)) (* condition modified *) ->
                 stepNeq c (ll1 ++ ll2)
  
  | stepNeq2 : forall f l1 l2 c j t1j t2j ll1 ll2,
               decompose ((OTerm f l1) \== (OTerm f l2)) c ll1 ll2 ->
               nth_error l1 j = Some t1j ->
               nth_error l2 j = Some t2j ->
                 stepNeq c ((Neq t1j t2j)::(ll1 ++ ll2))
  
  | stepNeq3 : forall s c l1 l2,
               decompose (Neq s s) c l1 l2 ->
               ((isVariable s)\/(isConstant s)) ->
                 stepNeq c [FalseC]
  
  | stepNeq4 : forall X t c l1 l2,
               decompose  (t \== (Var X)) c l1 l2 ->
               ~(isVariable t) ->
                 stepNeq c (((Var X) \== t)::(l1++l2))
  
  | stepNeq5 : forall X l f c l1 l2,
               decompose  (Neq (Var X) (OTerm f l)) c l1 l2 ->
               occurCheckList X l ->
                 stepNeq c (l1 ++ l2)
  
  | stepNeq6 : forall X t s c l1 l2,
               decompose  (Neq (Var X) (SetC t s)) c l1 l2 ->
               occurCheckList X (SetCToList t s) ->
                 stepNeq c (l1 ++ l2)
  
  | stepNeq7 : forall v lt c j tj l1 l2,
               decompose (Neq (Var v) (listSetC lt (Var v))) c l1 l2 ->
               nth_error lt j = Some tj ->
               ~(occurCheckList v lt) ->
                 stepNeq c ((Nmem tj (Var v)) :: (l1 ++ l2))
  
  | stepNeq8_1 : forall t1 s1 t2 s2 c N l1 l2,
                 decompose  (Neq (SetC t1 s1) (SetC t2 s2)) c l1 l2 ->
                 isFreshC N c ->
                 isFreshL N [s1;t1] ->
                 isFreshL N [s2;t2] ->
                   stepNeq c ((Mem (Var N) (SetC t1 s1))::(Nmem (Var N) (SetC t2 s2))::(l1++l2))
  
  | stepNeq8_2 : forall t1 s1 t2 s2 c N l1 l2,
                 decompose  (Neq (SetC t1 s1) (SetC t2 s2)) c l1 l2 ->
                 isFreshC N c ->
                 isFreshL N [s1;t1] ->
                 isFreshL N [s2;t2] ->
                   stepNeq c ((Mem (Var N) (SetC t2 s2)) :: (Nmem (Var N) (SetC t1 s1)) :: (l1++l2)).

(******************************************************)
(** rewriting procedure for non membership constraint *)
(******************************************************)

Inductive stepNmem  : constraint -> constraint -> Prop :=
  | stepNmem1 : forall t c l1 l2,
                decompose (t \:s EmptySet) c l1 l2 ->
                  stepNmem c (l1++l2)
  
  | stepNmem2 : forall r s t c l1 l2,
                decompose (r \:s (SetC t s)) c l1 l2 ->
                  stepNmem c ((r \== t)::((r \:s s)::(l1++l2)))
  
  | stepNmem3 : forall t c X l1 l2,
                decompose (t \:s (Var X)) c l1 l2 ->
                occurCheck X t ->
                  stepNmem c (l1++l2).

(*************************************)
(** rewriting procedure for setCheck *)
(*************************************)

Inductive stepSC  : constraint -> constraint -> Prop :=
  | stepSC1 : forall c l1 l2,
              decompose (IsSet EmptySet) c l1 l2 ->
                stepSC c (l1++l2)
  
  | stepSC2 : forall t s c l1 l2,
              decompose (IsSet (SetC t s)) c l1 l2 ->
                stepSC c (l1 ++ [IsSet s] ++ l2)
  
  | stepSC3 : forall f l c l1 l2,
              decompose (IsSet (OTerm f l)) c l1 l2 ->
                stepSC c [FalseC].

(*****************************)
(** Definition of step       *)
(*****************************)
(*step is a generalization of the previous rewriting procedures.
It is used to indicate which rewriting procedure we're going to use*)
Inductive step : constraint -> constraint -> Prop :=
  | step1 : forall c c',
              stepEq c c'-> step c c'
  
  | step2 : forall c c',
              stepMem c c'-> step c c'
  
  | step3 : forall c c',
              stepNeq c c'-> step c c'
  
  | step4 : forall c c',
              stepNmem c c'-> step c c'
  
  | step5 : forall c c',
              stepSC c c'->step c c'.

(*defines the reflexive transitive closure of step*)

Require Import RelationClasses.
Require Import Relations.
Require Import Transitive_Closure.

Definition stepStar := clos_refl_trans  _ step.


