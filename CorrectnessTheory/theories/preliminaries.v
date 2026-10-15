(****************************************
Maximiliano Cristia - Ricardo David Katz 
                  2026                   
****************************************)

Set Implicit Arguments.

Require Import Arith List Relations.
Require Import Decidable.

(*************************************************************************************)
(* This file contains properties that are needed to prove the results of the project *)
(*************************************************************************************)

(*************************************************************************************)
(*                           Strong induction                                        *)
(*************************************************************************************)

Lemma strong_ind (P : nat -> Prop) :
  P 0 -> (forall k, (forall l, (l <= k) -> P l) -> P (S k)) -> (forall n, P n).
Proof.
intros HP0 H.
assert (Hforall: (forall n, forall k, (k <= n) -> P k)).
  intro n.
  induction n as [ | n Hind]; intros m Hm.
  - now rewrite <- (le_n_0_eq _ Hm).
  - assert (Hor: (m <= n \/ m = S n)).
      now apply Nat.le_succ_r.
    case Hor; intro Hmn.
    + now apply Hind.
    + rewrite Hmn.
      now apply H.
- intro n.
  apply (Hforall n n).
  now apply le_n.
Qed.

(***************************************************************************************)
(*                      extra properties of nat                                        *)
(***************************************************************************************)

Lemma S_eq : forall n, S n = n+1.
Proof.
intro n.
induction n as [ | n Hind].
- now apply plus_O_n.
- simpl.
  rewrite Hind.
  reflexivity.
Qed.

Lemma le_add_r : forall n m p : nat,
  n + m <= p -> m <= p.
Proof.
intros n m p H.
apply (plus_le_reg_l _ _ n).
apply (le_trans _ p _ H).
now apply le_plus_r.
Qed.

Lemma le_add_l : forall n m p : nat,
  n + m <= p -> n <= p.
Proof.
intros n m p.
rewrite Nat.add_comm.
now apply le_add_r.
Qed.

Lemma leq_eqn : forall n m : nat,
  n <= m -> m <= n -> n = m.
Proof.
Nat.order.
Qed.

(*******************************************)
(*     extra properties of list            *)
(*******************************************)

Lemma cons_neq_nil (A : Type) (x : A) (l : list A) :
  x :: l <> nil.
Proof.
intro Habs.
absurd (In x nil); try now apply in_nil.
rewrite <- Habs.
now apply in_eq.
Qed.

Lemma last_map (A : Type) (f : A -> A) (l : list A) (d : A) :
  l <> nil -> last (map f l) d = f (last l d).
Proof.
intros Hneq_nil.
rewrite app_removelast_last with (l := l) (d := d); try assumption.
rewrite map_app; simpl.
now do 2 rewrite last_last.
Qed.

Lemma neg_in_app (A : Type) (a : A) (l1 l2 : list A) :
  ~ In a (l1 ++ l2) -> (~ In a l1) /\ (~ In a l2).
Proof.
intro HnIn.
apply not_or.
now apply (not_iff_compat (in_app_iff l1 l2 a)).
Qed.

Lemma incl_nodup (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) :
  incl (nodup eq_dec l) l.
Proof.
elim l.
- now apply incl_nil_l.
- intros a l' Hind.
  simpl.
  case (in_dec eq_dec a l') as [? | ?]; try now apply incl_tl.
  now apply incl_cons; [apply in_eq | apply incl_tl].
Qed.

Lemma incl_incl_nodup (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A) :
  incl l1 l2 -> incl (nodup eq_dec l1) (nodup eq_dec l2).
Proof.
intro.
now apply incl_tran with (m:= l1); [apply incl_nodup | apply nodup_incl].
Qed.

Lemma hd_split (A : Type) n (l : list A) a :
  (n < length l) ->
    exists l', l = (hd a l) :: l'.
Proof.
intros Hllgtn.
assert (Hllgt0 : 0 < length l).
  now apply Nat.lt_lt_0 with (n := n).
destruct (nth_split l a Hllgt0) as [l' [l'' [-> Hll'eq0]]].
exists l''.
assert (Hl'eqnil : l' = nil).
  now apply length_zero_iff_nil.
now rewrite Hl'eqnil.
Qed.

Lemma split_last (A : Type) n (l : list A) a :
  (n < length l) ->
    exists l', l = l' ++ ((last l a) :: nil).
Proof.
intro Hllgtn.
exists (removelast l).
apply app_removelast_last.
intro Heqnil.
rewrite Heqnil in Hllgtn.
absurd (n < 0); try assumption.
now apply Nat.nlt_0_r.
Qed.

Lemma incl_filter (A : Type) (f : A -> bool) (l : list A) :
  incl (filter f l) l.
Proof.
elim l; try now apply incl_nil_l.
intros a l' Hind.
simpl; case (f a); try now apply incl_tl.
now apply incl_cons; [apply in_eq | apply incl_tl].
Qed.

Lemma length_filter (A : Type) (f : A -> bool) (l : list A) :
  length (filter f l) <= length l.
Proof.
elim l; try now apply le_n.
intros a l' Hind.
now simpl; case (f a); [apply le_n_S | apply le_S].
Qed.

(* returns a list of length n with all elements equal to a *)
Fixpoint list_all_eq (A : Type) (a : A) n := match n with
                                             | 0 => nil
                                             | S p => a :: list_all_eq a p
                                             end.

Lemma length_list_all_eq (A : Type) (a : A) n :
  length (list_all_eq a n) = n.
Proof.
elim n; try reflexivity.
intros m Hm.
now simpl; rewrite Hm.
Qed.

Lemma In_list_all_eq (A : Type) (a : A) n :
  forall b, In b (list_all_eq a n) -> b = a.
Proof.
induction n as [ | n Hind].
- intro; contradiction.
- intros b HIn.
  case HIn; try now apply eq_sym.
  now apply Hind.
Qed.

Lemma nth_list_all_eq (A : Type) (a a' : A) n :
  forall m, m < n -> nth m (list_all_eq a n) a' = a.
Proof.
intros m Hm_lt.
apply In_list_all_eq with (n := n).
apply nth_In.
now rewrite (length_list_all_eq a n).
Qed.

Fixpoint cons_list (A : Type) (l : list A) (ll : list (list A)) :=
  match l with
  | nil => nil
  | t :: lt => match ll with
               | nil => nil
               | lt' :: llt => (t :: lt') :: (cons_list lt llt)
               end
  end.

Lemma length_cons_list (A : Type) (l : list A) ll :
  length (cons_list l ll) = Nat.min (length l) (length ll).
Proof.
set (P := fun (n : nat) => (forall (l' : list A) ll', ((length l' <= n) \/ (length ll' <= n)) ->
       length (cons_list l' ll') = Nat.min (length l') (length ll'))).
enough (H : (forall n, (P n))).
  apply (H (Nat.min (length l) (length ll))).
  now case (Nat.min_dec (length l) (length ll)) as [-> | ->];
    [left | right]; apply le_n.
intro n.
induction n as [ | n Hind].
- intros l' ll' Hor.
  case Hor as [Hl' | Hll'].
  + assert (Hnil : l' = nil).
      apply length_zero_iff_nil.
      apply eq_sym.
      now apply le_n_0_eq.
    rewrite Hnil.
    reflexivity.
  + assert (Hnil : ll' = nil).
      apply length_zero_iff_nil.
      apply eq_sym.
      now apply le_n_0_eq.
    rewrite Hnil.
    rewrite Nat.min_0_r.
    assert (H : (cons_list l' nil) = nil).
      now case l'.
    now rewrite H.
- intros l' ll'.
  elim l'; try reflexivity.
  intros t' lt'.
  elim ll'; try reflexivity.
  intros llt' lll' _ _ Hor.
  apply eq_S.
  apply Hind.
  case Hor as [Hlength | Hlength].
  + now left; apply le_S_n.
  + now right; apply le_S_n.
Qed.

Lemma nth_cons_list (A : Type) (d : A) m l ll:
  m < length l -> m < length ll ->
    nth m (cons_list l ll) nil = nth m l d :: nth m ll nil.
Proof.
set (P := fun (n : nat) => (forall l' ll' m', ((length l' <= n) \/ (length ll' <= n)) ->
       m' < length l' -> m' < length ll' ->
    nth m' (cons_list l' ll') nil = nth m' l' d :: nth m' ll' nil)).
enough (H : (forall n, (P n))).
  apply (H (Nat.min (length l) (length ll))).
  now case (Nat.min_dec (length l) (length ll)) as [-> | ->];
    [left | right]; apply le_n.
intro n.
induction n as [ | n Hind].
- intros l' ll' m' Hor.
  case Hor as [Hl' | Hll'].
  + assert (Hnil : l' = nil).
      apply length_zero_iff_nil.
      apply eq_sym.
      now apply le_n_0_eq.
    rewrite Hnil.
    intros.
    absurd (m' < 0); try assumption.
    now apply Nat.nlt_0_r.
  + assert (Hnil : ll' = nil).
      apply length_zero_iff_nil.
      apply eq_sym.
      now apply le_n_0_eq.
    rewrite Hnil.
    intros.
    absurd (m' < 0); try assumption.
    now apply Nat.nlt_0_r.
- intros l' ll'.
  elim l'.
  + intros.
    absurd (m' < 0); try assumption.
    now apply Nat.nlt_0_r.
  + intros t' lt'.
    elim ll'.
    * intros.
      absurd (m' < 0); try assumption.
      now apply Nat.nlt_0_r.
    * intros llt' lll' _ _ m' Hor.
      case m'; try reflexivity.
      intros m'' HSlt' HSlll'.
      simpl.
      apply Hind; try now apply lt_S_n.
      case Hor as [Hlength | Hlength].
      -- now left; apply le_S_n.
      -- now right; apply le_S_n.
Qed.

(*******************************************)
(*     extra properties of remove          *)
(*******************************************)

Lemma incl_remove_l (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) :
  In x l -> incl (x :: remove eq_dec x l) l.
Proof.
intros Hxin y Hyin.
case Hyin.
- now intros ->.
- intro Hinremove.
  now destruct (in_remove eq_dec _ _ _ Hinremove).
Qed.

Lemma incl_remove_r (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) :
  incl l (x :: remove eq_dec x l).
Proof.
intros y Hyin.
case (eq_dec y x) as [-> | Hneq].
- now apply in_eq.
- right.
  now apply in_in_remove.
Qed.

Lemma incl_remove_remove (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l1 l2 : list A) :
  incl l1 l2 -> incl (remove eq_dec x l1) (remove eq_dec x l2).
Proof.
elim l1; try now simpl.
intros a l Hind Hincl.
destruct (incl_cons_inv Hincl) as [HIn Hincl'].
simpl; case (eq_dec x a) as [_ | Hneq]; try now apply Hind.
apply incl_cons; try now apply Hind.
apply in_in_remove; try assumption.
intro Habs.
now rewrite Habs in Hneq.
Qed.

Lemma incl_remove (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) :
  incl (remove eq_dec x l) l.
Proof.
intros y Hinremove.
assert (H: In y l /\ y <> x).
  now apply (in_remove eq_dec).
now destruct H.
Qed.

Lemma remove_nil (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) :
  remove eq_dec x nil = nil.
Proof.
trivial.
Qed.

Lemma remove_eq_nil (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x : A) :
  remove eq_dec x l = nil <-> (incl l (x :: nil)).
Proof.
elim l.
- simpl.
  split; intros _; try trivial.
  now apply incl_nil_l.
- intros x' l' Hind.
  simpl.
  case (eq_dec x x') as [Heq | Hneq].
  + split.
    * intro H.
      apply incl_cons; try now apply Hind.
      rewrite Heq.
      now apply in_eq.
    * intro H.
      destruct (incl_cons_inv H) as [_ H'].
      now apply Hind.
  + split.
    * intro Heq_nil.
      enough (Habs : In x' nil).
        contradiction.
      rewrite <- Heq_nil.
      now left.
    * intro Hincl.
      destruct (incl_cons_inv Hincl) as [HInv' _].
      case HInv' as [Heq | Habs]; contradiction.
Qed.

(*******************************************)
(*     extra properties of list_max        *)
(*******************************************)

Lemma incl_listmax l1 l2 :
  incl l1 l2 -> list_max l1 <= list_max l2.
Proof.
intro Hincl.
apply list_max_le.
apply (incl_Forall Hincl).
now apply list_max_le.
Qed.

Lemma exists_listmax  n l :
  (exists m, (In m l) /\ (n <= m)) -> n <= list_max l.
Proof.
intro Hexists.
destruct Hexists as [m [HIn Hle]].
assert (Heq : m = list_max (m :: nil)).
  simpl; now rewrite Nat.max_0_r.
apply Nat.le_trans with (m := list_max (m :: nil)).
- now rewrite <- Heq.
- apply incl_listmax.
  apply incl_cons; try assumption.
  now apply incl_nil_l.
Qed.

Lemma S_listmax l :
  l <> nil -> S (list_max l) = list_max (map S l).
Proof.
elim l.
- contradiction.
- intros a l' Hind _.
  simpl.
  rewrite Nat.succ_max_distr.
  case (list_eq_dec eq_nat_dec l' nil) as [-> | Hnil].
  + simpl; now rewrite Nat.max_0_r.
  + now rewrite (Hind Hnil).
Qed.

(*******************************************)
(*     extra properties of clos_trans      *)
(*******************************************)

Lemma clos_rel_list (A : Type) (R : relation A) a1 a2 a :
  reflexive _ R -> (clos_trans _ R) a1 a2 ->
    exists l, (1 < length l) /\ ((nth 0 l a) = a1) /\ ((nth (Nat.pred (length l)) l a) = a2) /\
      (forall n, (n < Nat.pred (length l)) -> R (nth n l a) (nth (S n) l a)).
Proof.
intros HR_refl Hcr_a1_a2.
set (P := fun (a1' a2' : A) => (exists l, (1 < length l) /\ ((nth 0 l a) = a1') /\ ((nth (Nat.pred (length l)) l a) = a2') /\
                (forall n,  (n < Nat.pred (length l)) -> R (nth n l a) (nth (S n) l a)))).
enough (H : forall a1' a2', (clos_trans _ R) a1' a2' -> P a1' a2').
  destruct (H _ _ Hcr_a1_a2) as [l ?].
  now exists l.
apply clos_trans_ind.
- intros a1' a2' Hrel_term.
  exists (a1' :: (a2' :: nil)).
  split; try apply le_n.
  split; try trivial.
  split; try trivial.
  intro n.
  case n.
  + intro; assumption.
  + intros n' Hn'.
    assert (Hn'' : n' < Nat.pred (Nat.pred 2)).
      now apply lt_pred.
    absurd (n' < 0); try assumption.
    now apply Nat.nlt_0_r.
- intros a1' a2' a3' Ha1'a2' [l1 [Hlength1 [Hhd1 [Hlast1 H1]]]] Ha2'a3' [l2 [Hlength2 [Hhd2 [Hlast2 H2]]]].
  exists (l1 ++ l2).
  split.
  + rewrite app_length.
    now apply lt_plus_trans.
  + assert (Hlength1' : 0 < length l1).
      apply Nat.lt_trans with (m := 1); try assumption.
      now apply Nat.lt_0_1.
    assert (Hlength2' : 0 < length l2).
      apply Nat.lt_trans with (m := 1); try assumption.
      now apply Nat.lt_0_1.
    split; try now rewrite app_nth1.
    split.
    * rewrite app_length.
      rewrite <- Nat.add_pred_r; try now rewrite app_nth2_plus.
      now apply Nat.neq_0_lt_0.
    * intros n Hn.
      rewrite app_length in Hn.
      case (le_lt_dec (Nat.pred (length l1)) n) as [Hnl1 | Hnl1].
      -- case (le_lt_or_eq _ _ Hnl1) as [Hnl1' | Hnl1'].
         ++ assert (Hnl1''' : length l1 <= n).
              now apply Nat.lt_pred_le.
            assert (Hnl1'' : (length l1) <= S n).
              now apply le_S.
            rewrite (app_nth2 _ _ _ Hnl1'').
            rewrite (app_nth2 _ _ _ Hnl1''').
            rewrite <- (minus_Sn_m _ _ Hnl1''').
            apply H2.
            apply lt_pred.
            rewrite (minus_Sn_m _ _ Hnl1''').
            apply plus_lt_reg_l with (p := length l1).
            rewrite (le_plus_minus_r _ _ Hnl1'').
            now apply Nat.lt_succ_lt_pred.
         ++ assert (Hn_lt_ll1 : n < length l1).
              rewrite <- Hnl1'.
              now apply lt_pred_n_n.
            rewrite (app_nth1 _ _ _ Hn_lt_ll1).
            rewrite <- Hnl1'.
            rewrite Hlast1.
            assert (Hnl1'' : S (Nat.pred (length l1)) >= length l1).
              rewrite <- S_pred_pos; try assumption.
              now apply le_n.
            rewrite (app_nth2 _ _ _ Hnl1'').
            rewrite <- (S_pred _ _ Hn_lt_ll1).
            rewrite Nat.sub_diag.
            rewrite Hhd2.
            now apply HR_refl.
      -- assert (HSn_l1 : S n < length l1).
           now apply Nat.lt_succ_lt_pred.
         assert (Hn_l1 : n < length l1).
           now apply Nat.lt_succ_l.
         rewrite (app_nth1 _ _ _ HSn_l1).
         rewrite (app_nth1 _ _ _ Hn_l1).
         now apply H1.
Qed.

Lemma clos_rel_list_forall (A : Type) (R : relation A) a1 a2 a :
  reflexive _ R -> (clos_trans _ R) a1 a2 -> (exists n, forall m, n <= m -> 
    (exists l, (length l = m) /\ ((nth 0 l a) = a1) /\ ((nth (Nat.pred (length l)) l a) = a2) /\
      (forall n, (n < Nat.pred (length l)) -> R (nth n l a) (nth (S n) l a)))).
Proof.
intros HR_refl Hcr_a1_a2.
destruct (clos_rel_list a HR_refl Hcr_a1_a2) as [l [Hlength [Hhead [Htail Hforall]]]].
exists (length l).
intros m Hm.
exists (l ++ (list_all_eq a2 (m - length l))).
split.
- rewrite app_length.
  rewrite length_list_all_eq.
  now apply le_plus_minus_r.
- split.
  + rewrite <- Hhead.
    apply app_nth1.
    now apply Nat.lt_succ_l.
  + rewrite app_length.
    rewrite length_list_all_eq.
    case (le_lt_or_eq _ _ Hm) as [Hm' | <-].
    * assert (Hneq0 : m - length l <> 0).
        now apply Nat.sub_gt.
      rewrite <- (Nat.add_pred_r _ _ Hneq0).
      split.
      -- rewrite app_nth2_plus.
         rewrite nth_list_all_eq; try reflexivity.
         now apply Nat.lt_pred_l.
      -- intros n Hn.
         case (Nat.lt_ge_cases n (Nat.pred (length l))) as [Hn' | Hn'].
         ++ rewrite app_nth1; try now apply Nat.lt_pred_lt.
            rewrite app_nth1; try now apply Nat.lt_succ_lt_pred.
            now apply Hforall.
         ++ case (le_lt_or_eq _ _ Hn') as [Hn'' | <-].
            ** assert (H : n - length l < Nat.pred (m - length l)).
                 apply Nat.add_lt_mono_r with (p := length l).
                 rewrite Nat.sub_add; try now apply Nat.lt_pred_le.
                 now rewrite Nat.add_comm.
               rewrite app_nth2; try now apply Nat.lt_pred_le.
               rewrite app_nth2; try now apply Nat.le_pred_le_succ.
               rewrite nth_list_all_eq; try now apply Nat.lt_pred_lt.
               rewrite nth_list_all_eq; try now apply HR_refl.
               rewrite <- minus_Sn_m; try now apply Nat.lt_pred_le.
               now apply Nat.lt_succ_lt_pred.
            ** rewrite app_nth1; try now apply lt_pred_n_n; apply Nat.lt_succ_l.
               rewrite <- (S_pred _ _ Hlength).
               rewrite app_nth2; try now apply le_n.
               rewrite Nat.sub_diag.
               rewrite nth_list_all_eq; try now apply Nat.neq_0_lt_0.
               rewrite Htail.
               now apply HR_refl.
    * split.
      -- rewrite Nat.sub_diag.
         rewrite <- plus_n_O.
         rewrite <- Htail.
         apply app_nth1.
         apply lt_pred_n_n.
         now apply Nat.lt_succ_l.
      -- intro n.
         rewrite Nat.sub_diag.
         rewrite <- plus_n_O.
         intro Hn.
         rewrite app_nth1; try now apply Nat.lt_pred_lt.
         rewrite app_nth1; try now apply Nat.lt_succ_lt_pred.
         now apply Hforall.
Qed.

Lemma list_clos_rel (A : Type) (R : relation A) a1 a2 a :
  reflexive _ R ->
    (exists l, (1 < length l) /\ ((nth 0 l a) = a1) /\ ((nth (Nat.pred (length l)) l a) = a2) /\
      (forall n, (n < Nat.pred (length l)) -> R (nth n l a) (nth (S n) l a))) ->
        (clos_trans _ R) a1 a2.
Proof.
intros HR_refl [l [Hlength [Hhead [Htail Hforall]]]].
set (P := fun (n : nat) => forall a1' a2' l', (length l' <= n) -> (1 < length l') ->
                            ((nth 0 l' a) = a1') -> ((nth (Nat.pred (length l')) l' a) = a2') ->
                           (forall n, (n < Nat.pred (length l')) -> R (nth n l' a) (nth (S n) l' a)) ->
                           (clos_trans _ R) a1' a2').
enough (H : (forall n, (P n))).
  apply (H (length l) _ _ l); try assumption.
  now apply le_n.
intro n.
induction n as [ | n Hind].
- intros a1' a2' l' H Habs _ _ _.
  assert  (Heq0 : 0 = length l').
    now apply le_n_0_eq.
  absurd (S (length l') < (length l'));
  try now apply Nat.nlt_succ_diag_l.
  now rewrite Heq0 in Habs.
- intros a1' a2' l' Hlength' Hlength'' Hhead' Htail' Hforall'.
  assert (H : 0 < length l').
    now apply Nat.lt_succ_l.
  destruct (nth_split _ a H) as  [l1 [l2 [Heq Hlength_l1]]].
  assert (Hl1_eq_nil : l1 = nil).
    now apply length_zero_iff_nil.
  rewrite Hl1_eq_nil in Heq.
  rewrite app_nil_l in Heq.
  assert (H_l'_eq : l' = (nth 0 l' a :: nil) ++ l2).
    trivial.
  rewrite <- Hhead'.
  rewrite <- Htail'.
  case (le_lt_dec (length l2) 1); intro Hlength_l2.
  + assert (Hlength_l'_eq : length l' = 2).
      rewrite Heq.
      simpl; apply eq_S.
      apply leq_eqn; try assumption.
      case (le_lt_or_eq _ _ Hlength_l2) as [Hneq | ->]; try now apply le_n.
      assert (Heq0 : length l2 = 0).
        apply Nat.le_0_r.
        now apply lt_n_Sm_le.
      absurd (1 < length l'); try assumption.
      rewrite H_l'_eq.
      simpl; rewrite Heq0.
      now apply Nat.lt_irrefl.
    rewrite Hlength_l'_eq.
    apply t_step.
    apply Hforall'.
    rewrite Hlength_l'_eq.
    now apply Nat.lt_0_1.
  + apply t_trans with (y := nth 1 l' a).
    * apply t_step.
      apply Hforall'.
      rewrite H_l'_eq.
      now apply Nat.lt_succ_l.
    * assert (Hrel_lengths : (Nat.pred (length l')) = S (Nat.pred (length l2))).
        rewrite H_l'_eq.
        now apply S_pred with (m := 1).
      assert (Hforall2 : forall m, nth m l2 a = nth (S m) l' a).
        intro m.
        rewrite H_l'_eq.
        rewrite S_eq.
        rewrite Nat.add_comm.
        assert (Hlenght_eq_1 : length (nth 0 l' a :: nil) = 1).
          trivial.
        rewrite <- Hlenght_eq_1.
        now rewrite app_nth2_plus.
      rewrite <- (Hforall2 0).
      rewrite Hrel_lengths.
      rewrite <- (Hforall2 (Nat.pred (length l2))).
      apply (Hind _ _ l2); try reflexivity.
      -- rewrite Heq in Hlength'.
         now apply le_S_n.
      -- assumption.
      -- intros m Hm.
         rewrite (Hforall2 m).
         rewrite (Hforall2 (S m)).
         apply Hforall'.
         rewrite Hrel_lengths.
         now apply lt_n_S.
Qed.

(**************************************************************************************************)
(* remove list : a generalization of remove to lists which removes a list of elements from a list *)
(**************************************************************************************************)

Fixpoint remove_list (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A) :=
  match l1 with
  | nil => l2
  | v :: lv => remove eq_dec v (remove_list eq_dec lv l2)
  end.

Lemma incl_remove_list (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A) :
  incl (remove_list eq_dec l1 l2) l2.
Proof.
elim l1.
- now apply incl_refl.
- intros v lv Hind.
  simpl.
  apply incl_tran with (m := (remove_list eq_dec lv l2)).
  + now apply incl_remove.
  + exact Hind.
Qed.

Lemma in_remove_list (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A) a :
  In a (remove_list eq_dec l1 l2) <-> (In a l2 /\ ~ In a l1).
Proof.
split.
- elim l1.
  + intro HInremove.
    now split; [assumption | apply in_nil].
  + intros a' l Hind Hin.
    simpl in Hin.
    destruct (in_remove eq_dec _ _ _ Hin) as [Hin' Hneq].
    split.
    * now destruct (Hind Hin').
    * intro Hin''.
      case (Hin'') as [H1 | H2].
      -- assert (a = a').
           now apply eq_sym.
         contradiction.
      -- now destruct (Hind Hin').
- elim l1.
  + intros [? ?].
    assumption.
  + intros a' lv Hind [Hin Hnin].
    destruct (not_or _ _ Hnin).
    apply in_in_remove.
    * now apply not_eq_sym.
    * apply Hind.
      now split.
Qed.

Lemma incl_remove_list_r (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 l : list A) :
  incl l1 l2 -> incl (remove_list eq_dec l2 l) (remove_list eq_dec l1 l).
Proof.
elim l1.
- intro Hincl.
  now apply incl_remove_list.
- intros a l' Hind Hincl a' Huin.
  destruct (incl_cons_inv Hincl) as [Hvin Hincl'].
  simpl.
  apply in_in_remove.
  + intro Heq.
    assert (Hneg: ~ In a' l2).
      now apply (in_remove_list eq_dec _ l).
    rewrite Heq in Hneg.
    contradiction.
  + now apply (Hind Hincl').
Qed.

Lemma incl_remove_list_l (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 l : list A) :
  incl l1 l2 -> incl (remove_list eq_dec l l1) (remove_list eq_dec l l2).
Proof.
elim l.
- trivial.
- intros ? ? Hind ?.
  apply remove_incl.
  now apply Hind.
Qed.

Lemma remove_list_cons (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A) a :
  (remove_list eq_dec l1 (a :: l2)) = (remove_list eq_dec l1 (a :: nil)) ++ (remove_list eq_dec l1 l2).
Proof.
elim l1.
- trivial.
- intros a' l Hind.
  simpl; rewrite Hind.
  now rewrite remove_app.
Qed.

Lemma remove_list_app (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l l1 l2 : list A) :
  remove_list eq_dec l (l1 ++ l2) = remove_list eq_dec l l1 ++ remove_list eq_dec l l2.
Proof.
elim l.
- trivial.
- intros v l' Hind.
  simpl; rewrite Hind.
  now rewrite remove_app.
Qed.

Lemma remove_list_nil (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) :
  remove_list eq_dec l nil = nil.
Proof.
elim l.
- trivial.
- intros v l' Hind.
  simpl; rewrite Hind.
  now rewrite remove_nil.
Qed.

Lemma remove_list_length_1 (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (a : A) :
  ~ (In a l) -> remove_list eq_dec l (a :: nil) = (a :: nil).
Proof.
elim l; try trivial.
intros a' l' Hind HnIn.
simpl in HnIn.
destruct (not_or _ _ HnIn) as [Hneq HnIn'].
simpl; rewrite (Hind HnIn').
simpl; case (eq_dec a' a) as [Heq | _]; try reflexivity.
now rewrite Heq in Hneq.
Qed.

Lemma remove_list_l_l (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) :
  remove_list eq_dec l l = nil.
Proof.
elim l; try trivial.
intros a' l' Hind.
rewrite remove_list_cons.
simpl; rewrite Hind.
simpl; rewrite remove_list_cons.
rewrite app_nil_r.
assert (Heq : remove_list eq_dec l' nil = nil).
  apply incl_l_nil.
  now apply incl_remove_list.
rewrite Heq.
rewrite app_nil_r.
apply incl_l_nil.
apply incl_tran with (m:= remove eq_dec a' (a' :: nil)).
- apply remove_incl.
  now apply incl_remove_list.
- assert (Heq' : (remove eq_dec a' (a' :: nil)) = nil).
    now simpl; case (eq_dec a' a'); [trivial | contradiction].
  rewrite Heq'.
  now apply incl_nil_l.
Qed.

Lemma remove_list_eq_nil (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A) :
  (remove_list eq_dec l1 l2 = nil) <-> (incl l2 l1).
Proof.
elim l1.
- split.
  + simpl; intros ->.
    now apply incl_nil_l.
  + intros Hincl.
    now rewrite (incl_l_nil Hincl).
- intros a l Hind.
  simpl.
  split.
  + intro H.
    assert (Hincl : incl (remove_list eq_dec l l2) (a :: nil)).
      now apply (remove_eq_nil eq_dec).
    case (list_eq_dec eq_dec (remove_list eq_dec l l2) nil) as [? | Hneq_nil].
    * apply incl_tl.
      now apply Hind.
    * assert (H' : incl (remove_list eq_dec l l2) (a :: nil)).
        now apply (remove_eq_nil eq_dec).
      intros a' Ha'Inl2.
      case (in_dec eq_dec a' l) as [? | ?].
      -- now right.
      -- assert (Ha'In : In a' (a :: nil)).
           apply H'.
           apply in_remove_list.
           now split.
         now case Ha'In as [-> | ?]; [left | contradiction].
  + intro Hincl.
    apply remove_eq_nil.
    apply incl_tran with (m := remove_list eq_dec l (a :: l)); try now apply incl_remove_list_l.
    rewrite remove_list_cons.
    rewrite remove_list_l_l.
    rewrite app_nil_r.
    now apply incl_remove_list.
Qed.

Lemma remove_list_nodup (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) :
  remove_list eq_dec (nodup eq_dec l) l = nil.
Proof.
apply incl_l_nil.
rewrite <- remove_list_l_l with (l := l) (eq_dec := eq_dec).
apply incl_remove_list_r.
now apply nodup_incl.
Qed.



