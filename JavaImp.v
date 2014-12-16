Require Export Java.

(* A variable is some defined object (eg. array or number) *)
Inductive var: Set :=
  | Vnone: var
  | Vbool: bool -> var
  | Vnum: jnum -> var
  | Varr: id -> var.

Inductive state: Set :=
  | Scur: (id -> var) -> (id -> option (list var)) -> nat -> state.

(* Definition state := id -> var. *)

Definition state_get (s: state) (i: id): var :=
  match s with
  | Scur user _ _ => user i
  end.

Definition state_get_num (s: state) (i: id): option jnum :=
  match s with
  | Scur user _ _ => 
    match user i with
    | Vnum n => Some n
    | _ => None
    end
  end.

Definition state_get_ptr (s: state) (i: id): option id :=
  match s with
  | Scur user mem _ => 
    match user i with
    | Varr idx => Some idx 
    | _ => None
    end
  end.

Definition state_follow_ptr (s: state) (i: id): option (list var) :=
  match s with
  | Scur _ mem _ => mem i
  end.

Definition state_get_arr (s: state) (i: id): option (list var) :=
  match s with
  | Scur user mem _ => 
    match user i with
    | Varr idx => mem idx      
    | _ => None
    end
  end.

Inductive aexp: Set :=
| ANum: nat -> aexp
| AId: id -> aexp
| APlus: aexp -> aexp -> aexp
| AMinus: aexp -> aexp -> aexp
| AMult: aexp -> aexp -> aexp
| ADiv: aexp -> aexp -> aexp
| AMod: aexp -> aexp -> aexp
| AOr: aexp -> aexp -> aexp
| AAnd: aexp -> aexp -> aexp
| AXor: aexp -> aexp -> aexp
| ACast: aexp -> nat -> aexp
| ALoad: id -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp
  | BOr : bexp -> bexp -> bexp
  | BXor : bexp -> bexp -> bexp
  | BLoad : id -> aexp -> bexp.

Definition aeval_helper (f: jnum -> jnum -> jnum) (l r: option jnum): option jnum :=
  match l, r with
  | Some n1, Some n2 => Some (f n1 n2)
  | _, _ => None
  end.

Definition list_index {T: Type} (l: list T) (n: jnum): option T :=
  match nth_error l (jnum_to_nat n) with
  | Some n => Some n
  | _ => None
  end.

Definition list_insert {T: Type} (l: list T) (n: jnum) (val: T): list T :=
  let n' := jnum_to_nat n in
    (firstn n' l) ++ [val] ++ (skipn (n' + 1) l).

Fixpoint aeval (st: state) (a: aexp): option jnum :=
  match a with
  | ANum n => Some (nat_to_jnum n 8)
  | AId i => state_get_num st i
  | APlus l r => aeval_helper jnum_plus (aeval st l) (aeval st r)
  | AMinus l r => aeval_helper jnum_sub (aeval st l) (aeval st r)
  | AMult l r => aeval_helper jnum_mult (aeval st l) (aeval st r)
  | ADiv l r => aeval_helper jnum_div (aeval st l) (aeval st r)
  | AMod l r => aeval_helper jnum_mod (aeval st l) (aeval st r)
  | AOr l r => aeval_helper jnum_orb (aeval st l) (aeval st r)
  | AAnd l r => aeval_helper jnum_andb (aeval st l) (aeval st r)
  | AXor l r => aeval_helper jnum_xorb (aeval st l) (aeval st r)
  | ACast l r =>
    match (aeval st l) with
    | Some n => Some (jnum_promote n r)
    | None => None
    end 
  | ALoad i a' =>
    match (state_get_arr st i), (aeval st a') with
    | Some arr, Some n => 
      match list_index arr n with
      | Some (Vnum n') => Some n'
      | _ => None
      end
    | _, _ => None
    end 
  end.

Definition beval_helper (f: jnum -> jnum -> bool) (l r: option jnum): option bool :=
  match l, r with
  | Some n1, Some n2 => Some (f n1 n2)
  | _, _ => None
  end.

Definition beval_helper2 (f: bool -> bool -> bool) (l r: option bool): option bool :=
  match l, r with
  | Some n1, Some n2 => Some (f n1 n2)
  | _, _ => None
  end.

Fixpoint beval (st: state) (b : bexp) : option bool :=
  match b with
  | BTrue       => Some true
  | BFalse      => Some false
  | BEq a1 a2   => beval_helper jnum_eq (aeval st a1) (aeval st a2)
  | BLe a1 a2   => beval_helper jnum_leq (aeval st a1) (aeval st a2)
  | BNot b1     => 
    match (beval st b1) with
    | Some b' => Some (negb b')
    | _ => None
    end
  | BAnd b1 b2  => beval_helper2 andb (beval st b1) (beval st b2)
  | BOr b1 b2  => beval_helper2 orb (beval st b1) (beval st b2)
  | BXor b1 b2  => beval_helper2 xorb (beval st b1) (beval st b2)
  | BLoad i a' =>
    match (state_get_arr st i), (aeval st a') with
    | Some arr, Some n => 
      match list_index arr n with
      | Some (Vbool n') => Some n'
      | _ => None
      end
    | _, _ => None
    end 
  end.

Definition Aeval (a: aexp): state -> var :=
  fun st =>
    match aeval st a with
    | Some n => Vnum n
    | None => Vnone
    end.

Definition Beval (a: bexp): state -> var :=
  fun st =>
    match beval st a with
    | Some n => Vbool n
    | None => Vnone
    end.

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition bassn b : Assertion :=
  fun st => (beval st b = Some true).

Lemma bexp_eval_true : forall b st,
  beval st b = Some true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = Some false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

Definition update (st : state) (x : id) (v : state -> var) : state :=
  match st with
  | Scur user mem n => Scur (fun x' => if eq_id_dec x x' then v st else user x') mem n
  end.

Definition assn_sub X v P : Assertion :=
  fun (st : state) =>
    P (update st X v).

Definition update_mem (st : state) (x : id) (v : option (list var)) : state :=
  match st with
  | Scur user mem n => Scur user (fun x' => if eq_id_dec x x' then v else mem x') n
  end.

Definition update_arr (st : state) (x : id) (idx: aexp) (v: state -> var) : state :=
  let ptr := state_get_ptr st x in
    match st, ptr, aeval st idx with
    | Scur user mem n, Some ptr', Some idx' =>
      match state_follow_ptr st ptr' with
      | Some arr => update_mem st ptr' (Some (list_insert arr idx' (v st)))
      | _ => st
      end
    | _, _, _ => st
    end.

Definition store_sub X idx v P : Assertion :=
  fun (st : state) =>
    P (update_arr st X idx v).

(*Definition store_sub X idx v P : Assertion :=
  fun (st : state) =>
    let ptr := state_get_ptr st X in
      match ptr, (aeval st idx) with
      | Some ptr', Some idx' =>
        match state_follow_ptr st ptr' with
        | Some arr => P (update_mem st ptr' (Some (list_insert arr idx' v)))
        | _ => True
        end
      | _, _ => True
      end.*)

Notation "P [ X |-> v ]" := (assn_sub X v P) (at level 10).
Notation "P [ X <-| idx |-> v ]" := (store_sub X idx v P) (at level 10).

Inductive com : Type :=
  | CSkip : com
  | CStore : id -> aexp -> (state -> var) -> com
  | CAss : id -> (state -> var) -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Store  : forall st a1 x idx,
      (CStore x idx a1) / st || (update_arr st x idx a1)
  | E_Ass  : forall st a1 x,
      (x ::= a1) / st || (update st x a1)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || st' ->
      c2 / st' || st'' ->
      (c1 ;; c2) / st || st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = Some true ->
      c1 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = Some false ->
      c2 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b st c,
      beval st b = Some false ->
      (WHILE b DO c END) / st || st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = Some true ->
      c / st || st' ->
      (WHILE b DO c END) / st' || st'' ->
      (WHILE b DO c END) / st || st''

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Store" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st || st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_store : forall Q X idx a,
  {{Q [X <-| idx |-> a]}} (CStore X idx a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X idx a st st' HE HQ.
  inversion HE. subst.
  unfold store_sub in HQ. assumption.  Qed.

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st'). 
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP. 
  apply Himp.
  apply (Hhoare st st'). 
  assumption. assumption. Qed.

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst. 
  Case "b is true".
    apply (HTrue st st'). 
      assumption. 
      split. assumption. 
             apply bexp_eval_true. assumption.
  Case "b is false".
    apply (HFalse st st'). 
      assumption. 
      split. assumption.
             apply bexp_eval_false. assumption. Qed.

Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction 
     on [He], because, in the "keep looping" case, its hypotheses 
     talk about the whole loop instead of just [c]. *)
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  ceval_cases (induction He) Case;
    try (inversion Heqwcom); subst; clear Heqwcom.
  Case "E_WhileEnd".
    split. assumption. apply bexp_eval_false. assumption.
  Case "E_WhileLoop".
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

Inductive dcom : Type :=
  | DCSkip :  Assertion -> dcom
  | DCSeq : dcom -> dcom -> dcom
  | DCStore : id -> aexp -> (state -> var) -> Assertion -> dcom
  | DCAsgn : id -> (state -> var) ->  Assertion -> dcom
  | DCIf : bexp ->  Assertion -> dcom ->  Assertion -> dcom
           -> Assertion-> dcom
  | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
  | DCPre : Assertion -> dcom -> dcom
  | DCPost : dcom -> Assertion -> dcom.


Tactic Notation "dcom_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Skip" | Case_aux c "Seq" | Case_aux c "Store" | Case_aux c "Asgn"
  | Case_aux c "If" | Case_aux c "While"
  | Case_aux c "Pre" | Case_aux c "Post" ].

Notation "'SKIP' {{ P }}"
      := (DCSkip P)
      (at level 10) : dcom_scope.
Notation "l '::=' a {{ P }}"
      := (DCAsgn l a P)
      (at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
      (at level 80, right associativity) : dcom_scope.
Notation "'IFB' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI' {{ Q }}"
      := (DCIf b P d P' d' Q)
      (at level 80, right associativity)  : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
      (at level 90, right associativity)  : dcom_scope.
Notation "{{ P }} d"
      := (DCPre P d)
      (at level 90)  : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
      (at level 80, right associativity)  : dcom_scope.
Notation " d ;; d' "
      := (DCSeq d d')
      (at level 80, right associativity)  : dcom_scope.

Delimit Scope dcom_scope with dcom.

Fixpoint extract (d:dcom) : com :=
  match d with
  | DCSkip _           => SKIP
  | DCSeq d1 d2        => (extract d1 ;; extract d2)
  | DCStore X idx a _  => (CStore X idx a)
  | DCAsgn X a _       => X ::= a
  | DCIf b _ d1 _ d2 _ => IFB b THEN extract d1 ELSE extract d2 FI
  | DCWhile b _ d _    => WHILE b DO extract d END
  | DCPre _ d          => extract d
  | DCPost d _         => extract d
  end.

Fixpoint post (d:dcom) : Assertion :=
  match d with
  | DCSkip P                => P
  | DCSeq d1 d2             => post d2
  | DCStore X idx v Q       => Q
  | DCAsgn X v Q            => Q
  | DCIf  _ _ d1 _ d2 Q     => Q
  | DCWhile b Pbody c Ppost => Ppost
  | DCPre _ d               => post d
  | DCPost c Q              => Q
  end.

Fixpoint pre (d:dcom) : Assertion :=
  match d with
  | DCSkip P                => fun st => True
  | DCSeq c1 c2             => pre c1
  | DCStore X idx v Q       => fun st => True
  | DCAsgn X a Q            => fun st => True
  | DCIf  _ _ t _ e _       => fun st => True
  | DCWhile b Pbody c Ppost => fun st => True
  | DCPre P c               => P
  | DCPost c Q              => pre c
  end.

Fixpoint verification_conditions (P : Assertion) (d:dcom) : Prop :=
  match d with
  | DCSkip Q          =>
      (P ->> Q)
  | DCSeq d1 d2      =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCStore X idx v Q      =>
      (P ->> Q [X <-| idx |-> v])
  | DCAsgn X a Q      =>
      (P ->> Q [X |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((fun st => P st /\ bassn b st) ->> P1)
      /\ ((fun st => P st /\ ~ (bassn b st)) ->> P2)
      /\ (Q <<->> post d1) /\ (Q <<->> post d2)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost      =>
      (* post d is the loop invariant and the initial precondition *)
      (P ->> post d)
      /\ (Pbody <<->> (fun st => post d st /\ bassn b st))
      /\ (Ppost <<->> (fun st => post d st /\ ~(bassn b st)))
      /\ verification_conditions Pbody d
  | DCPre P' d         =>
      (P ->> P') /\ verification_conditions P' d
  | DCPost d Q        =>
      verification_conditions P d /\ (post d ->> Q)
  end.


Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} (extract d) {{post d}}.
Proof.
  dcom_cases (induction d) Case; intros P H; simpl in *.
  Case "Skip".
    eapply hoare_consequence_pre.
      apply hoare_skip.
      assumption.
  Case "Seq".
    inversion H as [H1 H2]. clear H.
    eapply hoare_seq.
      apply IHd2. apply H2.
      apply IHd1. apply H1.
  Case "Store".
    eapply hoare_consequence_pre.
      apply hoare_store.

      assumption.
  Case "Asgn".
    eapply hoare_consequence_pre.
      apply hoare_asgn.
      assumption.
  Case "If".
    inversion H as [HPre1 [HPre2 [[Hd11 Hd12]
                                  [[Hd21 Hd22] [HThen HElse]]]]].
    clear H.
    apply IHd1 in HThen. clear IHd1.
    apply IHd2 in HElse. clear IHd2.
    apply hoare_if.
      eapply hoare_consequence_pre; eauto.
      eapply hoare_consequence_post; eauto.
      eapply hoare_consequence_pre; eauto.
      eapply hoare_consequence_post; eauto.
  Case "While".
    inversion H as [Hpre [[Hbody1 Hbody2] [[Hpost1 Hpost2]  Hd]]];
    subst; clear H.
    eapply hoare_consequence_pre; eauto.
    eapply hoare_consequence_post; eauto.
    apply hoare_while.
    eapply hoare_consequence_pre; eauto.
  Case "Pre".
    inversion H as [HP Hd]; clear H.
    eapply hoare_consequence_pre. apply IHd. apply Hd. assumption.
  Case "Post".
    inversion H as [Hd HQ]; clear H.
    eapply hoare_consequence_post. apply IHd. apply Hd. assumption.
Qed.

Theorem update_eq : forall n x st,
  state_get (update st x n) x = n st.
Proof.
  intros.
  unfold update. unfold state_get.
  destruct st. apply eq_id.
  Qed.
(** [] *)

Theorem update_neq : forall x2 x1 n st,
  x2 <> x1 ->                        
  state_get (update st x2 n) x1 = (state_get st x1).
Proof.
  intros.
  unfold update. unfold state_get.
  destruct st. apply neq_id.
  apply H.
  Qed.

Lemma ble_nat_true_iff : forall n m : nat,
  ble_nat n m = true <-> n <= m.
Proof.
  intros n m. split. apply ble_nat_true.
  generalize dependent m. induction n; intros m H. reflexivity.
    simpl. destruct m. inversion H.
    apply le_S_n in H. apply IHn. assumption.
Qed.

Lemma ble_nat_false_iff : forall n m : nat,
  ble_nat n m = false <-> ~(n <= m).
Proof.
  intros n m. split. apply ble_nat_false.
  generalize dependent m. induction n; intros m H.
    apply ex_falso_quodlibet. apply H. apply le_0_n.
    simpl. destruct m. reflexivity.
    apply IHn. intro Hc. apply H. apply le_n_S. assumption.
Qed.

Tactic Notation "verify" :=
  apply verification_correct;
  repeat split;
  simpl; unfold assert_implies;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat rewrite update_eq;
  repeat (rewrite update_neq; [| (intro X; inversion X)]);
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite beq_nat_true_iff in *;
  repeat rewrite beq_nat_false_iff in *;
  repeat rewrite ble_nat_true_iff in *;
  repeat rewrite ble_nat_false_iff in *;
  try subst;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
          [H : st _ = _ |- _] => rewrite -> H in *; clear H
        | [H : _ = st _ |- _] => rewrite <- H in *; clear H
        end
    end;
  try eauto; try omega.




Definition num (n: nat): var :=
  Vnum (nat_to_jnum n 8).

Definition sum (n1 n2: var): var :=
  match n1, n2 with
  | Vnum n1', Vnum n2' => Vnum (jnum_plus n1' n2')
  | _, _ => Vnone
  end.

Definition sub (n1 n2: var): var :=
  match n1, n2 with
  | Vnum n1', Vnum n2' => Vnum (jnum_sub n1' n2')
  | _, _ => Vnone
  end.

Definition eq (n1 n2: var): var :=
  match n1, n2 with
  | Vnum n1', Vnum n2' => Vbool (jnum_eq n1' n2')
  | _, _ => Vnone
  end.

Definition neq (n1 n2: var): var :=
  match n1, n2 with
  | Vnum n1', Vnum n2' => Vbool (negb (jnum_eq n1' n2'))
  | _, _ => Vnone
  end.


Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.


Example slow_assignment_dec (m:nat) : dcom := (
      {{ fun st => state_get st X = num m }}
    Y ::= Aeval (ANum 0)
      {{ fun st => state_get st X = num m /\ state_get st Y = num 0 }} ->>
      {{ fun st => sum (state_get st X) (state_get st Y) = num m }} ;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
        {{ fun st => sum (state_get st X) (state_get st Y) = num m /\ neq (state_get st X) (num 0) = Vbool true }} ->>
        {{ fun st => sum (sub (state_get st X) (num 1)) (sum (state_get st Y) (num 1)) = num m }}
      X ::= Aeval (AMinus (AId X) (ANum 1))
        {{ fun st => sum (state_get st X) (sum (state_get st Y) (num 1)) = num m }} ;;
      Y ::= Aeval (APlus (AId Y) (ANum 1))
        {{ fun st => sum (state_get st X) (state_get st Y) = num m }}
    END
      {{ fun st => sum (state_get st X) (state_get st Y) = num m /\ eq (state_get st X) (num 0) = Vbool true }} ->>
      {{ fun st => state_get st Y = num m }}
) % dcom.

Definition dec_correct (d:dcom) :=
  {{pre d}} (extract d) {{post d}}.

Theorem slow_assignment_dec_correct : forall m,
  dec_correct (slow_assignment_dec m).
Proof. intros m. verify.
  rewrite H. rewrite H0. simpl.