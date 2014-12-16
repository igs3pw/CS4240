(**
 * This is a simplistic Hoare logic verifier for Java programs.
 * There are a few simplifications.
 * Exceptions aren't modeled. 
 * Floating point numbers aren't modeled.
 * *** Add stuff as I find it ***
 *)

Require Export SfLib.
Require Export Arith.
Require Export Arith.Div2.

(* In java, all integers are two's complement and signed *)
(* They are stored as a sequence of bits (ie. booleans) *)

(**
 * Promotion rules (Binary):
 * *** Floating point rules ***
 * Otherwise, if either operand is of type long, the other is converted to long.
 * Otherwise, both operands are converted to type int.
 *
 * Promotion rules (Binary):
 * *** Floating point rules ***
 * Otherwise, if the operand is of compile-time type byte, short, or char, it is promoted to a value of type int by a widening primitive conversion.
 * Otherwise, a unary numeric operand remains as is and is not converted.
 *)

Inductive jnum := 
| jend: bool -> jnum
| jbit: bool -> jnum -> jnum.

Definition jnum_promotion (n1 n2: nat): nat :=
  match (leb n1 n2), (leb n1 31), (leb n2 31) with
  | true, _, true => 31
  | true, _, false => n2
  | false, true, _ => 31
  | false, false, _ => n1
  end.

(* Treat the java number as unsigned and convert it into a natural number *)
Fixpoint jnum_width (n: jnum): nat :=
  match n with
  | jend _ => 0
  | jbit _ n' => 1 + jnum_width n'
  end.

Fixpoint jnum_to_nat (n: jnum): nat :=
  match n with
  | jend false => 0
  | jend true => 1
  | jbit false n' => 2 * jnum_to_nat n'
  | jbit true n' => 1 + 2 * jnum_to_nat n'
  end.

Fixpoint oddb (n: nat): bool :=
  match n with
  | O => false
  | S O => true
  | S (S n') => oddb n'
  end.

Theorem oddb_false: forall n,
  oddb (2 * n) = false.
Proof.
  simpl.
  induction n.
    reflexivity.

    simpl. rewrite <- plus_n_Sm. assumption.
  Qed.

Theorem oddb_true: forall n,
  oddb (1 + 2 * n) = true.
Proof.
  simpl.
  induction n.
    reflexivity.

    simpl. rewrite <- plus_n_Sm. assumption.
  Qed.

Fixpoint nat_to_jnum (n width: nat): jnum :=
  match width with
  | O => jend (oddb n)
  | S width' => jbit (oddb n) (nat_to_jnum (div2 n) width')
  end.

Theorem jconversion_reflexive: forall jn,
  nat_to_jnum (jnum_to_nat jn) (jnum_width jn) = jn.
Proof.
  intros jn.
  induction jn.
    simpl.
    destruct b; reflexivity.

    simpl. rewrite plus_0_r.
    assert(jnum_to_nat jn + jnum_to_nat jn = 2 * jnum_to_nat jn). simpl. rewrite plus_0_r. trivial.
    rewrite H.

    destruct b. 
      rewrite oddb_true. rewrite div2_double_plus_one. rewrite IHjn. trivial.

      rewrite oddb_false. rewrite div2_double. rewrite IHjn. trivial.
  Qed. 

Fixpoint jnum_is_neg (n: jnum): bool :=
  match n with
  | jend b => b
  | jbit _ n' => jnum_is_neg n'
  end.

Fixpoint jnum_promote (jn: jnum) (n: nat): jnum :=
  match n with
  | O =>
    match jn with
    | jend b => jend b
    | jbit b jn' => jend b
    end
  | S n' => 
    match jn with
    | jend b => jbit b (jnum_promote jn n')
    | jbit b jn' => jbit b (jnum_promote jn' n')
    end
  end.

Fixpoint jnum_zero (n: nat): jnum :=
  match n with
  | O => jend false
  | S n' => jbit false (jnum_zero n')
  end.

Fixpoint jnum_one (n: nat): jnum :=
  match n with
  | O => jend true
  | S n' => jbit true (jnum_zero n')
  end.

Fixpoint jnum_append (n1 n2: jnum): jnum :=
  match n1 with
  | jend b => jbit b n2
  | jbit b n1' => jbit b (jnum_append n1' n2)
  end.

Fixpoint jnum_negb (n: jnum): jnum :=
  match n with
  | jend b => jend (negb b)
  | jbit b n' => jbit (negb b) (jnum_negb n')
  end.

Fixpoint jnum_orb (n1 n2: jnum): jnum :=
  match n1, n2 with
  | jbit b1 n1', jbit b2 n2' => jbit (orb b1 b2) (jnum_orb n1' n2')
  | jbit b1 n1', jend b2 => jbit (orb b1 b2) (jnum_orb n1' n2)
  | jend b1, _ => if b1
                  then jnum_one (jnum_width n2)
                  else n2
  end.

Fixpoint jnum_andb (n1 n2: jnum): jnum :=
  match n1, n2 with
  | jbit b1 n1', jbit b2 n2' => jbit (orb b1 b2) (jnum_orb n1' n2')
  | jbit b1 n1', jend b2 => jbit (orb b1 b2) (jnum_orb n1' n2)
  | jend b1, _ => if b1
                  then n2
                  else jnum_zero (jnum_width n2)
  end.

Fixpoint jnum_xorb (n1 n2: jnum): jnum :=
  match n1, n2 with
  | jbit b1 n1', jbit b2 n2' => jbit (xorb b1 b2) (jnum_orb n1' n2')
  | jbit b1 n1', jend b2 => jbit (xorb b1 b2) (jnum_orb n1' n2)
  | jend b1, _ => if b1
                  then jnum_negb n2
                  else n2
  end.

Definition bool_sum (b1 b2 b3: bool): bool :=
  match b1, b2, b3 with
  | true, true, true => true
  | false, false, true => true
  | false, true, false => true
  | true, false, false => true
  | _, _, _ => false
  end.

Definition bool_sum_carry (b1 b2 b3: bool): bool :=
  match b1, b2, b3 with
  | true, true, true => true
  | true, true, _ => true
  | true, _, true => true
  | _, true, true => true
  | _, _, _ => false
  end.

Fixpoint jnum_plus0_fix (n: jnum) (c: bool): jnum :=
  if c
  then 
    match n with
    | jbit b n' => jbit (negb b) (jnum_plus0_fix n' b)
    | jend b => jbit (negb b) (jend b)
    end
  (* Nothing to change, short circuit *)
  else n.

Theorem jnum_plus0_correct: forall n c,
  jnum_to_nat (jnum_plus0_fix n c) = jnum_to_nat (jend c) + jnum_to_nat n.
Proof.
  intros n.
  induction n.
    simpl. destruct b; destruct c; reflexivity.

    simpl. destruct b; destruct c; simpl; try rewrite IHn; simpl;
    repeat rewrite <- plus_n_Sm; reflexivity.
  Qed.

Fixpoint jnum_plus_uns (n1 n2: jnum) (c: bool): jnum :=
  match n1, n2 with
  | jbit b1 n1', jbit b2 n2' => jbit (bool_sum b1 b2 c) (jnum_plus_uns n1' n2' (bool_sum_carry b1 b2 c))
  | jbit b1 n1', jend b2 => jbit (bool_sum b1 b2 c) (jnum_plus0_fix n1' (bool_sum_carry b1 b2 c))
  | jend b1, jbit b2 n2' => jbit (bool_sum b1 b2 c) (jnum_plus0_fix n2' (bool_sum_carry b1 b2 c))
  | jend b1, jend b2 => jbit (bool_sum b1 b2 c) (jend (bool_sum_carry b1 b2 c))
  end.

Theorem jnum_plus_correct: forall n1 n2 c,
  jnum_to_nat (jnum_plus_uns n1 n2 c) = 
  jnum_to_nat (jend c) + jnum_to_nat n1 + jnum_to_nat n2.
Proof.
  intros n1.
  induction n1.
    induction n2.
      simpl. destruct b; destruct b0; destruct c; reflexivity.

      simpl. destruct b; destruct b0; destruct c; simpl; rewrite jnum_plus0_correct;
      simpl; repeat rewrite <- plus_n_Sm; reflexivity.
        

    induction n2.
      simpl. destruct b; destruct b0; destruct c; simpl; rewrite jnum_plus0_correct;
      simpl; repeat rewrite <- plus_n_Sm; repeat rewrite plus_0_r; reflexivity.

      assert (jnum_to_nat n2 + (jnum_to_nat n1 + jnum_to_nat n2) = jnum_to_nat n1 + (jnum_to_nat n2 + jnum_to_nat n2)).
        repeat rewrite plus_assoc. rewrite (plus_comm (jnum_to_nat n1) (jnum_to_nat n2)). trivial. 
      simpl. destruct b; destruct b0; destruct c; simpl;
        rewrite IHn1; simpl; repeat rewrite plus_0_r; repeat rewrite <- plus_n_Sm;
        repeat rewrite <- plus_assoc; try rewrite H; trivial.
  Qed.

Definition jnum_plus (n1 n2: jnum): jnum :=
  let n := jnum_promotion (jnum_width n1) (jnum_width n2) in
    jnum_promote (jnum_plus_uns (jnum_promote n1 n) (jnum_promote n2 n) false) n.

(* ~n + 1 *)
Definition jnum_neg_uns (n: jnum): jnum :=
  jnum_plus0_fix (jnum_negb n) true.

Definition jnum_neg (jn: jnum): jnum :=
  let n := jnum_promotion (jnum_width jn) 0 in
    jnum_promote (jnum_neg_uns (jnum_promote jn n)) n.

Definition jnum_sub_uns (n1 n2: jnum) (c: bool): jnum :=
  jnum_plus_uns n1 (jnum_neg_uns n2) c.

Definition jnum_sub (n1 n2: jnum): jnum :=
  let n := jnum_promotion (jnum_width n1) (jnum_width n2) in
    jnum_promote (jnum_sub_uns (jnum_promote n1 n) (jnum_promote n2 n) false) n.

(**
 * sum = 0
 * if (n1 & 1) {
 *   sum += n2
 * }
 * if (n1 & 2) {
 *   sum += n2 << 1
 * }
 * if (n1 & 4) {
 *   sum += n2 << 2
 * }
 * ...
 *)
Fixpoint jnum_mult_uns (n1 n2: jnum): jnum :=
  match n1 with
  | jbit b1 n1' => if b1
                   then jnum_plus_uns (jbit false (jnum_mult_uns n1' n2)) n2 false
                   else jbit false (jnum_mult_uns n1' n2)
  | jend b1     => if b1
                   then n2
                   else jend false
  end.

Compute jnum_to_nat (jnum_mult_uns (nat_to_jnum 3 1) (nat_to_jnum 3 1)).

Theorem jnum_mult_correct: forall n1 n2,
  jnum_to_nat (jnum_mult_uns n1 n2) = (jnum_to_nat n1) * (jnum_to_nat n2).
Proof.
  intros n1.
  induction n1.
    intros n2.
    induction n2;
      destruct b; destruct b0;
        simpl; repeat rewrite plus_0_r; trivial.

    intros n2.
    induction n2.
      simpl. destruct b; destruct b0; simpl; try rewrite jnum_plus0_correct;
      simpl; rewrite IHn1; simpl; repeat rewrite plus_0_r; repeat rewrite mult_1_r;
      repeat rewrite mult_0_r; trivial.

      simpl. destruct b; destruct b0; simpl; repeat rewrite plus_0_r; 
      try rewrite jnum_plus_correct; simpl; rewrite IHn1; simpl; repeat rewrite plus_0_r; 
      repeat rewrite <- mult_n_Sm; repeat rewrite mult_plus_distr_l;
      repeat rewrite mult_plus_distr_r; omega.
  Qed.

Definition jnum_mult (n1 n2: jnum): jnum :=
  let n := jnum_promotion (jnum_width n1) (jnum_width n2) in
    jnum_promote (jnum_mult_uns (jnum_promote n1 n) (jnum_promote n2 n)) n.

Fixpoint jnum_is_zero (n: jnum): bool :=
  match n with
  | jbit b n' => if b then false else jnum_is_zero n'
  | jend b => negb b
  end.

Theorem jnum_is_zero_correct: forall n,
  jnum_is_zero (nat_to_jnum 0 n) = true.
Proof.
  induction n.
    reflexivity.

    simpl. assumption.
  Qed.

Theorem jnum_is_zero_correct2: forall n,
  jnum_to_nat n = 0 -> 
  jnum_is_zero n = true.
Proof.
  induction n.
    simpl. intros H. destruct b. inversion H. reflexivity.

    simpl. intros H. destruct b. inversion H.
      apply IHn. destruct (jnum_to_nat n).
        reflexivity.

        inversion H.
  Qed.

Theorem jnum_zero_implies: forall n,
  jnum_is_zero n = true ->
  jnum_to_nat n = 0.
Proof.
  induction n.
    simpl. intros H. destruct b. inversion H. reflexivity.

    simpl. intros H. destruct b. inversion H.
      rewrite IHn.
        reflexivity.

        assumption.
  Qed.

Fixpoint jnum_eq_uns (n1 n2: jnum): bool :=
  match n1, n2 with
  | jbit b1 n1', jbit b2 n2' => if xorb b1 b2 then false else jnum_eq_uns n1' n2'
  | jend b1, jend b2 => if xorb b1 b2 then false else true
  | jbit b1 n1', jend b2 => if xorb b1 b2 then false else jnum_is_zero n1'
  | jend b1, jbit b2 n2' => if xorb b1 b2 then false else jnum_is_zero n2'
  end.

Definition jnum_eq (n1 n2: jnum): bool :=
  let n := jnum_promotion (jnum_width n1) (jnum_width n2) in
    jnum_eq_uns (jnum_promote n1 n) (jnum_promote n2 n).

Fixpoint jnum_leq_uns (n1 n2: jnum): bool :=
  match n1, n2 with
  | jbit b1 n1', jbit b2 n2' => if jnum_eq_uns n1' n2' then orb b2 (negb b1) else jnum_leq_uns n1' n2'
  | jend b1, jend b2 => orb b2 (negb b1)
  | jbit b1 n1', jend b2 => if jnum_is_zero n1' then orb b2 (negb b1) else false
  | jend b1, jbit b2 n2' => if jnum_is_zero n2' then orb b2 (negb b1) else true
  end.

Definition jnum_leq (n1 n2: jnum): bool :=
  let n := jnum_promotion (jnum_width n1) (jnum_width n2) in
    match jnum_is_neg n1, jnum_is_neg n2 with
    | true, false => false
    | false, true => true
    | _, _ => jnum_leq_uns (jnum_promote n1 n) (jnum_promote n2 n)
    end.

Require Export Bool.

Theorem jnum_eq_correct: forall n1 n2,
  jnum_to_nat n1 = jnum_to_nat n2 -> 
  jnum_eq_uns n1 n2 = true.
Proof.
  induction n1; induction n2.
    destruct b; destruct b0; simpl; intros H; inversion H; reflexivity.

    destruct b; destruct b0; simpl; repeat rewrite plus_0_r;
    repeat rewrite <- plus_n_Sm; intros H; inversion H; simpl in IHn2.
      destruct (jnum_to_nat n2) eqn:Hn2; repeat rewrite <- plus_n_Sm in H; inversion H.
      apply jnum_is_zero_correct2. assumption.

      destruct (jnum_to_nat n2); repeat rewrite <- plus_n_Sm in H; inversion H.

      destruct (jnum_to_nat n2) eqn:Hn2; repeat rewrite <- plus_n_Sm in H; inversion H.
      apply jnum_is_zero_correct2. assumption.

    destruct b; destruct b0; simpl; repeat rewrite plus_0_r;
    repeat rewrite <- plus_n_Sm; intros H; inversion H; simpl in IHn1.
      destruct (jnum_to_nat n1) eqn:Hn1; repeat rewrite <- plus_n_Sm in H; inversion H.
      apply jnum_is_zero_correct2. assumption.

      destruct (jnum_to_nat n1); repeat rewrite <- plus_n_Sm in H; inversion H.

      destruct (jnum_to_nat n1) eqn:Hn1; repeat rewrite <- plus_n_Sm in H; inversion H.
      apply jnum_is_zero_correct2. assumption.

    destruct b; destruct b0; simpl; repeat rewrite plus_0_r;
    repeat rewrite <- plus_n_Sm; intros H; inversion H; simpl in IHn1.
      apply IHn1. destruct (jnum_to_nat n1); destruct (jnum_to_nat n2); inversion H1.
        reflexivity.

        omega. (* Magic *)

      omega. 

      omega. 

      apply IHn1. omega.
  Qed.

Fixpoint jnum_mod_uns (n1 n2: jnum): jnum :=
  match n1 with
  (* 0 % 1 = 0, 1 % 1 = 0, 0 % ...1 = 0, 1 % ...1 = 1 *) 
  | jend b1 => if jnum_leq_uns n2 n1 then jend false else jend b1
  | jbit b1 n1' => let n := jbit b1 (jnum_mod_uns n1' n2) in
                     if jnum_leq_uns n2 n
                     then jnum_promote (jnum_sub_uns n n2 false) (jnum_width n2)
                     else n
  end.

Definition jnum_mod (n1 n2: jnum): jnum :=
  let n := jnum_promotion (jnum_width n1) (jnum_width n2) in
    jnum_promote (jnum_mod_uns (jnum_promote n1 n) (jnum_promote n2 n)) n.

Fixpoint jnum_div_uns (n1 n2: jnum): jnum :=
  match n1 with
  | jend b1 => if jnum_leq_uns n2 n1 then jend true else jend false
  | jbit b1 n1' => let n := jnum_div_uns n1' n2 in
                     let n' := jnum_promote (jbit b1 (jnum_sub_uns n1' (jnum_mult_uns n2 n) false)) (jnum_width n2) in
                       if jnum_leq_uns n2 n' then jbit true n else jbit false n
  end.

Definition jnum_div (n1 n2: jnum): jnum :=
  let n := jnum_promotion (jnum_width n1) (jnum_width n2) in
    jnum_promote (jnum_div_uns (jnum_promote n1 n) (jnum_promote n2 n)) n.

Compute jnum_mod_uns (nat_to_jnum 41 16) (nat_to_jnum 7 16).
Compute jnum_div_uns (nat_to_jnum 41 16) (nat_to_jnum 7 16).
Compute jnum_to_nat (jnum_div_uns (nat_to_jnum 289 16) (nat_to_jnum 17 16)).

(*Theorem jnum_div_correct: forall n1 n2,
  jnum_to_nat n2 <> 0 ->
  jnum_to_nat (jnum_plus_uns (jnum_mult_uns (jnum_div_uns n1 n2) n2) (jnum_mod_uns n1 n2) false) = jnum_to_nat n1.
Proof.
  intros n1.
  induction n1.
    intros n2.
    rewrite jnum_plus_correct. simpl. rewrite jnum_mult_correct. simpl.
    induction n2.
      simpl. destruct b; destruct b0; simpl; try reflexivity.
        intros H; apply ex_falso_quodlibet; apply H; reflexivity.

      simpl. destruct b; destruct b0; simpl;
      destruct (jnum_is_zero n2) eqn:Hn2; simpl; repeat rewrite plus_0_r;
      try trivial.
        rewrite jnum_zero_implies.
          reflexivity.

          assumption.

        rewrite jnum_zero_implies.
          intros H. apply ex_falso_quodlibet; apply H; reflexivity.

          assumption.

        rewrite jnum_zero_implies.
          intros H. apply ex_falso_quodlibet; apply H; reflexivity.

          assumption.

    intros n2.
    rewrite jnum_plus_correct. simpl. rewrite jnum_mult_correct. simpl.
    induction n2.
      destruct b0; try (intros H; apply ex_falso_quodlibet; apply H; reflexivity).
      simpl. destruct b; simpl.

    admit.
  Qed.*)

Definition jnum_256 := nat_to_jnum 256 31.
Definition jnum_65536 := jnum_mult jnum_256 jnum_256.
Definition jnum_2_32 := jnum_mult jnum_65536 jnum_65536.

Compute jnum_to_nat jnum_2_32.
Compute jnum_mod_uns jnum_256 jnum_65536.
Compute jnum_div_uns jnum_65536 jnum_256.



Fixpoint jnum_shl_fix (n1: jnum) (n2: nat): jnum :=
  match n2 with
  | O => n1
  | S n2' => jbit false (jnum_shl_fix n1 n2')
  end.
    

Fixpoint jnum_shr_fix (n1: jnum) (n2: nat): jnum :=
  match n2 with
  | O => n1
  | S n2' =>
    match n1 with
    | jend _ => jend false
    | jbit _ n1' => jnum_shr_fix n1' n2'
    end
  end.