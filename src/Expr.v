Require Import FinFun.
Require Import BinInt ZArith_dec.
Require Export Id.
Require Export State.
Require Export Lia.

Require Import List.
Import ListNotations.

From hahn Require Import HahnBase.

Require Import Coq.Program.Equality.

(* Type of binary operators *)
Inductive bop : Type :=
| Add : bop
| Sub : bop
| Mul : bop
| Div : bop
| Mod : bop
| Le  : bop
| Lt  : bop
| Ge  : bop
| Gt  : bop
| Eq  : bop
| Ne  : bop
| And : bop
| Or  : bop.

(* Type of arithmetic expressions *)
Inductive expr : Type :=
| Nat : Z -> expr
| Var : id  -> expr
| Bop : bop -> expr -> expr -> expr.

(* Supplementary notation *)
Notation "x '[+]'  y" := (Bop Add x y) (at level 40, left associativity).
Notation "x '[-]'  y" := (Bop Sub x y) (at level 40, left associativity).
Notation "x '[*]'  y" := (Bop Mul x y) (at level 41, left associativity).
Notation "x '[/]'  y" := (Bop Div x y) (at level 41, left associativity).
Notation "x '[%]'  y" := (Bop Mod x y) (at level 41, left associativity).
Notation "x '[<=]' y" := (Bop Le  x y) (at level 39, no associativity).
Notation "x '[<]'  y" := (Bop Lt  x y) (at level 39, no associativity).
Notation "x '[>=]' y" := (Bop Ge  x y) (at level 39, no associativity).
Notation "x '[>]'  y" := (Bop Gt  x y) (at level 39, no associativity).
Notation "x '[==]' y" := (Bop Eq  x y) (at level 39, no associativity).
Notation "x '[/=]' y" := (Bop Ne  x y) (at level 39, no associativity).
Notation "x '[&]'  y" := (Bop And x y) (at level 38, left associativity).
Notation "x '[\/]' y" := (Bop Or  x y) (at level 38, left associativity).

Definition zbool (x : Z) : Prop := x = Z.one \/ x = Z.zero.

Definition zor (x y : Z) : Z :=
  if Z_le_gt_dec (Z.of_nat 1) (x + y) then Z.one else Z.zero.

Reserved Notation "[| e |] st => z" (at level 0).
Notation "st / x => y" := (st_binds Z st x y) (at level 0).

(* Big-step evaluation relation *)
Inductive eval : expr -> state Z -> Z -> Prop :=
  bs_Nat  : forall (s : state Z) (n : Z), [| Nat n |] s => n

| bs_Var  : forall (s : state Z) (i : id) (z : Z) (VAR : s / i => z),
    [| Var i |] s => z

| bs_Add  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb),
    [| a [+] b |] s => (za + zb)

| bs_Sub  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb),
    [| a [-] b |] s => (za - zb)

| bs_Mul  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb),
    [| a [*] b |] s => (za * zb)

| bs_Div  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (NZERO : ~ zb = Z.zero),
    [| a [/] b |] s => (Z.div za zb)

| bs_Mod  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (NZERO : ~ zb = Z.zero),
    [| a [%] b |] s => (Z.modulo za zb)

| bs_Le_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.le za zb),
    [| a [<=] b |] s => Z.one

| bs_Le_F : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.gt za zb),
    [| a [<=] b |] s => Z.zero

| bs_Lt_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.lt za zb),
    [| a [<] b |] s => Z.one

| bs_Lt_F : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.ge za zb),
    [| a [<] b |] s => Z.zero

| bs_Ge_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.ge za zb),
    [| a [>=] b |] s => Z.one

| bs_Ge_F : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.lt za zb),
    [| a [>=] b |] s => Z.zero

| bs_Gt_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.gt za zb),
    [| a [>] b |] s => Z.one

| bs_Gt_F : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.le za zb),
    [| a [>] b |] s => Z.zero

| bs_Eq_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.eq za zb),
    [| a [==] b |] s => Z.one

| bs_Eq_F : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : ~ Z.eq za zb),
    [| a [==] b |] s => Z.zero

| bs_Ne_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : ~ Z.eq za zb),
    [| a [/=] b |] s => Z.one

| bs_Ne_F : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.eq za zb),
    [| a [/=] b |] s => Z.zero

| bs_And  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (BOOLA : zbool za)
                   (BOOLB : zbool zb),
    [| a [&] b |] s => (za * zb)

| bs_Or   : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (BOOLA : zbool za)
                   (BOOLB : zbool zb),
    [| a [\/] b |] s => (zor za zb)
where "[| e |] st => z" := (eval e st z).

#[export] Hint Constructors eval : core.

Module SmokeTest.

  Lemma zero_always x (s : state Z) (n : Z) (H: s / x => n) : [| Var x [*] Nat 0 |] s => Z.zero.
  Proof.
    assert ((n * Z.zero)%Z = Z.zero).
    - apply Zmult_comm.
    - inversion H0.
      auto.
  Qed.

  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof.
    apply bs_Nat.
  Qed.

  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    inversion HH. subst. clear HH.
    inversion VALB. subst. clear VALB.
    assert ((za * 2)%Z = (za + za)%Z).
    - lia.
    - rewrite H. clear H. apply bs_Add; assumption.
  Qed.

End SmokeTest.

(* A relation of one expression being of a subexpression of another *)
Reserved Notation "e1 << e2" (at level 0).

Inductive subexpr : expr -> expr -> Prop :=
  subexpr_refl : forall e : expr, e << e
| subexpr_left : forall e e' e'' : expr, forall op : bop, e << e' -> e << (Bop op e' e'')
| subexpr_right : forall e e' e'' : expr, forall op : bop, e << e'' -> e << (Bop op e' e'')
where "e1 << e2" := (subexpr e1 e2).

Lemma strictness (e e' : expr) (HSub : e' << e) (st : state Z)
  (z : Z) (HV : [| e |] st => z) :
  exists z' : Z, [| e' |] st => z'.
Proof.
  generalize dependent z.
  induction HSub.
  - intros. exists z. assumption.
  - intros. inversion HV; subst;
    specialize IHHSub with (z := za); apply IHHSub; clear IHHSub; assumption.
  - intros. inversion HV; subst;
    specialize IHHSub with (z := zb); apply IHHSub; clear IHHSub; assumption.
Qed.

Reserved Notation "x ? e" (at level 0).

(* Set of variables is an expression *)
Inductive V : expr -> id -> Prop :=
  v_Var : forall (id : id), id ? (Var id)
| v_Bop : forall (id : id) (a b : expr) (op : bop), id ? a \/ id ? b -> id ? (Bop op a b)
where "x ? e" := (V e x).

#[export] Hint Constructors V : core.

(* If an expression is defined in some state, then each its' variable is
   defined in that state
 *)
Lemma defined_expression
      (e : expr) (s : state Z) (z : Z) (id : id)
      (RED : [| e |] s => z)
      (ID  : id ? e) :
  exists z', s / id => z'.
Proof.
  generalize dependent z.
  induction e.
  - exfalso. inversion ID.
  - intros. exists z. inversion ID; subst. inversion RED. assumption.
  - inversion ID; subst; intros.
    destruct H3.
    * inversion RED; subst;
      apply (IHe1 H za); assumption.
    * inversion RED; subst;
      apply (IHe2 H zb); assumption.
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  unfold not.
  intros.
  pose proof (Hh := defined_expression e s z id H ID).
  destruct Hh.
  specialize UNDEF with x.
  contradiction.
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z)
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  generalize dependent z1.
  generalize dependent z2.
  induction e.
  - intros. inversion E1; subst. inversion E2; subst. auto.
  - intros. inversion E1; subst. inversion E2; subst.
    apply (state_deterministic Z s i z1 z2 VAR VAR0).
  - intros. inversion E1; subst;
    pose proof (IHe1 za VALA);
    pose proof (IHe2 zb VALB);
    clear IHe1 IHe2 E1 VALA VALB;
    inversion E2; subst;
    pose proof (H za0 VALA);
    pose proof (H0 zb0 VALB);
    subst; try lia; try contradiction.
Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z : Z, s1 /id => z <-> s2 / id => z.

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (id : id) (ID : id ? e),
          equivalent_states s1 s2 id)
      (EV : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof.
  generalize dependent z.
  induction e.
  - intros.
    inversion EV; subst.
    constructor.
  - intros.
    inversion EV; subst.
    constructor.
    pose proof (H := FV i (v_Var i) z).
    apply H. assumption.
  - intros. inversion EV; subst;
    try constructor; subst.
    (* Bool operations solve *)
    all: try assumption.
    (* Arith operations solve *)
    all: try apply IHe1;
       intros; try apply FV; try apply v_Bop; try left; try assumption; try assumption.
    all: try apply IHe2;
       intros; try apply FV; try apply v_Bop; try right; try assumption; try assumption.
    (* Cmp operations solve *)
    all: econstructor; eauto.
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z),
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof.
  unfold "~~".
  intros.
  split; intro; assumption.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
  unfold "~~".
  unfold "~~" in EQ.
  intros.
  specialize EQ with n s.
  split.
  * apply <- EQ.
  * apply -> EQ.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  unfold "~~".
  unfold "~~" in EQ1.
  unfold "~~" in EQ2.
  intros.
  specialize EQ1 with n s.
  specialize EQ2 with n s.
  split.
  * intro. apply -> EQ2. apply -> EQ1. assumption.
  * intro. apply <- EQ1. apply <- EQ2. assumption.
Qed.

Inductive Context : Type :=
| Hole : Context
| BopL : bop -> Context -> expr -> Context
| BopR : bop -> expr -> Context -> Context.

Fixpoint plug (C : Context) (e : expr) : expr :=
  match C with
  | Hole => e
  | BopL b C e1 => Bop b (plug C e) e1
  | BopR b e1 C => Bop b e1 (plug C e)
  end.

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

Definition contextual_equivalent (e1 e2 : expr) : Prop :=
  forall (C : Context), (C <~ e1) ~~ (C <~ e2).

Notation "e1 '~c~' e2" := (contextual_equivalent e1 e2)
                            (at level 42, no associativity).

Lemma eq_eq_ceq (e1 e2 : expr) :
  e1 ~~ e2 <-> e1 ~c~ e2.
Proof.
  split.
  - intros.
    unfold "~c~".
    intros.
    induction C; auto.
    (* Expand cases (way + op) *)
    all: simpl; split; intros; inversion_clear H0.
    (* Proof most of ops *)
    all: subst; try constructor.
    all: try apply IHC; try assumption.
    (* Proof cmp ops *)
    all: econstructor; eauto; apply IHC; eauto.
  - intros.
    unfold "~c~" in H.
    intros.
    specialize H with Hole.
    simpl in H. assumption.
Qed.

Module SmallStep.

  Inductive is_value : expr -> Prop :=
    isv_Intro : forall n, is_value (Nat n).

  Reserved Notation "st |- e --> e'" (at level 0).

  Inductive ss_step : state Z -> expr -> expr -> Prop :=
    ss_Var   : forall (s   : state Z)
                      (i   : id)
                      (z   : Z)
                      (VAL : s / i => z), (s |- (Var i) --> (Nat z))
  | ss_Left  : forall (s      : state Z)
                      (l r l' : expr)
                      (op     : bop)
                      (LEFT   : s |- l --> l'), (s |- (Bop op l r) --> (Bop op l' r))
  | ss_Right : forall (s      : state Z)
                      (l r r' : expr)
                      (op     : bop)
                      (RIGHT  : s |- r --> r'), (s |- (Bop op l r) --> (Bop op l r'))
  | ss_Bop   : forall (s       : state Z)
                      (zl zr z : Z)
                      (op      : bop)
                      (EVAL    : [| Bop op (Nat zl) (Nat zr) |] s => z), (s |- (Bop op (Nat zl) (Nat zr)) --> (Nat z))
  where "st |- e --> e'" := (ss_step st e e').

  #[export] Hint Constructors ss_step : core.

  Reserved Notation "st |- e ~~> e'" (at level 0).

  Inductive ss_reachable st e : expr -> Prop :=
    reach_base : st |- e ~~> e
  | reach_step : forall e' e'' (HStep : SmallStep.ss_step st e e') (HReach : st |- e' ~~> e''), st |- e ~~> e''
  where "st |- e ~~> e'" := (ss_reachable st e e').

  #[export] Hint Constructors ss_reachable : core.

  Reserved Notation "st |- e -->> e'" (at level 0).

  Inductive ss_eval : state Z -> expr -> expr -> Prop :=
    se_Stop : forall (s : state Z)
                     (z : Z),  s |- (Nat z) -->> (Nat z)
  | se_Step : forall (s : state Z)
                     (e e' e'' : expr)
                     (HStep    : s |- e --> e')
                     (Heval    : s |- e' -->> e''), s |- e -->> e''
  where "st |- e -->> e'"  := (ss_eval st e e').

  #[export] Hint Constructors ss_eval : core.

  Lemma ss_eval_reachable s e e' (HE: s |- e -->> e') : s |- e ~~> e'.
  Proof.
    induction HE; eauto.
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof.
    remember (Nat z).
    induction HR; subst.
    - trivial.
    - eapply se_Step.
      * eexact HStep.
      * apply IHHR. trivial.
  Qed.

  #[export] Hint Resolve ss_eval_reachable : core.
  #[export] Hint Resolve ss_reachable_eval : core.

  Lemma ss_eval_assoc s e e' e''
                     (H1: s |- e  -->> e')
                     (H2: s |- e' -->  e'') :
    s |- e -->> e''.
  Proof.
    induction H1.
    - inversion H2.
    - pose proof (Hi := IHss_eval H2).
      clear H2 IHss_eval.
      econstructor.
      * eexact HStep.
      * assumption.
  Qed.

  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
  Proof.
    induction H1.
    - assumption.
    - pose proof (Hi := IHss_reachable H2).
      econstructor.
      * eexact HStep.
      * assumption.
  Qed.

  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof.
    intro.
    unfold not.
    intros.
    inversion HV; subst.
    destruct H.
    inversion H; subst.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
    unfold not.
    intros.
    pose (ex:=Nat 0 [/] Nat 0).
    assert (NV: normal_form (Nat 0 [/] Nat 0)).
    - intro. intro. destruct H0. specialize H with x.
      inversion H0; subst.
      * inversion LEFT.
      * inversion RIGHT.
      * inversion EVAL; subst.
        inversion VALB; subst.
        contradiction.
    - specialize (H ex).
      apply H in NV.
      inversion NV.
  Qed.

  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z),
    s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    unfold not.
    intros.
    pose (rx:=(Nat 1 [+] Nat 1)).
    pose (ex:=rx [+] rx).
    pose (ex'1:=Nat 2 [+] rx).
    pose (ex'2:=rx [+] Nat 2).
    assert (ex'1 <> ex'2).
    - injection. inversion H0.
    - specialize (H ex ex'1 ex'2 []).
      assert ((1 + 1)%Z = (2)%Z); try lia.
      apply H0 in H; try assumption.
      all: try apply ss_Left; try apply ss_Right;
           apply ss_Bop; rewrite <- H1.
      all: apply bs_Add; apply bs_Nat.
  Qed.

  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    inversion H1; subst.
    - inversion H2; subst.
      pose proof (state_deterministic Z s i z z0 VAL VAL0).
      subst. trivial.
    - inversion H2; subst.
      * inversion LEFT.
      * inversion RIGHT.
      * pose proof (eval_deterministic (Bop op (Nat zl) (Nat zr)) s z0 z EVAL0 EVAL).
        subst. trivial.
  Qed.

  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr)
    (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval.
    - apply isv_Intro.
    - assumption.
  Qed.

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof.
    induction C; eauto.
    all: simpl; induction IHC; eauto.
  Qed.

  Lemma ss_subst_binop s e1 e2 e1' e2' op
    (HR1: s |- e1 ~~> e1')
    (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
  Proof.
    eapply ss_reachable_trans.
    * pose proof (H1:=ss_subst s (BopL op Hole e2)). simpl in H1.
      specialize H1 with e1 e1'.
      apply H1.
      assumption.
    * pose proof (H2:=ss_subst s (BopR op e1' Hole)). simpl in H2.
      specialize H2 with e2 e2'.
      apply H2.
      assumption.
  Qed.

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof.
    inversion H; subst.
    all: pose proof (eval_deterministic e1 s za0 za VALA0 VALA);
         pose proof (eval_deterministic e2 s zb0 zb VALB0 VALB);
         subst;
         eapply reach_step.
    all: try apply reach_base.
    all: try apply ss_Bop;
         try simpl in H;
         try auto.
    all: eauto.
  Qed.

  #[export] Hint Resolve ss_bop_reachable : core.

  Lemma ss_eval_binop s e1 e2 za zb z op
        (IHe1 : (s) |- e1 -->> (Nat za))
        (IHe2 : (s) |- e2 -->> (Nat zb))
        (H    : [|Bop op e1 e2|] s => z)
        (VALA : [|e1|] s => (za))
        (VALB : [|e2|] s => (zb)) :
        s |- Bop op e1 e2 -->> (Nat z).
  Proof.
    apply ss_reachable_eval.
    eapply ss_reachable_trans.
    - eapply ss_subst_binop.
      * apply ss_eval_reachable in IHe1. eassumption.
      * apply ss_eval_reachable in IHe2. eassumption.
    - inversion H; subst.
      all: pose proof (eval_deterministic e1 s za0 za VALA0 VALA);
           pose proof (eval_deterministic e2 s zb0 zb VALB0 VALB);
           subst; eauto.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) :
    [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof. admit. Admitted.

End SmallStep.

Module StaticSemantics.

  Import SmallStep.

  Inductive Typ : Set := Int | Bool.

  Reserved Notation "t1 << t2" (at level 0).

  Inductive subtype : Typ -> Typ -> Prop :=
  | subt_refl : forall t,  t << t
  | subt_base : Bool << Int
  where "t1 << t2" := (subtype t1 t2).

  Lemma subtype_trans t1 t2 t3 (H1: t1 << t2) (H2: t2 << t3) : t1 << t3.
  Proof.
    inversion H1; subst.
    inversion H2; subst; assumption.
    * inversion H2; subst. assumption.
  Qed.

  Lemma subtype_antisymm t1 t2 (H1: t1 << t2) (H2: t2 << t1) :
        t1 = t2.
  Proof.
    inversion H1; subst.
    inversion H2; subst.
    * assumption.
    * inversion H2; subst.
  Qed.

  Reserved Notation "e :-: t" (at level 0).

  Inductive typeOf : expr -> Typ -> Prop :=
  | type_X   : forall x, (Var x) :-: Int
  | type_0   : (Nat 0) :-: Bool
  | type_1   : (Nat 1) :-: Bool
  | type_N   : forall z (HNbool : ~zbool z), (Nat z) :-: Int
  | type_Add : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [+]  e2) :-: Int
  | type_Sub : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [-]  e2) :-: Int
  | type_Mul : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [*]  e2) :-: Int
  | type_Div : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [/]  e2) :-: Int
  | type_Mod : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [%]  e2) :-: Int
  | type_Lt  : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [<]  e2) :-: Bool
  | type_Le  : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [<=] e2) :-: Bool
  | type_Gt  : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [>]  e2) :-: Bool
  | type_Ge  : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [>=] e2) :-: Bool
  | type_Eq  : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [==] e2) :-: Bool
  | type_Ne  : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [/=] e2) :-: Bool
  | type_And : forall e1 e2 (H1 : e1 :-: Bool) (H2 : e2 :-: Bool), (e1 [&]  e2) :-: Bool
  | type_Or  : forall e1 e2 (H1 : e1 :-: Bool) (H2 : e2 :-: Bool), (e1 [\/] e2) :-: Bool
  where "e :-: t" := (typeOf e t).

  Lemma type_preservation e t t' (HS: t' << t) (HT: e :-: t) :
    forall st e' (HR: st |- e ~~> e'), e' :-: t'.
  Proof. admit. Admitted.

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof.
    intros.
    inversion HT; subst.
    all: inversion HVal; subst.
    all: try solve [ left ; trivial].
    all: try solve [ right ; trivial].
    * inversion BOOLA; subst.
      all: inversion BOOLB; subst; auto.
    * inversion BOOLA; subst.
      all: inversion BOOLB; subst; auto.
  Qed.

End StaticSemantics.

Module Renaming.

  Definition renaming := { f : id -> id | Bijective f }.

  Fixpoint rename_id (r : renaming) (x : id) : id :=
    match r with
      exist _ f _ => f x
    end.

  Definition renamings_inv (r r' : renaming) :=
    forall (x : id), rename_id r (rename_id r' x) = x.

  Lemma renaming_inv (r : renaming) :
    exists (r' : renaming), renamings_inv r' r.
  Proof.
    destruct r.
    destruct b.
    destruct a.
    pose (f := (ex_intro
                 (fun g =>
                   (forall y : id, g (x0 y) = y) /\
                   (forall y : id, x0 (g y) = y)
                 )
                 x
                 (conj e0 e)
               )
         ).
    exists (exist _ x0 f).
    trivial.
  Qed.

  Lemma renaming_inv2 (r : renaming) :
    exists (r' : renaming), renamings_inv r r'.
  Proof.
    destruct r.
    destruct b.
    destruct a.
    pose (f := (ex_intro
                 (fun g =>
                   (forall y : id, g (x0 y) = y) /\
                   (forall y : id, x0 (g y) = y)
                 )
                 x
                 (conj e0 e)
               )
         ).
    exists (exist _ x0 f).
    trivial.
  Qed.

  Fixpoint rename_expr (r : renaming) (e : expr) : expr :=
    match e with
    | Var x => Var (rename_id r x)
    | Nat n => Nat n
    | Bop op e1 e2 => Bop op (rename_expr r e1) (rename_expr r e2)
    end.

  Lemma re_rename_expr
    (r r' : renaming)
    (Hinv : renamings_inv r r')
    (e    : expr) : rename_expr r (rename_expr r' e) = e.
  Proof.
    induction e; simpl.
    * reflexivity.
    * unfold renamings_inv in Hinv. specialize Hinv with i.
      rewrite Hinv. reflexivity.
    * rewrite IHe1. rewrite IHe2. reflexivity.
  Qed.

  Fixpoint rename_state (r : renaming) (st : state Z) : state Z :=
    match st with
    | [] => []
    | (id, x) :: tl =>
        match r with exist _ f _ => (f id, x) :: rename_state r tl end
    end.

  Lemma re_rename_state
    (r r' : renaming)
    (Hinv : renamings_inv r r')
    (st   : state Z) : rename_state r (rename_state r' st) = st.
  Proof.
    induction st; simpl.
    * reflexivity.
    * destruct a.
      destruct r.
      destruct r'.
      simpl.
      rewrite IHst.
      clear IHst.
      unfold renamings_inv in Hinv. specialize Hinv with i.
      unfold rename_id in Hinv.
      rewrite Hinv.
      reflexivity.
  Qed.

  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
    destruct BH.
    destruct H.
    unfold Injective.
    intros.
    specialize H0 with (f x0).
    rewrite H1 in H0.
    congruence.
  Qed.

  Lemma state_renaming_invariance (i : id) (s : state Z) (z : Z) (r : renaming)
    : s / i => z <-> (rename_state r s) / rename_id r i => z.
  Proof.
    split.
    - intros.
      induction H; destruct r; constructor.
      * intro. apply H. eapply bijective_injective; eauto.
      * assumption.
    - intros.
      dependent induction H.
      * destruct r. simpl in x.
        destruct s; simpl in x; inversion x; subst.
        destruct p; dependent destruction H0.
        apply bijective_injective in b.
        apply b in x.
        subst. constructor.
      * destruct r.
        destruct s; inversion x.
        simpl in *.
        destruct p.
        constructor.
        -- intro. rewrite H1 in H.
           inversion H2; subst. contradiction.
        -- eapply IHst_binds; try reflexivity.
           ** inversion H2; subst. eauto.
           ** reflexivity.
  Qed.


  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof.
    split.
    - intros.
      induction H.
      all:
        econstructor; eauto.
      * apply state_renaming_invariance. assumption.
    - intros.
      dependent induction H.
      all: destruct e; inversion x; eauto.
      * constructor.
        apply <- (state_renaming_invariance i0 st z r).
        subst. assumption.
  Qed.
End Renaming.
