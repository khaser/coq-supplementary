Require Import List.
Import ListNotations.
Require Import Lia.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id.
Require Export State.
Require Export Expr.

Require Export Coq.Program.Equality.

From hahn Require Import HahnBase.

(* AST for statements *)
Inductive stmt : Type :=
| SKIP  : stmt
| Assn  : id -> expr -> stmt
| READ  : id -> stmt
| WRITE : expr -> stmt
| Seq   : stmt -> stmt -> stmt
| If    : expr -> stmt -> stmt -> stmt
| While : expr -> stmt -> stmt.

(* Supplementary notation *)
Notation "x  '::=' e"                         := (Assn  x e    ) (at level 37, no associativity).
Notation "s1 ';;'  s2"                        := (Seq   s1 s2  ) (at level 35, right associativity).
Notation "'COND' e 'THEN' s1 'ELSE' s2 'END'" := (If    e s1 s2) (at level 36, no associativity).
Notation "'WHILE' e 'DO' s 'END'"             := (While e s    ) (at level 36, no associativity).

(* Configuration *)
Definition conf := (state Z * list Z * list Z)%type.

(* Big-step evaluation relation *)
Reserved Notation "c1 '==' s '==>' c2" (at level 0).

Notation "st [ x '<-' y ]" := (update Z st x y) (at level 0).

Inductive bs_int : stmt -> conf -> conf -> Prop :=
| bs_Skip        : forall (c : conf), c == SKIP ==> c
| bs_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z)
                          (VAL : [| e |] s => z),
                          (s, i, o) == x ::= e ==> (s [x <- z], i, o)
| bs_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
                          (s, z::i, o) == READ x ==> (s [x <- z], i, o)
| bs_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z)
                          (VAL : [| e |] s => z),
                          (s, i, o) == WRITE e ==> (s, i, z::o)
| bs_Seq         : forall (c c' c'' : conf) (s1 s2 : stmt)
                          (STEP1 : c == s1 ==> c') (STEP2 : c' == s2 ==> c''),
                          c ==  s1 ;; s2 ==> c''
| bs_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt)
                          (CVAL : [| e |] s => Z.one)
                          (STEP : (s, i, o) == s1 ==> c'),
                          (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt)
                          (CVAL : [| e |] s => Z.zero)
                          (STEP : (s, i, o) == s2 ==> c'),
                          (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_While_True  : forall (st : state Z) (i o : list Z) (c' c'' : conf) (e : expr) (s : stmt)
                          (CVAL  : [| e |] st => Z.one)
                          (STEP  : (st, i, o) == s ==> c')
                          (WSTEP : c' == WHILE e DO s END ==> c''),
                          (st, i, o) == WHILE e DO s END ==> c''
| bs_While_False : forall (st : state Z) (i o : list Z) (e : expr) (s : stmt)
                          (CVAL : [| e |] st => Z.zero),
                          (st, i, o) == WHILE e DO s END ==> (st, i, o)
where "c1 == s ==> c2" := (bs_int s c1 c2).

#[export] Hint Constructors bs_int : core.

(* "Surface" semantics *)
Definition eval (s : stmt) (i o : list Z) : Prop :=
  exists st, ([], i, []) == s ==> (st, [], o).

Notation "<| s |> i => o" := (eval s i o) (at level 0).

(* "Surface" equivalence *)
Definition eval_equivalent (s1 s2 : stmt) : Prop :=
  forall (i o : list Z),  <| s1 |> i => o <-> <| s2 |> i => o.

Notation "s1 ~e~ s2" := (eval_equivalent s1 s2) (at level 0).

(* Contextual equivalence *)
Inductive Context : Type :=
| Hole
| SeqL   : Context -> stmt -> Context
| SeqR   : stmt -> Context -> Context
| IfThen : expr -> Context -> stmt -> Context
| IfElse : expr -> stmt -> Context -> Context
| WhileC : expr -> Context -> Context.

(* Plugging a statement into a context *)
Fixpoint plug (C : Context) (s : stmt) : stmt :=
  match C with
  | Hole => s
  | SeqL     C  s1 => Seq (plug C s) s1
  | SeqR     s1 C  => Seq s1 (plug C s)
  | IfThen e C  s1 => If e (plug C s) s1
  | IfElse e s1 C  => If e s1 (plug C s)
  | WhileC   e  C  => While e (plug C s)
  end.

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Definition contextual_equivalent (s1 s2 : stmt) :=
  forall (C : Context), (C <~ s1) ~e~ (C <~ s2).

Notation "s1 '~c~' s2" := (contextual_equivalent s1 s2) (at level 42, no associativity).

Lemma contextual_equiv_stronger (s1 s2 : stmt) (H: s1 ~c~ s2) : s1 ~e~ s2.
Proof.
  unfold  "~c~" in H.
  specialize H with Hole.
  assumption.
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  pose (s1 := Assn (Id 0) (Nat 0)).
  pose (s2 := Assn (Id 0) (Nat 1)).
  exists s1, s2.
  split.
  - unfold "~e~". intros. split.
    * unfold eval. intros. destruct H. inversion H. subst.
      exists ([(Id 0, 1%Z)]).
      constructor. auto.
    * unfold eval. intros. destruct H. inversion H. subst.
      exists ([(Id 0, 0%Z)]).
      constructor. auto.
  - intro. unfold "~c~" in H.
    pose (Cp := SeqL Hole (WRITE (Var (Id 0)))).
    specialize H with Cp.
    unfold eval_equivalent in H.
    specialize H with ([]) ([0%Z]).
    destruct H. clear H0.
    unfold "<~" in H.
    simpl in H.
    assert (eval (s1;; WRITE (Var (Id 0))) ([]) ([0%Z])).
    * clear H. unfold eval. exists ([(Id 0, 0%Z)]).
      apply bs_Seq with (c' := ([(Id 0, 0%Z)], [], [])).
      -- constructor. auto.
      -- apply bs_Write. constructor. constructor.
    * apply H in H0. clear H.
      inversion_clear H0; subst.
      inversion_clear H; subst.
      inversion STEP1; subst.
      inversion VAL; subst.
      clear VAL STEP1.
      inversion STEP2; subst.
      inversion VAL; subst.
      clear STEP2 VAL.
      unfold update in VAR.
      inversion VAR; subst.
      contradiction.
Qed.

(* Big step equivalence *)
Definition bs_equivalent (s1 s2 : stmt) :=
  forall (c c' : conf), c == s1 ==> c' <-> c == s2 ==> c'.

Notation "s1 '~~~' s2" := (bs_equivalent s1 s2) (at level 0).

Ltac seq_inversion :=
  match goal with
    H: _ == _ ;; _ ==> _ |- _ => inversion_clear H
  end.

Ltac seq_apply :=
  match goal with
  | H: _   == ?s1 ==> ?c' |- _ == (?s1 ;; _) ==> _ =>
    apply bs_Seq with c'; solve [seq_apply | assumption]
  | H: ?c' == ?s2 ==>  _  |- _ == (_ ;; ?s2) ==> _ =>
    apply bs_Seq with c'; solve [seq_apply | assumption]
  end.

Module SmokeTest.

  (* Associativity of sequential composition *)
  Lemma seq_assoc (s1 s2 s3 : stmt) :
    ((s1 ;; s2) ;; s3) ~~~ (s1 ;; (s2 ;; s3)).
  Proof.
    unfold "~~~".
    intros.
    split.
    all: intro;
      seq_inversion;
      seq_inversion;
      seq_apply.
  Qed.

  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~
    (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    unfold "~~~".
    intros.
    split; intro.
    - inversion H; subst;
      [apply bs_If_True | apply bs_If_False]; eauto.
    - inversion H; subst;
      dependent destruction STEP;
      [eapply bs_While_True | eapply bs_While_False]; eauto.
  Qed.

  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    dependent induction EXE; eauto.
  Qed.

  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    unfold "~~~".
    split; intro.
    - exfalso. dependent induction H; eauto.
      inversion CVAL.
    - exfalso. inversion H; subst; inversion CVAL.
  Qed.

  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    unfold "~~~".
    intros.
    split; intros.
    all: dependent induction H; eauto.
    all: econstructor; eauto.
    all: apply EQ; assumption.
  Qed.

  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    unfold "~". intro.
    dependent induction H; eauto.
    inversion CVAL.
  Qed.

End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  unfold "~~~".
  intros.
  split; intros.
  all: seq_inversion.
  all: econstructor; eauto.
  all: apply EQ; assumption.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold "~~~".
  intros.
  split; intros.
  all: seq_inversion.
  all: econstructor; eauto.
  all: apply EQ; eassumption.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  unfold "~~~".
  intros.
  split; intros.
  all: inversion H; subst.
  all: try solve [econstructor; auto].
  all: eapply bs_If_False; eauto;
       apply EQ; assumption.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  unfold "~~~".
  intros.
  split; intros.
  all: inversion H; subst.
  all: try solve [econstructor; auto].
  all: eapply bs_If_True; eauto;
       apply EQ; assumption.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  unfold "~~~".
  intros.
  split; intros.
  all: dependent induction H; auto.
  all: eapply bs_While_True; auto;
       [ eapply EQ; eassumption | eapply IHbs_int2; eauto].
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split. apply eq_congruence_seq_r; assumption.
  split. apply eq_congruence_seq_l; assumption.
  split. apply eq_congruence_cond_else; assumption.
  split. apply eq_congruence_cond_then; assumption.
  apply eq_congruence_while. assumption.
Qed.

(* Big-step semantics is deterministic *)
Ltac by_eval_deterministic :=
  match goal with
    H1: [|?e|]?s => ?z1, H2: [|?e|]?s => ?z2 |- _ =>
     apply (eval_deterministic e s z1 z2) in H1; [subst z2; reflexivity | assumption]
  end.

Ltac eval_zero_not_one :=
  match goal with
    H : [|?e|] ?st => (Z.one), H' : [|?e|] ?st => (Z.zero) |- _ =>
    assert (Z.zero = Z.one) as JJ; [ | inversion JJ];
    eapply eval_deterministic; eauto
  end.

Lemma bs_int_deterministic (c c1 c2 : conf) (s : stmt)
      (EXEC1 : c == s ==> c1) (EXEC2 : c == s ==> c2) :
  c1 = c2.
Proof.
  generalize dependent c1.
  dependent induction EXEC2; intros; inversion EXEC1; subst; eauto.
  all: try eval_zero_not_one.
  all: try by_eval_deterministic.
  - apply IHEXEC2_2.
    pose proof (H := (IHEXEC2_1 c'0 STEP1)).
    rewrite H in STEP2; assumption.
  - apply IHEXEC2_2.
    pose proof (H := (IHEXEC2_1 c'0 STEP)).
    rewrite H in WSTEP; assumption.
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof. admit. Admitted.

(* Contextual equivalence is equivalent to the semantic one *)
(* TODO: no longer needed *)
Ltac by_eq_congruence e s s1 s2 H :=
  remember (eq_congruence e s s1 s2 H) as Congruence;
  match goal with H: Congruence = _ |- _ => clear H end;
  repeat (match goal with H: _ /\ _ |- _ => inversion_clear H end); assumption.

(* Small-step semantics *)
Module SmallStep.

  Reserved Notation "c1 '--' s '-->' c2" (at level 0).

  Inductive ss_int_step : stmt -> conf -> option stmt * conf -> Prop :=
  | ss_Skip        : forall (c : conf), c -- SKIP --> (None, c)
  | ss_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z)
                            (SVAL : [| e |] s => z),
      (s, i, o) -- x ::= e --> (None, (s [x <- z], i, o))
  | ss_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
      (s, z::i, o) -- READ x --> (None, (s [x <- z], i, o))
  | ss_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z)
                            (SVAL : [| e |] s => z),
      (s, i, o) -- WRITE e --> (None, (s, i, z::o))
  | ss_Seq_Compl   : forall (c c' : conf) (s1 s2 : stmt)
                            (SSTEP : c -- s1 --> (None, c')),
      c -- s1 ;; s2 --> (Some s2, c')
  | ss_Seq_InCompl : forall (c c' : conf) (s1 s2 s1' : stmt)
                            (SSTEP : c -- s1 --> (Some s1', c')),
      c -- s1 ;; s2 --> (Some (s1' ;; s2), c')
  | ss_If_True     : forall (s : state Z) (i o : list Z) (s1 s2 : stmt) (e : expr)
                            (SCVAL : [| e |] s => Z.one),
      (s, i, o) -- COND e THEN s1 ELSE s2 END --> (Some s1, (s, i, o))
  | ss_If_False    : forall (s : state Z) (i o : list Z) (s1 s2 : stmt) (e : expr)
                            (SCVAL : [| e |] s => Z.zero),
      (s, i, o) -- COND e THEN s1 ELSE s2 END --> (Some s2, (s, i, o))
  | ss_While       : forall (c : conf) (s : stmt) (e : expr),
      c -- WHILE e DO s END --> (Some (COND e THEN s ;; WHILE e DO s END ELSE SKIP END), c)
  where "c1 -- s --> c2" := (ss_int_step s c1 c2).

  Reserved Notation "c1 '--' s '-->>' c2" (at level 0).

  Inductive ss_int : stmt -> conf -> conf -> Prop :=
    ss_int_Base : forall (s : stmt) (c c' : conf),
                    c -- s --> (None, c') -> c -- s -->> c'
  | ss_int_Step : forall (s s' : stmt) (c c' c'' : conf),
                    c -- s --> (Some s', c') -> c' -- s' -->> c'' -> c -- s -->> c''
  where "c1 -- s -->> c2" := (ss_int s c1 c2).

  Lemma ss_int_step_deterministic (s : stmt)
        (c : conf) (c' c'' : option stmt * conf)
        (EXEC1 : c -- s --> c')
        (EXEC2 : c -- s --> c'') :
    c' = c''.
  Proof.
    dependent induction s.
    all: dependent destruction EXEC1; dependent destruction EXEC2; subst; auto.
    all: try solve [specialize (IHs1 _ _ _ EXEC1 EXEC2); inversion IHs1; subst; reflexivity].
    1-2: by_eval_deterministic.
    1-2: eval_zero_not_one.
  Qed.

  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    dependent induction STEP1.
    - inversion STEP2.
      * dependent destruction H; inversion H0; subst; auto; by_eval_deterministic.
      * dependent destruction H; inversion H0.
    - apply IHSTEP1. clear IHSTEP1 STEP1.
      inversion STEP2.
      * pose proof (Hf := ss_int_step_deterministic _ _ _ _ H H0).
        inversion Hf.
      * pose proof (Hf := ss_int_step_deterministic _ _ _ _ H H0).
        inversion Hf; subst.
        apply H1.
  Qed.

  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
    inversion STEP; auto.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'.
  Proof.
    induction STEP1.
    - eapply ss_int_Step.
      * apply ss_Seq_Compl. eexact H.
      * apply STEP2.
    - pose proof (Hh := IHSTEP1 STEP2); clear STEP2 IHSTEP1.
      eapply ss_int_Step.
      * apply ss_Seq_InCompl. eexact H.
      * eexact Hh.
  Qed.

  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    dependent induction s generalizing c c' c''; inversion STEP; subst.
    - eapply bs_Seq.
      * apply ss_bs_base. exact SSTEP.
      * apply EXEC.
    - inversion EXEC; subst.
      eapply bs_Seq.
      * apply (IHs1 _ _ _ _ SSTEP).
        eexact STEP1.
      * assumption.
    - apply bs_If_True.
      * apply SCVAL.
      * assumption.
    - apply bs_If_False.
      * apply SCVAL.
      * assumption.
    - apply SmokeTest.while_unfolds. apply EXEC.
  Qed.

  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split; intros.
    - dependent induction s.
      1-4: apply ss_int_Base;
        inversion H; subst;
        constructor; auto.
      * inversion H; subst.
        eapply ss_ss_composition.
        -- apply (IHs1 _ _ STEP1).
        -- apply (IHs2 _ _ STEP2).
      * inversion H; subst.
        -- eapply ss_int_Step.
           ** apply ss_If_True. apply CVAL.
           ** apply (IHs1 _ _ STEP).
        -- eapply ss_int_Step.
           ** apply ss_If_False. apply CVAL.
           ** apply (IHs2 _ _ STEP).
      * dependent induction H.
        -- eapply ss_int_Step; try apply ss_While.
           eapply ss_int_Step.
           ** apply ss_If_True. eauto.
           ** eapply ss_ss_composition; eauto.
        -- eapply ss_int_Step; try apply ss_While.
           eapply ss_int_Step.
           ** apply ss_If_False. eauto.
           ** repeat constructor.
    - dependent induction H.
      * apply ss_bs_base. apply H.
      * eapply ss_bs_step.
        -- eexact H.
        -- apply IHss_int.
  Qed.
End SmallStep.

Module Renaming.

  Definition renaming := Renaming.renaming.

  Definition rename_conf (r : renaming) (c : conf) : conf :=
    match c with
    | (st, i, o) => (Renaming.rename_state r st, i, o)
    end.

  Fixpoint rename (r : renaming) (s : stmt) : stmt :=
    match s with
    | SKIP                       => SKIP
    | x ::= e                    => (Renaming.rename_id r x) ::= Renaming.rename_expr r e
    | READ x                     => READ (Renaming.rename_id r x)
    | WRITE e                    => WRITE (Renaming.rename_expr r e)
    | s1 ;; s2                   => (rename r s1) ;; (rename r s2)
    | COND e THEN s1 ELSE s2 END => COND (Renaming.rename_expr r e) THEN (rename r s1) ELSE (rename r s2) END
    | WHILE e DO s END           => WHILE (Renaming.rename_expr r e) DO (rename r s) END
    end.

  Lemma re_rename
    (r r' : Renaming.renaming)
    (Hinv : Renaming.renamings_inv r r')
    (s    : stmt) : rename r (rename r' s) = s.
  Proof.
    dependent induction s.
    * auto.
    * unfold rename.
      unfold Renaming.renamings_inv in Hinv.
      pose proof (Hh := Hinv i).
      rewrite Hh.
      rewrite (Renaming.re_rename_expr _ _ Hinv e).
      reflexivity.
    * unfold rename.
      specialize (Hinv i). rewrite Hinv. reflexivity.
    * unfold rename.
      rewrite (Renaming.re_rename_expr _ _ Hinv e).
      reflexivity.
    * simpl.
      rewrite IHs1; rewrite IHs2.
      reflexivity.
    * simpl.
      rewrite IHs1; rewrite IHs2.
      rewrite (Renaming.re_rename_expr _ _ Hinv e).
      reflexivity.
    * simpl.
      rewrite IHs.
      rewrite (Renaming.re_rename_expr _ _ Hinv e).
      reflexivity.
  Qed.

  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    destruct r. simpl. reflexivity.
  Qed.

  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    dependent induction s;
    try solve [ inversion Hbs; subst;
                dependent destruction r;
                auto; constructor;
                rewrite <- Renaming.eval_renaming_invariance;
                assumption
              ].
    - simpl.
      inversion Hbs; subst.
      eapply bs_Seq.
      * apply IHs1. exact STEP1.
      * apply IHs2. exact STEP2.
    - simpl.
      inversion Hbs; subst.
      * apply bs_If_True.
        -- rewrite <- Renaming.eval_renaming_invariance.
           exact CVAL.
        -- apply (IHs1 r (s, i, o)).
           eexact STEP.
      * apply bs_If_False.
        -- rewrite <- Renaming.eval_renaming_invariance.
           exact CVAL.
        -- apply (IHs2 r (s, i, o)).
           eexact STEP.
    - simpl.
      dependent induction Hbs.
      * eapply bs_While_True.
        -- rewrite <- Renaming.eval_renaming_invariance.
           eexact CVAL.
        -- apply (IHs r (st, i, o)).
           exact Hbs1.
        -- apply IHHbs2; [exact IHs | reflexivity].
      * apply bs_While_False.
        rewrite <- Renaming.eval_renaming_invariance.
        eexact CVAL.
  Qed.

  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    destruct (Renaming.renaming_inv r).
    rewrite <- (re_rename _ _ H _).
    destruct c as [[st i] o].
    destruct c' as [[st' i'] o'].
    pose proof (Hh := Renaming.re_rename_state x r H).
    rewrite <- (Hh (st)).
    rewrite <- (Hh (st')).
    clear Hh.
    apply (renaming_invariant_bs _ x _ _ Hbs).
  Qed.

  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    split; intros; unfold eval in *; destruct H.
    - exists (Renaming.rename_state r x).
      assert (([], i, []) = rename_conf r ([], i, [])).
      * eauto.
      * rewrite  H0.
        pose proof (renaming_invariant_bs s r _ _ H).
        unfold rename_conf in *.
        apply H1.
    - destruct (Renaming.renaming_inv2 r).
      pose proof (Renaming.re_rename_state r x0 H0).
      exists (Renaming.rename_state x0 x).
      apply (renaming_invariant_bs_inv _ r).
      unfold rename_conf.
      rewrite (H1 (x)).
      assumption.
  Qed.

End Renaming.

(* CPS semantics *)
Inductive cont : Type :=
| KEmpty : cont
| KStmt  : stmt -> cont.

Definition Kapp (l r : cont) : cont :=
  match (l, r) with
  | (KStmt ls, KStmt rs) => KStmt (ls ;; rs)
  | (KEmpty  , _       ) => r
  | (_       , _       ) => l
  end.

Notation "'!' s" := (KStmt s) (at level 0).
Notation "s1 @ s2" := (Kapp s1 s2) (at level 0).

Reserved Notation "k '|-' c1 '--' s '-->' c2" (at level 0).

Inductive cps_int : cont -> cont -> conf -> conf -> Prop :=
| cps_Empty       : forall (c : conf), KEmpty |- c -- KEmpty --> c
| cps_Skip        : forall (c c' : conf) (k : cont)
                           (CSTEP : KEmpty |- c -- k --> c'),
    k |- c -- !SKIP --> c'
| cps_Assign      : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (x : id) (e : expr) (n : Z)
                           (CVAL : [| e |] s => n)
                           (CSTEP : KEmpty |- (s [x <- n], i, o) -- k --> c'),
    k |- (s, i, o) -- !(x ::= e) --> c'
| cps_Read        : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (x : id) (z : Z)
                           (CSTEP : KEmpty |- (s [x <- z], i, o) -- k --> c'),
    k |- (s, z::i, o) -- !(READ x) --> c'
| cps_Write       : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (z : Z)
                           (CVAL : [| e |] s => z)
                           (CSTEP : KEmpty |- (s, i, z::o) -- k --> c'),
    k |- (s, i, o) -- !(WRITE e) --> c'
| cps_Seq         : forall (c c' : conf) (k : cont) (s1 s2 : stmt)
                           (CSTEP : !s2 @ k |- c -- !s1 --> c'),
    k |- c -- !(s1 ;; s2) --> c'
| cps_If_True     : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s1 s2 : stmt)
                           (CVAL : [| e |] s => Z.one)
                           (CSTEP : k |- (s, i, o) -- !s1 --> c'),
    k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_If_False    : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s1 s2 : stmt)
                           (CVAL : [| e |] s => Z.zero)
                           (CSTEP : k |- (s, i, o) -- !s2 --> c'),
    k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_While_True  : forall (st : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s : stmt)
                           (CVAL : [| e |] st => Z.one)
                           (CSTEP : !(WHILE e DO s END) @ k |- (st, i, o) -- !s --> c'),
    k |- (st, i, o) -- !(WHILE e DO s END) --> c'
| cps_While_False : forall (st : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s : stmt)
                           (CVAL : [| e |] st => Z.zero)
                           (CSTEP : KEmpty |- (st, i, o) -- k --> c'),
    k |- (st, i, o) -- !(WHILE e DO s END) --> c'
where "k |- c1 -- s --> c2" := (cps_int k s c1 c2).

Ltac cps_bs_gen_helper k H :=
  destruct k eqn:K; subst; inversion H; subst;
  [inversion EXEC; subst | eapply bs_Seq; eauto];
  eauto.

Lemma cps_bs_gen (S : stmt) (c c' : conf) (S1 k : cont)
      (EXEC : k |- c -- S1 --> c') (DEF : !S = S1 @ k):
  c == S ==> c'.
Proof.
  dependent induction EXEC generalizing S.
  2-5: cps_bs_gen_helper k DEF.
  - inversion DEF.
  - destruct k eqn:K; subst; inversion DEF; subst.
    * eauto.
    * unfold Kapp in *.
      apply (SmokeTest.seq_assoc s1 s2 s).
      eauto.
  - dependent destruction k; dependent destruction DEF.
    * eauto.
    * unfold Kapp in *.
      specialize (IHEXEC (s1;; s0)).
      assert (KStmt (s1;; s0) = KStmt (s1;; s0)); auto.
      apply IHEXEC in H.
      dependent destruction H.
      eapply bs_Seq; eauto.
  - dependent destruction k; dependent destruction DEF.
    * eauto.
    * unfold Kapp in *.
      specialize (IHEXEC (s2;; s0)).
      assert (KStmt (s2;; s0) = KStmt (s2;; s0)); auto.
      apply IHEXEC in H.
      dependent destruction H.
      eapply bs_Seq; eauto.
  - dependent destruction k; dependent destruction DEF.
    * unfold Kapp in *.
      specialize (IHEXEC (s;; (WHILE e DO s END))).
      assert (KStmt (s;; (WHILE e DO s END)) = KStmt (s;; (WHILE e DO s END))); auto.
      apply IHEXEC in H.
      dependent destruction H.
      eauto.
    * unfold Kapp in *.
      pose (Sm := (s0;; (WHILE e DO s0 END);; s)).
      specialize (IHEXEC Sm).
      assert (KStmt Sm = KStmt Sm); auto.
      apply IHEXEC in H.
      dependent destruction H.
      inversion H0; subst.
      eapply bs_Seq; eauto.
  - dependent destruction k; dependent destruction DEF.
    * unfold Kapp in *.
      dependent destruction EXEC.
      eapply (bs_While_False _ _ _ _ _ CVAL).
    * unfold Kapp in *.
      pose (Sm := (s)).
      specialize (IHEXEC Sm).
      assert (KStmt Sm = KStmt Sm); auto.
      apply IHEXEC in H.
      eapply bs_Seq; eauto.
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf)
  (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof.
  eapply cps_bs_gen; eauto.
Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') :
  c == s ==> c'.
Proof.
  eapply cps_bs_gen; eauto.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof.
  dependent destruction k2;
  dependent destruction k1;
  unfold Kapp in *.
  - eauto.
  - eauto.
  - dependent destruction k3; inversion STEP.
  - apply cps_Seq.
    dependent destruction k3; eauto.
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
  dependent induction EXEC generalizing k.
  all: try solve [econstructor; eauto; dependent destruction STEP; eauto].
  - apply (cps_cont_to_seq c c3 (KStmt s1) (KStmt s2) k).
    apply IHEXEC1.
    apply IHEXEC2 in STEP.
    constructor.
    dependent destruction k; unfold Kapp.
    * auto.
    * apply (cps_cont_to_seq c' c3 (KStmt s2) (KStmt s) KEmpty).
      auto.
  - econstructor; auto.
    apply IHEXEC1.
    constructor.
    apply (cps_cont_to_seq).
    apply IHEXEC2.
    dependent destruction k; unfold "@"; auto.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  eapply bs_int_to_cps_int_cont.
  - eexact EXEC.
  - constructor. constructor.
Qed.
