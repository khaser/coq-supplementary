Require Import BinInt ZArith_dec.
Require Import List.
Import ListNotations.
Require Import Lia.

Require Export Id.
Require Export State.
Require Export Expr.
Require Export Stmt.
Require Import Coq.Program.Equality.

(* Configuration *)
Definition conf := (list Z * state Z * list Z * list Z)%type.

(* Straight-line code (no if-while) *)
Module StraightLine.

  (* Straigh-line statements *)
  Inductive StraightLine : stmt -> Set :=
  | sl_Assn  : forall x e, StraightLine (x ::= e)
  | sl_Read  : forall x  , StraightLine (READ x)
  | sl_Write : forall e  , StraightLine (WRITE e)
  | sl_Skip  : StraightLine SKIP
  | sl_Seq   : forall s1 s2 (SL1 : StraightLine s1) (SL2 : StraightLine s2),
      StraightLine (s1 ;; s2).

  (* Instructions *)
  Inductive insn : Set :=
  | R  : insn
  | W  : insn
  | C  : Z -> insn
  | L  : id -> insn
  | S  : id -> insn
  | B  : bop -> insn.

  (* Program *)
  Definition prog := list insn.

  (* Big-step evaluation relation*)
  Reserved Notation "c1 '--' q '-->' c2" (at level 0).
  Notation "st [ x '<-' y ]" := (update Z st x y) (at level 0).

  Inductive sm_int : conf -> prog -> conf -> Prop :=
  | sm_End   : forall (p : prog) (c : conf),
      c -- [] --> c

  | sm_Read  : forall (q : prog) (z : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : (z::s, m, i, o) -- q --> c'),
      (s, m, z::i, o) -- R::q --> c'

  | sm_Write : forall (q : prog) (z : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : (s, m, i, z::o) -- q --> c'),
      (z::s, m, i, o) -- W::q --> c'

  | sm_Load  : forall (q : prog) (x : id) (z : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (VAR : m / x => z)
                      (EXEC : (z::s, m, i, o) -- q --> c'),
      (s, m, i, o) -- (L x)::q --> c'

  | sm_Store : forall (q : prog) (x : id) (z : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : (s, m [x <- z], i, o) -- q --> c'),
      (z::s, m, i, o) -- (S x)::q --> c'

  | sm_Add   : forall (p q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : ((x + y)%Z::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Add)::q --> c'

  | sm_Sub   : forall (p q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : ((x - y)%Z::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Sub)::q --> c'

  | sm_Mul   : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : ((x * y)%Z::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Mul)::q --> c'

  | sm_Div   : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (NZERO : ~ y = Z.zero)
                      (EXEC : ((Z.div x y)::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Div)::q --> c'

  | sm_Mod   : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (NZERO : ~ y = Z.zero)
                      (EXEC : ((Z.modulo x y)::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Mod)::q --> c'

  | sm_Le_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.le x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Le)::q --> c'

  | sm_Le_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.gt x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Le)::q --> c'

  | sm_Ge_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.ge x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Ge)::q --> c'

  | sm_Ge_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.lt x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Ge)::q --> c'

  | sm_Lt_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.lt x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Lt)::q --> c'

  | sm_Lt_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.ge x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Lt)::q --> c'

  | sm_Gt_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.gt x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Gt)::q --> c'

  | sm_Gt_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.le x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Gt)::q --> c'

  | sm_Eq_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.eq x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Eq)::q --> c'

  | sm_Eq_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : ~ Z.eq x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Eq)::q --> c'

  | sm_Ne_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : ~ Z.eq x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Ne)::q --> c'

  | sm_Ne_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.eq x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Ne)::q --> c'

  | sm_And   : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (BOOLX : zbool x)
                      (BOOLY : zbool y)
                      (EXEC : ((x * y)%Z::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B And)::q --> c'

  | sm_Or    : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (BOOLX : zbool x)
                      (BOOLY : zbool y)
                      (EXEC : ((zor x y)::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Or)::q --> c'

  | sm_Const : forall (q : prog) (n : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : (n::s, m, i, o) -- q --> c'),
      (s, m, i, o) -- (C n)::q --> c'
  where "c1 '--' q '-->' c2" := (sm_int c1 q c2).

  (* Expression compiler *)
  Fixpoint compile_expr (e : expr) :=
  match e with
  | Var  x       => [L x]
  | Nat  n       => [C n]
  | Bop op e1 e2 => compile_expr e1 ++ compile_expr e2 ++ [B op]
  end.

  (* Partial correctness of expression compiler *)
  Lemma compiled_expr_correct_cont
        (e : expr) (st : state Z) (s i o : list Z) (n : Z)
        (p : prog) (c : conf)
        (VAL : [| e |] st => n)
        (EXEC: (n::s, st, i, o) -- p --> c) :
    (s, st, i, o) -- (compile_expr e) ++ p --> c.
  Proof.
    dependent induction e.
    - simpl.
      constructor.
      dependent destruction VAL.
      exact EXEC.
    - simpl.
      dependent destruction VAL.
      econstructor; eauto.
    - simpl.
      rewrite <- (Coq.Lists.List.app_assoc (compile_expr e1) (compile_expr e2 ++ [B b]) p).
      dependent destruction b.
      all: dependent destruction VAL; eapply IHe1.
      all: eauto.
      all: rewrite <- (Coq.Lists.List.app_assoc (compile_expr e2) _ p);
           eapply IHe2.
      all: eauto.
      all: try solve [constructor; auto].
  Qed.

  #[export] Hint Resolve compiled_expr_correct_cont.

  Lemma compiled_expr_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z)
        (VAL : [| e |] st => n) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o).
  Proof.
    rewrite <- (Coq.Lists.List.app_nil_r (compile_expr e)).
    eapply compiled_expr_correct_cont; eauto.
    repeat constructor.
  Qed.

  Lemma compiled_expr_not_incorrect_cont
        (e : expr) (st : state Z) (s i o : list Z) (p : prog) (c : conf)
        (EXEC : (s, st, i, o) -- compile_expr e ++ p --> c) :
    exists (n : Z), [| e |] st => n /\ (n :: s, st, i, o) -- p --> c.
  Proof.
    dependent induction e.
    - dependent destruction EXEC.
      repeat esplit; eauto.
    - dependent destruction EXEC.
      repeat esplit; eauto.
    - simpl in *.
      rewrite <- (Coq.Lists.List.app_assoc (compile_expr e1) (compile_expr e2 ++ [B b]) p) in EXEC.
      specialize (IHe1 _ _ _ _ _ _ EXEC).
      destruct IHe1 as [n1 [H1 Hc1]].
      rewrite <- (Coq.Lists.List.app_assoc (compile_expr e2) ([B b]) p) in Hc1.
      specialize (IHe2 _ _ _ _ _ _ Hc1).
      destruct IHe2 as [n2 [H2 Hc2]].
      dependent destruction Hc2; repeat esplit; eauto.
  Qed.

  Lemma compiled_expr_not_incorrect
        (e : expr) (st : state Z)
        (s i o : list Z) (n : Z)
        (EXEC : (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o)) :
    [| e |] st => n.
  Proof.
    rewrite <- (Coq.Lists.List.app_nil_r (compile_expr e)) in EXEC.
    pose proof (compiled_expr_not_incorrect_cont _ _ _ _ _ _ _ EXEC).
    destruct H as [nn [Ha Hb]].
    dependent destruction Hb.
    exact Ha.
  Qed.

  Lemma expr_compiler_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o)
    <->
    [| e |] st => n.
  Proof.
    split; intros.
    - eapply compiled_expr_not_incorrect; eauto.
    - eapply compiled_expr_correct; eauto.
  Qed.

  Fixpoint compile (s : stmt) (H : StraightLine s) : prog :=
    match H with
    | sl_Assn x e          => compile_expr e ++ [S x]
    | sl_Skip              => []
    | sl_Read x            => [R; S x]
    | sl_Write e           => compile_expr e ++ [W]
    | sl_Seq s1 s2 sl1 sl2 => compile s1 sl1 ++ compile s2 sl2
    end.

  Lemma compiled_straightline_correct_cont
        (p : stmt) (Sp : StraightLine p) (st st' : state Z)
        (s i o s' i' o' : list Z)
        (H : (st, i, o) == p ==> (st', i', o')) (q : prog) (c : conf)
        (EXEC : ([], st', i', o') -- q --> c) :
    ([], st, i, o) -- (compile p Sp) ++ q --> c.
  Proof.
    dependent induction Sp; simpl.
    - dependent destruction H.
      rewrite <- (Coq.Lists.List.app_assoc (compile_expr e)).
      eapply compiled_expr_correct_cont; eauto.
      constructor. exact EXEC.
    - dependent destruction H.
      repeat constructor.
      exact EXEC.
    - dependent destruction H.
      rewrite <- (Coq.Lists.List.app_assoc (compile_expr e)).
      eapply compiled_expr_correct_cont; eauto.
      constructor. exact EXEC.
    - dependent destruction H.
      eauto.
    - rewrite <- (Coq.Lists.List.app_assoc (compile s1 Sp1)).
      dependent destruction H.
      destruct c'.
      destruct p.
      eapply IHSp1; eauto.
  Qed.

  Lemma compiled_straightline_correct
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : (st, i, o) == p ==> (st', i', o')) :
    ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof.
    rewrite <- (Coq.Lists.List.app_nil_r (compile p Sp)).
    eapply compiled_straightline_correct_cont; eauto.
    repeat constructor.
  Qed.

  Lemma compiled_straightline_not_incorrect_cont
        (p : stmt) (Sp : StraightLine p) (st : state Z) (i o : list Z) (q : prog) (c : conf)
        (EXEC: ([], st, i, o) -- (compile p Sp) ++ q --> c) :
    exists (st' : state Z) (i' o' : list Z), (st, i, o) == p ==> (st', i', o') /\ ([], st', i', o') -- q --> c.
  Proof.
    dependent induction Sp; simpl.
    - simpl in EXEC.
      rewrite <- (Coq.Lists.List.app_assoc (compile_expr e)) in EXEC.
      destruct (compiled_expr_not_incorrect_cont _ _ _ _ _ _ _ EXEC) as [n [He Hc]].
      dependent destruction Hc.
      repeat esplit; eauto.
    - simpl in EXEC.
      dependent destruction EXEC.
      dependent destruction EXEC.
      eauto.
    - simpl in EXEC.
      rewrite <- (Coq.Lists.List.app_assoc (compile_expr e)) in EXEC.
      destruct (compiled_expr_not_incorrect_cont _ _ _ _ _ _ _ EXEC) as [n [He Hc]].
      dependent destruction Hc.
      repeat esplit; eauto.
    - simpl in EXEC.
      eauto.
    - simpl in *.
      rewrite <- (Coq.Lists.List.app_assoc (compile s1 Sp1)) in EXEC.
      destruct (IHSp1 _ _ _ _ _ EXEC) as [st' [i' [o' [H1 H2]]]].
      clear EXEC IHSp1.
      destruct (IHSp2 _ _ _ _ _ H2) as [st'' [i'' [o'' [H1' H2']]]].
      repeat esplit; eauto.
  Qed.

  Lemma compiled_straightline_not_incorrect
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : ([], st, i, o) -- compile p Sp --> ([], st', i', o')) :
    (st, i, o) == p ==> (st', i', o').
  Proof.
    rewrite <- (Coq.Lists.List.app_nil_r (compile p Sp)) in EXEC.
    pose proof (compiled_straightline_not_incorrect_cont _ _ _ _ _ _ _ EXEC).
    destruct H as [nn [i'' [o'' [Ha Hb]]]].
    dependent destruction Hb.
    exact Ha.
  Qed.


  Theorem straightline_compiler_correct
          (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z) :
    (st, i, o) == p ==> (st', i', o') <-> ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof.
    split; intros.
    - eapply compiled_straightline_correct. eauto.
    - eapply compiled_straightline_not_incorrect. eauto.
  Qed.

End StraightLine.

Inductive insn : Set :=
  JMP : nat -> insn
| JZ  : nat -> insn
| JNZ : nat -> insn
| LAB : nat -> insn
| B   : StraightLine.insn -> insn.

Definition prog := list insn.

Fixpoint at_label (l : nat) (p : prog) : prog :=
  match p with
    []          => []
  | LAB m :: p' => if eq_nat_dec l m then p' else at_label l p'
  | _     :: p' => at_label l p'
  end.

Notation "c1 '==' q '==>' c2" := (StraightLine.sm_int c1 q c2) (at level 0).
Reserved Notation "P '|-' c1 '--' q '-->' c2" (at level 0).

Inductive sm_int : prog -> conf -> prog -> conf -> Prop :=
| sm_Base      : forall (c c' c'' : conf)
                        (P p      : prog)
                        (i        : StraightLine.insn)
                        (H        : c == [i] ==> c')
                        (HP       : P |- c' -- p --> c''),
                 P |- c -- B i :: p --> c''

| sm_Label     : forall (c c' : conf)
                        (P p  : prog)
                        (l    : nat)
                        (H    : P |- c -- p --> c'),
                 P |- c -- LAB l :: p --> c'

| sm_JMP       : forall (c c' : conf)
                        (P p  : prog)
                        (l    : nat)
                        (H    : P |- c -- at_label l P --> c'),
                 P |- c -- JMP l :: p --> c'

| sm_JZ_False  : forall (s i o : list Z)
                        (m     : state Z)
                        (c'    : conf)
                        (P p   : prog)
                        (l     : nat)
                        (z     : Z)
                        (HZ    : z <> 0%Z)
                        (H     : P |- (s, m, i, o) -- p --> c'),
                 P |- (z :: s, m, i, o) -- JZ l :: p --> c'

| sm_JZ_True   : forall (s i o : list Z)
                        (m     : state Z)
                        (c'    : conf)
                        (P p   : prog)
                        (l     : nat)
                        (H     : P |- (s, m, i, o) -- at_label l P --> c'),
                 P |- (0%Z :: s, m, i, o) -- JZ l :: p --> c'

| sm_JNZ_False : forall (s i o : list Z)
                        (m     : state Z)
                        (c'    : conf)
                        (P p   : prog)
                        (l     : nat)
                        (H : P |- (s, m, i, o) -- p --> c'),
                 P |- (0%Z :: s, m, i, o) -- JNZ l :: p --> c'

| sm_JNZ_True  : forall (s i o : list Z)
                        (m     : state Z)
                        (c'    : conf)
                        (P p   : prog)
                        (l     : nat)
                        (z     : Z)
                        (HZ    : z <> 0%Z)
                        (H : P |- (s, m, i, o) -- at_label l P --> c'),
                 P |- (z :: s, m, i, o) -- JNZ l :: p --> c'
| sm_Empty : forall (c : conf) (P : prog), P |- c -- [] --> c
where "P '|-' c1 '--' q '-->' c2" := (sm_int P c1 q c2).

Fixpoint label_occurs_once_rec (occured : bool) (n: nat) (p : prog) : bool :=
  match p with
    LAB m :: p' => if eq_nat_dec n m
                   then if occured
                        then false
                        else label_occurs_once_rec true n p'
                   else label_occurs_once_rec occured n p'
  | _     :: p' => label_occurs_once_rec occured n p'
  | []          => occured
  end.

Definition label_occurs_once (n : nat) (p : prog) : bool :=
  label_occurs_once_rec false n p.

Fixpoint prog_wf_rec (prog p : prog) : bool :=
  match p with
    []      => true
  | i :: p' => match i with
                 JMP l => label_occurs_once l prog
               | JZ  l => label_occurs_once l prog
               | JNZ l => label_occurs_once l prog
               | _     => true
               end && prog_wf_rec prog p'
  end.

Definition prog_wf (p : prog) : bool := prog_wf_rec p p.

Lemma wf_app (p q  : prog)
             (l    : nat)
             (Hwf  : prog_wf_rec q p = true)
             (Hocc : label_occurs_once l q = true) :
      prog_wf_rec q (p ++ [JMP l]) = true.
Proof.
  dependent induction p.
  - simpl. rewrite Hocc. auto.
  - dependent destruction a.
    all: simpl in *; eauto;
         rewrite Bool.andb_true_iff in Hwf;
         destruct Hwf;
         eauto;
         lapply (IHp q l); eauto;
         clear IHp; intros;
         apply H1 in Hocc;
         rewrite Hocc;
         rewrite H;
         auto.
Qed.

Lemma wf_merge (p q w : prog)
             (H1: prog_wf_rec q p = true)
             (H2: prog_wf_rec q w = true):
             prog_wf_rec q (p ++ w) = true.
Proof.
  dependent induction p; auto.
  dependent destruction a; simpl in *.
  all: try solve [
       rewrite Bool.andb_true_iff in H1;
       destruct H1;
       rewrite H;
       rewrite (IHp q w H0 H2);
       auto
  ].
  all: apply (IHp q w H1 H2).
Qed.

Lemma wf_rev (p q : prog) (Hwf : prog_wf_rec q p = true) :
  prog_wf_rec q (rev p) = true.
Proof.
  dependent induction p; eauto.
  dependent destruction a; simpl in *.
  1-3: rewrite Bool.andb_true_iff in Hwf;
       destruct Hwf;
       specialize (IHp q H0);
       eapply wf_merge; auto;
       simpl; rewrite H; auto.
  all: eapply wf_merge; auto.
Qed.

Fixpoint convert_straightline (p : StraightLine.prog) : prog :=
  match p with
    []      => []
  | i :: p' => B i :: convert_straightline p'
  end.

Lemma cons_comm_app (A : Type) (a : A) (l1 l2 : list A) :
  l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof.
  dependent induction l1; eauto.
  simpl.
  specialize (IHl1 l2).
  rewrite IHl1.
  reflexivity.
Qed.

Definition compile_expr (e : expr) : prog :=
  convert_straightline (StraightLine.compile_expr e).
