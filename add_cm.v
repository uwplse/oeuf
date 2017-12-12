Require Import compcert.backend.Cminor.
Require Import compcert.common.AST.
Require Import BinNums.
Require Import compcert.lib.Integers.
Require Import List.
Import ListNotations.

Local Open Scope Z_scope.

Definition __x16 : ident := 65%positive.
Definition ___builtin_fmsub : ident := 40%positive.
Definition ___i64_stod : ident := 16%positive.
Definition ___builtin_fmin : ident := 38%positive.
Definition ___builtin_write32_reversed : ident := 46%positive.
Definition __x12 : ident := 69%positive.
Definition __x19 : ident := 62%positive.
Definition _add_lambda0_lambda1_lambda3 : ident := 54%positive.
Definition ___i64_smod : ident := 22%positive.
Definition ___compcert_va_float64 : ident := 12%positive.
Definition __x18 : ident := 63%positive.
Definition ___compcert_va_int32 : ident := 10%positive.
Definition ___builtin_read32_reversed : ident := 44%positive.
Definition ___builtin_annot : ident := 3%positive.
Definition ___builtin_memcpy_aligned : ident := 2%positive.
Definition ___builtin_fabs : ident := 1%positive.
Definition ___builtin_clzl : ident := 31%positive.
Definition __x2 : ident := 79%positive.
Definition __x9 : ident := 72%positive.
Definition _main : ident := 49%positive.
Definition __x15 : ident := 66%positive.
Definition __x22 : ident := 59%positive.
Definition ___builtin_annot_intval : ident := 4%positive.
Definition __x3 : ident := 78%positive.
Definition __x13 : ident := 68%positive.
Definition _add : ident := 58%positive.
Definition ___builtin_bswap32 : ident := 28%positive.
Definition ___builtin_va_arg : ident := 7%positive.
Definition ___i64_udiv : ident := 21%positive.
Definition ___i64_stof : ident := 18%positive.
Definition ___builtin_write16_reversed : ident := 45%positive.
Definition __x1 : ident := 80%positive.
Definition ___compcert_va_composite : ident := 13%positive.
Definition ___builtin_bswap : ident := 27%positive.
Definition __arg : ident := 84%positive.
Definition __switch_target : ident := 82%positive.
Definition ___builtin_ctz : ident := 33%positive.
Definition _add_lambda0_lambda1_lambda3_lambda4_lambda5 : ident := 56%positive.
Definition ___i64_shr : ident := 25%positive.
Definition ___i64_dtou : ident := 15%positive.
Definition __x21 : ident := 60%positive.
Definition ___i64_sdiv : ident := 20%positive.
Definition ___builtin_clzll : ident := 32%positive.
Definition __x11 : ident := 70%positive.
Definition ___i64_shl : ident := 24%positive.
Definition __x14 : ident := 67%positive.
Definition ___i64_utod : ident := 17%positive.
Definition ___builtin_va_copy : ident := 8%positive.
Definition ___builtin_membar : ident := 5%positive.
Definition __x8 : ident := 73%positive.
Definition _malloc : ident := 50%positive.
Definition ___builtin_read16_reversed : ident := 43%positive.
Definition __x7 : ident := 74%positive.
Definition _add_lambda0_lambda1 : ident := 53%positive.
Definition ___builtin_nop : ident := 47%positive.
Definition _add_lambda0_lambda1_lambda2 : ident := 57%positive.
Definition ___builtin_fsqrt : ident := 36%positive.
Definition ___i64_dtos : ident := 14%positive.
Definition ___builtin_va_start : ident := 6%positive.
Definition ___i64_sar : ident := 26%positive.
Definition ___i64_utof : ident := 19%positive.
Definition ___builtin_fmadd : ident := 39%positive.
Definition __self : ident := 83%positive.
Definition __x20 : ident := 61%positive.
Definition ___compcert_va_int64 : ident := 11%positive.
Definition ___builtin_fmax : ident := 37%positive.
Definition __x0 : ident := 81%positive.
Definition __x5 : ident := 76%positive.
Definition ___builtin_fnmsub : ident := 42%positive.
Definition ___builtin_va_end : ident := 9%positive.
Definition __x17 : ident := 64%positive.
Definition _add_lambda0 : ident := 52%positive.
Definition ___builtin_fnmadd : ident := 41%positive.
Definition __x4 : ident := 77%positive.
Definition __x10 : ident := 71%positive.
Definition __x6 : ident := 75%positive.
Definition ___builtin_ctzl : ident := 34%positive.
Definition ___builtin_bswap16 : ident := 29%positive.
Definition _add_lambda0_lambda1_lambda3_lambda4 : ident := 55%positive.
Definition ___builtin_ctzll : ident := 35%positive.
Definition ___builtin_clz : ident := 30%positive.
Definition ___i64_umod : ident := 23%positive.
Definition _add_lambda0_lambda1_elim0 : ident := 51%positive.
Definition ___builtin_debug : ident := 48%positive.

Definition f_add := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x0 :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some __x0)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 4))) :: nil))
    (Sstore Mint32 (Evar __x0)
      (Econst (Oaddrsymbol _add_lambda0 (Int.repr 0)))))
  (Sreturn (Some (Evar __x0))))
|}.

Definition f_add_lambda0_lambda1_lambda2 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x0 :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq (Sassign __x0 (Evar __arg)) (Sreturn (Some (Evar __x0))))
|}.

Definition f_add_lambda0_lambda1_lambda3_lambda4_lambda5 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x4 :: __x3 :: __x2 :: __x1 :: __x0 :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Sassign __x0 (Evar __self))
    (Sseq
      (Sassign __x1
        (Eload Mint32
          (Ebinop Oadd (Evar __x0) (Econst (Ointconst (Int.repr 4))))))
      (Sseq
        (Sassign __x2 (Evar __arg))
        (Sseq
          (Sseq
            (Sseq
              (Scall (Some __x3)
                (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
                (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                ((Econst (Ointconst (Int.repr 8))) :: nil))
              (Sstore Mint32 (Evar __x3) (Econst (Ointconst (Int.repr 1)))))
            (Sstore Mint32
              (Ebinop Oadd (Evar __x3) (Econst (Ointconst (Int.repr 4))))
              (Evar __x2)))
          (Scall (Some __x4)
            (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default) (Eload Mint32 (Evar __x1))
            ((Evar __x1) :: (Evar __x3) :: nil))))))
  (Sreturn (Some (Evar __x4))))
|}.

Definition f_add_lambda0_lambda1_lambda3_lambda4 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x7 :: __x6 :: __x5 :: __x4 :: __x3 :: __x2 :: __x1 :: __x0 ::
              nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Sassign __x0 (Evar __arg))
    (Sseq
      (Sassign __x1 (Evar __self))
      (Sseq
        (Sassign __x2
          (Eload Mint32
            (Ebinop Oadd (Evar __x1) (Econst (Ointconst (Int.repr 4))))))
        (Sseq
          (Sassign __x3 (Evar __self))
          (Sseq
            (Sassign __x4
              (Eload Mint32
                (Ebinop Oadd (Evar __x3) (Econst (Ointconst (Int.repr 8))))))
            (Sseq
              (Sassign __x5 (Evar __self))
              (Sseq
                (Sassign __x6
                  (Eload Mint32
                    (Ebinop Oadd (Evar __x5)
                      (Econst (Ointconst (Int.repr 12))))))
                (Sseq
                  (Sseq
                    (Scall (Some __x7)
                      (mksignature (AST.Tint :: nil) (Some AST.Tint)
                        cc_default)
                      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                      ((Econst (Ointconst (Int.repr 20))) :: nil))
                    (Sstore Mint32 (Evar __x7)
                      (Econst (Oaddrsymbol _add_lambda0_lambda1_lambda3_lambda4_lambda5 (Int.repr 0)))))
                  (Sseq
                    (Sstore Mint32
                      (Ebinop Oadd (Evar __x7)
                        (Econst (Ointconst (Int.repr 4)))) (Evar __x0))
                    (Sseq
                      (Sstore Mint32
                        (Ebinop Oadd (Evar __x7)
                          (Econst (Ointconst (Int.repr 8)))) (Evar __x2))
                      (Sseq
                        (Sstore Mint32
                          (Ebinop Oadd (Evar __x7)
                            (Econst (Ointconst (Int.repr 12)))) (Evar __x4))
                        (Sstore Mint32
                          (Ebinop Oadd (Evar __x7)
                            (Econst (Ointconst (Int.repr 16)))) (Evar __x6)))))))))))))
  (Sreturn (Some (Evar __x7))))
|}.

Definition f_add_lambda0_lambda1_lambda3 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x5 :: __x4 :: __x3 :: __x2 :: __x1 :: __x0 :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Sassign __x0 (Evar __arg))
    (Sseq
      (Sassign __x1 (Evar __self))
      (Sseq
        (Sassign __x2
          (Eload Mint32
            (Ebinop Oadd (Evar __x1) (Econst (Ointconst (Int.repr 4))))))
        (Sseq
          (Sassign __x3 (Evar __self))
          (Sseq
            (Sassign __x4
              (Eload Mint32
                (Ebinop Oadd (Evar __x3) (Econst (Ointconst (Int.repr 8))))))
            (Sseq
              (Sseq
                (Scall (Some __x5)
                  (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
                  (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                  ((Econst (Ointconst (Int.repr 16))) :: nil))
                (Sstore Mint32 (Evar __x5)
                  (Econst (Oaddrsymbol _add_lambda0_lambda1_lambda3_lambda4 (Int.repr 0)))))
              (Sseq
                (Sstore Mint32
                  (Ebinop Oadd (Evar __x5) (Econst (Ointconst (Int.repr 4))))
                  (Evar __x0))
                (Sseq
                  (Sstore Mint32
                    (Ebinop Oadd (Evar __x5)
                      (Econst (Ointconst (Int.repr 8)))) (Evar __x2))
                  (Sstore Mint32
                    (Ebinop Oadd (Evar __x5)
                      (Econst (Ointconst (Int.repr 12)))) (Evar __x4))))))))))
  (Sreturn (Some (Evar __x5))))
|}.

Definition f_add_lambda0_lambda1 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x8 :: __x7 :: __x6 :: __x5 :: __x4 :: __x3 :: __x2 :: __x1 ::
              __x0 :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Sassign __x0 (Evar __arg))
    (Sseq
      (Sassign __x1 (Evar __self))
      (Sseq
        (Sassign __x2
          (Eload Mint32
            (Ebinop Oadd (Evar __x1) (Econst (Ointconst (Int.repr 4))))))
        (Sseq
          (Sseq
            (Sseq
              (Scall (Some __x3)
                (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
                (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                ((Econst (Ointconst (Int.repr 12))) :: nil))
              (Sstore Mint32 (Evar __x3)
                (Econst (Oaddrsymbol _add_lambda0_lambda1_elim0 (Int.repr 0)))))
            (Sseq
              (Sstore Mint32
                (Ebinop Oadd (Evar __x3) (Econst (Ointconst (Int.repr 4))))
                (Evar __x0))
              (Sstore Mint32
                (Ebinop Oadd (Evar __x3) (Econst (Ointconst (Int.repr 8))))
                (Evar __x2))))
          (Sseq
            (Sassign __x4 (Evar __self))
            (Sseq
              (Sassign __x5
                (Eload Mint32
                  (Ebinop Oadd (Evar __x4) (Econst (Ointconst (Int.repr 4))))))
              (Sseq
                (Scall (Some __x6)
                  (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                    cc_default) (Eload Mint32 (Evar __x3))
                  ((Evar __x3) :: (Evar __x5) :: nil))
                (Sseq
                  (Sassign __x7 (Evar __arg))
                  (Scall (Some __x8)
                    (mksignature (AST.Tint :: AST.Tint :: nil)
                      (Some AST.Tint) cc_default) (Eload Mint32 (Evar __x6))
                    ((Evar __x6) :: (Evar __x7) :: nil))))))))))
  (Sreturn (Some (Evar __x8))))
|}.

Definition f_add_lambda0 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x1 :: __x0 :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Sassign __x0 (Evar __arg))
    (Sseq
      (Sseq
        (Scall (Some __x1)
          (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
          (Econst (Oaddrsymbol _malloc (Int.repr 0)))
          ((Econst (Ointconst (Int.repr 8))) :: nil))
        (Sstore Mint32 (Evar __x1)
          (Econst (Oaddrsymbol _add_lambda0_lambda1 (Int.repr 0)))))
      (Sstore Mint32
        (Ebinop Oadd (Evar __x1) (Econst (Ointconst (Int.repr 4))))
        (Evar __x0))))
  (Sreturn (Some (Evar __x1))))
|}.

Definition f_add_lambda0_lambda1_elim0 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x5 :: __x4 :: __x3 :: __x2 :: __x1 :: __x0 :: __x22 ::
              __x21 :: __x20 :: __x19 :: __x18 :: __x17 :: __x16 :: __x15 ::
              __x14 :: __x13 :: __x12 :: __x11 :: __x10 :: __x9 :: __x8 ::
              __x7 :: __x6 :: __switch_target :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sblock
    (Sseq
      (Sblock
        (Sseq
          (Sblock
            (Sseq
              (Sassign __switch_target (Evar __arg))
              (Sswitch false (Eload Mint32 (Evar __switch_target))
                ((0%Z, (S O)) :: (1%Z, O) :: nil)
                (S (S O)))))
          (Sseq
            (Sseq
              (Sassign __x6 (Evar __self))
              (Sseq
                (Sassign __x7
                  (Eload Mint32
                    (Ebinop Oadd (Evar __x6)
                      (Econst (Ointconst (Int.repr 4))))))
                (Sseq
                  (Sassign __x8 (Evar __self))
                  (Sseq
                    (Sassign __x9
                      (Eload Mint32
                        (Ebinop Oadd (Evar __x8)
                          (Econst (Ointconst (Int.repr 8))))))
                    (Sseq
                      (Sseq
                        (Sseq
                          (Scall (Some __x10)
                            (mksignature (AST.Tint :: nil) (Some AST.Tint)
                              cc_default)
                            (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                            ((Econst (Ointconst (Int.repr 12))) :: nil))
                          (Sstore Mint32 (Evar __x10)
                            (Econst (Oaddrsymbol _add_lambda0_lambda1_lambda3 (Int.repr 0)))))
                        (Sseq
                          (Sstore Mint32
                            (Ebinop Oadd (Evar __x10)
                              (Econst (Ointconst (Int.repr 4)))) (Evar __x7))
                          (Sstore Mint32
                            (Ebinop Oadd (Evar __x10)
                              (Econst (Ointconst (Int.repr 8)))) (Evar __x9))))
                      (Sseq
                        (Sassign __x11 (Evar __arg))
                        (Sseq
                          (Sassign __x12
                            (Eload Mint32
                              (Ebinop Oadd (Evar __x11)
                                (Econst (Ointconst (Int.repr 4))))))
                          (Sseq
                            (Scall (Some __x13)
                              (mksignature (AST.Tint :: AST.Tint :: nil)
                                (Some AST.Tint) cc_default)
                              (Eload Mint32 (Evar __x10))
                              ((Evar __x10) :: (Evar __x12) :: nil))
                            (Sseq
                              (Sassign __x14 (Evar __self))
                              (Sseq
                                (Sassign __x15
                                  (Eload Mint32
                                    (Ebinop Oadd (Evar __x14)
                                      (Econst (Ointconst (Int.repr 4))))))
                                (Sseq
                                  (Sassign __x16 (Evar __self))
                                  (Sseq
                                    (Sassign __x17
                                      (Eload Mint32
                                        (Ebinop Oadd (Evar __x16)
                                          (Econst (Ointconst (Int.repr 8))))))
                                    (Sseq
                                      (Sseq
                                        (Sseq
                                          (Scall (Some __x18)
                                            (mksignature (AST.Tint :: nil)
                                              (Some AST.Tint) cc_default)
                                            (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                                            ((Econst (Ointconst (Int.repr 12))) ::
                                             nil))
                                          (Sstore Mint32 (Evar __x18)
                                            (Econst (Oaddrsymbol _add_lambda0_lambda1_elim0 (Int.repr 0)))))
                                        (Sseq
                                          (Sstore Mint32
                                            (Ebinop Oadd (Evar __x18)
                                              (Econst (Ointconst (Int.repr 4))))
                                            (Evar __x15))
                                          (Sstore Mint32
                                            (Ebinop Oadd (Evar __x18)
                                              (Econst (Ointconst (Int.repr 8))))
                                            (Evar __x17))))
                                      (Sseq
                                        (Sassign __x19 (Evar __arg))
                                        (Sseq
                                          (Sassign __x20
                                            (Eload Mint32
                                              (Ebinop Oadd (Evar __x19)
                                                (Econst (Ointconst (Int.repr 4))))))
                                          (Sseq
                                            (Scall (Some __x21)
                                              (mksignature
                                                (AST.Tint :: AST.Tint :: nil)
                                                (Some AST.Tint) cc_default)
                                              (Eload Mint32 (Evar __x18))
                                              ((Evar __x18) ::
                                               (Evar __x20) :: nil))
                                            (Sseq
                                              (Scall (Some __x22)
                                                (mksignature
                                                  (AST.Tint :: AST.Tint ::
                                                   nil) (Some AST.Tint)
                                                  cc_default)
                                                (Eload Mint32 (Evar __x13))
                                                ((Evar __x13) ::
                                                 (Evar __x21) :: nil))
                                              (Sassign __x0 (Evar __x22)))))))))))))))))))
            (Sexit (S O)))))
      (Sseq
        (Sseq
          (Sassign __x1 (Evar __self))
          (Sseq
            (Sassign __x2
              (Eload Mint32
                (Ebinop Oadd (Evar __x1) (Econst (Ointconst (Int.repr 4))))))
            (Sseq
              (Sassign __x3 (Evar __self))
              (Sseq
                (Sassign __x4
                  (Eload Mint32
                    (Ebinop Oadd (Evar __x3)
                      (Econst (Ointconst (Int.repr 8))))))
                (Sseq
                  (Sseq
                    (Sseq
                      (Scall (Some __x5)
                        (mksignature (AST.Tint :: nil) (Some AST.Tint)
                          cc_default)
                        (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                        ((Econst (Ointconst (Int.repr 12))) :: nil))
                      (Sstore Mint32 (Evar __x5)
                        (Econst (Oaddrsymbol _add_lambda0_lambda1_lambda2 (Int.repr 0)))))
                    (Sseq
                      (Sstore Mint32
                        (Ebinop Oadd (Evar __x5)
                          (Econst (Ointconst (Int.repr 4)))) (Evar __x2))
                      (Sstore Mint32
                        (Ebinop Oadd (Evar __x5)
                          (Econst (Ointconst (Int.repr 8)))) (Evar __x4))))
                  (Sassign __x0 (Evar __x5)))))))
        (Sexit O))))
  (Sreturn (Some (Evar __x0))))
|}.

Definition f_main := {|
  fn_sig := (mksignature nil (Some AST.Tint) cc_default);
  fn_params := nil;
  fn_vars := nil;
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sreturn (Some (Econst (Ointconst (Int.repr 0)))))
  (Sreturn (Some (Econst (Ointconst (Int.repr 0))))))
|}.

Definition prog : Cminor.program := {|
prog_defs :=
((_add, Gfun(Internal f_add)) ::
 (_add_lambda0_lambda1_lambda2, Gfun(Internal f_add_lambda0_lambda1_lambda2)) ::
 (_add_lambda0_lambda1_lambda3_lambda4_lambda5, Gfun(Internal f_add_lambda0_lambda1_lambda3_lambda4_lambda5)) ::
 (_add_lambda0_lambda1_lambda3_lambda4, Gfun(Internal f_add_lambda0_lambda1_lambda3_lambda4)) ::
 (_add_lambda0_lambda1_lambda3, Gfun(Internal f_add_lambda0_lambda1_lambda3)) ::
 (_add_lambda0_lambda1, Gfun(Internal f_add_lambda0_lambda1)) ::
 (_add_lambda0, Gfun(Internal f_add_lambda0)) ::
 (_add_lambda0_lambda1_elim0, Gfun(Internal f_add_lambda0_lambda1_elim0)) ::
 (___i64_dtos,
   Gfun(External (EF_external "__i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)))) ::
 (___i64_dtou,
   Gfun(External (EF_external "__i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)))) ::
 (___i64_stod,
   Gfun(External (EF_external "__i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)))) ::
 (___i64_utod,
   Gfun(External (EF_external "__i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)))) ::
 (___i64_stof,
   Gfun(External (EF_external "__i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)))) ::
 (___i64_utof,
   Gfun(External (EF_external "__i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)))) ::
 (___i64_sdiv,
   Gfun(External (EF_external "__i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default)))) ::
 (___i64_udiv,
   Gfun(External (EF_external "__i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default)))) ::
 (___i64_smod,
   Gfun(External (EF_external "__i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default)))) ::
 (___i64_umod,
   Gfun(External (EF_external "__i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default)))) ::
 (___i64_shl,
   Gfun(External (EF_external "__i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default)))) ::
 (___i64_shr,
   Gfun(External (EF_external "__i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default)))) ::
 (___i64_sar,
   Gfun(External (EF_external "__i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default)))) ::
 (_malloc, Gfun(External EF_malloc)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)))) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default)))) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})))) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)))) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)))) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default)))) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)))) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)))) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default)))) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)))) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)))) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)))) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)))) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)))) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)))) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)))) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)))) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)))) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)))) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)))) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)))) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)))) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)))) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default)))) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default)))) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default)))) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default)))) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default)))) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default)))) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)))) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)))) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)))) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)))) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)))) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})))) ::
 (_main, Gfun(Internal f_main)) :: nil);
prog_public :=
(_main :: ___builtin_debug :: ___builtin_nop ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_fsqrt :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___i64_sar :: ___i64_shr :: ___i64_shl :: ___i64_umod :: ___i64_smod ::
 ___i64_udiv :: ___i64_sdiv :: ___i64_utof :: ___i64_stof :: ___i64_utod ::
 ___i64_stod :: ___i64_dtou :: ___i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_memcpy_aligned :: ___builtin_fabs :: nil);
prog_main := _main;
|}.

