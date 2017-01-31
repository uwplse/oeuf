Require Import compcert.backend.Cminor.
Require Import compcert.common.AST.
Require Import BinNums.
Require Import compcert.lib.Integers.
Require Import List.
Import ListNotations.

Local Open Scope Z_scope.

Definition __x4 : ident := 136%positive.
Definition _t : ident := 85%positive.
Definition _main : ident := 110%positive.
Definition __arg : ident := 143%positive.
Definition __x2 : ident := 138%positive.
Definition __x10 : ident := 130%positive.
Definition _add_lambda0_lambda1_elim0 : ident := 111%positive.
Definition __682 : ident := 22%positive.
Definition __x3 : ident := 137%positive.
Definition _tm : ident := 12%positive.
Definition __x12 : ident := 128%positive.
Definition _m : ident := 108%positive.
Definition ___builtin_ctz : ident := 63%positive.
Definition ___tm_gmtoff : ident := 10%positive.
Definition ___i64_dtos : ident := 44%positive.
Definition _tm_hour : ident := 3%positive.
Definition _tm_sec : ident := 1%positive.
Definition __x16 : ident := 124%positive.
Definition _get_time : ident := 88%positive.
Definition __x21 : ident := 119%positive.
Definition _printf : ident := 79%positive.
Definition ___builtin_fnmsub : ident := 72%positive.
Definition ___stringlit_3 : ident := 109%positive.
Definition ___builtin_debug : ident := 78%positive.
Definition ___builtin_fmin : ident := 68%positive.
Definition _cons : ident := 28%positive.
Definition __self : ident := 142%positive.
Definition _add_lambda0_lambda1 : ident := 113%positive.
Definition _a : ident := 102%positive.
Definition _tm_wday : ident := 7%positive.
Definition _call : ident := 103%positive.
Definition __x5 : ident := 135%positive.
Definition __switch_target : ident := 141%positive.
Definition _print_list_nat : ident := 101%positive.
Definition _ptr : ident := 89%positive.
Definition ___i64_dtou : ident := 45%positive.
Definition _nil : ident := 27%positive.
Definition _time_buf : ident := 84%positive.
Definition _time : ident := 82%positive.
Definition _next : ident := 25%positive.
Definition _nat : ident := 15%positive.
Definition ___builtin_clz : ident := 60%positive.
Definition __x11 : ident := 129%positive.
Definition _add_lambda0_lambda1_lambda3 : ident := 114%positive.
Definition ___builtin_memcpy_aligned : ident := 32%positive.
Definition _add_lambda0_lambda1_lambda2 : ident := 117%positive.
Definition ___builtin_fmsub : ident := 70%positive.
Definition _b : ident := 96%positive.
Definition __658 : ident := 17%positive.
Definition _tm_yday : ident := 8%positive.
Definition __x13 : ident := 127%positive.
Definition ___compcert_va_composite : ident := 43%positive.
Definition ___i64_umod : ident := 53%positive.
Definition ___i64_utod : ident := 47%positive.
Definition _tmp : ident := 91%positive.
Definition ___builtin_va_start : ident := 36%positive.
Definition _read_bool : ident := 98%positive.
Definition _S : ident := 19%positive.
Definition ___builtin_clzl : ident := 61%positive.
Definition _make_bool : ident := 97%positive.
Definition __x18 : ident := 122%positive.
Definition ___builtin_va_arg : ident := 37%positive.
Definition __x7 : ident := 133%positive.
Definition ___compcert_va_float64 : ident := 42%positive.
Definition __x8 : ident := 132%positive.
Definition ___builtin_fnmadd : ident := 71%positive.
Definition ___builtin_write16_reversed : ident := 75%positive.
Definition ___builtin_annot_intval : ident := 34%positive.
Definition _f : ident := 29%positive.
Definition _make_unit : ident := 95%positive.
Definition ___i64_shr : ident := 55%positive.
Definition ___i64_udiv : ident := 51%positive.
Definition ___i64_stof : ident := 48%positive.
Definition ___builtin_ctzll : ident := 65%positive.
Definition ___compcert_va_int32 : ident := 40%positive.
Definition _add_lambda0 : ident := 112%positive.
Definition _n : ident := 16%positive.
Definition ___builtin_va_copy : ident := 38%positive.
Definition ___i64_stod : ident := 46%positive.
Definition ___builtin_fmadd : ident := 69%positive.
Definition ___builtin_clzll : ident := 62%positive.
Definition ___i64_shl : ident := 54%positive.
Definition _make_nat : ident := 92%positive.
Definition _ap : ident := 104%positive.
Definition _tm_min : ident := 2%positive.
Definition __x19 : ident := 121%positive.
Definition ___builtin_fabs : ident := 31%positive.
Definition ___i64_utof : ident := 49%positive.
Definition ___builtin_fsqrt : ident := 66%positive.
Definition ___builtin_bswap16 : ident := 59%positive.
Definition _tm_mday : ident := 4%positive.
Definition _result : ident := 94%positive.
Definition ___builtin_bswap32 : ident := 58%positive.
Definition __x15 : ident := 125%positive.
Definition _l : ident := 99%positive.
Definition _bool : ident := 21%positive.
Definition _O : ident := 18%positive.
Definition _add : ident := 106%positive.
Definition _snprintf : ident := 80%positive.
Definition _tag : ident := 13%positive.
Definition ___builtin_annot : ident := 33%positive.
Definition __x17 : ident := 123%positive.
Definition ___i64_sar : ident := 56%positive.
Definition __x1 : ident := 139%positive.
Definition _add_lambda0_lambda1_lambda3_lambda4 : ident := 115%positive.
Definition ___stringlit_2 : ident := 100%positive.
Definition _unit : ident := 20%positive.
Definition _read_nat : ident := 93%positive.
Definition _vcall : ident := 105%positive.
Definition __x14 : ident := 126%positive.
Definition _list : ident := 24%positive.
Definition ___builtin_fmax : ident := 67%positive.
Definition _tm_mon : ident := 5%positive.
Definition ___builtin_read16_reversed : ident := 73%positive.
Definition ___i64_sdiv : ident := 50%positive.
Definition ___builtin_read32_reversed : ident := 74%positive.
Definition _add_closure : ident := 107%positive.
Definition ___builtin_bswap : ident := 57%positive.
Definition __657 : ident := 14%positive.
Definition _tm_year : ident := 6%positive.
Definition __x0 : ident := 140%positive.
Definition __x22 : ident := 118%positive.
Definition __683 : ident := 26%positive.
Definition __x6 : ident := 134%positive.
Definition ___builtin_va_end : ident := 39%positive.
Definition _i : ident := 90%positive.
Definition _localtime : ident := 83%positive.
Definition ___tm_zone : ident := 11%positive.
Definition _add_lambda0_lambda1_lambda3_lambda4_lambda5 : ident := 116%positive.
Definition _malloc : ident := 81%positive.
Definition ___builtin_write32_reversed : ident := 76%positive.
Definition _tm__1 : ident := 86%positive.
Definition _tm_isdst : ident := 9%positive.
Definition __x9 : ident := 131%positive.
Definition ___builtin_ctzl : ident := 64%positive.
Definition ___i64_smod : ident := 52%positive.
Definition ___compcert_va_int64 : ident := 41%positive.
Definition ___stringlit_1 : ident := 87%positive.
Definition ___builtin_nop : ident := 77%positive.
Definition __x20 : ident := 120%positive.
Definition ___builtin_membar : ident := 35%positive.
Definition _closure : ident := 30%positive.
Definition _data : ident := 23%positive.

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

Definition v___stringlit_2 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_time_buf := {|
  gvar_info := tt;
  gvar_init := (Init_space 8192 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_get_time := {|
  fn_sig := (mksignature nil (Some AST.Tint) cc_default);
  fn_params := nil;
  fn_vars := (145%positive :: 144%positive :: nil);
  fn_stackspace := 52;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 144%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _time (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 0))) :: nil))
    (Sstore Mint32 (Econst (Oaddrstack (Int.repr 0))) (Evar 144%positive)))
  (Sseq
    (Sseq
      (Scall (Some 145%positive)
        (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
        (Econst (Oaddrsymbol _localtime (Int.repr 0)))
        ((Econst (Oaddrstack (Int.repr 0))) :: nil))
      (Sbuiltin None (EF_memcpy 44 4)
        ((Econst (Oaddrstack (Int.repr 8))) :: (Evar 145%positive) :: nil)))
    (Sseq
      (Scall None
        (mksignature
          (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
           AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
          (Some AST.Tint)
          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
        (Econst (Oaddrsymbol _snprintf (Int.repr 0)))
        ((Econst (Oaddrsymbol _time_buf (Int.repr 0))) ::
         (Econst (Ointconst (Int.repr 8192))) ::
         (Econst (Oaddrsymbol ___stringlit_1 (Int.repr 0))) ::
         (Ebinop Oadd
           (Eload Mint32
             (Ebinop Oadd (Econst (Oaddrstack (Int.repr 8)))
               (Econst (Ointconst (Int.repr 20)))))
           (Econst (Ointconst (Int.repr 1900)))) ::
         (Ebinop Oadd
           (Eload Mint32
             (Ebinop Oadd (Econst (Oaddrstack (Int.repr 8)))
               (Econst (Ointconst (Int.repr 16)))))
           (Econst (Ointconst (Int.repr 1)))) ::
         (Eload Mint32
           (Ebinop Oadd (Econst (Oaddrstack (Int.repr 8)))
             (Econst (Ointconst (Int.repr 12))))) ::
         (Eload Mint32
           (Ebinop Oadd (Econst (Oaddrstack (Int.repr 8)))
             (Econst (Ointconst (Int.repr 8))))) ::
         (Eload Mint32
           (Ebinop Oadd (Econst (Oaddrstack (Int.repr 8)))
             (Econst (Ointconst (Int.repr 4))))) ::
         (Eload Mint32
           (Ebinop Oadd (Econst (Oaddrstack (Int.repr 8)))
             (Econst (Ointconst (Int.repr 0))))) :: nil))
      (Sreturn (Some (Econst (Oaddrsymbol _time_buf (Int.repr 0))))))))
|}.

Definition f_make_nat := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_n :: nil);
  fn_vars := (_ptr :: _i :: _tmp :: 147%positive :: 146%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 146%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 4))) :: nil))
    (Sassign _ptr (Evar 146%positive)))
  (Sseq
    (Sstore Mint32 (Evar _ptr) (Econst (Ointconst (Int.repr 0))))
    (Sseq
      (Sseq
        (Sassign _i (Econst (Ointconst (Int.repr 1))))
        (Sblock
          (Sloop
            (Sseq
              (Sblock
                (Sseq
                  (Sifthenelse (Ebinop (Ocmp Cle) (Evar _i) (Evar _n))
                    Sskip
                    (Sexit (S O)))
                  (Sseq
                    (Sseq
                      (Scall (Some 147%positive)
                        (mksignature (AST.Tint :: nil) (Some AST.Tint)
                          cc_default)
                        (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                        ((Econst (Ointconst (Int.repr 8))) :: nil))
                      (Sassign _tmp (Evar 147%positive)))
                    (Sseq
                      (Sstore Mint32 (Evar _tmp)
                        (Econst (Ointconst (Int.repr 1))))
                      (Sseq
                        (Sstore Mint32
                          (Ebinop Oadd (Evar _tmp)
                            (Econst (Ointconst (Int.repr 4)))) (Evar _ptr))
                        (Sassign _ptr (Evar _tmp)))))))
              (Sassign _i
                (Ebinop Oadd (Evar _i) (Econst (Ointconst (Int.repr 1)))))))))
      (Sreturn (Some (Evar _ptr))))))
|}.

Definition f_read_nat := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_n :: nil);
  fn_vars := (_i :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sassign _i (Econst (Ointconst (Int.repr 0))))
  (Sseq
    (Sblock
      (Sloop
        (Sblock
          (Sseq
            (Sifthenelse (Ebinop (Ocmp Ceq) (Eload Mint32 (Evar _n))
                           (Econst (Ointconst (Int.repr 1))))
              Sskip
              (Sexit (S O)))
            (Sseq
              (Sassign _i
                (Ebinop Oadd (Evar _i) (Econst (Ointconst (Int.repr 1)))))
              (Sassign _n
                (Eload Mint32
                  (Ebinop Oadd (Evar _n) (Econst (Ointconst (Int.repr 4)))))))))))
    (Sreturn (Some (Evar _i)))))
|}.

Definition f_make_unit := {|
  fn_sig := (mksignature nil (Some AST.Tint) cc_default);
  fn_params := nil;
  fn_vars := (_result :: 148%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 148%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 4))) :: nil))
    (Sassign _result (Evar 148%positive)))
  (Sseq
    (Sstore Mint32 (Evar _result) (Econst (Ointconst (Int.repr 0))))
    (Sreturn (Some (Evar _result)))))
|}.

Definition f_make_bool := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_b :: nil);
  fn_vars := (_result :: 150%positive :: 149%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 149%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 4))) :: nil))
    (Sassign _result (Evar 149%positive)))
  (Sseq
    (Sseq
      (Sifthenelse (Ebinop (Ocmp Cne) (Evar _b)
                     (Econst (Ointconst (Int.repr 0))))
        (Sassign 150%positive (Econst (Ointconst (Int.repr 0))))
        (Sassign 150%positive (Econst (Ointconst (Int.repr 1)))))
      (Sstore Mint32 (Evar _result) (Evar 150%positive)))
    (Sreturn (Some (Evar _result)))))
|}.

Definition f_read_bool := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_b :: nil);
  fn_vars := nil;
  fn_stackspace := 0;
  fn_body :=
(Sreturn (Some (Ebinop (Ocmp Ceq) (Eload Mint32 (Evar _b))
                 (Econst (Ointconst (Int.repr 0))))))
|}.

Definition f_print_list_nat := {|
  fn_sig := (mksignature (AST.Tint :: nil) None cc_default);
  fn_params := (_l :: nil);
  fn_vars := (_i :: 151%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sblock
  (Sloop
    (Sblock
      (Sseq
        (Sifthenelse (Ebinop (Ocmp Ceq) (Eload Mint32 (Evar _l))
                       (Econst (Ointconst (Int.repr 1))))
          Sskip
          (Sexit (S O)))
        (Sseq
          (Sseq
            (Scall (Some 151%positive)
              (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
              (Econst (Oaddrsymbol _read_nat (Int.repr 0)))
              ((Eload Mint32
                 (Ebinop Oadd (Evar _l) (Econst (Ointconst (Int.repr 4))))) ::
               nil))
            (Sassign _i (Evar 151%positive)))
          (Sseq
            (Scall None
              (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
              (Econst (Oaddrsymbol _printf (Int.repr 0)))
              ((Econst (Oaddrsymbol ___stringlit_2 (Int.repr 0))) ::
               (Evar _i) :: nil))
            (Sassign _l
              (Eload Mint32
                (Ebinop Oadd (Evar _l) (Econst (Ointconst (Int.repr 8))))))))))))
|}.

Definition f_call := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (_f :: _a :: nil);
  fn_vars := (152%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Scall (Some 152%positive)
    (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint) cc_default)
    (Eload Mint32 (Ebinop Oadd (Evar _f) (Econst (Ointconst (Int.repr 0)))))
    ((Evar _f) :: (Evar _a) :: nil))
  (Sreturn (Some (Evar 152%positive))))
|}.

Definition f_vcall := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint)
              {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|});
  fn_params := (_f :: nil);
  fn_vars := (_a :: 155%positive :: 154%positive :: 153%positive :: nil);
  fn_stackspace := 4;
  fn_body :=
(Sseq
  (Sassign _a (Econst (Ointconst (Int.repr 0))))
  (Sseq
    (Scall None (mksignature (AST.Tint :: nil) None cc_default)
      (Econst (Oaddrsymbol ___builtin_va_start (Int.repr 0)))
      ((Econst (Oaddrstack (Int.repr 0))) :: nil))
    (Sseq
      (Sblock
        (Sloop
          (Sblock
            (Sseq
              (Sseq
                (Sseq
                  (Sseq
                    (Scall (Some 153%positive)
                      (mksignature (AST.Tint :: nil) (Some AST.Tint)
                        cc_default)
                      (Econst (Oaddrsymbol ___compcert_va_int32 (Int.repr 0)))
                      ((Econst (Oaddrstack (Int.repr 0))) :: nil))
                    (Sassign 154%positive (Evar 153%positive)))
                  (Sassign _a (Evar 154%positive)))
                (Sifthenelse (Ebinop (Ocmpu Cne) (Evar 154%positive)
                               (Econst (Ointconst (Int.repr 0))))
                  Sskip
                  (Sexit (S O))))
              (Sseq
                (Scall (Some 155%positive)
                  (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                    cc_default) (Econst (Oaddrsymbol _call (Int.repr 0)))
                  ((Evar _f) :: (Evar _a) :: nil))
                (Sassign _f (Evar 155%positive)))))))
      (Sreturn (Some (Evar _f))))))
|}.

Definition f_main := {|
  fn_sig := (mksignature nil (Some AST.Tint) cc_default);
  fn_params := nil;
  fn_vars := (_n :: _add_closure :: _m :: 161%positive :: 160%positive ::
              159%positive :: 158%positive :: 157%positive :: 156%positive ::
              nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Sseq
      (Scall (Some 156%positive)
        (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
        (Econst (Oaddrsymbol _make_nat (Int.repr 0)))
        ((Econst (Ointconst (Int.repr 3))) :: nil))
      (Sassign _n (Evar 156%positive)))
    (Sseq
      (Sseq
        (Scall (Some 157%positive)
          (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
            cc_default) (Econst (Oaddrsymbol _add (Int.repr 0)))
          ((Econst (Ointconst (Int.repr 0))) ::
           (Econst (Ointconst (Int.repr 0))) :: nil))
        (Sassign _add_closure (Evar 157%positive)))
      (Sseq
        (Sseq
          (Scall (Some 158%positive)
            (mksignature
              (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
              (Some AST.Tint)
              {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
            (Econst (Oaddrsymbol _vcall (Int.repr 0)))
            ((Evar _add_closure) :: (Evar _n) :: (Evar _n) ::
             (Econst (Ointconst (Int.repr 0))) :: nil))
          (Sassign _m (Evar 158%positive)))
        (Sseq
          (Sseq
            (Sseq
              (Sseq
                (Scall (Some 159%positive)
                  (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
                  (Econst (Oaddrsymbol _read_nat (Int.repr 0)))
                  ((Evar _n) :: nil))
                (Scall (Some 160%positive)
                  (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
                  (Econst (Oaddrsymbol _read_nat (Int.repr 0)))
                  ((Evar _n) :: nil)))
              (Scall (Some 161%positive)
                (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
                (Econst (Oaddrsymbol _read_nat (Int.repr 0)))
                ((Evar _m) :: nil)))
            (Scall None
              (mksignature
                (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                (Some AST.Tint)
                {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
              (Econst (Oaddrsymbol _printf (Int.repr 0)))
              ((Econst (Oaddrsymbol ___stringlit_3 (Int.repr 0))) ::
               (Evar 159%positive) :: (Evar 160%positive) ::
               (Evar 161%positive) :: nil)))
          (Sreturn (Some (Econst (Ointconst (Int.repr 0)))))))))
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
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
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
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})))) ::
 (_snprintf,
   Gfun(External (EF_external "snprintf"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})))) ::
 (_time,
   Gfun(External (EF_external "time"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)))) ::
 (_localtime,
   Gfun(External (EF_external "localtime"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)))) ::
 (_time_buf, Gvar v_time_buf) :: (_get_time, Gfun(Internal f_get_time)) ::
 (_make_nat, Gfun(Internal f_make_nat)) ::
 (_read_nat, Gfun(Internal f_read_nat)) ::
 (_make_unit, Gfun(Internal f_make_unit)) ::
 (_make_bool, Gfun(Internal f_make_bool)) ::
 (_read_bool, Gfun(Internal f_read_bool)) ::
 (_print_list_nat, Gfun(Internal f_print_list_nat)) ::
 (_call, Gfun(Internal f_call)) :: (_vcall, Gfun(Internal f_vcall)) ::
 (_main, Gfun(Internal f_main)) :: nil);
prog_public :=
(_main :: _add :: _vcall :: _call :: _print_list_nat :: _read_bool ::
 _make_bool :: _make_unit :: _read_nat :: _make_nat :: _get_time ::
 _localtime :: _time :: _malloc :: _snprintf :: _printf ::
 ___builtin_debug :: ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_fsqrt :: ___builtin_ctzll ::
 ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll :: ___builtin_clzl ::
 ___builtin_clz :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___i64_sar :: ___i64_shr :: ___i64_shl :: ___i64_umod ::
 ___i64_smod :: ___i64_udiv :: ___i64_sdiv :: ___i64_utof :: ___i64_stof ::
 ___i64_utod :: ___i64_stod :: ___i64_dtou :: ___i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_memcpy_aligned :: ___builtin_fabs :: nil);
prog_main := _main;
|}.

