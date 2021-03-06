Require Import compcert.backend.Cminor.
Require Import compcert.common.AST.
Require Import BinNums.
Require Import compcert.lib.Integers.
Require Import List.
Import ListNotations.

Local Open Scope Z_scope.

Definition __x27 : ident := 136%positive.
Definition _t : ident := 85%positive.
Definition __x9 : ident := 154%positive.
Definition _fib_lambda0_elim1 : ident := 110%positive.
Definition __x15 : ident := 148%positive.
Definition __x20 : ident := 143%positive.
Definition __x25 : ident := 138%positive.
Definition __x33 : ident := 130%positive.
Definition _fib_lambda0_lambda3_lambda4_lambda5_lambda6_elim0 : ident := 111%positive.
Definition __682 : ident := 22%positive.
Definition __x26 : ident := 137%positive.
Definition _tm : ident := 12%positive.
Definition __x35 : ident := 128%positive.
Definition ___stringlit_3 : ident := 108%positive.
Definition ___builtin_ctz : ident := 63%positive.
Definition ___tm_gmtoff : ident := 10%positive.
Definition ___i64_dtos : ident := 44%positive.
Definition _tm_hour : ident := 3%positive.
Definition _tm_sec : ident := 1%positive.
Definition __x39 : ident := 124%positive.
Definition _get_time : ident := 88%positive.
Definition _fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda8_lambda9_lambda10 : ident := 119%positive.
Definition _printf : ident := 79%positive.
Definition ___builtin_fnmsub : ident := 72%positive.
Definition __x13 : ident := 150%positive.
Definition _main : ident := 109%positive.
Definition ___builtin_debug : ident := 78%positive.
Definition ___builtin_fmin : ident := 68%positive.
Definition _cons : ident := 28%positive.
Definition __x21 : ident := 142%positive.
Definition _fib_lambda0_lambda3 : ident := 113%positive.
Definition _a : ident := 102%positive.
Definition _tm_wday : ident := 7%positive.
Definition __x6 : ident := 157%positive.
Definition _call : ident := 103%positive.
Definition __x28 : ident := 135%positive.
Definition __x22 : ident := 141%positive.
Definition _print_list_nat : ident := 101%positive.
Definition _ptr : ident := 89%positive.
Definition ___i64_dtou : ident := 45%positive.
Definition _nil : ident := 27%positive.
Definition _time_buf : ident := 84%positive.
Definition _time : ident := 82%positive.
Definition _next : ident := 25%positive.
Definition _nat : ident := 15%positive.
Definition ___builtin_clz : ident := 60%positive.
Definition __x34 : ident := 129%positive.
Definition _fib_lambda0_lambda3_lambda4 : ident := 114%positive.
Definition ___builtin_memcpy_aligned : ident := 32%positive.
Definition _fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda8 : ident := 117%positive.
Definition ___builtin_fmsub : ident := 70%positive.
Definition _b : ident := 96%positive.
Definition __658 : ident := 17%positive.
Definition _tm_yday : ident := 8%positive.
Definition __x36 : ident := 127%positive.
Definition ___compcert_va_composite : ident := 43%positive.
Definition ___i64_umod : ident := 53%positive.
Definition ___i64_utod : ident := 47%positive.
Definition __x14 : ident := 149%positive.
Definition _tmp : ident := 91%positive.
Definition ___builtin_va_start : ident := 36%positive.
Definition _read_bool : ident := 98%positive.
Definition _S : ident := 19%positive.
Definition ___builtin_clzl : ident := 61%positive.
Definition _make_bool : ident := 97%positive.
Definition _fib_lambda0_lambda1_lambda2 : ident := 122%positive.
Definition ___builtin_va_arg : ident := 37%positive.
Definition __x30 : ident := 133%positive.
Definition __x11 : ident := 152%positive.
Definition ___compcert_va_float64 : ident := 42%positive.
Definition __x31 : ident := 132%positive.
Definition ___builtin_fnmadd : ident := 71%positive.
Definition __x2 : ident := 161%positive.
Definition __x4 : ident := 159%positive.
Definition ___builtin_write16_reversed : ident := 75%positive.
Definition ___builtin_annot_intval : ident := 34%positive.
Definition _f : ident := 29%positive.
Definition _make_unit : ident := 95%positive.
Definition ___i64_shr : ident := 55%positive.
Definition ___i64_udiv : ident := 51%positive.
Definition ___i64_stof : ident := 48%positive.
Definition __arg : ident := 166%positive.
Definition __x16 : ident := 147%positive.
Definition ___builtin_ctzll : ident := 65%positive.
Definition ___compcert_va_int32 : ident := 40%positive.
Definition _fib_lambda0 : ident := 112%positive.
Definition _n : ident := 16%positive.
Definition ___builtin_va_copy : ident := 38%positive.
Definition ___i64_stod : ident := 46%positive.
Definition ___builtin_fmadd : ident := 69%positive.
Definition ___builtin_clzll : ident := 62%positive.
Definition ___i64_shl : ident := 54%positive.
Definition _make_nat : ident := 92%positive.
Definition __x10 : ident := 153%positive.
Definition _ap : ident := 104%positive.
Definition _tm_min : ident := 2%positive.
Definition _fib_lambda0_lambda1 : ident := 121%positive.
Definition ___builtin_fabs : ident := 31%positive.
Definition __x1 : ident := 162%positive.
Definition ___i64_utof : ident := 49%positive.
Definition ___builtin_fsqrt : ident := 66%positive.
Definition ___builtin_bswap16 : ident := 59%positive.
Definition _tm_mday : ident := 4%positive.
Definition __switch_target : ident := 164%positive.
Definition __self : ident := 165%positive.
Definition _result : ident := 94%positive.
Definition ___builtin_bswap32 : ident := 58%positive.
Definition __x12 : ident := 151%positive.
Definition __x17 : ident := 146%positive.
Definition __x0 : ident := 163%positive.
Definition __x38 : ident := 125%positive.
Definition _l : ident := 99%positive.
Definition _bool : ident := 21%positive.
Definition _O : ident := 18%positive.
Definition _fib : ident := 106%positive.
Definition _snprintf : ident := 80%positive.
Definition _tag : ident := 13%positive.
Definition ___builtin_annot : ident := 33%positive.
Definition __x40 : ident := 123%positive.
Definition ___i64_sar : ident := 56%positive.
Definition __x24 : ident := 139%positive.
Definition _fib_lambda0_lambda3_lambda4_lambda5 : ident := 115%positive.
Definition ___stringlit_2 : ident := 100%positive.
Definition _unit : ident := 20%positive.
Definition __x7 : ident := 156%positive.
Definition _read_nat : ident := 93%positive.
Definition _vcall : ident := 105%positive.
Definition __x37 : ident := 126%positive.
Definition _list : ident := 24%positive.
Definition ___builtin_fmax : ident := 67%positive.
Definition _tm_mon : ident := 5%positive.
Definition ___builtin_read16_reversed : ident := 73%positive.
Definition ___i64_sdiv : ident := 50%positive.
Definition ___builtin_read32_reversed : ident := 74%positive.
Definition __x8 : ident := 155%positive.
Definition _fib_closure : ident := 107%positive.
Definition ___builtin_bswap : ident := 57%positive.
Definition __657 : ident := 14%positive.
Definition _tm_year : ident := 6%positive.
Definition __x23 : ident := 140%positive.
Definition _fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda8_lambda9 : ident := 118%positive.
Definition __683 : ident := 26%positive.
Definition __x5 : ident := 158%positive.
Definition __x29 : ident := 134%positive.
Definition ___builtin_va_end : ident := 39%positive.
Definition _i : ident := 90%positive.
Definition _localtime : ident := 83%positive.
Definition ___tm_zone : ident := 11%positive.
Definition _fib_lambda0_lambda3_lambda4_lambda5_lambda6 : ident := 116%positive.
Definition _malloc : ident := 81%positive.
Definition ___builtin_write32_reversed : ident := 76%positive.
Definition __x18 : ident := 145%positive.
Definition __x3 : ident := 160%positive.
Definition __x19 : ident := 144%positive.
Definition _tm__1 : ident := 86%positive.
Definition _tm_isdst : ident := 9%positive.
Definition __x32 : ident := 131%positive.
Definition ___builtin_ctzl : ident := 64%positive.
Definition ___i64_smod : ident := 52%positive.
Definition ___compcert_va_int64 : ident := 41%positive.
Definition ___stringlit_1 : ident := 87%positive.
Definition ___builtin_nop : ident := 77%positive.
Definition _fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda7 : ident := 120%positive.
Definition ___builtin_membar : ident := 35%positive.
Definition _closure : ident := 30%positive.
Definition _data : ident := 23%positive.

Definition f_fib := {|
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
      (Econst (Oaddrsymbol _fib_lambda0 (Int.repr 0)))))
  (Sreturn (Some (Evar __x0))))
|}.

Definition f_fib_lambda0_lambda1_lambda2 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x1 :: __x0 :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Sassign __x0 (Evar __self))
    (Sassign __x1
      (Eload Mint32
        (Ebinop Oadd (Evar __x0) (Econst (Ointconst (Int.repr 4)))))))
  (Sreturn (Some (Evar __x1))))
|}.

Definition f_fib_lambda0_lambda1 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x3 :: __x2 :: __x1 :: __x0 :: nil);
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
            (Scall (Some __x3)
              (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
              (Econst (Oaddrsymbol _malloc (Int.repr 0)))
              ((Econst (Ointconst (Int.repr 12))) :: nil))
            (Sstore Mint32 (Evar __x3)
              (Econst (Oaddrsymbol _fib_lambda0_lambda1_lambda2 (Int.repr 0)))))
          (Sseq
            (Sstore Mint32
              (Ebinop Oadd (Evar __x3) (Econst (Ointconst (Int.repr 4))))
              (Evar __x0))
            (Sstore Mint32
              (Ebinop Oadd (Evar __x3) (Econst (Ointconst (Int.repr 8))))
              (Evar __x2)))))))
  (Sreturn (Some (Evar __x3))))
|}.

Definition f_fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda7 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x0 :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq (Sassign __x0 (Evar __arg)) (Sreturn (Some (Evar __x0))))
|}.

Definition f_fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda8_lambda9_lambda10 := {|
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

Definition f_fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda8_lambda9 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x13 :: __x12 :: __x11 :: __x10 :: __x9 :: __x8 :: __x7 ::
              __x6 :: __x5 :: __x4 :: __x3 :: __x2 :: __x1 :: __x0 :: nil);
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
                  (Sassign __x7 (Evar __self))
                  (Sseq
                    (Sassign __x8
                      (Eload Mint32
                        (Ebinop Oadd (Evar __x7)
                          (Econst (Ointconst (Int.repr 16))))))
                    (Sseq
                      (Sassign __x9 (Evar __self))
                      (Sseq
                        (Sassign __x10
                          (Eload Mint32
                            (Ebinop Oadd (Evar __x9)
                              (Econst (Ointconst (Int.repr 20))))))
                        (Sseq
                          (Sassign __x11 (Evar __self))
                          (Sseq
                            (Sassign __x12
                              (Eload Mint32
                                (Ebinop Oadd (Evar __x11)
                                  (Econst (Ointconst (Int.repr 24))))))
                            (Sseq
                              (Sseq
                                (Scall (Some __x13)
                                  (mksignature (AST.Tint :: nil)
                                    (Some AST.Tint) cc_default)
                                  (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                                  ((Econst (Ointconst (Int.repr 32))) :: nil))
                                (Sstore Mint32 (Evar __x13)
                                  (Econst (Oaddrsymbol _fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda8_lambda9_lambda10 (Int.repr 0)))))
                              (Sseq
                                (Sstore Mint32
                                  (Ebinop Oadd (Evar __x13)
                                    (Econst (Ointconst (Int.repr 4))))
                                  (Evar __x0))
                                (Sseq
                                  (Sstore Mint32
                                    (Ebinop Oadd (Evar __x13)
                                      (Econst (Ointconst (Int.repr 8))))
                                    (Evar __x2))
                                  (Sseq
                                    (Sstore Mint32
                                      (Ebinop Oadd (Evar __x13)
                                        (Econst (Ointconst (Int.repr 12))))
                                      (Evar __x4))
                                    (Sseq
                                      (Sstore Mint32
                                        (Ebinop Oadd (Evar __x13)
                                          (Econst (Ointconst (Int.repr 16))))
                                        (Evar __x6))
                                      (Sseq
                                        (Sstore Mint32
                                          (Ebinop Oadd (Evar __x13)
                                            (Econst (Ointconst (Int.repr 20))))
                                          (Evar __x8))
                                        (Sseq
                                          (Sstore Mint32
                                            (Ebinop Oadd (Evar __x13)
                                              (Econst (Ointconst (Int.repr 24))))
                                            (Evar __x10))
                                          (Sstore Mint32
                                            (Ebinop Oadd (Evar __x13)
                                              (Econst (Ointconst (Int.repr 28))))
                                            (Evar __x12))))))))))))))))))))))
  (Sreturn (Some (Evar __x13))))
|}.

Definition f_fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda8 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x11 :: __x10 :: __x9 :: __x8 :: __x7 :: __x6 :: __x5 ::
              __x4 :: __x3 :: __x2 :: __x1 :: __x0 :: nil);
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
                  (Sassign __x7 (Evar __self))
                  (Sseq
                    (Sassign __x8
                      (Eload Mint32
                        (Ebinop Oadd (Evar __x7)
                          (Econst (Ointconst (Int.repr 16))))))
                    (Sseq
                      (Sassign __x9 (Evar __self))
                      (Sseq
                        (Sassign __x10
                          (Eload Mint32
                            (Ebinop Oadd (Evar __x9)
                              (Econst (Ointconst (Int.repr 20))))))
                        (Sseq
                          (Sseq
                            (Scall (Some __x11)
                              (mksignature (AST.Tint :: nil) (Some AST.Tint)
                                cc_default)
                              (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                              ((Econst (Ointconst (Int.repr 28))) :: nil))
                            (Sstore Mint32 (Evar __x11)
                              (Econst (Oaddrsymbol _fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda8_lambda9 (Int.repr 0)))))
                          (Sseq
                            (Sstore Mint32
                              (Ebinop Oadd (Evar __x11)
                                (Econst (Ointconst (Int.repr 4))))
                              (Evar __x0))
                            (Sseq
                              (Sstore Mint32
                                (Ebinop Oadd (Evar __x11)
                                  (Econst (Ointconst (Int.repr 8))))
                                (Evar __x2))
                              (Sseq
                                (Sstore Mint32
                                  (Ebinop Oadd (Evar __x11)
                                    (Econst (Ointconst (Int.repr 12))))
                                  (Evar __x4))
                                (Sseq
                                  (Sstore Mint32
                                    (Ebinop Oadd (Evar __x11)
                                      (Econst (Ointconst (Int.repr 16))))
                                    (Evar __x6))
                                  (Sseq
                                    (Sstore Mint32
                                      (Ebinop Oadd (Evar __x11)
                                        (Econst (Ointconst (Int.repr 20))))
                                      (Evar __x8))
                                    (Sstore Mint32
                                      (Ebinop Oadd (Evar __x11)
                                        (Econst (Ointconst (Int.repr 24))))
                                      (Evar __x10)))))))))))))))))))
  (Sreturn (Some (Evar __x11))))
|}.

Definition f_fib_lambda0_lambda3_lambda4_lambda5_lambda6 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x19 :: __x18 :: __x17 :: __x16 :: __x15 :: __x14 :: __x13 ::
              __x12 :: __x11 :: __x10 :: __x9 :: __x8 :: __x7 :: __x6 ::
              __x5 :: __x4 :: __x3 :: __x2 :: __x1 :: __x0 :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Sassign __x0 (Evar __self))
    (Sseq
      (Sassign __x1
        (Eload Mint32
          (Ebinop Oadd (Evar __x0) (Econst (Ointconst (Int.repr 8))))))
      (Sseq
        (Sassign __x2 (Evar __arg))
        (Sseq
          (Scall (Some __x3)
            (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default) (Eload Mint32 (Evar __x1))
            ((Evar __x1) :: (Evar __x2) :: nil))
          (Sseq
            (Sassign __x4 (Evar __arg))
            (Sseq
              (Sassign __x5 (Evar __self))
              (Sseq
                (Sassign __x6
                  (Eload Mint32
                    (Ebinop Oadd (Evar __x5)
                      (Econst (Ointconst (Int.repr 4))))))
                (Sseq
                  (Sassign __x7 (Evar __self))
                  (Sseq
                    (Sassign __x8
                      (Eload Mint32
                        (Ebinop Oadd (Evar __x7)
                          (Econst (Ointconst (Int.repr 8))))))
                    (Sseq
                      (Sassign __x9 (Evar __self))
                      (Sseq
                        (Sassign __x10
                          (Eload Mint32
                            (Ebinop Oadd (Evar __x9)
                              (Econst (Ointconst (Int.repr 12))))))
                        (Sseq
                          (Sassign __x11 (Evar __self))
                          (Sseq
                            (Sassign __x12
                              (Eload Mint32
                                (Ebinop Oadd (Evar __x11)
                                  (Econst (Ointconst (Int.repr 16))))))
                            (Sseq
                              (Sseq
                                (Sseq
                                  (Scall (Some __x13)
                                    (mksignature (AST.Tint :: nil)
                                      (Some AST.Tint) cc_default)
                                    (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                                    ((Econst (Ointconst (Int.repr 24))) ::
                                     nil))
                                  (Sstore Mint32 (Evar __x13)
                                    (Econst (Oaddrsymbol _fib_lambda0_lambda3_lambda4_lambda5_lambda6_elim0 (Int.repr 0)))))
                                (Sseq
                                  (Sstore Mint32
                                    (Ebinop Oadd (Evar __x13)
                                      (Econst (Ointconst (Int.repr 4))))
                                    (Evar __x4))
                                  (Sseq
                                    (Sstore Mint32
                                      (Ebinop Oadd (Evar __x13)
                                        (Econst (Ointconst (Int.repr 8))))
                                      (Evar __x6))
                                    (Sseq
                                      (Sstore Mint32
                                        (Ebinop Oadd (Evar __x13)
                                          (Econst (Ointconst (Int.repr 12))))
                                        (Evar __x8))
                                      (Sseq
                                        (Sstore Mint32
                                          (Ebinop Oadd (Evar __x13)
                                            (Econst (Ointconst (Int.repr 16))))
                                          (Evar __x10))
                                        (Sstore Mint32
                                          (Ebinop Oadd (Evar __x13)
                                            (Econst (Ointconst (Int.repr 20))))
                                          (Evar __x12)))))))
                              (Sseq
                                (Sassign __x14 (Evar __self))
                                (Sseq
                                  (Sassign __x15
                                    (Eload Mint32
                                      (Ebinop Oadd (Evar __x14)
                                        (Econst (Ointconst (Int.repr 4))))))
                                  (Sseq
                                    (Scall (Some __x16)
                                      (mksignature
                                        (AST.Tint :: AST.Tint :: nil)
                                        (Some AST.Tint) cc_default)
                                      (Eload Mint32 (Evar __x13))
                                      ((Evar __x13) :: (Evar __x15) :: nil))
                                    (Sseq
                                      (Sassign __x17 (Evar __arg))
                                      (Sseq
                                        (Scall (Some __x18)
                                          (mksignature
                                            (AST.Tint :: AST.Tint :: nil)
                                            (Some AST.Tint) cc_default)
                                          (Eload Mint32 (Evar __x16))
                                          ((Evar __x16) :: (Evar __x17) ::
                                           nil))
                                        (Scall (Some __x19)
                                          (mksignature
                                            (AST.Tint :: AST.Tint :: nil)
                                            (Some AST.Tint) cc_default)
                                          (Eload Mint32 (Evar __x3))
                                          ((Evar __x3) :: (Evar __x18) ::
                                           nil)))))))))))))))))))))
  (Sreturn (Some (Evar __x19))))
|}.

Definition f_fib_lambda0_lambda3_lambda4_lambda5 := {|
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
                      (Econst (Oaddrsymbol _fib_lambda0_lambda3_lambda4_lambda5_lambda6 (Int.repr 0)))))
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

Definition f_fib_lambda0_lambda3_lambda4 := {|
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
                  (Econst (Oaddrsymbol _fib_lambda0_lambda3_lambda4_lambda5 (Int.repr 0)))))
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

Definition f_fib_lambda0_lambda3 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x3 :: __x2 :: __x1 :: __x0 :: nil);
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
            (Scall (Some __x3)
              (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
              (Econst (Oaddrsymbol _malloc (Int.repr 0)))
              ((Econst (Ointconst (Int.repr 12))) :: nil))
            (Sstore Mint32 (Evar __x3)
              (Econst (Oaddrsymbol _fib_lambda0_lambda3_lambda4 (Int.repr 0)))))
          (Sseq
            (Sstore Mint32
              (Ebinop Oadd (Evar __x3) (Econst (Ointconst (Int.repr 4))))
              (Evar __x0))
            (Sstore Mint32
              (Ebinop Oadd (Evar __x3) (Econst (Ointconst (Int.repr 8))))
              (Evar __x2)))))))
  (Sreturn (Some (Evar __x3))))
|}.

Definition f_fib_lambda0 := {|
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
      (Sseq
        (Sseq
          (Scall (Some __x1)
            (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
            (Econst (Oaddrsymbol _malloc (Int.repr 0)))
            ((Econst (Ointconst (Int.repr 8))) :: nil))
          (Sstore Mint32 (Evar __x1)
            (Econst (Oaddrsymbol _fib_lambda0_elim1 (Int.repr 0)))))
        (Sstore Mint32
          (Ebinop Oadd (Evar __x1) (Econst (Ointconst (Int.repr 4))))
          (Evar __x0)))
      (Sseq
        (Sassign __x2 (Evar __arg))
        (Sseq
          (Scall (Some __x3)
            (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default) (Eload Mint32 (Evar __x1))
            ((Evar __x1) :: (Evar __x2) :: nil))
          (Sseq
            (Sseq
              (Scall (Some __x4)
                (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
                (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                ((Econst (Ointconst (Int.repr 4))) :: nil))
              (Sstore Mint32 (Evar __x4) (Econst (Ointconst (Int.repr 0)))))
            (Sseq
              (Scall (Some __x5)
                (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                  cc_default) (Eload Mint32 (Evar __x3))
                ((Evar __x3) :: (Evar __x4) :: nil))
              (Sseq
                (Sseq
                  (Scall (Some __x6)
                    (mksignature (AST.Tint :: nil) (Some AST.Tint)
                      cc_default) (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                    ((Econst (Ointconst (Int.repr 4))) :: nil))
                  (Sstore Mint32 (Evar __x6)
                    (Econst (Ointconst (Int.repr 0)))))
                (Sseq
                  (Sseq
                    (Sseq
                      (Scall (Some __x7)
                        (mksignature (AST.Tint :: nil) (Some AST.Tint)
                          cc_default)
                        (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                        ((Econst (Ointconst (Int.repr 8))) :: nil))
                      (Sstore Mint32 (Evar __x7)
                        (Econst (Ointconst (Int.repr 1)))))
                    (Sstore Mint32
                      (Ebinop Oadd (Evar __x7)
                        (Econst (Ointconst (Int.repr 4)))) (Evar __x6)))
                  (Scall (Some __x8)
                    (mksignature (AST.Tint :: AST.Tint :: nil)
                      (Some AST.Tint) cc_default) (Eload Mint32 (Evar __x5))
                    ((Evar __x5) :: (Evar __x7) :: nil))))))))))
  (Sreturn (Some (Evar __x8))))
|}.

Definition f_fib_lambda0_lambda3_lambda4_lambda5_lambda6_elim0 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x11 :: __x10 :: __x9 :: __x8 :: __x7 :: __x6 :: __x5 ::
              __x4 :: __x3 :: __x2 :: __x1 :: __x0 :: __x40 :: __x39 ::
              __x38 :: __x37 :: __x36 :: __x35 :: __x34 :: __x33 :: __x32 ::
              __x31 :: __x30 :: __x29 :: __x28 :: __x27 :: __x26 :: __x25 ::
              __x24 :: __x23 :: __x22 :: __x21 :: __x20 :: __x19 :: __x18 ::
              __x17 :: __x16 :: __x15 :: __x14 :: __x13 :: __x12 ::
              __switch_target :: nil);
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
              (Sassign __x12 (Evar __self))
              (Sseq
                (Sassign __x13
                  (Eload Mint32
                    (Ebinop Oadd (Evar __x12)
                      (Econst (Ointconst (Int.repr 4))))))
                (Sseq
                  (Sassign __x14 (Evar __self))
                  (Sseq
                    (Sassign __x15
                      (Eload Mint32
                        (Ebinop Oadd (Evar __x14)
                          (Econst (Ointconst (Int.repr 8))))))
                    (Sseq
                      (Sassign __x16 (Evar __self))
                      (Sseq
                        (Sassign __x17
                          (Eload Mint32
                            (Ebinop Oadd (Evar __x16)
                              (Econst (Ointconst (Int.repr 12))))))
                        (Sseq
                          (Sassign __x18 (Evar __self))
                          (Sseq
                            (Sassign __x19
                              (Eload Mint32
                                (Ebinop Oadd (Evar __x18)
                                  (Econst (Ointconst (Int.repr 16))))))
                            (Sseq
                              (Sassign __x20 (Evar __self))
                              (Sseq
                                (Sassign __x21
                                  (Eload Mint32
                                    (Ebinop Oadd (Evar __x20)
                                      (Econst (Ointconst (Int.repr 20))))))
                                (Sseq
                                  (Sseq
                                    (Sseq
                                      (Scall (Some __x22)
                                        (mksignature (AST.Tint :: nil)
                                          (Some AST.Tint) cc_default)
                                        (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                                        ((Econst (Ointconst (Int.repr 24))) ::
                                         nil))
                                      (Sstore Mint32 (Evar __x22)
                                        (Econst (Oaddrsymbol _fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda8 (Int.repr 0)))))
                                    (Sseq
                                      (Sstore Mint32
                                        (Ebinop Oadd (Evar __x22)
                                          (Econst (Ointconst (Int.repr 4))))
                                        (Evar __x13))
                                      (Sseq
                                        (Sstore Mint32
                                          (Ebinop Oadd (Evar __x22)
                                            (Econst (Ointconst (Int.repr 8))))
                                          (Evar __x15))
                                        (Sseq
                                          (Sstore Mint32
                                            (Ebinop Oadd (Evar __x22)
                                              (Econst (Ointconst (Int.repr 12))))
                                            (Evar __x17))
                                          (Sseq
                                            (Sstore Mint32
                                              (Ebinop Oadd (Evar __x22)
                                                (Econst (Ointconst (Int.repr 16))))
                                              (Evar __x19))
                                            (Sstore Mint32
                                              (Ebinop Oadd (Evar __x22)
                                                (Econst (Ointconst (Int.repr 20))))
                                              (Evar __x21)))))))
                                  (Sseq
                                    (Sassign __x23 (Evar __arg))
                                    (Sseq
                                      (Sassign __x24
                                        (Eload Mint32
                                          (Ebinop Oadd (Evar __x23)
                                            (Econst (Ointconst (Int.repr 4))))))
                                      (Sseq
                                        (Scall (Some __x25)
                                          (mksignature
                                            (AST.Tint :: AST.Tint :: nil)
                                            (Some AST.Tint) cc_default)
                                          (Eload Mint32 (Evar __x22))
                                          ((Evar __x22) :: (Evar __x24) ::
                                           nil))
                                        (Sseq
                                          (Sassign __x26 (Evar __self))
                                          (Sseq
                                            (Sassign __x27
                                              (Eload Mint32
                                                (Ebinop Oadd (Evar __x26)
                                                  (Econst (Ointconst (Int.repr 4))))))
                                            (Sseq
                                              (Sassign __x28 (Evar __self))
                                              (Sseq
                                                (Sassign __x29
                                                  (Eload Mint32
                                                    (Ebinop Oadd (Evar __x28)
                                                      (Econst (Ointconst (Int.repr 8))))))
                                                (Sseq
                                                  (Sassign __x30
                                                    (Evar __self))
                                                  (Sseq
                                                    (Sassign __x31
                                                      (Eload Mint32
                                                        (Ebinop Oadd
                                                          (Evar __x30)
                                                          (Econst (Ointconst (Int.repr 12))))))
                                                    (Sseq
                                                      (Sassign __x32
                                                        (Evar __self))
                                                      (Sseq
                                                        (Sassign __x33
                                                          (Eload Mint32
                                                            (Ebinop Oadd
                                                              (Evar __x32)
                                                              (Econst (Ointconst (Int.repr 16))))))
                                                        (Sseq
                                                          (Sassign __x34
                                                            (Evar __self))
                                                          (Sseq
                                                            (Sassign __x35
                                                              (Eload Mint32
                                                                (Ebinop Oadd
                                                                  (Evar __x34)
                                                                  (Econst (Ointconst (Int.repr 20))))))
                                                            (Sseq
                                                              (Sseq
                                                                (Sseq
                                                                  (Scall (Some __x36)
                                                                    (mksignature
                                                                    (AST.Tint ::
                                                                    nil)
                                                                    (Some AST.Tint)
                                                                    cc_default)
                                                                    (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                                                                    ((Econst (Ointconst (Int.repr 24))) ::
                                                                    nil))
                                                                  (Sstore
                                                                    Mint32
                                                                    (Evar __x36)
                                                                    (Econst (Oaddrsymbol _fib_lambda0_lambda3_lambda4_lambda5_lambda6_elim0 (Int.repr 0)))))
                                                                (Sseq
                                                                  (Sstore
                                                                    Mint32
                                                                    (Ebinop Oadd
                                                                    (Evar __x36)
                                                                    (Econst (Ointconst (Int.repr 4))))
                                                                    (Evar __x27))
                                                                  (Sseq
                                                                    (Sstore
                                                                    Mint32
                                                                    (Ebinop Oadd
                                                                    (Evar __x36)
                                                                    (Econst (Ointconst (Int.repr 8))))
                                                                    (Evar __x29))
                                                                    (Sseq
                                                                    (Sstore
                                                                    Mint32
                                                                    (Ebinop Oadd
                                                                    (Evar __x36)
                                                                    (Econst (Ointconst (Int.repr 12))))
                                                                    (Evar __x31))
                                                                    (Sseq
                                                                    (Sstore
                                                                    Mint32
                                                                    (Ebinop Oadd
                                                                    (Evar __x36)
                                                                    (Econst (Ointconst (Int.repr 16))))
                                                                    (Evar __x33))
                                                                    (Sstore
                                                                    Mint32
                                                                    (Ebinop Oadd
                                                                    (Evar __x36)
                                                                    (Econst (Ointconst (Int.repr 20))))
                                                                    (Evar __x35)))))))
                                                              (Sseq
                                                                (Sassign
                                                                  __x37
                                                                  (Evar __arg))
                                                                (Sseq
                                                                  (Sassign
                                                                    __x38
                                                                    (Eload Mint32
                                                                    (Ebinop Oadd
                                                                    (Evar __x37)
                                                                    (Econst (Ointconst (Int.repr 4))))))
                                                                  (Sseq
                                                                    (Scall (Some __x39)
                                                                    (mksignature
                                                                    (AST.Tint ::
                                                                    AST.Tint ::
                                                                    nil)
                                                                    (Some AST.Tint)
                                                                    cc_default)
                                                                    (Eload Mint32
                                                                    (Evar __x36))
                                                                    ((Evar __x36) ::
                                                                    (Evar __x38) ::
                                                                    nil))
                                                                    (Sseq
                                                                    (Scall (Some __x40)
                                                                    (mksignature
                                                                    (AST.Tint ::
                                                                    AST.Tint ::
                                                                    nil)
                                                                    (Some AST.Tint)
                                                                    cc_default)
                                                                    (Eload Mint32
                                                                    (Evar __x25))
                                                                    ((Evar __x25) ::
                                                                    (Evar __x39) ::
                                                                    nil))
                                                                    (Sassign
                                                                    __x0
                                                                    (Evar __x40)))))))))))))))))))))))))))))))
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
                  (Sassign __x5 (Evar __self))
                  (Sseq
                    (Sassign __x6
                      (Eload Mint32
                        (Ebinop Oadd (Evar __x5)
                          (Econst (Ointconst (Int.repr 12))))))
                    (Sseq
                      (Sassign __x7 (Evar __self))
                      (Sseq
                        (Sassign __x8
                          (Eload Mint32
                            (Ebinop Oadd (Evar __x7)
                              (Econst (Ointconst (Int.repr 16))))))
                        (Sseq
                          (Sassign __x9 (Evar __self))
                          (Sseq
                            (Sassign __x10
                              (Eload Mint32
                                (Ebinop Oadd (Evar __x9)
                                  (Econst (Ointconst (Int.repr 20))))))
                            (Sseq
                              (Sseq
                                (Sseq
                                  (Scall (Some __x11)
                                    (mksignature (AST.Tint :: nil)
                                      (Some AST.Tint) cc_default)
                                    (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                                    ((Econst (Ointconst (Int.repr 24))) ::
                                     nil))
                                  (Sstore Mint32 (Evar __x11)
                                    (Econst (Oaddrsymbol _fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda7 (Int.repr 0)))))
                                (Sseq
                                  (Sstore Mint32
                                    (Ebinop Oadd (Evar __x11)
                                      (Econst (Ointconst (Int.repr 4))))
                                    (Evar __x2))
                                  (Sseq
                                    (Sstore Mint32
                                      (Ebinop Oadd (Evar __x11)
                                        (Econst (Ointconst (Int.repr 8))))
                                      (Evar __x4))
                                    (Sseq
                                      (Sstore Mint32
                                        (Ebinop Oadd (Evar __x11)
                                          (Econst (Ointconst (Int.repr 12))))
                                        (Evar __x6))
                                      (Sseq
                                        (Sstore Mint32
                                          (Ebinop Oadd (Evar __x11)
                                            (Econst (Ointconst (Int.repr 16))))
                                          (Evar __x8))
                                        (Sstore Mint32
                                          (Ebinop Oadd (Evar __x11)
                                            (Econst (Ointconst (Int.repr 20))))
                                          (Evar __x10)))))))
                              (Sassign __x0 (Evar __x11)))))))))))))
        (Sexit O))))
  (Sreturn (Some (Evar __x0))))
|}.

Definition f_fib_lambda0_elim1 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x3 :: __x2 :: __x1 :: __x0 :: __x16 :: __x15 :: __x14 ::
              __x13 :: __x12 :: __x11 :: __x10 :: __x9 :: __x8 :: __x7 ::
              __x6 :: __x5 :: __x4 :: __switch_target :: nil);
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
              (Sassign __x4 (Evar __self))
              (Sseq
                (Sassign __x5
                  (Eload Mint32
                    (Ebinop Oadd (Evar __x4)
                      (Econst (Ointconst (Int.repr 4))))))
                (Sseq
                  (Sseq
                    (Sseq
                      (Scall (Some __x6)
                        (mksignature (AST.Tint :: nil) (Some AST.Tint)
                          cc_default)
                        (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                        ((Econst (Ointconst (Int.repr 8))) :: nil))
                      (Sstore Mint32 (Evar __x6)
                        (Econst (Oaddrsymbol _fib_lambda0_lambda3 (Int.repr 0)))))
                    (Sstore Mint32
                      (Ebinop Oadd (Evar __x6)
                        (Econst (Ointconst (Int.repr 4)))) (Evar __x5)))
                  (Sseq
                    (Sassign __x7 (Evar __arg))
                    (Sseq
                      (Sassign __x8
                        (Eload Mint32
                          (Ebinop Oadd (Evar __x7)
                            (Econst (Ointconst (Int.repr 4))))))
                      (Sseq
                        (Scall (Some __x9)
                          (mksignature (AST.Tint :: AST.Tint :: nil)
                            (Some AST.Tint) cc_default)
                          (Eload Mint32 (Evar __x6))
                          ((Evar __x6) :: (Evar __x8) :: nil))
                        (Sseq
                          (Sassign __x10 (Evar __self))
                          (Sseq
                            (Sassign __x11
                              (Eload Mint32
                                (Ebinop Oadd (Evar __x10)
                                  (Econst (Ointconst (Int.repr 4))))))
                            (Sseq
                              (Sseq
                                (Sseq
                                  (Scall (Some __x12)
                                    (mksignature (AST.Tint :: nil)
                                      (Some AST.Tint) cc_default)
                                    (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                                    ((Econst (Ointconst (Int.repr 8))) ::
                                     nil))
                                  (Sstore Mint32 (Evar __x12)
                                    (Econst (Oaddrsymbol _fib_lambda0_elim1 (Int.repr 0)))))
                                (Sstore Mint32
                                  (Ebinop Oadd (Evar __x12)
                                    (Econst (Ointconst (Int.repr 4))))
                                  (Evar __x11)))
                              (Sseq
                                (Sassign __x13 (Evar __arg))
                                (Sseq
                                  (Sassign __x14
                                    (Eload Mint32
                                      (Ebinop Oadd (Evar __x13)
                                        (Econst (Ointconst (Int.repr 4))))))
                                  (Sseq
                                    (Scall (Some __x15)
                                      (mksignature
                                        (AST.Tint :: AST.Tint :: nil)
                                        (Some AST.Tint) cc_default)
                                      (Eload Mint32 (Evar __x12))
                                      ((Evar __x12) :: (Evar __x14) :: nil))
                                    (Sseq
                                      (Scall (Some __x16)
                                        (mksignature
                                          (AST.Tint :: AST.Tint :: nil)
                                          (Some AST.Tint) cc_default)
                                        (Eload Mint32 (Evar __x9))
                                        ((Evar __x9) :: (Evar __x15) :: nil))
                                      (Sassign __x0 (Evar __x16)))))))))))))))
            (Sexit (S O)))))
      (Sseq
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
                    (mksignature (AST.Tint :: nil) (Some AST.Tint)
                      cc_default) (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                    ((Econst (Ointconst (Int.repr 8))) :: nil))
                  (Sstore Mint32 (Evar __x3)
                    (Econst (Oaddrsymbol _fib_lambda0_lambda1 (Int.repr 0)))))
                (Sstore Mint32
                  (Ebinop Oadd (Evar __x3) (Econst (Ointconst (Int.repr 4))))
                  (Evar __x2)))
              (Sassign __x0 (Evar __x3)))))
        (Sexit O))))
  (Sreturn (Some (Evar __x0))))
|}.

Definition prog : Cminor.program := {|
prog_defs :=
((_fib, Gfun(Internal f_fib)) ::
 (_fib_lambda0_lambda1_lambda2, Gfun(Internal f_fib_lambda0_lambda1_lambda2)) ::
 (_fib_lambda0_lambda1, Gfun(Internal f_fib_lambda0_lambda1)) ::
 (_fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda7, Gfun(Internal f_fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda7)) ::
 (_fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda8_lambda9_lambda10, Gfun(Internal f_fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda8_lambda9_lambda10)) ::
 (_fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda8_lambda9, Gfun(Internal f_fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda8_lambda9)) ::
 (_fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda8, Gfun(Internal f_fib_lambda0_lambda3_lambda4_lambda5_lambda6_lambda8)) ::
 (_fib_lambda0_lambda3_lambda4_lambda5_lambda6, Gfun(Internal f_fib_lambda0_lambda3_lambda4_lambda5_lambda6)) ::
 (_fib_lambda0_lambda3_lambda4_lambda5, Gfun(Internal f_fib_lambda0_lambda3_lambda4_lambda5)) ::
 (_fib_lambda0_lambda3_lambda4, Gfun(Internal f_fib_lambda0_lambda3_lambda4)) ::
 (_fib_lambda0_lambda3, Gfun(Internal f_fib_lambda0_lambda3)) ::
 (_fib_lambda0, Gfun(Internal f_fib_lambda0)) ::
 (_fib_lambda0_lambda3_lambda4_lambda5_lambda6_elim0, Gfun(Internal f_fib_lambda0_lambda3_lambda4_lambda5_lambda6_elim0)) ::
 (_fib_lambda0_elim1, Gfun(Internal f_fib_lambda0_elim1)) ::
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
 (_malloc, Gfun(External EF_malloc)) :: nil);
prog_public :=
(_fib :: nil);
prog_main := _tm_sec;
|}.

