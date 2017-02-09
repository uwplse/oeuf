Require Import compcert.backend.Cminor.
Require Import compcert.common.AST.
Require Import BinNums.
Require Import compcert.lib.Integers.
Require Import List.
Import ListNotations.

Local Open Scope Z_scope.

Definition _t : ident := 85%positive.
Definition _main : ident := 110%positive.
Definition __switch_target : ident := 130%positive.
Definition _long_id_lambda0_elim0 : ident := 111%positive.
Definition __682 : ident := 22%positive.
Definition _tm : ident := 12%positive.
Definition __x1 : ident := 128%positive.
Definition _m : ident := 108%positive.
Definition ___builtin_ctz : ident := 63%positive.
Definition ___tm_gmtoff : ident := 10%positive.
Definition ___i64_dtos : ident := 44%positive.
Definition _tm_hour : ident := 3%positive.
Definition _tm_sec : ident := 1%positive.
Definition __x5 : ident := 124%positive.
Definition _get_time : ident := 88%positive.
Definition __x10 : ident := 119%positive.
Definition _printf : ident := 79%positive.
Definition ___builtin_fnmsub : ident := 72%positive.
Definition ___stringlit_3 : ident := 109%positive.
Definition ___builtin_debug : ident := 78%positive.
Definition ___builtin_fmin : ident := 68%positive.
Definition _cons : ident := 28%positive.
Definition _long_id_lambda0_lambda1 : ident := 113%positive.
Definition _a : ident := 102%positive.
Definition _tm_wday : ident := 7%positive.
Definition _call : ident := 103%positive.
Definition _print_list_nat : ident := 101%positive.
Definition _ptr : ident := 89%positive.
Definition ___i64_dtou : ident := 45%positive.
Definition _nil : ident := 27%positive.
Definition _time_buf : ident := 84%positive.
Definition _time : ident := 82%positive.
Definition _next : ident := 25%positive.
Definition _nat : ident := 15%positive.
Definition ___builtin_clz : ident := 60%positive.
Definition __x0 : ident := 129%positive.
Definition _long_id_lambda0_lambda1_lambda2 : ident := 114%positive.
Definition ___builtin_memcpy_aligned : ident := 32%positive.
Definition __x12 : ident := 117%positive.
Definition ___builtin_fmsub : ident := 70%positive.
Definition _b : ident := 96%positive.
Definition __658 : ident := 17%positive.
Definition _tm_yday : ident := 8%positive.
Definition __x2 : ident := 127%positive.
Definition ___compcert_va_composite : ident := 43%positive.
Definition ___i64_umod : ident := 53%positive.
Definition ___i64_utod : ident := 47%positive.
Definition _tmp : ident := 91%positive.
Definition ___builtin_va_start : ident := 36%positive.
Definition _read_bool : ident := 98%positive.
Definition _S : ident := 19%positive.
Definition ___builtin_clzl : ident := 61%positive.
Definition _make_bool : ident := 97%positive.
Definition __x7 : ident := 122%positive.
Definition ___builtin_va_arg : ident := 37%positive.
Definition ___compcert_va_float64 : ident := 42%positive.
Definition __arg : ident := 132%positive.
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
Definition _long_id_lambda0 : ident := 112%positive.
Definition _n : ident := 16%positive.
Definition ___builtin_va_copy : ident := 38%positive.
Definition ___i64_stod : ident := 46%positive.
Definition ___builtin_fmadd : ident := 69%positive.
Definition ___builtin_clzll : ident := 62%positive.
Definition ___i64_shl : ident := 54%positive.
Definition _make_nat : ident := 92%positive.
Definition _ap : ident := 104%positive.
Definition _tm_min : ident := 2%positive.
Definition __x8 : ident := 121%positive.
Definition ___builtin_fabs : ident := 31%positive.
Definition ___i64_utof : ident := 49%positive.
Definition ___builtin_fsqrt : ident := 66%positive.
Definition ___builtin_bswap16 : ident := 59%positive.
Definition _tm_mday : ident := 4%positive.
Definition _result : ident := 94%positive.
Definition ___builtin_bswap32 : ident := 58%positive.
Definition __x4 : ident := 125%positive.
Definition _l : ident := 99%positive.
Definition _bool : ident := 21%positive.
Definition _O : ident := 18%positive.
Definition _long_id : ident := 106%positive.
Definition _snprintf : ident := 80%positive.
Definition _tag : ident := 13%positive.
Definition ___builtin_annot : ident := 33%positive.
Definition __x6 : ident := 123%positive.
Definition ___i64_sar : ident := 56%positive.
Definition __x14 : ident := 115%positive.
Definition ___stringlit_2 : ident := 100%positive.
Definition _unit : ident := 20%positive.
Definition _read_nat : ident := 93%positive.
Definition _vcall : ident := 105%positive.
Definition __x3 : ident := 126%positive.
Definition _list : ident := 24%positive.
Definition ___builtin_fmax : ident := 67%positive.
Definition _tm_mon : ident := 5%positive.
Definition ___builtin_read16_reversed : ident := 73%positive.
Definition ___i64_sdiv : ident := 50%positive.
Definition ___builtin_read32_reversed : ident := 74%positive.
Definition _long_id_closure : ident := 107%positive.
Definition ___builtin_bswap : ident := 57%positive.
Definition __657 : ident := 14%positive.
Definition _tm_year : ident := 6%positive.
Definition __x11 : ident := 118%positive.
Definition __683 : ident := 26%positive.
Definition ___builtin_va_end : ident := 39%positive.
Definition _i : ident := 90%positive.
Definition _localtime : ident := 83%positive.
Definition ___tm_zone : ident := 11%positive.
Definition __x13 : ident := 116%positive.
Definition _malloc : ident := 81%positive.
Definition ___builtin_write32_reversed : ident := 76%positive.
Definition _tm__1 : ident := 86%positive.
Definition _tm_isdst : ident := 9%positive.
Definition __self : ident := 131%positive.
Definition ___builtin_ctzl : ident := 64%positive.
Definition ___i64_smod : ident := 52%positive.
Definition ___compcert_va_int64 : ident := 41%positive.
Definition ___stringlit_1 : ident := 87%positive.
Definition ___builtin_nop : ident := 77%positive.
Definition __x9 : ident := 120%positive.
Definition ___builtin_membar : ident := 35%positive.
Definition _closure : ident := 30%positive.
Definition _data : ident := 23%positive.

Definition f_long_id := {|
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
      (Econst (Oaddrsymbol _long_id_lambda0 (Int.repr 0)))))
  (Sreturn (Some (Evar __x0))))
|}.

Definition f_long_id_lambda0_lambda1_lambda2 := {|
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
        (Sstore Mint32 (Evar __x1) (Econst (Ointconst (Int.repr 1)))))
      (Sstore Mint32
        (Ebinop Oadd (Evar __x1) (Econst (Ointconst (Int.repr 4))))
        (Evar __x0))))
  (Sreturn (Some (Evar __x1))))
|}.

Definition f_long_id_lambda0_lambda1 := {|
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
              (Econst (Oaddrsymbol _long_id_lambda0_lambda1_lambda2 (Int.repr 0)))))
          (Sseq
            (Sstore Mint32
              (Ebinop Oadd (Evar __x3) (Econst (Ointconst (Int.repr 4))))
              (Evar __x0))
            (Sstore Mint32
              (Ebinop Oadd (Evar __x3) (Econst (Ointconst (Int.repr 8))))
              (Evar __x2)))))))
  (Sreturn (Some (Evar __x3))))
|}.

Definition f_long_id_lambda0 := {|
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
      (Sseq
        (Sseq
          (Scall (Some __x1)
            (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
            (Econst (Oaddrsymbol _malloc (Int.repr 0)))
            ((Econst (Ointconst (Int.repr 8))) :: nil))
          (Sstore Mint32 (Evar __x1)
            (Econst (Oaddrsymbol _long_id_lambda0_elim0 (Int.repr 0)))))
        (Sstore Mint32
          (Ebinop Oadd (Evar __x1) (Econst (Ointconst (Int.repr 4))))
          (Evar __x0)))
      (Sseq
        (Sassign __x2 (Evar __arg))
        (Scall (Some __x3)
          (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
            cc_default) (Eload Mint32 (Evar __x1))
          ((Evar __x1) :: (Evar __x2) :: nil)))))
  (Sreturn (Some (Evar __x3))))
|}.

Definition f_long_id_lambda0_elim0 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x1 :: __x0 :: __x14 :: __x13 :: __x12 :: __x11 :: __x10 ::
              __x9 :: __x8 :: __x7 :: __x6 :: __x5 :: __x4 :: __x3 :: __x2 ::
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
              (Sassign __x2 (Evar __self))
              (Sseq
                (Sassign __x3
                  (Eload Mint32
                    (Ebinop Oadd (Evar __x2)
                      (Econst (Ointconst (Int.repr 4))))))
                (Sseq
                  (Sseq
                    (Sseq
                      (Scall (Some __x4)
                        (mksignature (AST.Tint :: nil) (Some AST.Tint)
                          cc_default)
                        (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                        ((Econst (Ointconst (Int.repr 8))) :: nil))
                      (Sstore Mint32 (Evar __x4)
                        (Econst (Oaddrsymbol _long_id_lambda0_lambda1 (Int.repr 0)))))
                    (Sstore Mint32
                      (Ebinop Oadd (Evar __x4)
                        (Econst (Ointconst (Int.repr 4)))) (Evar __x3)))
                  (Sseq
                    (Sassign __x5 (Evar __arg))
                    (Sseq
                      (Sassign __x6
                        (Eload Mint32
                          (Ebinop Oadd (Evar __x5)
                            (Econst (Ointconst (Int.repr 4))))))
                      (Sseq
                        (Scall (Some __x7)
                          (mksignature (AST.Tint :: AST.Tint :: nil)
                            (Some AST.Tint) cc_default)
                          (Eload Mint32 (Evar __x4))
                          ((Evar __x4) :: (Evar __x6) :: nil))
                        (Sseq
                          (Sassign __x8 (Evar __self))
                          (Sseq
                            (Sassign __x9
                              (Eload Mint32
                                (Ebinop Oadd (Evar __x8)
                                  (Econst (Ointconst (Int.repr 4))))))
                            (Sseq
                              (Sseq
                                (Sseq
                                  (Scall (Some __x10)
                                    (mksignature (AST.Tint :: nil)
                                      (Some AST.Tint) cc_default)
                                    (Econst (Oaddrsymbol _malloc (Int.repr 0)))
                                    ((Econst (Ointconst (Int.repr 8))) ::
                                     nil))
                                  (Sstore Mint32 (Evar __x10)
                                    (Econst (Oaddrsymbol _long_id_lambda0_elim0 (Int.repr 0)))))
                                (Sstore Mint32
                                  (Ebinop Oadd (Evar __x10)
                                    (Econst (Ointconst (Int.repr 4))))
                                  (Evar __x9)))
                              (Sseq
                                (Sassign __x11 (Evar __arg))
                                (Sseq
                                  (Sassign __x12
                                    (Eload Mint32
                                      (Ebinop Oadd (Evar __x11)
                                        (Econst (Ointconst (Int.repr 4))))))
                                  (Sseq
                                    (Scall (Some __x13)
                                      (mksignature
                                        (AST.Tint :: AST.Tint :: nil)
                                        (Some AST.Tint) cc_default)
                                      (Eload Mint32 (Evar __x10))
                                      ((Evar __x10) :: (Evar __x12) :: nil))
                                    (Sseq
                                      (Scall (Some __x14)
                                        (mksignature
                                          (AST.Tint :: AST.Tint :: nil)
                                          (Some AST.Tint) cc_default)
                                        (Eload Mint32 (Evar __x7))
                                        ((Evar __x7) :: (Evar __x13) :: nil))
                                      (Sassign __x0 (Evar __x14)))))))))))))))
            (Sexit (S O)))))
      (Sseq
        (Sseq
          (Sseq
            (Scall (Some __x1)
              (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
              (Econst (Oaddrsymbol _malloc (Int.repr 0)))
              ((Econst (Ointconst (Int.repr 4))) :: nil))
            (Sstore Mint32 (Evar __x1) (Econst (Ointconst (Int.repr 0)))))
          (Sassign __x0 (Evar __x1)))
        (Sexit O))))
  (Sreturn (Some (Evar __x0))))
|}.

Definition prog : Cminor.program := {|
prog_defs :=
((_long_id, Gfun(Internal f_long_id)) ::
 (_long_id_lambda0_lambda1_lambda2, Gfun(Internal f_long_id_lambda0_lambda1_lambda2)) ::
 (_long_id_lambda0_lambda1, Gfun(Internal f_long_id_lambda0_lambda1)) ::
 (_long_id_lambda0, Gfun(Internal f_long_id_lambda0)) ::
 (_long_id_lambda0_elim0, Gfun(Internal f_long_id_lambda0_elim0)) ::
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
(_long_id :: nil);
prog_main := _tm_sec;
|}.

