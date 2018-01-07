Require Import compcert.backend.Cminor.
Require Import compcert.common.AST.
Require Import BinNums.
Require Import compcert.lib.Integers.
Require Import List.
Import ListNotations.

Local Open Scope Z_scope.

Definition _make_nil : ident := 136%positive.
Definition ___builtin_clz : ident := 85%positive.
Definition ___stringlit_9 : ident := 154%positive.
Definition _time : ident := 110%positive.
Definition _make_xO : ident := 148%positive.
Definition _f1 : ident := 143%positive.
Definition _clone_list : ident := 138%positive.
Definition _make_unit : ident := 130%positive.
Definition _time_buf : ident := 111%positive.
Definition _unit : ident := 22%positive.
Definition __self : ident := 205%positive.
Definition __x9 : ident := 194%positive.
Definition _make_cons : ident := 137%positive.
Definition _tm : ident := 12%positive.
Definition ___stringlit_3 : ident := 128%positive.
Definition _printf : ident := 108%positive.
Definition ___builtin_va_copy : ident := 63%positive.
Definition _tm_gmtoff : ident := 10%positive.
Definition __arg : ident := 206%positive.
Definition __1358 : ident := 44%positive.
Definition _tm_hour : ident := 3%positive.
Definition _tm_sec : ident := 1%positive.
Definition _nat_of_uint : ident := 124%positive.
Definition ___builtin_ctz : ident := 88%positive.
Definition _tail_p : ident := 119%positive.
Definition ___i64_shl : ident := 79%positive.
Definition ___i64_utod : ident := 72%positive.
Definition _double_nat_elim_0_1 : ident := 187%positive.
Definition _clone_positive : ident := 150%positive.
Definition _localtime : ident := 109%positive.
Definition ___i64_umod : ident := 78%positive.
Definition ___compcert_va_composite : ident := 68%positive.
Definition __1323 : ident := 28%positive.
Definition _make_pair : ident := 142%positive.
Definition _tm__1 : ident := 113%positive.
Definition ___builtin_nop : ident := 102%positive.
Definition _tm_wday : ident := 7%positive.
Definition __x13 : ident := 190%positive.
Definition ___stringlit_16 : ident := 179%positive.
Definition ___stringlit_10 : ident := 157%positive.
Definition ___builtin_debug : ident := 103%positive.
Definition ___stringlit_20 : ident := 183%positive.
Definition _l : ident := 135%positive.
Definition __x5 : ident := 198%positive.
Definition ___stringlit_6 : ident := 141%positive.
Definition ___builtin_write32_reversed : ident := 101%positive.
Definition ___builtin_ctzl : ident := 89%positive.
Definition _xI : ident := 45%positive.
Definition __x11 : ident := 192%positive.
Definition ___stringlit_17 : ident := 180%positive.
Definition _bool_ : ident := 27%positive.
Definition ___builtin_bswap16 : ident := 84%positive.
Definition ___builtin_bswap : ident := 82%positive.
Definition _true_ : ident := 25%positive.
Definition _nat : ident := 15%positive.
Definition ___builtin_membar : ident := 60%positive.
Definition ___stringlit_4 : ident := 129%positive.
Definition ___stringlit_1 : ident := 114%positive.
Definition __1324 : ident := 32%positive.
Definition _m : ident := 117%positive.
Definition ___i64_dtou : ident := 70%positive.
Definition _double_nat_elim : ident := 175%positive.
Definition ___builtin_fnmadd : ident := 96%positive.
Definition __1280 : ident := 17%positive.
Definition _tm_yday : ident := 8%positive.
Definition __switch_target : ident := 204%positive.
Definition _print_nat : ident := 127%positive.
Definition __1357 : ident := 43%positive.
Definition _f : ident := 53%positive.
Definition _xH : ident := 47%positive.
Definition _make_xH : ident := 149%positive.
Definition ___builtin_fsqrt : ident := 91%positive.
Definition _snd : ident := 36%positive.
Definition __x8 : ident := 195%positive.
Definition ___builtin_read16_reversed : ident := 98%positive.
Definition _S : ident := 19%positive.
Definition ___stringlit_19 : ident := 182%positive.
Definition ___builtin_va_start : ident := 61%positive.
Definition ___builtin_fnmsub : ident := 97%positive.
Definition _result : ident := 122%positive.
Definition __1344 : ident := 37%positive.
Definition _b : ident := 133%positive.
Definition ___stringlit_7 : ident := 152%positive.
Definition __x12 : ident := 191%positive.
Definition __1356 : ident := 42%positive.
Definition _c : ident := 169%positive.
Definition _make_false : ident := 132%positive.
Definition ___i64_stod : ident := 71%positive.
Definition _make_N0 : ident := 161%positive.
Definition _print_positive : ident := 159%positive.
Definition ___i64_sdiv : ident := 75%positive.
Definition _cons : ident := 34%positive.
Definition _head : ident := 29%positive.
Definition _n_ : ident := 176%positive.
Definition ___builtin_fmsub : ident := 95%positive.
Definition _closure : ident := 55%positive.
Definition _Npos : ident := 51%positive.
Definition __1390 : ident := 48%positive.
Definition ___stringlit_21 : ident := 184%positive.
Definition ___stringlit_13 : ident := 166%positive.
Definition _make_xI : ident := 147%positive.
Definition ___compcert_va_int32 : ident := 65%positive.
Definition _positive : ident := 40%positive.
Definition _main : ident := 185%positive.
Definition _t : ident := 112%positive.
Definition _n : ident := 16%positive.
Definition _pair : ident := 38%positive.
Definition ___stringlit_14 : ident := 167%positive.
Definition _xO : ident := 46%positive.
Definition ___i64_dtos : ident := 69%positive.
Definition ___builtin_va_arg : ident := 62%positive.
Definition _upvars : ident := 54%positive.
Definition ___stringlit_18 : ident := 181%positive.
Definition _make_closure : ident := 170%positive.
Definition __x0 : ident := 203%positive.
Definition _a : ident := 171%positive.
Definition ___builtin_fmax : ident := 92%positive.
Definition ___stringlit_8 : ident := 153%positive.
Definition _scanf : ident := 104%positive.
Definition _tm_min : ident := 2%positive.
Definition __x4 : ident := 199%positive.
Definition __x6 : ident := 197%positive.
Definition _x : ident := 121%positive.
Definition _tail : ident := 31%positive.
Definition _make_Npos : ident := 162%positive.
Definition __1391 : ident := 49%positive.
Definition ___compcert_va_int64 : ident := 66%positive.
Definition ___builtin_annot_intval : ident := 59%positive.
Definition _tm_mday : ident := 4%positive.
Definition __x2 : ident := 201%positive.
Definition _N_of_uint : ident := 164%positive.
Definition _uint_of_N : ident := 165%positive.
Definition ___builtin_fmadd : ident := 94%positive.
Definition ___builtin_annot : ident := 58%positive.
Definition _leading_zeros : ident := 151%positive.
Definition _q : ident := 146%positive.
Definition _clone_N : ident := 163%positive.
Definition _uint_of_nat : ident := 125%positive.
Definition ___builtin_read32_reversed : ident := 99%positive.
Definition _tt : ident := 21%positive.
Definition _O : ident := 18%positive.
Definition _malloc : ident := 106%positive.
Definition ___i64_shr : ident := 80%positive.
Definition _tag : ident := 13%positive.
Definition _double_nat_elim_elim0 : ident := 186%positive.
Definition _nil : ident := 33%positive.
Definition _i : ident := 123%positive.
Definition ___builtin_fabs : ident := 56%positive.
Definition __x3 : ident := 200%positive.
Definition ___stringlit_5 : ident := 139%positive.
Definition _get_time : ident := 115%positive.
Definition ___builtin_write16_reversed : ident := 100%positive.
Definition __1306 : ident := 20%positive.
Definition __x14 : ident := 189%positive.
Definition _ap : ident := 173%positive.
Definition __x10 : ident := 193%positive.
Definition _positive_to_uint : ident := 156%positive.
Definition ___builtin_fmin : ident := 93%positive.
Definition _call : ident := 172%positive.
Definition _snprintf : ident := 105%positive.
Definition ___stringlit_2 : ident := 126%positive.
Definition __1312 : ident := 24%positive.
Definition ___compcert_va_float64 : ident := 67%positive.
Definition _tm_mon : ident := 5%positive.
Definition ___i64_stof : ident := 73%positive.
Definition _N0 : ident := 50%positive.
Definition ___i64_utof : ident := 74%positive.
Definition _m_ : ident := 177%positive.
Definition _print_N : ident := 168%positive.
Definition _uint_to_positive : ident := 155%positive.
Definition _abort : ident := 107%positive.
Definition ___builtin_memcpy_aligned : ident := 57%positive.
Definition __1279 : ident := 14%positive.
Definition _tm_year : ident := 6%positive.
Definition _print_list : ident := 140%positive.
Definition _make_S : ident := 118%positive.
Definition _false_ : ident := 26%positive.
Definition ___stringlit_11 : ident := 158%positive.
Definition _int_of_bool : ident := 134%positive.
Definition _prod : ident := 39%positive.
Definition __x1 : ident := 202%positive.
Definition _double_nat_elim_0 : ident := 188%positive.
Definition ___stringlit_15 : ident := 178%positive.
Definition ___builtin_ctzll : ident := 90%positive.
Definition ___builtin_bswap32 : ident := 83%positive.
Definition _tm_zone : ident := 11%positive.
Definition _make_O : ident := 116%positive.
Definition __x7 : ident := 196%positive.
Definition ___i64_sar : ident := 81%positive.
Definition ___i64_udiv : ident := 76%positive.
Definition _clone_prod : ident := 145%positive.
Definition ___stringlit_12 : ident := 160%positive.
Definition _f2 : ident := 144%positive.
Definition ___builtin_clzl : ident := 86%positive.
Definition _tm_isdst : ident := 9%positive.
Definition _make_true : ident := 131%positive.
Definition ___builtin_va_end : ident := 64%positive.
Definition _N : ident := 52%positive.
Definition _p : ident := 41%positive.
Definition _vcall : ident := 174%positive.
Definition ___builtin_clzll : ident := 87%positive.
Definition ___i64_smod : ident := 77%positive.
Definition _clone_nat : ident := 120%positive.
Definition _fst : ident := 35%positive.
Definition _list : ident := 30%positive.
Definition __1311 : ident := 23%positive.

Definition f_double_nat_elim := {|
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
            (Econst (Oaddrsymbol _double_nat_elim_elim0 (Int.repr 0)))))
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

Definition f_double_nat_elim_0 := {|
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
              (Econst (Oaddrsymbol _double_nat_elim_0_1 (Int.repr 0)))))
          (Sseq
            (Sstore Mint32
              (Ebinop Oadd (Evar __x3) (Econst (Ointconst (Int.repr 4))))
              (Evar __x0))
            (Sstore Mint32
              (Ebinop Oadd (Evar __x3) (Econst (Ointconst (Int.repr 8))))
              (Evar __x2)))))))
  (Sreturn (Some (Evar __x3))))
|}.

Definition f_double_nat_elim_0_1 := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x2 :: __x1 :: __x0 :: nil);
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
          (Sstore Mint32 (Evar __x1) (Econst (Ointconst (Int.repr 1)))))
        (Sstore Mint32
          (Ebinop Oadd (Evar __x1) (Econst (Ointconst (Int.repr 4))))
          (Evar __x0)))
      (Sseq
        (Sseq
          (Scall (Some __x2)
            (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
            (Econst (Oaddrsymbol _malloc (Int.repr 0)))
            ((Econst (Ointconst (Int.repr 8))) :: nil))
          (Sstore Mint32 (Evar __x2) (Econst (Ointconst (Int.repr 1)))))
        (Sstore Mint32
          (Ebinop Oadd (Evar __x2) (Econst (Ointconst (Int.repr 4))))
          (Evar __x1)))))
  (Sreturn (Some (Evar __x2))))
|}.

Definition f_double_nat_elim_elim0 := {|
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
                        (Econst (Oaddrsymbol _double_nat_elim_0 (Int.repr 0)))))
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
                                    (Econst (Oaddrsymbol _double_nat_elim_elim0 (Int.repr 0)))))
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
((_double_nat_elim, Gfun(Internal f_double_nat_elim)) ::
 (_double_nat_elim_0, Gfun(Internal f_double_nat_elim_0)) ::
 (_double_nat_elim_0_1, Gfun(Internal f_double_nat_elim_0_1)) ::
 (_double_nat_elim_elim0, Gfun(Internal f_double_nat_elim_elim0)) ::
 (_malloc, Gfun(External EF_malloc)) :: nil);
prog_public :=
(_double_nat_elim :: _double_nat_elim_0 :: _double_nat_elim_0_1 :: nil);
prog_main := _tm_sec;
|}.

