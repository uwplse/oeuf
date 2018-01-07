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

Definition v___stringlit_6 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 91) :: Init_int8 (Int.repr 93) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_14 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_20 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_10 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 72) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_21 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_18 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_13 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 0) :: nil);
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

Definition v___stringlit_16 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_9 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 96) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 39) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_11 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 79) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_17 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_15 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 63) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_19 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_8 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 47) :: Init_int8 (Int.repr 85) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 47) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 47) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_7 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_12 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := tt;
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_time_buf := {|
  gvar_info := tt;
  gvar_init := (Init_space 1024 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_get_time := {|
  fn_sig := (mksignature nil (Some AST.Tint) cc_default);
  fn_params := nil;
  fn_vars := (208%positive :: 207%positive :: nil);
  fn_stackspace := 52;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 207%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _time (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 0))) :: nil))
    (Sstore Mint32 (Econst (Oaddrstack (Int.repr 0))) (Evar 207%positive)))
  (Sseq
    (Sseq
      (Scall (Some 208%positive)
        (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
        (Econst (Oaddrsymbol _localtime (Int.repr 0)))
        ((Econst (Oaddrstack (Int.repr 0))) :: nil))
      (Sbuiltin None (EF_memcpy 44 4)
        ((Econst (Oaddrstack (Int.repr 8))) :: (Evar 208%positive) :: nil)))
    (Sseq
      (Scall None
        (mksignature
          (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
           AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
          (Some AST.Tint)
          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
        (Econst (Oaddrsymbol _snprintf (Int.repr 0)))
        ((Econst (Oaddrsymbol _time_buf (Int.repr 0))) ::
         (Econst (Ointconst (Int.repr 1024))) ::
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

Definition f_make_O := {|
  fn_sig := (mksignature nil (Some AST.Tint) cc_default);
  fn_params := nil;
  fn_vars := (_n :: 209%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 209%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 4))) :: nil))
    (Sassign _n (Evar 209%positive)))
  (Sseq
    (Sstore Mint32 (Ebinop Oadd (Evar _n) (Econst (Ointconst (Int.repr 0))))
      (Econst (Ointconst (Int.repr 0))))
    (Sreturn (Some (Evar _n)))))
|}.

Definition f_make_S := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_m :: nil);
  fn_vars := (_n :: 210%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 210%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 8))) :: nil))
    (Sassign _n (Evar 210%positive)))
  (Sseq
    (Sstore Mint32 (Ebinop Oadd (Evar _n) (Econst (Ointconst (Int.repr 0))))
      (Econst (Ointconst (Int.repr 1))))
    (Sseq
      (Sstore Mint32
        (Ebinop Oadd (Evar _n) (Econst (Ointconst (Int.repr 4)))) (Evar _m))
      (Sreturn (Some (Evar _n))))))
|}.

Definition f_clone_nat := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_n :: nil);
  fn_vars := (_tail_p :: 212%positive :: 211%positive :: nil);
  fn_stackspace := 4;
  fn_body :=
(Sseq
  (Sstore Mint32 (Econst (Oaddrstack (Int.repr 0)))
    (Econst (Ointconst (Int.repr 0))))
  (Sseq
    (Sassign _tail_p (Econst (Oaddrstack (Int.repr 0))))
    (Sseq
      (Sblock
        (Sloop
          (Sblock
            (Sseq
              (Sifthenelse (Ebinop (Ocmpu Cne) (Evar _n)
                             (Econst (Ointconst (Int.repr 0))))
                Sskip
                (Sexit (S O)))
              (Sblock
                (Sblock
                  (Sseq
                    (Sblock
                      (Sseq
                        (Sblock
                          (Sseq
                            (Sblock
                              (Sswitch false (Eload Mint32 (Evar _n))
                                ((0%Z, O) :: (1%Z, (S O)) :: nil)
                                (S (S O))))
                            (Sseq
                              (Sseq
                                (Scall (Some 211%positive)
                                  (mksignature nil (Some AST.Tint)
                                    cc_default)
                                  (Econst (Oaddrsymbol _make_O (Int.repr 0)))
                                  nil)
                                (Sstore Mint32 (Evar _tail_p)
                                  (Evar 211%positive)))
                              (Sseq
                                (Sassign _n
                                  (Econst (Ointconst (Int.repr 0))))
                                (Sexit (S (S (S O))))))))
                        (Sseq
                          (Sseq
                            (Scall (Some 212%positive)
                              (mksignature (AST.Tint :: nil) (Some AST.Tint)
                                cc_default)
                              (Econst (Oaddrsymbol _make_S (Int.repr 0)))
                              ((Econst (Ointconst (Int.repr 0))) :: nil))
                            (Sstore Mint32 (Evar _tail_p)
                              (Evar 212%positive)))
                          (Sseq
                            (Sassign _tail_p
                              (Ebinop Oadd (Eload Mint32 (Evar _tail_p))
                                (Econst (Ointconst (Int.repr 4)))))
                            (Sseq
                              (Sassign _n
                                (Eload Mint32
                                  (Ebinop Oadd (Evar _n)
                                    (Econst (Ointconst (Int.repr 4))))))
                              (Sexit (S (S O))))))))
                    (Scall None (mksignature nil None cc_default)
                      (Econst (Oaddrsymbol _abort (Int.repr 0))) nil))))))))
      (Sreturn (Some (Eload Mint32 (Econst (Oaddrstack (Int.repr 0)))))))))
|}.

Definition f_nat_of_uint := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_x :: nil);
  fn_vars := (_result :: _i :: 214%positive :: 213%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 213%positive) (mksignature nil (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _make_O (Int.repr 0))) nil)
    (Sassign _result (Evar 213%positive)))
  (Sseq
    (Sseq
      (Sassign _i (Econst (Ointconst (Int.repr 0))))
      (Sblock
        (Sloop
          (Sseq
            (Sblock
              (Sseq
                (Sifthenelse (Ebinop (Ocmpu Clt) (Evar _i) (Evar _x))
                  Sskip
                  (Sexit (S O)))
                (Sseq
                  (Scall (Some 214%positive)
                    (mksignature (AST.Tint :: nil) (Some AST.Tint)
                      cc_default) (Econst (Oaddrsymbol _make_S (Int.repr 0)))
                    ((Evar _result) :: nil))
                  (Sassign _result (Evar 214%positive)))))
            (Sassign _i
              (Ebinop Oadd (Evar _i) (Econst (Ointconst (Int.repr 1)))))))))
    (Sreturn (Some (Evar _result)))))
|}.

Definition f_uint_of_nat := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_n :: nil);
  fn_vars := (_result :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sassign _result (Econst (Ointconst (Int.repr 0))))
  (Sseq
    (Sblock
      (Sloop
        (Sblock
          (Sseq
            (Sifthenelse (Ebinop (Ocmp Cne) (Eload Mint32 (Evar _n))
                           (Econst (Ointconst (Int.repr 0))))
              Sskip
              (Sexit (S O)))
            (Sseq
              (Sassign _result
                (Ebinop Oadd (Evar _result)
                  (Econst (Ointconst (Int.repr 1)))))
              (Sassign _n
                (Eload Mint32
                  (Ebinop Oadd (Evar _n) (Econst (Ointconst (Int.repr 4)))))))))))
    (Sreturn (Some (Evar _result)))))
|}.

Definition f_print_nat := {|
  fn_sig := (mksignature (AST.Tint :: nil) None cc_default);
  fn_params := (_n :: nil);
  fn_vars := nil;
  fn_stackspace := 0;
  fn_body :=
(Sblock
  (Sblock
    (Sseq
      (Sblock
        (Sseq
          (Sblock
            (Sswitch false (Eload Mint32 (Evar _n))
              ((0%Z, O) :: (1%Z, (S O)) :: nil)
              (S (S O))))
          (Sseq
            (Scall None
              (mksignature (AST.Tint :: nil) (Some AST.Tint)
                {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
              (Econst (Oaddrsymbol _printf (Int.repr 0)))
              ((Econst (Oaddrsymbol ___stringlit_4 (Int.repr 0))) :: nil))
            (Sexit (S (S O))))))
      (Sseq
        (Scall None
          (mksignature (AST.Tint :: nil) (Some AST.Tint)
            {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
          (Econst (Oaddrsymbol _printf (Int.repr 0)))
          ((Econst (Oaddrsymbol ___stringlit_2 (Int.repr 0))) :: nil))
        (Sseq
          (Scall None (mksignature (AST.Tint :: nil) None cc_default)
            (Econst (Oaddrsymbol _print_nat (Int.repr 0)))
            ((Eload Mint32
               (Ebinop Oadd (Evar _n) (Econst (Ointconst (Int.repr 4))))) ::
             nil))
          (Sseq
            (Scall None
              (mksignature (AST.Tint :: nil) (Some AST.Tint)
                {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
              (Econst (Oaddrsymbol _printf (Int.repr 0)))
              ((Econst (Oaddrsymbol ___stringlit_3 (Int.repr 0))) :: nil))
            (Sexit (S O))))))))
|}.

Definition f_make_unit := {|
  fn_sig := (mksignature nil (Some AST.Tint) cc_default);
  fn_params := nil;
  fn_vars := (_result :: 215%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 215%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 4))) :: nil))
    (Sassign _result (Evar 215%positive)))
  (Sseq
    (Sstore Mint32
      (Ebinop Oadd (Evar _result) (Econst (Ointconst (Int.repr 0))))
      (Econst (Ointconst (Int.repr 0))))
    (Sreturn (Some (Evar _result)))))
|}.

Definition f_make_true := {|
  fn_sig := (mksignature nil (Some AST.Tint) cc_default);
  fn_params := nil;
  fn_vars := (_result :: 216%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 216%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 4))) :: nil))
    (Sassign _result (Evar 216%positive)))
  (Sseq
    (Sstore Mint32
      (Ebinop Oadd (Evar _result) (Econst (Ointconst (Int.repr 0))))
      (Econst (Ointconst (Int.repr 0))))
    (Sreturn (Some (Evar _result)))))
|}.

Definition f_make_false := {|
  fn_sig := (mksignature nil (Some AST.Tint) cc_default);
  fn_params := nil;
  fn_vars := (_result :: 217%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 217%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 4))) :: nil))
    (Sassign _result (Evar 217%positive)))
  (Sseq
    (Sstore Mint32
      (Ebinop Oadd (Evar _result) (Econst (Ointconst (Int.repr 0))))
      (Econst (Ointconst (Int.repr 1))))
    (Sreturn (Some (Evar _result)))))
|}.

Definition f_int_of_bool := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_b :: nil);
  fn_vars := nil;
  fn_stackspace := 0;
  fn_body :=
(Sreturn (Some (Ebinop (Ocmp Ceq) (Eload Mint32 (Evar _b))
                 (Econst (Ointconst (Int.repr 0))))))
|}.

Definition f_make_nil := {|
  fn_sig := (mksignature nil (Some AST.Tint) cc_default);
  fn_params := nil;
  fn_vars := (_l :: 218%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 218%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 4))) :: nil))
    (Sassign _l (Evar 218%positive)))
  (Sseq
    (Sstore Mint32 (Ebinop Oadd (Evar _l) (Econst (Ointconst (Int.repr 0))))
      (Econst (Ointconst (Int.repr 0))))
    (Sreturn (Some (Evar _l)))))
|}.

Definition f_make_cons := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (_head :: _tail :: nil);
  fn_vars := (_l :: 219%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 219%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 12))) :: nil))
    (Sassign _l (Evar 219%positive)))
  (Sseq
    (Sstore Mint32 (Ebinop Oadd (Evar _l) (Econst (Ointconst (Int.repr 0))))
      (Econst (Ointconst (Int.repr 1))))
    (Sseq
      (Sstore Mint32
        (Ebinop Oadd (Evar _l) (Econst (Ointconst (Int.repr 4))))
        (Evar _head))
      (Sseq
        (Sstore Mint32
          (Ebinop Oadd (Evar _l) (Econst (Ointconst (Int.repr 8))))
          (Evar _tail))
        (Sreturn (Some (Evar _l)))))))
|}.

Definition f_clone_list := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (_l :: _f :: nil);
  fn_vars := (_tail_p :: 222%positive :: 221%positive :: 220%positive :: nil);
  fn_stackspace := 4;
  fn_body :=
(Sseq
  (Sstore Mint32 (Econst (Oaddrstack (Int.repr 0)))
    (Econst (Ointconst (Int.repr 0))))
  (Sseq
    (Sassign _tail_p (Econst (Oaddrstack (Int.repr 0))))
    (Sseq
      (Sblock
        (Sloop
          (Sblock
            (Sseq
              (Sifthenelse (Ebinop (Ocmpu Cne) (Evar _l)
                             (Econst (Ointconst (Int.repr 0))))
                Sskip
                (Sexit (S O)))
              (Sblock
                (Sblock
                  (Sseq
                    (Sblock
                      (Sseq
                        (Sblock
                          (Sseq
                            (Sblock
                              (Sswitch false (Eload Mint32 (Evar _l))
                                ((0%Z, O) :: (1%Z, (S O)) :: nil)
                                (S (S O))))
                            (Sseq
                              (Sseq
                                (Scall (Some 220%positive)
                                  (mksignature nil (Some AST.Tint)
                                    cc_default)
                                  (Econst (Oaddrsymbol _make_nil (Int.repr 0)))
                                  nil)
                                (Sstore Mint32 (Evar _tail_p)
                                  (Evar 220%positive)))
                              (Sseq
                                (Sassign _l
                                  (Econst (Ointconst (Int.repr 0))))
                                (Sexit (S (S (S O))))))))
                        (Sseq
                          (Sseq
                            (Sseq
                              (Scall (Some 221%positive)
                                (mksignature (AST.Tint :: nil)
                                  (Some AST.Tint) cc_default) (Evar _f)
                                ((Eload Mint32
                                   (Ebinop Oadd (Evar _l)
                                     (Econst (Ointconst (Int.repr 4))))) ::
                                 nil))
                              (Scall (Some 222%positive)
                                (mksignature (AST.Tint :: AST.Tint :: nil)
                                  (Some AST.Tint) cc_default)
                                (Econst (Oaddrsymbol _make_cons (Int.repr 0)))
                                ((Evar 221%positive) ::
                                 (Econst (Ointconst (Int.repr 0))) :: nil)))
                            (Sstore Mint32 (Evar _tail_p)
                              (Evar 222%positive)))
                          (Sseq
                            (Sassign _tail_p
                              (Ebinop Oadd (Eload Mint32 (Evar _tail_p))
                                (Econst (Ointconst (Int.repr 8)))))
                            (Sseq
                              (Sassign _l
                                (Eload Mint32
                                  (Ebinop Oadd (Evar _l)
                                    (Econst (Ointconst (Int.repr 8))))))
                              (Sexit (S (S O))))))))
                    (Scall None (mksignature nil None cc_default)
                      (Econst (Oaddrsymbol _abort (Int.repr 0))) nil))))))))
      (Sreturn (Some (Eload Mint32 (Econst (Oaddrstack (Int.repr 0)))))))))
|}.

Definition f_print_list := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) None cc_default);
  fn_params := (_l :: _f :: nil);
  fn_vars := nil;
  fn_stackspace := 0;
  fn_body :=
(Sblock
  (Sblock
    (Sseq
      (Sblock
        (Sseq
          (Sblock
            (Sswitch false (Eload Mint32 (Evar _l))
              ((0%Z, O) :: (1%Z, (S O)) :: nil)
              (S (S O))))
          (Sseq
            (Scall None
              (mksignature (AST.Tint :: nil) (Some AST.Tint)
                {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
              (Econst (Oaddrsymbol _printf (Int.repr 0)))
              ((Econst (Oaddrsymbol ___stringlit_6 (Int.repr 0))) :: nil))
            (Sexit (S (S O))))))
      (Sseq
        (Scall None (mksignature (AST.Tint :: nil) None cc_default) (Evar _f)
          ((Eload Mint32
             (Ebinop Oadd (Evar _l) (Econst (Ointconst (Int.repr 4))))) ::
           nil))
        (Sseq
          (Scall None
            (mksignature (AST.Tint :: nil) (Some AST.Tint)
              {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
            (Econst (Oaddrsymbol _printf (Int.repr 0)))
            ((Econst (Oaddrsymbol ___stringlit_5 (Int.repr 0))) :: nil))
          (Sseq
            (Scall None
              (mksignature (AST.Tint :: AST.Tint :: nil) None cc_default)
              (Econst (Oaddrsymbol _print_list (Int.repr 0)))
              ((Eload Mint32
                 (Ebinop Oadd (Evar _l) (Econst (Ointconst (Int.repr 8))))) ::
               (Evar _f) :: nil))
            (Sexit (S O))))))))
|}.

Definition f_make_pair := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (_fst :: _snd :: nil);
  fn_vars := (_p :: 223%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 223%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 12))) :: nil))
    (Sassign _p (Evar 223%positive)))
  (Sseq
    (Sstore Mint32 (Ebinop Oadd (Evar _p) (Econst (Ointconst (Int.repr 0))))
      (Econst (Ointconst (Int.repr 0))))
    (Sseq
      (Sstore Mint32
        (Ebinop Oadd (Evar _p) (Econst (Ointconst (Int.repr 4))))
        (Evar _fst))
      (Sseq
        (Sstore Mint32
          (Ebinop Oadd (Evar _p) (Econst (Ointconst (Int.repr 8))))
          (Evar _snd))
        (Sreturn (Some (Evar _p)))))))
|}.

Definition f_clone_prod := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
              (Some AST.Tint) cc_default);
  fn_params := (_p :: _f1 :: _f2 :: nil);
  fn_vars := (226%positive :: 225%positive :: 224%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Sseq
      (Scall (Some 224%positive)
        (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default) (Evar _f1)
        ((Eload Mint32
           (Ebinop Oadd (Evar _p) (Econst (Ointconst (Int.repr 4))))) :: nil))
      (Scall (Some 225%positive)
        (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default) (Evar _f2)
        ((Eload Mint32
           (Ebinop Oadd (Evar _p) (Econst (Ointconst (Int.repr 8))))) :: nil)))
    (Scall (Some 226%positive)
      (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _make_pair (Int.repr 0)))
      ((Evar 224%positive) :: (Evar 225%positive) :: nil)))
  (Sreturn (Some (Evar 226%positive))))
|}.

Definition f_make_xI := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_q :: nil);
  fn_vars := (_p :: 227%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 227%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 8))) :: nil))
    (Sassign _p (Evar 227%positive)))
  (Sseq
    (Sstore Mint32 (Ebinop Oadd (Evar _p) (Econst (Ointconst (Int.repr 0))))
      (Econst (Ointconst (Int.repr 0))))
    (Sseq
      (Sstore Mint32
        (Ebinop Oadd (Evar _p) (Econst (Ointconst (Int.repr 4)))) (Evar _q))
      (Sreturn (Some (Evar _p))))))
|}.

Definition f_make_xO := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_q :: nil);
  fn_vars := (_p :: 228%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 228%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 8))) :: nil))
    (Sassign _p (Evar 228%positive)))
  (Sseq
    (Sstore Mint32 (Ebinop Oadd (Evar _p) (Econst (Ointconst (Int.repr 0))))
      (Econst (Ointconst (Int.repr 1))))
    (Sseq
      (Sstore Mint32
        (Ebinop Oadd (Evar _p) (Econst (Ointconst (Int.repr 4)))) (Evar _q))
      (Sreturn (Some (Evar _p))))))
|}.

Definition f_make_xH := {|
  fn_sig := (mksignature nil (Some AST.Tint) cc_default);
  fn_params := nil;
  fn_vars := (_p :: 229%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 229%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 4))) :: nil))
    (Sassign _p (Evar 229%positive)))
  (Sseq
    (Sstore Mint32 (Ebinop Oadd (Evar _p) (Econst (Ointconst (Int.repr 0))))
      (Econst (Ointconst (Int.repr 2))))
    (Sreturn (Some (Evar _p)))))
|}.

Definition f_clone_positive := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_p :: nil);
  fn_vars := (_tail_p :: 232%positive :: 231%positive :: 230%positive :: nil);
  fn_stackspace := 4;
  fn_body :=
(Sseq
  (Sstore Mint32 (Econst (Oaddrstack (Int.repr 0)))
    (Econst (Ointconst (Int.repr 0))))
  (Sseq
    (Sassign _tail_p (Econst (Oaddrstack (Int.repr 0))))
    (Sseq
      (Sblock
        (Sloop
          (Sblock
            (Sseq
              (Sifthenelse (Ebinop (Ocmpu Cne) (Evar _p)
                             (Econst (Ointconst (Int.repr 0))))
                Sskip
                (Sexit (S O)))
              (Sblock
                (Sblock
                  (Sseq
                    (Sblock
                      (Sseq
                        (Sblock
                          (Sseq
                            (Sblock
                              (Sseq
                                (Sblock
                                  (Sswitch false (Eload Mint32 (Evar _p))
                                    ((0%Z, O) :: (1%Z, (S O)) ::
                                     (2%Z, (S (S O))) :: nil)
                                    (S (S (S O)))))
                                (Sseq
                                  (Sseq
                                    (Scall (Some 230%positive)
                                      (mksignature (AST.Tint :: nil)
                                        (Some AST.Tint) cc_default)
                                      (Econst (Oaddrsymbol _make_xI (Int.repr 0)))
                                      ((Econst (Ointconst (Int.repr 0))) ::
                                       nil))
                                    (Sstore Mint32 (Evar _tail_p)
                                      (Evar 230%positive)))
                                  (Sseq
                                    (Sassign _tail_p
                                      (Ebinop Oadd
                                        (Eload Mint32 (Evar _tail_p))
                                        (Econst (Ointconst (Int.repr 4)))))
                                    (Sseq
                                      (Sassign _p
                                        (Eload Mint32
                                          (Ebinop Oadd (Evar _p)
                                            (Econst (Ointconst (Int.repr 4))))))
                                      (Sexit (S (S (S (S O))))))))))
                            (Sseq
                              (Sseq
                                (Scall (Some 231%positive)
                                  (mksignature (AST.Tint :: nil)
                                    (Some AST.Tint) cc_default)
                                  (Econst (Oaddrsymbol _make_xO (Int.repr 0)))
                                  ((Econst (Ointconst (Int.repr 0))) :: nil))
                                (Sstore Mint32 (Evar _tail_p)
                                  (Evar 231%positive)))
                              (Sseq
                                (Sassign _tail_p
                                  (Ebinop Oadd (Eload Mint32 (Evar _tail_p))
                                    (Econst (Ointconst (Int.repr 4)))))
                                (Sseq
                                  (Sassign _p
                                    (Eload Mint32
                                      (Ebinop Oadd (Evar _p)
                                        (Econst (Ointconst (Int.repr 4))))))
                                  (Sexit (S (S (S O)))))))))
                        (Sseq
                          (Sseq
                            (Scall (Some 232%positive)
                              (mksignature nil (Some AST.Tint) cc_default)
                              (Econst (Oaddrsymbol _make_xH (Int.repr 0)))
                              nil)
                            (Sstore Mint32 (Evar _tail_p)
                              (Evar 232%positive)))
                          (Sseq
                            (Sassign _p (Econst (Ointconst (Int.repr 0))))
                            (Sexit (S (S O)))))))
                    (Scall None (mksignature nil None cc_default)
                      (Econst (Oaddrsymbol _abort (Int.repr 0))) nil))))))))
      (Sreturn (Some (Eload Mint32 (Econst (Oaddrstack (Int.repr 0)))))))))
|}.

Definition f_uint_to_positive := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_x :: nil);
  fn_vars := (_result :: _leading_zeros :: _i :: 239%positive ::
              238%positive :: 237%positive :: 236%positive :: 235%positive ::
              234%positive :: 233%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sifthenelse (Ebinop (Ocmpu Cge) (Evar _x)
                 (Econst (Ointconst (Int.repr 1))))
    (Sassign 233%positive (Econst (Ointconst (Int.repr 0))))
    (Sseq
      (Sseq
        (Scall (Some 234%positive)
          (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
            (Some AST.Tint)
            {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
          (Econst (Oaddrsymbol _printf (Int.repr 0)))
          ((Econst (Oaddrsymbol ___stringlit_9 (Int.repr 0))) ::
           (Econst (Oaddrsymbol ___stringlit_8 (Int.repr 0))) ::
           (Econst (Ointconst (Int.repr 339))) ::
           (Econst (Oaddrsymbol ___stringlit_7 (Int.repr 0))) :: nil))
        (Scall (Some 235%positive) (mksignature nil None cc_default)
          (Econst (Oaddrsymbol _abort (Int.repr 0))) nil))
      (Sassign 233%positive (Evar 235%positive))))
  (Sseq
    (Sseq
      (Scall (Some 236%positive) (mksignature nil (Some AST.Tint) cc_default)
        (Econst (Oaddrsymbol _make_xH (Int.repr 0))) nil)
      (Sassign _result (Evar 236%positive)))
    (Sseq
      (Sseq
        (Scall (Some 237%positive)
          (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
          (Econst (Oaddrsymbol ___builtin_clz (Int.repr 0)))
          ((Evar _x) :: nil))
        (Sassign _leading_zeros (Evar 237%positive)))
      (Sseq
        (Sseq
          (Sassign _i
            (Ebinop Osub (Econst (Ointconst (Int.repr 30)))
              (Evar _leading_zeros)))
          (Sblock
            (Sloop
              (Sseq
                (Sblock
                  (Sseq
                    (Sifthenelse (Ebinop (Ocmp Cge) (Evar _i)
                                   (Econst (Ointconst (Int.repr 0))))
                      Sskip
                      (Sexit (S O)))
                    (Sifthenelse (Ebinop (Ocmp Cne)
                                   (Ebinop Oand (Evar _x)
                                     (Ebinop Oshl
                                       (Econst (Ointconst (Int.repr 1)))
                                       (Evar _i)))
                                   (Econst (Ointconst (Int.repr 0))))
                      (Sseq
                        (Scall (Some 238%positive)
                          (mksignature (AST.Tint :: nil) (Some AST.Tint)
                            cc_default)
                          (Econst (Oaddrsymbol _make_xI (Int.repr 0)))
                          ((Evar _result) :: nil))
                        (Sassign _result (Evar 238%positive)))
                      (Sseq
                        (Scall (Some 239%positive)
                          (mksignature (AST.Tint :: nil) (Some AST.Tint)
                            cc_default)
                          (Econst (Oaddrsymbol _make_xO (Int.repr 0)))
                          ((Evar _result) :: nil))
                        (Sassign _result (Evar 239%positive))))))
                (Sassign _i
                  (Ebinop Osub (Evar _i) (Econst (Ointconst (Int.repr 1)))))))))
        (Sreturn (Some (Evar _result)))))))
|}.

Definition f_positive_to_uint := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_p :: nil);
  fn_vars := (_i :: _result :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sassign _i (Econst (Ointconst (Int.repr 0))))
  (Sseq
    (Sassign _result (Econst (Ointconst (Int.repr 0))))
    (Sblock
      (Sloop
        (Sseq
          (Sblock
            (Sseq
              Sskip
              (Sblock
                (Sblock
                  (Sseq
                    (Sblock
                      (Sseq
                        (Sblock
                          (Sseq
                            (Sblock
                              (Sswitch false (Eload Mint32 (Evar _p))
                                ((0%Z, O) :: (1%Z, (S O)) ::
                                 (2%Z, (S (S O))) :: nil)
                                (S (S (S O)))))
                            (Sseq
                              (Sassign _result
                                (Ebinop Oor (Evar _result)
                                  (Ebinop Oshl
                                    (Econst (Ointconst (Int.repr 1)))
                                    (Evar _i))))
                              (Sseq
                                (Sassign _p
                                  (Eload Mint32
                                    (Ebinop Oadd (Evar _p)
                                      (Econst (Ointconst (Int.repr 4))))))
                                (Sexit (S (S (S O))))))))
                        (Sseq
                          (Sassign _p
                            (Eload Mint32
                              (Ebinop Oadd (Evar _p)
                                (Econst (Ointconst (Int.repr 4))))))
                          (Sexit (S (S O))))))
                    (Sseq
                      (Sassign _result
                        (Ebinop Oor (Evar _result)
                          (Ebinop Oshl (Econst (Ointconst (Int.repr 1)))
                            (Evar _i))))
                      (Sreturn (Some (Evar _result)))))))))
          (Sassign _i
            (Ebinop Oadd (Evar _i) (Econst (Ointconst (Int.repr 1))))))))))
|}.

Definition f_print_positive := {|
  fn_sig := (mksignature (AST.Tint :: nil) None cc_default);
  fn_params := (_p :: nil);
  fn_vars := nil;
  fn_stackspace := 0;
  fn_body :=
(Sblock
  (Sblock
    (Sseq
      (Sblock
        (Sseq
          (Sblock
            (Sseq
              (Sblock
                (Sswitch false (Eload Mint32 (Evar _p))
                  ((0%Z, O) :: (1%Z, (S O)) :: (2%Z, (S (S O))) :: nil)
                  (S (S (S O)))))
              (Sseq
                (Scall None
                  (mksignature (AST.Tint :: nil) (Some AST.Tint)
                    {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
                  (Econst (Oaddrsymbol _printf (Int.repr 0)))
                  ((Econst (Oaddrsymbol ___stringlit_12 (Int.repr 0))) ::
                   nil))
                (Sseq
                  (Scall None (mksignature (AST.Tint :: nil) None cc_default)
                    (Econst (Oaddrsymbol _print_positive (Int.repr 0)))
                    ((Eload Mint32
                       (Ebinop Oadd (Evar _p)
                         (Econst (Ointconst (Int.repr 4))))) :: nil))
                  (Sseq
                    (Scall None
                      (mksignature (AST.Tint :: nil) (Some AST.Tint)
                        {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
                      (Econst (Oaddrsymbol _printf (Int.repr 0)))
                      ((Econst (Oaddrsymbol ___stringlit_3 (Int.repr 0))) ::
                       nil))
                    (Sexit (S (S (S O)))))))))
          (Sseq
            (Scall None
              (mksignature (AST.Tint :: nil) (Some AST.Tint)
                {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
              (Econst (Oaddrsymbol _printf (Int.repr 0)))
              ((Econst (Oaddrsymbol ___stringlit_11 (Int.repr 0))) :: nil))
            (Sseq
              (Scall None (mksignature (AST.Tint :: nil) None cc_default)
                (Econst (Oaddrsymbol _print_positive (Int.repr 0)))
                ((Eload Mint32
                   (Ebinop Oadd (Evar _p) (Econst (Ointconst (Int.repr 4))))) ::
                 nil))
              (Sseq
                (Scall None
                  (mksignature (AST.Tint :: nil) (Some AST.Tint)
                    {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
                  (Econst (Oaddrsymbol _printf (Int.repr 0)))
                  ((Econst (Oaddrsymbol ___stringlit_3 (Int.repr 0))) :: nil))
                (Sexit (S (S O))))))))
      (Sseq
        (Scall None
          (mksignature (AST.Tint :: nil) (Some AST.Tint)
            {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
          (Econst (Oaddrsymbol _printf (Int.repr 0)))
          ((Econst (Oaddrsymbol ___stringlit_10 (Int.repr 0))) :: nil))
        (Sexit (S O))))))
|}.

Definition f_make_N0 := {|
  fn_sig := (mksignature nil (Some AST.Tint) cc_default);
  fn_params := nil;
  fn_vars := (_n :: 240%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 240%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 4))) :: nil))
    (Sassign _n (Evar 240%positive)))
  (Sseq
    (Sstore Mint32 (Ebinop Oadd (Evar _n) (Econst (Ointconst (Int.repr 0))))
      (Econst (Ointconst (Int.repr 0))))
    (Sreturn (Some (Evar _n)))))
|}.

Definition f_make_Npos := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_p :: nil);
  fn_vars := (_n :: 241%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 241%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 8))) :: nil))
    (Sassign _n (Evar 241%positive)))
  (Sseq
    (Sstore Mint32 (Ebinop Oadd (Evar _n) (Econst (Ointconst (Int.repr 0))))
      (Econst (Ointconst (Int.repr 1))))
    (Sseq
      (Sstore Mint32
        (Ebinop Oadd (Evar _n) (Econst (Ointconst (Int.repr 4)))) (Evar _p))
      (Sreturn (Some (Evar _n))))))
|}.

Definition f_clone_N := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_n :: nil);
  fn_vars := (244%positive :: 243%positive :: 242%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sblock
  (Sblock
    (Sseq
      (Sblock
        (Sseq
          (Sblock
            (Sseq
              (Sblock
                (Sswitch false (Eload Mint32 (Evar _n))
                  ((0%Z, O) :: (1%Z, (S O)) :: nil)
                  (S (S O))))
              (Sseq
                (Scall (Some 242%positive)
                  (mksignature nil (Some AST.Tint) cc_default)
                  (Econst (Oaddrsymbol _make_N0 (Int.repr 0))) nil)
                (Sreturn (Some (Evar 242%positive))))))
          (Sseq
            (Sseq
              (Scall (Some 243%positive)
                (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
                (Econst (Oaddrsymbol _clone_positive (Int.repr 0)))
                ((Eload Mint32
                   (Ebinop Oadd (Evar _n) (Econst (Ointconst (Int.repr 4))))) ::
                 nil))
              (Scall (Some 244%positive)
                (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
                (Econst (Oaddrsymbol _make_Npos (Int.repr 0)))
                ((Evar 243%positive) :: nil)))
            (Sreturn (Some (Evar 244%positive))))))
      (Scall None (mksignature nil None cc_default)
        (Econst (Oaddrsymbol _abort (Int.repr 0))) nil))))
|}.

Definition f_N_of_uint := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_x :: nil);
  fn_vars := (247%positive :: 246%positive :: 245%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sifthenelse (Ebinop (Ocmpu Ceq) (Evar _x) (Econst (Ointconst (Int.repr 0))))
  (Sseq
    (Scall (Some 245%positive) (mksignature nil (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _make_N0 (Int.repr 0))) nil)
    (Sreturn (Some (Evar 245%positive))))
  (Sseq
    (Sseq
      (Scall (Some 246%positive)
        (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
        (Econst (Oaddrsymbol _uint_to_positive (Int.repr 0)))
        ((Evar _x) :: nil))
      (Scall (Some 247%positive)
        (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
        (Econst (Oaddrsymbol _make_Npos (Int.repr 0)))
        ((Evar 246%positive) :: nil)))
    (Sreturn (Some (Evar 247%positive)))))
|}.

Definition f_uint_of_N := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_n :: nil);
  fn_vars := (248%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sblock
  (Sblock
    (Sseq
      (Sblock
        (Sseq
          (Sblock
            (Sswitch false (Eload Mint32 (Evar _n))
              ((0%Z, O) :: (1%Z, (S O)) :: nil)
              (S (S O))))
          (Sreturn (Some (Econst (Ointconst (Int.repr 0)))))))
      (Sseq
        (Scall (Some 248%positive)
          (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
          (Econst (Oaddrsymbol _positive_to_uint (Int.repr 0)))
          ((Eload Mint32
             (Ebinop Oadd (Evar _n) (Econst (Ointconst (Int.repr 4))))) ::
           nil))
        (Sreturn (Some (Evar 248%positive)))))))
|}.

Definition f_print_N := {|
  fn_sig := (mksignature (AST.Tint :: nil) None cc_default);
  fn_params := (_n :: nil);
  fn_vars := nil;
  fn_stackspace := 0;
  fn_body :=
(Sblock
  (Sblock
    (Sseq
      (Sblock
        (Sseq
          (Sblock
            (Sswitch false (Eload Mint32 (Evar _n))
              ((0%Z, O) :: (1%Z, (S O)) :: nil)
              (S (S O))))
          (Sseq
            (Scall None
              (mksignature (AST.Tint :: nil) (Some AST.Tint)
                {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
              (Econst (Oaddrsymbol _printf (Int.repr 0)))
              ((Econst (Oaddrsymbol ___stringlit_14 (Int.repr 0))) :: nil))
            (Sexit (S (S O))))))
      (Sseq
        (Scall None
          (mksignature (AST.Tint :: nil) (Some AST.Tint)
            {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
          (Econst (Oaddrsymbol _printf (Int.repr 0)))
          ((Econst (Oaddrsymbol ___stringlit_13 (Int.repr 0))) :: nil))
        (Sseq
          (Scall None (mksignature (AST.Tint :: nil) None cc_default)
            (Econst (Oaddrsymbol _print_positive (Int.repr 0)))
            ((Eload Mint32
               (Ebinop Oadd (Evar _n) (Econst (Ointconst (Int.repr 4))))) ::
             nil))
          (Sseq
            (Scall None
              (mksignature (AST.Tint :: nil) (Some AST.Tint)
                {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
              (Econst (Oaddrsymbol _printf (Int.repr 0)))
              ((Econst (Oaddrsymbol ___stringlit_3 (Int.repr 0))) :: nil))
            (Sexit (S O))))))))
|}.

Definition f_make_closure := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default);
  fn_params := (_f :: nil);
  fn_vars := (_c :: 249%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Sseq
    (Scall (Some 249%positive)
      (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)
      (Econst (Oaddrsymbol _malloc (Int.repr 0)))
      ((Econst (Ointconst (Int.repr 4))) :: nil))
    (Sassign _c (Evar 249%positive)))
  (Sseq
    (Sstore Mint32 (Ebinop Oadd (Evar _c) (Econst (Ointconst (Int.repr 0))))
      (Evar _f))
    (Sreturn (Some (Evar _c)))))
|}.

Definition f_call := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (_f :: _a :: nil);
  fn_vars := (250%positive :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq
  (Scall (Some 250%positive)
    (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint) cc_default)
    (Eload Mint32 (Ebinop Oadd (Evar _f) (Econst (Ointconst (Int.repr 0)))))
    ((Evar _f) :: (Evar _a) :: nil))
  (Sreturn (Some (Evar 250%positive))))
|}.

Definition f_vcall := {|
  fn_sig := (mksignature (AST.Tint :: nil) (Some AST.Tint)
              {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|});
  fn_params := (_f :: nil);
  fn_vars := (_a :: 253%positive :: 252%positive :: 251%positive :: nil);
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
                    (Scall (Some 251%positive)
                      (mksignature (AST.Tint :: nil) (Some AST.Tint)
                        cc_default)
                      (Econst (Oaddrsymbol ___compcert_va_int32 (Int.repr 0)))
                      ((Econst (Oaddrstack (Int.repr 0))) :: nil))
                    (Sassign 252%positive (Evar 251%positive)))
                  (Sassign _a (Evar 252%positive)))
                (Sifthenelse (Ebinop (Ocmpu Cne) (Evar 252%positive)
                               (Econst (Ointconst (Int.repr 0))))
                  Sskip
                  (Sexit (S O))))
              (Sseq
                (Scall (Some 253%positive)
                  (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                    cc_default) (Econst (Oaddrsymbol _call (Int.repr 0)))
                  ((Evar _f) :: (Evar _a) :: nil))
                (Sassign _f (Evar 253%positive)))))))
      (Sreturn (Some (Evar _f))))))
|}.

Definition f_main := {|
  fn_sig := (mksignature nil (Some AST.Tint) cc_default);
  fn_params := nil;
  fn_vars := (_n_ :: _i :: _m_ :: _m :: 257%positive :: 256%positive ::
              255%positive :: 254%positive :: nil);
  fn_stackspace := 4;
  fn_body :=
(Sseq
  (Sseq
    (Scall None
      (mksignature (AST.Tint :: nil) (Some AST.Tint)
        {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
      (Econst (Oaddrsymbol _printf (Int.repr 0)))
      ((Econst (Oaddrsymbol ___stringlit_15 (Int.repr 0))) :: nil))
    (Sseq
      (Scall None
        (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
        (Econst (Oaddrsymbol _scanf (Int.repr 0)))
        ((Econst (Oaddrsymbol ___stringlit_16 (Int.repr 0))) ::
         (Econst (Oaddrstack (Int.repr 0))) :: nil))
      (Sseq
        (Sifthenelse (Ebinop (Ocmp Clt)
                       (Eload Mint32 (Econst (Oaddrstack (Int.repr 0))))
                       (Econst (Ointconst (Int.repr 0))))
          (Sseq
            (Scall None
              (mksignature (AST.Tint :: nil) (Some AST.Tint)
                {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
              (Econst (Oaddrsymbol _printf (Int.repr 0)))
              ((Econst (Oaddrsymbol ___stringlit_17 (Int.repr 0))) :: nil))
            (Sreturn (Some (Econst (Ointconst (Int.repr 1))))))
          Sskip)
        (Sseq
          (Sseq
            (Scall (Some 254%positive)
              (mksignature nil (Some AST.Tint) cc_default)
              (Econst (Oaddrsymbol _make_O (Int.repr 0))) nil)
            (Sassign _n_ (Evar 254%positive)))
          (Sseq
            (Sseq
              (Sassign _i (Econst (Ointconst (Int.repr 0))))
              (Sblock
                (Sloop
                  (Sseq
                    (Sblock
                      (Sseq
                        (Sifthenelse (Ebinop (Ocmp Clt) (Evar _i)
                                       (Eload Mint32
                                         (Econst (Oaddrstack (Int.repr 0)))))
                          Sskip
                          (Sexit (S O)))
                        (Sseq
                          (Scall (Some 255%positive)
                            (mksignature (AST.Tint :: nil) (Some AST.Tint)
                              cc_default)
                            (Econst (Oaddrsymbol _make_S (Int.repr 0)))
                            ((Evar _n_) :: nil))
                          (Sassign _n_ (Evar 255%positive)))))
                    (Sassign _i
                      (Ebinop Oadd (Evar _i)
                        (Econst (Ointconst (Int.repr 1)))))))))
            (Sseq
              (Scall None
                (mksignature (AST.Tint :: nil) (Some AST.Tint)
                  {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
                (Econst (Oaddrsymbol _printf (Int.repr 0)))
                ((Econst (Oaddrsymbol ___stringlit_18 (Int.repr 0))) :: nil))
              (Sseq
                (Scall None (mksignature (AST.Tint :: nil) None cc_default)
                  (Econst (Oaddrsymbol _print_nat (Int.repr 0)))
                  ((Evar _n_) :: nil))
                (Sseq
                  (Scall None
                    (mksignature (AST.Tint :: nil) (Some AST.Tint)
                      {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
                    (Econst (Oaddrsymbol _printf (Int.repr 0)))
                    ((Econst (Oaddrsymbol ___stringlit_19 (Int.repr 0))) ::
                     nil))
                  (Sseq
                    (Sseq
                      (Sseq
                        (Scall (Some 256%positive)
                          (mksignature (AST.Tint :: nil) (Some AST.Tint)
                            cc_default)
                          (Econst (Oaddrsymbol _make_closure (Int.repr 0)))
                          ((Econst (Oaddrsymbol _double_nat_elim (Int.repr 0))) ::
                           nil))
                        (Scall (Some 257%positive)
                          (mksignature
                            (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                            (Some AST.Tint)
                            {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
                          (Econst (Oaddrsymbol _vcall (Int.repr 0)))
                          ((Evar 256%positive) :: (Evar _n_) ::
                           (Econst (Ointconst (Int.repr 0))) :: nil)))
                      (Sassign _m_ (Evar 257%positive)))
                    (Sseq
                      (Scall None
                        (mksignature (AST.Tint :: nil) (Some AST.Tint)
                          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
                        (Econst (Oaddrsymbol _printf (Int.repr 0)))
                        ((Econst (Oaddrsymbol ___stringlit_20 (Int.repr 0))) ::
                         nil))
                      (Sseq
                        (Scall None
                          (mksignature (AST.Tint :: nil) None cc_default)
                          (Econst (Oaddrsymbol _print_nat (Int.repr 0)))
                          ((Evar _m_) :: nil))
                        (Sseq
                          (Scall None
                            (mksignature (AST.Tint :: nil) (Some AST.Tint)
                              {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
                            (Econst (Oaddrsymbol _printf (Int.repr 0)))
                            ((Econst (Oaddrsymbol ___stringlit_19 (Int.repr 0))) ::
                             nil))
                          (Sseq
                            (Sassign _m (Econst (Ointconst (Int.repr 0))))
                            (Sseq
                              (Sblock
                                (Sloop
                                  (Sblock
                                    (Sseq
                                      (Sifthenelse (Ebinop (Ocmp Ceq)
                                                     (Eload Mint32
                                                       (Evar _m_))
                                                     (Econst (Ointconst (Int.repr 1))))
                                        Sskip
                                        (Sexit (S O)))
                                      (Sseq
                                        (Sassign _m
                                          (Ebinop Oadd (Evar _m)
                                            (Econst (Ointconst (Int.repr 1)))))
                                        (Sassign _m_
                                          (Eload Mint32
                                            (Ebinop Oadd (Evar _m_)
                                              (Econst (Ointconst (Int.repr 4)))))))))))
                              (Sseq
                                (Scall None
                                  (mksignature (AST.Tint :: AST.Tint :: nil)
                                    (Some AST.Tint)
                                    {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})
                                  (Econst (Oaddrsymbol _printf (Int.repr 0)))
                                  ((Econst (Oaddrsymbol ___stringlit_21 (Int.repr 0))) ::
                                   (Evar _m) :: nil))
                                (Sreturn (Some (Econst (Ointconst (Int.repr 0))))))))))))))))))))
  (Sreturn (Some (Econst (Ointconst (Int.repr 0))))))
|}.

Definition prog : Cminor.program := {|
prog_defs :=
((_double_nat_elim, Gfun(Internal f_double_nat_elim)) ::
 (_double_nat_elim_0, Gfun(Internal f_double_nat_elim_0)) ::
 (_double_nat_elim_0_1, Gfun(Internal f_double_nat_elim_0_1)) ::
 (_double_nat_elim_elim0, Gfun(Internal f_double_nat_elim_elim0)) ::
 (_malloc, Gfun(External EF_malloc)) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_14, Gvar v___stringlit_14) ::
 (___stringlit_20, Gvar v___stringlit_20) ::
 (___stringlit_10, Gvar v___stringlit_10) ::
 (___stringlit_21, Gvar v___stringlit_21) ::
 (___stringlit_18, Gvar v___stringlit_18) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_13, Gvar v___stringlit_13) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_16, Gvar v___stringlit_16) ::
 (___stringlit_9, Gvar v___stringlit_9) ::
 (___stringlit_11, Gvar v___stringlit_11) ::
 (___stringlit_17, Gvar v___stringlit_17) ::
 (___stringlit_15, Gvar v___stringlit_15) ::
 (___stringlit_19, Gvar v___stringlit_19) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_8, Gvar v___stringlit_8) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_12, Gvar v___stringlit_12) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
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
 (_scanf,
   Gfun(External (EF_external "scanf"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})))) ::
 (_snprintf,
   Gfun(External (EF_external "snprintf"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})))) ::
 (_abort,
   Gfun(External (EF_external "abort" (mksignature nil None cc_default)))) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})))) ::
 (_localtime,
   Gfun(External (EF_external "localtime"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)))) ::
 (_time,
   Gfun(External (EF_external "time"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)))) ::
 (_time_buf, Gvar v_time_buf) :: (_get_time, Gfun(Internal f_get_time)) ::
 (_make_O, Gfun(Internal f_make_O)) :: (_make_S, Gfun(Internal f_make_S)) ::
 (_clone_nat, Gfun(Internal f_clone_nat)) ::
 (_nat_of_uint, Gfun(Internal f_nat_of_uint)) ::
 (_uint_of_nat, Gfun(Internal f_uint_of_nat)) ::
 (_print_nat, Gfun(Internal f_print_nat)) ::
 (_make_unit, Gfun(Internal f_make_unit)) ::
 (_make_true, Gfun(Internal f_make_true)) ::
 (_make_false, Gfun(Internal f_make_false)) ::
 (_int_of_bool, Gfun(Internal f_int_of_bool)) ::
 (_make_nil, Gfun(Internal f_make_nil)) ::
 (_make_cons, Gfun(Internal f_make_cons)) ::
 (_clone_list, Gfun(Internal f_clone_list)) ::
 (_print_list, Gfun(Internal f_print_list)) ::
 (_make_pair, Gfun(Internal f_make_pair)) ::
 (_clone_prod, Gfun(Internal f_clone_prod)) ::
 (_make_xI, Gfun(Internal f_make_xI)) ::
 (_make_xO, Gfun(Internal f_make_xO)) ::
 (_make_xH, Gfun(Internal f_make_xH)) ::
 (_clone_positive, Gfun(Internal f_clone_positive)) ::
 (_uint_to_positive, Gfun(Internal f_uint_to_positive)) ::
 (_positive_to_uint, Gfun(Internal f_positive_to_uint)) ::
 (_print_positive, Gfun(Internal f_print_positive)) ::
 (_make_N0, Gfun(Internal f_make_N0)) ::
 (_make_Npos, Gfun(Internal f_make_Npos)) ::
 (_clone_N, Gfun(Internal f_clone_N)) ::
 (_N_of_uint, Gfun(Internal f_N_of_uint)) ::
 (_uint_of_N, Gfun(Internal f_uint_of_N)) ::
 (_print_N, Gfun(Internal f_print_N)) ::
 (_make_closure, Gfun(Internal f_make_closure)) ::
 (_call, Gfun(Internal f_call)) :: (_vcall, Gfun(Internal f_vcall)) ::
 (_main, Gfun(Internal f_main)) :: nil);
prog_public :=
(_main :: _double_nat_elim :: _vcall :: _call :: _make_closure :: _print_N ::
 _uint_of_N :: _N_of_uint :: _clone_N :: _make_Npos :: _make_N0 ::
 _print_positive :: _positive_to_uint :: _uint_to_positive ::
 _clone_positive :: _make_xH :: _make_xO :: _make_xI :: _clone_prod ::
 _make_pair :: _print_list :: _clone_list :: _make_cons :: _make_nil ::
 _int_of_bool :: _make_false :: _make_true :: _make_unit :: _print_nat ::
 _uint_of_nat :: _nat_of_uint :: _clone_nat :: _make_S :: _make_O ::
 _get_time :: _time :: _localtime :: _printf :: _abort :: _malloc ::
 _snprintf :: _scanf :: ___builtin_debug :: ___builtin_nop ::
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

