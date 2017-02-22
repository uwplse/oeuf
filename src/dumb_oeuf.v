Require Import compcert.backend.Cminor.
Require Import compcert.common.AST.
Require Import BinNums.
Require Import compcert.lib.Integers.
Require Import List.
Import ListNotations.

Local Open Scope Z_scope.

Definition _t : ident := 85%positive.
Definition ___builtin_ctzll : ident := 65%positive.
Definition ___compcert_va_int32 : ident := 40%positive.
Definition __switch_target : ident := 112%positive.
Definition _main : ident := 110%positive.
Definition _n : ident := 16%positive.
Definition ___builtin_va_copy : ident := 38%positive.
Definition ___i64_stod : ident := 46%positive.
Definition ___builtin_fmadd : ident := 69%positive.
Definition ___builtin_clzll : ident := 62%positive.
Definition ___i64_shl : ident := 54%positive.
Definition __x0 : ident := 111%positive.
Definition __682 : ident := 22%positive.
Definition _tm : ident := 12%positive.
Definition _make_nat : ident := 92%positive.
Definition _id_closure : ident := 108%positive.
Definition _ap : ident := 104%positive.
Definition ___builtin_ctz : ident := 63%positive.
Definition ___tm_gmtoff : ident := 10%positive.
Definition ___i64_dtos : ident := 44%positive.
Definition _tm_hour : ident := 3%positive.
Definition _tm_min : ident := 2%positive.
Definition _tm_sec : ident := 1%positive.
Definition ___builtin_fabs : ident := 31%positive.
Definition _get_time : ident := 88%positive.
Definition _printf : ident := 79%positive.
Definition ___builtin_fnmsub : ident := 72%positive.
Definition ___i64_utof : ident := 49%positive.
Definition ___builtin_fsqrt : ident := 66%positive.
Definition ___builtin_bswap16 : ident := 59%positive.
Definition _tm_mday : ident := 4%positive.
Definition ___stringlit_3 : ident := 109%positive.
Definition ___builtin_debug : ident := 78%positive.
Definition _result : ident := 94%positive.
Definition ___builtin_fmin : ident := 68%positive.
Definition ___builtin_bswap32 : ident := 58%positive.
Definition _cons : ident := 28%positive.
Definition __self : ident := 113%positive.
Definition _a : ident := 102%positive.
Definition _tm_wday : ident := 7%positive.
Definition _call : ident := 103%positive.
Definition _l : ident := 99%positive.
Definition _bool : ident := 21%positive.
Definition _O : ident := 18%positive.
Definition _print_list_nat : ident := 101%positive.
Definition _ptr : ident := 89%positive.
Definition ___i64_dtou : ident := 45%positive.
Definition _id : ident := 106%positive.
Definition _snprintf : ident := 80%positive.
Definition _tag : ident := 13%positive.
Definition _nil : ident := 27%positive.
Definition _time_buf : ident := 84%positive.
Definition _time : ident := 82%positive.
Definition ___builtin_annot : ident := 33%positive.
Definition ___i64_sar : ident := 56%positive.
Definition _next : ident := 25%positive.
Definition _nat : ident := 15%positive.
Definition ___builtin_clz : ident := 60%positive.
Definition ___stringlit_2 : ident := 100%positive.
Definition __arg : ident := 114%positive.
Definition _unit : ident := 20%positive.
Definition ___builtin_memcpy_aligned : ident := 32%positive.
Definition _read_nat : ident := 93%positive.
Definition _vcall : ident := 105%positive.
Definition ___builtin_fmsub : ident := 70%positive.
Definition _list : ident := 24%positive.
Definition _b : ident := 96%positive.
Definition ___builtin_fmax : ident := 67%positive.
Definition __658 : ident := 17%positive.
Definition _tm_yday : ident := 8%positive.
Definition _tm_mon : ident := 5%positive.
Definition ___builtin_read16_reversed : ident := 73%positive.
Definition ___i64_sdiv : ident := 50%positive.
Definition ___compcert_va_composite : ident := 43%positive.
Definition ___builtin_read32_reversed : ident := 74%positive.
Definition ___i64_umod : ident := 53%positive.
Definition ___i64_utod : ident := 47%positive.
Definition _zero_value : ident := 107%positive.
Definition ___builtin_bswap : ident := 57%positive.
Definition _tmp : ident := 91%positive.
Definition ___builtin_va_start : ident := 36%positive.
Definition __657 : ident := 14%positive.
Definition _tm_year : ident := 6%positive.
Definition _read_bool : ident := 98%positive.
Definition __683 : ident := 26%positive.
Definition _S : ident := 19%positive.
Definition ___builtin_va_end : ident := 39%positive.
Definition _i : ident := 90%positive.
Definition _localtime : ident := 83%positive.
Definition ___builtin_clzl : ident := 61%positive.
Definition ___tm_zone : ident := 11%positive.
Definition _make_bool : ident := 97%positive.
Definition ___builtin_va_arg : ident := 37%positive.
Definition _malloc : ident := 81%positive.
Definition ___builtin_write32_reversed : ident := 76%positive.
Definition _tm__1 : ident := 86%positive.
Definition ___compcert_va_float64 : ident := 42%positive.
Definition _tm_isdst : ident := 9%positive.
Definition ___builtin_ctzl : ident := 64%positive.
Definition ___i64_smod : ident := 52%positive.
Definition ___compcert_va_int64 : ident := 41%positive.
Definition ___stringlit_1 : ident := 87%positive.
Definition ___builtin_nop : ident := 77%positive.
Definition ___builtin_fnmadd : ident := 71%positive.
Definition ___builtin_write16_reversed : ident := 75%positive.
Definition ___builtin_annot_intval : ident := 34%positive.
Definition _f : ident := 29%positive.
Definition _make_unit : ident := 95%positive.
Definition ___i64_shr : ident := 55%positive.
Definition ___builtin_membar : ident := 35%positive.
Definition _closure : ident := 30%positive.
Definition _data : ident := 23%positive.
Definition ___i64_udiv : ident := 51%positive.
Definition ___i64_stof : ident := 48%positive.

Definition f_id := {|
  fn_sig := (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
              cc_default);
  fn_params := (__self :: __arg :: nil);
  fn_vars := (__x0 :: nil);
  fn_stackspace := 0;
  fn_body :=
(Sseq (Sassign __x0 (Evar __arg)) (Sreturn (Some (Evar __x0))))
|}.

Definition prog : Cminor.program := {|
prog_defs :=
((_id, Gfun(Internal f_id)) :: (_malloc, Gfun(External EF_malloc)) :: nil);
prog_public :=
(_id :: nil);
prog_main := _tm_sec;
|}.

