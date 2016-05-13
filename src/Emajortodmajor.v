Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Switch.
Require Import compcert.common.Smallstep.

Require Import List.
Import ListNotations.
Require Import Arith.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Emajor.
Require Import Dmajor.

(* given an address, addresses of the nested values *)
Fixpoint arg_addrs (b : block) (ofs : int) (l : list value) : list (value * val) :=
  match l with
  | nil => nil
  | v :: vs =>
    let ofs' := Int.add ofs (Int.repr 4) in
    (v, Vptr b ofs') :: arg_addrs b ofs' vs
  end.

Fixpoint load_all (l : list (value * val)) (m : mem) : option (list (value * val)) :=
  match l with
  | nil => Some nil
  | (hval,vaddr) :: rest =>
    match Mem.loadv Mint32 m vaddr with
    | None => None
    | Some v' =>
      match load_all rest m with
      | None => None
      | Some res => Some ((hval,v') :: res)
      end
    end
  end.
                     

(* mapping of high level values to low level values *)
Inductive value_inject (ge : genv) (m : mem) : value -> val -> Prop :=
| inj_constr :
    forall b ofs n values l',
      Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint n) -> (* correct tag *)
      load_all (arg_addrs b ofs values) m = Some l' -> (* one more deref for args *)
      (forall a b, In (a,b) l' -> value_inject ge m a b) -> (* all args inject *)
      value_inject ge m (Constr (Int.unsigned n) values) (Vptr b ofs)
| inj_closure :
    forall b ofs bcode f fname values l',
      Mem.loadv Mint32 m (Vptr b ofs) = Some (Vptr bcode Int.zero) ->
      Genv.find_funct_ptr ge bcode = Some f -> (* legit pointer to some code *)
      Genv.find_symbol ge fname = Some bcode -> (* name we have points to same code *)
      load_all (arg_addrs b ofs values) m = Some l' -> (* one more deref for args *)
      (forall a b, In (a,b) l' -> value_inject ge m a b) -> (* all args inject *)
      value_inject ge m (Close fname values) (Vptr b ofs).


