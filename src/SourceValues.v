Require Import oeuf.Common.
Require Import oeuf.HList.
Require Import oeuf.Utopia.
Require Import oeuf.OpaqueTypes.


Inductive type :=
| ADT : type_name -> type
| Arrow : type -> type -> type
.

Definition Opaque : opaque_type_name -> type :=
    fun oty => ADT (Topaque oty).


Definition type_eq_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
  decide equality; auto using type_name_eq_dec.
Defined.
Hint Resolve type_eq_dec : eq_dec.

(* Why is this not in Utopia? *)
(* Extend this if you want to extend Oeuf *)
Inductive constr_type : constr_name -> list type -> type_name -> Type :=
| CTO            : constr_type CO         []                          Tnat
| CTS            : constr_type CS         [ADT Tnat]                  Tnat

| CTtrue         : constr_type Ctrue      []                          Tbool
| CTfalse        : constr_type Cfalse     []                          Tbool

| CTnil ty       : constr_type Cnil       []                          (Tlist ty)
| CTcons ty      : constr_type Ccons      [ADT ty; ADT (Tlist ty)]    (Tlist ty)

| CTtt           : constr_type Ctt        []                          Tunit

| CTpair ty1 ty2 : constr_type Cpair      [ADT ty1; ADT ty2]          (Tpair ty1 ty2)

| CTsome ty      : constr_type Csome      [ADT ty]                    (Toption ty)
| CTnone ty      : constr_type Cnone      []                          (Toption ty)

| CTxI           : constr_type CxI        [ADT Tpositive]             Tpositive
| CTxO           : constr_type CxO        [ADT Tpositive]             Tpositive
| CTxH           : constr_type CxH        []                          Tpositive

| CTN0           : constr_type CN0        []                          TN
| CTNpos         : constr_type CNpos      [ADT Tpositive]             TN

| CTZ0           : constr_type CZ0        []                          TZ
| CTZpos         : constr_type CZpos      [ADT Tpositive]             TZ
| CTZneg         : constr_type CZneg      [ADT Tpositive]             TZ

| CTAscii       : constr_type CAscii      [ADT Tbool; ADT Tbool; ADT Tbool; ADT Tbool;ADT Tbool; ADT Tbool; ADT Tbool; ADT Tbool]   Tascii

(*| CTascii_0      : constr_type Cascii_0   []                          Tascii
| CTascii_1      : constr_type Cascii_1   []                          Tascii
| CTascii_2      : constr_type Cascii_2   []                          Tascii
| CTascii_3      : constr_type Cascii_3   []                          Tascii
| CTascii_4      : constr_type Cascii_4   []                          Tascii
| CTascii_5      : constr_type Cascii_5   []                          Tascii
| CTascii_6      : constr_type Cascii_6   []                          Tascii
| CTascii_7      : constr_type Cascii_7   []                          Tascii
| CTascii_8      : constr_type Cascii_8   []                          Tascii
| CTascii_9      : constr_type Cascii_9   []                          Tascii
| CTascii_10      : constr_type Cascii_10   []                          Tascii
| CTascii_11      : constr_type Cascii_11   []                          Tascii
| CTascii_12      : constr_type Cascii_12   []                          Tascii
| CTascii_13      : constr_type Cascii_13   []                          Tascii
| CTascii_14      : constr_type Cascii_14   []                          Tascii
| CTascii_15      : constr_type Cascii_15   []                          Tascii
| CTascii_16      : constr_type Cascii_16   []                          Tascii
| CTascii_17      : constr_type Cascii_17   []                          Tascii
| CTascii_18      : constr_type Cascii_18   []                          Tascii
| CTascii_19      : constr_type Cascii_19   []                          Tascii
| CTascii_20      : constr_type Cascii_20   []                          Tascii
| CTascii_21      : constr_type Cascii_21   []                          Tascii
| CTascii_22      : constr_type Cascii_22   []                          Tascii
| CTascii_23      : constr_type Cascii_23   []                          Tascii
| CTascii_24      : constr_type Cascii_24   []                          Tascii
| CTascii_25      : constr_type Cascii_25   []                          Tascii
| CTascii_26      : constr_type Cascii_26   []                          Tascii
| CTascii_27      : constr_type Cascii_27   []                          Tascii
| CTascii_28      : constr_type Cascii_28   []                          Tascii
| CTascii_29      : constr_type Cascii_29   []                          Tascii
| CTascii_30      : constr_type Cascii_30   []                          Tascii
| CTascii_31      : constr_type Cascii_31   []                          Tascii
| CTascii_32      : constr_type Cascii_32   []                          Tascii
| CTascii_33      : constr_type Cascii_33   []                          Tascii
| CTascii_34      : constr_type Cascii_34   []                          Tascii
| CTascii_35      : constr_type Cascii_35   []                          Tascii
| CTascii_36      : constr_type Cascii_36   []                          Tascii
| CTascii_37      : constr_type Cascii_37   []                          Tascii
| CTascii_38      : constr_type Cascii_38   []                          Tascii
| CTascii_39      : constr_type Cascii_39   []                          Tascii
| CTascii_40      : constr_type Cascii_40   []                          Tascii
| CTascii_41      : constr_type Cascii_41   []                          Tascii
| CTascii_42      : constr_type Cascii_42   []                          Tascii
| CTascii_43      : constr_type Cascii_43   []                          Tascii
| CTascii_44      : constr_type Cascii_44   []                          Tascii
| CTascii_45      : constr_type Cascii_45   []                          Tascii
| CTascii_46      : constr_type Cascii_46   []                          Tascii
| CTascii_47      : constr_type Cascii_47   []                          Tascii
| CTascii_48      : constr_type Cascii_48   []                          Tascii
| CTascii_49      : constr_type Cascii_49   []                          Tascii
| CTascii_50      : constr_type Cascii_50   []                          Tascii
| CTascii_51      : constr_type Cascii_51   []                          Tascii
| CTascii_52      : constr_type Cascii_52   []                          Tascii
| CTascii_53      : constr_type Cascii_53   []                          Tascii
| CTascii_54      : constr_type Cascii_54   []                          Tascii
| CTascii_55      : constr_type Cascii_55   []                          Tascii
| CTascii_56      : constr_type Cascii_56   []                          Tascii
| CTascii_57      : constr_type Cascii_57   []                          Tascii
| CTascii_58      : constr_type Cascii_58   []                          Tascii
| CTascii_59      : constr_type Cascii_59   []                          Tascii
| CTascii_60      : constr_type Cascii_60   []                          Tascii
| CTascii_61      : constr_type Cascii_61   []                          Tascii
| CTascii_62      : constr_type Cascii_62   []                          Tascii
| CTascii_63      : constr_type Cascii_63   []                          Tascii
| CTascii_64      : constr_type Cascii_64   []                          Tascii
| CTascii_65      : constr_type Cascii_65   []                          Tascii
| CTascii_66      : constr_type Cascii_66   []                          Tascii
| CTascii_67      : constr_type Cascii_67   []                          Tascii
| CTascii_68      : constr_type Cascii_68   []                          Tascii
| CTascii_69      : constr_type Cascii_69   []                          Tascii
| CTascii_70      : constr_type Cascii_70   []                          Tascii
| CTascii_71      : constr_type Cascii_71   []                          Tascii
| CTascii_72      : constr_type Cascii_72   []                          Tascii
| CTascii_73      : constr_type Cascii_73   []                          Tascii
| CTascii_74      : constr_type Cascii_74   []                          Tascii
| CTascii_75      : constr_type Cascii_75   []                          Tascii
| CTascii_76      : constr_type Cascii_76   []                          Tascii
| CTascii_77      : constr_type Cascii_77   []                          Tascii
| CTascii_78      : constr_type Cascii_78   []                          Tascii
| CTascii_79      : constr_type Cascii_79   []                          Tascii
| CTascii_80      : constr_type Cascii_80   []                          Tascii
| CTascii_81      : constr_type Cascii_81   []                          Tascii
| CTascii_82      : constr_type Cascii_82   []                          Tascii
| CTascii_83      : constr_type Cascii_83   []                          Tascii
| CTascii_84      : constr_type Cascii_84   []                          Tascii
| CTascii_85      : constr_type Cascii_85   []                          Tascii
| CTascii_86      : constr_type Cascii_86   []                          Tascii
| CTascii_87      : constr_type Cascii_87   []                          Tascii
| CTascii_88      : constr_type Cascii_88   []                          Tascii
| CTascii_89      : constr_type Cascii_89   []                          Tascii
| CTascii_90      : constr_type Cascii_90   []                          Tascii
| CTascii_91      : constr_type Cascii_91   []                          Tascii
| CTascii_92      : constr_type Cascii_92   []                          Tascii
| CTascii_93      : constr_type Cascii_93   []                          Tascii
| CTascii_94      : constr_type Cascii_94   []                          Tascii
| CTascii_95      : constr_type Cascii_95   []                          Tascii
| CTascii_96      : constr_type Cascii_96   []                          Tascii
| CTascii_97      : constr_type Cascii_97   []                          Tascii
| CTascii_98      : constr_type Cascii_98   []                          Tascii
| CTascii_99      : constr_type Cascii_99   []                          Tascii
| CTascii_100      : constr_type Cascii_100   []                          Tascii
| CTascii_101      : constr_type Cascii_101   []                          Tascii
| CTascii_102      : constr_type Cascii_102   []                          Tascii
| CTascii_103      : constr_type Cascii_103   []                          Tascii
| CTascii_104      : constr_type Cascii_104   []                          Tascii
| CTascii_105      : constr_type Cascii_105   []                          Tascii
| CTascii_106      : constr_type Cascii_106   []                          Tascii
| CTascii_107      : constr_type Cascii_107   []                          Tascii
| CTascii_108      : constr_type Cascii_108   []                          Tascii
| CTascii_109      : constr_type Cascii_109   []                          Tascii
| CTascii_110      : constr_type Cascii_110   []                          Tascii
| CTascii_111      : constr_type Cascii_111   []                          Tascii
| CTascii_112      : constr_type Cascii_112   []                          Tascii
| CTascii_113      : constr_type Cascii_113   []                          Tascii
| CTascii_114      : constr_type Cascii_114   []                          Tascii
| CTascii_115      : constr_type Cascii_115   []                          Tascii
| CTascii_116      : constr_type Cascii_116   []                          Tascii
| CTascii_117      : constr_type Cascii_117   []                          Tascii
| CTascii_118      : constr_type Cascii_118   []                          Tascii
| CTascii_119      : constr_type Cascii_119   []                          Tascii
| CTascii_120      : constr_type Cascii_120   []                          Tascii
| CTascii_121      : constr_type Cascii_121   []                          Tascii
| CTascii_122      : constr_type Cascii_122   []                          Tascii
| CTascii_123      : constr_type Cascii_123   []                          Tascii
| CTascii_124      : constr_type Cascii_124   []                          Tascii
| CTascii_125      : constr_type Cascii_125   []                          Tascii
| CTascii_126      : constr_type Cascii_126   []                          Tascii
| CTascii_127      : constr_type Cascii_127   []                          Tascii*)

.


Section value.
(* since these types make hlists of recursive calls, the auto-generated schemes are garbage. *)
Local Unset Elimination Schemes.

Inductive value {G : list (type * list type * type)} : type -> Type :=
| VConstr : forall {ty ctor arg_tys} (ct : constr_type ctor arg_tys ty),
        hlist (value) arg_tys ->
        value (ADT ty)
| VClose : forall {arg_ty free_tys ret_ty},
        member (arg_ty, free_tys, ret_ty) G ->
        hlist (value) free_tys ->
        value (Arrow arg_ty ret_ty)
| VOpaque : forall {oty},
        opaque_type_denote oty ->
        value (ADT (Topaque oty))
.

End value.
Implicit Arguments value.


Fixpoint type_denote (ty : type) : Type :=
  match ty with
  | ADT tyn => type_name_denote tyn
  | Arrow ty1 ty2 => type_denote ty1 -> type_denote ty2
  end.

Definition func_type_denote (fty : type * list type * type) : Type :=
    let '(arg_ty, free_tys, ret_ty) := fty in
    hlist type_denote free_tys -> type_denote arg_ty -> type_denote ret_ty.


(* Extend me if you want to extend Oeuf *)
Definition constr_denote {arg_tys ty c} (ct : constr_type c arg_tys ty) :
  hlist type_denote arg_tys -> type_denote (ADT ty) :=
  match ct with
  | CTO => fun _ => 0
  | CTS => fun h => S (hhead h)

  | CTtrue => fun _ => true
  | CTfalse => fun _ => false

  | CTnil _ => fun _ => []
  | CTcons _ => fun h => cons (hhead h) (hhead (htail h))

  | CTtt => fun _ => tt

  | CTpair _ _ => fun h => (hhead h, hhead (htail h))

  | CTsome _ => fun h => Some (hhead h)
  | CTnone _ => fun h => None

  | CTxI => fun h => xI (hhead h)
  | CTxO => fun h => xO (hhead h)
  | CTxH => fun h => xH

  | CTN0 => fun h => N0
  | CTNpos => fun h => Npos (hhead h)

  | CTZ0 => fun h => Z0
  | CTZpos => fun h => Zpos (hhead h)
  | CTZneg => fun h => Zneg (hhead h)

  | CTAscii => fun h => Ascii.Ascii ((hhead h) : bool)
                                     (hhead (htail h))
                                     (hhead (htail (htail h)))
                                     (hhead (htail (htail (htail h))))
                                     (hhead (htail (htail (htail (htail h)))))
                                     (hhead (htail (htail (htail (htail (htail h))))))
                                     (hhead (htail (htail (htail (htail (htail (htail h)))))))
                                     (hhead (htail (htail (htail (htail (htail (htail (htail h))))))))

(*  | CTascii_0 => fun _ => ascii_0
  | CTascii_1 => fun _ => ascii_1
  | CTascii_2 => fun _ => ascii_2
  | CTascii_3 => fun _ => ascii_3
  | CTascii_4 => fun _ => ascii_4
  | CTascii_5 => fun _ => ascii_5
  | CTascii_6 => fun _ => ascii_6
  | CTascii_7 => fun _ => ascii_7
  | CTascii_8 => fun _ => ascii_8
  | CTascii_9 => fun _ => ascii_9
  | CTascii_10 => fun _ => ascii_10
  | CTascii_11 => fun _ => ascii_11
  | CTascii_12 => fun _ => ascii_12
  | CTascii_13 => fun _ => ascii_13
  | CTascii_14 => fun _ => ascii_14
  | CTascii_15 => fun _ => ascii_15
  | CTascii_16 => fun _ => ascii_16
  | CTascii_17 => fun _ => ascii_17
  | CTascii_18 => fun _ => ascii_18
  | CTascii_19 => fun _ => ascii_19
  | CTascii_20 => fun _ => ascii_20
  | CTascii_21 => fun _ => ascii_21
  | CTascii_22 => fun _ => ascii_22
  | CTascii_23 => fun _ => ascii_23
  | CTascii_24 => fun _ => ascii_24
  | CTascii_25 => fun _ => ascii_25
  | CTascii_26 => fun _ => ascii_26
  | CTascii_27 => fun _ => ascii_27
  | CTascii_28 => fun _ => ascii_28
  | CTascii_29 => fun _ => ascii_29
  | CTascii_30 => fun _ => ascii_30
  | CTascii_31 => fun _ => ascii_31
  | CTascii_32 => fun _ => ascii_32
  | CTascii_33 => fun _ => ascii_33
  | CTascii_34 => fun _ => ascii_34
  | CTascii_35 => fun _ => ascii_35
  | CTascii_36 => fun _ => ascii_36
  | CTascii_37 => fun _ => ascii_37
  | CTascii_38 => fun _ => ascii_38
  | CTascii_39 => fun _ => ascii_39
  | CTascii_40 => fun _ => ascii_40
  | CTascii_41 => fun _ => ascii_41
  | CTascii_42 => fun _ => ascii_42
  | CTascii_43 => fun _ => ascii_43
  | CTascii_44 => fun _ => ascii_44
  | CTascii_45 => fun _ => ascii_45
  | CTascii_46 => fun _ => ascii_46
  | CTascii_47 => fun _ => ascii_47
  | CTascii_48 => fun _ => ascii_48
  | CTascii_49 => fun _ => ascii_49
  | CTascii_50 => fun _ => ascii_50
  | CTascii_51 => fun _ => ascii_51
  | CTascii_52 => fun _ => ascii_52
  | CTascii_53 => fun _ => ascii_53
  | CTascii_54 => fun _ => ascii_54
  | CTascii_55 => fun _ => ascii_55
  | CTascii_56 => fun _ => ascii_56
  | CTascii_57 => fun _ => ascii_57
  | CTascii_58 => fun _ => ascii_58
  | CTascii_59 => fun _ => ascii_59
  | CTascii_60 => fun _ => ascii_60
  | CTascii_61 => fun _ => ascii_61
  | CTascii_62 => fun _ => ascii_62
  | CTascii_63 => fun _ => ascii_63
  | CTascii_64 => fun _ => ascii_64
  | CTascii_65 => fun _ => ascii_65
  | CTascii_66 => fun _ => ascii_66
  | CTascii_67 => fun _ => ascii_67
  | CTascii_68 => fun _ => ascii_68
  | CTascii_69 => fun _ => ascii_69
  | CTascii_70 => fun _ => ascii_70
  | CTascii_71 => fun _ => ascii_71
  | CTascii_72 => fun _ => ascii_72
  | CTascii_73 => fun _ => ascii_73
  | CTascii_74 => fun _ => ascii_74
  | CTascii_75 => fun _ => ascii_75
  | CTascii_76 => fun _ => ascii_76
  | CTascii_77 => fun _ => ascii_77
  | CTascii_78 => fun _ => ascii_78
  | CTascii_79 => fun _ => ascii_79
  | CTascii_80 => fun _ => ascii_80
  | CTascii_81 => fun _ => ascii_81
  | CTascii_82 => fun _ => ascii_82
  | CTascii_83 => fun _ => ascii_83
  | CTascii_84 => fun _ => ascii_84
  | CTascii_85 => fun _ => ascii_85
  | CTascii_86 => fun _ => ascii_86
  | CTascii_87 => fun _ => ascii_87
  | CTascii_88 => fun _ => ascii_88
  | CTascii_89 => fun _ => ascii_89
  | CTascii_90 => fun _ => ascii_90
  | CTascii_91 => fun _ => ascii_91
  | CTascii_92 => fun _ => ascii_92
  | CTascii_93 => fun _ => ascii_93
  | CTascii_94 => fun _ => ascii_94
  | CTascii_95 => fun _ => ascii_95
  | CTascii_96 => fun _ => ascii_96
  | CTascii_97 => fun _ => ascii_97
  | CTascii_98 => fun _ => ascii_98
  | CTascii_99 => fun _ => ascii_99
  | CTascii_100 => fun _ => ascii_100
  | CTascii_101 => fun _ => ascii_101
  | CTascii_102 => fun _ => ascii_102
  | CTascii_103 => fun _ => ascii_103
  | CTascii_104 => fun _ => ascii_104
  | CTascii_105 => fun _ => ascii_105
  | CTascii_106 => fun _ => ascii_106
  | CTascii_107 => fun _ => ascii_107
  | CTascii_108 => fun _ => ascii_108
  | CTascii_109 => fun _ => ascii_109
  | CTascii_110 => fun _ => ascii_110
  | CTascii_111 => fun _ => ascii_111
  | CTascii_112 => fun _ => ascii_112
  | CTascii_113 => fun _ => ascii_113
  | CTascii_114 => fun _ => ascii_114
  | CTascii_115 => fun _ => ascii_115
  | CTascii_116 => fun _ => ascii_116
  | CTascii_117 => fun _ => ascii_117
  | CTascii_118 => fun _ => ascii_118
  | CTascii_119 => fun _ => ascii_119
  | CTascii_120 => fun _ => ascii_120
  | CTascii_121 => fun _ => ascii_121
  | CTascii_122 => fun _ => ascii_122
  | CTascii_123 => fun _ => ascii_123
  | CTascii_124 => fun _ => ascii_124
  | CTascii_125 => fun _ => ascii_125
  | CTascii_126 => fun _ => ascii_126
  | CTascii_127 => fun _ => ascii_127*)
  end.

Definition value_denote
        {G} (g : hlist func_type_denote G) :
        forall {ty}, value G ty -> type_denote ty :=
    let fix go {ty} (v : value G ty) : type_denote ty :=
        let fix go_hlist {tys} (vs : hlist (value G) tys) : hlist type_denote tys :=
            match vs with
            | hnil => hnil
            | hcons v vs => hcons (go v) (go_hlist vs)
            end in
        match v with
        | VConstr ct args => constr_denote ct (go_hlist args)
        | VClose mb free =>
                let func := hget g mb in
                let free' := go_hlist free in
                fun x => func free' x
        | VOpaque v => v
        end in @go.

Definition value_hlist_denote
        {G} (g : hlist func_type_denote G) :
        forall {tys}, hlist (value G) tys -> hlist type_denote tys :=
    let go := @value_denote G g in
    let fix go_hlist {tys} (vs : hlist (value G) tys) : hlist type_denote tys :=
        match vs with
        | hnil => hnil
        | hcons v vs => hcons (go _ v) (go_hlist vs)
        end in @go_hlist.



(* induction schemes for value *)

Definition value_rect_mut_comb G
        (P : forall {ty}, value G ty -> Type)
        (Pl : forall {tys}, hlist (value G) tys -> Type)
    (HVConstr : forall {ty ctor arg_tys} (ct : constr_type ctor arg_tys ty) args,
        Pl args -> P (VConstr ct args))
    (HVClose : forall {arg_ty free_tys ret_ty} (mb : member (arg_ty, free_tys, ret_ty) G) free,
        Pl free -> P (VClose mb free))
    (HVOpaque : forall {oty} (v : opaque_type_denote oty), P (VOpaque v))
    (Hhnil : Pl hnil)
    (Hhcons : forall {ty tys} (v : value G ty) (vs : hlist (value G) tys),
        P v -> Pl vs -> Pl (hcons v vs)) :
    (forall {ty} (v : value G ty), P v) *
    (forall {tys} (v : hlist (value G) tys), Pl v) :=
    let fix go {ty} (v : value G ty) :=
        let fix go_hlist {tys} (vs : hlist (value G) tys) :=
            match vs as vs_ return Pl vs_ with
            | hnil => Hhnil
            | hcons v vs => Hhcons v vs (go v) (go_hlist vs)
            end in
        match v as v_ return P v_ with
        | VConstr ct args => HVConstr ct args (go_hlist args)
        | VClose mb free => HVClose mb free (go_hlist free)
        | VOpaque v => HVOpaque v
        end in
    let fix go_hlist {tys} (vs : hlist (value G) tys) :=
        match vs as vs_ return Pl vs_ with
        | hnil => Hhnil
        | hcons v vs => Hhcons v vs (go v) (go_hlist vs)
        end in
    (@go, @go_hlist).

Definition value_rect_mut G P Pl HVConstr HVClose HVOpaque Hhnil Hhcons :=
    fst (value_rect_mut_comb G P Pl HVConstr HVClose HVOpaque Hhnil Hhcons).


(* dependent case analysis scheme for values *)
Lemma case_value_opaque :
  forall G o (P : value G (Opaque o) -> Type),
    (forall ov : opaque_type_denote o, P (VOpaque ov)) ->
    forall v, P v.
Proof.
  intros G o P H v.
  revert P H.
  refine (match v with
         | VConstr ct _ => _
         | VOpaque _ => _
         end).
  - destruct t; try exact idProp. inversion ct.
  - auto.
Qed.
