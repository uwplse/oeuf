Require Import ZArith.
Require Import oeuf.FastAscii.
Require Export oeuf.FastAscii.

Require Import Ascii.

(* All types present in Oeuf *)
(* In order to add types to Oeuf, extend this datatype *)
Inductive type_name :=
| Tnat
| Tbool
| Tlist : type_name -> type_name
| Tunit
| Tpair : type_name -> type_name -> type_name
| Toption : type_name -> type_name
| Tpositive
| TN
| TZ
(*| Tascii (* FastAscii *)*)
| Tascii (* Coq's builtin ascii *)    
.

Definition type_name_eq_dec (tn1 tn2 : type_name) : {tn1 = tn2} + {tn1 <> tn2}.
  decide equality.
Defined.

(* Denotation function for Oeuf types *)
Fixpoint type_name_denote (tyn : type_name) : Type :=
  match tyn with
  | Tbool => bool
  | Tnat => nat
  | Tlist tyn' => list (type_name_denote tyn')
  | Tunit => unit
  | Tpair ty1 ty2 => type_name_denote ty1 * type_name_denote ty2
  | Toption ty => option (type_name_denote ty)
  | Tpositive => positive
  | TN => N
  | TZ => Z
(*  | Tascii => FastAscii.ascii*)
  | Tascii => Ascii.ascii
  end.

(* All constructors in Oeuf *)
Inductive constr_name :=
| CS
| CO
| Ctrue
| Cfalse
| Cnil
| Ccons
| Ctt
| Cpair
| Csome
| Cnone
| CxI
| CxO
| CxH
| CN0
| CNpos
| CZ0
| CZpos
| CZneg
(*| Cascii_0
| Cascii_1
| Cascii_2
| Cascii_3
| Cascii_4
| Cascii_5
| Cascii_6
| Cascii_7
| Cascii_8
| Cascii_9
| Cascii_10
| Cascii_11
| Cascii_12
| Cascii_13
| Cascii_14
| Cascii_15
| Cascii_16
| Cascii_17
| Cascii_18
| Cascii_19
| Cascii_20
| Cascii_21
| Cascii_22
| Cascii_23
| Cascii_24
| Cascii_25
| Cascii_26
| Cascii_27
| Cascii_28
| Cascii_29
| Cascii_30
| Cascii_31
| Cascii_32
| Cascii_33
| Cascii_34
| Cascii_35
| Cascii_36
| Cascii_37
| Cascii_38
| Cascii_39
| Cascii_40
| Cascii_41
| Cascii_42
| Cascii_43
| Cascii_44
| Cascii_45
| Cascii_46
| Cascii_47
| Cascii_48
| Cascii_49
| Cascii_50
| Cascii_51
| Cascii_52
| Cascii_53
| Cascii_54
| Cascii_55
| Cascii_56
| Cascii_57
| Cascii_58
| Cascii_59
| Cascii_60
| Cascii_61
| Cascii_62
| Cascii_63
| Cascii_64
| Cascii_65
| Cascii_66
| Cascii_67
| Cascii_68
| Cascii_69
| Cascii_70
| Cascii_71
| Cascii_72
| Cascii_73
| Cascii_74
| Cascii_75
| Cascii_76
| Cascii_77
| Cascii_78
| Cascii_79
| Cascii_80
| Cascii_81
| Cascii_82
| Cascii_83
| Cascii_84
| Cascii_85
| Cascii_86
| Cascii_87
| Cascii_88
| Cascii_89
| Cascii_90
| Cascii_91
| Cascii_92
| Cascii_93
| Cascii_94
| Cascii_95
| Cascii_96
| Cascii_97
| Cascii_98
| Cascii_99
| Cascii_100
| Cascii_101
| Cascii_102
| Cascii_103
| Cascii_104
| Cascii_105
| Cascii_106
| Cascii_107
| Cascii_108
| Cascii_109
| Cascii_110
| Cascii_111
| Cascii_112
| Cascii_113
| Cascii_114
| Cascii_115
| Cascii_116
| Cascii_117
| Cascii_118
| Cascii_119
| Cascii_120
| Cascii_121
| Cascii_122
| Cascii_123
| Cascii_124
| Cascii_125
| Cascii_126
| Cascii_127*)
| CAscii
.

Definition constr_name_eq_dec (cn1 cn2 : constr_name) : {cn1 = cn2} + {cn1 <> cn2}.
  decide equality.
Defined.

(* Index of each constructor within its type *)
(* each constructor of the same type must have a unique index within that type *)
Definition constructor_index ctor : nat :=
    match ctor with
    | CO => 0
    | CS => 1

    | Ctrue => 0
    | Cfalse => 1

    | Cnil => 0
    | Ccons => 1

    | Ctt => 0

    | Cpair => 0

    | Csome => 0
    | Cnone => 1

    | CxI => 0
    | CxO => 1
    | CxH => 2

    | CN0 => 0
    | CNpos => 1

    | CZ0 => 0
    | CZpos => 1
    | CZneg => 2

(*    | Cascii_0 => 0
    | Cascii_1 => 1
    | Cascii_2 => 2
    | Cascii_3 => 3
    | Cascii_4 => 4
    | Cascii_5 => 5
    | Cascii_6 => 6
    | Cascii_7 => 7
    | Cascii_8 => 8
    | Cascii_9 => 9
    | Cascii_10 => 10
    | Cascii_11 => 11
    | Cascii_12 => 12
    | Cascii_13 => 13
    | Cascii_14 => 14
    | Cascii_15 => 15
    | Cascii_16 => 16
    | Cascii_17 => 17
    | Cascii_18 => 18
    | Cascii_19 => 19
    | Cascii_20 => 20
    | Cascii_21 => 21
    | Cascii_22 => 22
    | Cascii_23 => 23
    | Cascii_24 => 24
    | Cascii_25 => 25
    | Cascii_26 => 26
    | Cascii_27 => 27
    | Cascii_28 => 28
    | Cascii_29 => 29
    | Cascii_30 => 30
    | Cascii_31 => 31
    | Cascii_32 => 32
    | Cascii_33 => 33
    | Cascii_34 => 34
    | Cascii_35 => 35
    | Cascii_36 => 36
    | Cascii_37 => 37
    | Cascii_38 => 38
    | Cascii_39 => 39
    | Cascii_40 => 40
    | Cascii_41 => 41
    | Cascii_42 => 42
    | Cascii_43 => 43
    | Cascii_44 => 44
    | Cascii_45 => 45
    | Cascii_46 => 46
    | Cascii_47 => 47
    | Cascii_48 => 48
    | Cascii_49 => 49
    | Cascii_50 => 50
    | Cascii_51 => 51
    | Cascii_52 => 52
    | Cascii_53 => 53
    | Cascii_54 => 54
    | Cascii_55 => 55
    | Cascii_56 => 56
    | Cascii_57 => 57
    | Cascii_58 => 58
    | Cascii_59 => 59
    | Cascii_60 => 60
    | Cascii_61 => 61
    | Cascii_62 => 62
    | Cascii_63 => 63
    | Cascii_64 => 64
    | Cascii_65 => 65
    | Cascii_66 => 66
    | Cascii_67 => 67
    | Cascii_68 => 68
    | Cascii_69 => 69
    | Cascii_70 => 70
    | Cascii_71 => 71
    | Cascii_72 => 72
    | Cascii_73 => 73
    | Cascii_74 => 74
    | Cascii_75 => 75
    | Cascii_76 => 76
    | Cascii_77 => 77
    | Cascii_78 => 78
    | Cascii_79 => 79
    | Cascii_80 => 80
    | Cascii_81 => 81
    | Cascii_82 => 82
    | Cascii_83 => 83
    | Cascii_84 => 84
    | Cascii_85 => 85
    | Cascii_86 => 86
    | Cascii_87 => 87
    | Cascii_88 => 88
    | Cascii_89 => 89
    | Cascii_90 => 90
    | Cascii_91 => 91
    | Cascii_92 => 92
    | Cascii_93 => 93
    | Cascii_94 => 94
    | Cascii_95 => 95
    | Cascii_96 => 96
    | Cascii_97 => 97
    | Cascii_98 => 98
    | Cascii_99 => 99
    | Cascii_100 => 100
    | Cascii_101 => 101
    | Cascii_102 => 102
    | Cascii_103 => 103
    | Cascii_104 => 104
    | Cascii_105 => 105
    | Cascii_106 => 106
    | Cascii_107 => 107
    | Cascii_108 => 108
    | Cascii_109 => 109
    | Cascii_110 => 110
    | Cascii_111 => 111
    | Cascii_112 => 112
    | Cascii_113 => 113
    | Cascii_114 => 114
    | Cascii_115 => 115
    | Cascii_116 => 116
    | Cascii_117 => 117
    | Cascii_118 => 118
    | Cascii_119 => 119
    | Cascii_120 => 120
    | Cascii_121 => 121
    | Cascii_122 => 122
    | Cascii_123 => 123
    | Cascii_124 => 124
    | Cascii_125 => 125
    | Cascii_126 => 126
    | Cascii_127 => 127*)
    | Cdascii => 0
    end.

(* Number of arguments that constructor takes *)
Definition constructor_arg_n ctor : nat :=
    match ctor with
    | CO => 0
    | CS => 1

    | Cfalse => 0
    | Ctrue => 0

    | Cnil => 0
    | Ccons => 2

    | Ctt => 0

    | Cpair => 2

    | Csome => 1
    | Cnone => 0

    | CxI => 1
    | CxO => 1
    | CxH => 0

    | CN0 => 0
    | CNpos => 1

    | CZ0 => 0
    | CZpos => 1
    | CZneg => 1

(*    | Cascii_0 => 0
    | Cascii_1 => 0
    | Cascii_2 => 0
    | Cascii_3 => 0
    | Cascii_4 => 0
    | Cascii_5 => 0
    | Cascii_6 => 0
    | Cascii_7 => 0
    | Cascii_8 => 0
    | Cascii_9 => 0
    | Cascii_10 => 0
    | Cascii_11 => 0
    | Cascii_12 => 0
    | Cascii_13 => 0
    | Cascii_14 => 0
    | Cascii_15 => 0
    | Cascii_16 => 0
    | Cascii_17 => 0
    | Cascii_18 => 0
    | Cascii_19 => 0
    | Cascii_20 => 0
    | Cascii_21 => 0
    | Cascii_22 => 0
    | Cascii_23 => 0
    | Cascii_24 => 0
    | Cascii_25 => 0
    | Cascii_26 => 0
    | Cascii_27 => 0
    | Cascii_28 => 0
    | Cascii_29 => 0
    | Cascii_30 => 0
    | Cascii_31 => 0
    | Cascii_32 => 0
    | Cascii_33 => 0
    | Cascii_34 => 0
    | Cascii_35 => 0
    | Cascii_36 => 0
    | Cascii_37 => 0
    | Cascii_38 => 0
    | Cascii_39 => 0
    | Cascii_40 => 0
    | Cascii_41 => 0
    | Cascii_42 => 0
    | Cascii_43 => 0
    | Cascii_44 => 0
    | Cascii_45 => 0
    | Cascii_46 => 0
    | Cascii_47 => 0
    | Cascii_48 => 0
    | Cascii_49 => 0
    | Cascii_50 => 0
    | Cascii_51 => 0
    | Cascii_52 => 0
    | Cascii_53 => 0
    | Cascii_54 => 0
    | Cascii_55 => 0
    | Cascii_56 => 0
    | Cascii_57 => 0
    | Cascii_58 => 0
    | Cascii_59 => 0
    | Cascii_60 => 0
    | Cascii_61 => 0
    | Cascii_62 => 0
    | Cascii_63 => 0
    | Cascii_64 => 0
    | Cascii_65 => 0
    | Cascii_66 => 0
    | Cascii_67 => 0
    | Cascii_68 => 0
    | Cascii_69 => 0
    | Cascii_70 => 0
    | Cascii_71 => 0
    | Cascii_72 => 0
    | Cascii_73 => 0
    | Cascii_74 => 0
    | Cascii_75 => 0
    | Cascii_76 => 0
    | Cascii_77 => 0
    | Cascii_78 => 0
    | Cascii_79 => 0
    | Cascii_80 => 0
    | Cascii_81 => 0
    | Cascii_82 => 0
    | Cascii_83 => 0
    | Cascii_84 => 0
    | Cascii_85 => 0
    | Cascii_86 => 0
    | Cascii_87 => 0
    | Cascii_88 => 0
    | Cascii_89 => 0
    | Cascii_90 => 0
    | Cascii_91 => 0
    | Cascii_92 => 0
    | Cascii_93 => 0
    | Cascii_94 => 0
    | Cascii_95 => 0
    | Cascii_96 => 0
    | Cascii_97 => 0
    | Cascii_98 => 0
    | Cascii_99 => 0
    | Cascii_100 => 0
    | Cascii_101 => 0
    | Cascii_102 => 0
    | Cascii_103 => 0
    | Cascii_104 => 0
    | Cascii_105 => 0
    | Cascii_106 => 0
    | Cascii_107 => 0
    | Cascii_108 => 0
    | Cascii_109 => 0
    | Cascii_110 => 0
    | Cascii_111 => 0
    | Cascii_112 => 0
    | Cascii_113 => 0
    | Cascii_114 => 0
    | Cascii_115 => 0
    | Cascii_116 => 0
    | Cascii_117 => 0
    | Cascii_118 => 0
    | Cascii_119 => 0
    | Cascii_120 => 0
    | Cascii_121 => 0
    | Cascii_122 => 0
    | Cascii_123 => 0
    | Cascii_124 => 0
    | Cascii_125 => 0
    | Cascii_126 => 0
    | Cascii_127 => 0*)
                      
    | Cdascii => 8
    end.

(* Add a case if a constructor is recursive *)
Definition ctor_arg_is_recursive ctor pos : bool :=
    match ctor, pos with
    | CS, 0 => true
    | Ccons, 1 => true
    | CxI, 0 => true
    | CxO, 0 => true
    | _, _ => false
    end.

(* Redundant definition, could be auto generated *)
(* Given an Oeuf model fo a type and an index, give the constructor *)
Definition type_constr ty idx : option constr_name :=
    match ty, idx with
    | Tnat, 0 => Some CO
    | Tnat, 1 => Some CS

    | Tbool, 0 => Some Ctrue
    | Tbool, 1 => Some Cfalse

    | Tlist _, 0 => Some Cnil
    | Tlist _, 1 => Some Ccons

    | Tunit, 0 => Some Ctt

    | Tpair _ _, 0 => Some Cpair

    | Toption _, 0 => Some Csome
    | Toption _, 1 => Some Cnone

    | Tpositive, 0 => Some CxI
    | Tpositive, 1 => Some CxO
    | Tpositive, 2 => Some CxH

    | TN, 0 => Some CN0
    | TN, 1 => Some CNpos

    | TZ, 0 => Some CZ0
    | TZ, 1 => Some CZpos
    | TZ, 2 => Some CZneg

(*    | Tascii, 0 => Some Cascii_0
    | Tascii, 1 => Some Cascii_1
    | Tascii, 2 => Some Cascii_2
    | Tascii, 3 => Some Cascii_3
    | Tascii, 4 => Some Cascii_4
    | Tascii, 5 => Some Cascii_5
    | Tascii, 6 => Some Cascii_6
    | Tascii, 7 => Some Cascii_7
    | Tascii, 8 => Some Cascii_8
    | Tascii, 9 => Some Cascii_9
    | Tascii, 10 => Some Cascii_10
    | Tascii, 11 => Some Cascii_11
    | Tascii, 12 => Some Cascii_12
    | Tascii, 13 => Some Cascii_13
    | Tascii, 14 => Some Cascii_14
    | Tascii, 15 => Some Cascii_15
    | Tascii, 16 => Some Cascii_16
    | Tascii, 17 => Some Cascii_17
    | Tascii, 18 => Some Cascii_18
    | Tascii, 19 => Some Cascii_19
    | Tascii, 20 => Some Cascii_20
    | Tascii, 21 => Some Cascii_21
    | Tascii, 22 => Some Cascii_22
    | Tascii, 23 => Some Cascii_23
    | Tascii, 24 => Some Cascii_24
    | Tascii, 25 => Some Cascii_25
    | Tascii, 26 => Some Cascii_26
    | Tascii, 27 => Some Cascii_27
    | Tascii, 28 => Some Cascii_28
    | Tascii, 29 => Some Cascii_29
    | Tascii, 30 => Some Cascii_30
    | Tascii, 31 => Some Cascii_31
    | Tascii, 32 => Some Cascii_32
    | Tascii, 33 => Some Cascii_33
    | Tascii, 34 => Some Cascii_34
    | Tascii, 35 => Some Cascii_35
    | Tascii, 36 => Some Cascii_36
    | Tascii, 37 => Some Cascii_37
    | Tascii, 38 => Some Cascii_38
    | Tascii, 39 => Some Cascii_39
    | Tascii, 40 => Some Cascii_40
    | Tascii, 41 => Some Cascii_41
    | Tascii, 42 => Some Cascii_42
    | Tascii, 43 => Some Cascii_43
    | Tascii, 44 => Some Cascii_44
    | Tascii, 45 => Some Cascii_45
    | Tascii, 46 => Some Cascii_46
    | Tascii, 47 => Some Cascii_47
    | Tascii, 48 => Some Cascii_48
    | Tascii, 49 => Some Cascii_49
    | Tascii, 50 => Some Cascii_50
    | Tascii, 51 => Some Cascii_51
    | Tascii, 52 => Some Cascii_52
    | Tascii, 53 => Some Cascii_53
    | Tascii, 54 => Some Cascii_54
    | Tascii, 55 => Some Cascii_55
    | Tascii, 56 => Some Cascii_56
    | Tascii, 57 => Some Cascii_57
    | Tascii, 58 => Some Cascii_58
    | Tascii, 59 => Some Cascii_59
    | Tascii, 60 => Some Cascii_60
    | Tascii, 61 => Some Cascii_61
    | Tascii, 62 => Some Cascii_62
    | Tascii, 63 => Some Cascii_63
    | Tascii, 64 => Some Cascii_64
    | Tascii, 65 => Some Cascii_65
    | Tascii, 66 => Some Cascii_66
    | Tascii, 67 => Some Cascii_67
    | Tascii, 68 => Some Cascii_68
    | Tascii, 69 => Some Cascii_69
    | Tascii, 70 => Some Cascii_70
    | Tascii, 71 => Some Cascii_71
    | Tascii, 72 => Some Cascii_72
    | Tascii, 73 => Some Cascii_73
    | Tascii, 74 => Some Cascii_74
    | Tascii, 75 => Some Cascii_75
    | Tascii, 76 => Some Cascii_76
    | Tascii, 77 => Some Cascii_77
    | Tascii, 78 => Some Cascii_78
    | Tascii, 79 => Some Cascii_79
    | Tascii, 80 => Some Cascii_80
    | Tascii, 81 => Some Cascii_81
    | Tascii, 82 => Some Cascii_82
    | Tascii, 83 => Some Cascii_83
    | Tascii, 84 => Some Cascii_84
    | Tascii, 85 => Some Cascii_85
    | Tascii, 86 => Some Cascii_86
    | Tascii, 87 => Some Cascii_87
    | Tascii, 88 => Some Cascii_88
    | Tascii, 89 => Some Cascii_89
    | Tascii, 90 => Some Cascii_90
    | Tascii, 91 => Some Cascii_91
    | Tascii, 92 => Some Cascii_92
    | Tascii, 93 => Some Cascii_93
    | Tascii, 94 => Some Cascii_94
    | Tascii, 95 => Some Cascii_95
    | Tascii, 96 => Some Cascii_96
    | Tascii, 97 => Some Cascii_97
    | Tascii, 98 => Some Cascii_98
    | Tascii, 99 => Some Cascii_99
    | Tascii, 100 => Some Cascii_100
    | Tascii, 101 => Some Cascii_101
    | Tascii, 102 => Some Cascii_102
    | Tascii, 103 => Some Cascii_103
    | Tascii, 104 => Some Cascii_104
    | Tascii, 105 => Some Cascii_105
    | Tascii, 106 => Some Cascii_106
    | Tascii, 107 => Some Cascii_107
    | Tascii, 108 => Some Cascii_108
    | Tascii, 109 => Some Cascii_109
    | Tascii, 110 => Some Cascii_110
    | Tascii, 111 => Some Cascii_111
    | Tascii, 112 => Some Cascii_112
    | Tascii, 113 => Some Cascii_113
    | Tascii, 114 => Some Cascii_114
    | Tascii, 115 => Some Cascii_115
    | Tascii, 116 => Some Cascii_116
    | Tascii, 117 => Some Cascii_117
    | Tascii, 118 => Some Cascii_118
    | Tascii, 119 => Some Cascii_119
    | Tascii, 120 => Some Cascii_120
    | Tascii, 121 => Some Cascii_121
    | Tascii, 122 => Some Cascii_122
    | Tascii, 123 => Some Cascii_123
    | Tascii, 124 => Some Cascii_124
    | Tascii, 125 => Some Cascii_125
    | Tascii, 126 => Some Cascii_126
    | Tascii, 127 => Some Cascii_127*)

    | Tascii, 0 => Some CAscii
                          
    | _, _ => None
    end.


Definition is_ctor_for_type ty ctor :=
    exists idx, type_constr ty idx = Some ctor.

Lemma type_constr_index : forall ty i ctor,
    type_constr ty i = Some ctor ->
    i = constructor_index ctor.
intros. destruct ty; unfold type_constr in H;
  repeat (destruct i as [|i]; try discriminate H);
  inversion H; reflexivity.
Qed.

Lemma type_constr_injective : forall ty i j ctor,
    type_constr ty i = Some ctor ->
    type_constr ty j = Some ctor ->
    i = j.
intros ? ? ? ? Hi Hj.
eapply type_constr_index in Hi.
eapply type_constr_index in Hj.
congruence.
Qed.

Lemma ctor_for_type_constr_index : forall ty ctor,
    is_ctor_for_type ty ctor ->
    type_constr ty (constructor_index ctor) = Some ctor.
inversion 1.  erewrite <- type_constr_index; eassumption.
Qed.

  

(* Induction scheme for type_name that gives you an induction hypothesis for
   each type contained in `tyn`.  For example, an `N` may contain a `positive`,
   so the `N` case provides an induction hypothesis `P Tpositive`. *)
Definition type_name_containment_rect (P : type_name -> Type)
    (Hnat :         P Tnat)
    (Hbool :        P Tbool)
    (Hlist :        forall tyn, P tyn -> P (Tlist tyn))
    (Hunit :        P Tunit)
    (Hpair :        forall tyn1 tyn2, P tyn1 -> P tyn2 -> P (Tpair tyn1 tyn2))
    (Hoption :      forall tyn, P tyn -> P (Toption tyn))
    (Hpositive :    P Tpositive)
    (HN :           P Tpositive -> P TN)
    (HZ :           P Tpositive -> P TZ)
    (Hascii :       P Tbool -> P Tascii) :
    forall tyn, P tyn.
induction tyn; eauto.
Defined.

