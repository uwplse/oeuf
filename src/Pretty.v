Require Import Program.
Require Import oeuf.SourceLifted oeuf.Utopia List oeuf.Monads oeuf.HList oeuf.CompilationUnit oeuf.ListLemmas.
Require Import oeuf.StuartTact.
Import ListNotations.

From StructTact Require Import StructTactics.
From PrettyParsing Require Import PrettyParsing.
Import OptionNotations.

Set Implicit Arguments.

Notation "( x , y , .. , z )" := (existT _ .. (existT _ x y) .. z).


Module type_name.
  Fixpoint to_tree (tyn : type_name) : tree symbol.t :=
    match tyn with
    | Tnat            => atom (symbol.of_string_unsafe "nat")
    | Tbool           => atom (symbol.of_string_unsafe "bool")
    | Tlist tyn       => node [atom (symbol.of_string_unsafe "list"); to_tree tyn]
    | Tunit           => atom (symbol.of_string_unsafe "unit")
    | Tpair tyn1 tyn2 => node [atom (symbol.of_string_unsafe "pair"); to_tree tyn1; to_tree tyn2]
    | Toption tyn     => node [atom (symbol.of_string_unsafe "option"); to_tree tyn]
    | Tpositive       => atom (symbol.of_string_unsafe "positive")
    | TN              => atom (symbol.of_string_unsafe "N")
    | TZ              => atom (symbol.of_string_unsafe "Z")
    | Tascii          => atom (symbol.of_string_unsafe "ascii")
    end.

  Fixpoint from_tree (t : tree symbol.t) : option type_name :=
    match t with
    | atom s =>
      if symbol.eq_dec s (symbol.of_string_unsafe "nat") then Some Tnat
      else if symbol.eq_dec s (symbol.of_string_unsafe "bool") then Some Tbool
      else if symbol.eq_dec s (symbol.of_string_unsafe "unit") then Some Tunit
      else if symbol.eq_dec s (symbol.of_string_unsafe "positive") then Some Tpositive
      else if symbol.eq_dec s (symbol.of_string_unsafe "N") then Some TN
      else if symbol.eq_dec s (symbol.of_string_unsafe "Z") then Some TZ
      else if symbol.eq_dec s (symbol.of_string_unsafe "ascii") then Some Tascii
      else None
    | node (atom s :: l) =>
      if symbol.eq_dec s (symbol.of_string_unsafe "list")
      then match l with
           | [t] => match from_tree t with None => None
                   | Some tyn => Some (Tlist tyn)
                   end
           | _ => None
           end
      else if symbol.eq_dec s (symbol.of_string_unsafe "pair")
      then match l with
           | [t1; t2] =>
             match from_tree t1 with None => None
             | Some tyn1 =>
             match from_tree t2 with None => None
             | Some tyn2 => Some (Tpair tyn1 tyn2)
             end end
           | _ => None
           end
      else if symbol.eq_dec s (symbol.of_string_unsafe "option")
      then match l with
           | [t] => match from_tree t with None => None
                   | Some tyn => Some (Toption tyn)
                   end
           | _ => None
           end
      else None
    | _ => None
    end.

  Lemma to_from_tree_id : forall ty, from_tree (to_tree ty) = Some ty.
  Proof.
    induction ty; simpl; auto.
    - now rewrite IHty.
    - now rewrite IHty1, IHty2.
    - now rewrite IHty.
  Qed.

  Lemma to_tree_wf:
    forall tyn, Forall symbol.wf (type_name.to_tree tyn).
  Proof. induction tyn; simpl; auto. Qed.
  Hint Resolve to_tree_wf.
End type_name.


Module type.
  Fixpoint to_tree (ty : type) : tree symbol.t :=
    match ty with
    | ADT tyn => node [atom (symbol.of_string_unsafe "ADT"); type_name.to_tree tyn]
    | Arrow ty1 ty2 => node [atom (symbol.of_string_unsafe "Arrow"); to_tree ty1; to_tree ty2]
    end.

  Fixpoint from_tree (t : tree symbol.t) : option type :=
    match t with
    | node (atom s :: l) =>
      if symbol.eq_dec s (symbol.of_string_unsafe "ADT")
      then match l with
           | [t] => ADT <$> type_name.from_tree t
           | _ => None
           end
      else if symbol.eq_dec s (symbol.of_string_unsafe "Arrow")
      then match l with
           | [t1; t2] => Arrow <$> from_tree t1 <*> from_tree t2
           | _ => None
           end
      else None
    | _ => None
    end.

  Lemma to_from_tree_id : forall ty, from_tree (to_tree ty) = Some ty.
  Proof.
    induction ty; simpl; unfold_option.
    - now rewrite type_name.to_from_tree_id.
    - now rewrite IHty1, IHty2.
  Qed.

  Lemma to_tree_wf:
    forall ty, Forall symbol.wf (type.to_tree ty).
  Proof. induction ty; simpl; auto. Qed.
  Hint Resolve to_tree_wf.
End type.


Module constr_name.
  Definition to_symbol (cn : constr_name) : symbol.t :=
    match cn with
    | CS     => symbol.of_string_unsafe "CS"
    | CO     => symbol.of_string_unsafe "CO"
    | Ctrue  => symbol.of_string_unsafe "Ctrue"
    | Cfalse => symbol.of_string_unsafe "Cfalse"
    | Cnil   => symbol.of_string_unsafe "Cnil"
    | Ccons  => symbol.of_string_unsafe "Ccons"
    | Ctt    => symbol.of_string_unsafe "Ctt"
    | Cpair  => symbol.of_string_unsafe "Cpair"
    | Csome  => symbol.of_string_unsafe "Csome"
    | Cnone  => symbol.of_string_unsafe "Cnone"
    | CxI    => symbol.of_string_unsafe "CxI"
    | CxO    => symbol.of_string_unsafe "CxO"
    | CxH    => symbol.of_string_unsafe "CxH"
    | CN0    => symbol.of_string_unsafe "CN0"
    | CNpos  => symbol.of_string_unsafe "CNpos"
    | CZ0    => symbol.of_string_unsafe "CZ0"
    | CZpos  => symbol.of_string_unsafe "CZpos"
    | CZneg  => symbol.of_string_unsafe "CZneg"
    | Cascii_0 => symbol.of_string_unsafe "Cascii_0"
    | Cascii_1 => symbol.of_string_unsafe "Cascii_1"
    | Cascii_2 => symbol.of_string_unsafe "Cascii_2"
    | Cascii_3 => symbol.of_string_unsafe "Cascii_3"
    | Cascii_4 => symbol.of_string_unsafe "Cascii_4"
    | Cascii_5 => symbol.of_string_unsafe "Cascii_5"
    | Cascii_6 => symbol.of_string_unsafe "Cascii_6"
    | Cascii_7 => symbol.of_string_unsafe "Cascii_7"
    | Cascii_8 => symbol.of_string_unsafe "Cascii_8"
    | Cascii_9 => symbol.of_string_unsafe "Cascii_9"
    | Cascii_10 => symbol.of_string_unsafe "Cascii_10"
    | Cascii_11 => symbol.of_string_unsafe "Cascii_11"
    | Cascii_12 => symbol.of_string_unsafe "Cascii_12"
    | Cascii_13 => symbol.of_string_unsafe "Cascii_13"
    | Cascii_14 => symbol.of_string_unsafe "Cascii_14"
    | Cascii_15 => symbol.of_string_unsafe "Cascii_15"
    | Cascii_16 => symbol.of_string_unsafe "Cascii_16"
    | Cascii_17 => symbol.of_string_unsafe "Cascii_17"
    | Cascii_18 => symbol.of_string_unsafe "Cascii_18"
    | Cascii_19 => symbol.of_string_unsafe "Cascii_19"
    | Cascii_20 => symbol.of_string_unsafe "Cascii_20"
    | Cascii_21 => symbol.of_string_unsafe "Cascii_21"
    | Cascii_22 => symbol.of_string_unsafe "Cascii_22"
    | Cascii_23 => symbol.of_string_unsafe "Cascii_23"
    | Cascii_24 => symbol.of_string_unsafe "Cascii_24"
    | Cascii_25 => symbol.of_string_unsafe "Cascii_25"
    | Cascii_26 => symbol.of_string_unsafe "Cascii_26"
    | Cascii_27 => symbol.of_string_unsafe "Cascii_27"
    | Cascii_28 => symbol.of_string_unsafe "Cascii_28"
    | Cascii_29 => symbol.of_string_unsafe "Cascii_29"
    | Cascii_30 => symbol.of_string_unsafe "Cascii_30"
    | Cascii_31 => symbol.of_string_unsafe "Cascii_31"
    | Cascii_32 => symbol.of_string_unsafe "Cascii_32"
    | Cascii_33 => symbol.of_string_unsafe "Cascii_33"
    | Cascii_34 => symbol.of_string_unsafe "Cascii_34"
    | Cascii_35 => symbol.of_string_unsafe "Cascii_35"
    | Cascii_36 => symbol.of_string_unsafe "Cascii_36"
    | Cascii_37 => symbol.of_string_unsafe "Cascii_37"
    | Cascii_38 => symbol.of_string_unsafe "Cascii_38"
    | Cascii_39 => symbol.of_string_unsafe "Cascii_39"
    | Cascii_40 => symbol.of_string_unsafe "Cascii_40"
    | Cascii_41 => symbol.of_string_unsafe "Cascii_41"
    | Cascii_42 => symbol.of_string_unsafe "Cascii_42"
    | Cascii_43 => symbol.of_string_unsafe "Cascii_43"
    | Cascii_44 => symbol.of_string_unsafe "Cascii_44"
    | Cascii_45 => symbol.of_string_unsafe "Cascii_45"
    | Cascii_46 => symbol.of_string_unsafe "Cascii_46"
    | Cascii_47 => symbol.of_string_unsafe "Cascii_47"
    | Cascii_48 => symbol.of_string_unsafe "Cascii_48"
    | Cascii_49 => symbol.of_string_unsafe "Cascii_49"
    | Cascii_50 => symbol.of_string_unsafe "Cascii_50"
    | Cascii_51 => symbol.of_string_unsafe "Cascii_51"
    | Cascii_52 => symbol.of_string_unsafe "Cascii_52"
    | Cascii_53 => symbol.of_string_unsafe "Cascii_53"
    | Cascii_54 => symbol.of_string_unsafe "Cascii_54"
    | Cascii_55 => symbol.of_string_unsafe "Cascii_55"
    | Cascii_56 => symbol.of_string_unsafe "Cascii_56"
    | Cascii_57 => symbol.of_string_unsafe "Cascii_57"
    | Cascii_58 => symbol.of_string_unsafe "Cascii_58"
    | Cascii_59 => symbol.of_string_unsafe "Cascii_59"
    | Cascii_60 => symbol.of_string_unsafe "Cascii_60"
    | Cascii_61 => symbol.of_string_unsafe "Cascii_61"
    | Cascii_62 => symbol.of_string_unsafe "Cascii_62"
    | Cascii_63 => symbol.of_string_unsafe "Cascii_63"
    | Cascii_64 => symbol.of_string_unsafe "Cascii_64"
    | Cascii_65 => symbol.of_string_unsafe "Cascii_65"
    | Cascii_66 => symbol.of_string_unsafe "Cascii_66"
    | Cascii_67 => symbol.of_string_unsafe "Cascii_67"
    | Cascii_68 => symbol.of_string_unsafe "Cascii_68"
    | Cascii_69 => symbol.of_string_unsafe "Cascii_69"
    | Cascii_70 => symbol.of_string_unsafe "Cascii_70"
    | Cascii_71 => symbol.of_string_unsafe "Cascii_71"
    | Cascii_72 => symbol.of_string_unsafe "Cascii_72"
    | Cascii_73 => symbol.of_string_unsafe "Cascii_73"
    | Cascii_74 => symbol.of_string_unsafe "Cascii_74"
    | Cascii_75 => symbol.of_string_unsafe "Cascii_75"
    | Cascii_76 => symbol.of_string_unsafe "Cascii_76"
    | Cascii_77 => symbol.of_string_unsafe "Cascii_77"
    | Cascii_78 => symbol.of_string_unsafe "Cascii_78"
    | Cascii_79 => symbol.of_string_unsafe "Cascii_79"
    | Cascii_80 => symbol.of_string_unsafe "Cascii_80"
    | Cascii_81 => symbol.of_string_unsafe "Cascii_81"
    | Cascii_82 => symbol.of_string_unsafe "Cascii_82"
    | Cascii_83 => symbol.of_string_unsafe "Cascii_83"
    | Cascii_84 => symbol.of_string_unsafe "Cascii_84"
    | Cascii_85 => symbol.of_string_unsafe "Cascii_85"
    | Cascii_86 => symbol.of_string_unsafe "Cascii_86"
    | Cascii_87 => symbol.of_string_unsafe "Cascii_87"
    | Cascii_88 => symbol.of_string_unsafe "Cascii_88"
    | Cascii_89 => symbol.of_string_unsafe "Cascii_89"
    | Cascii_90 => symbol.of_string_unsafe "Cascii_90"
    | Cascii_91 => symbol.of_string_unsafe "Cascii_91"
    | Cascii_92 => symbol.of_string_unsafe "Cascii_92"
    | Cascii_93 => symbol.of_string_unsafe "Cascii_93"
    | Cascii_94 => symbol.of_string_unsafe "Cascii_94"
    | Cascii_95 => symbol.of_string_unsafe "Cascii_95"
    | Cascii_96 => symbol.of_string_unsafe "Cascii_96"
    | Cascii_97 => symbol.of_string_unsafe "Cascii_97"
    | Cascii_98 => symbol.of_string_unsafe "Cascii_98"
    | Cascii_99 => symbol.of_string_unsafe "Cascii_99"
    | Cascii_100 => symbol.of_string_unsafe "Cascii_100"
    | Cascii_101 => symbol.of_string_unsafe "Cascii_101"
    | Cascii_102 => symbol.of_string_unsafe "Cascii_102"
    | Cascii_103 => symbol.of_string_unsafe "Cascii_103"
    | Cascii_104 => symbol.of_string_unsafe "Cascii_104"
    | Cascii_105 => symbol.of_string_unsafe "Cascii_105"
    | Cascii_106 => symbol.of_string_unsafe "Cascii_106"
    | Cascii_107 => symbol.of_string_unsafe "Cascii_107"
    | Cascii_108 => symbol.of_string_unsafe "Cascii_108"
    | Cascii_109 => symbol.of_string_unsafe "Cascii_109"
    | Cascii_110 => symbol.of_string_unsafe "Cascii_110"
    | Cascii_111 => symbol.of_string_unsafe "Cascii_111"
    | Cascii_112 => symbol.of_string_unsafe "Cascii_112"
    | Cascii_113 => symbol.of_string_unsafe "Cascii_113"
    | Cascii_114 => symbol.of_string_unsafe "Cascii_114"
    | Cascii_115 => symbol.of_string_unsafe "Cascii_115"
    | Cascii_116 => symbol.of_string_unsafe "Cascii_116"
    | Cascii_117 => symbol.of_string_unsafe "Cascii_117"
    | Cascii_118 => symbol.of_string_unsafe "Cascii_118"
    | Cascii_119 => symbol.of_string_unsafe "Cascii_119"
    | Cascii_120 => symbol.of_string_unsafe "Cascii_120"
    | Cascii_121 => symbol.of_string_unsafe "Cascii_121"
    | Cascii_122 => symbol.of_string_unsafe "Cascii_122"
    | Cascii_123 => symbol.of_string_unsafe "Cascii_123"
    | Cascii_124 => symbol.of_string_unsafe "Cascii_124"
    | Cascii_125 => symbol.of_string_unsafe "Cascii_125"
    | Cascii_126 => symbol.of_string_unsafe "Cascii_126"
    | Cascii_127 => symbol.of_string_unsafe "Cascii_127"
    end.
  
  Definition from_symbol (s : symbol.t) : option constr_name :=
    if      symbol.eq_dec s (symbol.of_string_unsafe "CS")     then Some CS
    else if symbol.eq_dec s (symbol.of_string_unsafe "CO")     then Some CO
    else if symbol.eq_dec s (symbol.of_string_unsafe "Ctrue")  then Some Ctrue
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cfalse") then Some Cfalse
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cnil")   then Some Cnil
    else if symbol.eq_dec s (symbol.of_string_unsafe "Ccons")  then Some Ccons
    else if symbol.eq_dec s (symbol.of_string_unsafe "Ctt")    then Some Ctt
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cpair")  then Some Cpair
    else if symbol.eq_dec s (symbol.of_string_unsafe "Csome")  then Some Csome
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cnone")  then Some Cnone
    else if symbol.eq_dec s (symbol.of_string_unsafe "CxI")    then Some CxI
    else if symbol.eq_dec s (symbol.of_string_unsafe "CxO")    then Some CxO
    else if symbol.eq_dec s (symbol.of_string_unsafe "CxH")    then Some CxH
    else if symbol.eq_dec s (symbol.of_string_unsafe "CN0")    then Some CN0
    else if symbol.eq_dec s (symbol.of_string_unsafe "CNpos")  then Some CNpos
    else if symbol.eq_dec s (symbol.of_string_unsafe "CZ0")    then Some CZ0
    else if symbol.eq_dec s (symbol.of_string_unsafe "CZpos")  then Some CZpos
    else if symbol.eq_dec s (symbol.of_string_unsafe "CZneg")  then Some CZneg
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_0")  then Some Cascii_0
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_0")  then Some Cascii_0
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_1")  then Some Cascii_1
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_2")  then Some Cascii_2
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_3")  then Some Cascii_3
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_4")  then Some Cascii_4
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_5")  then Some Cascii_5
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_6")  then Some Cascii_6
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_7")  then Some Cascii_7
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_8")  then Some Cascii_8
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_9")  then Some Cascii_9
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_10")  then Some Cascii_10
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_11")  then Some Cascii_11
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_12")  then Some Cascii_12
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_13")  then Some Cascii_13
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_14")  then Some Cascii_14
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_15")  then Some Cascii_15
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_16")  then Some Cascii_16
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_17")  then Some Cascii_17
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_18")  then Some Cascii_18
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_19")  then Some Cascii_19
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_20")  then Some Cascii_20
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_21")  then Some Cascii_21
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_22")  then Some Cascii_22
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_23")  then Some Cascii_23
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_24")  then Some Cascii_24
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_25")  then Some Cascii_25
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_26")  then Some Cascii_26
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_27")  then Some Cascii_27
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_28")  then Some Cascii_28
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_29")  then Some Cascii_29
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_30")  then Some Cascii_30
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_31")  then Some Cascii_31
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_32")  then Some Cascii_32
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_33")  then Some Cascii_33
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_34")  then Some Cascii_34
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_35")  then Some Cascii_35
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_36")  then Some Cascii_36
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_37")  then Some Cascii_37
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_38")  then Some Cascii_38
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_39")  then Some Cascii_39
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_40")  then Some Cascii_40
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_41")  then Some Cascii_41
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_42")  then Some Cascii_42
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_43")  then Some Cascii_43
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_44")  then Some Cascii_44
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_45")  then Some Cascii_45
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_46")  then Some Cascii_46
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_47")  then Some Cascii_47
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_48")  then Some Cascii_48
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_49")  then Some Cascii_49
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_50")  then Some Cascii_50
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_51")  then Some Cascii_51
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_52")  then Some Cascii_52
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_53")  then Some Cascii_53
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_54")  then Some Cascii_54
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_55")  then Some Cascii_55
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_56")  then Some Cascii_56
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_57")  then Some Cascii_57
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_58")  then Some Cascii_58
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_59")  then Some Cascii_59
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_60")  then Some Cascii_60
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_61")  then Some Cascii_61
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_62")  then Some Cascii_62
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_63")  then Some Cascii_63
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_64")  then Some Cascii_64
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_65")  then Some Cascii_65
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_66")  then Some Cascii_66
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_67")  then Some Cascii_67
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_68")  then Some Cascii_68
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_69")  then Some Cascii_69
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_70")  then Some Cascii_70
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_71")  then Some Cascii_71
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_72")  then Some Cascii_72
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_73")  then Some Cascii_73
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_74")  then Some Cascii_74
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_75")  then Some Cascii_75
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_76")  then Some Cascii_76
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_77")  then Some Cascii_77
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_78")  then Some Cascii_78
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_79")  then Some Cascii_79
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_80")  then Some Cascii_80
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_81")  then Some Cascii_81
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_82")  then Some Cascii_82
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_83")  then Some Cascii_83
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_84")  then Some Cascii_84
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_85")  then Some Cascii_85
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_86")  then Some Cascii_86
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_87")  then Some Cascii_87
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_88")  then Some Cascii_88
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_89")  then Some Cascii_89
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_90")  then Some Cascii_90
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_91")  then Some Cascii_91
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_92")  then Some Cascii_92
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_93")  then Some Cascii_93
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_94")  then Some Cascii_94
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_95")  then Some Cascii_95
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_96")  then Some Cascii_96
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_97")  then Some Cascii_97
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_98")  then Some Cascii_98
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_108")  then Some Cascii_108
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_99")  then Some Cascii_99
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_109")  then Some Cascii_109
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_100")  then Some Cascii_100
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_107")  then Some Cascii_107
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_106")  then Some Cascii_106
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_105")  then Some Cascii_105
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_104")  then Some Cascii_104
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_103")  then Some Cascii_103
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_102")  then Some Cascii_102
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_101")  then Some Cascii_101
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_110")  then Some Cascii_110
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_111")  then Some Cascii_111
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_112")  then Some Cascii_112
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_113")  then Some Cascii_113
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_114")  then Some Cascii_114
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_115")  then Some Cascii_115
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_116")  then Some Cascii_116
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_117")  then Some Cascii_117
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_118")  then Some Cascii_118
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_119")  then Some Cascii_119
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_120")  then Some Cascii_120
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_121")  then Some Cascii_121
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_122")  then Some Cascii_122
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_123")  then Some Cascii_123
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_124")  then Some Cascii_124
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_125")  then Some Cascii_125
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_126")  then Some Cascii_126
    else if symbol.eq_dec s (symbol.of_string_unsafe "Cascii_127")  then Some Cascii_127
    else None.

  
  Lemma to_from_symbol_id : forall cn, from_symbol (to_symbol cn) = Some cn.
  Proof. destruct cn; auto. Qed.

  Lemma to_symbol_wf:
    forall cn, symbol.wf (constr_name.to_symbol cn).
  Proof. destruct cn; auto. Qed.
  Hint Resolve to_symbol_wf.
End constr_name.




Module constr_type.
  Definition check_constr_type {c arg_tys tyn} :
      option (constr_type c arg_tys tyn) :=
      match tyn with
      | Tnat          =>
        match c, arg_tys with
        | CS, [ADT Tnat] => Some CTS
        | CO, [] => Some CTO
        | _, _ => None
        end
      | Tbool         =>
        match c, arg_tys with
        | Ctrue, [] => Some CTtrue
        | Cfalse, [] =>  Some CTfalse
        | _, _ => None
        end
      | Tlist tyA     =>
        match c, arg_tys with
        | Cnil, [] => Some (CTnil _)
        | Ccons, [ADT tyA1; ADT (Tlist tyA2)] =>
          match type_name_eq_dec tyA tyA1 with right _ => None
          | left pf => match pf with eq_refl =>
          match type_name_eq_dec tyA tyA2 with right _ => None
          | left pf => match pf with eq_refl => Some (CTcons _)
          end end
          end end
        | _, _ => None
        end
      | Tunit         =>
        match c, arg_tys with
        | Ctt, [] => Some CTtt
        | _, _ => None
        end
      | Tpair ty1 ty2 =>
        match c, arg_tys with
        | Cpair, [ADT ty1'; ADT ty2'] =>
          match type_name_eq_dec ty1 ty1' with right _ => None
          | left pf => match pf with eq_refl =>
          match type_name_eq_dec ty2 ty2' with right _ => None
          | left pf => match pf with eq_refl => Some (CTpair _ _)
          end end end end
        | _, _ => None
        end
      | Toption tyA   =>
        match c, arg_tys with
        | Csome, [ADT tyA'] =>
          match type_name_eq_dec tyA tyA' with right _ => None
          | left pf => match pf with eq_refl => Some (CTsome _)
          end end
        | Cnone, [] => Some (CTnone _)
        | _, _ => None
        end
      | Tpositive     =>
        match c, arg_tys with
        | CxI, [ADT Tpositive] => Some CTxI
        | CxO, [ADT Tpositive] => Some CTxO
        | CxH, [] => Some CTxH
        | _, _ => None
        end
      | TN     =>
        match c, arg_tys with
        | CN0, [] => Some CTN0
        | CNpos, [ADT Tpositive] => Some CTNpos
        | _, _ => None
        end
      | TZ     =>
        match c, arg_tys with
        | CZ0, [] => Some CTZ0
        | CZpos, [ADT Tpositive] => Some CTZpos
        | CZneg, [ADT Tpositive] => Some CTZneg
        | _, _ => None
        end
      | Tascii =>
        match c, arg_tys with
        | Cascii_0, [] => Some CTascii_0
        | Cascii_1, [] => Some CTascii_1
        | Cascii_2, [] => Some CTascii_2
        | Cascii_3, [] => Some CTascii_3
        | Cascii_4, [] => Some CTascii_4
        | Cascii_5, [] => Some CTascii_5
        | Cascii_6, [] => Some CTascii_6
        | Cascii_7, [] => Some CTascii_7
        | Cascii_8, [] => Some CTascii_8
        | Cascii_9, [] => Some CTascii_9
        | Cascii_10, [] => Some CTascii_10
        | Cascii_11, [] => Some CTascii_11
        | Cascii_12, [] => Some CTascii_12
        | Cascii_13, [] => Some CTascii_13
        | Cascii_14, [] => Some CTascii_14
        | Cascii_15, [] => Some CTascii_15
        | Cascii_16, [] => Some CTascii_16
        | Cascii_17, [] => Some CTascii_17
        | Cascii_18, [] => Some CTascii_18
        | Cascii_19, [] => Some CTascii_19
        | Cascii_20, [] => Some CTascii_20
        | Cascii_21, [] => Some CTascii_21
        | Cascii_22, [] => Some CTascii_22
        | Cascii_23, [] => Some CTascii_23
        | Cascii_24, [] => Some CTascii_24
        | Cascii_25, [] => Some CTascii_25
        | Cascii_26, [] => Some CTascii_26
        | Cascii_27, [] => Some CTascii_27
        | Cascii_28, [] => Some CTascii_28
        | Cascii_29, [] => Some CTascii_29
        | Cascii_30, [] => Some CTascii_30
        | Cascii_31, [] => Some CTascii_31
        | Cascii_32, [] => Some CTascii_32
        | Cascii_33, [] => Some CTascii_33
        | Cascii_34, [] => Some CTascii_34
        | Cascii_35, [] => Some CTascii_35
        | Cascii_36, [] => Some CTascii_36
        | Cascii_37, [] => Some CTascii_37
        | Cascii_38, [] => Some CTascii_38
        | Cascii_39, [] => Some CTascii_39
        | Cascii_40, [] => Some CTascii_40
        | Cascii_41, [] => Some CTascii_41
        | Cascii_42, [] => Some CTascii_42
        | Cascii_43, [] => Some CTascii_43
        | Cascii_44, [] => Some CTascii_44
        | Cascii_45, [] => Some CTascii_45
        | Cascii_46, [] => Some CTascii_46
        | Cascii_47, [] => Some CTascii_47
        | Cascii_48, [] => Some CTascii_48
        | Cascii_49, [] => Some CTascii_49
        | Cascii_50, [] => Some CTascii_50
        | Cascii_51, [] => Some CTascii_51
        | Cascii_52, [] => Some CTascii_52
        | Cascii_53, [] => Some CTascii_53
        | Cascii_54, [] => Some CTascii_54
        | Cascii_55, [] => Some CTascii_55
        | Cascii_56, [] => Some CTascii_56
        | Cascii_57, [] => Some CTascii_57
        | Cascii_58, [] => Some CTascii_58
        | Cascii_59, [] => Some CTascii_59
        | Cascii_60, [] => Some CTascii_60
        | Cascii_61, [] => Some CTascii_61
        | Cascii_62, [] => Some CTascii_62
        | Cascii_63, [] => Some CTascii_63
        | Cascii_64, [] => Some CTascii_64
        | Cascii_65, [] => Some CTascii_65
        | Cascii_66, [] => Some CTascii_66
        | Cascii_67, [] => Some CTascii_67
        | Cascii_68, [] => Some CTascii_68
        | Cascii_69, [] => Some CTascii_69
        | Cascii_70, [] => Some CTascii_70
        | Cascii_71, [] => Some CTascii_71
        | Cascii_72, [] => Some CTascii_72
        | Cascii_73, [] => Some CTascii_73
        | Cascii_74, [] => Some CTascii_74
        | Cascii_75, [] => Some CTascii_75
        | Cascii_76, [] => Some CTascii_76
        | Cascii_77, [] => Some CTascii_77
        | Cascii_78, [] => Some CTascii_78
        | Cascii_79, [] => Some CTascii_79
        | Cascii_80, [] => Some CTascii_80
        | Cascii_81, [] => Some CTascii_81
        | Cascii_82, [] => Some CTascii_82
        | Cascii_83, [] => Some CTascii_83
        | Cascii_84, [] => Some CTascii_84
        | Cascii_85, [] => Some CTascii_85
        | Cascii_86, [] => Some CTascii_86
        | Cascii_87, [] => Some CTascii_87
        | Cascii_88, [] => Some CTascii_88
        | Cascii_89, [] => Some CTascii_89
        | Cascii_90, [] => Some CTascii_90
        | Cascii_91, [] => Some CTascii_91
        | Cascii_92, [] => Some CTascii_92
        | Cascii_93, [] => Some CTascii_93
        | Cascii_94, [] => Some CTascii_94
        | Cascii_95, [] => Some CTascii_95
        | Cascii_96, [] => Some CTascii_96
        | Cascii_97, [] => Some CTascii_97
        | Cascii_98, [] => Some CTascii_98
        | Cascii_99, [] => Some CTascii_99
        | Cascii_100, [] => Some CTascii_100
        | Cascii_101, [] => Some CTascii_101
        | Cascii_102, [] => Some CTascii_102
        | Cascii_103, [] => Some CTascii_103
        | Cascii_104, [] => Some CTascii_104
        | Cascii_105, [] => Some CTascii_105
        | Cascii_106, [] => Some CTascii_106
        | Cascii_107, [] => Some CTascii_107
        | Cascii_108, [] => Some CTascii_108
        | Cascii_109, [] => Some CTascii_109
        | Cascii_110, [] => Some CTascii_110
        | Cascii_111, [] => Some CTascii_111
        | Cascii_112, [] => Some CTascii_112
        | Cascii_113, [] => Some CTascii_113
        | Cascii_114, [] => Some CTascii_114
        | Cascii_115, [] => Some CTascii_115
        | Cascii_116, [] => Some CTascii_116
        | Cascii_117, [] => Some CTascii_117
        | Cascii_118, [] => Some CTascii_118
        | Cascii_119, [] => Some CTascii_119
        | Cascii_120, [] => Some CTascii_120
        | Cascii_121, [] => Some CTascii_121
        | Cascii_122, [] => Some CTascii_122
        | Cascii_123, [] => Some CTascii_123
        | Cascii_124, [] => Some CTascii_124
        | Cascii_125, [] => Some CTascii_125
        | Cascii_126, [] => Some CTascii_126
        | Cascii_127, [] => Some CTascii_127
        | _,_ => None
        end
      end.

  Lemma check_constr_type_correct :
    forall c arg_tys ty (ct : constr_type c arg_tys ty),
      constr_type.check_constr_type = Some ct.
  Proof.
    unfold constr_type.check_constr_type.
    intros.
    destruct ct; auto;
      repeat (break_match; try congruence;
              dependent destruction e; auto).
  Qed.

End constr_type.




Module elim.
  Definition check_elim {case_tys target_tyn ty} :
    option (elim case_tys (ADT target_tyn) ty) :=
      match target_tyn with
      | Tascii         => match case_tys with
                          | [ty0;ty1;ty2;ty3;ty4;ty5;ty6;ty7;
                             ty8;ty9;ty10;ty11;ty12;ty13;ty14;ty15;
                             ty16;ty17;ty18;ty19;ty20;ty21;ty22;ty23;
                             ty24;ty25;ty26;ty27;ty28;ty29;ty30;ty31;
                             ty32;ty33;ty34;ty35;ty36;ty37;ty38;ty39;
                             ty40;ty41;ty42;ty43;ty44;ty45;ty46;ty47;
                             ty48;ty49;ty50;ty51;ty52;ty53;ty54;ty55;
                             ty56;ty57;ty58;ty59;ty60;ty61;ty62;ty63;
                             ty64;ty65;ty66;ty67;ty68;ty69;ty70;ty71;
                             ty72;ty73;ty74;ty75;ty76;ty77;ty78;ty79;
                             ty80;ty81;ty82;ty83;ty84;ty85;ty86;ty87;
                             ty88;ty89;ty90;ty91;ty92;ty93;ty94;ty95;
                             ty96;ty97;ty98;ty99;ty100;ty101;ty102;ty103;
                             ty104;ty105;ty106;ty107;ty108;ty109;ty110;ty111;
                             ty112;ty113;ty114;ty115;ty116;ty117;ty118;ty119;
                             ty120;ty121;ty122;ty123;ty124;ty125;ty126;ty127
                            ] =>
                          match type_eq_dec ty ty0 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty1 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty2 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty3 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty4 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty5 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty6 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty7 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty8 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty9 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty10 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty11 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty12 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty13 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty14 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty15 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty16 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty17 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty18 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty19 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty20 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty21 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty22 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty23 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty24 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty25 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty26 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty27 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty28 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty29 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty30 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty31 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty32 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty33 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty34 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty35 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty36 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty37 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty38 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty39 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty40 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty41 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty42 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty43 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty44 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty45 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty46 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty47 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty48 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty49 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty50 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty51 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty52 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty53 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty54 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty55 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty56 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty57 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty58 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty59 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty60 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty61 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty62 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty63 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty64 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty65 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty66 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty67 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty68 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty69 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty70 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty71 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty72 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty73 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty74 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty75 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty76 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty77 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty78 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty79 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty80 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty81 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty82 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty83 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty84 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty85 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty86 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty87 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty88 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty89 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty90 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty91 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty92 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty93 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty94 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty95 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty96 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty97 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty98 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty99 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty100 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty101 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty102 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty103 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty104 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty105 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty106 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty107 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty108 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty109 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty110 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty111 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty112 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty113 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty114 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty115 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty116 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty117 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty118 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty119 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty120 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty121 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty122 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty123 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty124 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty125 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty126 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty127 with right _ => None
                          | left pf => match pf with | eq_refl => Some (EAscii _)
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end end end end end end end end end
                          end end end
                        | _ => None
                        end
      | Tnat          => match case_tys with
                        | [ty1; Arrow (ADT Tnat) (Arrow ty2 ty3)] =>
                          match type_eq_dec ty ty1 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty2 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty3 with right _ => None
                          | left pf => match pf with | eq_refl => Some (ENat _)
                          end end end end end end
                        | _ => None
                        end
      | Tbool         => match case_tys with
                        | [ty1; ty2] =>
                          match type_eq_dec ty ty1 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty2 with right _ => None
                          | left pf => match pf with | eq_refl => Some (EBool _)
                          end end end end
                        | _ => None
                        end
      | Tlist tyA     => match case_tys with
                        | [ty1; Arrow (ADT tyA1) (Arrow (ADT (Tlist tyA2)) (Arrow ty2 ty3))] =>
                          match type_eq_dec ty ty1 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty2 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty3 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_name_eq_dec tyA tyA1 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_name_eq_dec tyA tyA2 with right _ => None
                          | left pf => match pf with | eq_refl => Some (EList _ _)
                          end end end end end end end end end end
                        | _ => None
                        end
      | Tunit         => match case_tys with
                        | [ty1] =>
                          match type_eq_dec ty ty1 with right _ => None
                          | left pf => match pf with | eq_refl => Some (EUnit _)
                          end end
                        | _ => None
                        end
      | Tpair ty1 ty2 => match case_tys with
                        | [Arrow (ADT ty1') (Arrow (ADT ty2') ty')] =>
                          match type_eq_dec ty ty' with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_name_eq_dec ty1 ty1' with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_name_eq_dec ty2 ty2' with right _ => None
                          | left pf => match pf with | eq_refl => Some (EPair _ _ _)
                          end end end end end end
                        | _ => None
                        end
      | Toption tyA   => match case_tys with
                        | [Arrow (ADT tyA1) ty1; ty2] =>
                          match type_eq_dec ty ty1 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty2 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_name_eq_dec tyA tyA1 with right _ => None
                          | left pf => match pf with | eq_refl => Some (EOption _ _)
                          end end end end end end
                        | _ => None
                        end
      | Tpositive     => match case_tys with
                        | [Arrow (ADT Tpositive) (Arrow ty1 ty2);
                           Arrow (ADT Tpositive) (Arrow ty3 ty4); ty5] =>
                          match type_eq_dec ty ty1 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty2 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty3 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty4 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty5 with right _ => None
                          | left pf => match pf with | eq_refl => Some (EPositive _)
                          end end end end end end end end end end
                        | _ => None
                        end
      | TN            => match case_tys with
                        | [ty1;
                           Arrow (ADT Tpositive) ty2] =>
                          match type_eq_dec ty ty1 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty2 with right _ => None
                          | left pf => match pf with | eq_refl => Some (EN _)
                          end end end end
                        | _ => None
                        end
      | TZ            => match case_tys with
                        | [ty1;
                           Arrow (ADT Tpositive) ty2;
                           Arrow (ADT Tpositive) ty3] =>
                          match type_eq_dec ty ty1 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty2 with right _ => None
                          | left pf => match pf with | eq_refl =>
                          match type_eq_dec ty ty3 with right _ => None
                          | left pf => match pf with | eq_refl => Some (EZ _)
                          end end end end end end
                        | _ => None
                         end
      end.

  Lemma check_elim_correct :
    forall case_tys target_tyn ty (e : elim case_tys (ADT target_tyn) ty),
      check_elim = Some e.
  Proof.
  Admitted.


    (* OLD *)
  (*   unfold check_elim. *)
  (*   intros. *)
  (*   refine match e with *)
  (*            | EBool t    => _ *)
  (*            | ENat t     => _ *)
  (*            | EList _ t => _ *)
  (*            | EUnit t    => _ *)
  (*            | EPair _ _ t => _ *)
  (*            | EOption _ t => _ *)
  (*            | EPositive t => _ *)
  (*            | EN t        => _ *)
  (*            | EZ t        => _ *)
  (*            | EAscii t => _ *)
  (*          end; *)
  (*     repeat (break_match; try congruence; *)
  (*     dependent destruction e0; auto). *)
  (* Qed. *)
End elim.


Module value.
  Fixpoint to_tree {G ty} (e : value G ty) {struct e} : tree symbol.t.
    refine (let fix go_hlist {G tys} (h : hlist (value G) tys) : list (tree symbol.t) :=
                match h with
                | hnil => []
                | hcons e h => to_tree _ _ e :: go_hlist h
                end
            in _).
    refine match e with
           | @VConstr _ tyn cn _ ct args =>
             node [atom (symbol.of_string_unsafe "vconstr");
                   type_name.to_tree tyn;
                   atom (constr_name.to_symbol cn);
                   node (go_hlist _ _ args)]
           | @VClose _ _ _ _ mb free =>
             node [atom (symbol.of_string_unsafe "vclose");
                   atom (nat_to_symbol (member_to_nat mb));
                   node (go_hlist _ _ free)]
           end.
  Defined.

  Definition to_tree_hlist :=
    fix go_hlist {G tys} (h : hlist (value G) tys) : list (tree symbol.t) :=
      match h with
      | hnil => []
      | hcons e h => to_tree e :: go_hlist h
      end.

  Fixpoint from_tree (t : tree symbol.t) {G} {struct t} : option {ty : type & value G ty}.
    refine (let fix go_list (l : list (tree symbol.t)) G :
                  option {tys : list type & hlist (value G) tys} :=
                match l with
                | [] => Some ([], hnil)
                | t :: l =>
                  match from_tree t G with
                  | Some (ty, e) =>
                  match go_list l G with
                  | Some (l, h) => Some (ty :: l, hcons e h)
                  | None => None
                  end
                  | None => None
                  end
                end
            in _).
    refine match t with
           | node (atom tag :: l) =>
             if symbol.eq_dec tag (symbol.of_string_unsafe "vconstr")
             then match l with
                  | [t_tyn; atom s_cn; node t_args] =>
                  match go_list t_args G with None => None
                  | Some (arg_tys, args) =>
                  match type_name.from_tree t_tyn with None => None
                  | Some tyn =>
                  match constr_name.from_symbol s_cn with None => None
                  | Some cn =>
                  match @constr_type.check_constr_type cn arg_tys tyn with None => None
                  | Some ct => Some (ADT tyn, VConstr ct args)
                  end end end end
                  | _ => None
                  end
             else if symbol.eq_dec tag (symbol.of_string_unsafe "vclose")
             then match l with
                  | [atom t_mb; node t_free] =>
                  match member_from_nat (nat_from_symbol t_mb) with None => None
                  | Some (pair (pair arg_ty free_tys) ret_ty, mb) =>
                  match go_list t_free G with None => None
                  | Some (free_tys', free) =>
                  match list_eq_dec type_eq_dec free_tys free_tys' with right _ => None
                  | left pf => match pf with eq_refl => fun free =>
                        Some (Arrow arg_ty ret_ty, VClose mb free)
                  end free end end end
                  | _ => None
                  end
             else None
           | _ => None
           end.
  Defined.

  Definition from_tree_list :=
    fix go_list (l : list (tree symbol.t)) G :
      option {tys : list type & hlist (value G) tys} :=
      match l with
      | [] => Some ([], hnil)
      | t :: l =>
        match @from_tree t G with
        | Some (ty, e) =>
          match go_list l G with
          | Some (l, h) => Some (ty :: l, hcons e h)
          | None => None
          end
        | None => None
        end
      end.

  Lemma to_from_tree_id_and : forall G,
    (forall ty (e : value G ty), from_tree (to_tree e) = Some (ty,e)) *
    (forall args h, from_tree_list (to_tree_hlist h) G = Some (args, h)).
  Proof.
    intro G.
    apply value_rect_mut_comb; simpl; intros.

    - fold @from_tree_list.
      fold @to_tree_hlist.
      rewrite H, type_name.to_from_tree_id, constr_name.to_from_symbol_id.
      rewrite constr_type.check_constr_type_correct with (ct := ct).
      auto.

    - fold @from_tree_list.
      fold @to_tree_hlist.
      rewrite nat_to_from_symbol, member_to_from_nat_id.
      rewrite H.
      break_match; try congruence.
      dependent destruction e.
      auto.

    - auto.
    - now rewrite H, H0.
  Qed.

  Lemma to_from_tree_id : forall G ty (e : value G ty), from_tree (to_tree e) = Some (ty, e).
  Proof. apply to_from_tree_id_and. Qed.

  Lemma to_from_tree_list_id : forall G args h, from_tree_list (to_tree_hlist h) G = Some (args, h).
  Proof. apply to_from_tree_id_and. Qed.

  Lemma to_tree_wf_and : forall G,
    (forall ty (e : value G ty), Tree.Forall symbol.wf (to_tree e)) *
    (forall l (h : hlist (value G) l), List.Forall (Tree.Forall symbol.wf) (to_tree_hlist h)).
  Proof.
    intro G.
    apply value_rect_mut_comb; simpl; auto 10 using nat_to_symbol_wf.
  Qed.

  Lemma to_tree_wf : forall G ty (e : value G ty), Tree.Forall symbol.wf (to_tree e).
  Proof. apply to_tree_wf_and. Qed.
  Hint Resolve to_tree_wf.

  Lemma to_tree_hlist_wf :
    forall G l (h : hlist (value G) l), List.Forall (Tree.Forall symbol.wf) (to_tree_hlist h).
  Proof. apply to_tree_wf_and. Qed.
  Hint Resolve to_tree_hlist_wf.

  Definition print {G ty} (e : value G ty) : String.string :=
    print_tree (to_tree e).

  Definition pretty w {G ty} (e : value G ty) : String.string :=
    pretty_tree w (to_tree e).

  Definition parse (s : String.string) {G} : option {ty : type & value G ty} :=
    parse s >>= (fun t => from_tree t).

  Lemma parse_print_id : forall G ty (e : value G ty), parse (print e) = Some (ty, e).
  Proof.
    unfold parse, print.
    intros.
    unfold_option.
    now rewrite parse_print_tree, to_from_tree_id by auto.
  Qed.

  Lemma parse_pretty_id : forall w G ty (e : value G ty), parse (pretty w e) = Some (ty, e).
  Proof.
    unfold parse, pretty.
    intros.
    unfold_option.
    now rewrite parse_pretty_tree, to_from_tree_id by auto.
  Qed.
End value.


Module expr.
  Fixpoint to_tree {G L ty} (e : expr G L ty) {struct e} : tree symbol.t.
    refine (let fix go_hlist {G L l} (h : hlist (expr G L) l) : list (tree symbol.t) :=
                match h with
                | hnil => []
                | hcons e h => to_tree _ _ _ e :: go_hlist h
                end
            in _).
    refine match e with
           | Value v => 
             node [atom (symbol.of_string_unsafe "value");
                   value.to_tree v]
           | Var m => node [atom (symbol.of_string_unsafe "var"); atom (nat_to_symbol (member_to_nat m))]
           | App e1 e2 =>
             node [atom (symbol.of_string_unsafe "app"); to_tree _ _ _ e1; to_tree _ _ _ e2]
           | @Constr _ _ tyn cn _ c args =>
             node [atom (symbol.of_string_unsafe "constr");
                   type_name.to_tree tyn;
                   atom (constr_name.to_symbol cn);
                   node (go_hlist _ _ _ args)]
           | @Close _ _ _ _ _ mb free =>
             node [atom (symbol.of_string_unsafe "close");
                   atom (nat_to_symbol (member_to_nat mb));
                   node (go_hlist _ _ _ free)]
           | @Elim _ _ case_tys target_tyn ty e cases target =>
             node [atom (symbol.of_string_unsafe "elim");
                   type.to_tree ty;
                   node (go_hlist _ _ _ cases);
                   to_tree _ _ _ target]
           end.
  Defined.

  Definition to_tree_hlist :=
    fix go_hlist {G L tys} (h : hlist (expr G L) tys) : list (tree symbol.t) :=
      match h with
      | hnil => []
      | hcons e h => to_tree e :: go_hlist h
      end.

  Fixpoint from_tree (t : tree symbol.t) {G L} {struct t} : option {ty : type & expr G L ty}.
    refine (let fix go_list (l : list (tree symbol.t)) G L :
                  option {tys : list type & hlist (expr G L) tys} :=
                match l with
                | [] => Some ([], hnil)
                | t :: l =>
                  match from_tree t G L with
                  | Some (ty, e) =>
                  match go_list l G L with
                  | Some (l, h) => Some (ty :: l, hcons e h)
                  | None => None
                  end
                  | None => None
                  end
                end
            in _).
    refine match t with
           | node (atom tag :: l) =>
             if symbol.eq_dec tag (symbol.of_string_unsafe "value")
             then match l with
                  | [t_v] =>
                    match value.from_tree t_v with None => None
                    | Some (ty, v) => Some (ty, Value v)
                    end
                  | _ => None
                  end
             else if symbol.eq_dec tag (symbol.of_string_unsafe "var")
             then match l with
                  | [atom n] => match member_from_nat (nat_from_symbol n) with
                          | Some (ty, m) => Some (ty, Var m)
                          | _ => None
                          end
                  | _ => None
                  end
             else if symbol.eq_dec tag (symbol.of_string_unsafe "app")
             then match l with
                  | [t_e1; t_e2] =>
                    match from_tree t_e1 G L with None => None
                    | Some (ty1, e1) =>
                    match from_tree t_e2 G L with None => None
                    | Some (ty2, e2) =>
                    match ty1 with
                    | Arrow ty11 ty12 => fun e1 : expr _ _ (Arrow ty11 ty12) =>
                    match type_eq_dec ty11 ty2 with right _ => None
                    | left pf => match pf with eq_refl => fun e2 => Some (ty12 , App e1 e2)
                    end e2 end
                    | _ => fun _ => None
                    end e1 end end
                  | _ => None
                  end
             else if symbol.eq_dec tag (symbol.of_string_unsafe "constr")
             then match l with
                  | [t_tyn; atom s_cn; node t_args] =>
                  match go_list t_args G L with None => None
                  | Some (arg_tys, args) =>
                  match type_name.from_tree t_tyn with None => None
                  | Some tyn =>
                  match constr_name.from_symbol s_cn with None => None
                  | Some cn =>
                  match @constr_type.check_constr_type cn arg_tys tyn with None => None
                  | Some ct => Some (ADT tyn, Constr ct args)
                  end end end end
                  | _ => None
                  end
             else if symbol.eq_dec tag (symbol.of_string_unsafe "close")
             then match l with
                  | [atom t_mb; node t_free] =>
                  match member_from_nat (nat_from_symbol t_mb) with None => None
                  | Some (pair (pair arg_ty free_tys) ret_ty, mb) =>
                  match go_list t_free G L with None => None
                  | Some (free_tys', free) =>
                  match list_eq_dec type_eq_dec free_tys free_tys' with right _ => None
                  | left pf => match pf with eq_refl => fun free =>
                        Some (Arrow arg_ty ret_ty, Close mb free)
                  end free end end end
                  | _ => None
                  end
             else if symbol.eq_dec tag (symbol.of_string_unsafe "elim")
             then match l with
                  | [t_ty; node ts_cases; t_target] =>
                  match type.from_tree t_ty with None => None
                  | Some ty =>
                  match go_list ts_cases G L with None => None
                  | Some (case_tys, cases) =>
                  match from_tree t_target G L with
                  | Some (ADT target_tyn, target) =>
                  match @elim.check_elim case_tys target_tyn ty with None => None
                  | Some e => Some (ty, Elim e cases target)
                  end
                  | _ => None
                  end end end
                  | _ => None
                  end
             else None
           | _ => None
           end.
  Defined.

  Definition from_tree_list :=
    fix go_list (l : list (tree symbol.t)) G L :
      option {tys : list type & hlist (expr G L) tys} :=
      match l with
      | [] => Some ([], hnil)
      | t :: l =>
        match @from_tree t G L with
        | Some (ty, e) =>
          match go_list l G L with
          | Some (l, h) => Some (ty :: l, hcons e h)
          | None => None
          end
        | None => None
        end
      end.

  Lemma to_from_tree_id_and : forall G L,
    (forall ty (e : expr G L ty), from_tree (to_tree e) = Some (ty,e)) *
    (forall args h, from_tree_list (to_tree_hlist h) G L = Some (args, h)).
  Proof.
    intros G L.
    apply expr_rect_mut_comb; simpl; intros.
    - now rewrite value.to_from_tree_id.
    - now rewrite nat_to_from_symbol, member_to_from_nat_id.
    - rewrite H, H0.
      break_match; try congruence.
      now dependent destruction e.
    - fold @from_tree_list.
      fold @to_tree_hlist.
      rewrite H, type_name.to_from_tree_id, constr_name.to_from_symbol_id.
      now rewrite constr_type.check_constr_type_correct with (ct := ct).
    - fold @from_tree_list.
      fold @to_tree_hlist.
      rewrite nat_to_from_symbol, member_to_from_nat_id, H.
      break_match; try congruence.
      now dependent destruction e.
    - fold @from_tree_list.
      fold @to_tree_hlist.
      rewrite type.to_from_tree_id, H, H0.
      now rewrite elim.check_elim_correct with (e := e).

    - auto.
    - now rewrite H, H0.
  Qed.

  Lemma to_from_tree_id : forall G L ty (e : expr G L ty),
      from_tree (to_tree e) = Some (ty, e).
  Proof. apply to_from_tree_id_and. Qed.

  Lemma to_from_tree_list_id : forall G L args h,
      from_tree_list (to_tree_hlist h) G L = Some (args, h).
  Proof. apply to_from_tree_id_and. Qed.

  Lemma to_tree_wf_and : forall G L,
    (forall ty (e : expr G L ty), Tree.Forall symbol.wf (to_tree e)) *
    (forall l (h : hlist (expr G L) l), List.Forall (Tree.Forall symbol.wf) (to_tree_hlist h)).
  Proof.
    intros G L.
    apply expr_rect_mut_comb; simpl; auto 10 using nat_to_symbol_wf.
  Qed.

  Lemma to_tree_wf : forall G L ty (e : expr G L ty), Tree.Forall symbol.wf (to_tree e).
  Proof. apply to_tree_wf_and. Qed.
  Hint Resolve to_tree_wf.

  Lemma to_tree_hlist_wf :
    forall G L l (h : hlist (expr G L) l), List.Forall (Tree.Forall symbol.wf) (to_tree_hlist h).
  Proof. apply to_tree_wf_and. Qed.
  Hint Resolve to_tree_hlist_wf.

  Definition print {G L ty} (e : expr G L ty) : String.string :=
    print_tree (to_tree e).

  Definition pretty w {G L ty} (e : expr G L ty) : String.string :=
    pretty_tree w (to_tree e).

  Definition parse (s : String.string) {G L} : option {ty : type & expr G L ty} :=
    parse s >>= (fun t => from_tree t).

  Lemma parse_print_id : forall G L ty (e : expr G L ty), parse (print e) = Some (ty, e).
  Proof.
    unfold parse, print.
    intros.
    unfold_option.
    now rewrite parse_print_tree, to_from_tree_id by auto.
  Qed.

  Lemma parse_pretty_id : forall w G L ty (e : expr G L ty), parse (pretty w e) = Some (ty, e).
  Proof.
    unfold parse, pretty.
    intros.
    unfold_option.
    now rewrite parse_pretty_tree, to_from_tree_id by auto.
  Qed.
End expr.


Module genv.
  Fixpoint to_tree {G} (g : genv G) {struct g} : tree symbol.t.
    refine match g with
           | GenvNil => node [atom (symbol.of_string_unsafe "genvnil")]
           | @GenvCons fn_sig G' e g' =>
             match fn_sig as fn_sig_ return body_expr G' fn_sig_ -> _ with
             | pair (pair arg_ty free_tys) ret_ty => fun e =>
               node [atom (symbol.of_string_unsafe "genvcons");
                     type.to_tree arg_ty;
                     node (map type.to_tree free_tys);
                     expr.to_tree e;
                     to_tree _ g']
             end e
           end.
  Defined.

  Fixpoint from_tree (t : tree symbol.t) {struct t} : option {G : list _ & genv G}.
    refine match t with
           | node (atom tag :: l) =>
             if symbol.eq_dec tag (symbol.of_string_unsafe "genvnil")
             then match l with
                  | [] => Some ([], GenvNil)
                  | _ => None
                  end
             else if symbol.eq_dec tag (symbol.of_string_unsafe "genvcons")
             then match l with
                  | [t_arg_ty; node t_free_tys; t_e; t_g'] =>
                    match type.from_tree t_arg_ty with None => None
                    | Some arg_ty =>
                    match map_partial type.from_tree t_free_tys with None => None
                    | Some free_tys =>
                    match from_tree t_g' with None => None
                    | Some (G, g) =>
                    match @expr.from_tree t_e G (arg_ty :: free_tys) with None => None
                    | Some (ret_ty, e) =>
                      let fn_sig := pair (pair arg_ty free_tys) ret_ty in
                      Some (fn_sig :: G, @GenvCons fn_sig _ e g)
                    end end end end
                  | _ => None
                  end
             else None
           | _ => None
           end.
  Defined.

  Lemma to_from_tree_id :
    (forall G (g : genv G), from_tree (to_tree g) = Some (G, g)).
  Proof.
    induction g; simpl; intros.

    - auto.
    - break_match. break_match. simpl.
      rewrite type.to_from_tree_id.
      rewrite Forall2_map_partial with (ys := l); cycle 1.
        { eapply nth_error_Forall2.
          - rewrite map_length. auto.
          - intros. erewrite map_nth_error in *; eauto. inject_some.
            eapply type.to_from_tree_id. }
      rewrite IHg, expr.to_from_tree_id.
      auto.
  Qed.

  Lemma to_tree_wf :
    (forall G (g : genv G), Tree.Forall symbol.wf (to_tree g)).
  Proof.
    induction g; unfold to_tree.
      { auto 10. }
    do 2 break_match. econstructor.
    fold @to_tree.
    auto 10 using Forall_map_intro, Forall_forall_intro, symbol.of_string_safe_wf.
  Qed.
  Hint Resolve to_tree_wf.

  Definition print {G} (g : genv G) : String.string :=
    print_tree (to_tree g).

  Definition pretty w {G} (g : genv G) : String.string :=
    pretty_tree w (to_tree g).

  Definition parse (s : String.string) : option {G : list _ & genv G} :=
    parse s >>= (fun t => from_tree t).

  Lemma parse_print_id : forall G (g : genv G), parse (print g) = Some (G, g).
  Proof.
    unfold parse, print.
    intros.
    unfold_option.
    rewrite parse_print_tree by auto using to_tree_wf.
    now rewrite to_from_tree_id by auto.
  Qed.

  Lemma parse_pretty_id : forall w G (g : genv G), parse (pretty w g) = Some (G, g).
  Proof.
    unfold parse, pretty.
    intros.
    unfold_option.
    rewrite parse_pretty_tree by auto using to_tree_wf.
    now rewrite to_from_tree_id by auto.
  Qed.
End genv.


Require Import String.

Module compilation_unit.
  Definition current_major_version : symbol.t := symbol.of_string_unsafe "1".
  Definition current_minor_version : symbol.t := symbol.of_string_unsafe "0".
  Definition current_version_vector : list (tree symbol.t) :=
    [atom current_major_version;
     atom current_minor_version].

  Lemma current_version_vector_wf :
    List.Forall (Forall symbol.wf) current_version_vector.
  Proof. unfold current_version_vector. auto. Qed.
  Hint Resolve current_version_vector_wf.

  Definition to_tree (j : compilation_unit) : tree symbol.t :=
    node [node [atom (symbol.of_string_unsafe "version"); node current_version_vector];
          node (List.map (fun s => atom (symbol.of_string_safe s)) (names j));
          genv.to_tree (exprs j)].

  Definition from_tree (t : tree symbol.t) : option compilation_unit :=
    match t with
    | node [node [atom tag; node vs]; node name_ts; genv_t] =>
      if symbol.eq_dec tag (symbol.of_string_unsafe "version")
      then if list_eq_dec (tree_eq_dec symbol.eq_dec) vs current_version_vector
      then match genv.from_tree genv_t with None => None
           | Some (G, g) =>
           match sequence (List.map (fun t => get_atom t >>= symbol.to_string) name_ts) with
           | None => None
           | Some names => Some (CompilationUnit G g names)
           end
           end
      else None
      else None
    | _ => None
    end.

  Lemma to_from_tree_id :
    forall j, from_tree (to_tree j) = Some j.
  Proof.
    unfold from_tree, to_tree.
    intros.
    repeat break_if; try congruence.
    rewrite genv.to_from_tree_id.
    rewrite map_map.
    rewrite map_ext with (g := Some).
    - rewrite sequence_map_Some.
      destruct j; auto.
    - intros s. simpl. now rewrite symbol.to_string_of_string_safe_id.
  Qed.

  Lemma to_tree_wf : forall j, Tree.Forall symbol.wf (to_tree j).
  Proof.
    unfold to_tree.
    auto 10 using Forall_map_intro, Forall_forall_intro, symbol.of_string_safe_wf.
  Qed.
  Hint Resolve to_tree_wf.

  Definition print (j : compilation_unit) : String.string :=
    print_tree (to_tree j).

  Definition pretty w j : String.string :=
    pretty_tree w (to_tree j).

  Definition parse (s : String.string) : option compilation_unit :=
    parse s >>= from_tree.

  Lemma parse_print_id : forall j, parse (print j) = Some j.
  Proof.
    unfold parse, print.
    intros.
    unfold_option.
    now rewrite parse_print_tree, to_from_tree_id by auto.
  Qed.

  Lemma parse_pretty_id : forall w j, parse (pretty w j) = Some j.
  Proof.
    unfold parse, pretty.
    intros.
    unfold_option.
    now rewrite parse_pretty_tree, to_from_tree_id by auto.
  Qed.
End compilation_unit.
