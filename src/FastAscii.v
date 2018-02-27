(* This will be a much more efficient representation of text*)
(* lists of these will still be slower than C-style strings *)
(* But much better than Coq's builtin ascii *)
Inductive ascii :=
| ascii_0 (* | NULL*)
| ascii_1 (* | SOH*)
| ascii_2 (* | STX*)
| ascii_3 (* | ETX*)
| ascii_4 (* | EOT*)
| ascii_5 (* | ENQ*)
| ascii_6 (* | ACK*)
| ascii_7 (* | BEL*)
| ascii_8 (* | BS*)
| ascii_9 (* | TAB*)
| ascii_10 (* | LF*)
| ascii_11 (* | VT*)
| ascii_12 (* | FF*)
| ascii_13 (* | CR*)
| ascii_14 (* | SO*)
| ascii_15 (* | SI*)
| ascii_16 (* | DLE*)
| ascii_17 (* | DC1*)
| ascii_18 (* | DC2*)
| ascii_19 (* | DC3*)
| ascii_20 (* | DC4*)
| ascii_21 (* | NAK*)
| ascii_22 (* | SYN*)
| ascii_23 (* | ETB*)
| ascii_24 (* | CAN*)
| ascii_25 (* | EM*)
| ascii_26 (* | SUB*)
| ascii_27 (* | ESC*)
| ascii_28 (* | FS*)
| ascii_29 (* | GS*)
| ascii_30 (* | RS*)
| ascii_31 (* | US*)
| ascii_32 (* | SPACE*)
| ascii_33 (* | EXCLAMATION*)
| ascii_34 (* | DOUBLE_QUOTE*)
| ascii_35 (* | HASH*)
| ascii_36 (* | DOLLAR*)
| ascii_37 (* | PERCENT*)
| ascii_38 (* | AMPERSAND*)
| ascii_39 (* | SINGLE_QUOTE*)
| ascii_40 (* | LEFT_PAREN*)
| ascii_41 (* | RIGHT_PAREN*)
| ascii_42 (* | ASTERISK*)
| ascii_43 (* | PLUS*)
| ascii_44 (* | FORWARD_SINGLE_QUOTE*)
| ascii_45 (* | HYPHEN*)
| ascii_46 (* | PERIOD*)
| ascii_47 (* | SLASH*)
| ascii_48 (* | NUMERAL_0*)
| ascii_49 (* | NUMERAL_1*)
| ascii_50 (* | NUMERAL_2*)
| ascii_51 (* | NUMERAL_3*)
| ascii_52 (* | NUMERAL_4*)
| ascii_53 (* | NUMERAL_5*)
| ascii_54 (* | NUMERAL_6*)
| ascii_55 (* | NUMERAL_7*)
| ascii_56 (* | NUMERAL_8*)
| ascii_57 (* | NUMERAL_9*)
| ascii_58 (* | COLON*)
| ascii_59 (* | SEMICOLON*)
| ascii_60 (* | LESS_THAN*)
| ascii_61 (* | EQUAL*)
| ascii_62 (* | GREATER_THAN*)
| ascii_63 (* | QUESTION_MARK*)
| ascii_64 (* | AT*)
| ascii_65 (* | CAPITAL_A*)
| ascii_66 (* | CAPITAL_B*)
| ascii_67 (* | CAPITAL_C*)
| ascii_68 (* | CAPITAL_D*)
| ascii_69 (* | CAPITAL_E*)
| ascii_70 (* | CAPITAL_F*)
| ascii_71 (* | CAPITAL_G*)
| ascii_72 (* | CAPITAL_H*)
| ascii_73 (* | CAPITAL_I*)
| ascii_74 (* | CAPITAL_J*)
| ascii_75 (* | CAPITAL_K*)
| ascii_76 (* | CAPITAL_L*)
| ascii_77 (* | CAPITAL_M*)
| ascii_78 (* | CAPITAL_N*)
| ascii_79 (* | CAPITAL_O*)
| ascii_80 (* | CAPITAL_P*)
| ascii_81 (* | CAPITAL_Q*)
| ascii_82 (* | CAPITAL_R*)
| ascii_83 (* | CAPITAL_S*)
| ascii_84 (* | CAPITAL_T*)
| ascii_85 (* | CAPITAL_U*)
| ascii_86 (* | CAPITAL_V*)
| ascii_87 (* | CAPITAL_W*)
| ascii_88 (* | CAPITAL_X*)
| ascii_89 (* | CAPITAL_Y*)
| ascii_90 (* | CAPITAL_Z*)
| ascii_91 (* | LEFT_SQUARE_BRACKET*)
| ascii_92 (* | BACKSLASH*)
| ascii_93 (* | RIGHT_SQUARE_BRACKET*)
| ascii_94 (* | CARROT*)
| ascii_95 (* | UNDERSCORE*)
| ascii_96 (* | BACKTICK*)
| ascii_97 (* | LOWERCASE_A*)
| ascii_98 (* | LOWERCASE_B*)
| ascii_99 (* | LOWERCASE_C*)
| ascii_100 (* | LOWERCASE_D*)
| ascii_101 (* | LOWERCASE_E*)
| ascii_102 (* | LOWERCASE_F*)
| ascii_103 (* | LOWERCASE_G*)
| ascii_104 (* | LOWERCASE_H*)
| ascii_105 (* | LOWERCASE_I*)
| ascii_106 (* | LOWERCASE_J*)
| ascii_107 (* | LOWERCASE_K*)
| ascii_108 (* | LOWERCASE_L*)
| ascii_109 (* | LOWERCASE_M*)
| ascii_110 (* | LOWERCASE_N*)
| ascii_111 (* | LOWERCASE_O*)
| ascii_112 (* | LOWERCASE_P*)
| ascii_113 (* | LOWERCASE_Q*)
| ascii_114 (* | LOWERCASE_R*)
| ascii_115 (* | LOWERCASE_S*)
| ascii_116 (* | LOWERCASE_T*)
| ascii_117 (* | LOWERCASE_U*)
| ascii_118 (* | LOWERCASE_V*)
| ascii_119 (* | LOWERCASE_W*)
| ascii_120 (* | LOWERCASE_X*)
| ascii_121 (* | LOWERCASE_Y*)
| ascii_122 (* | LOWERCASE_Z*)
| ascii_123 (* | LEFT_CURLY_BRACE*)
| ascii_124 (* | PIPE*)
| ascii_125 (* | RIGHT_CURLY_BRACE*)
| ascii_126 (* | TILDE*)
| ascii_127 (* | DEL*)
.

Definition whitespace (x : ascii) : Prop :=
  match x with
  | ascii_9 => True
  | ascii_10 => True
  | ascii_13 => True
  | ascii_32 => True
  | _ => False
  end.
             

Definition is_whitespace_dep (x : ascii) : 
  { whitespace x } + { ~ whitespace x }.
  destruct x; try solve [right; intro; simpl in H; inversion H];
    left; constructor.
Defined.

Definition is_whitespace (x : ascii) : bool :=
  match x with
  | ascii_9 => true
  | ascii_10 => true
  | ascii_13 => true
  | ascii_32 => true
  | _ => false
  end.

Lemma is_whitespace_spec :
  forall x,
    if is_whitespace x then
      whitespace x
    else
      ~ whitespace x.
Proof.
  intros; destruct x; simpl; try constructor;
    intro; simpl in H; inversion H.
Qed.

Definition is_whitespace_elim (x : ascii) : bool :=
  @ascii_rect
    (fun _ => bool)
    false (* | NULL *)
    false (* | SOH *)
    false (* | STX *)
    false (* | ETX *)
    false (* | EOT *)
    false (* | ENQ *)
    false (* | ACK *)
    false (* | BEL *)
    false (* | BS *)
    true  (* | TAB *)
    true  (* | LF *)
    false (* | VT *)
    false (* | FF *)
    true  (* | CR *)
    false (* | SO *)
    false (* | SI *)
    false (* | DLE *)
    false (* | DC1 *)
    false (* | DC2 *)
    false (* | DC3 *)
    false (* | DC4 *)
    false (* | NAK *)
    false (* | SYN *)
    false (* | ETB *)
    false (* | CAN *)
    false (* | EM *)
    false (* | SUB *)
    false (* | ESC *)
    false (* | FS *)
    false (* | GS *)
    false (* | RS *)
    false (* | US *)
    true  (* | SPACE *)
    false (* | EXCLAMATION *)
    false (* | DOUBLE_QUOTE *)
    false (* | HASH *)
    false (* | DOLLAR *)
    false (* | PERCENT *)
    false (* | AMPERSAND *)
    false (* | SINGLE_QUOTE *)
    false (* | LEFT_PAREN *)
    false (* | RIGHT_PAREN *)
    false (* | ASTERISK *)
    false (* | PLUS *)
    false (* | FORWARD_SINGLE_QUOTE *)
    false (* | HYPHEN *)
    false (* | PERIOD *)
    false (* | SLASH *)
    false (* | NUMERAL_0 *)
    false (* | NUMERAL_1 *)
    false (* | NUMERAL_2 *)
    false (* | NUMERAL_3 *)
    false (* | NUMERAL_4 *)
    false (* | NUMERAL_5 *)
    false (* | NUMERAL_6 *)
    false (* | NUMERAL_7 *)
    false (* | NUMERAL_8 *)
    false (* | NUMERAL_9 *)
    false (* | COLON *)
    false (* | SEMICOLON *)
    false (* | LESS_THAN *)
    false (* | EQUAL *)
    false (* | GREATER_THAN *)
    false (* | QUESTION_MARK *)
    false (* | AT *)
    false (* | CAPITAL_A *)
    false (* | CAPITAL_B *)
    false (* | CAPITAL_C *)
    false (* | CAPITAL_D *)
    false (* | CAPITAL_E *)
    false (* | CAPITAL_F *)
    false (* | CAPITAL_G *)
    false (* | CAPITAL_H *)
    false (* | CAPITAL_I *)
    false (* | CAPITAL_J *)
    false (* | CAPITAL_K *)
    false (* | CAPITAL_L *)
    false (* | CAPITAL_M *)
    false (* | CAPITAL_N *)
    false (* | CAPITAL_O *)
    false (* | CAPITAL_P *)
    false (* | CAPITAL_Q *)
    false (* | CAPITAL_R *)
    false (* | CAPITAL_S *)
    false (* | CAPITAL_T *)
    false (* | CAPITAL_U *)
    false (* | CAPITAL_V *)
    false (* | CAPITAL_W *)
    false (* | CAPITAL_X *)
    false (* | CAPITAL_Y *)
    false (* | CAPITAL_Z *)
    false (* | LEFT_SQUARE_BRACKET *)
    false (* | BACKSLASH *)
    false (* | RIGHT_SQUARE_BRACKET *)
    false (* | CARROT *)
    false (* | UNDERSCORE *)
    false (* | BACKTICK *)
    false (* | LOWERCASE_A *)
    false (* | LOWERCASE_B *)
    false (* | LOWERCASE_C *)
    false (* | LOWERCASE_D *)
    false (* | LOWERCASE_E *)
    false (* | LOWERCASE_F *)
    false (* | LOWERCASE_G *)
    false (* | LOWERCASE_H *)
    false (* | LOWERCASE_I *)
    false (* | LOWERCASE_J *)
    false (* | LOWERCASE_K *)
    false (* | LOWERCASE_L *)
    false (* | LOWERCASE_M *)
    false (* | LOWERCASE_N *)
    false (* | LOWERCASE_O *)
    false (* | LOWERCASE_P *)
    false (* | LOWERCASE_Q *)
    false (* | LOWERCASE_R *)
    false (* | LOWERCASE_S *)
    false (* | LOWERCASE_T *)
    false (* | LOWERCASE_U *)
    false (* | LOWERCASE_V *)
    false (* | LOWERCASE_W *)
    false (* | LOWERCASE_X *)
    false (* | LOWERCASE_Y *)
    false (* | LOWERCASE_Z *)
    false (* | LEFT_CURLY_BRACE *)
    false (* | PIPE *)
    false (* | RIGHT_CURLY_BRACE *)
    false (* | TILDE *)
    false (* | DEL *)
    x
.    


Lemma is_whitespace_equiv :
  forall x,
    is_whitespace x = is_whitespace_elim x.
Proof.
  intros. destruct x; reflexivity.
Qed.


Definition eq_bool (x y : ascii) : bool :=
  match x,y with
  | ascii_0, ascii_0 => true
  | ascii_1, ascii_1 => true
  | ascii_2, ascii_2 => true
  | ascii_3, ascii_3 => true
  | ascii_4, ascii_4 => true
  | ascii_5, ascii_5 => true
  | ascii_6, ascii_6 => true
  | ascii_7, ascii_7 => true
  | ascii_8, ascii_8 => true
  | ascii_9, ascii_9 => true
  | ascii_10, ascii_10 => true
  | ascii_11, ascii_11 => true
  | ascii_12, ascii_12 => true
  | ascii_13, ascii_13 => true
  | ascii_14, ascii_14 => true
  | ascii_15, ascii_15 => true
  | ascii_16, ascii_16 => true
  | ascii_17, ascii_17 => true
  | ascii_18, ascii_18 => true
  | ascii_19, ascii_19 => true
  | ascii_20, ascii_20 => true
  | ascii_21, ascii_21 => true
  | ascii_22, ascii_22 => true
  | ascii_23, ascii_23 => true
  | ascii_24, ascii_24 => true
  | ascii_25, ascii_25 => true
  | ascii_26, ascii_26 => true
  | ascii_27, ascii_27 => true
  | ascii_28, ascii_28 => true
  | ascii_29, ascii_29 => true
  | ascii_30, ascii_30 => true
  | ascii_31, ascii_31 => true
  | ascii_32, ascii_32 => true
  | ascii_33, ascii_33 => true
  | ascii_34, ascii_34 => true
  | ascii_35, ascii_35 => true
  | ascii_36, ascii_36 => true
  | ascii_37, ascii_37 => true
  | ascii_38, ascii_38 => true
  | ascii_39, ascii_39 => true
  | ascii_40, ascii_40 => true
  | ascii_41, ascii_41 => true
  | ascii_42, ascii_42 => true
  | ascii_43, ascii_43 => true
  | ascii_44, ascii_44 => true
  | ascii_45, ascii_45 => true
  | ascii_46, ascii_46 => true
  | ascii_47, ascii_47 => true
  | ascii_48, ascii_48 => true
  | ascii_49, ascii_49 => true
  | ascii_50, ascii_50 => true
  | ascii_51, ascii_51 => true
  | ascii_52, ascii_52 => true
  | ascii_53, ascii_53 => true
  | ascii_54, ascii_54 => true
  | ascii_55, ascii_55 => true
  | ascii_56, ascii_56 => true
  | ascii_57, ascii_57 => true
  | ascii_58, ascii_58 => true
  | ascii_59, ascii_59 => true
  | ascii_60, ascii_60 => true
  | ascii_61, ascii_61 => true
  | ascii_62, ascii_62 => true
  | ascii_63, ascii_63 => true
  | ascii_64, ascii_64 => true
  | ascii_65, ascii_65 => true
  | ascii_66, ascii_66 => true
  | ascii_67, ascii_67 => true
  | ascii_68, ascii_68 => true
  | ascii_69, ascii_69 => true
  | ascii_70, ascii_70 => true
  | ascii_71, ascii_71 => true
  | ascii_72, ascii_72 => true
  | ascii_73, ascii_73 => true
  | ascii_74, ascii_74 => true
  | ascii_75, ascii_75 => true
  | ascii_76, ascii_76 => true
  | ascii_77, ascii_77 => true
  | ascii_78, ascii_78 => true
  | ascii_79, ascii_79 => true
  | ascii_80, ascii_80 => true
  | ascii_81, ascii_81 => true
  | ascii_82, ascii_82 => true
  | ascii_83, ascii_83 => true
  | ascii_84, ascii_84 => true
  | ascii_85, ascii_85 => true
  | ascii_86, ascii_86 => true
  | ascii_87, ascii_87 => true
  | ascii_88, ascii_88 => true
  | ascii_89, ascii_89 => true
  | ascii_90, ascii_90 => true
  | ascii_91, ascii_91 => true
  | ascii_92, ascii_92 => true
  | ascii_93, ascii_93 => true
  | ascii_94, ascii_94 => true
  | ascii_95, ascii_95 => true
  | ascii_96, ascii_96 => true
  | ascii_97, ascii_97 => true
  | ascii_98, ascii_98 => true
  | ascii_99, ascii_99 => true
  | ascii_100, ascii_100 => true
  | ascii_101, ascii_101 => true
  | ascii_102, ascii_102 => true
  | ascii_103, ascii_103 => true
  | ascii_104, ascii_104 => true
  | ascii_105, ascii_105 => true
  | ascii_106, ascii_106 => true
  | ascii_107, ascii_107 => true
  | ascii_108, ascii_108 => true
  | ascii_109, ascii_109 => true
  | ascii_110, ascii_110 => true
  | ascii_111, ascii_111 => true
  | ascii_112, ascii_112 => true
  | ascii_113, ascii_113 => true
  | ascii_114, ascii_114 => true
  | ascii_115, ascii_115 => true
  | ascii_116, ascii_116 => true
  | ascii_117, ascii_117 => true
  | ascii_118, ascii_118 => true
  | ascii_119, ascii_119 => true
  | ascii_120, ascii_120 => true
  | ascii_121, ascii_121 => true
  | ascii_122, ascii_122 => true
  | ascii_123, ascii_123 => true
  | ascii_124, ascii_124 => true
  | ascii_125, ascii_125 => true
  | ascii_126, ascii_126 => true
  | ascii_127, ascii_127 => true
  | _,_ => false
  end.


Definition elim_num (x : nat) :=
  @ascii_rect (fun _ => bool)
              (Nat.eqb x 0)
              (Nat.eqb x 1)
              (Nat.eqb x 2)
              (Nat.eqb x 3)
              (Nat.eqb x 4)
              (Nat.eqb x 5)
              (Nat.eqb x 6)
              (Nat.eqb x 7)
              (Nat.eqb x 8)
              (Nat.eqb x 9)
              (Nat.eqb x 10)
              (Nat.eqb x 11)
              (Nat.eqb x 12)
              (Nat.eqb x 13)
              (Nat.eqb x 14)
              (Nat.eqb x 15)
              (Nat.eqb x 16)
              (Nat.eqb x 17)
              (Nat.eqb x 18)
              (Nat.eqb x 19)
              (Nat.eqb x 20)
              (Nat.eqb x 21)
              (Nat.eqb x 22)
              (Nat.eqb x 23)
              (Nat.eqb x 24)
              (Nat.eqb x 25)
              (Nat.eqb x 26)
              (Nat.eqb x 27)
              (Nat.eqb x 28)
              (Nat.eqb x 29)
              (Nat.eqb x 30)
              (Nat.eqb x 31)
              (Nat.eqb x 32)
              (Nat.eqb x 33)
              (Nat.eqb x 34)
              (Nat.eqb x 35)
              (Nat.eqb x 36)
              (Nat.eqb x 37)
              (Nat.eqb x 38)
              (Nat.eqb x 39)
              (Nat.eqb x 40)
              (Nat.eqb x 41)
              (Nat.eqb x 42)
              (Nat.eqb x 43)
              (Nat.eqb x 44)
              (Nat.eqb x 45)
              (Nat.eqb x 46)
              (Nat.eqb x 47)
              (Nat.eqb x 48)
              (Nat.eqb x 49)
              (Nat.eqb x 50)
              (Nat.eqb x 51)
              (Nat.eqb x 52)
              (Nat.eqb x 53)
              (Nat.eqb x 54)
              (Nat.eqb x 55)
              (Nat.eqb x 56)
              (Nat.eqb x 57)
              (Nat.eqb x 58)
              (Nat.eqb x 59)
              (Nat.eqb x 60)
              (Nat.eqb x 61)
              (Nat.eqb x 62)
              (Nat.eqb x 63)
              (Nat.eqb x 64)
              (Nat.eqb x 65)
              (Nat.eqb x 66)
              (Nat.eqb x 67)
              (Nat.eqb x 68)
              (Nat.eqb x 69)
              (Nat.eqb x 70)
              (Nat.eqb x 71)
              (Nat.eqb x 72)
              (Nat.eqb x 73)
              (Nat.eqb x 74)
              (Nat.eqb x 75)
              (Nat.eqb x 76)
              (Nat.eqb x 77)
              (Nat.eqb x 78)
              (Nat.eqb x 79)
              (Nat.eqb x 80)
              (Nat.eqb x 81)
              (Nat.eqb x 82)
              (Nat.eqb x 83)
              (Nat.eqb x 84)
              (Nat.eqb x 85)
              (Nat.eqb x 86)
              (Nat.eqb x 87)
              (Nat.eqb x 88)
              (Nat.eqb x 89)
              (Nat.eqb x 90)
              (Nat.eqb x 91)
              (Nat.eqb x 92)
              (Nat.eqb x 93)
              (Nat.eqb x 94)
              (Nat.eqb x 95)
              (Nat.eqb x 96)
              (Nat.eqb x 97)
              (Nat.eqb x 98)
              (Nat.eqb x 99)
              (Nat.eqb x 100)
              (Nat.eqb x 101)
              (Nat.eqb x 102)
              (Nat.eqb x 103)
              (Nat.eqb x 104)
              (Nat.eqb x 105)
              (Nat.eqb x 106)
              (Nat.eqb x 107)
              (Nat.eqb x 108)
              (Nat.eqb x 109)
              (Nat.eqb x 110)
              (Nat.eqb x 111)
              (Nat.eqb x 112)
              (Nat.eqb x 113)
              (Nat.eqb x 114)
              (Nat.eqb x 115)
              (Nat.eqb x 116)
              (Nat.eqb x 117)
              (Nat.eqb x 118)
              (Nat.eqb x 119)
              (Nat.eqb x 120)
              (Nat.eqb x 121)
              (Nat.eqb x 122)
              (Nat.eqb x 123)
              (Nat.eqb x 124)
              (Nat.eqb x 125)
              (Nat.eqb x 126)
              (Nat.eqb x 127)
              .


Definition eq_bool_elim (x y : ascii) : bool :=
  @ascii_rect (fun _ => ascii -> bool)
              (elim_num 0)
              (elim_num 1)
              (elim_num 2)
              (elim_num 3)
              (elim_num 4)
              (elim_num 5)
              (elim_num 6)
              (elim_num 7)
              (elim_num 8)
              (elim_num 9)
              (elim_num 10)
              (elim_num 11)
              (elim_num 12)
              (elim_num 13)
              (elim_num 14)
              (elim_num 15)
              (elim_num 16)
              (elim_num 17)
              (elim_num 18)
              (elim_num 19)
              (elim_num 20)
              (elim_num 21)
              (elim_num 22)
              (elim_num 23)
              (elim_num 24)
              (elim_num 25)
              (elim_num 26)
              (elim_num 27)
              (elim_num 28)
              (elim_num 29)
              (elim_num 30)
              (elim_num 31)
              (elim_num 32)
              (elim_num 33)
              (elim_num 34)
              (elim_num 35)
              (elim_num 36)
              (elim_num 37)
              (elim_num 38)
              (elim_num 39)
              (elim_num 40)
              (elim_num 41)
              (elim_num 42)
              (elim_num 43)
              (elim_num 44)
              (elim_num 45)
              (elim_num 46)
              (elim_num 47)
              (elim_num 48)
              (elim_num 49)
              (elim_num 50)
              (elim_num 51)
              (elim_num 52)
              (elim_num 53)
              (elim_num 54)
              (elim_num 55)
              (elim_num 56)
              (elim_num 57)
              (elim_num 58)
              (elim_num 59)
              (elim_num 60)
              (elim_num 61)
              (elim_num 62)
              (elim_num 63)
              (elim_num 64)
              (elim_num 65)
              (elim_num 66)
              (elim_num 67)
              (elim_num 68)
              (elim_num 69)
              (elim_num 70)
              (elim_num 71)
              (elim_num 72)
              (elim_num 73)
              (elim_num 74)
              (elim_num 75)
              (elim_num 76)
              (elim_num 77)
              (elim_num 78)
              (elim_num 79)
              (elim_num 80)
              (elim_num 81)
              (elim_num 82)
              (elim_num 83)
              (elim_num 84)
              (elim_num 85)
              (elim_num 86)
              (elim_num 87)
              (elim_num 88)
              (elim_num 89)
              (elim_num 90)
              (elim_num 91)
              (elim_num 92)
              (elim_num 93)
              (elim_num 94)
              (elim_num 95)
              (elim_num 96)
              (elim_num 97)
              (elim_num 98)
              (elim_num 99)
              (elim_num 100)
              (elim_num 101)
              (elim_num 102)
              (elim_num 103)
              (elim_num 104)
              (elim_num 105)
              (elim_num 106)
              (elim_num 107)
              (elim_num 108)
              (elim_num 109)
              (elim_num 110)
              (elim_num 111)
              (elim_num 112)
              (elim_num 113)
              (elim_num 114)
              (elim_num 115)
              (elim_num 116)
              (elim_num 117)
              (elim_num 118)
              (elim_num 119)
              (elim_num 120)
              (elim_num 121)
              (elim_num 122)
              (elim_num 123)
              (elim_num 124)
              (elim_num 125)
              (elim_num 126)
              (elim_num 127)
              x y.


Lemma eq_bool_equiv :
  forall x y,
    eq_bool x y = eq_bool_elim x y.
Proof.
  intros.
  destruct x; destruct y; simpl; try reflexivity.
Qed.
  
              
(* Conversion from normal coq strings *)
Require Import String.

(* Utility function to convert to flatter rep of ascii *)
Definition ascii_to_fast_ascii (a : Ascii.ascii) : ascii :=
  match a with
  | Ascii.Ascii false false false false false false false false => ascii_0 (* NULL*)
  | Ascii.Ascii true  false false false false false false false  => ascii_1 (* SOH*)
  | Ascii.Ascii  false  true false false false false false false => ascii_2 (* STX*)
  | Ascii.Ascii  true  true false false false false false false  => ascii_3 (* ETX*)
  | Ascii.Ascii false   false true false false false false false => ascii_4 (* EOT*)
  | Ascii.Ascii true   false true false false false false false  => ascii_5 (* ENQ*)
  | Ascii.Ascii  false   true true false false false false false => ascii_6 (* ACK*)
  | Ascii.Ascii  true   true true false false false false false  => ascii_7 (* BEL*)
  | Ascii.Ascii false  false  false true false false false false => ascii_8 (* BS*)
  | Ascii.Ascii true  false  false true false false false false  => ascii_9 (* TAB*)
  | Ascii.Ascii  false  true  false true false false false false => ascii_10 (* LF*)
  | Ascii.Ascii  true  true  false true false false false false  => ascii_11 (* VT*)
  | Ascii.Ascii false   false  true true false false false false => ascii_12 (* FF*)
  | Ascii.Ascii true   false  true true false false false false  => ascii_13 (* CR*)
  | Ascii.Ascii  false   true  true true false false false false => ascii_14 (* SO*)
  | Ascii.Ascii  true   true  true true false false false false  => ascii_15 (* SI*)
  | Ascii.Ascii false  false false  false true false false false => ascii_16 (* DLE*)
  | Ascii.Ascii true  false false  false true false false false  => ascii_17 (* DC1*)
  | Ascii.Ascii  false  true false  false true false false false => ascii_18 (* DC2*)
  | Ascii.Ascii  true  true false  false true false false false  => ascii_19 (* DC3*)
  | Ascii.Ascii false   false true  false true false false false => ascii_20 (* DC4*)
  | Ascii.Ascii true   false true  false true false false false  => ascii_21 (* NAK*)
  | Ascii.Ascii  false   true true  false true false false false => ascii_22 (* SYN*)
  | Ascii.Ascii  true   true true  false true false false false  => ascii_23 (* ETB*)
  | Ascii.Ascii false  false  false  true true false false false => ascii_24 (* CAN*)
  | Ascii.Ascii true  false  false  true true false false false  => ascii_25 (* EM*)
  | Ascii.Ascii  false  true  false  true true false false false => ascii_26 (* SUB*)
  | Ascii.Ascii  true  true  false  true true false false false  => ascii_27 (* ESC*)
  | Ascii.Ascii false   false  true  true true false false false => ascii_28 (* FS*)
  | Ascii.Ascii true   false  true  true true false false false  => ascii_29 (* GS*)
  | Ascii.Ascii  false   true  true  true true false false false => ascii_30 (* RS*)
  | Ascii.Ascii  true   true  true  true true false false false  => ascii_31 (* US*)
  | Ascii.Ascii false  false  false false false true false false => ascii_32 (* SPACE*)
  | Ascii.Ascii true  false  false false false true false false  => ascii_33 (* EXCLAMATION*)
  | Ascii.Ascii  false  true  false false false true false false => ascii_34 (* DOUBLE_QUOTE*)
  | Ascii.Ascii  true  true  false false false true false false  => ascii_35 (* HASH*)
  | Ascii.Ascii false   false  true false false true false false => ascii_36 (* DOLLAR*)
  | Ascii.Ascii true   false  true false false true false false  => ascii_37 (* PERCENT*)
  | Ascii.Ascii  false   true  true false false true false false => ascii_38 (* AMPERSAND*)
  | Ascii.Ascii  true   true  true false false true false false  => ascii_39 (* SINGLE_QUOTE*)
  | Ascii.Ascii false  false   false true false true false false => ascii_40 (* LEFT_PAREN*)
  | Ascii.Ascii true  false   false true false true false false  => ascii_41 (* RIGHT_PAREN*)
  | Ascii.Ascii  false  true   false true false true false false => ascii_42 (* ASTERISK*)
  | Ascii.Ascii  true  true   false true false true false false  => ascii_43 (* PLUS*)
  | Ascii.Ascii false   false   true true false true false false => ascii_44 (* FORWARD_SINGLE_QUOTE*)
  | Ascii.Ascii true   false   true true false true false false  => ascii_45 (* HYPHEN*)
  | Ascii.Ascii  false   true   true true false true false false => ascii_46 (* PERIOD*)
  | Ascii.Ascii  true   true   true true false true false false  => ascii_47 (* SLASH*)
  | Ascii.Ascii false  false  false  false true true false false => ascii_48 (* NUMERAL_0*)
  | Ascii.Ascii true  false  false  false true true false false  => ascii_49 (* NUMERAL_1*)
  | Ascii.Ascii  false  true  false  false true true false false => ascii_50 (* NUMERAL_2*)
  | Ascii.Ascii  true  true  false  false true true false false  => ascii_51 (* NUMERAL_3*)
  | Ascii.Ascii false   false  true  false true true false false => ascii_52 (* NUMERAL_4*)
  | Ascii.Ascii true   false  true  false true true false false  => ascii_53 (* NUMERAL_5*)
  | Ascii.Ascii  false   true  true  false true true false false => ascii_54 (* NUMERAL_6*)
  | Ascii.Ascii  true   true  true  false true true false false  => ascii_55 (* NUMERAL_7*)
  | Ascii.Ascii false  false   false  true true true false false => ascii_56 (* NUMERAL_8*)
  | Ascii.Ascii true  false   false  true true true false false  => ascii_57 (* NUMERAL_9*)
  | Ascii.Ascii  false  true   false  true true true false false => ascii_58 (* COLON*)
  | Ascii.Ascii  true  true   false  true true true false false  => ascii_59 (* SEMICOLON*)
  | Ascii.Ascii false   false   true  true true true false false => ascii_60 (* LESS_THAN*)
  | Ascii.Ascii true   false   true  true true true false false  => ascii_61 (* EQUAL*)
  | Ascii.Ascii  false   true   true  true true true false false => ascii_62 (* GREATER_THAN*)
  | Ascii.Ascii  true   true   true  true true true false false  => ascii_63 (* QUESTION_MARK*)
  | Ascii.Ascii false   false false false false false true false => ascii_64 (* AT*)
  | Ascii.Ascii true   false false false false false true false  => ascii_65 (* CAPITAL_A*)
  | Ascii.Ascii  false   true false false false false true false => ascii_66 (* CAPITAL_B*)
  | Ascii.Ascii  true   true false false false false true false  => ascii_67 (* CAPITAL_C*)
  | Ascii.Ascii false    false true false false false true false => ascii_68 (* CAPITAL_D*)
  | Ascii.Ascii true    false true false false false true false  => ascii_69 (* CAPITAL_E*)
  | Ascii.Ascii  false    true true false false false true false => ascii_70 (* CAPITAL_F*)
  | Ascii.Ascii  true    true true false false false true false  => ascii_71 (* CAPITAL_G*)
  | Ascii.Ascii false   false  false true false false true false => ascii_72 (* CAPITAL_H*)
  | Ascii.Ascii true   false  false true false false true false  => ascii_73 (* CAPITAL_I*)
  | Ascii.Ascii  false   true  false true false false true false => ascii_74 (* CAPITAL_J*)
  | Ascii.Ascii  true   true  false true false false true false  => ascii_75 (* CAPITAL_K*)
  | Ascii.Ascii false    false  true true false false true false => ascii_76 (* CAPITAL_L*)
  | Ascii.Ascii true    false  true true false false true false  => ascii_77 (* CAPITAL_M*)
  | Ascii.Ascii  false    true  true true false false true false => ascii_78 (* CAPITAL_N*)
  | Ascii.Ascii  true    true  true true false false true false  => ascii_79 (* CAPITAL_O*)
  | Ascii.Ascii false   false false  false true false true false => ascii_80 (* CAPITAL_P*)
  | Ascii.Ascii true   false false  false true false true false  => ascii_81 (* CAPITAL_Q*)
  | Ascii.Ascii  false   true false  false true false true false => ascii_82 (* CAPITAL_R*)
  | Ascii.Ascii  true   true false  false true false true false  => ascii_83 (* CAPITAL_S*)
  | Ascii.Ascii false    false true  false true false true false => ascii_84 (* CAPITAL_T*)
  | Ascii.Ascii true    false true  false true false true false  => ascii_85 (* CAPITAL_U*)
  | Ascii.Ascii  false    true true  false true false true false => ascii_86 (* CAPITAL_V*)
  | Ascii.Ascii  true    true true  false true false true false  => ascii_87 (* CAPITAL_W*)
  | Ascii.Ascii false   false  false  true true false true false => ascii_88 (* CAPITAL_X*)
  | Ascii.Ascii true   false  false  true true false true false  => ascii_89 (* CAPITAL_Y*)
  | Ascii.Ascii  false   true  false  true true false true false => ascii_90 (* CAPITAL_Z*)
  | Ascii.Ascii  true   true  false  true true false true false  => ascii_91 (* LEFT_SQUARE_BRACKET*)
  | Ascii.Ascii false    false  true  true true false true false => ascii_92 (* BACKSLASH*)
  | Ascii.Ascii true    false  true  true true false true false  => ascii_93 (* RIGHT_SQUARE_BRACKET*)
  | Ascii.Ascii  false    true  true  true true false true false => ascii_94 (* CARROT*)
  | Ascii.Ascii  true    true  true  true true false true false  => ascii_95 (* UNDERSCORE*)
  | Ascii.Ascii false   false  false false false true true false => ascii_96 (* BACKTICK*)
  | Ascii.Ascii true   false  false false false true true false  => ascii_97 (* LOWERCASE_A*)
  | Ascii.Ascii  false   true  false false false true true false => ascii_98 (* LOWERCASE_B*)
  | Ascii.Ascii  true   true  false false false true true false  => ascii_99 (* LOWERCASE_C*)
  | Ascii.Ascii false    false  true false false true true false => ascii_100 (* LOWERCASE_D*)
  | Ascii.Ascii true    false  true false false true true false  => ascii_101 (* LOWERCASE_E*)
  | Ascii.Ascii  false    true  true false false true true false => ascii_102 (* LOWERCASE_F*)
  | Ascii.Ascii  true    true  true false false true true false  => ascii_103 (* LOWERCASE_G*)
  | Ascii.Ascii false   false   false true false true true false => ascii_104 (* LOWERCASE_H*)
  | Ascii.Ascii true   false   false true false true true false  => ascii_105 (* LOWERCASE_I*)
  | Ascii.Ascii  false   true   false true false true true false => ascii_106 (* LOWERCASE_J*)
  | Ascii.Ascii  true   true   false true false true true false  => ascii_107 (* LOWERCASE_K*)
  | Ascii.Ascii false    false   true true false true true false => ascii_108 (* LOWERCASE_L*)
  | Ascii.Ascii true    false   true true false true true false  => ascii_109 (* LOWERCASE_M*)
  | Ascii.Ascii  false    true   true true false true true false => ascii_110 (* LOWERCASE_N*)
  | Ascii.Ascii  true    true   true true false true true false  => ascii_111 (* LOWERCASE_O*)
  | Ascii.Ascii false   false  false  false true true true false => ascii_112 (* LOWERCASE_P*)
  | Ascii.Ascii true   false  false  false true true true false  => ascii_113 (* LOWERCASE_Q*)
  | Ascii.Ascii  false   true  false  false true true true false => ascii_114 (* LOWERCASE_R*)
  | Ascii.Ascii  true   true  false  false true true true false  => ascii_115 (* LOWERCASE_S*)
  | Ascii.Ascii false    false  true  false true true true false => ascii_116 (* LOWERCASE_T*)
  | Ascii.Ascii true    false  true  false true true true false  => ascii_117 (* LOWERCASE_U*)
  | Ascii.Ascii  false    true  true  false true true true false => ascii_118 (* LOWERCASE_V*)
  | Ascii.Ascii  true    true  true  false true true true false  => ascii_119 (* LOWERCASE_W*)
  | Ascii.Ascii false   false   false  true true true true false => ascii_120 (* LOWERCASE_X*)
  | Ascii.Ascii true   false   false  true true true true false  => ascii_121 (* LOWERCASE_Y*)
  | Ascii.Ascii  false   true   false  true true true true false => ascii_122 (* LOWERCASE_Z*)
  | Ascii.Ascii  true   true   false  true true true true false  => ascii_123 (* LEFT_CURLY_BRACE*)
  | Ascii.Ascii false    false   true  true true true true false => ascii_124 (* PIPE*)
  | Ascii.Ascii true    false   true  true true true true false  => ascii_125 (* RIGHT_CURLY_BRACE*)
  | Ascii.Ascii  false    true   true  true true true true false => ascii_126 (* TILDE*)
  | Ascii.Ascii  true    true   true  true true true true false  => ascii_127 (* DEL*)
  | Ascii.Ascii _ _ _ _ _ _ _ true  => ascii_0 (* NULL*)
  end.

Fixpoint string_to_fast_string (s : string) : list ascii :=
  match s with
  | EmptyString => nil
  | String a s' =>
    (ascii_to_fast_ascii a) :: string_to_fast_string s'
  end.

(* (* Uncommment to verify eq_bool *) *)
(* Lemma eq_bool_spec : *)
(*   forall x y, *)
(*     if eq_bool x y then *)
(*       x = y *)
(*     else *)
(*       x <> y. *)
(* Proof. *)
(*   intros. *)
(*   destruct x; destruct y; simpl; congruence. *)
(* Qed. *)

