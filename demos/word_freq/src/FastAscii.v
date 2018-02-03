(* This will be a much more efficient representation of text*)
(* lists of these will still be slower than C-style strings *)
(* But much better than Coq's builtin ascii *)
Inductive ascii :=
| NULL
| SOH
| STX
| ETX
| EOT
| ENQ
| ACK
| BEL
| BS
| TAB
| LF
| VT
| FF
| CR
| SO
| SI
| DLE
| DC1
| DC2
| DC3
| DC4
| NAK
| SYN
| ETB
| CAN
| EM
| SUB
| ESC
| FS
| GS
| RS
| US
| SPACE
| EXCLAMATION
| DOUBLE_QUOTE
| HASH
| DOLLAR
| PERCENT
| AMPERSAND
| SINGLE_QUOTE
| LEFT_PAREN
| RIGHT_PAREN
| ASTERISK
| PLUS
| FORWARD_SINGLE_QUOTE
| HYPHEN
| PERIOD
| SLASH
| NUMERAL_0
| NUMERAL_1
| NUMERAL_2
| NUMERAL_3
| NUMERAL_4
| NUMERAL_5
| NUMERAL_6
| NUMERAL_7
| NUMERAL_8
| NUMERAL_9
| COLON
| SEMICOLON
| LESS_THAN
| EQUAL
| GREATER_THAN
| QUESTION_MARK
| AT
| CAPITAL_A
| CAPITAL_B
| CAPITAL_C
| CAPITAL_D
| CAPITAL_E
| CAPITAL_F
| CAPITAL_G
| CAPITAL_H
| CAPITAL_I
| CAPITAL_J
| CAPITAL_K
| CAPITAL_L
| CAPITAL_M
| CAPITAL_N
| CAPITAL_O
| CAPITAL_P
| CAPITAL_Q
| CAPITAL_R
| CAPITAL_S
| CAPITAL_T
| CAPITAL_U
| CAPITAL_V
| CAPITAL_W
| CAPITAL_X
| CAPITAL_Y
| CAPITAL_Z
| LEFT_SQUARE_BRACKET
| BACKSLASH
| RIGHT_SQUARE_BRACKET
| CARROT
| UNDERSCORE
| BACKTICK
| LOWERCASE_A
| LOWERCASE_B
| LOWERCASE_C
| LOWERCASE_D
| LOWERCASE_E
| LOWERCASE_F
| LOWERCASE_G
| LOWERCASE_H
| LOWERCASE_I
| LOWERCASE_J
| LOWERCASE_K
| LOWERCASE_L
| LOWERCASE_M
| LOWERCASE_N
| LOWERCASE_O
| LOWERCASE_P
| LOWERCASE_Q
| LOWERCASE_R
| LOWERCASE_S
| LOWERCASE_T
| LOWERCASE_U
| LOWERCASE_V
| LOWERCASE_W
| LOWERCASE_X
| LOWERCASE_Y
| LOWERCASE_Z
| LEFT_CURLY_BRACE
| PIPE
| RIGHT_CURLY_BRACE
| TILDE
| DEL
.


Definition whitespace (x : ascii) : Prop :=
  match x with
  | SPACE => True
  | TAB => True
  | CR => True
  | LF => True
  | _ => False
  end.
             

Definition is_whitespace_dep (x : ascii) : 
  { whitespace x } + { ~ whitespace x }.
  destruct x; try solve [right; intro; simpl in H; inversion H];
    left; constructor.
Defined.

Definition is_whitespace (x : ascii) : bool :=
  match x with
  | SPACE => true
  | TAB => true
  | CR => true
  | LF => true
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


Definition eq_bool (x y : ascii) : bool :=
  match x,y with
| NULL, NULL => true
| SOH, SOH => true
| STX, STX => true
| ETX, ETX => true
| EOT, EOT => true
| ENQ, ENQ => true
| ACK, ACK => true
| BEL, BEL => true
| BS, BS => true
| TAB, TAB => true
| LF, LF => true
| VT, VT => true
| FF, FF => true
| CR, CR => true
| SO, SO => true
| SI, SI => true
| DLE, DLE => true
| DC1, DC1 => true
| DC2, DC2 => true
| DC3, DC3 => true
| DC4, DC4 => true
| NAK, NAK => true
| SYN, SYN => true
| ETB, ETB => true
| CAN, CAN => true
| EM, EM => true
| SUB, SUB => true
| ESC, ESC => true
| FS, FS => true
| GS, GS => true
| RS, RS => true
| US, US => true
| SPACE, SPACE => true
| EXCLAMATION, EXCLAMATION => true
| DOUBLE_QUOTE, DOUBLE_QUOTE => true
| HASH, HASH => true
| DOLLAR, DOLLAR => true
| PERCENT, PERCENT => true
| AMPERSAND, AMPERSAND => true
| SINGLE_QUOTE, SINGLE_QUOTE => true
| LEFT_PAREN, LEFT_PAREN => true
| RIGHT_PAREN, RIGHT_PAREN => true
| ASTERISK, ASTERISK => true
| PLUS, PLUS => true
| FORWARD_SINGLE_QUOTE, FORWARD_SINGLE_QUOTE => true
| HYPHEN, HYPHEN => true
| PERIOD, PERIOD => true
| SLASH, SLASH => true
| NUMERAL_0, NUMERAL_0 => true
| NUMERAL_1, NUMERAL_1 => true
| NUMERAL_2, NUMERAL_2 => true
| NUMERAL_3, NUMERAL_3 => true
| NUMERAL_4, NUMERAL_4 => true
| NUMERAL_5, NUMERAL_5 => true
| NUMERAL_6, NUMERAL_6 => true
| NUMERAL_7, NUMERAL_7 => true
| NUMERAL_8, NUMERAL_8 => true
| NUMERAL_9, NUMERAL_9 => true
| COLON, COLON => true
| SEMICOLON, SEMICOLON => true
| LESS_THAN, LESS_THAN => true
| EQUAL, EQUAL => true
| GREATER_THAN, GREATER_THAN => true
| QUESTION_MARK, QUESTION_MARK => true
| AT, AT => true
| CAPITAL_A, CAPITAL_A => true
| CAPITAL_B, CAPITAL_B => true
| CAPITAL_C, CAPITAL_C => true
| CAPITAL_D, CAPITAL_D => true
| CAPITAL_E, CAPITAL_E => true
| CAPITAL_F, CAPITAL_F => true
| CAPITAL_G, CAPITAL_G => true
| CAPITAL_H, CAPITAL_H => true
| CAPITAL_I, CAPITAL_I => true
| CAPITAL_J, CAPITAL_J => true
| CAPITAL_K, CAPITAL_K => true
| CAPITAL_L, CAPITAL_L => true
| CAPITAL_M, CAPITAL_M => true
| CAPITAL_N, CAPITAL_N => true
| CAPITAL_O, CAPITAL_O => true
| CAPITAL_P, CAPITAL_P => true
| CAPITAL_Q, CAPITAL_Q => true
| CAPITAL_R, CAPITAL_R => true
| CAPITAL_S, CAPITAL_S => true
| CAPITAL_T, CAPITAL_T => true
| CAPITAL_U, CAPITAL_U => true
| CAPITAL_V, CAPITAL_V => true
| CAPITAL_W, CAPITAL_W => true
| CAPITAL_X, CAPITAL_X => true
| CAPITAL_Y, CAPITAL_Y => true
| CAPITAL_Z, CAPITAL_Z => true
| LEFT_SQUARE_BRACKET, LEFT_SQUARE_BRACKET => true
| BACKSLASH, BACKSLASH => true
| RIGHT_SQUARE_BRACKET, RIGHT_SQUARE_BRACKET => true
| CARROT, CARROT => true
| UNDERSCORE, UNDERSCORE => true
| BACKTICK, BACKTICK => true
| LOWERCASE_A, LOWERCASE_A => true
| LOWERCASE_B, LOWERCASE_B => true
| LOWERCASE_C, LOWERCASE_C => true
| LOWERCASE_D, LOWERCASE_D => true
| LOWERCASE_E, LOWERCASE_E => true
| LOWERCASE_F, LOWERCASE_F => true
| LOWERCASE_G, LOWERCASE_G => true
| LOWERCASE_H, LOWERCASE_H => true
| LOWERCASE_I, LOWERCASE_I => true
| LOWERCASE_J, LOWERCASE_J => true
| LOWERCASE_K, LOWERCASE_K => true
| LOWERCASE_L, LOWERCASE_L => true
| LOWERCASE_M, LOWERCASE_M => true
| LOWERCASE_N, LOWERCASE_N => true
| LOWERCASE_O, LOWERCASE_O => true
| LOWERCASE_P, LOWERCASE_P => true
| LOWERCASE_Q, LOWERCASE_Q => true
| LOWERCASE_R, LOWERCASE_R => true
| LOWERCASE_S, LOWERCASE_S => true
| LOWERCASE_T, LOWERCASE_T => true
| LOWERCASE_U, LOWERCASE_U => true
| LOWERCASE_V, LOWERCASE_V => true
| LOWERCASE_W, LOWERCASE_W => true
| LOWERCASE_X, LOWERCASE_X => true
| LOWERCASE_Y, LOWERCASE_Y => true
| LOWERCASE_Z, LOWERCASE_Z => true
| LEFT_CURLY_BRACE, LEFT_CURLY_BRACE => true
| PIPE, PIPE => true
| RIGHT_CURLY_BRACE, RIGHT_CURLY_BRACE => true
| TILDE, TILDE => true
| DEL, DEL => true
| _, _ => false
  end.


(* Conversion from normal coq strings *)
Require Import String.

(* Utility function to convert to flatter rep of ascii *)
Definition ascii_to_fast_ascii (a : Ascii.ascii) : ascii :=
  match a with
  | Ascii.Ascii false false false false false false false false => NULL
  | Ascii.Ascii true  false false false false false false false  => SOH
  | Ascii.Ascii  false  true false false false false false false => STX
  | Ascii.Ascii  true  true false false false false false false  => ETX
  | Ascii.Ascii false   false true false false false false false => EOT
  | Ascii.Ascii true   false true false false false false false  => ENQ
  | Ascii.Ascii  false   true true false false false false false => ACK
  | Ascii.Ascii  true   true true false false false false false  => BEL
  | Ascii.Ascii false  false  false true false false false false => BS
  | Ascii.Ascii true  false  false true false false false false  => TAB
  | Ascii.Ascii  false  true  false true false false false false => LF
  | Ascii.Ascii  true  true  false true false false false false  => VT
  | Ascii.Ascii false   false  true true false false false false => FF
  | Ascii.Ascii true   false  true true false false false false  => CR
  | Ascii.Ascii  false   true  true true false false false false => SO
  | Ascii.Ascii  true   true  true true false false false false  => SI
  | Ascii.Ascii false  false false  false true false false false => DLE
  | Ascii.Ascii true  false false  false true false false false  => DC1
  | Ascii.Ascii  false  true false  false true false false false => DC2
  | Ascii.Ascii  true  true false  false true false false false  => DC3
  | Ascii.Ascii false   false true  false true false false false => DC4
  | Ascii.Ascii true   false true  false true false false false  => NAK
  | Ascii.Ascii  false   true true  false true false false false => SYN
  | Ascii.Ascii  true   true true  false true false false false  => ETB
  | Ascii.Ascii false  false  false  true true false false false => CAN
  | Ascii.Ascii true  false  false  true true false false false  => EM
  | Ascii.Ascii  false  true  false  true true false false false => SUB
  | Ascii.Ascii  true  true  false  true true false false false  => ESC
  | Ascii.Ascii false   false  true  true true false false false => FS
  | Ascii.Ascii true   false  true  true true false false false  => GS
  | Ascii.Ascii  false   true  true  true true false false false => RS
  | Ascii.Ascii  true   true  true  true true false false false  => US
  | Ascii.Ascii false  false  false false false true false false => SPACE
  | Ascii.Ascii true  false  false false false true false false  => EXCLAMATION
  | Ascii.Ascii  false  true  false false false true false false => DOUBLE_QUOTE
  | Ascii.Ascii  true  true  false false false true false false  => HASH
  | Ascii.Ascii false   false  true false false true false false => DOLLAR
  | Ascii.Ascii true   false  true false false true false false  => PERCENT
  | Ascii.Ascii  false   true  true false false true false false => AMPERSAND
  | Ascii.Ascii  true   true  true false false true false false  => SINGLE_QUOTE
  | Ascii.Ascii false  false   false true false true false false => LEFT_PAREN
  | Ascii.Ascii true  false   false true false true false false  => RIGHT_PAREN
  | Ascii.Ascii  false  true   false true false true false false => ASTERISK
  | Ascii.Ascii  true  true   false true false true false false  => PLUS
  | Ascii.Ascii false   false   true true false true false false => FORWARD_SINGLE_QUOTE
  | Ascii.Ascii true   false   true true false true false false  => HYPHEN
  | Ascii.Ascii  false   true   true true false true false false => PERIOD
  | Ascii.Ascii  true   true   true true false true false false  => SLASH
  | Ascii.Ascii false  false  false  false true true false false => NUMERAL_0
  | Ascii.Ascii true  false  false  false true true false false  => NUMERAL_1
  | Ascii.Ascii  false  true  false  false true true false false => NUMERAL_2
  | Ascii.Ascii  true  true  false  false true true false false  => NUMERAL_3
  | Ascii.Ascii false   false  true  false true true false false => NUMERAL_4
  | Ascii.Ascii true   false  true  false true true false false  => NUMERAL_5
  | Ascii.Ascii  false   true  true  false true true false false => NUMERAL_6
  | Ascii.Ascii  true   true  true  false true true false false  => NUMERAL_7
  | Ascii.Ascii false  false   false  true true true false false => NUMERAL_8
  | Ascii.Ascii true  false   false  true true true false false  => NUMERAL_9
  | Ascii.Ascii  false  true   false  true true true false false => COLON
  | Ascii.Ascii  true  true   false  true true true false false  => SEMICOLON
  | Ascii.Ascii false   false   true  true true true false false => LESS_THAN
  | Ascii.Ascii true   false   true  true true true false false  => EQUAL
  | Ascii.Ascii  false   true   true  true true true false false => GREATER_THAN
  | Ascii.Ascii  true   true   true  true true true false false  => QUESTION_MARK
  | Ascii.Ascii false   false false false false false true false => AT
  | Ascii.Ascii true   false false false false false true false  => CAPITAL_A
  | Ascii.Ascii  false   true false false false false true false => CAPITAL_B
  | Ascii.Ascii  true   true false false false false true false  => CAPITAL_C
  | Ascii.Ascii false    false true false false false true false => CAPITAL_D
  | Ascii.Ascii true    false true false false false true false  => CAPITAL_E
  | Ascii.Ascii  false    true true false false false true false => CAPITAL_F
  | Ascii.Ascii  true    true true false false false true false  => CAPITAL_G
  | Ascii.Ascii false   false  false true false false true false => CAPITAL_H
  | Ascii.Ascii true   false  false true false false true false  => CAPITAL_I
  | Ascii.Ascii  false   true  false true false false true false => CAPITAL_J
  | Ascii.Ascii  true   true  false true false false true false  => CAPITAL_K
  | Ascii.Ascii false    false  true true false false true false => CAPITAL_L
  | Ascii.Ascii true    false  true true false false true false  => CAPITAL_M
  | Ascii.Ascii  false    true  true true false false true false => CAPITAL_N
  | Ascii.Ascii  true    true  true true false false true false  => CAPITAL_O
  | Ascii.Ascii false   false false  false true false true false => CAPITAL_P
  | Ascii.Ascii true   false false  false true false true false  => CAPITAL_Q
  | Ascii.Ascii  false   true false  false true false true false => CAPITAL_R
  | Ascii.Ascii  true   true false  false true false true false  => CAPITAL_S
  | Ascii.Ascii false    false true  false true false true false => CAPITAL_T
  | Ascii.Ascii true    false true  false true false true false  => CAPITAL_U
  | Ascii.Ascii  false    true true  false true false true false => CAPITAL_V
  | Ascii.Ascii  true    true true  false true false true false  => CAPITAL_W
  | Ascii.Ascii false   false  false  true true false true false => CAPITAL_X
  | Ascii.Ascii true   false  false  true true false true false  => CAPITAL_Y
  | Ascii.Ascii  false   true  false  true true false true false => CAPITAL_Z
  | Ascii.Ascii  true   true  false  true true false true false  => LEFT_SQUARE_BRACKET
  | Ascii.Ascii false    false  true  true true false true false => BACKSLASH
  | Ascii.Ascii true    false  true  true true false true false  => RIGHT_SQUARE_BRACKET
  | Ascii.Ascii  false    true  true  true true false true false => CARROT
  | Ascii.Ascii  true    true  true  true true false true false  => UNDERSCORE
  | Ascii.Ascii false   false  false false false true true false => BACKTICK
  | Ascii.Ascii true   false  false false false true true false  => LOWERCASE_A
  | Ascii.Ascii  false   true  false false false true true false => LOWERCASE_B
  | Ascii.Ascii  true   true  false false false true true false  => LOWERCASE_C
  | Ascii.Ascii false    false  true false false true true false => LOWERCASE_D
  | Ascii.Ascii true    false  true false false true true false  => LOWERCASE_E
  | Ascii.Ascii  false    true  true false false true true false => LOWERCASE_F
  | Ascii.Ascii  true    true  true false false true true false  => LOWERCASE_G
  | Ascii.Ascii false   false   false true false true true false => LOWERCASE_H
  | Ascii.Ascii true   false   false true false true true false  => LOWERCASE_I
  | Ascii.Ascii  false   true   false true false true true false => LOWERCASE_J
  | Ascii.Ascii  true   true   false true false true true false  => LOWERCASE_K
  | Ascii.Ascii false    false   true true false true true false => LOWERCASE_L
  | Ascii.Ascii true    false   true true false true true false  => LOWERCASE_M
  | Ascii.Ascii  false    true   true true false true true false => LOWERCASE_N
  | Ascii.Ascii  true    true   true true false true true false  => LOWERCASE_O
  | Ascii.Ascii false   false  false  false true true true false => LOWERCASE_P
  | Ascii.Ascii true   false  false  false true true true false  => LOWERCASE_Q
  | Ascii.Ascii  false   true  false  false true true true false => LOWERCASE_R
  | Ascii.Ascii  true   true  false  false true true true false  => LOWERCASE_S
  | Ascii.Ascii false    false  true  false true true true false => LOWERCASE_T
  | Ascii.Ascii true    false  true  false true true true false  => LOWERCASE_U
  | Ascii.Ascii  false    true  true  false true true true false => LOWERCASE_V
  | Ascii.Ascii  true    true  true  false true true true false  => LOWERCASE_W
  | Ascii.Ascii false   false   false  true true true true false => LOWERCASE_X
  | Ascii.Ascii true   false   false  true true true true false  => LOWERCASE_Y
  | Ascii.Ascii  false   true   false  true true true true false => LOWERCASE_Z
  | Ascii.Ascii  true   true   false  true true true true false  => LEFT_CURLY_BRACE
  | Ascii.Ascii false    false   true  true true true true false => PIPE
  | Ascii.Ascii true    false   true  true true true true false  => RIGHT_CURLY_BRACE
  | Ascii.Ascii  false    true   true  true true true true false => TILDE
  | Ascii.Ascii  true    true   true  true true true true false  => DEL
  | Ascii.Ascii _ _ _ _ _ _ _ true  => NULL
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

