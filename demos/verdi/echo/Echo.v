Require SourceLang.
Require List.
Import List.ListNotations.

Open Scope list.

Definition node_name := bool.
Definition state := unit.
Definition msg := bool.
Definition input := unit.

Definition other (h : node_name) : node_name := negb h.

Definition ping : msg := true.
Definition pong : msg := false.

Definition initial_state : state := tt.

Definition handleInput (h : node_name) (i : input) (s : state)
  : state * list (node_name * msg) :=
  (s, [(other h, ping)]).

Definition handleMsg (dst : node_name) (m : msg) (s : state)
  : state * list (node_name * msg) :=
  if m
  then (* got ping; send pong *) (s, [(other dst, pong)])
  else (* got pong; yay! *) (s, [])
.

Definition initial_state_reflect_ty :=
  ltac:(let x := eval compute in unit in SourceLang.type_reflect x) : SourceLang.type.

Definition initial_state_reflect : SourceLang.expr [] initial_state_reflect_ty :=
  ltac:(let x := eval compute in initial_state in SourceLang.reflect x).


Definition handleInput_reflect_ty :=
  ltac:(let x := eval compute in (node_name -> input -> state -> state * list (node_name * msg)) in SourceLang.type_reflect x) : SourceLang.type.

Definition handleInput_reflect : SourceLang.expr [] handleInput_reflect_ty :=
  ltac:(let x := eval compute in handleInput in SourceLang.reflect x) : SourceLang.expr [] _ .

Definition handleMsg_reflect_ty :=
  ltac:(let x := eval compute in (node_name -> msg -> state -> state * list (node_name * msg)) in SourceLang.type_reflect x) : SourceLang.type.

Definition handleMsg_reflect : SourceLang.expr [] handleMsg_reflect_ty :=
  ltac:(let x := eval compute in handleMsg in SourceLang.reflect x).

