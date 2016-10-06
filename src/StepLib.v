

Inductive sstar {state : Type} (sstep : state -> state -> Prop) : state -> state -> Prop :=
| SStarNil : forall e, sstar sstep e e
| SStarCons : forall e e' e'',
        sstep e e' ->
        sstar sstep e' e'' ->
        sstar sstep e e''.

Inductive splus {state : Type} (sstep : state -> state -> Prop) : state -> state -> Prop :=
| SPlusOne : forall s s',
        sstep s s' ->
        splus sstep s s'
| SPlusCons : forall s s' s'',
        sstep s s' ->
        splus sstep s' s'' ->
        splus sstep s s''.




(* Inductive sstar {A : Type} (step : A -> A -> Prop) : A -> A -> Prop := *)
(* | star_refl : *)
(*     forall st, *)
(*       simple_star step st st *)
(* | star_left : *)
(*     forall st1 st2 st3, *)
(*       step st1 st2 -> *)
(*       simple_star step st2 st3 -> *)
(*       simple_star step st1 st3. *)

(* Inductive splus {A : Type} (step : A -> A -> Prop) : A -> A -> Prop := *)
(* | plus_one : *)
(*     forall st st', *)
(*       step st st' -> *)
(*       simple_plus step st st' *)
(* | plus_left : *)
(*     forall st1 st2 st3, *)
(*       step st1 st2 -> *)
(*       simple_plus step st2 st3 -> *)
(*       simple_plus step st1 st3. *)

