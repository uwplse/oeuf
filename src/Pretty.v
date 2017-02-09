Require Import Program.
Require Import SourceLifted Utopia List Monads HList CompilationUnit ListLemmas.
Require Import StuartTact.
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
    end.

  Fixpoint from_tree (t : tree symbol.t) : option type_name :=
    match t with
    | atom s =>
      if symbol.eq_dec s (symbol.of_string_unsafe "nat") then Some Tnat
      else if symbol.eq_dec s (symbol.of_string_unsafe "bool") then Some Tbool
      else if symbol.eq_dec s (symbol.of_string_unsafe "unit") then Some Tunit
      else if symbol.eq_dec s (symbol.of_string_unsafe "positive") then Some Tpositive
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
      end.

  Lemma check_elim_correct :
    forall case_tys target_tyn ty (e : elim case_tys (ADT target_tyn) ty),
      check_elim = Some e.
  Proof.
    unfold check_elim.
    intros.
    refine match e with
             | EBool t    => _
             | ENat t     => _
             | EList _ t => _
             | EUnit t    => _
             | EPair _ _ t => _
             | EOption _ t => _
             | EPositive t => _
           end;
      repeat (break_match; try congruence;
      dependent destruction e0; auto).
  Qed.
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
