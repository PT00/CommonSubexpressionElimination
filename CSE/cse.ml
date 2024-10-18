(* abstract syntax tree *)

type bop = Mult | Div | Add | Sub | Eq | Lt | Gt | Leq | Geq | Neq

type ident = string

type expr =
  | Int of int
  | Bool of bool
  | Binop of bop * expr * expr
  | If of expr * expr * expr
  | Var of ident
  | Let of ident * expr * expr

(* CSE *)

let cse (expr : expr) : expr option = 


  let fresh_var =
    let counter = ref 0 in
    fun () ->
      let var = "v" ^ string_of_int !counter in
      incr counter;
      var in

  (* Funkcja sprawdzająca alfa-rownowaznosc *)
  let alpha_equiv (e1 : expr) (e2 : expr) : bool =
    let rec check env1 env2 e1 e2 =
      match e1, e2 with
      | Binop (op1, a1, b1), Binop (op2, a2, b2) -> 
          op1 = op2 && check env1 env2 a1 a2 && check env1 env2 b1 b2
      | If (a1, b1, c1), If (a2, b2, c2) -> 
          check env1 env2 a1 a2 && check env1 env2 b1 b2 && check env1 env2 c1 c2
      | Let (i1, a1, b1), Let (i2, a2, b2) ->
          check env1 env2 a1 a2 && check ((i1, i2) :: env1) ((i2, i1) :: env2) b1 b2
      | Var a, Var b -> 
          (try List.assoc a env1 = b with Not_found -> a = b)
      | Int n1, Int n2 -> n1 = n2
      | Bool b1, Bool b2 -> b1 = b2
      | _, _ -> false
    in check [] [] e1 e2 in


  let rec free_vars (env : ident list) (expr : expr) : ident list = 
    match expr with
    | Int _ | Bool _ -> []
    | Var x -> if List.mem x env then [] else [x]
    | Binop (_, e1, e2) -> (free_vars env e1) @ (free_vars env e2)
    | If (e1, e2, e3) -> (free_vars env e1) @ ((free_vars env e2) @ (free_vars env e3))
    | Let (x, e1, e2) ->  (free_vars env e1) @ (free_vars (x :: env) e2) in


  let collect_free_subexpressions (expr : expr) : expr list =
    let rec aux env acc expr =
      match expr with
      | Int _ | Bool _ | Var _ -> acc
      | Binop (_, e1, e2) ->
          let acc' = aux env acc e1 in 
          let acc'' = aux env acc' e2 in
          if List.for_all (fun v -> not(List.mem v env)) (free_vars [] expr) then expr :: acc'' else acc''
      | If (e1, e2, e3) ->
          let acc' = aux env acc e1 in
          let acc'' = aux env acc' e2 in
          let acc''' = aux env acc'' e3 in
          if List.for_all (fun v -> not(List.mem v env)) (free_vars [] expr) then expr :: acc''' else acc'''
      | Let (x, e1, e2) ->
          let acc' = aux env acc e1 in
          let env' = x :: env in
          let acc'' = aux env' acc' e2 in
          if List.for_all (fun v -> not(List.mem v env)) (free_vars [] expr) then expr :: acc'' else acc''
    in
    aux [] [] expr in


  let rec replace (expr : expr) (old_expr : expr) (new_var : ident) : expr =
    if alpha_equiv expr old_expr 
      then Var new_var
    else
      match expr with
      | Binop (op, e1, e2) -> Binop (op, replace e1 old_expr new_var, replace e2 old_expr new_var)
      | If (e1, e2, e3) -> If (replace e1 old_expr new_var, replace e2 old_expr new_var, replace e3 old_expr new_var)
      | Let (x, e1, e2) ->
          Let (x, replace e1 old_expr new_var,

              if List.memq x (free_vars [] old_expr) then e2 else replace e2 old_expr new_var)
      | _ -> expr in

  let find_alpha_equiv (subexprs : expr list) (env : ident list) : expr option =
    let rec find = function
      | [] -> None
      | e1 :: rest ->
          match List.find_opt (fun e2 -> alpha_equiv e1 e2 && free_vars env e1 = free_vars env e2) rest with
          | Some e2 -> Some e1
          | None -> find rest
    in
    find subexprs in

  let rec cse_rec (env : ident list) (expr : expr) : expr option =
    let subexprs = collect_free_subexpressions expr in
    match find_alpha_equiv subexprs env with
    | Some subexpr ->
        let v = fresh_var () in
        let replaced_expr = replace expr subexpr v in
        Some (Let (v, subexpr, replaced_expr))
    | None ->
        match expr with
        | Binop (op, e1, e2) ->
            (match cse_rec env e1 with
            | Some e1' -> Some (Binop (op, e1', e2))
            | None -> (match cse_rec env e2 with
                      | Some e2' -> Some (Binop (op, e1, e2'))
                      | None -> None))
        | If (e1, e2, e3) ->
            (match cse_rec env e1 with
            | Some e1' -> Some (If (e1', e2, e3))
            | None -> (match cse_rec env e2 with
                      | Some e2' -> Some (If (e1, e2', e3))
                      | None -> (match cse_rec env e3 with
                                  | Some e3' -> Some (If (e1, e2, e3'))
                                  | None -> None)))
        | Let (x, e1, e2) ->
            (match cse_rec env e1 with
            | Some e1' -> Some (Let (x, e1', e2))
            | None -> (match cse_rec (x :: env) e2 with
                      | Some e2' -> Some (Let (x, e1, e2'))
                      | None -> None))
        | _ -> None
  in
  cse_rec [] expr;;
