module Ident = struct
  type t = string

  let id = ref 0
  let create base =
    incr id;
    base ^ "/" ^ (string_of_int !id)

  module Map = Map.Make (struct
      type nonrec t = t
      let compare = compare
    end)
end

type atom =
| Unit
| Int of int
| String of string

and t =
| Var of Ident.t
| Lambda of Ident.t * t
| App of t * t
| Atom of atom
| Prim of int * (value list -> t)

and value = Closure of value Ident.Map.t * t

let rec subst map e =
  match e with
  | Var x -> (try Ident.Map.find x map with Not_found -> e)
  | Lambda (x, e) -> Lambda (x, subst map e)
  | App (u, v) -> App (subst map u, subst map v)
  | _ -> e

let rec cps e =
  let k = Ident.create "k" in
  let cont e c =
    let is_value = function
      | Var _ | Atom _ | Prim _ -> true
      | _ -> false in

    match e with
    | Lambda (k, App (Var k', e')) when k = k' && is_value e' ->
      begin match c with
        | Var k ->
          App (Var k, e')
        | Lambda (kx, kbody) ->
          subst Ident.Map.(add kx e' empty) kbody
        | _ -> raise (Invalid_argument "cont")
      end

    | _ ->
      App (e, c)
  in

  match e with
  | Var _ | Atom _ ->
    Lambda (k, App (Var k, e))
  | Prim (n, p) ->
    let p' =
      Prim (n + 1, fun l ->
        let l = List.rev l in
        let Closure (_, k) = List.hd l in
        let args = List.rev @@ List.tl l in
        App (k, p args)) in
    Lambda (k, App (Var k, p'))

  | Lambda (x, e) ->
    Lambda (k, App (Var k, Lambda (x, cps e)))
  | App (u, v) ->
    let val_u = Ident.create "v" in
    let val_v = Ident.create "v" in
    Lambda (k,
      cont (cps u) (Lambda (val_u,
        cont (cps v) (Lambda (val_v,
          cont (App (Var val_u, Var val_v)) (Var k))))))

let cps_main e =
  let x = Ident.create "x" in
  App (cps e, Lambda (x, Var x))

(* Useful operators *)

let lam idents body =
  List.fold_left (fun acc id -> Lambda (id, acc)) body idents

let app f args =
  let hd, args = (List.hd args), (List.tl args) in
  List.fold_left (fun acc arg -> App (acc, arg)) (App (f, hd)) args

let rec seq = function
  | [] -> Atom Unit
  | [e] -> e
  | e :: es ->
    let dummy = Ident.create "_" in
    App (Lambda (dummy, seq es), e)

let int x = Atom (Int x)
let string s = Atom (String s)
let unit = Atom Unit

let print_atom cout = function
  | Unit -> output_string cout "()"
  | Int i -> Printf.fprintf cout "%d" i
  | String s -> output_string cout s

let print =
  Prim
    (1, function
       | [Closure (_, Atom a)] ->
         Printf.printf "%a" print_atom a; Atom Unit
       | _ -> raise (Invalid_argument "print"))

let printl =
  Prim
    (1, function
       | [Closure (_, Atom a)] ->
         Printf.printf "%a\n%!" print_atom a; Atom Unit
       | _ -> raise (Invalid_argument "printl"))

let print_t cout =
  let rec aux paren = function
    | Var x -> output_string cout x
    | Lambda (x, e) ->
      if paren then output_string cout "(";
      aux_lambda [x] e;
      if paren then output_string cout ")"
    | App (u, v) ->
      if paren then output_string cout "(";
      aux_app [v] u;
      if paren then output_string cout ")"
    | Atom a -> print_atom cout a
    | Prim (n, _) -> Printf.fprintf cout "<prim %d>" n

  and aux_lambda idents = function
    | Lambda (i, e) -> aux_lambda (i :: idents) e
    | e ->
      output_string cout "λ";
      List.iter (fun id -> Printf.fprintf cout " %s" id) (List.rev idents);
      output_string cout ". ";
      aux false e

  and aux_app args = function
    | App (u, v) -> aux_app (v :: args) u
    | e ->
      aux true e;
      List.iter (fun arg -> output_string cout " "; aux true arg) args
  in
  aux false

(* Interpreter *)

exception Segfault

let rec eval env = function
  | Var v ->
    (try Ident.Map.find v env with
       Not_found -> raise Segfault)
  | Lambda (_, _)
  | Atom _ as e ->
    Closure (env, e)
  | Prim (0, p) -> eval env (p [])
  | Prim (n, _) as e ->
    if n < 0 then failwith "Invalid primitive arity";
    Closure (env, e)
  | App (u, v) ->
    apply (eval env u) (eval env v)

and apply (Closure (envu, u)) (Closure (envv, v) as cv) =
  match u with
  | Lambda (x, e) -> eval (Ident.Map.add x cv envu) e
  | Prim (n, p) when n > 0 ->
    if n = 1 then
      eval envu (p [cv])
    else
      Closure (envu, Prim (n - 1, fun l -> p (cv :: l)))
  | _ -> raise Segfault

(** *)

let ev t =
  Printf.printf "%a\n>> " print_t t;
  eval Ident.Map.empty t |> ignore;
  Printf.printf "\n%!"

let _ =
  let x = Ident.create "x" in
  ev (app printl [app (lam [x] (Var x)) [Atom (Int 3)]])

let _ =
  let x = Ident.create "x" in
  ev (cps_main (app printl [app (lam [x] (Var x)) [Atom (Int 3)]]))

let _ =
  ev
    (cps_main (seq [App (printl, int 3); App (printl, string "slt"); App (printl, string "toto")]))
