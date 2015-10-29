module Ident = struct
  type t = string

  let id = ref 0
  let create base =
    incr id;
    base ^ "/" ^ (string_of_int !id)

  let compare = compare
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
| Prim of int * (atom list -> t)

(* Useful operators *)

let lam idents body =
  List.fold_left (fun acc id -> Lambda (id, acc)) body idents

let app f args =
  let hd, args = (List.hd args), (List.tl args) in
  List.fold_left (fun acc arg -> App (acc, arg)) (App (f, hd)) args

let print_atom cout = function
  | Unit -> output_string cout "()"
  | Int i -> Printf.fprintf cout "%d" i
  | String s -> output_string cout s

let print =
  Prim
    (1, function [atom] -> Printf.printf "%a" print_atom atom; Atom Unit
               | _ -> raise (Invalid_argument "print"))

let printl =
  Prim
    (1, function [atom] -> Printf.printf "%a\n%!" print_atom atom; Atom Unit
               | _ -> raise (Invalid_argument "printl"))

(* Interpreter *)

exception Segfault

module Env = Map.Make (Ident)
type closure = Closure of closure Env.t * t

let assert_atom = function
  | Atom a -> a
  | _ -> raise Segfault

let rec eval env = function
  | Var v ->
    (try Env.find v env with
       Not_found -> raise Segfault)
  | Lambda (_, _)
  | Atom _ as e ->
    Closure (env, e)
  | Prim (0, p) -> Closure (env, p [])
  | Prim (n, _) as e ->
    if n < 0 then failwith "Invalid primitive arity";
    Closure (env, e)
  | App (u, v) ->
    apply (eval env u) (eval env v)

and apply (Closure (envu, u)) (Closure (envv, v) as cv) =
  match u with
  | Lambda (x, e) -> eval (Env.add x cv envu) e
  | Prim (n, p) when n > 0 ->
    let a = assert_atom v in
    Closure (envu, Prim (n - 1, fun l -> p (a :: l)))
  | _ -> raise Segfault
