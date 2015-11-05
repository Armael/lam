(* We have concrete identifiers. 

   Ident.Map.t is used e.g. for the environment of the interpreter.
*)
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

(* Our lambda calculus, which is standard lambda-calculus, plus:

   - atoms
   - primitives, which are basically OCaml functions along with their
     arity (in order to know when to only collect the arguments and
     where to apply the function)
   - effects primitives: perform, handle, continue and delegate
*)

type atom =
  | Unit
  | Int of int
  | String of string

and t =
  | Var of Ident.t
  | Lambda of Ident.t * t
  | App of t * t
  | Atom of atom
  | Prim of (env -> t list -> env * t) * t list
  | Perform of t
  | Handle of handler
  | Continue of t * t
  | Delegate of t * t

and handler = { body: t; hv: Ident.t * t; hf: Ident.t * Ident.t * t }

(* A runtime value: a closure of a term with its environment.

   This is defined now because primitives take runtime values as
   arguments.
*)
and value = Closure of env * t
and env = value Ident.Map.t

(* Helpers ********************************************************************)

(* Lambda and App constructors are the simplest possible. To define
   lambdas with multiple identifiers at the same time, or application
   with multiple arguments, use the [lam] and [app] helpers.
*)

let lam (idents: Ident.t list) (body: t): t =
  List.fold_right (fun id acc -> Lambda (id, acc)) idents body

let app (f: t) (args: t list): t =
  let hd, args = (List.hd args), (List.tl args) in
  List.fold_left (fun acc arg -> App (acc, arg)) (App (f, hd)) args

let rec seq : t list -> t = function
  | [] -> Atom Unit
  | [e] -> e
  | e :: es ->
    let dummy = Ident.create "_" in
    App (Lambda (dummy, seq es), e)

let letin (x: Ident.t) (e1: t) (e2: t): t =
  App (Lambda (x, e2), e1)

(* Helpers for building atomic terms. *)

let int (x: int): t = Atom (Int x)
let string (s: string): t = Atom (String s)
let unit : t = Atom Unit

(* Printers. *)

let print_atom ppf = function
  | Unit -> Format.fprintf ppf "()"
  | Int i -> Format.fprintf ppf "%d" i
  | String s -> Format.fprintf ppf "%s" s

let print_t ppf =
  let open Format in
  let rec aux paren ppf = function
    | Var x -> fprintf ppf "%s" x
    | Lambda (x, e) ->
      fprintf ppf "@[<2>%s%a%s@]"
        (if paren then "(" else "")
        (aux_lambda [x]) e
        (if paren then ")" else "")

    | App (u, v) ->
      fprintf ppf "@[<2>%s%a%s@]"
        (if paren then "(" else "")
        (aux_app [v]) u
        (if paren then ")" else "")

    | Atom a -> print_atom ppf a
    | Prim (f, args) ->
      fprintf ppf "@[<2>%s<prim>%a%s@]"
        (if paren then "(" else "")
        (fun ppf _ ->
           List.iter (fun arg -> fprintf ppf "@ %a" (aux false) arg) args)
        ()
        (if paren then ")" else "")

    | Perform e ->
      fprintf ppf "@[<2>%sperform@ %a%s@]"
        (if paren then "(" else "")
        (aux false) e
        (if paren then ")" else "")

    | Handle {body; hv = (v, hv); hf = (e, k, hf)} ->
      fprintf ppf "@[<2>%shandle@ %a@ with@ %s@ ->@ %a@ |@ effect@ %s@ %s@ ->@ %a%s@]"
        (if paren then "(" else "")
        (aux false) body v (aux false) hv e k (aux false) hf
        (if paren then ")" else "")
    | Continue (k, e) ->
      fprintf ppf "@[<2>%scontinue @ %a@ %a%s@]"
        (if paren then "(" else "")
        (aux false) k (aux false) e
        (if paren then ")" else "")
    | Delegate (e, k) ->
      fprintf ppf "@[<2>%sdelegate @ %a@ %a%s@]"
        (if paren then "(" else "")
        (aux false) e (aux false) k
        (if paren then ")" else "")

  and aux_lambda idents ppf = function
    | Lambda (i, e) -> aux_lambda (i :: idents) ppf e
    | e ->
      fprintf ppf "λ";
      List.iter (fun id -> fprintf ppf "@ %s" id) (List.rev idents);
      fprintf ppf ".@ %a" (aux false) e

  and aux_app args ppf = function
    | App (u, v) -> aux_app (v :: args) ppf u
    | e ->
      fprintf ppf "%a"
        (aux true) e;
      List.iter (fun arg -> fprintf ppf "@ %a" (aux true) arg) args
  in
  aux false ppf

(* Printing primitives. *)

let print t =
  let f env = function
    | [t] ->
      Format.printf "%a" print_t t; (env, unit)
    | _ -> raise (Invalid_argument "print") in
  Prim (f, [t])

let printl t =
  let f env = function
    | [t] ->
      Format.printf "%a\n%!" print_t t; (env, unit)
    | _ -> raise (Invalid_argument "printl") in
  Prim (f, [t])

(* CPS transform **************************************************************)

(* Variable substitution. Only used to perform administrative
   reductions. *)
let rec subst map e =
  match e with
  | Var x -> (try Ident.Map.find x map with Not_found -> e)
  | Lambda (x, e) -> Lambda (x, subst map e)
  | App (u, v) -> App (subst map u, subst map v)
  | Prim (f, args) -> Prim (f, List.map (subst map) args)
  | _ -> e

let rec cps e =
  let k = Ident.create "k" in
  let kf = Ident.create "kf" in
  let g = Ident.create "γ" in

  (* [cont e c cf g] "continues" term [e] with continuations [c],
     [cf], [g].

     It is semantically equivalent to [app e [c; cf; g]], but can
     perform some administrative reductions.
  *)
  let cont e ?metacont c cf =
    let is_value = function
      | Var _ | Atom _ | Prim _ -> true
      | _ -> false in

    match e with
    | Lambda (k, Lambda (kf, Lambda (g, App (App (Var k', e'), Var g'))))
      when k = k' && g = g' && is_value e' ->
      begin match c with
        | Var k ->
          begin match metacont with
            | Some mc ->
              app (Var k) [e'; mc]
            | None ->
              app (Var k) [e']
          end
        | Lambda (kx, Lambda (kg, kbody)) ->
          begin match metacont with
            | Some (Var _ as mc) ->
              subst Ident.Map.(add kx e' @@ add kg mc @@ empty) kbody
            | Some mc ->
              (* Do not substitute [mc] if it's not a variable. *)
              app c [e; mc]
            | None ->
              app c [e]
          end
        | _ -> raise (Invalid_argument "cont")
      end

    | _ ->
      begin match metacont with
        | Some mc ->
          app e [c; cf; mc]
        | None ->
          app e [c; cf]
      end
  in

  match e with
  | Var _ | Atom _ ->
    lam [k; kf] (App (Var k, e))

  | Prim (f, args) ->
    let args_idents = List.map (fun _ -> Ident.create "v") args in
    lam [k; kf] (
      List.fold_right (fun (arg, id) e ->
          cont (cps arg) (Lambda (id, e)) (Var kf)
        ) (List.combine args args_idents)
        (App (Var k, Prim (f, List.map (fun v -> Var v) args_idents)))
    )

  | Lambda (x, e) ->
    lam [k; kf] (App (Var k, Lambda (x, cps e)))

  | App (u, v) ->
    let val_u = Ident.create "v" in
    let val_v = Ident.create "v" in
    lam [k; kf] (
      (cont (cps u)
         (lam [val_u]
            (cont (cps v)
               (lam [val_v]
                  (cont (App (Var val_u, Var val_v))
                     (Var k) (Var kf)))
               (Var kf)))
         (Var kf))
    )

  | Perform e ->
    let val_e = Ident.create "e" in
    let f = Ident.create "f" in
    let v = Ident.create "v" in
    let k' = Ident.create "k'" in
    let g' = Ident.create "γ'" in
    let kf' = Ident.create "kf'" in
    let x = Ident.create "x" in
    lam [k; kf; g] (
      cont (cps e)
        (lam [val_e; g]
           (app (Var kf) [
               Var val_e;
               (lam [f; v; k'; kf'; g']
                  (cont (cps (App (Var f, Var v)))
                     (Var k) (Var kf)
                     ~metacont:(lam [x] (app (Var k') [Var x; Var g']))));
               Var g
             ]))
        (Var kf) ~metacont:(Var g)
    )

  | Handle {body; hv = (v, hv); hf = (ve, vk, hf)} ->
    let x = Ident.create "x" in
    let g' = Ident.create "γ'" in
    lam [k; kf; g]
      (cont (cps body)
         (lam [v; g'] (cont (cps hv)
                         (lam [x; g'] (App (Var g', Var x)))
                         (Var kf) ~metacont:(Var g')))
         (lam [ve; vk; g'] (cont (cps hf) (lam [x; g'] (App (Var g', Var x)))
                              (Var kf) ~metacont:(Var g')))
         ~metacont:(lam [x] (app (Var k) [Var x; Var g])))

  | Continue (stack, e) ->
    let val_e = Ident.create "ve" in
    let x = Ident.create "x" in
    let f = Ident.create "f" in
    lam [k; kf; g] (
      cont (cps e)
        (lam [val_e; g]
           (cont (cps (Lambda (x, Var x)))
              (lam [f; g]
                 (app stack [Var f; Var val_e;
                             Var k; Var kf; Var g]))
              (Var kf) ~metacont:(Var g)))
        (Var kf) ~metacont:(Var g)
    )

  | Delegate (e, stack) ->
    let val_e = Ident.create "ve" in
    lam [k; kf; g] (
      cont (cps e)
        (lam [val_e; g]
           (app (Var kf) [
               Var val_e;
               stack;
               Var g
             ]))
        (Var kf) ~metacont:(Var g)
    )

let unhandled_effect e k =
  let f env = function
    | [e; k] ->
      Format.printf "Unhandled effect: %a\n%!" print_t e;
      Format.printf "cont: %a\n%!" print_t k;
      Format.printf "bound in cont env:";
      Ident.Map.iter (fun v _ -> Format.printf " %s" v) env;
      Format.printf "\n%!";
      env, unit
    | _ -> raise (Invalid_argument "unhandled_effect") in
  Prim (f, [e; k])

(* CPS transformation for a toplevel term: CPS transforms it, and
   applies it to "identity" continuations. *)
let cps_main e =
  let x = Ident.create "x" in
  let kv = Ident.create "kv" in
  let g = Ident.create "γ" in
  app (cps e) [lam [x; g] (app (Var g) [Var x]);
               lam [x; kv; g] (unhandled_effect (Var x) (Var kv));
               lam [x] (Var x)]

(* Interpreter ****************************************************************)

let rec eval env = function
  | Var v ->
    (try Ident.Map.find v env with Not_found ->
      Printf.printf "DEBUG: %s\n%!" v;
      failwith "Unbound identifier")
  | Lambda (_, _)
  | Atom _ as e ->
    Closure (env, e)
  | Prim (f, args) ->
    let env, args_values_r = List.fold_left (fun (env, args_values_r) arg ->
        let Closure (env, arg_val) = eval env arg in
        (env, arg_val :: args_values_r)
      ) (env, []) args in
    let env, ret = f env (List.rev args_values_r) in
    eval env ret
  | App (u, v) ->
    apply (eval env u) (eval env v)
  | _ -> failwith "not handled by the interpreter"

and apply (Closure (envu, u)) (Closure (envv, v) as cv) =
  match u with
  | Lambda (x, e) -> eval (Ident.Map.add x cv envu) e
  | _ ->
    Format.eprintf "DEBUG: %a\n" print_t u;
    failwith "trying to apply a value that is not a function"

(* Examples *******************************************************************)

(* Prints a term, evaluates it, and prints the result. *)
let ev t =
  (* Format.printf "%a\n" print_t t; *)
  let Closure (_, res) = eval Ident.Map.empty t in
  Format.printf "\n>> %a\n%!" print_t res

let rec check_scope env = function
  | Var v -> (try Ident.Map.find v env; [] with Not_found -> [Var v])
  | Lambda (x, e) -> check_scope (Ident.Map.add x () env) e
  | App (e1, e2) ->
    (check_scope env e1) @ (check_scope env e2)
  | Atom _ -> []
  | Prim (_,_) -> []
  | _ -> failwith "not handled"

let ex0 =
  let x = Ident.create "x" in
  app (lam [x] (Var x)) [int 3]

let ex1 =
  let x = Ident.create "x" in
  printl (app (lam [x] (Var x)) [Atom (Int 3)])

let ex1_1 =
  seq [printl (string "a"); printl (string "b")]

let ex1_2 =
  let x = Ident.create "x" in
  app (lam [x] (Var x)) [app (lam [x] (Var x)) [int 3]]

let ex2 =
  seq [printl (int 3);
       printl (string "abc");
       printl (string "def")]

let ex3 =
  let e = Ident.create "my_e" in
  let k = Ident.create "my_k" in
  let v = Ident.create "my_v" in
  Handle {
    body = seq [printl (string "abc");
                printl (Perform (int 0));
                printl (string "def")];
    hv = v, Var v;
    hf = e, k, Continue (Var k, int 18)
  }

let ex3_1 =
  let e = Ident.create "my_e" in
  let k = Ident.create "my_k" in
  let v = Ident.create "my_v" in
  Handle {
    body = Perform (int 0);
    hv = v, Var v;
    hf = e, k, Continue (Var k, int 18)
  }


let ex4 =
  let e = Ident.create "my_e" in
  let k = Ident.create "my_k" in
  let v = Ident.create "my_v" in
  Handle {
    body =
      Handle {
        body = seq [printl (string "abc");
                    printl (Perform (int 0));
                    printl (string "def")];
        hv = v, Var v;
        hf = e, k, Delegate (Var e, Var k)
      };
    hv = v, Var v;
    hf = e, k, Continue (Var k, int 18)
  }

let ex5 =
  let e = Ident.create "my_e" in
  let k = Ident.create "my_k" in
  let v = Ident.create "my_v" in
  Handle {
    body = seq [printl (string "abc");
                printl (Perform (int 0));
                printl (string "def")];
    hv = v, Var v;
    hf = e, k, seq [Continue (Var k, int 18);
                    printl (string "handler end")]
  }

let ex6 =
  let e = Ident.create "my_e" in
  let k = Ident.create "my_k" in
  let v = Ident.create "my_v" in
  seq [
    Handle {
      body = unit;
      hv = v, Var v;
      hf = e, k, unit;
    };
    printl (string "abc")
  ]

let ex7 =
  let e = Ident.create "my_e" in
  let k = Ident.create "my_k" in
  let v = Ident.create "my_v" in
  Handle {
    body = seq [Perform unit; Perform unit];
    hv = v, seq [printl (string "hv"); Var v];
    hf = e, k, seq [
        printl (string "hf1");
        Continue (Var k, unit);
        printl (string "hf2")
      ]
  }
