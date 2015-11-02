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
| Perform of t
| Handle of t * t
| Continue of t * t

and value = Closure of value Ident.Map.t * t

(* Helpers ********)

let lam idents body =
  List.fold_right (fun id acc -> Lambda (id, acc)) idents body

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

let print_atom ppf = function
  | Unit -> Format.fprintf ppf "()"
  | Int i -> Format.fprintf ppf "%d" i
  | String s -> Format.fprintf ppf "%s" s

let print =
  Prim
    (1, function
       | [Closure (_, Atom a)] ->
         Format.printf "%a" print_atom a; Atom Unit
       | _ -> raise (Invalid_argument "print"))

let printl =
  Prim
    (1, function
       | [Closure (_, Atom a)] ->
         Format.printf "%a\n%!" print_atom a; Atom Unit
       | _ -> raise (Invalid_argument "printl"))

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
    | Prim (n, _) -> Format.fprintf ppf "<prim %d>" n
    | Perform e ->
      fprintf ppf "@[<2>%sperform@ %a%s@]"
        (if paren then "(" else "")
        (aux false) e
        (if paren then ")" else "")

    | Handle (e, h) ->
      fprintf ppf "@[<2>%shandle@ %a@ with@ %a%s@]"
        (if paren then "(" else "")
        (aux false) e (aux false) h
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

(******************)

let rec subst map e =
  match e with
  | Var x -> (try Ident.Map.find x map with Not_found -> e)
  | Lambda (x, e) -> Lambda (x, subst map e)
  | App (u, v) -> App (subst map u, subst map v)
  | _ -> e

let rec cps e =
  let k = Ident.create "k" in
  let kf = Ident.create "kf" in
  let gf = Ident.create "γf" in
  let cont e c cf gf =
    let is_value = function
      | Var _ | Atom _ | Prim _ -> true
      | _ -> false in

    match e with
    | Lambda (k, Lambda (kf, Lambda (gf, App (Var k', e')))) when k = k' && is_value e' ->
      begin match c with
        | Var k ->
          App (Var k, e')
        | Lambda (kx, kbody) ->
          subst Ident.Map.(add kx e' empty) kbody
        | _ -> raise (Invalid_argument "cont")
      end

    | _ ->
      app e [c; cf; gf]
  in

  match e with
  | Var _ | Atom _ ->
    lam [k; kf; gf] (App (Var k, e))
  | Prim (n, p) ->
    let p' =
      Prim (n + 3, fun l ->
        match List.rev l with
        | _ :: _ :: (Closure (_, k)) :: args ->
          App (k, p (List.rev args))
        | _ -> assert false)
    in
    lam [k; kf; gf] (App (Var k, p'))

  | Lambda (x, e) ->
    lam [k; kf; gf] (App (Var k, Lambda (x, cps e)))
  | App (u, v) ->
    let val_u = Ident.create "v" in
    let val_v = Ident.create "v" in
    lam [k; kf; gf] (
      (cont (cps u)
         (lam [val_u]
            (cont (cps v)
               (lam [val_v]
                  (cont (App (Var val_u, Var val_v))
                     (Var k) (Var kf) (Var gf)))
               (Var kf) (Var gf)))
         (Var kf) (Var gf))
    )

  | Perform e ->
    let val_e = Ident.create "e" in
    let f = Ident.create "f" in
    let v = Ident.create "v" in
    let k' = Ident.create "k'" in
    let kf' = Ident.create "kf'" in
    let gf' = Ident.create "γf'" in
    lam [k; kf; gf] (
      cont (cps e)
        (lam [val_e]
           (app (Var kf) [
             Var val_e;
             (lam [f; v; k'; kf'; gf']
                (cont (cps (App (Var f, Var v))) (Var k) (Var kf) (Var gf)));
             Var gf
           ]))
        (Var kf) (Var gf)
    )

  | Handle (body, hf) ->
    (* let dummy = Ident.create "_" in *)
    (* let vbody = Ident.create "body" in *)
    let hf_var = Ident.create "hf" in
    (* let f = Ident.create "f" in *)
    (* let v = Ident.create "v" in *)
    (* let k' = Ident.create "k'" in *)
    (* let kf' = Ident.create "kf'" in *)
    (* let gf' = Ident.create "γf'" in *)
    let x = Ident.create "x" in
    let g' = Ident.create "γ'" in
    let kk = Ident.create "kk" in
    (* let stack = *)
    (*   lam [f; v; k'; kf'; gf'] ( *)
    (*     cont (cps (App (Var f, Var v))) *)
    (*       (lam [x] (Var x)) *)
    (*       (lam [x; kk; g'] (app (Var g') [Var x; Var kk])) *)
    (*       (lam [x; kk] (cont (cps hf) *)
    (*                       (lam [hf_var] (app (Var hf_var) [Var x; Var kk; Var k'; Var kf'; Var gf'])) *)
    (*                       (Var kf') (Var gf'))) *)
    (*   ) in *)

    (* lam [k; kf; gf] ( *)
    (*   cont (cps (Lambda (dummy, body))) (lam [vbody] ( *)
    (*     app stack [Var vbody; Var k; Var kf; Var gf; *)
    (*                unit; Var k; Var kf; Var gf] *)
    (*   )) (Var kf) (Var gf) *)
    (* ) *)

    (* Inlined version of what is commented before: *)
    lam [k; kf; gf]
      (cont (cps body)
         (lam [x] (Var x))
         (lam [x; kk; g'] (app (Var g') [Var x; Var kk]))
         (lam [x; kk] (cont (cps hf)
                         (lam [hf_var] (app (Var hf_var)
                                          [Var x; Var k; Var kf; Var gf;
                                           Var kk; Var k; Var kf; Var gf]))
                         (Var kf) (Var gf))))

  | Continue (stack, e) ->
    let val_e = Ident.create "ve" in
    let x = Ident.create "x" in
    let f = Ident.create "f" in
    lam [k; kf; gf] (
      cont (cps e)
        (lam [val_e]
           (cont (cps (Lambda (x, Var x)))
              (lam [f]
                 (app stack [Var f; Var val_e; Var k; Var kf; Var gf]))
              (Var kf) (Var gf)))
        (Var kf) (Var gf)
    )

let unhandled_effect =
  Prim
    (1, function
       | [Closure (_, e)] ->
         Format.printf "Unhandled effect: %a\n%!" print_t e; Atom Unit
       | _ -> raise (Invalid_argument "unhandled_effect"))

let cps_main e =
  let x = Ident.create "x" in
  let kv = Ident.create "kv" in
  let g = Ident.create "γ" in
  app (cps e) [lam [x] (Var x);
               lam [x; kv; g] (app (Var g) [Var x; Var kv]);
               lam [x; kv] (App (unhandled_effect, Var x))]

(* Interpreter *)

let rec eval env = function
  | Var v ->
    (try Ident.Map.find v env with
       Not_found -> failwith "Unbound identifier")
  | Lambda (_, _)
  | Atom _ as e ->
    Closure (env, e)
  | Prim (0, p) -> eval env (p [])
  | Prim (n, _) as e ->
    if n < 0 then failwith "Invalid primitive arity";
    Closure (env, e)
  | App (u, v) ->
    apply (eval env u) (eval env v)
  | _ -> failwith "not handled"

and apply (Closure (envu, u)) (Closure (envv, v) as cv) =
  match u with
  | Lambda (x, e) -> eval (Ident.Map.add x cv envu) e
  | Prim (n, p) when n > 0 ->
    if n = 1 then
      eval envu (p [cv])
    else
      Closure (envu, Prim (n - 1, fun l -> p (cv :: l)))
  | _ ->
    Format.eprintf "DEBUG: %a\n" print_t u;
    failwith "trying to apply a value that is not a function"

(** *)

let ev t =
  Format.printf "%a\n" print_t t;
  let Closure (_, res) = eval Ident.Map.empty t in
  Format.printf "\n>> %a\n%!" print_t res

let ex0 =
  let x = Ident.create "x" in
  app (lam [x] (Var x)) [int 3]

let ex1 =
  let x = Ident.create "x" in
  (app printl [app (lam [x] (Var x)) [Atom (Int 3)]])

let ex1_1 =
  seq [App (printl, string "a"); App (printl, string "b")]

let ex1_2 =
  let x = Ident.create "x" in
  app (lam [x] (Var x)) [app (lam [x] (Var x)) [int 3]]

let ex2 =
  (seq [App (printl, int 3); App (printl, string "abc"); App (printl, string "def")])

let ex3 =
  let e = Ident.create "my_e" in
  let k = Ident.create "my_k" in
  Handle (seq [App (printl, string "abc");
               App (printl, Perform (int 0));
               App (printl, string "def")],
          Lambda (e, Lambda (k, Continue (Var k, int 18))))
