(********************************************************************)
(* SessML - Implementation                                          *)
(*                                                                  *)
(* mlsyntax.ml                                                      *)
(********************************************************************)
(* $ Time-stamp: <28-07-2010 14:37 by Pierre-Malo Denielou> $ *)

let limit = 70

(* type res = string list *)

let text s = [s]
let slen = String.length
let space (i:int) = String.make i ' '
let prefix s = List.map (fun x -> s^x)

let hcat x y = 
    let z = List.rev x in
    let h,t = List.hd z, (List.rev (List.tl z)) in
    let i = slen h + 1 in
    t@[h^(space 1)^(List.hd y)]@(prefix (space i) (List.tl y))

let vcat x y = x@y

let rec hlcat = function
    [] -> []
  | [l] -> l
  | s::q -> hcat s (hlcat q)

let rec vlcat = function
    [] -> []
  | [l] -> l
  | s::q -> vcat s (vlcat q)

let rec hsep s = function
    [] -> []
  | [l] -> l
  | a::q -> hcat a (hcat s (hsep s q))
let rec vsepe s = function
    [] -> []
  | [l] -> l
  | a::q -> vcat (hcat a s) (vsepe s q)
let rec vsepb s = function
    [] -> []
  | [l] -> l
  | a::q -> vcat a (hcat s (vsepb s q))

let htuple = function l -> hlcat ([text "(" ; hsep (text ",") l ; text ")"])
let vtuple = function l -> hlcat ([text "(" ; vsepe (text ",") l ; text ")"])
let hrec = function l -> hlcat ([text "{" ; hsep (text ";") l ; text "}"])
let vrec = function l -> hlcat ([text "{" ; vsepe (text ";") l ; text "}"])

let paren () = ()

(* File to ease the generation and pretty-printing of ml programs *)

type id = string

type type_expr =
    | ArrowT of (type_expr * type_expr)
    | ProductT of (type_expr list)
    | RecordT of (id * type_expr) list
    | VarT of id

type type_decl = 
    | Sum_type of (id *((id * type_expr) list))
    | Alias of (id * type_expr)

type mlexpr = 
    | VarE of id
    | AppE of (mlexpr * mlexpr)
    | LambdaE of (id * type_expr * mlexpr)
 (*   | PatternE of (id * id * mlexpr) list   Pattern matching for constructors *)
    | MatchE of (id * ((id * id * mlexpr) list))
    | LetE of (id * type_expr * mlexpr * mlexpr)

type expr_decl = id * type_expr * mlexpr
    

let rec prettyT (i:int) = function
  | ArrowT (a,b) -> Printf.sprintf "(%s -> %s)" (prettyT i a) (prettyT i b)
  | VarT s -> s
  | ProductT lp -> Printf.sprintf "(%s" (prettyT_lp (i+1) lp)
  | RecordT lr -> Printf.sprintf "{%s" (prettyT_lr (i+1) lr)

and prettyT_lp (i:int) = function
  | [] -> assert false
  | [t] -> Printf.sprintf "%s)" (prettyT i t)
  | t::q -> Printf.sprintf "%s, %s" (prettyT i t) (prettyT_lp i q)

and prettyT_lr (i:int) = function
  | [] -> assert false
  | [n,t] -> Printf.sprintf "%s : %s}" n (prettyT i t)
  | (n,t)::q -> Printf.sprintf "%s : %s; %s" n (prettyT i t) (prettyT_lr i q)


let rec pretty (i:int) = function
  | VarE s -> s
  | AppE (a,b) -> Printf.sprintf "(%s %s)" (pretty i a) (pretty i b)
  | LambdaE (x,t,e) -> 
      Printf.sprintf "function (%s:%s) -> \n%s%s" x (prettyT i t) (space (i+2)) (pretty (i+2) e)
  | MatchE (x,lp) ->
      Printf.sprintf "match %s with%s" x (pretty_lp i lp)
  | LetE (x,t,a,b) ->
      Printf.sprintf "let %s : %s = %s in\n%s%s" x (prettyT i t) (pretty (i+2) a) (space i) (pretty i b)

and pretty_lp (i:int) = function
    [] -> ""
  | (c,x,e)::q -> Printf.sprintf "\n%s| %s %s -> %s%s" (space i) c x (pretty (i+4) e) (pretty_lp i q) 


let rec pretty_sum (i:int) = function
    [] -> ""
  | (c,t)::q -> Printf.sprintf "\n | %s of %s%s" c (prettyT 4 t) (pretty_sum i q)
      
let pretty_typedecl = function
  | Sum_type (t,l) -> Printf.sprintf "type %s = %s\n" t (pretty_sum 0 l)
  | Alias (t, exp) -> Printf.sprintf "type %s = %s\n" t (prettyT 2 exp)

let pretty_expdecl (x,t,exp) =
  Printf.sprintf "let %s : %s = %s\n" x (prettyT 0 t) (pretty 0 exp)
