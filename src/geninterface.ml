(********************************************************************)
(* SessML - Implementation                                          *)
(*                                                                  *)
(* geninterface.ml                                                  *)
(********************************************************************)
(* Time-stamp: <05-08-2010 15:48 by Pierre-Malo Denielou> *)


open Common
open Syntax 
open Graph
open Printf

(********************************************)
(*         Global Helper Functions          *)
(********************************************)

let first_send r = 
  match r with
    | Send (_,_) -> true
    | _ -> false 


let rec vars_to_type vl = function
    [] -> "unit"
  | [a] -> (List.assoc a vl)
  | a::q -> (List.assoc a vl)^" * "^(vars_to_type vl q)
 

(********************************************)
(*            Interface Generation          *)
(********************************************)

(* Principal singleton type name *)
let prin_type s = "var_"^s
let prin_cons s = capitalize s

(* Variable singleton type name *)
let var_type s = "var_"^s
let var_cons s = capitalize s

(* types and labels *)
let gen_result_type (role:string) = Printf.sprintf "result_%s" role
let gen_typename (n:node) = Printf.sprintf "msg%d" n
let gen_handler_label (cons:string) = Printf.sprintf "h%s" cons


let rec create_var_prin_i : role_list -> string = function
    [] -> ""
  | (r,_,_)::q -> 
      (Printf.sprintf "type %s = %s of principal\n" 
        (prin_type r)
        (prin_cons r)
      )^create_var_prin_i q

let rec create_var_i : varlist -> string = function
    [] -> ""
  | (n,t)::q -> 
      (Printf.sprintf "type %s = %s of %s\n" 
        (var_type n)
        (var_cons n)
        t
      )^create_var_i q



let gen_prins (varlist:varlist) (rl:role_list) (fut:future) = 
  let var = String.concat ";\n  "
    (List.map (function (n,t) -> Printf.sprintf "%s: %s" n t) varlist) in
  let hashes = String.concat ";\n  "
    (List.map (function (n,t) -> Printf.sprintf "h%s:bytes" n) varlist) in
  let macs = remove_duplicates 
    (List.flatten (List.map 
                     (function ((m,a),l) -> 
                        List.map 
                          (function (r,v) -> r^m.label^(String.concat "" v)) l) fut))  in
  let macs = String.concat ";\n  " (List.map (function s -> s^": bytes") macs)
  in 
  let roles = List.map (function (r,_,_) -> r) rl in
  let pairs = List.filter (function (x,y) -> x<>y) (product roles roles) in
  let keys = String.concat ";\n  " 
    (List.map (function (x,y)-> "key_"^x^y^": bytes") pairs) in
  "\ntype vars = {\n  "^var^"}\n"
  ^"type hashes = {\n  "^hashes^"}\n"
  ^"type macs = {\n  "^macs^"}\n"
  ^"type keys = {\n  "^keys^"}\n"
  ^"type header = {\n"
  ^"  ts: int;\n"
  ^"  sid: bytes }\n"
  ^"type store = \n"
  ^"  { vars: vars; hashes: hashes; macs: macs; keys: keys; header: header }\n"


(********************************************)
(*             Proof Support                *)
(********************************************)


let genEvents vl (g:graph) (sg:stategraph) =
  let g = List.rev g in
  let lsend =
    List.map 
      (function (_,m,_)-> 
         let wv = List.map 
           (function x -> Printf.sprintf "%s" (List.assoc x vl)) m.write in
         let args = 
           if m.write = [] then "" else "* "^(String.concat " * " wv) in
         Printf.sprintf "| Send_%s of (principal * bytes * int%s)\n" m.label args
      ) g in
  let lrecv =
    List.map 
      (function (_,m,_)-> 
         let rv = List.map 
           (function x -> Printf.sprintf "%s" (List.assoc x vl)) m.read in
         let args = 
           if m.read = [] then "" else " * "^(String.concat " * " rv) in
         Printf.sprintf "| Recv_%s of (principal * bytes * int%s)\n" m.label args
      ) g in
  let predsdecl = "\ntype preds = \n" in
  predsdecl
  ^(String.concat "" (lsend @ lrecv))

(* Send and Recv wired interface *)

let rec generate_wired_type vl visib : state list -> string list= function 
    [] -> []
  | state::q -> 
      let gen_type sv = 
        String.concat "\n" 
          (List.map (function v -> 
                       let ((_,seq),_) = List.hd v in
                       let (_,m,_) = List.hd seq in
                       Printf.sprintf "  | Wired_in_%s_of_%s of (%s) * store"
                         (print_state state)
                         (print_vi v)
                         (vars_to_type vl m.read))
             sv)
      in
      let lv = remove_duplicates (subset_assoc state visib) in
      (Printf.sprintf "\ntype wired_%s ="
         (print_state state))::
        (String.concat "\n" (List.map gen_type lv))
      ::(generate_wired_type vl visib q)
 

let genrecvwired (visib:visib) =
  let states = remove_duplicates (List.map fst visib) in
  let from_state = function state ->
    Printf.sprintf 
      "\nval receiveWired_%s: store -> wired_%s" (print_state state) (print_state state)
  in
  remove_duplicates (List.map from_state states)
  

let gensendwired vl (sg:stategraph) =
  let lv = List.map fst vl in
  let from_edge = function ((state,next),m,_) ->
    let argvars = String.concat "" (List.map (fun x->(List.assoc x vl)^" -> ") m.write) in
    Printf.sprintf 
      "\n val sendWired_%s_%s: %s store -> store" 
      m.label
      (print_state state)
      argvars
  in
  remove_duplicates (List.map from_edge sg)


(*------------------------------*)
(* First Lines of the interface *)
(*------------------------------*)

let candy_title =
"(*******************************)\n"
  ^"(* Generated Session Interface *)\n"
  ^"(*******************************)"

let global_def_i rl vl =
  candy_title^"\nopen Data\n\n"
  ^"type principal=string\n\n"

let gen_user_inputs_i (l:role_type list) : string =
  match l with
      [] -> assert false
    | (Send (n,_ ))::_-> Printf.sprintf " %s ->" ((gen_typename n))
    | (Receive (n,_))::_-> Printf.sprintf " %s ->" ((gen_typename n))
    | _ -> assert false

let crypto_first_line_i = ": principal ->"
let crypto_first_line_recv_i = ": principal ->"
let first_line_i (l:role_type list) = crypto_first_line_i^(gen_user_inputs_i l)
let first_line_recv_i (l:role_type list) = crypto_first_line_recv_i^gen_user_inputs_i l
  


(*------------*)
(* Flow types *)
(*------------*)

(* sending types *)
let rec gen_type_var_send : string list -> string = function
  | [] -> ""
  | v::q -> (var_type v)^" * "^(gen_type_var_send q)

let gen_constructor_send (m:message) : string = 
  Printf.sprintf " %s of (%s" m.label (gen_type_var_send m.write)

let rec gen_sumtype_send (role:string) : (message * role_type) list -> string = function 
    [] -> ""
  | [m,Goto n] -> 
      (gen_constructor_send m)^(gen_typename n)^")\n"
  | [m,End _] -> 
      (gen_constructor_send m)^(gen_result_type role)^")\n"
  | [_,_] -> assert false
  | (m,Goto n)::q -> 
      (gen_constructor_send m)^(gen_typename n)^")\n |"^(gen_sumtype_send role q)
  | (m,End _)::q -> 
      (gen_constructor_send m)^(gen_result_type role)^")\n |"^(gen_sumtype_send role q)
  | _ -> assert false

(* recieving types *)
let rec gen_type_var_recv : string list -> string = function
  | [] -> "unit -> "
  | [v] -> (var_type v)^" -> "
  | v::q -> (var_type v)^" * "^(gen_type_var_recv q)

let gen_constructor_recv (m:message) : string = 
  Printf.sprintf "   %s : (%s" (gen_handler_label m.label) (gen_type_var_recv m.read)


let rec gen_sumtype_recv (role:string) : (message * role_type) list -> string = function 
    [] -> ""
  | [m,Goto n] -> 
      (gen_constructor_recv m)^(gen_typename n)^")}\n"
  | [m,End _] -> 
      (gen_constructor_recv m)^(gen_result_type role)^")}\n"
  | [_,_] -> assert false
  | (m,Goto n)::q -> 
      (gen_constructor_recv m)^(gen_typename n)^");\n"^(gen_sumtype_recv role q)
  | (m,End _)::q -> 
      (gen_constructor_recv m)^(gen_result_type role)^");\n"^(gen_sumtype_recv role q)
  | _ -> assert false

let gen_decl (role:string) : role_type -> string = function
    End _ -> assert false
  | Goto _ -> assert false
  | Send (n,l) -> (gen_typename n)^" = \n  "^(gen_sumtype_send role l )
  | Receive (n,l) -> (gen_typename n)^" = {\n"^(gen_sumtype_recv role l )

 (*     let n = alias na n in *)

let rec gen_types (param:string) (role:string) : role_type list -> string = function
    [] -> ""
  | [r] -> "\n"^param^"type "^(gen_decl role r)
  | r::q -> (gen_types param role q)^"and "^(gen_decl role r)


let generate_functions_i (role:string) (r : role_type list) (original_role:role_type)=
let initiator = (first_send original_role) in
  Printf.sprintf "val %s %s result_%s\n"
    role
    (if initiator then
	(debug (Printf.sprintf "%s is initiator" role); first_line_i r)
      else 
	(debug (Printf.sprintf "%s is not initiator" role); first_line_recv_i r))
    role


(*-----------------*)
(* Main generation *)
(*-----------------*)


(* Generate the proxy interface for each role *)
let generate_from_role_i (param:string) (role_name:string) (typ:string) (role:role_type) (original_role:role_type)= 
  let flatten_session = flatten role in
  (Printf.sprintf "\n(* Proxy function for role %s *)\n" role_name)
  ^(Printf.sprintf "\n%stype %s = %s\n" param (gen_result_type role_name) typ)
  ^(gen_types param role_name (List.rev flatten_session))^"\n"
  ^(generate_functions_i role_name flatten_session role)
      
(* Generate the proxy interfaces *)
let rec generate_from_session_i (param:string) (s:role_list) = 
  match s with
      [] -> []
    | (str,typ,rol)::q -> 
        debug (Printf.sprintf "Generating interface of role %s " str);
        (generate_from_role_i param str typ rol rol)
        ::(generate_from_session_i param q )

(* Generates the full interface *)
let generate_protocol (s:session) (g:graph) (visib:visib) (fut:future) (sg:stategraph): string =
  match s with Global _ -> failwith "Unsupported"
    | Local (vl,tl,rl) ->
  let vl = (List.map (function (r,_,_) -> (r,"principal")) rl)@vl in
  let states = remove_duplicates (List.map fst visib) in
  let roles = List.map (function (r,_,_) -> r) rl in
  (global_def_i rl vl)
  ^(gen_prins vl rl fut)
  ^(String.concat "" 
      (List.map (fun r -> "val empty_store_"^r^" : principal -> bool -> store\n") roles))
  ^(genEvents vl g sg)^"\n\n"
  ^(String.concat "\n" (generate_wired_type vl visib states))
  ^(String.concat "\n" (genrecvwired visib))
  ^(String.concat "\n" (gensendwired vl sg))

(* Generates the full interface *)
let generate (session_name:string) (s:session)=
  match s with Global _ -> failwith "Unsupported"
    | Local (vl,tl,rl) ->
  let vl = (List.map (function (r,_,_) -> (r,"principal")) rl)@vl in
  ("open "^session_name^"_protocol\n")
  ::(create_var_i vl)
  ::(generate_from_session_i "" rl)



(********************************************)
(*              SessML Part                 *)
(********************************************)

let rec lgen_rectypes : (string list) -> string = function
    [] -> ""
  | [r] -> r
  | r::q -> r^"\nand "^(lgen_rectypes q)

let lgen_nexttype role = function
  | LEnd n -> "unit"
  | x -> sprintf "%s_%d" role (node_of_local x)


let rec lgen_local role next = function
  | LEnd n -> [] (*[sprintf " %s_%d = unit " role (fst n)]*)
      (* begin
        match next with
          | None -> [sprintf " %s_%d = result_%s " role (fst n) role]
          | Some (i) -> [sprintf " %s_%d = %s_%i " role (fst n) role i]
      end*)
  | LGoto n -> []
  | LSend (n,((r,rr),ml)) -> 
      (sprintf " %s_%d = %s%s" role (fst n) (if List.length ml = 1 then "" else "\n   ")
         (String.concat "\n | " 
            (List.map (function ((c,t),lv,g)-> 
                         let lv = List.map (fun x->"principal") lv in
                         let lv = if lv=[] then "" else (" * "^(String.concat "*" lv)) in
                         Printf.sprintf "%s of %s%s * %s" c t lv (lgen_nexttype role
                           g)) ml)))::
        (List.flatten 
           (List.map (function ((c,t),lv,l)-> lgen_local role next l) ml))
  | LRecv (n,((s,ss),ml)) -> 
      (sprintf " %s_%d = %s{ %s }" role (fst n) (if List.length ml = 1 then "" else "\n")
         (String.concat " ; \n  " 
            (List.map (function ((c,t),lv,g)-> 
                         let lv = List.map (fun x->"principal") lv in
                         let lv = if lv=[] then "" else (" * "^(String.concat "*" lv)) in
                         Printf.sprintf "h%s : %s%s ->  %s" c t lv (lgen_nexttype role
                            g)) ml)))::
        (List.flatten 
           (List.map (function ((c,t),lv,l)-> lgen_local role next l) ml))
  | LPoll (n,((x,r),pl,g,c)) -> 
      (Printf.sprintf " %s_%d = (principal -> %s) * (unit -> %s)"
         role (fst n) (lgen_nexttype role g) (lgen_nexttype role c))::
        (lgen_local role (Some (node_of_local c)) g)@(lgen_local role next c)
  | LPar (n,(g,r,c)) -> 
      (Printf.sprintf " %s_%d = (unit -> %s) * (unit -> %s) * (unit -> %s)"
         role (fst n) (lgen_nexttype role g) 
         (lgen_nexttype role r) (lgen_nexttype role c))::
        (lgen_local role (Some (node_of_local c)) g)@
        (lgen_local role (Some (node_of_local c)) r)@
        (lgen_local role next c)
  | LRec (n,g) -> 
      (sprintf " %s_start = %s_%d " role role (node_of_local g))::
        (sprintf " %s_%d = Continue_as_%s of %s_%d | Quit_as_%s of result_%s"
           role (fst n) role role (node_of_local g) role role)::
        (lgen_local role next g)

let lgen_localtypes role local = 
  Printf.sprintf "\ntype%s\n" (lgen_rectypes (lgen_local role None local))

let lgen_types name rt local =
  (Printf.sprintf "\ntype result_%s = %s\n" name rt)
  ^(lgen_localtypes name local)
