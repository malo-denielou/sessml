(********************************************************************)
(* SessML - Implementation                                          *)
(*                                                                  *)
(* syntax.ml                                                        *)
(********************************************************************)
(* $Time-stamp: <05-08-2010 10:27 by Malo Deniélou>$ *)

open Common

(************************************)
(* Abstract syntax for source files *)
(************************************)

type principal = string

type vars = string list

type message = 
    {label : string ;
     write : vars;
     read : vars} (* name of the constructor and the type of the sent value *)


type as_role_type = 
  | ASEnd
  | ASGoto of info * string
  | ASMu of info * string * as_role_type
  | ASSend of info * ((message * as_role_type) list)
  | ASReceive of info * ((message * as_role_type) list)

type as_session =
    (string * string * as_role_type) list
      (* role name, type and description *)  

type varlist = 
    (string * string) list (* var name and type name *)

type trustlist =
    (string * string) list (* role name and role name *)

type rtype = Single | Multi

type as_rolelist =
    (string * rtype * string) list

type as_global =
  | GASEnd
  | GASGoto of info * string
  | GASMu of info * string * as_global
  | GASMsg of info * (string * string * (((string * string) * string list) * as_global) list)
  | GASPoll of info * (string * string * as_global)
  | GASSeq of info * (as_global * as_global)
  | GASPar of info * (as_global * as_global)

type ast = 
    Localast of string * varlist * trustlist * as_session
  | Globalast of string * as_rolelist * as_global

type node = int (* index *)


let node_ident = 
  Hashtbl.create 10
    
let clear_ident () = 
  Hashtbl.clear node_ident

    
let find_node (i:string) =
  Hashtbl.find node_ident i
    
let remove_ident (i:string) =
  Hashtbl.remove node_ident i

let nref = ref 0

let create_node_name ()=
  let i = !nref in 
  let _ = incr nref in
  i

let add_ident (i:string) =
  if Hashtbl.mem node_ident i
  then Hashtbl.find node_ident i
  else 
    let n = create_node_name () in
    let () = Hashtbl.add node_ident i n in
    n


let rec print_as_role  = function
  | ASEnd -> "End "
  | ASGoto (_,g) -> ("Goto "^g)
  | ASMu (_,g,r) -> ("Mu "^g^":")^(print_as_role r)
  | ASSend (_,l) -> "Send ("^(String.concat "+" (List.map (function (_,r) -> print_as_role r) l))^")"
  | ASReceive (_,l) -> "Receive ["^(String.concat "|" (List.map (function (_,r) -> print_as_role r) l))^"]"

    (*
let rec role_to_string  = function
  | ASEnd -> "End"
  | ASGoto _ -> "Goto"
  | ASMu (_,_,r) -> "Mu "^(role_to_string r)
  | ASSend (_,l) -> "Send"^()
  | ASReceive _ -> "Receive"
    *)

let rec print_as_global : as_global -> string = function
  | GASEnd -> "End "
  | GASGoto (_,g) -> ("Goto "^g)
  | GASMu (_,g,r) -> ("Mu "^g^":")^(print_as_global r)
  | GASMsg (_,(s,r,ml)) -> s^" -> "^r^" with ("
      ^(String.concat "|" 
          (List.map (function (((c,t),lv),r) -> 
                       let lv = if lv=[] then "" else ("{"^(String.concat "," lv)^"}") in
                     c^lv^"("^t^")."^print_as_global r) ml))^")"
  | GASPoll(_,(v,r,g)) -> "forall ("^v^":"^r^").("^(print_as_global g)^")"
  | GASSeq (_,(g,r)) -> (print_as_global g)^" ;\n "^(print_as_global r)
  | GASPar (_,(g,r)) ->  (print_as_global g)^" \n|| "^(print_as_global r)



(*********************************************)
(* Graph-like representation of the protocol *)
(*********************************************)

type role_name = string
type var_name = string

type p = var_name * role_name

type role_type =
    | End of node
    | Goto of node
    | Send of node * ((message * role_type) list)
    | Receive of node * ((message * role_type) list)

type role_list = (role_name * string * role_type) list

(*
type as_rolelist =
    (string * rtype * string) list
*)
type roles_list = as_rolelist

type global_type =
    | GEnd of node
    | GGoto of node
    | GMsg of node * (p * p * ((string * string) * (var_name list) * global_type) list)
    | GPoll of node * (p * (var_name list) * global_type * global_type) 
    | GPar of node * (global_type * global_type * global_type) 
    | GRec of node * global_type

type lnode = node * node

type local_type =
    | LEnd of lnode
    | LGoto of lnode
    | LSend of lnode * (p * ((string * string) * (var_name list) * local_type) list)
    | LRecv of lnode * (p * ((string * string) * (var_name list) * local_type) list)
    | LPoll of lnode * (p * (var_name list) * local_type * local_type) 
    | LPar of lnode * (local_type * local_type * local_type) 
    | LRec of lnode * local_type

type session = 
    Local of (varlist * trustlist * role_list)
  | Global of (string * roles_list * global_type)

(* Nodes *)

let node_of_global = function
  | GEnd n -> n
  | GGoto n -> n
  | GMsg (n,_) -> n
  | GPoll (n,_) -> n
  | GPar (n,_) -> n
  | GRec (n,_) -> n
 
let node_of_local = function
  | LEnd n -> fst n
  | LGoto n -> fst n
  | LSend (n,_) -> fst n
  | LRecv (n,_) -> fst n
  | LPoll (n,_) -> fst n
  | LPar (n,_) -> fst n
  | LRec (n,_) -> fst n
       

(* Equality modulo nodes *)

let rec ltequal = function
  | LEnd _,LEnd _ -> true 
  | LGoto n,LGoto m -> snd n=snd m
  | LSend (n,(r,ml)),LSend (m,(rr,mll)) -> 
      r = rr && List.for_all (function ((l,lv,g),(ll,lvv,gg)) ->
                                l = ll && lv = lvv && ltequal (g,gg))
                                (List.combine ml mll)
  | LRecv (n,(s,ml)),LRecv (m,(ss,mll)) -> 
      s = ss && List.for_all (function ((l,lv,g),(ll,lvv,gg)) ->
                                l = ll && lv = lvv && ltequal (g,gg))
                                (List.combine ml mll)
  | LPoll (n,(v,pl,g,c)),LPoll (m,(vv,pll,gg,cc))-> 
      v = vv && pl = pll && ltequal (g,gg) && ltequal (c,cc)
  | LPar (n,(g,r,c)),LPar (m,(gg,rr,cc)) -> 
      ltequal (g,gg) && ltequal (r,rr) && ltequal (c,cc)
  | LRec (n,g),LRec (m,gg) -> ltequal (g,gg)
  | _,_ -> false

(* Printing *)

let rec sprint_gt = function
  | GEnd n -> Printf.sprintf "<%d>End" n
  | GGoto n -> Printf.sprintf "Goto[%d]" n
  | GMsg (n,((s,ss),(r,rr),ml)) -> 
      Printf.sprintf "<%d>%s->%s(%s)" n 
        (if s=ss then s else s^":"^ss) (if r=rr then r else r^":"^rr) 
        (String.concat "+" 
           (List.map (function ((c,t),lv,g)-> 
                       let lv = if lv=[] then "" else ("{"^(String.concat "," lv)^"}") in
                       Printf.sprintf "%s%s(%s).(%s)" c lv t (sprint_gt g)) ml))
  | GPoll (n,((x,r),pl,g,c)) -> 
      Printf.sprintf "<%d>Poll(%s:%s|%s).(%s);%s" n x r (String.concat "," pl)
        (sprint_gt g) (sprint_gt c)
  | GPar (n,(g,r,c)) -> 
      Printf.sprintf "<%d>(%s||%s);%s" n (sprint_gt g) (sprint_gt r) (sprint_gt c)
  | GRec (n,g) -> Printf.sprintf "<%d>{%s} " n (sprint_gt g)



let rec sprint_lt = function
  | LEnd n -> Printf.sprintf "End[%d]" (fst n)
  | LGoto n -> Printf.sprintf "Goto[%d]" (fst n)
  | LSend (n,((r,rr),ml)) -> 
      Printf.sprintf "<%d>!%s(%s)" (fst n) (if r=rr then r else r^":"^rr) 
        (String.concat "+" 
           (List.map (function ((c,t),lv,g)-> 
                       let lv = if lv=[] then "" else ("{"^(String.concat "," lv)^"}") in
                       Printf.sprintf "%s%s(%s).(%s)" c lv t (sprint_lt g)) ml))
  | LRecv (n,((s,ss),ml)) -> 
      Printf.sprintf "<%d>?%s(%s)" (fst n) 
        (if s=ss then s else s^":"^ss)
        (String.concat "+" 
           (List.map (function ((c,t),lv,g)-> 
                       let lv = if lv=[] then "" else ("{"^(String.concat "," lv)^"}") in
                       Printf.sprintf "%s%s(%s).(%s)" c lv t (sprint_lt g)) ml))
  | LPoll (n,((x,r),pl,g,c)) -> 
      Printf.sprintf "<%d>Poll(%s:%s|%s).(%s);%s" (fst n) x r (String.concat "," pl)
        (sprint_lt g) (sprint_lt c)
  | LPar (n,(g,r,c)) -> 
      Printf.sprintf "<%d>(%s||%s);%s" (fst n) (sprint_lt g) (sprint_lt r) (sprint_lt c)
  | LRec (n,g) -> Printf.sprintf "<%d>{%s} " (fst n) (sprint_lt g)


let sprint_global = function
    Global (s,rl,g) -> 
      begin
        s^":\nroles: "^(String.concat "," (List.map (function (r,_,_)->r) rl))
        ^"\n"^(sprint_gt g)^"\n"
      end


(* Conversion function from AS to role_type *)
let rec conversion (next:node option) = function
  | ASEnd -> 
      let n = create_node_name () in End n
  | ASGoto (_,i) -> Goto (add_ident i)
  | ASMu (_,i,r) -> 
      let n = add_ident i in
      conversion (Some n) r
  | ASSend (_,l) -> 
      let n = match next with None -> create_node_name () | Some k -> k in
      Send (n, List.map (function (m,r) -> (m,conversion None r)) l)
  | ASReceive (_,l) -> 
      let n = match next with None -> create_node_name () | Some k -> k in
      Receive (n, List.map (function (m,r) -> (m,conversion None r)) l)

let to_role_type : as_session -> role_list =
  List.map 
    (function (x,y,z) -> 
       let () = clear_ident () in
       (* let _ = nref:=0 in *)
       (x,y,conversion None z))



(* Get the starting node of a role_type *)
let node_of : role_type -> node = function
  | End n -> n
  | Goto n -> n
  | Send (n,_) -> n
  | Receive (n,_) -> n


let rec sprint_role = function
  | End n -> Printf.sprintf "End %d " n
  | Goto n -> Printf.sprintf "Goto %d " n
  | Send (n,l) -> (Printf.sprintf "%d:Send{%s" n (sprint_list_messages l))
  | Receive (n,l) -> (Printf.sprintf "%d:Receive{%s" n (sprint_list_messages l))
and sprint_list_messages = function
    [] -> ""
  | (m,r)::q -> (Printf.sprintf "|{%s}%s{%s}.%s%s" 
                    (String.concat "," m.write) 
                    m.label 
                    (String.concat "," m.read) 
                    (sprint_role r) 
                    (sprint_list_messages q))

let rec sprint_session : role_list -> string = function
    [] -> ""
  | (s,u,r)::q -> 
      begin
        s^" : "^u^"\n"^
        (sprint_role r)^"\n"^
        (sprint_session q)
      end

