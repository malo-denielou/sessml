(********************************************************************)
(* SessML - Implementation                                          *)
(*                                                                  *)
(* properties.ml                                                    *)
(********************************************************************)
(* $Time-stamp: <28-07-2010 14:36 by Pierre-Malo Denielou>$ *)

open Common
open Syntax 
open Graph

let debug_prop = gen_debug debug_properties  "graph-properties"
  
(**************************)
(* Verification functions *)
(**************************)

let trusts tl (a:role_name) (b:role_name) =
  a = b || List.mem b (subset_assoc a tl)


(* Property 1:
   By construction the graphs' edges have different source and target roles, but
   we can check it anyway *)
let rec check_no_self_send (role_assoc:node_to_role) (g:graph) =
  match g with
      [] -> ()
    | (i,m,j)::q -> 
        if (List.assoc i role_assoc = List.assoc j role_assoc)
        then begin Printf.printf 
            "The message %s carrying is internal to %s.\n" 
            m.label (List.assoc i role_assoc) ;
          raise (Graph_error "The graph does not satisfy the property 1.")
        end
        else (check_no_self_send role_assoc q)

(* Property 2:
   We check the unicity of labels *)
let check_unique_target (role_assoc:node_to_role) (g:graph) =
  let sorted_graph = 
    List.sort 
      (function (_,m,_) -> function (_,m',_) -> compare m.label m'.label) g in 
  let rec check_labels (i,c,j) = function
      [] -> ()
    | (k,m,l)::q -> 
        if c.label = m.label 
        then if (j<>l) || (List.assoc i role_assoc <> List.assoc k role_assoc)
        then begin Printf.printf 
            "Two different messages have label %s: from %d to %d and from %d to %d.\n"
            m.label i j k l ;
          raise (Graph_error "The graph does not satisfy the property 2.")
        end
        else (check_labels (i,c,j) q)
        else check_labels (k,m,l) q
  in
  match sorted_graph with
      [] -> assert false
    | (k,m,l)::q -> check_labels (k,m,l) q
          

(* Property 3:
   We check the No Blind Fork property. *)
(* Since we enforce that each send only send to one role, this property is
   already enforced for less than 3 roles *)
let check_no_blind_fork (role_assoc:node_to_role) (tl:(role_name*role_name)list) (g:graph) =
  let rec check_width origin (visi,visj) roles i j (sli,slj) = 
    match (sli,slj) with
        [],[] -> true
      | [],(j,n,k)::r ->  let _ = debug_prop 
          (Printf.sprintf "Prop 3: from %d,%d, looking towards %d" i j k) 
        in ((i=j) || (List.mem (j,n,k) visj) (*|| (List.mem (List.assoc k role_assoc) roles) *)
             || (check_depth origin (visi,(j,n,k)::visj) ((List.assoc k role_assoc)::roles) i k))
        && (let _ = debug_prop (Printf.sprintf "Prop 3: from %d,%d, looking after %d" i j k) in 
            (List.assoc j role_assoc) = origin || check_width origin (visi,visj) roles i j ([],r))
      | (i,m,k)::q,[] -> let _ = debug_prop 
          (Printf.sprintf "Prop 3: from %d,%d, looking towards %d" i j k)
        in ((i=j) || (List.mem (i,m,k) visi) (*|| (List.mem (List.assoc k role_assoc) roles) *)
             || (check_depth origin ((i,m,k)::visi,visj) ((List.assoc k role_assoc)::roles) k j))
        && (let _ = debug_prop (Printf.sprintf "Prop 3: from %d,%d, looking after %d" i j k) in 
            (List.assoc i role_assoc) = origin || check_width origin (visi,visj) roles i j (q,[]))
      | (i,m,k)::q,(j,n,l)::r -> let _ = debug_prop 
          (Printf.sprintf "Prop 3: Width =>from %d,%d, looking at %d, %d" i j k l)
        in
        let rolei = (List.assoc i role_assoc) in
        let rolej = (List.assoc j role_assoc) in
        let rolek = (List.assoc k role_assoc) in
        let rolel = (List.assoc l role_assoc) in
        (if (List.mem rolek roles) || (List.mem rolel roles) 
           || (List.exists (trusts tl rolek) roles) 
           || (List.exists (trusts tl rolel) roles)
           || rolek = rolel
         then
           (rolei = origin || rolej = origin
               || (List.mem (i,m,k) visi) || (List.mem (j,n,k) visj)
               || check_depth origin ((i,m,k)::visi,(j,n,l)::visj) (roles) k l)
         else begin
           Printf.printf "There is a forking attack against %s at node %d or %s at node %d;\n" 
             rolek k rolel l ;flush_all ();
           false
         end)
        && (let _ = debug_prop 
              (Printf.sprintf "Prop 3: from %d,%d, finished %d,%d, absorbing %d" i j k l j) in
            rolej = origin || check_width origin (visi,visj) (roles) i j (sli,r))
        && (let _ = debug_prop 
              (Printf.sprintf "Prop 3: from %d,%d, finished %d,%d, absorbing %d" i j k l i) in
            rolei = origin || check_width origin (visi,visj) (roles) i j (q,slj))
  and check_depth origin visited roles i j =
    let _ = debug_prop (Printf.sprintf "Prop 3: Depth => looking at nodes %d and %d knowing %s"
                      i j (concat_c roles)) in
    let sli,_ = select i g in
    let slj,_ = select j g in
    let rolei = (List.assoc i role_assoc) in
    let rolej = (List.assoc j role_assoc) in
    if ((List.mem rolei roles) || (List.mem rolej roles) 
        || (List.exists (trusts tl rolei) roles) 
        || (List.exists (trusts tl rolej) roles)
        || (rolei = rolej))
    then
      (check_width origin visited (rolei::rolej::roles) i j (sli,slj))
    else begin
      Printf.printf "There is a forking attack against %s or %s at nodes %d and %d;\n" 
        (List.assoc i role_assoc) (List.assoc j role_assoc) i j ;flush_all ();
      false
    end
  in
  List.for_all
    (function (i,m,j) -> 
      let _ = debug_prop (Printf.sprintf "Prop 3: Initial from node %d to node %d !!\n" i j) in
      if check_depth (List.assoc i role_assoc) ([],[]) [] j j
      then true
      else begin
        Printf.printf 
          "this attack starts at node %d by a message %s from %s to the node %d.\n" 
          i m.label (List.assoc i role_assoc) j;
        raise (Graph_error "The graph does not satisfy the property 3.")
      end)
    g


(* Property 4: *)
(* Checking that on any initial path every role var is written at most once *)
let check_write_role_once (role_assoc:node_to_role) (g:graph) =
  let sg = sort_by_send g in
  let rec check_depth_once v visited i =
    debug_prop (Printf.sprintf "Prop 4:  -> node %d" i) ;
    let edges = List.flatten (subset_assoc i sg) in
    check_width_once v visited edges
  and check_width_once v visited = function
      [] -> true
    | (i,m,j)::q -> 
        if not (List.mem m visited) then 
          ((if List.mem v m.write 
            then check_depth_none v [] j 
            else check_depth_once v (m::visited) j)
            && check_width_once v visited q)
        else check_width_once v visited q
  and check_depth_none v visited i =
    let edges = List.flatten (subset_assoc i sg) in
    check_width_none v visited edges
  and check_width_none v visited = function
      [] -> true
    | (i,m,j)::q -> 
        if not (List.mem m visited) then 
          ((if List.mem v m.write 
            then begin
                Printf.printf 
                  "The role variable %s is written for a second time in the message %s\n" v m.label;
                raise (Graph_error "The graph does not satisfy the property 4.")
              end
            else check_depth_none v (m::visited) j)
            && check_width_none v visited q)
        else check_width_none v visited q
  in
  let role_list = remove_duplicates (List.map snd role_assoc) in
  List.for_all (function v -> 
    debug_prop (Printf.sprintf "Prop 4: Looking at variable %s" v) ;
    check_depth_once v [] 0) role_list
            
(* Property 5: *)
(* Checking that every role knows its value *)
let check_read_before_role (role_assoc:node_to_role) (g:graph) =
  let sg = sort_by_send g in
  let role_list = remove_duplicates (List.map snd role_assoc) in
  let rec check_depth_once v visited i =
    let edges = List.flatten (subset_assoc i sg) in
    check_width_once v visited edges
  and check_width_once v visited = function
      [] -> true
    | (i,m,j)::q -> 
        debug_prop (Printf.sprintf "Prop 5:            message %s" m.label) ;
        if not (List.mem m visited) then 
          ((if List.assoc j role_assoc = v
            then if List.mem v m.read then true else 
                begin
                Printf.printf 
                  "The role variable %s is not readable by %s in the message %s\n" v v m.label;
                raise (Graph_error "The graph does not satisfy the property 5.")
              end
            else check_depth_once v (m::visited) j)
            && check_width_once v visited q)
        else check_width_once v visited q
  in
  List.for_all (function v -> 
    debug_prop (Printf.sprintf "Prop 5: Looking at role variable %s" v) ;
    check_depth_once v [] 0) (List.tl role_list)
            
(* Property 6: *)
(* Checking that every receiving role knows the previous sending roles *)
let check_knows_before_recv (role_assoc:node_to_role) (g:graph) =
  let sg = sort_by_send g in
  let role_list = remove_duplicates (List.map snd role_assoc) in
  let known = List.map (function r -> (r,[])) role_list in
  let write r vars = 
    let rec remove = function
        [] -> []
      | (rr,v)::q -> 
          (if rr = r then (rr,vars@v) 
            else (rr,List.filter (function x -> not (List.mem x vars)) v)
          )::(remove q)
    in remove in
  let read r vars =
    let rec add = function
      | [] -> []
      | (rr,v)::q -> 
          (if rr = r then (rr,vars@v) 
            else (rr,v))::(add q)
    in add in
  let rec check_depth active known visited i =
    let edges = List.flatten (subset_assoc i sg) in
    debug_prop (Printf.sprintf "Prop 6: node %d" i) ;
    check_width active known visited edges
  and check_width active known visited = function
      [] -> true
    | (i,m,j)::q -> 
        if not (List.mem m visited) then 
          let sender = List.assoc i role_assoc in
          let recver = List.assoc j role_assoc in
          let active = (sender)::active in
          let known = write sender m.write known in
          let known = read recver m.read known in
          ((if List.for_all (function x -> List.mem x (List.assoc recver known)) active
            then check_depth active known (m::visited) j
            else begin
                Printf.printf 
                  "The receiver role %s of message %s does not know the previous active roles\n" recver m.label;
                raise (Graph_error "The graph does not satisfy the property 6.")
              end)
            && check_width active known visited q)
        else check_width active known visited q
  in
  debug_prop (Printf.sprintf "Prop 6: Checking ...") ;
  check_depth [] known [] 0


(* Property 7: *)
(* Check that senders know the future receivers *)
let check_know_before_send (role_assoc:node_to_role) tl (g:graph) =
  let sg = sort_by_send g in
  let role_list = remove_duplicates (List.map snd role_assoc) in
  let known = List.map (function r -> (r,[])) role_list in
  let write r vars = 
    let rec remove = function
        [] -> []
      | (rr,v)::q -> 
          (if rr = r then (rr,vars@v) 
            else (rr,List.filter (function x -> not (List.mem x vars)) v)
          )::(remove q)
    in remove in
  let read r vars =
    let rec add = function
      | [] -> []
      | (rr,v)::q -> 
          (if rr = r then (rr,vars@v) 
            else (rr,v))::(add q)
    in add in
  let rec check_depth_once active known v visited i =
    debug_prop (Printf.sprintf "Prop 7: role %s, from node %i" v i) ;
    let edges = List.flatten (subset_assoc i sg) in
    check_width_once active known v visited edges
  and check_width_once active known v visited = function
      [] -> true
    | (i,m,j)::q -> 
        if not (List.mem m visited) then 
          let sender = List.assoc i role_assoc in
          let recver = List.assoc j role_assoc in
          let active = (sender)::active in
          let known = write sender m.write known in
          let known = read recver m.read known in
          ((if recver = v
            then 
              if List.for_all (fun e -> List.exists (function rr -> trusts tl e rr &&
                List.mem v (List.assoc rr known)) active) active
              then true else 
                begin
                  Printf.printf 
                    "One role does not know %s when sending a message that will be forwarded along with message %s\n" v m.label;
                  raise (Graph_error "The graph does not satisfy the property 7.")
                end
            else check_depth_once active known v (m::visited) j)
            && check_width_once active known v visited q)
        else check_width_once active known v visited q
  in
  List.for_all (function v -> 
    debug_prop (Printf.sprintf "Prop 7: Looking at first contact of role %s" v) ;
    check_depth_once [] known v [] 0) (List.tl role_list)           
   
       
(* Property 8: *)
(* Checking that every sending role knows the variables he is sending. *)
let check_knows_vars(role_assoc:node_to_role) (g:graph) =
  let sg = sort_by_send g in
  let role_list = remove_duplicates (List.map snd role_assoc) in
  let known = List.map (function r -> (r,[])) role_list in
  let write r vars = 
    let rec remove = function
        [] -> []
      | (rr,v)::q -> 
          (if rr = r then (rr,vars@v) 
            else (rr,List.filter (function x -> not (List.mem x vars)) v)
          )::(remove q)
    in remove in
  let read r vars =
    let rec add = function
      | [] -> []
      | (rr,v)::q -> 
          (if rr = r then (rr,vars@v) 
            else (rr,v))::(add q)
    in add in
  let rec check_depth known visited i =
    let edges = List.flatten (subset_assoc i sg) in
    debug_prop (Printf.sprintf "Prop 8: node %d" i) ;
    check_width known visited edges
  and check_width known visited = function
      [] -> true
    | (i,m,j)::q -> 
        if not (List.mem m visited) then 
          let sender = List.assoc i role_assoc in
          let recver = List.assoc j role_assoc in
          let known = write sender m.write known in
          let known = read recver m.read known in
          ((if List.for_all (function x -> List.mem x (List.assoc sender known)) m.read
            then check_depth known (m::visited) j
            else begin
                Printf.printf 
                  "The sender role %s of message %s does not know all the variables that will be read by role %s\n" sender m.label recver;
                raise (Graph_error "The graph does not satisfy the property 8.")
              end)
            && check_width known visited q)
        else check_width known visited q
  in
  debug_prop (Printf.sprintf "Prop 8: Checking ...") ;
  check_depth known [] 0


(* Additional sanity property *)
(* Checking that every variable is declared *)
let check_declared_vars (s:session) (g:graph) =
  match s with Global _ -> failwith "Unsupported"
    | Local (var_list,trust_list,rl) ->
  let lr = List.map (function (r,_,_) -> r) rl in
  let vl = (List.map (function r -> (r,"principal")) lr)@var_list in
  let _ = debug (Printf.sprintf "The variables are %s." (String.concat ","
                                                           (List.map fst vl))) in
  let rec test = function
    | [] -> ()
    | (_,msg,_)::q -> (List.iter 
        (function x -> if List.mem_assoc x vl then () else
           raise (Graph_error ("The variable '"^x^"' has not been declared.")))
          (msg.read @ msg.write);
                       test q)
  in
  (test g)

let check_all (s:session) (role_assoc:node_to_role) (g:graph) =
  match s with Global _ -> failwith "Unsupported"
    | Local (_,tl,_) -> (* tl is the trust relation *)
  let _ = debug (Printf.sprintf "Checking the properties of the session.") in
  let _ = (check_no_self_send role_assoc g) in
  let _ = (check_unique_target role_assoc g) in
  let _ = (check_no_blind_fork role_assoc tl g) in
  let _ = (check_write_role_once role_assoc g) in
  let _ = (check_read_before_role role_assoc g) in
  let _ = (check_knows_before_recv role_assoc g) in
  let _ = (check_know_before_send role_assoc tl g) in
  let _ = (check_knows_vars role_assoc g) in
  let _ = (check_declared_vars s g) in
  ()
