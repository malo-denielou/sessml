(********************************************************************)
(* SessML - Implementation                                          *)
(*                                                                  *)
(* wf.ml                                                            *)
(********************************************************************)
(* $Time-stamp: <05-08-2010 15:37 by Pierre-Malo Denielou>$ *)

open Common
open Syntax

let debug_wf = gen_debug debug_wf "Well-formedness"

(* Conversion to global type *)
let global_conversion (rl:roles_list) (g:as_global) =
  let rk = List.map (function (r,k,_)-> (r,k)) rl in
  
  let rec muelimination (bv: p list) (next:node option) (gend:global_type option) = function
    | GASEnd -> 
        let n = match next with None -> create_node_name () | Some k -> k in
        (match gend with None -> GEnd n | Some g -> g)
    | GASGoto (_,g) -> 
        GGoto (add_ident g)
    | GASMu (_,g,r) ->
        let n = add_ident g in
        muelimination bv (Some n) gend r
    | GASMsg (_,(s,r,ml)) -> 
        let n = match next with None -> create_node_name () | Some k -> k in
        let ss,bbv = try (s,List.assoc s bv),bv 
        with _ -> if List.assoc s rk = Single then (s,s),((s,s)::bv) else assert false in
        let rr,bbv = try (r,List.assoc r bbv),bbv 
        with _ -> if List.assoc r rk = Single then (r,r),((r,r)::bv) else assert false in
        GMsg (n,(ss,rr,(List.map (function ((m,lv),r) ->
                                    (m, lv, muelimination bbv None gend r)) ml)))
    | GASPoll(_,(v,r,g)) -> 
        let n = match next with None -> create_node_name () | Some k -> k in
        let k = create_node_name () in
        let cont = match gend with None -> GEnd (create_node_name ()) | Some g -> g in
        let bbv = (v,r)::bv in
        let lv = List.map fst (List.filter (function (vv,rr) -> r=rr) bv) in
        GPoll(n,((v,r),lv,muelimination bbv None None g,cont))
    | GASSeq (_,(g,r)) -> 
        (muelimination bv next (Some (muelimination bv None gend r)) g)
    | GASPar (_,(g,r)) -> 
        let n = match next with None -> create_node_name () | Some k -> k in
        let cont = match gend with None -> GEnd (create_node_name ()) | Some g -> g in
        GPar (n,(muelimination bv None None g ,muelimination bv None None r,cont))
  in
  muelimination [] None (Some (GGoto 0)) g

let linearity (g:global_type) =
  let rec get_sub lss pl r i =
    if List.mem (r^(string_of_int i)) lss || List.mem (r^(string_of_int i)) pl
    then get_sub lss pl r (i+1) 
    else (r^(string_of_int i),i) in
  let rec dequant ls = function 
    | GEnd n -> GEnd n 
    | GGoto n -> GGoto n 
    | GMsg (n,((vs,s),(vr,r),ml)) -> 
        let s = alias ls vs,s in 
        let r = alias ls vr,r in
        GMsg (n,(s,r,(List.map (function (m,lv,r) ->
                                  let llv = List.map (alias ls) lv in
                                  (m,llv,dequant ls r)) ml)))
    | GPoll (n,((x,r),pl,g,c)) -> 
        let pll = List.map (alias ls) pl in
        let lss = List.map snd ls in
        let s1,i = get_sub lss pll r 1 in
        let s2,_ = get_sub lss pll r (i+1) in
        let ls1 = (x,s1)::ls in
        let ls2 = (x,s2)::ls in
        GPar (n,(dequant ls1 g,dequant ls2 g,dequant ls c))
    | GPar (n,(g,r,c)) -> GPar (n,(dequant ls g,dequant ls r,dequant ls c))
    | GRec (n,g) -> GRec (n,dequant ls g) 
  in
  let dqg = dequant [] g in
 let () = debug_wf ("Dequantification\n"^sprint_gt dqg) in
  let rec get_msg = function
    | GEnd n -> []
    | GGoto n -> []
    | GMsg (n,(s,r,ml)) -> 
        List.concat (List.map (function ((l,t),lv,c) ->
                                 (((s,r),l),(lv,t,c))::(get_msg c)) ml)
    | GPoll (n,((x,r),pl,g,c)) -> assert false
    | GPar (n,(g,r,c)) -> (get_msg g)@(get_msg r)@(get_msg c)
    | GRec (n,g) -> get_msg g
  in
  let lm = get_msg dqg in
  let () = 
     debug_wf ("List of messages\n"^ String.concat "\n" 
     (List.map (function (((s,r),l),(lv,t,c)) ->
     Printf.sprintf "%s>>%s:%s->%s:%s   {%s}(%s) ==> %s"
     l (fst s) (snd s) (fst r) (snd r)
     (String.concat "," lv) t (sprint_gt c)) lm)) in
  let rec compat lm = function
      [] -> true
    | (k,(lv,t,c))::q -> if List.mem_assoc k lm 
      then (
        let llv,tt,cc = List.assoc k lm in
        (lv <> llv || (
           let () = debug_wf ("Linearity WARNING: ambiguous message label "^snd k) in
           t=tt && c=cc)) && compat lm q
      )
      else compat lm q in
  let rec check = function
    | GEnd n -> true
    | GGoto n -> true
    | GMsg (n,(s,r,ml)) -> 
        List.for_all (fun x->x) (List.map (function (_,_,c) -> check c) ml)
    | GPoll (n,((x,r),pl,g,c)) -> assert false
    | GPar (n,(g,r,c)) -> 
        (check g) && (check r) && (check c) && (
          let lg = (get_msg g) in
          let lr = (get_msg r) in 
          compat lg lr)
    | GRec (n,g) -> check g
  in
  let () = debug_wf ("Linearity "^(string_of_bool (check dqg))) in 
  ()



let sanitize (rl:roles_list) (g:as_global)= 
  (* if it's a looping global type *)
  let zero = create_node_name () in
  let g = GRec (zero,global_conversion rl g) in
  let rk = List.map (function (r,k,_)-> (r,k)) rl in
  let () = debug_wf ("Conversion from AST\n"^sprint_gt g) in
  let () = linearity g in
  g



let project (rl:roles_list) (g:global_type) =
  let torole role g =
    let nref = ref 0 in
    let create_node_name ()= let i = !nref in let _ = incr nref in i in
    let ndb = ref [] in
    let add_node n =
      if List.mem_assoc n !ndb
      then (List.assoc n !ndb,n)
      else 
        let i = create_node_name () in
        let () = ndb := (n,i)::!ndb in
        (i,n)
    in
    let next (i,n) =
      let ii = create_node_name () in
      let () = ndb := (n,ii)::!ndb in
      (ii,n) in
    let rec lmmerge lm = function
      | [] -> lm
      | ((l,t),lv,c)::q -> 
          if List.exists (function ((ll,_),lvv,cc)->ll=l && lv=lvv) lm
          then 
            let newlm = List.map (function ((ll,tt),lvv,cc) -> 
                                    if ll=l && lv=lvv
                                    then (if t=tt
                                          then ((ll,tt),lvv,merge [cc;c])
                                          else failwith "Unmergeable (different payload types)")
                                    else ((ll,tt),lvv,cc)) lm in
            lmmerge newlm q
          else
            lmmerge (((l,t),lv,c)::lm) q
    and merge l = match l with
        [] -> assert false
      | [lt] -> lt
      | c::q -> 
          if List.for_all (fun l -> ltequal (l,c)) q 
          then c 
          else match c,List.for_all (function LRecv(_) -> true|_->false) q with
            | LRecv(k,(s,lm)),true -> add (k,(s,lm)) q
            | _,_ -> failwith "Unmergeable (not only reception)"
    and add (k,(s,lm)) = function 
      | [] -> LRecv(k,(s,lm))
      | (LRecv(kk,(ss,lmm)))::q -> 
          if s = ss then
            let newlm = lmmerge lm lmm in
            add (k,(s,newlm)) q
          else failwith "Unmergeable (different senders)"
      | _ -> assert false
    in
    let rec aux ls = function
      | GEnd n -> let k = add_node n in LEnd k
      | GGoto n -> let k = add_node n in LGoto k
      | GMsg (n,(s,r,ml)) -> 
          let k = add_node n in 
          let kk = next k in 
          let ss = alias ls (fst s),snd s in 
          let rr = alias ls (fst r),snd r in
          if ss = (role,role)
          then LSend(kk,(rr,
                        (List.map 
                           (function((l,t),lv,c)->
                              (l,t),(List.map (alias ls) lv),aux ls c
                           ) ml)))
          else if rr = (role,role)
          then LRecv(kk,(ss,
                        (List.map 
                           (function((l,t),lv,c)->
                              (l,t),(List.map (alias ls) lv),aux ls c
                           ) ml)))
          else merge (List.map (function (_,_,c)-> aux ls c) ml)
      | GPoll (n,((x,r),pl,g,c)) -> 
          let k = add_node n in 
          let kk = next k in 
          let kkk = next kk in 
          if r <> role then
            LPoll(k,((x,r),pl,aux ls g,aux ls c))
          else if List.mem role (List.map (alias ls) pl) then
            LPoll(k,((x,r),(List.map (alias ls) pl),aux ls g,aux ls c))
          else 
            LPar(k,(aux ((x,role)::ls) g,
                    LPoll(kk,((x,r),role::pl,aux ls g,LEnd kkk)),aux ls c))
      | GPar (n,(g,r,c)) -> 
          let k = add_node n in 
          LPar(k,(aux ls g,aux ls r,aux ls c))
      | GRec (n,g) -> 
          let k = add_node n in LRec (k,aux ls g)
                                  
    in (role,aux [] g)
  in
  let ltypes = List.map (function (role,_,_) -> torole role g) rl in
  let () = 
    List.iter (function (r,l) -> 
                 debug_wf ("Local type for "^r^":\n"^sprint_lt l)) ltypes in
  ltypes


(* Cleans the local types for empty parallel branches *)
let clean_local lt = 
  let rec lappend cc = function
    | LEnd n -> cc
    | LGoto n -> LGoto n 
    | LSend (n,((r,rr),ml)) ->
        let lmm = List.map (function (l,lv,g)-> (l,lv,lappend cc g)) ml in 
        LSend (n,((r,rr),lmm))
    | LRecv (n,((s,ss),ml)) -> 
        let lmm = List.map (function (l,lv,g)-> (l,lv,lappend cc g)) ml in 
        LRecv (n,((s,ss),lmm))
    | LPoll (n,((x,r),pl,g,c)) -> LPoll (n,((x,r),pl,g,lappend cc c))
    | LPar (n,(g,r,c)) -> LPar (n,(g,r,lappend cc c)) 
    | LRec (n,g) -> LRec (n,g) 
  in
  let rec aux = function 
    | LEnd n -> LEnd n 
    | LGoto n -> LGoto n 
    | LSend (n,((r,rr),ml)) ->
        let mll = List.map (function (l,lv,g)-> (l,lv,aux g)) ml in 
        LSend (n,((r,rr),mll))
    | LRecv (n,((s,ss),ml)) -> 
        let mll = List.map (function (l,lv,g)-> (l,lv,aux g)) ml in 
        LRecv (n,((s,ss),mll))
    | LPoll (n,((x,r),pl,LEnd _,c)) -> aux c
    | LPoll (n,((x,r),pl,g,c)) -> LPoll (n,((x,r),pl,aux g,aux c))
    | LPar (n,(LEnd _,LEnd _,c)) ->  aux c
    | LPar (n,(LEnd _,r,c)) -> lappend (aux c) (aux r)
    | LPar (n,(g,LEnd _,c)) -> lappend (aux c) (aux g)
    | LPar (n,(g,r,c)) -> LPar (n,(aux g,aux r,aux c)) 
    | LRec (n,g) -> LRec (n,aux g) 
  in
  let rec apply x =
    let xx = aux x in
    if x = xx then x else apply xx 
  in
  let ltypes =  List.map (function (r,t)->(r,apply t)) lt in
  let () = 
    List.iter (function (r,l) -> 
                 debug_wf ("Cleaned type for "^r^":\n"^sprint_lt l)) ltypes
  in
  ltypes
