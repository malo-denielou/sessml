(********************************************************************)
(* SessML - Implementation                                          *)
(*                                                                  *)
(* generation.ml                                                    *)
(********************************************************************)
(* Time-stamp: <Pierre-Malo Denielou - 2010> *)

open Common
open Syntax 
open Graph

let debug = gen_debug debug_generation "gen"


(********************************************)
(*             Initial Part                 *)
(********************************************)

(********************************************)
(*         Global Helper Functions          *)
(********************************************)

let rec print_stategraph (g:stategraph) = 
  match g with
      [] -> ""
    | ((a,b),m,(a1,b1))::rest -> 
        (Printf.sprintf "(%s,%s),({%s}%s{%s}),(%s,%s))" 
           (print_state a)
           (print_state b)
            (String.concat "," m.write) 
            m.label
            (String.concat "," m.read) 
           (print_state a1)
           (print_state b1))
         ^(print_stategraph rest)

let global_def (g:stategraph) =
  "open Runtime\n"
(*  ^"open Base64\n" *)
  ^"open Data\n"
  ^"open Pi\n"
  ^"open Crypto\n"
  ^"open Prins\n\n"
  ^"let debug_impl = debug \"Impl\"\n\n" 
  ^"type principal = string\n"
  ^"\ntype mackey = bytes hkey\n"
  ^"let get_mackey (a:principal) (b:principal) = Prins.get_mackey (cS a) (cS b)\n"




(********************************************)
(*              Wired Part                  *)
(********************************************)

let seq_to_s seq = 
  let s = String.concat "_" (List.map (function (_,m,v) -> m.label) seq) in
  if s = "" then "start"
  else s

let rec vars_to_pats opt = function
    [] -> ""
  | [v] -> (capitalize v)^" "^v^opt
  | v::q -> (capitalize v)^" "^v^", "^(vars_to_pats opt q)

let rec vars_to_pats_light = function
    [] -> ""
  | [v] -> v
  | v::q -> v^", "^(vars_to_pats_light q)

let rec vars_to_type vl = function
    [] -> "unit"
  | [a] -> (List.assoc a vl)
  | a::q -> (List.assoc a vl)^" * "^(vars_to_type vl q)
 
(* Store management *)
let recreate_store hd lv lh lm lk =
  let rec vars = function
      [] -> ""
    | v::q -> " "^v^" = "^v^";"^(vars q)
  in
  let rec hashes = function
      [] -> ""
    | v::q -> " h"^v^" = h"^v^";"^(hashes q)
  in
  let rec macs = function
      [] -> ""
    | (role,m,vars,r)::q -> 
      let v = String.concat "" vars in
      " "^r^m.label^v^" = "^r^m.label^v^";"^(macs q)
  in
  let rec keys = function
      [] -> ""
    | (x,y)::q -> " key_"^x^y^" = key_"^x^y^";"^(keys q)
  in
  
  let v = if lv = [] then "" else ("\n      vars = {store.vars with"^(vars lv)^"};" )in
  let h = if lh = [] then "" else ("\n      hashes = {store.hashes with"^(hashes lh)^"};" )in
  let m = if lm = [] then "" else ("\n      macs = {store.macs with"^(macs lm)^"};") in
  let k = if lk = [] then "" else ("\n      keys = {store.keys with"^(keys lk)^"};" )in
  let t = if hd = [] then "" else 
    if hd = ["sid";"ts"] ||  hd = ["ts";"sid"] then ("\n      header = {"^(vars hd)^"}")
    else ("\n      header = {store.header with"^(vars hd)^"}")
  in
  if (lv = []) && (lh = []) && (lm = []) && (lk = []) && (hd = [])
  then ""
  else if (lv = []) || (lh = []) || (lm = []) || (lk = []) || (hd = [])
  then (
    "  let store = { store with "^(v)^(h)^(m)^(k)^(t)^"} in\n"
  )
  else (
  "  let store = { \n      vars = "^(v)^";\n      hashes = "^(h)^";\n      macs = "^(m)^"; \n      keys = "^(k)^"; \n      header = "^(t)^"} in\n"
    )
   

(* Marshalling and Unmarshalling *)   
let unmar_a_var vl v =
  match List.assoc v vl with
    | "string" -> 
        "  let string_"^v^" = iutf8 mar_"^v^" in\n"^
          "  let "^v^" = iS string_"^v^" in\n"
    | "int" -> 
        "  let string_"^v^" = iutf8 mar_"^v^" in\n"^
          "  let marred_"^v^" = iS string_"^v^" in\n"^
          "  let "^v^" = int_of_string marred_"^v^" in\n"
    | "principal" -> 
        "  let string_"^v^" = iutf8 mar_"^v^" in\n"^
          "  let "^v^" = iS string_"^v^" in\n"
    | _ -> assert false


let rec decr_vars send recv lr hl vl = function
    [] -> ""
  | v::q -> 
      if List.mem v lr then (decr_vars send recv lr hl vl q)
      else if List.mem v hl 
      then 
        ("  let mar_"^v^" = unpickle (sym_decrypt (get_symkey (cS store.vars."^send^") (cS store.vars."^recv^")) encr_"^v^") in\n"^
           (unmar_a_var vl v)^
           (decr_vars send recv lr hl vl q))
      else 
        ("  let key"^send^recv^" = get_symkey (cS store.vars."^send^") (cS store.vars."^recv^") in\n"^
           "  let mar_"^v^" = unpickle (sym_decrypt key"^send^recv^" encr_"^v^") in\n"^
           (unmar_a_var vl v)^
           "  let h"^v^" = sha1 mar_"^v^" in\n"
        )^(decr_vars send recv lr hl vl q)
        

let rec unmar_vars keys sender recver lr hl vl vars = 
  let getv x = if List.mem x vars then x  else "store.vars."^x in
  let unmarppalvariables =
    (String.concat "" 
       (List.map (fun v -> "  let mar_"^v^",variables = iconcat variables in\n"^
                    (unmar_a_var vl v)^
                    (if List.mem v hl then "" else
                       "  let h"^v^" = sha1 mar_"^v^" in\n")
                 )
          (List.rev (intersect lr vars)))) in
  let unmarvariables =
    (String.concat "" 
       (List.map (fun v -> "  let mar_"^v^",variables = iconcat variables in\n"^
                    (unmar_a_var vl v)^
                    "  let h"^v^" = sha1 mar_"^v^" in\n")
          (List.rev (substract lr vars)))) in
  let decryptvariables =
    "  let key"^sender^recver^" = get_symkey (cS "^getv sender^") (cS "^getv recver^") in\n"^
      "  let variables = unpickle (sym_decrypt key"^sender^recver^" variables) in\n" in
  (if unmarppalvariables = "" 
   then ""
   else  (
     "  (* Unmarshalling principal variables *)\n"^unmarppalvariables^
       (recreate_store [] (intersect lr vars) [] [] [])
   ))^keys^(
    if unmarvariables = ""
    then ""
    else (
     "  (* Decrypting variables *)\n"^
       decryptvariables^
       "  (* Unmarshalling variables *)\n"^
       unmarvariables
    )
  )
    
    
    
let mar_a_var vl prefix v =
  match List.assoc v vl with
  | "string" -> 
        "  let string_"^v^" = cS "^prefix^v^" in\n"^
          "  let mar_"^v^" = utf8 string_"^v^" in\n"
  | "int" -> 
        "  let marred_"^v^" = string_of_int "^prefix^v^" in\n"^
        "  let string_"^v^" = cS marred_"^v^" in\n"^
          "  let mar_"^v^" = utf8 string_"^v^" in\n"
  | "principal" -> 
        "  let string_"^v^" = cS "^prefix^v^" in\n"^
          "  let mar_"^v^" = utf8 string_"^v^" in\n"
  | _ -> assert false

let rec mar_vars sender recver lr vl vars = 
  if vars = [] then "  let variables = nil in\n"
  else (
    "  (* Marshalling variables *)\n"^
    "  let variables = nil in\n"^
      (String.concat "" 
         (List.map (fun v -> (mar_a_var vl "store.vars." v)^
	              "  let variables = concat mar_"^v^" variables in\n")
            (substract lr vars)))^
      "  let key"^sender^recver^" = get_symkey (cS store.vars."^sender^") (cS store.vars."^recver^") in\n"^
      "  let variables = sym_encrypt key"^sender^recver^" (pickle variables) in\n"^
      (String.concat "" 
         (List.map (fun v -> (mar_a_var vl "store.vars." v)^
	              "  let variables = concat mar_"^v^" variables in\n")
            (intersect lr vars)))
  )

let rec mar_hashes = function 
  | [] -> "  let hashes = nil in\n"
  | [v] -> "  (* Marshalling hashes *)\n"^
        "  let hashes = concat store.hashes.h"^v^" nil in\n"
  | v::q -> (mar_hashes q)^
      ("  let hashes = concat store.hashes.h"^v^" hashes in\n")

let rec unmar_hashes = function
  | [] -> ""
  | [v] -> ("  (* Unmarshalling hashes *)\n"^
              "  let h"^v^",_ = iconcat hashes in\n")
  | v::q -> ("  let h"^v^",hashes = iconcat hashes in\n")
      ^(unmar_hashes q)

let rec mar_macs = function
  | [] -> "  let macs = nil in\n"
  | (role,m,vars,r)::q -> 
      let v = String.concat "" vars in
      (mar_macs q)^
      ("  let macs = concat store.macs."^r^m.label^v^" macs in\n")

let rec unmar_macs = function 
    [] -> ""
  | [role,m,vars,r] -> 
      let v = String.concat "" vars in
      "  let "^r^m.label^v^",_ = iconcat macs in\n"
  | (role,m,vars,r)::q -> 
      let v = String.concat "" vars in
      ("  let "^r^m.label^v^",macs = iconcat macs in\n"^
        (unmar_macs q))


(* Creation of hashes and macs *)
let rec gen_hashes vl = function
    [] -> ""
  | v::q -> 
      ((mar_a_var vl "" v)^
         "  let h"^v^" = sha1 mar_"^v^" in\n")^(gen_hashes vl q)
       
let rec gen_macs vl st nextst role m = function 
  | [] -> ""
  | (r,v)::q -> 
      let va = String.concat "" v in
      "  (* Generation of a MAC from state "^(print_state st)^" to role "^r^" *)\n"^
	"  let content = content_"^(print_state nextst)^"_"^va^" store.header.ts store in\n"^
        "  let mackey"^role^r^" = get_mackey store.vars."^role^" store.vars."^r^" in\n"^
        "  let macmsg = mac mackey"^role^r^" (pickle content) in\n"^
        "  let "^r^m.label^va^" = concat header macmsg in\n"^
        (gen_macs vl st nextst role m q)


(* Verifications *)

let rec mac_verify first_recv role : (state * vars) list -> string = function 
    [] -> "  let _ = test_eq oldts store.header.ts \"Time-stamp verification\" in\n"
  | (s,v)::q -> 
      let (r,m,vars) = List.hd (snd s) in
      let va = String.concat "" v in
      "  (* Verification of a MAC from state "^(print_state s)^" with variables "^(va)^"*)\n"^
        "  let macheader,maccontent = iconcat store.macs."^role^m.label^va^" in\n"^
        "  let macsid,ts_mar = iconcat macheader in\n"^
        "  let ts_str = iutf8 ts_mar in\n"^
        "  let ts_string = iS ts_str in\n"^
        "  let ts = int_of_string ts_string in\n"^
        "  let _ = test_inf oldts ts \"MAC verification\" in\n"^
        "  let oldts = ts in\n"^
        "  let _ = test_eq macsid "^(if first_recv 
                                      then "sid" 
                                      else "store.header.sid")^" \"MAC verification\" in\n"^
        "  let mackey"^r^role^" = get_mackey store.vars."^r^" store.vars."^role^" in\n"^
        "  let content = mac_verify_"^role^"_"^(print_state s)^"_"^va^" ts store mackey"^r^role^" maccontent in\n"^
        (mac_verify first_recv role q)


let mac_fun (visib:visib) = 
  let mac_aux (st,l) =
    let rec unfold l =
      match l with
          [] -> []
        | (s,v)::q -> 
            let (r,m,vars) = List.hd (snd s) in
            let va = String.concat "" v in
            ("(* Verification of a MAC from role "^r^" at state "^(print_state s)^" with variables "^(va)^"*)\n"^
               "let mac_verify_"^(fst st)^"_"^(print_state s)^"_"^va^" ts store k m =\n"^
               "  let content = content_"^(print_state s)^"_"^va^" ts store in\n"^
               "  let cc = mac_verify k m content in\n"^
               "  let pc = pickle content in\n"^
               "  let _ = test_eq cc pc \"MAC incorrect\" in\n"^
               "  let up = unpickle cc in\n"^
               "  up\n")::
              (unfold q)
    in
    unfold (List.flatten l)
  in
  let mac_content (st,l) =
    let rec unfold l =
      match l with
          [] -> []
        | (s,v)::q -> 
            let va = String.concat "" v in
            let (r,m,vars) = List.hd (snd s) in
            ("(* Content of the MAC from role "^r^" at state "^(print_state s)^" with variables "^(va)^"*)\n"^
               "let content_"^(print_state s)^"_"^va^" ts store =\n"^
               "  let empty_str = cS \"\" in\n"^
               "  let nil = utf8 empty_str in\n"^
               (mar_hashes (v))^
               "  let nextstate = cS \""^(print_state s)^"\" in\n"^
               "  let nextstate_string = utf8 nextstate in\n"^
               "  let payload = concat nextstate_string hashes in\n"^
               "  let ts_string = string_of_int ts in\n"^
               "  let ts_str = cS ts_string in\n"^
               "  let ts_mar = utf8 ts_str in\n"^
               "  let header = concat store.header.sid ts_mar in\n"^
	       "  let content = concat header payload in\n"^
               "  content\n")::
              (unfold q)
    in
    unfold (List.flatten l)
  in
  (remove_duplicates (List.flatten (List.map mac_content visib)))@
  (remove_duplicates (List.flatten (List.map mac_aux visib)))


let rec var_verify vl = function
    [] -> "" 
  | v::q -> 
      (mar_a_var vl "" v)^
        "    let () = sha1_verify mar_"^v^" store.hashes.h"^v^" in\n"^
        (var_verify vl q) 


(* Keys *)

let rec mar_keys sender = function 
  | [] -> "  let keys = nil in\n"
  | (s,r)::q -> (mar_keys sender q)^
      if s = sender || r = sender then
        ("  let key_"^s^r^" = gen_keys (cS store.vars."^s^") (cS store.vars."^r^") in\n"^
           "  let keys = concat key_"^s^r^" keys in\n")
      else
        ("  let keys = concat store.keys.key_"^s^r^" keys in\n"
        )

(*
let rec mar_keys sender = function 
  | [] -> "  let keys = nil in\n"
  | [s,r] -> 
      "  (* Marshalling keys *)\n"^
      (if s = sender || r = sender then
         ("  let key"^s^r^" = gen_keys (cS store.vars."^s^") (cS store.vars."^r^") in\n"^
            "  let keys = concat key"^s^r^" nil in\n"^
            "  let keys = concat (gen_keys (cS store.vars."^r^") (cS store.vars."^s^")) keys in\n"  )
       else
         ("  let keys = concat store.keys.key_"^s^r^" nil in\n"
          ^"  let keys = concat store.keys.key_"^r^s^" keys in\n"))
  | (s,r)::q -> (mar_keys sender q)^
      if s = sender || r = sender then
        ("  let key"^s^r^" = gen_keys (cS store.vars."^s^") (cS store.vars."^r^") in\n"^
           "  let keys = concat key"^s^r^" keys in\n"^
           "  let keys = concat (gen_keys (cS store.vars."^r^") (cS store.vars."^s^")) keys in\n"  )
      else
        ("  let keys = concat store.keys.key_"^s^r^" keys in\n"
         ^"  let keys = concat store.keys.key_"^r^s^" keys in\n")
*)  
      
(*let rec unmar_keys role lk = 
  let rec aux = function
      [] -> assert false
    | [s,r] -> 
          "  let key_"^r^s^",keys = iconcat keys in\n"^
          "  let key_"^s^r^",_ = iconcat keys in\n"^
	  if role = s || role = r
          then ("  let () = reg_keys (cS "^r^") (cS "^s^") key_"^r^s^" in\n"^
	          "  let () = reg_keys (cS "^s^") (cS "^r^") key_"^s^r^" in\n")
          else ""
    | (s,r)::q -> 
        ( "  let key_"^r^s^",keys = iconcat keys in\n"^
            "  let key_"^s^r^",keys = iconcat keys in\n"^
	    (if role = s || role = r
             then (
	       "  let () = reg_keys (cS "^r^") (cS "^s^") key_"^r^s^" in\n"^
	         "  let () = reg_keys (cS "^s^") (cS "^r^") key_"^s^r^" in\n")
             else ""))^
          (aux q)
  in
  if lk = [] then "" else (
    "  (* Unmarshalling keys *)\n"^(aux lk)
  )*)

let rec unmar_keys role lk = 
  let rec aux = function
      [] -> assert false
    | [s,r] -> 
          "  let key_"^s^r^",_ = iconcat keys in\n"^
	  if role = s || role = r
          then ("  let () = reg_keys (cS store.vars."^s^") (cS store.vars."^r^") key_"^s^r^" in\n")
          else ""
    | (s,r)::q -> 
        ("  let key_"^s^r^",keys = iconcat keys in\n"^
	    (if role = s || role = r
             then (
	       "  let () = reg_keys (cS store.vars."^s^") (cS store.vars."^r^") key_"^s^r^" in\n")
             else ""))^
          (aux q)
  in
  if lk = [] then "" else (
    "  (* Unmarshalling keys *)\n"^(aux lk)
  )
       
(* Code Generation *)

let check_sid_ts flag role= 
  if flag then (
    "  let sid,ts_mar = iconcat header in\n"^
      "  let ts_str = iutf8 ts_mar in\n"^
      "  let ts_string = iS ts_str in\n"^
      "  let ts = int_of_string ts_string in\n"^
      "  let () = check_cache store.vars."^role^" \""^role^"\" sid in\n"^
      "  let oldts = store.header.ts in\n"^
      (recreate_store ["sid";"ts"] [] [] [] []) )
  else (
    "  let sid,ts_mar = iconcat header in\n"^
      "  let ts_str = iutf8 ts_mar in\n"^
      "  let ts_string = iS ts_str in\n"^
      "  let ts = int_of_string ts_string in\n"^
      "  let oldts = store.header.ts in\n"^
      "  let _ = test_inf oldts ts \"Replay attack!\" in\n"^
      "  let _ = test_eq store.header.sid sid \"Session confusion attack!\" in\n"^
      (recreate_store ["ts"] [] [] [] []))
    

let rec generate_wired_recv lr vl fut known visib fwd nextrecvg : state list -> string list = function 
    [] -> []
  | (state)::q -> 
      let fwdh,fwdm,fwdk = fwd in
      let recv = fst state in
      let lv = subset_assoc state visib in
      (*debug (Printf.sprintf "Generating wired recving of state %s "(print_seq state));*)
      let gen_recv vis =        String.concat "\n" 
        (List.map 
           (function v ->
              let ((send,seq),_) = List.hd v in
              let (_,m,_) = List.hd seq in
              let edge = List.assoc (state,m,(send,seq)) nextrecvg in
              let (sendst,sendnext),_,(_,recvnext) = edge in
              debug ("Looking at message "^m.label^" at position "^
                       (print_state_display state)^" going to "^(print_state_display recvnext));
              let recvvars = m.read in
              let recvhashes = safe_assoc edge fwdh in
              let recvmacs = List.sort 
                (function (_,m,_,_) -> (function (_,m',_,_) -> compare m m')) (safe_assoc edge fwdm) in
              let recvkeys = safe_assoc edge fwdk in
       
              let _,_,_ = List.assoc (state) known in
              let vars2,still,hashes2 = List.assoc (recvnext) known in
              let tocheck = intersect still m.read (*intersect (substract m.write m.read) hashes*) in
              let tostore = substract tocheck m.read in
              let learnthashes = substract tostore (substract still hashes2)
                (*substract tostore (substract (substract m.write hashes) hashes2)*)
              in 
              let () = debug (Printf.sprintf "Learning variables: direct %s | indirect %s" 
                                (String.concat "," tostore) (String.concat "," 
                                                           learnthashes)) in 
              let keys = (unmar_keys recv recvkeys) in
              let recvops =
                "  | \""^(print_vi v)^"\" ->\n"^
                  "  let variables,security = iconcat payload in\n"^
                  "  let keys,protocol = iconcat security in\n"^
                  "  let hashes,macs = iconcat protocol in\n"^
                (*  "  (* Unmarshalling variables *)\n"^
                    (unmar_vars send recv lr tocheck vl recvvars)^
                    (recreate_store [] (intersect recvvars lr) [] [] [])^ *)
                  (unmar_vars keys send recv lr tocheck vl recvvars)^
                  (var_verify vl tocheck)^
                  (recreate_store [] (substract lr recvvars) tostore [] recvkeys)^
                  (unmar_hashes recvhashes)^ 
                  "  (* Unmarshalling MACs *)\n"^
                  (unmar_macs recvmacs)^
                  (recreate_store [] [] recvhashes recvmacs [])^
                  (mac_verify (snd state=[]) recv (List.rev v))^ 
                  "  (* Verification Ended *)\n"^
                  (Printf.sprintf  "    let wired = Wired_in_%s_of_%s((%s),store) in\n    wired"
                     (print_state state)
                     (print_vi v)
                     (String.concat "," recvvars))   
              in
              recvops )
           vis)
      in
      let binding1 = "  let empty_str = cS \"\" in\n" in
      let binding2 = "  let nil = utf8 empty_str in\n" in
      let recvprin = "  let msg = precv  store.vars."^recv^" in\n" in
      let sep = 
	"  let header,content = iconcat (ibase64 msg) in\n" in
      let check =
      check_sid_ts (snd state=[]) recv (* pass flag telling whether its first message or nor *)
      in
      let tags = "  let tag,payload = iconcat content in\n" in
      (Printf.sprintf "\nlet receiveWired_%s (store:store) : wired_%s = \n%s%s%s%s%s%s  match iS (iutf8 tag) with"
          (print_state state)
          (print_state state)
          binding1
          binding2
          recvprin
          sep
	  check
          tags
      )
      ::(String.concat "\n" (List.map gen_recv lv))
      ::("  | _ -> failwith \"Critical Error\"\n")
      :: (generate_wired_recv lr vl fut known visib fwd nextrecvg q)


let rec generate_wired_send lr vl antivisib fut fwd = function
    [] -> []
  | (((sendst,sendnext),m,(recvst,recvnext)) as e)::q -> 
      (*debug (Printf.sprintf "Generating wired sending of message %s " m.label);*)
      let send = fst sendst in
      let recv,recvseq = recvst in
      let fwdh,fwdm,fwdk = fwd in
      let sentvars = m.read in
      let senthashes = safe_assoc e fwdh in
      let sentmacs = List.sort 
                (function (_,m,_,_) -> (function (_,m',_,_) -> compare m m')) (safe_assoc e fwdm) in
      let sentkeys = safe_assoc e fwdk in
      let macto = List.assoc (m,sendst) fut in
      let lm = List.map (function r,v -> (send,m,v,r)) macto in
      let v = List.hd (subset_assoc e antivisib) in 
      (* let v = (hist_to_visib recv
         (snd recvnext)) in *)
      let fstcomment = Printf.sprintf "(* Sending message from %s to %s *)\n"
        (send) (recv) in
      let sndcomment = Printf.sprintf "(* Message has to be MACed for %s *)\n"
        (String.concat " " (List.map (function a,b -> a) macto)) in
      let sendops = 
        (gen_hashes vl m.write)^ (* Hash writen vars *)
          "  let ts = store.header.ts + 1 in\n"^
          (recreate_store ["ts"] m.write m.write [] [])^(* Update store *)
          "  let ts_string = string_of_int store.header.ts in\n"^
          "  let ts_str = cS ts_string in\n"^
          "  let ts_mar = utf8 ts_str in\n"^
          "  let header = concat store.header.sid ts_mar in\n"^
          (mar_keys send sentkeys)^
          (gen_macs vl sendst sendnext send m macto)^
          (recreate_store [] [] [] lm [])^
          (mar_macs sentmacs)^
          (mar_hashes senthashes)^
          (mar_vars send recv lr vl sentvars)^ 
          "  let protocol = concat hashes macs in\n"^
          "  let security = concat keys protocol in\n"^
          "  let payload = concat variables security in\n"^
          "  let visib = cS \""^(print_vi v)^"\" in\n"^
          "  let visib_string = utf8 visib in\n"^
          "  let content = concat visib_string payload in\n"^
          "  let msg = base64 (concat header content) in\n"^
          "  let () = psend  store.vars."^recv^" msg in "^
          "" in
      let binding1 = "  let empty_str = cS \"\" in\n" in
      let binding2 = "  let nil = utf8 empty_str in\n" in
      (Printf.sprintf "%s%slet sendWired_%s_%s%s store =\n%s%s%s\n  store \n"
         fstcomment
         sndcomment
         m.label
         (print_state sendst)
         (String.concat "" (List.map (fun x-> " "^x) m.write))
         (*(vars_to_type vl m.write)*)
         binding1
         binding2
         sendops
      )
      :: (generate_wired_send lr vl antivisib fut fwd q)


let generate_wired lr vl (visib:visib) antivisib (fut:future) (known:known) (fwd:fwd) (stategraph:stategraph) =
  let states = remove_duplicates (List.map fst visib) in
  let nextrecvg = List.map (function ((d,e),b,(a,c)) -> ((a,b,e),((d,e),b,(a,c)))) stategraph in
  "\n(*******************************************)
(* Wired types, send and receive functions *)
(*******************************************)\n\n"^
    (String.concat "\n" (mac_fun visib))^
    "\n\n"^
    (String.concat "\n" (Geninterface.generate_wired_type vl visib states))^
    "\n\n"^
    String.concat "\n" (remove_duplicates (generate_wired_recv lr vl fut known visib fwd nextrecvg states))^ 
    "\n\n" ^
    String.concat "\n" (remove_duplicates (generate_wired_send lr vl antivisib fut fwd stategraph))^ 
    "\n\n"
  


(********************************************)
(*           Proxy generation               *)
(********************************************)
(* String generation *)

(*let gen_handler_name s = Printf.sprintf "handlers.h%s newSt.prins " s*)

let gen_handler_name s = Printf.sprintf "handlers.h%s" s
let crypto_params3 = "newSt"
let crypto_params3_recv = "newSt"

(* Sending operations *)
let crypto_params = " (st:store)"
let crypto_params_recv = " (st:store)"
let crypto_wired = "st"
let crypto_wired_init_recv = "prin "


(*------------------*)
(* Proxy generation *)
(*------------------*)



let rec gen_proxy_send sn sg_recv = function
    [] -> []
  | (s,lm)::q ->
      let role = fst s in
      let rec gen_pattern s = function
          [] -> ""
        | (m,ss)::q -> 
            (*debug (Printf.sprintf "Message %s" m.label);*)
            let conting = List.mem_assoc ss sg_recv in
            let state = if conting then "newSt" else "_" in
            let cont = 
              if conting 
              then Printf.sprintf "%s newSt next" (print_state ss)  
              else "next" 
            in 
            let assume =
              if m.write = [] then ""
              else ","^(String.concat "," m.write) 
            in
            let myself = if List.mem role m.write then role else "st.vars."^role in
            (Printf.sprintf "  | %s(%snext) ->\n%s    let %s = sendWired_%s_%s %sst in\n    %s\n"
               (m.label) 
               (vars_to_pats "," m.write)
               (Printf.sprintf 
                  "    let ts1 = st.header.ts+1 in\n    let () = assume (Send_%s(%s,st.header.sid,ts1%s)) in\n"
                  m.label myself assume)
               state
               (m.label)
               (print_state s)
               (String.concat "" (List.map (fun x -> x^" ") m.write))
               cont)
            ^(gen_pattern s q)
      in
      let n = 
        if List.mem_assoc s sn 
        then List.assoc s sn  
        else (debug (Printf.sprintf "Error at point %s" (print_state s));assert false) 
      in 
      ((Printf.sprintf "%s (st:store) (msg:%s) : %s = match msg with\n" 
            (print_state s) 
            (Geninterface.gen_typename n) 
            (Geninterface.gen_result_type role))^         
         (gen_pattern s lm))
      ::(gen_proxy_send sn sg_recv q)
        

let rec gen_proxy_recv2 visib sn sg_send sg_sendnext = function
    [] -> []
  | state::q ->
      let role = fst state in
      let lv = List.assoc state visib in
      let rec gen_pattern = function
          [] -> ""
        | v::q -> 
            (*debug (Printf.sprintf "Message %s" m.label);*)
            let (senderst,_) = List.hd v in
            let edge = List.assoc senderst sg_sendnext in
            let _,m,(_,rr) = edge in
            let conting = List.mem_assoc rr sg_send in
            let cont = 
              if conting 
              then Printf.sprintf "%s %s next" (print_state rr) crypto_params3 
              else "next" 
            in 
            let assume =
              if m.read = [] then ""
              else ","^(String.concat "," (List.map (fun x -> "newSt.vars."^x) m.read))
            in
            (Printf.sprintf "  | Wired_in_%s_of_%s ((%s), newSt) ->\n%s    let next = %s (%s) in\n    %s\n"
               (print_state state (*m.label*) )
               (print_vi v) 
               (vars_to_pats_light m.read)
               (Printf.sprintf 
                     "    let () = assume (Recv_%s(newSt.vars.%s,newSt.header.sid,newSt.header.ts%s)) in\n"
                     m.label role assume)
               (gen_handler_name m.label)
               (vars_to_pats "" m.read)
               cont)
            ^(gen_pattern q)
      in
      let n = 
        if List.mem_assoc state sn 
        then List.assoc state sn
        else (debug (Printf.sprintf "Error at point %s" (print_state state));assert false) 
      in 
      ((Printf.sprintf "%s (st:store) (handlers:%s) : %s =\n  let r = receiveWired_%s %s in\n  match r with\n" 
          (print_state state)
          (Geninterface.gen_typename n) 
          (Geninterface.gen_result_type role)
          (print_state state) 
	  (crypto_wired))^
         (gen_pattern lv))
      ::(gen_proxy_recv2 visib sn sg_send sg_sendnext q)

let proxy_functions (role:string) (visib:visib) (state_to_node:state_node) (sg:stategraph): string list =
  let sg_recv = List.map (function (_,m,(p,pp))-> p,(m,pp)) sg in
  let sg_recv = List.filter (function (r,_),_ -> r = role) sg_recv in
  let sg_send = List.map (function ((s,ss),m,_)->s,(m,ss)) sg in
  let sg_send = List.filter (function (r,_),_ -> r = role) sg_send in
  let send_states = remove_duplicates (List.map (function (_,s),_ -> s) sg_send) in
  let send_sorted = 
    List.map (function s -> (role,s),remove_duplicates (subset_assoc (role,s) sg_send)) send_states in
  let recv_states = remove_duplicates (List.map fst sg_recv) in
(*  let recv_sorted = 
    List.map (function s -> (role,s),remove_duplicates (subset_assoc (role,s)
    sg_recv)) recv_states in *)

  let sg_sendnext = List.map (function ((s,ss),m,r)->ss,((s,ss),m,r)) sg in

  (gen_proxy_send state_to_node sg_recv send_sorted)
  @(gen_proxy_recv2 visib state_to_node sg_send sg_sendnext recv_states)
(*
  List.flatten (List.map (gen_proxy loc sg_send sg_recv visib v role) l)
*)


(* Pretty printing functions *)
let rec gen_rec_fun : (string*string) list -> string = function
    [] -> ""
  | [(s1,s2)] -> Printf.sprintf "(* %s *)\nlet rec %s" s1 s2
  | (s1,s2)::q -> (gen_rec_fun q)^"(* "^s1^" *)\nand "^s2


let rec gen_rec_fun2 : string list -> string = function
    [] -> ""
  | [s] -> Printf.sprintf "let rec %s" s
  | (s)::q -> (gen_rec_fun2 q)^"and "^s



(*----------------------*)
(* First and last lines *)

let gen_user_inputs (l:role_type list) : string =
  match l with
      [] -> assert false
    | (Send (n,_ ))::_-> Printf.sprintf "(user_input: %s) " ((Geninterface.gen_typename n))
    | (Receive (n,_))::_-> Printf.sprintf "(user_input: %s) " ((Geninterface.gen_typename n))
    | _ -> assert false


let gen_empty_store (varlist:varlist) (rl:role_list) (fut:future) (*(rt:role_type)*) = 
  let def role n = function
    | "principal" -> (if n=role then "role" else "\"\"") 
    | "string" -> "\"\"" 
    | "int" -> "0"
    | _ -> assert false in
  let var role = String.concat ";"
    (List.map (function (n,t) -> Printf.sprintf " %s = %s" n (def role n t)) varlist) in
  let hashes = String.concat ";"
    (List.map (function (n,t) -> Printf.sprintf " h%s = utf8 (cS \"\")" n) varlist) in
  let macs = remove_duplicates
    (List.flatten 
       (List.map 
          (function ((m,a),l) -> 
             List.map 
               (function (r,v) -> r^m.label^(String.concat "" v)) l) fut))  in
  let macs = 
    String.concat "; " (List.map (function s -> s^" = utf8 (cS \"\")") macs) in 
  let roles = List.map (function (r,_,_) -> r) rl in
  let pairs = List.filter (function (x,y) -> x<>y) (product roles roles) in
  let keys = String.concat ";\n            " 
    (List.map (function (x,y)-> "key_"^x^y^" = utf8 (cS \"\")") pairs) in
  let header = 
    " sid = if starting then sha1 (concat (mkNonce()) session) else utf8 (cS \"\"); ts = 0 "
(*    if Geninterface.first_send rt then
    else
      " sid = utf8 (cS \"\"); ts = 0 " *)
  in 
  String.concat ""
    (List.map (fun role ->
                 "\nlet empty_store_"^role^" role starting = \n"^
                   "  {vars = {"^(var role)^"};\n"^
                   "   hashes = {"^hashes^"};\n"^
                   "   macs = { "^macs^"};\n"^
                   "   keys = { "^keys^"};\n"^
                   "   header = {"^header^"} }\n") roles)


let crypto_first_line = " (prins: principals) "
let crypto_first_line_recv = " (prin: principal) "

let first_line role (state_to_node:state_node) = 
  let i = List.assoc (role,[]) state_to_node in
  Printf.sprintf "(host:principal) (user_input:msg%d)" i
  
let crypto_last_line c= 
  "  let empty_store = empty_store_"^c^" host true in\n"^(*gen_empty_store "" vl rl fut rt*)
    "  let () = bind host in\n"^
    "  debug_impl (\"Executing role "^c^" ...\");\n"^
    "  let result ="

let crypto_last_line_recv c = 
  "  let empty_store = empty_store_"^c^" host false in\n"^(*gen_empty_store c vl rl fut rt)^" in\n"^*)
    "  let () = bind host in\n"^
    "  debug_impl (\"Executing role "^c^" ...\");\n"^
    "  let result ="

let last_line rl vl fut (role:string) (r:role_type) = 
  if Geninterface.first_send r
  then
    (Printf.sprintf "%s %s_start empty_store user_input in (*close();*)\n  result\n"
       (crypto_last_line role)
       role)
  else
    (Printf.sprintf "%s %s_start empty_store user_input in (*close();*)\n  result\n" 
       (crypto_last_line_recv role)
       role)
(* Function generation complete *)

let generate_functions2  (role:string) (visib:visib) (fut:future) (state_to_node:state_node) (stategraph:stategraph)
    (rl:role_list) (vl:varlist)  (rt:role_type) = 
  Printf.sprintf "%s\n\nlet %s %s =\n%s"
    (gen_rec_fun2 (proxy_functions role visib state_to_node stategraph))
    role
    (first_line role state_to_node)
    (last_line rl vl fut role rt)


(********************************************)
(*           Complete generation            *)
(********************************************)


let generate_from_role (rl:role_list) (vl:varlist) (visib:visib) (fut:future)
    (state_to_node:state_node) (stategraph:stategraph) (role_name:string)
    (typ:string) (role:role_type) : string = 
  let flatten_session = flatten role in
  (Printf.sprintf "\n(* Proxy function for %s *)\n" role_name)^
    (Printf.sprintf "\ntype %s = %s\n" (Geninterface.gen_result_type role_name) typ)^
    (Geninterface.gen_types "" role_name (List.rev flatten_session))^"\n"^
    (generate_functions2 role_name visib fut state_to_node stategraph rl vl role)
      
let rec generate_from_session (visib:visib) (fut:future) (state_to_node:state_node) (stategraph:stategraph) (s:role_list)
    (rl:role_list) (vl:varlist) : string = 
  match s with
    [] -> ""
  | (str,typ,rol)::q -> 
      let () = debug (Printf.sprintf "Generating code for role %s" str) in
      let g : string = (generate_from_role rl vl visib fut state_to_node stategraph str typ rol) in
      let () = debug (Printf.sprintf "Generation done for role %s" str) in
      (g^(generate_from_session visib fut state_to_node stategraph q rl vl))



let generate_proxy (session_name:string) (g:graph) (s:session) (visib:visib)
    (fut:future) (state_to_node:state_node) (stategraph:stategraph) : string =
  match s with Global _ -> failwith "Unsupported"
    | Local (vl,tl,rl) ->
  let lr = List.map (function (r,_,_) -> r) rl in
  let vl = (List.map (function r -> (r,"principal")) lr)@vl in
  let res = 
    ("\n(*******************)\n(* Proxy functions *)\n(*******************)\n\n")
    ^("\n\nopen Global\nopen Pi\nopen Crypto\nopen Data\nopen Prins\nopen "^session_name^"_protocol\n\n")
    ^"let debug_impl = debug \"impl\"\n\n" 
    ^(Geninterface.create_var_i vl)
    ^(generate_from_session visib fut state_to_node stategraph rl rl vl) 
  in
  let () = debug "Generation of the proxy module done!" in
  res
   
let generate_code (s:session) (g:graph) (visib:visib) antivisib (fut:future)
    (known:known) (fwd:fwd) (state_to_node:state_node) (stategraph:stategraph) 
    : string = 
  match s with Global _ -> failwith "Unsupported"
    | Local (vl,tl,rl) ->
  let lr = List.map (function (r,_,_) -> r) rl in
  let vl = (List.map (function r -> (r,"principal")) lr)@vl in
  let () = debug "Generation of the global definitions" in
  let s_global = (global_def stategraph) in
  let () = debug "Generation of the session id" in
  let s_stateg = (print_stategraph stategraph) in
  let () = debug "Generation of the principal records" in
  let s_interf = (Geninterface.gen_prins vl rl fut) in
  let () = debug "Generation of the store definitions" in
  let s_emptst = (gen_empty_store vl rl fut) in
  let () = debug "Generation of the events definition" in
  let s_events = (Geninterface.genEvents vl g stategraph) in
  let () = debug "Generation of the wired functions" in
  let s_wired  = (generate_wired lr vl visib antivisib fut known fwd stategraph)
    in
  let res = 
    s_global
    ^"let session = sha1 (utf8 (cS\""
    ^ s_stateg^"\"))\n\n"
    ^ s_interf 
    ^ s_emptst
    ^ s_events^"\n\n"
    ^ s_wired
(*    ^("\n(*******************)\n(* Proxy functions *)\n(*******************)\n\n")
    ^(generate_from_session visib fut state_to_node stategraph rl rl vl) *)
  in
  let () = debug "Generation of the module done!" in
  res
   

(********************************************)
(*              SessML Part                 *)
(********************************************)

let lgen_header (sname:string) (g:global_type) = 
  ("(* "^sname^" module *)\n")
  ^"open Runtime\n\n"
    (* ^"open Global\n" ^"open Data\n" ^"open Pi\n" ^"open Crypto\n" ^"open
       Prins\n\n" *)
  ^"let debug_impl = debug \"Impl\"\n\n"
  ^"type principal = string\n\n"
  ^"let session = (* sha1 *) (cS \""
  ^(sprint_gt g)^"\")\n\n"

let lgen_nextrole role = function
  | LEnd n -> "()"
  | x -> Printf.sprintf "%s_%d reg sub x" role (node_of_local x)

let rec lgen_fun_local role next = function
  | LSend (n,((r,rr),ml)) -> 
      (Printf.sprintf " %s_%d reg sub (x:%s_%d) = match x with\n   %s"
         role (fst n) role (fst n) 
         (String.concat "\n | " 
            (List.map (function ((c,t),lv,g)-> 
                         Printf.sprintf 
                           "%s (v,x) -> sendMsg session \"%s\" id \"%s\" (alias sub \"%s\") \"%s\" [%s] v sub ; %s "
                           c role rr r c (String.concat ";" lv)
                           (lgen_nextrole role g)) ml)))::
        (List.flatten 
           (List.map (function ((c,t),lv,l)-> lgen_fun_local role next l) ml))
  | LRecv (n,((s,ss),ml)) -> 
      (Printf.sprintf 
         " %s_%d reg sub (x:%s_%d) = \n  let tags = [%s] in\n  let m = recvMsg session \"%s\" tags in\n  %s%s"
         role (fst n) role (fst n)
         (String.concat ";" 
            (List.map 
               (function ((c,_),lv,_)-> 
                  Printf.sprintf "(\"%s\",(List.map (alias sub) [%s]))"
                    c (String.concat ";" (List.map (fun x -> "\""^x^"\"")
                                            lv))) ml))
         role
         "match m with\n   "
         (String.concat "\n | " 
            (List.map 
               (function ((c,t),lv,g)-> 
                  Printf.sprintf 
                    "(\"%s\",v) -> \n     let v:%s = Marshal.from_string v 0 in %s%s" 
                    c 
                    t (*lv*) 
                    (Printf.sprintf "let x = x.h%s v in " c)
                    (lgen_nextrole role g)) ml)))::
        (List.flatten 
           (List.map (function ((c,t),lv,l)-> lgen_fun_local role next l) ml))
  | LPoll (n,((x,r),pl,g,c)) -> 
      ((Printf.sprintf " %s_%d reg sub (x:%s_%d) = \n   let (g,c) = x in\n   "
          role (fst n) role (fst n))
       ^(Printf.sprintf "let lt = List.map (fun y -> \n       Thread.create (fun ()-> \n          let sub = (\"%s\",y)::sub in \n          let x = g(y) in %s) ())\n      (lreg_get reg \"%s\" sub [%s]) in\n   "
           x (lgen_nextrole role g) r 
           (String.concat ";" (List.map (fun x -> "\""^x^"\"") pl)))
       ^("let () = List.iter (fun t -> Thread.join t) lt in\n   ")
       ^(Printf.sprintf "let x = c () in %s"
           (lgen_nextrole role c)))::
        (lgen_fun_local role (Some (node_of_local c)) g)@(lgen_fun_local role next c)
  | LPar (n,(g,d,c)) -> 
      ((Printf.sprintf " %s_%d reg sub (x:%s_%d) = \n   let (g,d,c) = x in\n   "
          role (fst n) role (fst n))
       ^(Printf.sprintf "let t1 = Thread.create (fun() -> let x = g() in %s) () in\n   "
           (lgen_nextrole role g))
       ^(Printf.sprintf "let t2 = Thread.create (fun() s-> let x = d() in %s) () in\n   "
           (lgen_nextrole role d))
       ^(Printf.sprintf "let () = Thread.join t1 ; Thread.join t2 in\n   let x = c () in %s"
           (lgen_nextrole role c)))::
        (lgen_fun_local role (Some (node_of_local c)) g)@
        (lgen_fun_local role (Some (node_of_local c)) d)@
        (lgen_fun_local role next c)
  | LRec (n,g) -> 
      (Printf.sprintf " %s_start (x:%s_start) = \n   sendJoin session \"%s\" id registry ;\n   let reg = sendLock session \"%s\" id registry in\n   %s_%d reg [\"%s\",id] x "
         role role role role role (node_of_local g) role )::
        (Printf.sprintf " %s_%d reg sub (x:%s_%d) = \n   sendUnlock session \"%s\" id registry;\n   match x with \n   Continue_as_%s x -> let reg = sendLock session \"%s\" id registry in %s\n | Quit_as_%s x -> sendQuit session \"%s\" id registry ; x"
           role (fst n) role (fst n) role role role
           (lgen_nextrole role g) role role)::
        (lgen_fun_local role next g)
  | LEnd n -> []
  | LGoto n -> []

let lgen_fun name rt local =
  Printf.sprintf "let %s registry id (x:%s_start) =\n%s"
    name name
    (" let rec"
     ^(String.concat "\n and" (lgen_fun_local name None local))
     ^"\n in\n "
     ^"start_runtime session \""^name^"\" id ; "
     ^name^"_start x")
    
let lgen_from_role name rt local =
  (Printf.sprintf "(* -- %s API -- *)\n" name)
  ^(Geninterface.lgen_types name rt local)^"\n"
  ^(lgen_fun name rt local)^"\n\n"

let rec lgen_roles rl lt = match rl,lt with
    [],[] -> ""
  | (name,rk,rt)::rl,(n,local)::lt when n=name -> 
      let () = debug (Printf.sprintf "Generating code for role %s" name) in
      let g : string = (lgen_from_role name rt local) in
      let () = debug (Printf.sprintf "Generation done for role %s" name) in
      (g^(lgen_roles rl lt))
  | _,_ -> assert false

let lgen_initjoin (name,kind,_) =
  Printf.sprintf "\n  | AdmJoin(\"%s\",rid) -> %s"
    name
    (Printf.sprintf "join jq (\"%s\",rid)" name)
let lgen_initquit (name,kind,_) =
  Printf.sprintf "\n  | AdmQuit(\"%s\",rid) -> %s"
    name
    (Printf.sprintf "quit jq (\"%s\",rid)" name)
let lgen_initlock (name,kind,_) =
  Printf.sprintf "\n  | AdmLock(\"%s\",rid) -> %s"
    name
    (Printf.sprintf "lock locked locking reglock jq reg session id \"%s\" rid reg" name)
let lgen_initunlock (name,kind,_) =
  Printf.sprintf "\n  | AdmUnlock(\"%s\",rid) -> %s"
    name
    (Printf.sprintf "unlock locked locking reglock jq reg session id \"%s\" rid reg" name)
  

let lgen_init rl =
  Printf.sprintf "%s\nlet registry id =\n%s%s%s%sdone\n\n"
    ("(* -- Registry implementation -- *)\n")
    " start_runtime session \"Adm\" id ;\n"
    (" let reg = ref [] in\n"
     ^" let reglock = ref [] in\n"
     ^" let jq = Queue.create () in\n"
     ^" let locked = ref false in\n"
     ^" let locking = ref false in\n")
    " while true do\n"
    ("  let m = recvAdm session in\n"
     ^"  match m with"
     ^(String.concat "" (List.map lgen_initjoin rl))
     ^(String.concat "" (List.map lgen_initquit rl))
     ^(String.concat "" (List.map lgen_initlock rl))
     ^(String.concat "" (List.map lgen_initunlock rl))
     ^"\n  | _ -> assert false\n")


let generate_localcode (sname:string) (g:global_type) (rl:roles_list)
    (lt:(string*local_type) list) = 
  let () = debug "Generation of the global definitions" in
  let s_header = (lgen_header sname g) in
  let s_init = (lgen_init rl) in
  let s_roles = (lgen_roles rl lt) in 
  let res = 
    s_header
    ^ s_init
    ^ s_roles
  in
  let () = debug "Generation of the module done!" in
  res


