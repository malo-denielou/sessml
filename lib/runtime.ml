(********************************************************************)
(* SessML - Runtime                                                 *)
(*                                                                  *)
(* runtime.ml                                                       *)
(********************************************************************)
(* Time-stamp: <Deniélou Malo - 2010> *)

open Unix

(**********************************)
(* Global constants and functions *)
(**********************************)

let debug_bool = ref true

let debug modul msg =
  if !debug_bool then begin
    print_string ("["^modul^"] ");
    print_string msg ;
    print_newline ();
    flush Pervasives.stdout
  end
  else ()

let debug = debug "Runtime"

let test_eq i j m =
  if i = j then ()
  else failwith m   

let test_inf i j m =
  if i < j then ()
  else failwith m   

(*********************)
(* List Manipulation *)
(*********************)

(* Substitution *)
let alias subst =
  function n ->
    if List.mem_assoc n subst 
    then List.assoc n subst
    else n

(* Remove duplicates in a list *)
let rec remove_duplicates l = 
  match  l with
      [] -> []
    | a::q -> if (List.mem a q) 
      then (remove_duplicates q) 
      else a::(remove_duplicates q)

(* Substraction *)
let rec substract l ll =
  let rec remove x = function
  [] -> []
    | a::q -> if a = x then remove x q else a::(remove x q) in
  match l with
      [] -> ll
    | a::q -> substract q (remove a ll)

(**********)
(* Base64 *)
(**********)

let char_table = 
  [|'A';'B';'C';'D';'E';'F';'G';'H';'I';'J';'K';'L';'M';'N';'O';'P';'Q';'R';'S';
    'T';'U';'V';'W';'X';'Y';'Z';'a';'b';'c';'d';'e';'f';'g';'h';'i';'j';'k';'l';
    'm';'n';'o';'p';'q';'r';'s';'t';'u';'v';'w';'x';'y';'z';'0';'1';'2';'3';'4';
    '5';'6';'7';'8';'9';'+';'/'|] 

let table_back c =
  match c with
    | 'a' .. 'z' -> Some (int_of_char c - 71)
    | 'A' .. 'Z' -> Some (int_of_char c - 65)
    | '0' .. '9' -> Some (int_of_char c + 4)
    | '+' -> Some (62)
    | '/' -> Some (63)
    | '=' -> None
    | _ -> assert false

let eq = '='
  
let base64 (s:string) =
  let size = 8*String.length s in
  let ssize = 
    (size / 24 ) * 4 + (if size mod 24 <> 0 then 4 else 0) in
  let res = String.create ssize in
  (*  let _ = Printf.printf "Taille : %i donc %i\n" size ssize in *)
  let rec encode p =
    if p*8 >= size then ()
    else
      let byte1 = int_of_char (s.[p]) in
      let bits1 = (byte1 / 4) in
      let _ = res.[p*8/6] <- (char_table.(bits1)) in
      if 8*p+8 >= size 
      then 
        let bits2 = (byte1 mod 4)*16 in
        let _ = res.[p*8/6+1] <- (char_table.(bits2)) in
        ()
      else
        let byte2 = int_of_char (s.[p+1]) in
        let bits2 = (byte1 mod 4)*16 + (byte2 / 16) in
        let _ = res.[p*8/6+1] <- (char_table.(bits2)) in
        if 8*p+16 >= size 
        then
          let bits3 = (byte2 mod 16)*4 in
          let _ = res.[p*8/6+2] <- (char_table.(bits3)) in
          ()
        else 
          let byte3 = int_of_char (s.[p+2]) in
          let bits3 = (byte2 mod 16)*4 + (byte3 / 64) in
          let bits4 = (byte3 mod 64) in
          let _ = res.[p*8/6+2] <- (char_table.(bits3)) in
          let _ = res.[p*8/6+3] <- (char_table.(bits4)) in
          encode (p+3)
  in
  (* filling the last bits with equals *)
  if size mod 24 <> 0 then 
    for i = ssize - 3 to ssize-1 do
      res.[i] <- eq
    done;
  encode 0 ;
  res

    
let ibase64 (s:string) =
  let size = String.length s in
  let ssize = size * 6 / 8 in
  let res = String.create ssize in
  
  let rec decode p =
    if p = size 
    then 0
    else
      let i = (p*6)/8 in
      let v1 = table_back s.[p] in
      let v2 = table_back s.[p+1] in
      let v3 = table_back s.[p+2] in
      let v4 = table_back s.[p+3] in
      match (v1,v2,v3,v4) with
        | Some a, Some b, Some c, Some d -> 
            (*            let _ = Printf.printf "Chars : %i %i %i %i\n" a b c d in
                          let _ = Printf.printf "donne : %i %i %i \n" (a * 4 + b / 16) ((b
                          mod 16)*16 + c / 4) ((c mod 4)*64 + d) in *)
          let _ = res.[i] <- char_of_int (a * 4 + b / 16) in
          let _ = res.[i+1] <- char_of_int ((b mod 16)*16 + c / 4) in
          let _ = res.[i+2] <- char_of_int ((c mod 4)*64 + d) in
          decode (p+4)
        | Some a, Some b, Some c, None ->
          let _ = res.[i] <- char_of_int (a * 4 + b / 16) in
          let _ = res.[i+1] <- char_of_int ((b mod 16)*16 + c / 4) in
          1
        | Some a, Some b, None, None ->
          let _ = res.[i] <- char_of_int (a * 4 + b / 16) in
            (*            let _ = res.[i+1] <- char_of_int (b mod 16) in *)
          2 
        | _ -> assert false
  in
  let i = decode 0 in
  String.sub res 0 (ssize-i)


(**********************************************)
(* String operations and message construction *)
(**********************************************)


let concat x y = 
  let cv i = (if i<10 then "000" else 
      (if i<100 then "00" else
	  (if i<1000 then "0" else "")))
    ^(string_of_int i) in
  let ret = 
    (cv (String.length x + String.length y))
    ^(cv (String.length x))
    ^x^y in
(*    Printf.printf "Concatenating %d + %d = %d\n" (String.length x) (String.length y) (String.length ret); *) ret

let iconcat z = 
  (*  Printf.printf "Attempting decat %d: " (String.length z);*)
  let total = int_of_string (String.sub z 0 4) in
  let shift = int_of_string (String.sub z 4 4) in
  (*  Printf.printf "shift: %d\n " (shift);*)
  let x1 = String.sub z 8 shift in
  let x2 = String.sub z (shift+8) (total-shift) in 
    (*    Printf.printf "success %d %d!\n" (String.length x1) (String.length x2);*)
  (x1,x2)
    
let concat3 x y z = concat x (concat y z)
let iconcat3 e = (let x,yz = iconcat e in let y,z = iconcat yz in x,y,z)

let concatlist l = 
  let n = List.length l in
  let rec aux = function
  [] -> ""
    | [a] -> a
    | a::q -> concat a (aux q)
  in
  concat (string_of_int n) (aux l)

let iconcatlist s =
  let ns,ls = iconcat s in
  let n = int_of_string ns in
  let rec aux s = function
    | 0 -> []
    | 1 -> [s]
    | n -> let a,q = iconcat s in a::(aux q (n-1))
  in
  aux ls n

type str = string

let cS (x:string) : str = x
let iS (x:str) : string = x


(**********************)
(* Principal database *)
(**********************)

type pr = {id:string; ip:string; port:int}

let addrDb : (string * (string * int)) list ref = ref []

let register (prin:pr) =
  debug ("Registering "^prin.id);
  if List.mem_assoc prin.id !addrDb
  then (if List.assoc prin.id !addrDb = (prin.ip,prin.port)
    then debug (prin.id^" already known") 
    else failwith ("Principal identity confusion in database"))
  else
    addrDb := (prin.id,(prin.ip,prin.port))::!addrDb

let reg_read idl =
  debug ("Updating database") ;
  let ls = iconcatlist idl in
  let l = List.map (fun s ->
    let (r,net) = iconcat s in
    let ip,pos = iconcat net in
    let po = int_of_string pos in
    {id=r;ip=ip;port=po}) ls in
  List.iter register l;
  debug ("Database updated") ;
  ()


let reg_write reg =
  let rec aux = function
    | [] -> []
    | (role,l)::q -> l@(aux q)
  in
  let l = remove_duplicates (aux reg) in
  let ls = List.map 
    (function id -> 
      let ip,po = List.assoc id !addrDb in
      concat id (concat ip (string_of_int po))
    ) l in
  concatlist ls

(* Local registry *)

let lreg_get reg role sub lv =
  let lv = List.map (alias sub) lv in
  let lp = List.assoc role reg in
  substract lv lp


(*****************)
(* Communication *)
(*****************)

let udp = ref (Unix.stderr)

let local = ref ("")

let bind prin =
  let (_,localport) = List.assoc prin (!addrDb) in
  debug ("Listening on port "^(string_of_int localport));
  udp := Unix.socket Unix.PF_INET Unix.SOCK_DGRAM 0;
  Unix.setsockopt !udp SO_REUSEADDR true;
  Unix.setsockopt_float !udp SO_RCVTIMEO 0.1;
  Unix.bind !udp (Unix.ADDR_INET (Unix.inet_addr_loopback, localport))

let close () = 
  Unix.close !udp

let netlock = Mutex.create ()

(* Low-level communication *)
let psend ?(verb=true) (dest:string) (text:str): unit = 
  Mutex.lock netlock;
  let (url,destport) = List.assoc dest !addrDb in
  let text = iS text in
  let udpSend = socket PF_INET SOCK_DGRAM 0 in
  let addr = inet_addr_of_string url in
  let _ = sendto udpSend text 0 (String.length text) [] (ADDR_INET(addr,destport)) in 
  let _ = Unix.close udpSend in
  if verb then debug ("sent to "^dest^":\n"^text) ;
  Mutex.unlock netlock;
  ()
    
let precv () : str =
  Mutex.lock netlock;
  let text = String.create 2056 in
   (*   let (len,_) = recvfrom udp text 0 1024 [] in *)
  let len = recv !udp text 0 2056 [] in
  debug ("received:\n"^text) ;
  Mutex.unlock netlock;
  cS (String.sub text 0 len)

let buildmsg session kind mnb srole sid rrole rid content =
  let sender = concat srole sid in
  let recver = concat rrole rid in
  let pid = concat sender recver in
  let mid = concat kind mnb in
  let header = concat3 session mid pid in
  concat header content


let sendAck session srole sid rrole rid mnb =
  let txt = buildmsg session "Ack" mnb srole sid rrole rid "" in
  debug ("Sending acknowlegement message") ;
  psend rid txt
    

(****************)
(* Runtime loop *)
(****************)

let runtime = ref None

let sendqueue = Queue.create ()
let cache = Hashtbl.create 10
let recvqueue = ref []
let ackwait = ref false
let ackpause = ref false
let acknumb = ref ""
let ackmesg = ref ("","")

let runtimeloop () = 
  debug ("Starting runtime loop") ;
  while true do
    Thread.yield ();
    if !ackwait || Queue.is_empty sendqueue 
    then (try begin (* Receive *)
      let m = precv () in (* What happens if there is no message? *)
      let header,body = iconcat m in
      let session,mid,pid = iconcat3 header in
      let kind,mnb = iconcat mid in
      let sender,recver = iconcat pid in
      let srole,sid = iconcat sender in
      let rrole,rid = iconcat recver in
      debug (Printf.sprintf "Received a %s message %s from %s:%s to %s:%s"
               kind mnb srole sid rrole rid);
      (match kind with
        | "Ack" -> (
          assert (mnb = !acknumb);
          ackwait:=false)
        | "Msg" -> (
          if Hashtbl.mem cache mnb
          then (if !ackwait then ()
            else (sendAck session rrole rid srole sid mnb)) 
          else ( (* If not already received *)
            sendAck session rrole rid srole sid mnb;
            Hashtbl.add cache mnb ();
            let lref = List.assoc session !recvqueue in
            let q = List.assoc rrole !lref in
            Queue.push (srole,sid,rrole,rid,body) q))
        | "Reg"-> (
          if Hashtbl.mem cache mnb
          then (
            sendAck session rrole rid srole sid mnb )
          else ( (* If not already received *)
            sendAck session rrole rid srole sid mnb;
            Hashtbl.add cache mnb ();
            let reg,idl = iconcat body in
            reg_read idl;
            let lref = List.assoc session !recvqueue in
            let q = List.assoc rrole !lref in
            (* If not already received *)
            (*            sendAck session srole sid rrole rid mnb;*)
            Queue.push (srole,sid,rrole,rid,reg) q)
        )
        | _ -> assert false);
      Thread.yield ()
    end with Unix_error (_,_,_) -> (
      Mutex.unlock netlock;
      if !ackwait then begin
        let (rid,txt) = !ackmesg in 
        debug ("Resending previous message") ;
        psend ~verb:false rid txt
      end else ()))
    else begin (* Send *)
      let (session,kind,srole,sid,rrole,rid,content) = Queue.pop sendqueue in
      let mnb = string_of_int (Random.bits ()) in
      let txt = buildmsg session kind mnb srole sid rrole rid content in
      let () = ackwait := true ; acknumb := mnb ; ackmesg := (rid,txt) in
      psend rid txt;
      debug ("Expecting an Ack") ;
    end;
    Thread.yield ();
  done


let start_runtime session role id =
  let lref = 
    if List.mem_assoc session !recvqueue
    then List.assoc session !recvqueue
    else (let l = ref [] in recvqueue := (session,l)::!recvqueue ; l)
  in
  let () = if List.mem_assoc role !lref
    then failwith "Role already locally running"
    else (bind id ; lref := (role,Queue.create ())::!lref)
  in
  if !runtime = None 
  then (
    Random.self_init ();
    runtime := Some (Thread.create runtimeloop ())
  )
  else ()

(*******)
(* API *)
(*******)

let sendMsg session srole sid rrole rid tag lt v sub =
  let lt = List.map (alias sub) lt in
  let stag = concat tag (concatlist lt) in
  let vs = Marshal.to_string v [] in
  let content = concat stag vs in
  Queue.push (session,"Msg",srole,sid,rrole,rid,content) sendqueue

let recvMsg session rrole tags =
  debug ("Waiting for reception") ;
  let lref = List.assoc session !recvqueue in
  let q = List.assoc rrole !lref in
  let wait = ref true in
  while !wait do
    while Queue.is_empty q do (Thread.yield ()) done;
                 (*    debug ("Tentative reception") ; *)
    let (srole,sid,rrole,rid,body) = Queue.peek q in
    let stag,vs = iconcat body in
    let tag,ls = iconcat stag in
(*    debug (Printf.sprintf "A message %s in the queue" tag) ;*)
    let lv = iconcatlist ls in
    if List.mem (tag,lv) tags
    then wait :=false
    else ();
    Thread.yield ()
  done;
  debug ("Reading received message") ;
  let (srole,sid,rrole,rid,body) = Queue.pop q in
  let stag,vs = iconcat body in
  let tag,ls = iconcat stag in
  (tag,vs)



let sendJoin session srole sid regid = 
  debug ("Sending join message") ;
  let ip,po = List.assoc sid !addrDb in
  let content = concat "Join" (concat sid (concat ip (string_of_int po))) in
  Queue.push (session,"Msg",srole,sid,"Adm",regid,content) sendqueue

let sendQuit session srole sid regid = 
  debug ("Sending quit message") ;
  let content = concat "Quit" sid in
  Queue.push (session,"Msg",srole,sid,"Adm",regid,content) sendqueue;
  Thread.delay(1.0) (* To be sure that the messages are through *)
 
let sendLock session srole sid regid = 
  debug ("Sending lock message") ;
  let content = concat "Lock" sid in
  Queue.push (session,"Msg",srole,sid,"Adm",regid,content) sendqueue;
  let (_,reg) = recvMsg session srole ["registryupdate",[]] in
  let ls = iconcatlist reg in
  let l = List.map 
    (fun x -> let role,pl = iconcat x in (role,iconcatlist pl)) ls in
  l

let sendUnlock session srole sid regid  = 
  debug ("Sending unlock message") ;
  let content = concat "Unlock" sid in
  Queue.push (session,"Msg",srole,sid,"Adm",regid,content) sendqueue

let sendReg session sid rrole rid reg =
  debug ("Sending registry message") ;
  let lr = List.map (function r,lp -> concat r (concatlist lp)) reg in
  let sreg = concatlist lr in
  let stag = concat "registryupdate" (concatlist []) in
  let content = concat stag sreg in
  let greg = reg_write reg in
  let body = concat content greg in
  Queue.push (session,"Reg","Adm",sid,rrole,rid,body) sendqueue
  
type admin = 
  | AdmJoin of string * string
  | AdmQuit of string * string
  | AdmLock of string * string
  | AdmUnlock of string * string

let recvAdm session =
  debug ("Waiting for Adm reception") ;
  let lref = List.assoc session !recvqueue in
  let q = List.assoc "Adm" !lref in
  while Queue.is_empty q do (Thread.yield ()) done;
  let (srole,sid,rrole,rid,body) = Queue.pop q in
  let tag,vs = iconcat body in
  debug (Printf.sprintf "An Adm message %s in the queue" tag) ;
  match tag with
    | "Join" -> AdmJoin(srole,sid)
    | "Quit" -> AdmQuit(srole,sid)
    | "Lock" -> AdmLock(srole,sid)
    | "Unlock" -> AdmUnlock(srole,sid)
    | _ -> assert false 

let join jq p = Queue.push ("Join",p) jq

let quit jq p = Queue.push ("Quit",p) jq

let lock locked locking reglock jq reg session id role rid reg = 
  if (not !locked)
  then begin
    if not !locking
    then (locking:=true;locked:=false;
          debug (Printf.sprintf "Starting a new iteration");
          Queue.iter 
            (function
               | ("Join",(r,p)) -> (
                 debug (Printf.sprintf "%s joins the session as %s" p r);
                 if List.mem_assoc r !reg
                 then (let l = List.assoc r !reg in
                       let rreg = List.remove_assoc r !reg in
                       reg:= (r,p::l)::rreg)
                                    (* Missing joining conditions [1] [*] *)
                 else (reg:= (r,[p])::!reg))
               | ("Quit",(r,p)) -> (
                 debug (Printf.sprintf "%s leaves the session as %s" p r);
                 let l = List.assoc r !reg in
                 let rreg = List.remove_assoc r !reg in
                 reg:= (r,List.filter (fun x->x<>p) l)::rreg)
               | _ -> assert false)
            jq;
          debug (Printf.sprintf "Session in a locking state");
          Queue.clear jq
         );
    reglock:=(role,rid)::!reglock;
    sendReg session id role rid !reg;
    if (List.for_all (fun (r,l) -> 
                        List.for_all (fun y -> 
                                        List.mem (r,y) !reglock) l) !reg)
    then (locked:=true ; locking:=false;
          debug (Printf.sprintf "Session in a locked state"))
    else (debug (Printf.sprintf "Session not yet locked"))
  end
  else
    (
      let lref = List.assoc session !recvqueue in
      let q = List.assoc "Adm" !lref in
      Queue.push (role,rid,"Adm",id,concat "Lock" rid) q
    )

let unlock locked locking reglock jq reg session id role rid reg = 
  if (!locked && not !locking)
  then begin
    reglock:= List.filter (fun x -> x <> (role,rid)) !reglock;
    if !reglock = []
    then (locked:=false;locking:=false;
          debug (Printf.sprintf "Session is not locked anymore"))
  end
  else begin
    let lref = List.assoc session !recvqueue in
    let q = List.assoc "Adm" !lref in
    Queue.push (role,rid,"Adm",id,concat "Unlock" rid) q
  end
  
  
  
