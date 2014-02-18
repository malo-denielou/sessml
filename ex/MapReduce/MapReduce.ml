(* MapReduce module *)
open Runtime

let debug_impl = debug "Impl"

type principal = string

let session = (* sha1 *) (cS "<0>{<7>client->control(Task(int).(<1>Poll(x:cluster|).(<5>control->x:cluster(Map(int).(<3>x:cluster->control(Reduce(int).(<4>End)))));Goto[0]))} ")

(* -- Registry implementation -- *)

let registry id =
 start_runtime session "Adm" id ;
 let reg = ref [] in
 let reglock = ref [] in
 let jq = Queue.create () in
 let locked = ref false in
 let locking = ref false in
 while true do
  let m = recvAdm session in
  match m with
  | AdmJoin("client",rid) -> join jq ("client",rid)
  | AdmJoin("control",rid) -> join jq ("control",rid)
  | AdmJoin("cluster",rid) -> join jq ("cluster",rid)
  | AdmQuit("client",rid) -> quit jq ("client",rid)
  | AdmQuit("control",rid) -> quit jq ("control",rid)
  | AdmQuit("cluster",rid) -> quit jq ("cluster",rid)
  | AdmLock("client",rid) -> lock locked locking reglock jq reg session id "client" rid reg
  | AdmLock("control",rid) -> lock locked locking reglock jq reg session id "control" rid reg
  | AdmLock("cluster",rid) -> lock locked locking reglock jq reg session id "cluster" rid reg
  | AdmUnlock("client",rid) -> unlock locked locking reglock jq reg session id "client" rid reg
  | AdmUnlock("control",rid) -> unlock locked locking reglock jq reg session id "control" rid reg
  | AdmUnlock("cluster",rid) -> unlock locked locking reglock jq reg session id "cluster" rid reg
  | _ -> assert false
done

(* -- client API -- *)

type result_client = int

type client_start = client_2 
and  client_0 = Continue_as_client of client_2 | Quit_as_client of result_client
and  client_2 = Task of int * client_0

let client registry id (x:client_start) =
 let rec client_start (x:client_start) = 
   sendJoin session "client" id registry ;
   let reg = sendLock session "client" id registry in
   client_2 reg ["client",id] x 
 and client_0 reg sub (x:client_0) = 
   sendUnlock session "client" id registry;
   match x with 
   Continue_as_client x -> let reg = sendLock session "client" id registry in client_2 reg sub x
 | Quit_as_client x -> sendQuit session "client" id registry ; x
 and client_2 reg sub (x:client_2) = match x with
   Task (v,x) -> sendMsg session "client" id "control" (alias sub "control") "Task" [] v sub ; client_0 reg sub x 
 in
 start_runtime session "client" id ; client_start x

(* -- control API -- *)

type result_control = int

type control_start = control_2 
and  control_0 = Continue_as_control of control_2 | Quit_as_control of result_control
and  control_2 = { hTask : int ->  control_3 }
and  control_3 = (principal -> control_7) * (unit -> control_0)
and  control_7 = Map of int * control_9
and  control_9 = { hReduce : int ->  unit }

let control registry id (x:control_start) =
 let rec control_start (x:control_start) = 
   sendJoin session "control" id registry ;
   let reg = sendLock session "control" id registry in
   control_2 reg ["control",id] x 
 and control_0 reg sub (x:control_0) = 
   sendUnlock session "control" id registry;
   match x with 
   Continue_as_control x -> let reg = sendLock session "control" id registry in control_2 reg sub x
 | Quit_as_control x -> sendQuit session "control" id registry ; x
 and control_2 reg sub (x:control_2) = 
  let tags = [("Task",(List.map (alias sub) []))] in
  let m = recvMsg session "control" tags in
  match m with
   ("Task",v) -> 
     let v:int = Marshal.from_string v 0 in let x = x.hTask v in control_3 reg sub x
 and control_3 reg sub (x:control_3) = 
   let (g,c) = x in
   let lt = List.map (fun y -> 
       Thread.create (fun ()-> 
          let sub = ("x",y)::sub in 
          let x = g(y) in control_7 reg sub x) ())
      (lreg_get reg "cluster" sub []) in
   let () = List.iter (fun t -> Thread.join t) lt in
   let x = c () in control_0 reg sub x
 and control_7 reg sub (x:control_7) = match x with
   Map (v,x) -> sendMsg session "control" id "cluster" (alias sub "x") "Map" [] v sub ; control_9 reg sub x 
 and control_9 reg sub (x:control_9) = 
  let tags = [("Reduce",(List.map (alias sub) []))] in
  let m = recvMsg session "control" tags in
  match m with
   ("Reduce",v) -> 
     let v:int = Marshal.from_string v 0 in let x = x.hReduce v in ()
 in
 start_runtime session "control" id ; control_start x

(* -- cluster API -- *)

type result_cluster = string

type cluster_start = cluster_11 
and  cluster_0 = Continue_as_cluster of cluster_11 | Quit_as_cluster of result_cluster
and  cluster_11 = { hMap : int ->  cluster_12 }
and  cluster_12 = Reduce of int * cluster_0

let cluster registry id (x:cluster_start) =
 let rec cluster_start (x:cluster_start) = 
   sendJoin session "cluster" id registry ;
   let reg = sendLock session "cluster" id registry in
   cluster_11 reg ["cluster",id] x 
 and cluster_0 reg sub (x:cluster_0) = 
   sendUnlock session "cluster" id registry;
   match x with 
   Continue_as_cluster x -> let reg = sendLock session "cluster" id registry in cluster_11 reg sub x
 | Quit_as_cluster x -> sendQuit session "cluster" id registry ; x
 and cluster_11 reg sub (x:cluster_11) = 
  let tags = [("Map",(List.map (alias sub) []))] in
  let m = recvMsg session "cluster" tags in
  match m with
   ("Map",v) -> 
     let v:int = Marshal.from_string v 0 in let x = x.hMap v in cluster_12 reg sub x
 and cluster_12 reg sub (x:cluster_12) = match x with
   Reduce (v,x) -> sendMsg session "cluster" id "control" (alias sub "control") "Reduce" [] v sub ; cluster_0 reg sub x 
 in
 start_runtime session "cluster" id ; cluster_start x

