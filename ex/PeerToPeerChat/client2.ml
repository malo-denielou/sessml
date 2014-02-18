(********************************************************************)
(* SessML - Examples                                                *)
(*                                                                  *)
(* client2.ml                                                       *)
(********************************************************************)
(* Time-stamp: <Deniélou Malo - 2010> *)

open Runtime
open PeerToPeerChat

let () = register {id="bob";ip="127.0.0.1";port=8052}
let () = register {id="charlie";ip="127.0.0.1";port=8050}

let nop () = () 

let () = 
  let rec continuation n =
    ((fun () -> ((fun x -> Msg(x,())),nop)),
     (fun () -> ((fun x -> {hMsg=fun s -> Printf.printf "Received %s\n" s}),nop)),
     (fun _ -> Printf.printf "Iteration nb %d\n" n ; Continue_as_client (continuation (n+1))))
  in
  let res = client "charlie" "bob" (continuation 0) 
  in Printf.printf
  "Finished with %d\n" res
