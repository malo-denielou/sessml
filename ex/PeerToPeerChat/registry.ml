(********************************************************************)
(* SessML - Examples                                                *)
(*                                                                  *)
(* registry.ml                                                      *)
(********************************************************************)
(* Time-stamp: <Deniélou Malo - 2010> *)

open Runtime
open PeerToPeerChat

let () = register {id="alice";ip="127.0.0.1";port=8051}
let () = register {id="bob";ip="127.0.0.1";port=8052}
let () = register {id="charlie";ip="127.0.0.1";port=8050}

let () =
    registry "charlie"
