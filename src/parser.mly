%{
  (********************************************************************)
  (* Session - Implementation                                         *)
  (*                                                                  *)
  (* parser.mly                                                       *)
  (********************************************************************)
  (* $Time-stamp: <03-08-2010 15:09 by Pierre-Malo Denielou>$ *)
  
  open Common
  open Syntax
  open Lexing

  let debug = gen_debug debug_parserlexer "parser"
 
  let error t info =
    debug ("Error: "^t) ;
    let (l,c1),(_,c2) = info in
    let s = Printf.sprintf "%d:%d-%d" l c1 c2 in
    if t = "" then raise (Common.Parse_error (s,info))
    else raise (Common.Parse_error ((*s^ ": " ^ *)t,info))

  let parse_error _ =
    let start_pos = Parsing.symbol_start_pos () in
    let end_pos = Parsing.symbol_end_pos () in
    let (l1,c1),(l2,c2) =
      (start_pos.pos_lnum,start_pos.pos_bol),(end_pos.pos_lnum,end_pos.pos_bol)
    in
(*    let s = Printf.sprintf "%d:%d-%d" l1 c1 c2 in*)
    raise (Common.Parse_error ("",((l1,c1),(l2,c2))))

    
    

%}

%token <Common.info> ROLES GLOBAL REC WITH FORALL
%token <Common.info> ROLE SESSION VAR
%token <Common.info> EOF
%token <Common.info> SEND RECV OR ARROW TRUSTS INF
%token <Common.info> LPA RPA LCB RCB LBR RBR
%token <Common.info> LANG
%token <Common.info * string> RANG
%token <Common.info> DOT SEMI EQUAL COMMA MUL COLON PLUS ONE PAR
%token <Common.info * string> IDENTUP IDENTLO
%token <Common.info * string> TYP
%left OR
%start sess
%type <Syntax.ast> sess

%%

sess:
| SESSION IDENTUP EQUAL vars trust ROLE roles { Localast (snd $2, $4, $5, $7) }
| SESSION IDENTUP EQUAL vars trust ROLE       { error "Missing role name" ($6) }
| SESSION IDENTUP EQUAL vars trust      { error "Missing role declaration" ($3) }
| SESSION IDENTUP EQUAL vars ROLE roles { Localast (snd $2, $4, [], $6) }
| SESSION IDENTUP EQUAL vars ROLE       { error "Missing role name" ($5) }
| SESSION IDENTUP EQUAL ROLE roles      { Localast (snd $2, [], [], $5) }
| SESSION IDENTUP EQUAL ROLE            { error "Missing role name" ($3) }
| SESSION IDENTUP EQUAL vars            { error "Missing role declaration" ($3)}
| SESSION IDENTUP EQUAL                 { error "Missing role declaration" ($3) }
| SESSION IDENTUP EQUAL ROLES rdec GLOBAL glob  { Globalast (snd $2, $5, $7) }
| SESSION IDENTUP EQUAL ROLES rdec GLOBAL  {error "Missing rec declaration" ($6)  }
| SESSION IDENTUP EQUAL ROLES rdec         {error "Missing global declaration" ($4)  }
| SESSION IDENTUP EQUAL ROLES              {error "Missing roles declaration" ($4)  }
| SESSION IDENTUP                       { error "Missing equal" (fst $2) }
| SESSION IDENTLO                       { error "Lowercase session name" (fst $2) }
| SESSION                               { error "Missing identifier" ($1) }
| IDENTLO                               { error "Sessions should start with keyword 'session'" (fst $1) }
| IDENTUP                               { error "Sessions should start with keyword 'session'" (fst $1) }
|                                       { error "Shouldn't happen" bogusInfo }
;

rdec:
| IDENTLO LBR ONE RBR COLON IDENTLO COMMA rdec { [(snd $1,Single,snd $6)]@$8 }
| IDENTLO LBR MUL RBR COLON IDENTLO COMMA rdec { [(snd $1,Multi,snd $6)]@$8 }
| IDENTLO LBR ONE RBR COLON IDENTLO            { [(snd $1,Single,snd $6)] }
| IDENTLO LBR MUL RBR COLON IDENTLO            { [(snd $1,Multi,snd $6)] }
;

glob:
| REC IDENTLO EQUAL global  { ($4) }
| REC IDENTLO EQUAL         { error "Missing global type declaration" ($3)  }
| REC IDENTLO               { error "Missing equal" (fst $2)  }
| REC                       { error "Missing global type name" ($1)  }
;

global:
| IDENTLO COLON global              { GASMu (merge_info (fst $1) $2,snd $1,$3) }
| IDENTLO COLON                     { error "Missing session after recursive point" $2 }
| IDENTLO                           { error "Missing colon after recursing point name" (fst $1) }
| IDENTLO ARROW IDENTLO WITH msglist SEMI global
      { GASSeq ($6,(GASMsg (merge_info (fst $1) $2, (snd $1,snd $3,$5)),$7))}
| IDENTLO ARROW IDENTLO WITH msglist PAR global
      { GASPar ($6,(GASMsg (merge_info (fst $1) $2, (snd $1,snd $3,$5)),$7))}
| IDENTLO ARROW IDENTLO WITH msglist {GASMsg (merge_info (fst $1) $2,
                                              (snd $1,snd $3,$5))}
| FORALL IDENTLO COLON IDENTLO DOT global { GASPoll ($1,(snd $2,snd $4,$6)) }
| LPA global RPA {$2}
;
msg:
| IDENTUP LCB varlist RCB LPA IDENTLO RPA { ((snd $1, snd $6),$3) }
| IDENTUP LCB varlist RCB                 { ((snd $1, "unit"),$3) }
| IDENTUP LPA IDENTLO RPA                 { ((snd $1, snd $3),[]) }
| IDENTUP                                 { ((snd $1, "unit"),[]) }
;
msglist:
| msg DOT LPA global RPA OR msglist {[($1,$4)]@$7}
| msg DOT LPA global RPA            {[($1,$4)]}
| msg                               {[($1,GASEnd)]}
;
varlist:
| IDENTLO COMMA varlist {(snd $1)::$3 }
| IDENTLO               { [snd $1] }
;

vars:
| VAR IDENTLO COLON IDENTLO SEMI vars { [(snd $2,snd $4)]@$6 }
| VAR IDENTLO COLON IDENTLO vars      { [(snd $2,snd $4)]@$5 }
| VAR IDENTLO COLON IDENTLO SEMI      { [(snd $2,snd $4)] }
| VAR IDENTLO COLON IDENTLO           { [(snd $2,snd $4)] }
| VAR IDENTLO COLON                   { error "Missing variable type" ($3)}
| VAR IDENTLO                         { error "Missing colon" (fst $2)}
| VAR                                 { error "Missing variable name" ($1)}
;
trust:
| TRUSTS IDENTLO INF IDENTLO listrole trust  { (List.map (function x -> (snd $2,x))
                                          ((snd $4)::$5)@$6)}
| TRUSTS IDENTLO INF IDENTLO trust           {(snd $2,snd $4)::$5 }
| TRUSTS IDENTLO INF IDENTLO listrole { List.map (function x -> (snd $2,x))
                                          ((snd $4)::$5) }
| TRUSTS IDENTLO INF IDENTLO                 { [snd $2,snd $4]}
| TRUSTS IDENTLO INF                         { error "Missing role name" ($3) }
| TRUSTS IDENTLO                             { error "Missing '<'" (fst $2) }
| TRUSTS                                     { error "Missing role name" ($1) }

listrole:
| COMMA IDENTLO listrole     { (snd $2)::$3 }
| COMMA IDENTLO              { (snd $2)::[] }
| COMMA                      { error "Missing role name" ($1) }
;
roles:
| IDENTLO COLON IDENTLO EQUAL session ROLE roles    { (snd $1,snd $3,$5)::$7 }
| IDENTLO COLON                               { error "Missing return type" $2 }
| IDENTLO EQUAL session ROLE roles            { (snd $1,"string",$3)::$5 }
| IDENTLO EQUAL session ROLE                  { error "Missing role name" $4 }
| IDENTLO COLON IDENTLO EQUAL session         { (snd $1,snd $3,$5)::[] }
| IDENTLO EQUAL session                       { (snd $1,"string",$3)::[] }
| IDENTLO EQUAL                               { error "Missing session description" ($2)}
| IDENTLO                                     { error "Missing equal" (fst $1)}
;


session:
| IDENTLO COLON session             { ASMu (merge_info (fst $1) $2,snd $1,$3) }
| IDENTLO COLON                     { error "Missing session after recursive point" $2 }
| IDENTLO                           { error "Missing colon after recursing point name" (fst $1) }
| SEND LPA sendmsg sendmsglist      { ASSend ($1,$3::$4) }
| SEND LPA sendmsg                  { error "Missing matching parenthesis" $2 }
| SEND LPA                          { error "Missing matching parenthesis" $2 }
| SEND sendmsg                      { ASSend ($1,[$2]) }
| SEND                              { error "Missing label" $1 }
//| RECV LBR OR recvmsg recvmsglist   { ASReceive ($1,$4::$5) }
//| RECV LBR OR                       { error "Missing label" $3 }
| RECV LBR OR recvmsg recvmsglist     { ASReceive ($1,$4::$5) }
| RECV LBR recvmsg recvmsglist        { ASReceive ($1,$3::$4) }
| RECV LBR recvmsg                    { error "Missing label" $2 }
| RECV LBR                            { error "Missing label" $2 }
| RECV recvmsg                        { ASReceive ($1,[$2]) }
| RECV                                { error "Missing label" $1 }

listname:
| IDENTLO COMMA listname              { (snd $1)::$3 }
| IDENTLO listname                    { (snd $1)::$2 }
| IDENTLO                             { error "Missing curly brace" (fst $1) }
| RCB                                 { [] }
;

label:
| IDENTUP LCB listname                { (snd $1,$3) }
| IDENTUP LCB                         { error "Missing variable name" ($2)}
| IDENTUP                             { (snd $1,[]) }
| LCB listname IDENTUP                { (snd $3,$2) }
| LCB                                 { error "Missing variable name" ($1)}
;

sendsession:
| SEND LPA sendmsg sendmsglist    { ASSend ($1,$3::$4) }
| SEND LPA sendmsg error          { error "Missing matching parenthesis" $2 }
| SEND LPA                        { error "Missing matching parenthesis" $2 }
| SEND sendmsg                    { ASSend ($1,[$2]) }
| SEND                            { error "Missing label" $1 }
| IDENTLO COLON sendsession       { ASMu (merge_info (fst $1) $2,snd $1,$3) }
| IDENTLO COLON                   { ASMu (merge_info (fst $1) $2,snd $1,ASEnd) }
| IDENTLO                         { ASGoto (fst $1,snd $1) }
;

sendmsg:
| label SEMI recvsession { ({label = fst $1; write = snd $1; read = []},$3)}
| label SEMI             { ({label = fst $1; write = snd $1; read = []},ASEnd)}
| label                  { ({label = fst $1; write = snd $1; read = []},ASEnd)}
;

sendmsglist:
| PLUS label SEMI recvsession sendmsglist { [({label = fst $2; write = snd $2; read = []},$4)]@$5}
| PLUS label sendmsglist                  { [({label = fst $2; write = snd $2; read = []},ASEnd)]@$3}
| PLUS label error                        { error "Missing semi-colon" $1 }
| PLUS                                    { error "Missing label" $1 }
| OR                                      { error "Recv lists use '|' and not '+'" $1 }
| RPA                                     { [] }
| PLUS label SEMI sendmsglist             { [({label = fst $2; write = snd $2; read = []},ASEnd)]@$4}
;



recvsession:
| RECV LBR OR recvmsg recvmsglist     { ASReceive ($1,$4::$5) }
| RECV LBR recvmsg recvmsglist        { ASReceive ($1,$3::$4) }
| RECV LBR recvmsg error              { error "Missing label" $2 }
| RECV recvmsg                        { ASReceive ($1,[$2]) }
//| RECV LBR                            { error "Missing label" $2 }
| RECV                                { error "Missing label" $1 }
| IDENTLO COLON recvsession           { ASMu (merge_info (fst $1) $2,snd $1,$3) }
| IDENTLO COLON                       { ASMu (merge_info (fst $1) $2,snd $1,ASEnd) }
| IDENTLO                             { ASGoto (fst $1,snd $1) }
//| RECV                                { error "Missing label" $1 }
//| RECV LBR                            { error "Missing label" $2 }
//| RECV LBR OR                         { error "Missing label" $3 }
//| RECV LBR recvmsg                    { error "Missing corresponding right bracket" $2}
;

recvmsg:
| label ARROW sendsession { ({label = fst $1; read = snd $1; write = []},$3)}
| label ARROW             { error "Missing sending session" $2}
| label                   { ({label = fst $1; read = snd $1; write = []},ASEnd)}
;

recvmsglist:
| OR label ARROW sendsession recvmsglist { [({label = fst $2; read = snd $2; write = []},$4)]@$5}
//| OR label ARROW sendsession error       { error "Missing pipe" $3}
//| OR label ARROW error                   { error "Wrong session" $3}
| OR label ARROW                         { error "Missing sending session" $3}
| OR label recvmsglist                   { [({label = fst $2; read = snd $2; write = []},ASEnd)]@$3} 
//| OR label                               { error "Missing right bracket" (fst $2)}
| OR                                     { error "Missing label" $1 }    
| RBR                                    { [] }
;





/*
recvmsglist:
| OR label ARROW sendsession recvmsglist { [((snd $2,"string"),$4)]@$5}
| OR label ARROW sendsession RBR     { [((snd $2,"string"),$4)]}
| OR label ARROW                         { error "Missing sending session" $3}
| OR label recvmsglist                   { [((snd $2,"string"),ASEnd)]@$3} 
| OR label RBR                           { [((snd $2,"string"),ASEnd)]} 
| OR                                     { error "Missing label" $1 }    
;

*/















/*

session:
| SEND sendmsg            { ASSend ($1,$2) }
| SEND                    { error "Missing message declaration" $1 }
| RECV recvmsg            { ASReceive ($1,$2) }
| RECV                    { error "Missing message declaration" $1 }
| IDENTLO COLON session   { ASMu (merge_info (fst $1) $2,snd $1,$3) }
| IDENTLO COLON           { ASMu (merge_info (fst $1) $2,snd $1,ASEnd) }
| IDENTLO                 { ASGoto (fst $1,snd $1) }
| LPA session RPA         { $2 }
| LPA                     { error "Missing right parenthesis" $1 }
;


sendmsg:
| IDENTUP SEMI session                   { [(snd $1,"string"),$3]}
| IDENTUP SEMI                           { [(snd $1,"string"),ASEnd]}
| IDENTUP                                { [(snd $1,"string"),ASEnd]}
| IDENTUP LCB listname RCB SEMI session  { [(snd $1,"string"),$6]}
| IDENTUP LCB listname RCB SEMI          { [(snd $1,"string"),ASEnd]}
| IDENTUP LCB listname RCB               { [(snd $1,"string"),ASEnd]}
| IDENTUP LCB listname                   { error "Missing matching brace" $2}
| IDENTUP LCB                            { error "Missing list of variable names" $2}
| LPA listsendmsg RPA                    { $2 }
| LPA                                    { error "Missing message declaration" $1}
;

recvmsg:
| IDENTUP ARROW SEND sendmsg              { [(snd $1,"string"),ASSend ($3,$4)]}
| IDENTUP ARROW IDENTLO COLON SEND sendmsg{ [(snd $1,"string"),ASMu (merge_info (fst $3) $4,snd $3,ASSend ($5,$6))]}
| IDENTUP ARROW IDENTLO COLON             { [(snd $1,"string"),ASMu (merge_info (fst $3) $4,snd $3,ASEnd)]}
| IDENTUP ARROW IDENTLO                   { [(snd $1,"string"),ASGoto (fst $3,snd $3)]}
| IDENTUP ARROW                           { [(snd $1,"string"),ASEnd]}
| IDENTUP                                 { [(snd $1,"string"),ASEnd]}
| IDENTUP LCB listname RCB ARROW SEND sendmsg  { [(snd $1,"string"),ASSend ($6,$7)]}
| IDENTUP LCB listname RCB ARROW IDENTLO COLON SEND sendmsg{ [(snd $1,"string"),ASMu (merge_info (fst $6) $7,snd $6,ASSend ($8,$9))]}
| IDENTUP LCB listname RCB ARROW IDENTLO COLON             { [(snd $1,"string"),ASMu (merge_info (fst $6) $7,snd $6,ASEnd)]}
| IDENTUP LCB listname RCB ARROW IDENTLO                   { [(snd $1,"string"),ASGoto (fst $6,snd $6)]}
| IDENTUP LCB listname RCB ARROW          { [(snd $1,"string"),ASEnd]}
| IDENTUP LCB listname RCB                { [(snd $1,"string"),ASEnd]}
| IDENTUP LCB listname                    { error "Missing matching brace" $2}
| IDENTUP LCB                             { error "Missing list of variable names" $2}
| OR listrecvmsg                          { $2 }
| OR                                      { error "Wrong message label" $1 }
;

listsendmsg:
| IDENTUP SEMI session                   { [(snd $1,"string"),$3]}
| IDENTUP SEMI                           { [(snd $1,"string"),ASEnd]}
| IDENTUP                                { [(snd $1,"string"),ASEnd]}
| IDENTUP LCB listname RCB SEMI session  { [(snd $1,"string"),$6]}
| IDENTUP LCB listname RCB SEMI          { [(snd $1,"string"),ASEnd]}
| IDENTUP LCB listname RCB               { [(snd $1,"string"),ASEnd]}
| IDENTUP SEMI session PLUS listsendmsg  { [(snd $1,"string"),$3]@$5}
| IDENTUP SEMI PLUS listsendmsg          { [(snd $1,"string"),ASEnd]@$4}
| IDENTUP PLUS listsendmsg               { [(snd $1,"string"),ASEnd]@$3}
| IDENTUP LCB listname RCB SEMI session PLUS listsendmsg { [(snd $1,"string"),$6]@$8}
| IDENTUP LCB listname RCB SEMI PLUS listsendmsg         { [(snd $1,"string"),ASEnd]@$7}
| IDENTUP LCB listname RCB PLUS listsendmsg              { [(snd $1,"string"),ASEnd]@$6}
;

listrecvmsg:
| IDENTUP ARROW SEND sendmsg              { [(snd $1,"string"),ASSend ($3,$4)]}
| IDENTUP ARROW IDENTLO COLON SEND sendmsg{ [(snd $1,"string"),ASMu (merge_info (fst $3) $4,snd $3,ASSend ($5,$6))]}
| IDENTUP ARROW IDENTLO COLON             { [(snd $1,"string"),ASMu (merge_info (fst $3) $4,snd $3,ASEnd)]}
| IDENTUP ARROW IDENTLO                   { [(snd $1,"string"),ASGoto (fst $3,snd $3)]}
| IDENTUP ARROW                           { [(snd $1,"string"),ASEnd]}
| IDENTUP                                 { [(snd $1,"string"),ASEnd]}
| IDENTUP LCB listname RCB ARROW SEND sendmsg  { [(snd $1,"string"),ASSend ($6,$7)]}
| IDENTUP LCB listname RCB ARROW IDENTLO COLON SEND sendmsg{ [(snd $1,"string"),ASMu(merge_info (fst $6) $7,snd $6,ASSend($8,$9))]}
| IDENTUP LCB listname RCB ARROW IDENTLO COLON             { [(snd $1,"string"),ASMu (merge_info (fst $6) $7,snd $6,ASEnd)]}
| IDENTUP LCB listname RCB ARROW IDENTLO                   { [(snd $1,"string"),ASGoto (fst $6,snd $6)]}
| IDENTUP LCB listname RCB ARROW          { [(snd $1,"string"),ASEnd]}
| IDENTUP LCB listname RCB                { [(snd $1,"string"),ASEnd]}
| IDENTUP ARROW SEND sendmsg OR listrecvmsg              { [(snd $1,"string"),ASSend ($3,$4)]@$6}
| IDENTUP ARROW IDENTLO COLON SEND sendmsg OR listrecvmsg{ [(snd $1,"string"),ASMu (merge_info (fst $3) $4,snd $3,ASSend ($5,$6))]@$8}
| IDENTUP ARROW IDENTLO COLON OR listrecvmsg             { [(snd $1,"string"),ASMu (merge_info (fst $3) $4,snd $3,ASEnd)]@$6}
| IDENTUP ARROW IDENTLO OR listrecvmsg                   { [(snd $1,"string"),ASGoto (fst $3,snd $3)]@$5}
| IDENTUP ARROW OR listrecvmsg                           { [(snd $1,"string"),ASEnd]@$4}
| IDENTUP OR listrecvmsg                                 { [(snd $1,"string"),ASEnd]@$3}
| IDENTUP LCB listname RCB ARROW SEND sendmsg OR listrecvmsg  { [(snd $1,"string"),ASSend ($6,$7)]@$9}
| IDENTUP LCB listname RCB ARROW IDENTLO COLON SEND sendmsg OR listrecvmsg{ [(snd $1,"string"),ASMu(merge_info (fst $6) $7,snd $6,ASSend($8,$9))]@$11}
| IDENTUP LCB listname RCB ARROW IDENTLO COLON OR listrecvmsg             { [(snd $1,"string"),ASMu (merge_info (fst $6) $7,snd $6,ASEnd)]@$9}
| IDENTUP LCB listname RCB ARROW IDENTLO OR listrecvmsg                   { [(snd $1,"string"),ASGoto (fst $6,snd $6)]@$8}
| IDENTUP LCB listname RCB ARROW OR listrecvmsg          { [(snd $1,"string"),ASEnd]@$7}
| IDENTUP LCB listname RCB OR listrecvmsg                { [(snd $1,"string"),ASEnd]@$6}


| IDENTUP ARROW session OR listrecvmsg                  { [(snd $1,"string"),$3]@$5}
| IDENTUP ARROW OR listrecvmsg                          { [(snd $1,"string"),ASEnd]@$4}
| IDENTUP OR listrecvmsg                                { [(snd $1,"string"),ASEnd]@$3}
| IDENTUP LCB listname RCB ARROW session OR listrecvmsg { [(snd $1,"string"),$6]@$8}
| IDENTUP LCB listname RCB ARROW OR listrecvmsg         { [(snd $1,"string"),ASEnd]@$7}
| IDENTUP LCB listname RCB OR listrecvmsg               { [(snd $1,"string"),ASEnd]@$6}
;

*/

// Old stuff

/*

msgold:
| IDENT TYP SEMI session                 { [(snd $1,snd $2),$4]}
| IDENT TYP                              { [(snd $1,snd $2),ASEnd]}
| IDENT                                  { error "Missing type information" (fst $1)}
| LPA IDENT TYP SEMI session listmsg RPA { ((snd $2,snd $3),$5)::$6}
| LPA IDENT TYP SEMI session RPA         { [(snd $2,snd $3),$5] }
| LPA IDENT TYP SEMI                     { error "Missing right parenthesis" $1 }
| LPA IDENT TYP listmsg RPA              { ((snd $2,snd $3),ASEnd)::$4}
| LPA IDENT                              { error "Missing type information" (fst $2)}
| LPA                                    { error "Missing message declaration" $1}
;

*/
