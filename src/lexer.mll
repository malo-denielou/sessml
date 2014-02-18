{
  (********************************************************************)
  (* Sessml - Implementation                                          *)
  (*                                                                  *)
  (* lexer.mll                                                        *)
  (********************************************************************)
  (* $Id: lexer.mll 5020 2008-02-20 15:12:15Z denielou $ *)

open Common
open Syntax
open Parser

module LE = Lexing

let debug = gen_debug Common.debug_parserlexer "lexer"

let lexeme = LE.lexeme
let linestart = ref 0
let lineno = ref 1

let newline lexbuf : unit =
(*  debug "New line added" ; *)
  linestart := LE.lexeme_start lexbuf; 
  let pos = lexbuf.Lexing.lex_curr_p in
  lexbuf.Lexing.lex_curr_p <- { pos with
    Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
    Lexing.pos_bol = pos.Lexing.pos_cnum;} ;
  incr lineno

let info lexbuf : info =
(*  debug "Gathering lexeme information" ; *)
  let c1 = LE.lexeme_start lexbuf in
  let c2 = LE.lexeme_end lexbuf in
  (!lineno, c1 - !linestart),(!lineno, c2 - !linestart)

let error lexbuf s =
  debug ("Error generation: "^s) ;
  let (l1,c1),(l2,c2) = info lexbuf in
  let t = lexeme lexbuf in
  let s = Printf.sprintf " %d:%d-%d: %s" l1 c1 c2 s in
  if t = "" then (debug ("No lexeme found") ;raise (Syntax_error (s,((l1,c1),(l2,c2)))))
  else (debug ("Lexeme found: "^t) ;raise (Syntax_error (s^ ": " ^ t,((l1,c1),(l2,c2)))))

}

let blank = [' ' '\t']+
let symbol = [^ '"' '=' '{' '}' '[' ']' '(' ')' ':'
                  '<' '>' ';' ',' '\n' '\r' ' ' '\t' '-' '+' '#' '$']+
  let identlower = [ 'a' - 'z' '_'] ['a' - 'z' 'A' - 'Z' '0' - '9' '_']*
let identupper = [ 'A' - 'Z'] ['a' - 'z' 'A' - 'Z' '0' - '9' '_']*
let identifier = [ 'a' - 'z' 'A' - 'Z'] ['a' - 'z' 'A' - 'Z' '0' - '9' '_']*
let ocamltype = [ 'a' - 'z' 'A' - 'Z'][ 'a' - 'z' 'A' - 'Z' '0' - '9' '.']*
let nat = ['0' - '9']+
let newline = '\n' 
let char = [^ '\n'] 


rule token = parse
  | blank         { token lexbuf }
  | "role"        { ROLE (info lexbuf) }
  | "roles"       { ROLES (info lexbuf) }
  | "session"     { SESSION (info lexbuf) }
  | "global"      { GLOBAL (info lexbuf) }
  | "rec"         { REC (info lexbuf) }
  | "forall"      { FORALL (info lexbuf) }
  | "with"        { WITH (info lexbuf) }
  | "var"         { VAR (info lexbuf) }
  | "="           { EQUAL (info lexbuf) }
  | "send"        { SEND (info lexbuf) }
  | "recv"        { RECV (info lexbuf) }
  | "->"          { ARROW (info lexbuf) }
  | "trusts"      { TRUSTS (info lexbuf)}
  | ":"           { COLON (info lexbuf) }
  | ";"           { SEMI (info lexbuf) }
  | "."           { DOT (info lexbuf) }
  | ","           { COMMA (info lexbuf) }
  | "("           { LPA (info lexbuf) }
  | ")"           { RPA (info lexbuf) }
  | "{"           { LCB (info lexbuf) }
  | "}"           { RCB (info lexbuf) }
  | "["           { LBR (info lexbuf) }
  | "]"           { RBR (info lexbuf) }
  | "+"           { PLUS (info lexbuf) }
  | "||"          { PAR (info lexbuf) }
  | "|"           { OR (info lexbuf) }
  | "*"           { MUL (info lexbuf) }
  | "<"           { INF (info lexbuf) }
  | identupper    { IDENTUP (info lexbuf,lexeme lexbuf) }
  | identlower    { IDENTLO (info lexbuf,lexeme lexbuf) }
  | '1'           { ONE (info lexbuf) }
  | eof		  { EOF (info lexbuf) }
  | "\r\n"        { newline lexbuf; token lexbuf }
  | newline       { newline lexbuf; token lexbuf }
  | "(*"          { comment lexbuf; token lexbuf }
  | _		  { error lexbuf "Unknown token" }

and comment = parse
  | "(*"             { comment lexbuf; comment lexbuf }
  | "*)"             { () }
  | newline          { newline lexbuf; comment lexbuf }
  | eof		     { error lexbuf "Unmatched '(*'" }
  | _                { comment lexbuf }

and code = parse
  | newline          { newline lexbuf; "\n"^(code lexbuf) }
  | eof		     { "" }
  | _ as x           { (String.make 1 x)^(code lexbuf) }

and ocamltyp = parse
  | ocamltype     { TYP (info lexbuf,lexeme lexbuf) }
  | _             { error lexbuf "Wrong type expression" }
