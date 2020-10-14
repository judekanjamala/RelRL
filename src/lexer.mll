{

open Lexing
open Parser

exception Lexer_error of string

let symbols = Hashtbl.of_seq @@ List.to_seq [
    ("ghost", GHOST);
    ("public", PUBLIC);
    ("modscope", MODSCOPE);

    ("null", NULL);
    ("true", TRUE);
    ("false", FALSE);

    ("(", LPAREN);
    (")", RPAREN);
    (",", COMMA);
    (":", COLON);
    ("::", DOUBLE_COLON);
    (";", SEMICOLON);
    ("{", LBRACE);
    ("}", RBRACE);
    ("[", LBRACK);
    ("]", RBRACK);
    (".", DOT);
    ("+", PLUS);
    ("-", MINUS);
    ("*", MULT);
    ("/", DIV);
    ("`", IMAGE);
    ("=", EQUAL);
    ("<>", NOTEQUAL);
    ("<=", LEQ);
    ("<", LT);
    (">=", GEQ);
    (">", GT);
    ("#", DISJOINT);
    ("union", UNION);
    ("inter", INTER);
    ("diff", DIFF);
    ("in", IN);
    ("notin", NOTIN);
    ("subset", SUBSETEQ);
    ("not", NOT);
    ("and", AND);
    ("or", OR);

    ("True", FRM_TRUE);
    ("False", FRM_FALSE);
    ("Type", FRM_TYPE);
    ("~", FRM_NOT);
    ("/\\", CONJ);
    ("\\/", DISJ);
    ("NOT", FRM_NOT);
    ("AND", CONJ);
    ("OR", DISJ);
    ("->", IMP);
    ("<->", IFF);
    ("let", LET);
    ("old", OLD);
    ("forall", FORALL);
    ("exists", EXISTS);

    ("skip", SKIP);
    (":=", ASSIGN);
    ("new", NEW);
    ("var", VAR);
    ("if", IF);
    ("then", THEN);
    ("else", ELSE);
    ("while", WHILE);
    ("do", DO);
    ("done", DONE);
    ("assume", ASSUME);
    ("assert", ASSERT);
    ("invariant", INVARIANT);

    ("rd", READ);
    ("wr", WRITE);
    ("rw", READWRITE);
    ("requires", REQUIRES);
    ("ensures", ENSURES);
    ("effects", EFFECTS);
    ("reads", EFFECT_RDS);
    ("writes", EFFECT_WRS);
    ("reads/writes", EFFECT_RWS);

    ("meth", METH);
    ("class", CLASS);
    ("interface", INTERFACE);
    ("end", END);

    ("predicate", PREDICATE);
    ("axiom", AXIOM);
    ("lemma", LEMMA);

    ("import", IMPORT);
    ("theory", THEORY);
    ("as", AS);
    ("boundary", BOUNDARY);
    ("datagroup", DATAGROUP);
    ("contains", CONTAINS);

    ("module", MODULE);
    ("bimodule", BIMODULE);

    ("|", BAR);
    ("<|", LEFT_OPEN);
    ("<]", LEFT_CLOSE);
    ("[>", RIGHT_OPEN);
    ("|>", RIGHT_CLOSE);
    ("=:=", BIEQUAL);
    ("|_", LEFT_SYNC);
    ("_|", RIGHT_SYNC);
    ("|.", LEFT_SYNC);
    (".|", RIGHT_SYNC);

    ("Agree", AGREE);
    ("Both", BOTH);

    ("Var", BIVAR);
    ("If", BIIF);
    ("While", BIWHILE);
    ("Assume", BIASSUME);
    ("Assert", BIASSERT);
    ("Link", BIUPDATE);
    ("with", WITH);

    ("extern", EXTERN);
    ("type", TYPE);
    ("const", CONST);
    ("default", DEFAULT);
  ]

let is_uppercase_ident str =
  let ini = str.[0] in
  Char.uppercase_ascii ini = ini

let mk_token lexbuf =
  let str = lexeme lexbuf in
  try (Hashtbl.find symbols str)
  with _ ->
    if is_uppercase_ident str
    then UIDENT str
    else LIDENT str

}

let newline = '\n' | ('\r' '\n') | '\r'
let lowercase = ['a'-'z']
let uppercase = ['A'-'Z']
let character = uppercase | lowercase
let whitespace = ['\t' ' ']
let digit = ['0'-'9']

rule token = parse
  | eof { EOF }
  | whitespace { token lexbuf }
  | newline { new_line lexbuf; token lexbuf }
  | "/*" { comments 0 lexbuf }
  | '(' | ')' | '{' | '}' | '[' | ']' | ':' | ';'
  | '+' | '-' | '*' | '/' | '`' | '~'
  | '=' | '<' | '>' | "<=" | ">=" | "<>"
  | '.' | "/\\" | "\\/" | "->" | "<->"
  | '#' | ',' | "==" | ":=" | "|" | "=:="
  | "<|" | "<]" | "[>" | "|>" | "|_" | "_|"
  | "::" | "|." | ".|" { mk_token lexbuf }
  | character (digit | character | '_' | '\'' | '/')* { mk_token lexbuf }
  | digit+ { INT (int_of_string (lexeme lexbuf)) }
  | _ { raise @@ Lexer_error ("Unexpected char: " ^ Lexing.lexeme lexbuf) }

and comments level = parse
  | "*/" { if level = 0 then token lexbuf else comments (level-1) lexbuf }
  | "/*" { comments (level+1) lexbuf }
  | newline { new_line lexbuf; comments level lexbuf }
  | eof  { raise @@ Lexer_error ("Comment not closed") }
  | _    { comments level lexbuf }
