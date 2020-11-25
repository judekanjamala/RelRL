%{

open Ast

let mk_node (e: 'a) (pos: Lexing.position) =
  { elt = e; loc = pos }

let mk_meth_param_info modifier name t =
  let pty, is_non_null =
    match t with
    | `Can_be_null t -> (t, false)
    | `Non_null t -> (t, true) in
  { param_name = name;
    param_modifier = modifier;
    param_ty = pty;
    is_non_null = is_non_null
  }

let mk_meth_decl mname params rty spec =
  let rty, is_non_null =
    match rty with
    | `Can_be_null t -> (t, false)
    | `Non_null t -> (t, true) in
  { meth_name = mname;
    params = params;
    result_ty = rty;
    result_ty_is_non_null = is_non_null;
    meth_spec = spec
  }

let mk_bimeth_decl mname params_left params_right ret_left ret_right bispec =
  let is_non_null = function
    | `Can_be_null _ -> false
    | `Non_null _ -> true in
  let get_ty = function
    | `Can_be_null t | `Non_null t -> t in
  let left_null_status, right_null_status =
    is_non_null ret_left, is_non_null ret_right in
  { bimeth_name = mname;
    bimeth_left_params = params_left;
    bimeth_right_params = params_right;
    result_ty = (get_ty ret_left, get_ty ret_right);
    result_ty_is_non_null = (left_null_status, right_null_status);
    bimeth_spec = bispec
  }


let mk_extern_symbol sym kind inp out def =
  { extern_symbol = sym;
    extern_kind = kind;
    extern_input = inp;
    extern_output = out;
    extern_default = def;
  }

let mk_effect_elt kind desc loc =
  let mk kind desc = mk_node {effect_kind = kind; effect_desc = desc} loc in
  let mk_effect_desc = function
    | `Ident id -> Effvar id
    | `Image (g,f) -> Effimg (g,f) in
  let desc = mk_effect_desc desc in
  match kind with
  | `Read_effect -> [mk Read desc]
  | `Write_effect -> [mk Write desc]
  | `Readwrite_effect -> [mk Read desc; mk Write desc]

let mk_boundary_elt desc =
  match desc.elt with
  | `Ident id -> mk_node (Effvar id) desc.loc
  | `Image (g,f) -> mk_node (Effimg (g,f)) desc.loc

%}

%token EOF

%token GHOST                    /* ghost */
%token PUBLIC                   /* public */
%token MODSCOPE                 /* modscope */

%token <string> UIDENT		/* upper case identifier */
%token <string> LIDENT		/* lower case identifier */

%token DOUBLE_COLON             /* :: */

%token PLUS                     /* + */
%token MINUS                    /* - */
%token MULT                     /* * */
%token DIV                      /* / */
%token UNION                    /* union */
%token INTER                    /* inter */
%token DIFF                     /* diff */
%token IN                       /* in */
%token NOTIN                    /* notin */
%token SUBSETEQ                 /* subset */
%token DISJOINT                 /* # */
%token IMAGE                    /* ` */
%token NOT                      /* not */
%token AND                      /* and */
%token OR                       /* or */
%token EQUAL                    /* = */
%token NOTEQUAL                 /* != */
%token LEQ                      /* <= */
%token LT                       /* < */
%token GT                       /* > */
%token GEQ                      /* >= */

%token NULL                     /* null */
%token TRUE                     /* true */
%token FALSE                    /* false */
%token <int> INT                /* <integer> */

%token FRM_TRUE                 /* True */
%token FRM_FALSE                /* False */
%token FRM_NOT                  /* ~ */
%token FRM_TYPE			/* Type */
%token CONJ                     /* /\ */
%token DISJ                     /* \/ */
%token IMP                      /* => */
%token IFF                      /* <=> */
%token LET                      /* let */
%token OLD			/* old */
%token INIT                     /* init */
%token FORALL                   /* forall */
%token EXISTS                   /* exists */

%token SKIP                     /* skip */
%token ASSIGN                   /* := */
%token NEW                      /* new */
%token VAR                      /* var */
%token IF                       /* if */
%token THEN                     /* then */
%token ELSE                     /* else */
%token WHILE                    /* while */
%token DO                       /* do */
%token INVARIANT                /* invariant */
%token DONE                     /* done */
%token ASSUME                   /* assume */
%token ASSERT                   /* assert */

%token READ                     /* rd */
%token WRITE                    /* wr */
%token READWRITE                /* rw */
%token REQUIRES                 /* requires */
%token ENSURES                  /* ensures */
%token EFFECTS                  /* effects */
%token EFFECT_RDS		/* reads */
%token EFFECT_WRS		/* writes */
%token EFFECT_RWS		/* reads/writes */

%token METH                     /* meth */
%token CLASS                    /* class */
%token INTERFACE                /* interface */
%token END                      /* end */

%token PREDICATE                /* predicate */
%token AXIOM                    /* axiom */
%token LEMMA                    /* lemma */

%token IMPORT                   /* import */
%token THEORY                   /* theory */
%token AS                       /* as */
%token BOUNDARY                 /* boundary */
%token DATAGROUP                /* datagroup */
%token CONTAINS                 /* contains */

%token MODULE                   /* module */
%token BIMODULE			/* bimodule */

%token LPAREN                   /* ( */
%token RPAREN                   /* ) */
%token LBRACE                   /* { */
%token RBRACE                   /* } */
%token LBRACK                   /* [ */
%token RBRACK                   /* ] */
%token COMMA                    /* , */
%token COLON                    /* : */
%token SEMICOLON                /* ; */
%token DOT                      /* . */

%token BAR                      /* | */
%token LEFT_OPEN                /* <| */
%token LEFT_CLOSE               /* <] */
%token RIGHT_OPEN               /* [> */
%token RIGHT_CLOSE              /* |> */
%token BIEQUAL                  /* =:= */
%token LEFT_SYNC                /* |_ */
%token RIGHT_SYNC               /* _| */
%token AGREE                    /* Agree */
%token BOTH                     /* Both */

%token PUBLIC_INV_ANNOT         /* public */
%token PRIVATE_INV_ANNOT        /* private */
%token COUPLING_ANNOT           /* coupling */

%token BIVAR                    /* Var */
%token BIIF                     /* If */
%token BIWHILE                  /* While */
%token BIASSUME                 /* Assume */
%token BIASSERT                 /* Assert */
%token BIUPDATE                 /* Link */
%token WITH                     /* With */

%token EXTERN                   /* extern */
%token TYPE                     /* type */
%token CONST                    /* const */
%token DEFAULT			/* default */

%right IN
%nonassoc BAR
%right SEMICOLON
%right IMP
%nonassoc IFF
%right OR DISJ
%right AND CONJ
%nonassoc LEQ LT GEQ GT
%right NOTEQUAL EQUAL
%left PLUS MINUS
%left MULT DIV
%left UNION INTER DIFF
%left IMAGE
%nonassoc BOTH
%nonassoc UMINUS

%start <Ast.program> top

%%

top:
  | i=program EOF { i }
  ;

ident_name:
  | id=UIDENT { id }
  | id=LIDENT { id }
  ;

simple_lident:
  | id=LIDENT { Id id }
  ;

simple_uident:
  | id=UIDENT { Id id }
  ;

simple_ident:
  | id=ident_name { Id id }
  ;

uident:
  | id=simple_uident { id }
  | id=UIDENT; DOUBLE_COLON; is=separated_nonempty_list(DOUBLE_COLON, UIDENT)
    { Qualid (id, is) }
  ;

ident:
  | id=simple_ident { id }
  | id=UIDENT; DOUBLE_COLON; is=separated_nonempty_list(DOUBLE_COLON, ident_name)
    { Qualid(id, is) }
  ;

ty:
  | t=option(ty); id=ident
    { mk_node
	begin match t with
	| None -> Tctor(id, [])
	| Some t -> Tctor(id, [t])
	end
      $startpos
    }
  | LPAREN; t=ty; RPAREN
    { t }
  ;

%inline const_exp:
  | NULL                { mk_node Enull $startpos }
  | LPAREN; RPAREN      { mk_node Eunit $startpos }
  | TRUE                { mk_node (Ebool true) $startpos }
  | FALSE               { mk_node (Ebool false) $startpos }
  | i=INT               { mk_node (Eint i) $startpos }
  | LBRACE; RBRACE      { mk_node Eemptyset $startpos }
  ;

exp:
  | e=simple_exp { e }
  | e=call_exp { e }
  ;

simple_exp:
  | c=const_exp { mk_node (Econst(c)) $startpos }
  | id=ident    { mk_node (Evar(id)) $startpos }
  | LBRACE; e=simple_exp; RBRACE
    { mk_node (Esingleton(e)) $startpos }
  | e1=simple_exp; op=binop; e2=simple_exp
    { mk_node (Ebinop(op, e1, e2)) $startpos }
  | MINUS; e=simple_exp %prec UMINUS
    { mk_node (Eunrop(Uminus, e)) $startpos }
  | NOT; e=simple_exp %prec UMINUS
    { mk_node (Eunrop(Not, e)) $startpos }
  | e=simple_exp; IMAGE; f=ident
    { mk_node (Eimage(e,f)) $startpos }
  | LPAREN; e=simple_exp; RPAREN
    { e }
  ;

call_exp:
  | fn=ident; args=exp_tuple { mk_node (Ecall(fn,args)) $startpos }
  | LPAREN; e=call_exp; RPAREN { e }
  ;

%inline exp_tuple:
  | LPAREN; es=separated_list(COMMA, exp); RPAREN
    { es }
  ;

%inline binop:
  | PLUS        { Plus }
  | MINUS       { Minus }
  | MULT        { Mult }
  | DIV         { Div }
  | UNION       { Union }
  | INTER       { Inter }
  | DIFF        { Diff }
  | AND         { And }
  | OR          { Or }
  | EQUAL       { Equal }
  | NOTEQUAL    { Nequal }
  | LEQ         { Leq }
  | LT          { Lt }
  | GEQ         { Geq }
  | GT          { Gt }
  ;

formula:
  | f=simple_formula { f }
  | f=general_formula { f }
  ;

simple_formula:
  | e=simple_exp               { mk_node (Fexp e) $startpos }
  | e=call_exp                 { mk_node (Fexp e) $startpos }
  | e=simple_exp; EQUAL; e2=call_exp
    { let eq = mk_node (Ebinop(Equal, e, e2)) $startpos in
      mk_node (Fexp (eq)) $startpos }
  | e=call_exp; EQUAL; e2=simple_exp
    { let eq = mk_node (Ebinop(Equal, e, e2)) $startpos in
      mk_node (Fexp (eq)) $startpos }
  | e=call_exp; EQUAL; e2=call_exp
    { let eq = mk_node (Ebinop(Equal, e, e2)) $startpos in
      mk_node (Fexp (eq)) $startpos }
  | x=ident; DOT; f=ident; EQUAL; e=call_exp
    { mk_node (Fpointsto(x,f,e)) $startpos }
  | e=call_exp; EQUAL; x=ident; DOT; f=ident
    { mk_node (Fpointsto(x,f,e)) $startpos }
  | x=ident; DOT; f=ident; NOTEQUAL; e=call_exp
    { mk_node (Fnot (mk_node (Fpointsto(x,f,e)) $startpos)) $startpos }
  | e=call_exp; NOTEQUAL; x=ident; DOT; f=ident
    { mk_node (Fnot (mk_node (Fpointsto(x,f,e)) $startpos)) $startpos }
  ;

general_formula:
  | FRM_TRUE
    { mk_node (Ftrue) $startpos }
  | FRM_FALSE
    { mk_node (Ffalse) $startpos }
  | x=ident; DOT; f=ident; EQUAL; e=simple_exp
    { mk_node (Fpointsto(x,f,e)) $startpos }
  | e=simple_exp; EQUAL; x=ident; DOT; f=ident
    { mk_node (Fpointsto(x,f,e)) $startpos }

  | x=ident; DOT; f=ident; NOTEQUAL; e=simple_exp
    { mk_node (Fnot (mk_node (Fpointsto(x,f,e)) $startpos)) $startpos }
  | e=simple_exp; NOTEQUAL; x=ident; DOT; f=ident
    { mk_node (Fnot (mk_node (Fpointsto(x,f,e)) $startpos)) $startpos }

  | a=ident; LBRACK; idx=simple_exp; RBRACK; EQUAL; e=simple_exp
    { mk_node (Farray_pointsto(a,idx,e)) $startpos }
  | e=simple_exp; EQUAL; a=ident; LBRACK; idx=simple_exp; RBRACK
    { mk_node (Farray_pointsto(a,idx,e)) $startpos }

  | a=ident; LBRACK; idx=simple_exp; RBRACK; NOTEQUAL; e=simple_exp
    { let inner = mk_node (Farray_pointsto(a,idx,e)) $startpos in
      mk_node (Fnot inner) $startpos }
  | e=simple_exp; NOTEQUAL; a=ident; LBRACK; idx=simple_exp; RBRACK
    { let inner = mk_node (Farray_pointsto(a,idx,e)) $startpos in
      mk_node (Fnot inner) $startpos }

  | e1=exp; SUBSETEQ; e2=exp
    { mk_node (Fsubseteq(e1,e2)) $startpos }
  | e1=exp; DISJOINT; e2=exp
    { mk_node (Fdisjoint (e1,e2)) $startpos }
  | e1=exp; IN; e2=exp
    { mk_node (Fmember(e1,e2)) $startpos }
  | e1=exp; NOTIN; e2=exp
    { let mem_node = mk_node (Fmember(e1,e2)) $startpos in
      mk_node (Fnot mem_node) $startpos }
  | f1=formula; c=connective; f2=formula
    { mk_node (Fconn(c,f1,f2)) $startpos }
  | FRM_NOT; f=formula %prec UMINUS
    { mk_node (Fnot(f)) $startpos }
  | INIT; LPAREN; e=let_bound_value; RPAREN
    { mk_node (Finit e) $startpos }
  | f=let_formula
    { f }
  | f=quantified_formula %prec IN { f }
  | LPAREN; f=general_formula; RPAREN
    { f }
  | x=simple_exp; EQUAL; OLD; LPAREN; valu=let_bound_value; RPAREN
    { mk_node (Fold(x, valu)) $startpos }
  | OLD; LPAREN; valu=let_bound_value; RPAREN; EQUAL; x=simple_exp
    { mk_node (Fold(x, valu)) $startpos }
  | FRM_TYPE; LPAREN; e=exp; COMMA; tys=separated_nonempty_list(BAR,ident); RPAREN
    { mk_node (Ftype(e, tys)) $startpos }
  ;

let_formula:
  | LET; x=simple_lident; t=option(preceded(COLON, ty)); EQUAL; u=let_bound_value;
    IN; frm=formula
    { mk_node (Flet(x, t, { value = u; is_old = false; is_init = false }, frm)) $startpos }
  | LET; x=simple_lident; t=option(preceded(COLON, ty)); EQUAL;
    OLD; LPAREN; u=let_bound_value; RPAREN; IN; frm=formula
    { mk_node (Flet(x, t, { value = u; is_old = true; is_init = false }, frm)) $startpos }
  | LET; x=simple_lident; t=option(preceded(COLON, ty)); EQUAL;
    INIT; LPAREN; u=let_bound_value; RPAREN; IN; frm=formula
    { mk_node (Flet(x, t, { value = u; is_old = false; is_init = true }, frm)) $startpos }
  ;

%inline let_bound_value:
  | y=ident; DOT; fld=ident           { mk_node (Lloc(y,fld)) $startpos }
  | e=exp                             { mk_node (Lexp(e)) $startpos }
  | a=ident; LBRACK; idx=exp; RBRACK  { mk_node (Larr(a,idx)) $startpos }
  ;

%inline quantified_formula:
  | q=quantifier; xs=separated_list(COMMA, quantifier_binding); DOT; f=formula
    { mk_node (Fquant(q,xs,f)) $startpos }
  ;

%inline quantifier_binding:
  | x=simple_lident; COLON; t=ty; e=option(preceded(IN, exp)) { (x, t, e) }
  ;

%inline connective:
  | CONJ { Conj }
  | DISJ { Disj }
  | IMP  { Imp }
  | IFF  { Iff }
  ;

%inline quantifier:
  | FORALL { Forall }
  | EXISTS { Exists }
  ;

atomic_command:
  | SKIP
    { mk_node Skip $startpos }
  | x=ident; ASSIGN; e=simple_exp
    { mk_node (Assign(x,e)) $startpos }
  | x=ident; ASSIGN; NEW; k=uident
    { mk_node (New_class(x,k)) $startpos }
  | x=ident; ASSIGN; NEW; k=uident; LBRACK; sz=exp; RBRACK
    { mk_node (New_array(x,k,sz)) $startpos }
  | y=ident; ASSIGN; x=ident; DOT; f=ident
    { mk_node (Field_deref(y,x,f)) $startpos }
  | x=ident; DOT; f=ident; ASSIGN; e=exp
    { mk_node (Field_update(x,f,e)) $startpos }
  | x=ident; ASSIGN; m=ident; LPAREN; args=separated_list(COMMA, ident); RPAREN
    { mk_node (Call(Some x,m,List.map (fun e -> mk_node e $startpos) args)) $startpos }
  | m=ident; LPAREN; args=separated_list(COMMA, ident); RPAREN
    { mk_node (Call(None,m, List.map (fun e -> mk_node e $startpos) args)) $startpos }
  | a=ident; LBRACK; e=exp; RBRACK; ASSIGN; e2=exp
    { mk_node (Array_update(a,e,e2)) $startpos }
  | x=ident; ASSIGN; a=ident; LBRACK; e=exp; RBRACK
    { mk_node (Array_access(x,a,e)) $startpos }
  ;

command:
  | ac=atomic_command
    { mk_node (Acommand(ac)) $startpos }
  | ASSUME; LBRACE; f=formula; RBRACE
    { mk_node (Assume(f)) $startpos }
  | ASSERT; LBRACE; f=formula; RBRACE
    { mk_node (Assert(f)) $startpos }
  | LBRACE; f=formula; RBRACE;
    { mk_node (Assert(f)) $startpos }
  | VAR; GHOST; x=simple_lident; COLON; t=ty; IN; c=command
    { mk_node (Vardecl(x,Some Ghost,t,c)) $startpos }
  | VAR; x=simple_lident; COLON; t=ty; IN; c=command
    { mk_node (Vardecl(x,None,t,c)) $startpos }

    /* SYNTAX SUGAR -- assign a default value to local vars (non-ghost) */
  | VAR; x=simple_lident; COLON; t=ty; ASSIGN; e=exp; IN; c=command
    { let assign_node = mk_node (Assign(x,e)) $startpos in
      let assign_node = mk_node (Acommand assign_node) $startpos in
      let seq_node = mk_node (Seq(assign_node, c)) $startpos in
      mk_node (Vardecl(x,None,t,seq_node)) $startpos }
  | VAR; x=simple_lident; COLON; t=ty; ASSIGN; y=ident; DOT; f=ident; IN; c=command
    { let assign_node = mk_node (Field_deref(x,y,f)) $startpos in
      let assign_node = mk_node (Acommand assign_node) $startpos in
      let seq_node = mk_node (Seq(assign_node, c)) $startpos in
      mk_node (Vardecl(x,None,t,seq_node)) $startpos }

  | c1=command; SEMICOLON; c2=command
    { mk_node (Seq(c1,c2)) $startpos }
  | IF; e=exp; THEN; c1=command; END
    { let skip_node = mk_node (Acommand (mk_node Skip $startpos)) $startpos in
      mk_node (If(e,c1,skip_node)) $startpos }
  | IF; e=exp; THEN; c1=command; ELSE; c2=command; END
    { mk_node (If(e,c1,c2)) $startpos }
  | WHILE; e=exp; DO; i=while_invariant_list; c=command; DONE
    { mk_node (While(e,i,c)) $startpos }
  | LPAREN; c=command; RPAREN
    { c }
  | c=command; SEMICOLON { c }
  ;

while_invariant_list:
  | invs=nonempty_list(while_invariant)
    { let mk_conjs a b = mk_node (Fconn (Conj, a, b)) a.loc in
      let frm = match invs with
	| [] -> assert false
	| f :: fs -> List.fold_left mk_conjs f fs in
      frm }

%inline while_invariant:
  | INVARIANT; LBRACE; f=formula; RBRACE { f }
  ;

%inline modifier:
  | GHOST       { Ghost }
  | PUBLIC      { Public }
  | MODSCOPE    { Modscope }
  ;

effect_elt_desc:
  | id=ident                     { mk_node (`Ident id) $startpos }
  | e=simple_exp; IMAGE; f=ident { mk_node (`Image (e, f)) $startpos }
  ;

%inline effect_kind:
  | READ	{ `Read_effect }
  | WRITE	{ `Write_effect }
  | READWRITE	{ `Readwrite_effect }
  ;

effect_list_elt:
  | k=effect_kind; es=separated_nonempty_list(COMMA, effect_elt_desc)
    { List.flatten @@
	List.map (fun e -> mk_effect_elt k e.elt e.loc) es
    }
  ;

effect_list:
  | es=separated_list(SEMICOLON, effect_list_elt)
    { mk_node (List.flatten es) $startpos }
  ;

spec_elt:
  | REQUIRES; LBRACE; f=formula; RBRACE     { mk_node (Precond(f)) $startpos }
  | ENSURES; LBRACE; f=formula; RBRACE      { mk_node (Postcond(f)) $startpos }
  | EFFECTS; LBRACE; es=effect_list; RBRACE { mk_node (Effects(es)) $startpos }
  | EFFECT_RDS;
    LBRACE; es=separated_nonempty_list(COMMA, effect_elt_desc); RBRACE
    { let es = List.map (fun e -> mk_effect_elt `Read_effect e.elt e.loc) es in
      mk_node (Effects (mk_node (List.flatten es) $startpos)) $startpos }
  | EFFECT_WRS;
    LBRACE; es=separated_nonempty_list(COMMA, effect_elt_desc); RBRACE
    { let es = List.map (fun e -> mk_effect_elt `Write_effect e.elt e.loc) es in
      mk_node (Effects (mk_node (List.flatten es) $startpos)) $startpos }
  | EFFECT_RWS;
    LBRACE; es=separated_nonempty_list(COMMA, effect_elt_desc); RBRACE
    { let es = List.map (fun e ->
			  mk_effect_elt `Read_effect e.elt e.loc @
                          mk_effect_elt `Write_effect e.elt e.loc
			) es in
      mk_node (Effects (mk_node (List.flatten es) $startpos)) $startpos }
  ;

spec_elts:
  |                          { [] }
  | s=spec_elt; rs=spec_elts { s :: rs }
  ;

spec:
  | s=spec_elts; { mk_node s $startpos }
  ;

field_decl:
  | m=modifier; fname=simple_lident; COLON; t=ty; SEMICOLON
    { mk_node { field_name = fname; field_ty = t; attribute = m } $startpos }
  | fname=simple_lident; COLON; t=ty; SEMICOLON
    { mk_node { field_name = fname; field_ty = t; attribute = Public } $startpos }
  ;

field_decls:
  | fs=list(field_decl) { fs }
  ;

class_decl:
  | CLASS; cname=simple_uident; LBRACE; fs=field_decls; RBRACE
    { mk_node { class_name = cname; fields = fs } $startpos }
  ;

class_def:
  | c=class_decl { mk_node (Class c) $startpos }
  ;

meth_decl:
  | METH; mname=simple_ident; p=meth_param_list; COLON; rty=ty_or_ty_plus; s=spec
    { mk_node (mk_meth_decl mname p rty s) $startpos }
  ;

%inline meth_param_list:
  | LPAREN; ps=separated_list(COMMA, meth_param); RPAREN { ps }
  ;

meth_param:
  | m=modifier; x=simple_lident; COLON; t=ty_or_ty_plus
    { mk_meth_param_info (Some m) x t }
  | x=simple_lident; COLON; t=ty_or_ty_plus
    { mk_meth_param_info None x t }
  ;

ty_or_ty_plus:
  | t=ty       { `Can_be_null t }
  | t=ty; PLUS { `Non_null t }
  ;

meth_def:
  | m=meth_decl                   { mk_node (Method(m,None)) $startpos }
  | m=meth_decl; EQUAL; c=command { mk_node (Method(m,Some c)) $startpos }
  | m=meth_decl; LBRACK; c=command; RBRACK
    { mk_node (Method (m,Some c)) $startpos }
  ;

named_formula:
  | PREDICATE; name=simple_lident; ps=named_formula_params;
    annot=option(named_formula_annotation); EQUAL; f=formula
    { let inner =
        {kind=`Predicate; annotation=annot; formula_name=name; params=ps; body=f}
      in mk_node inner $startpos }
  | a=axiom_or_lemma; name=simple_lident; COLON; f=formula
    { mk_node { kind=a; annotation=None; formula_name=name; params=[]; body=f } $startpos }
  ;

named_formula_annotation:
  | LBRACK; PUBLIC_INV_ANNOT; RBRACK { Public_invariant }
  | LBRACK; PRIVATE_INV_ANNOT; RBRACK { Private_invariant }
  ;

%inline axiom_or_lemma:
  | AXIOM { `Axiom }
  | LEMMA { `Lemma }
  ;

%inline named_formula_params:
  | LPAREN; ps=separated_list(COMMA, named_formula_param); RPAREN { ps }
  | COLON; { [] }
  ;

named_formula_param:
  | x=simple_lident; COLON; t=ty { (x, t) }
  ;

import_directive:
  | IMPORT; k=import_kind; id=uident; name=option(preceded(AS, simple_uident))
    { mk_node (k, id, name) $startpos }
  ;

%inline import_kind:
  | (* epsilon *) { Iregular }
  | THEORY        { Itheory }
  ;

extern_decl:
  | EXTERN; TYPE; tid=simple_lident; WITH; DEFAULT; EQUAL; def=simple_lident
    { mk_node (mk_extern_symbol tid Ex_type [] None (Some def)) $startpos }
  | EXTERN; PREDICATE; id=simple_lident;
    LPAREN; params=separated_list(COMMA, ty); RPAREN
    { mk_node (mk_extern_symbol id Ex_predicate params None None) $startpos }
  | EXTERN; LEMMA; id=simple_lident
    { mk_node (mk_extern_symbol id Ex_lemma [] None None) $startpos }
  | EXTERN; AXIOM; id=simple_lident
    { mk_node (mk_extern_symbol id Ex_axiom [] None None) $startpos }
  | EXTERN; CONST; id=simple_lident; COLON; t=ty
    { mk_node (mk_extern_symbol id Ex_const [] (Some t) None) $startpos }
  | EXTERN; id=simple_lident; LPAREN; params=separated_list(COMMA, ty); RPAREN;
    COLON; retty=ty
    { mk_node (mk_extern_symbol id Ex_function params (Some retty) None) $startpos }
  ;

interface_vardecl:
  | m=public_or_ghost; x=simple_lident; COLON; t=ty
    { (m,x,t) }
  ;

%inline public_or_ghost:
  | PUBLIC { Public }
  | GHOST  { Ghost }
  ;

interface_elt:
  | c=class_decl { mk_node (Intr_cdecl(c)) $startpos }
  | m=meth_decl  { mk_node (Intr_mdecl(m)) $startpos }
  | n=named_formula { mk_node (Intr_formula(n)) $startpos }
  | i=import_directive { mk_node (Intr_import(i)) $startpos }
  | v=interface_vardecl
    { let (m,x,t) = v in
      mk_node (Intr_vdecl(m,x,t)) $startpos
    }
  | BOUNDARY; LBRACE; es=separated_list(COMMA, effect_elt_desc); RBRACE
    { mk_node
	(Intr_boundary (mk_node (List.map mk_boundary_elt es) $startpos))
      $startpos
    }
  | DATAGROUP; LBRACE; is=separated_list(COMMA, simple_lident); RBRACE
    { mk_node (Intr_datagroup(is)) $startpos }
  | e=extern_decl
    { mk_node (Intr_extern e) $startpos }
  ;

interface_elt_list:
  |                                             { [] }
  | i=interface_elt; is=interface_elt_list      { i :: is }
  ;

interface_def:
  | INTERFACE; iname=simple_uident; EQUAL; is=interface_elt_list; END
    { mk_node { intr_name=iname; intr_elts=is } $startpos }
  ;

module_def:
  | MODULE; mname=simple_uident; COLON; iname=simple_uident; EQUAL;
    ms=module_elt_list; END
    { mk_node { mdl_name = mname;
                mdl_interface = iname;
                mdl_elts = ms }
      $startpos }
  ;

module_elt_list:
  |                                     { [] }
  | m=module_elt; ms=module_elt_list    { m :: ms }
  ;

module_elt:
  | c=class_def
    { mk_node (Mdl_cdef c) $startpos }
  | m=meth_def
    { mk_node (Mdl_mdef m) $startpos }
  | f=named_formula
    { mk_node (Mdl_formula f) $startpos }
  | i=import_directive
    { mk_node (Mdl_import i) $startpos }
  | m=modifier; x=simple_lident; COLON; t=ty
    { mk_node (Mdl_vdecl(m,x,t)) $startpos }
  | d=datagroup_def
    { let (group,flds) = d in
      mk_node (Mdl_datagroup(group,flds)) $startpos }
  | e=extern_decl
    { mk_node (Mdl_extern(e)) $startpos }
  ;

datagroup_def:
  | DATAGROUP; g=simple_lident; CONTAINS; fs=separated_list(COMMA, ident) { (g,fs) }
  ;

rformula:
  | f=ident; LPAREN; us=separated_list(COMMA, exp); BAR;
    vs=separated_list(COMMA, exp); RPAREN
    { let us = List.map (fun e -> mk_node (Left e) $startpos) us in
      let vs = List.map (fun e -> mk_node (Right e) $startpos) vs in
      mk_node (Rprimitive(f,us @ vs)) $startpos }
  | e1=simple_exp; BIEQUAL; e2=simple_exp
    { mk_node (Rbiequal(e1,e2)) $startpos }
  | AGREE; x=simple_lident
    { let var_x = mk_node (Evar x) $startpos in
      mk_node (Rbiequal(var_x,var_x)) $startpos }
  | AGREE; e=simple_exp; IMAGE; f=ident
    { mk_node (Ragree(e,f)) $startpos }
  | BOTH; f=formula
    { mk_node (Rboth(f)) $startpos }
  | FRM_NOT; r=rformula %prec UMINUS
    { mk_node (Rnot(r)) $startpos }
  | LEFT_OPEN; f=formula; LEFT_CLOSE
    { mk_node (Rleft(f)) $startpos }
  | RIGHT_OPEN; f=formula; RIGHT_CLOSE
    { mk_node (Rright(f)) $startpos }
  | r1=rformula; c=connective; r2=rformula
    { mk_node (Rconn(c,r1,r2)) $startpos }
  | r=quantified_rformula %prec IN
    { r }
  | LPAREN; r=rformula; RPAREN
    { r }
  | lrf=let_rformula
    { lrf }
  ;

let_rformula:
  | LET;
    x=simple_lident; xt=option(preceded(COLON, ty)); BAR;
    y=simple_lident; yt=option(preceded(COLON, ty)); EQUAL;
    xval=let_bound_value; BAR; yval=let_bound_value; IN;
    rfrm=rformula
    { let lbind = (x, xt, mk_node {value=xval; is_old=false; is_init=false} $startpos) in
      let rbind = (y, yt, mk_node {value=yval; is_old=false; is_init=false} $startpos) in
      mk_node (Rlet (lbind, rbind, rfrm)) $startpos }
  | LET;
    x=simple_lident; xt=option(preceded(COLON, ty)); BAR;
    y=simple_lident; yt=option(preceded(COLON, ty)); EQUAL;
    OLD; LPAREN; xval=let_bound_value; RPAREN; BAR; OLD; LPAREN; yval=let_bound_value; RPAREN; IN;
    rfrm=rformula
    { let lbind = (x, xt, mk_node {value=xval; is_old=true; is_init=false} $startpos) in
      let rbind = (y, yt, mk_node {value=yval; is_old=true; is_init=false} $startpos) in
      mk_node (Rlet (lbind, rbind, rfrm)) $startpos }
  | LET;
    x=simple_lident; xt=option(preceded(COLON, ty)); BAR;
    y=simple_lident; yt=option(preceded(COLON, ty)); EQUAL;
    INIT; LPAREN; xval=let_bound_value; RPAREN; BAR; INIT; LPAREN; yval=let_bound_value; RPAREN; IN;
    rfrm=rformula
    { let lbind = (x, xt, mk_node {value=xval; is_old=false; is_init=true} $startpos) in
      let rbind = (y, yt, mk_node {value=yval; is_old=false; is_init=true} $startpos) in
      mk_node (Rlet (lbind, rbind, rfrm)) $startpos }
  ;

%inline quantified_rformula:
  | q=quantifier; xs=rquantifier_bindings; DOT; r=rformula
    { mk_node (Rquant(q,xs,r)) $startpos }
  ;

%inline rquantifier_bindings:
  | xs=separated_list(COMMA, quantifier_binding); BAR;
    ys=separated_list(COMMA, quantifier_binding)
    { (xs,ys) }
  ;

named_rformula:
  | a=axiom_or_lemma; name=simple_lident; COLON; rf=rformula
    { mk_node { kind=a; biformula_name=name; biparams=([],[]);
                body=rf; is_coupling=false } $startpos }
  | a=axiom_or_lemma; name=simple_lident; LBRACK; COUPLING_ANNOT; RBRACK;
    COLON; rf=rformula
    { mk_node { kind=a; biformula_name=name; biparams=([],[]);
                body=rf; is_coupling=true } $startpos }
  | PREDICATE; name=simple_lident;
    LPAREN; psl=separated_list(COMMA, named_formula_param); BAR;
            psr=separated_list(COMMA, named_formula_param); RPAREN;
    EQUAL; rf=rformula
    { mk_node { kind=`Predicate;
		biformula_name=name;
		biparams=(psl, psr);
		body=rf;
                is_coupling = false; }
      $startpos }
  | PREDICATE; name=simple_lident;
    LPAREN; psl=separated_list(COMMA, named_formula_param); BAR;
            psr=separated_list(COMMA, named_formula_param); RPAREN;
    LBRACK; COUPLING_ANNOT; RBRACK;
    EQUAL; rf=rformula
    { mk_node { kind=`Predicate;
		biformula_name=name;
		biparams=(psl, psr);
		body=rf;
                is_coupling = true; }
      $startpos }

bicommand:
  | c1=command; BAR; c2=command
    { mk_node (Bisplit(c1,c2)) $startpos }
  | LEFT_SYNC; a=atomic_command; RIGHT_SYNC
    { mk_node (Bisync(a)) $startpos }
  | BIVAR; x1=varbind; BAR; x2=varbind; IN; b=bicommand
    { mk_node (Bivardecl(x1,x2,b)) $startpos }
  | b1=bicommand; SEMICOLON; b2=bicommand
    { mk_node (Biseq(b1,b2)) $startpos }
  | BIIF; e1=exp; BAR; e2=exp; THEN; b1=bicommand; END
    { let skip_node = mk_node Skip $startpos in
      let biskip_node = mk_node (Bisync (skip_node)) $startpos in
      mk_node (Biif(e1,e2,b1,biskip_node)) $startpos }
  | BIIF; e1=exp; BAR; e2=exp; THEN; b1=bicommand; ELSE; b2=bicommand; END
    { mk_node (Biif(e1,e2,b1,b2)) $startpos }
  | BIASSUME; LBRACE; r=rformula; RBRACE
    { mk_node (Biassume(r)) $startpos }
  | BIASSERT; LBRACE; r=rformula; RBRACE
    { mk_node (Biassert(r)) $startpos }
  | LBRACE; LBRACE; r=rformula; RBRACE; RBRACE
    { mk_node (Biassert(r)) $startpos }
  | BIWHILE; e1=exp; BAR; e2=exp; DOT; ag=alignment_guard; DO;
    rinv=biwhile_invariant_list; b=bicommand; DONE
    { mk_node (Biwhile(e1,e2,ag,rinv,b)) $startpos }
  | BIUPDATE; x1=ident; WITH; x2=ident
    { mk_node (Biupdate(x1,x2)) $startpos }
  | LPAREN; b=bicommand; RPAREN
    { b }
  | b=bicommand; SEMICOLON { b }
  ;

biwhile_invariant_list:
  | invs=nonempty_list(biwhile_invariant)
    { let mk_conjs a b = mk_node (Rconn (Conj, a, b)) a.loc in
      match invs with
      | [] -> assert false
      | f :: fs -> List.fold_left mk_conjs f fs }
  ;

%inline biwhile_invariant:
  | INVARIANT; LBRACE; rf=rformula; RBRACE { rf }
  ;

varbind:
  | GHOST; x=simple_lident; COLON; t=ty { (x,Some Ghost,t) }
  | x=simple_lident; COLON; t=ty        { (x,None,t) }
  ;

alignment_guard:
  |                                     { None }
  | r1=rformula; BAR; r2=rformula       { Some(r1,r2) }
  ;

bispec_elt:
  | REQUIRES; LBRACE; rf=rformula; RBRACE
    { mk_node (Biprecond (rf)) $startpos }
  | ENSURES; LBRACE; rf=rformula; RBRACE
    { mk_node (Bipostcond (rf)) $startpos }
  | EFFECTS; LBRACE; es=effect_list; BAR; es2=effect_list; RBRACE
    { mk_node (Bieffects (es, es2)) $startpos }
  ;

bispec:
  | bs=list(bispec_elt) { mk_node bs $startpos }
  ;

bimeth_decl:
  | METH; mname=simple_ident; LPAREN;
    psl=separated_list(COMMA, meth_param); BAR
    psr=separated_list(COMMA, meth_param); RPAREN;
    COLON;
    LPAREN; retl=ty_or_ty_plus; BAR; retr=ty_or_ty_plus; RPAREN;
    bs=bispec
    { let meth_decl = mk_bimeth_decl mname psl psr retl retr bs in
      mk_node meth_decl $startpos }
  ;

bimeth_def:
  | b=bimeth_decl
    { mk_node (Bimethod (b, None)) $startpos }
  | b=bimeth_decl; EQUAL; cc=bicommand
    { mk_node (Bimethod (b, Some cc)) $startpos }
  | b=bimeth_decl; LBRACK; cc=bicommand; RBRACK
    { mk_node (Bimethod (b, Some cc)) $startpos }
  ;


bimodule_elt:
  | mdef=bimeth_def    { mk_node (Bimdl_mdef mdef) $startpos }
  | e=extern_decl      { mk_node (Bimdl_extern e) $startpos }
  | i=import_directive { mk_node (Bimdl_import i) $startpos }
  | nf=named_rformula  { mk_node (Bimdl_formula nf) $startpos }
  ;

bimodule_def:
  | BIMODULE; bmdlname=simple_uident;
    LPAREN; left_mdl=simple_uident; BAR; right_mdl=simple_uident; RPAREN;
    EQUAL; bs=list(bimodule_elt); END
    { mk_node {
	  bimdl_name = bmdlname;
	  bimdl_left_impl = left_mdl;
	  bimdl_right_impl = right_mdl;
	  bimdl_elts = bs
	}
      $startpos
    }
  ;


%inline program_elt:
  | i=interface_def     { mk_node (Unr_intr i) $startpos }
  | m=module_def        { mk_node (Unr_mdl m) $startpos }
  | b=bimodule_def      { mk_node (Rel_mdl b) $startpos }
  ;

program:
  | { [] }
  | p=program_elt; ps=program { p :: ps }
  ;
