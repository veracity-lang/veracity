%{
open Ast

let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : 'a node =
  { elt ; loc=Range.mk_lex_range startpos endpos }

%}

/* Declare your tokens here. */
%token EOF
%token <int64>  INT
%token NULL
%token <string> STRING
%token <string> IDENT
%token <string> UIDENT

%token TINT     /* int */
%token TVOID    /* void */
%token TSTRING  /* string */
%token STRUCT   /* struct */
%token IF       /* if */
%token ELSE     /* else */
%token WHILE    /* while */
%token COMMUTE_SEQ /* commute_seq */
%token COMMUTE_PAR /* commute_par */
%token HASHTABLE /* hashtable */
%token HASHTABLE_SEQ
%token HASHTABLE_NAIVE
%token RETURN   /* return */
%token SEMI     /* ; */
%token COLON    /* : */
%token QMARK    /* ? */
%token COMMA    /* , */
%token LBRACE   /* { */
%token RBRACE   /* } */
%token PLUS     /* + */
%token SLASH
%token STARSTAR
%token CARET    /* ^ */
%token DASH     /* - */
%token STAR     /* * */
%token PERCENT  /* % */
%token EQEQ     /* == */
%token EQ       /* = */
%token LPAREN   /* ( */
%token RPAREN   /* ) */
%token LBRACKET /* [ */
%token RBRACKET /* ] */
%token TILDE    /* ~ */
%token BANG     /* ! */
%token DOT      /* . */

%token NEW      /* new */
%token TBOOL    /* bool */
%token TRUE     /* true */
%token FALSE    /* false */
%token FOR      /* for */
%token TCHANR
%token TCHANW

%token NEQ      /* != */
%token LT       /* < */
%token LEQ      /* <= */
%token GT       /* > */
%token GEQ      /* >= */

%token LSHIFT   /* << */
%token RSHIFT   /* >> */
%token RSHIFTU  /* >>> */

%token LAND     /* & */
%token LOR      /* | */
%token BAND     /* [&] */
%token BOR      /* [|] */

%token FUNC      /* => */
%token RAISE
%token PURE

%token ASSERT ASSUME HAVOC

%token UNDERSCORE

%left BOR
%left BAND
%left LOR
%left LAND
%left EQEQ NEQ
%left GEQ GT LEQ LT
%left RSHIFTU RSHIFT LSHIFT
%left DASH PLUS CARET
%left STAR
%left DOT
%left PERCENT
%right QMARK COLON
%nonassoc BANG
%nonassoc TILDE
%nonassoc LBRACKET
(* %nonassoc LPAREN *)


/* ---------------------------------------------------------------------- */

%start prog
%start exp_top
%start stmt_top
%type <Ast.exp Ast.node> exp_top
%type <Ast.stmt Ast.node> stmt_top

%type <Ast.prog> prog
%type <Ast.exp Ast.node> exp
%type <Ast.stmt Ast.node> stmt
%type <Ast.block Ast.node> block
%type <Ast.ty> ty
%%

exp_top:
  | e=exp EOF { e }

stmt_top:
  | s=stmt EOF { s }

prog:
  | p=list(decl) EOF  { p }

decl:
  | ty=ty name=IDENT EQ init=exp(*gexp*) SEMI
    { Gvdecl (loc $startpos $endpos { name; ty; init }) }
  | (*p=pure*) mrtyp=ty mname=IDENT LPAREN args=arglist RPAREN body=block
    { Gmdecl (loc $startpos $endpos { pure=false; mrtyp; mname; args; body }) }
  | mrtyp=ty mname=IDENT LPAREN args=arglist RPAREN FUNC e=exp SEMI
    { Gmdecl (loc $startpos $endpos { 
      pure=true; mrtyp; mname; args; 
      body = no_loc [no_loc @@ Ret(Some e)]
    }) }
  | STRUCT sname=UIDENT LBRACE fields=separated_list(SEMI, decl_field) RBRACE 
    { Gsdecl (loc $startpos $endpos {sname; fields}) }

(*(*%inline*) pure:
  | PURE { true }
  | (* BLANK *) { false }*)

decl_field:
  | t=ty id=IDENT { { field_name=id; ftyp=t } }

arglist:
  | l=separated_list(COMMA, pair(ty,IDENT)) { l }
    
ty:
  | TINT   { TInt }
  | TBOOL  { TBool }
  | TSTRING { TStr }
  | TVOID { TVoid }
  | TCHANR { TChanR }
  | TCHANW { TChanW }
  | t=ty LBRACKET RBRACKET { TArr t }
  | HASHTABLE LBRACKET tyk=ty COMMA tyv=ty RBRACKET { THashTable (tyk,tyv) }
  | id=UIDENT { TStruct id }

%inline bop:
  | STAR {Mul}
  | PLUS {Add}
  | CARET {Concat}
  | DASH {Sub}
  | LSHIFT {Shl}
  | RSHIFT {Shr}
  | RSHIFTU {Sar}
  | LT {Lt}
  | LEQ {Lte}
  | GT {Gt}
  | GEQ {Gte}
  | EQEQ {Eq}
  | NEQ {Neq}
  | LAND {And}
  | LOR {Or}
  | BAND {IAnd}
  | BOR {IOr}
  | PERCENT {Mod}
  | SLASH {Div}
  | STARSTAR {Exp}

%inline uop:
  | DASH  { Neg }
  | BANG  { Lognot }
  | TILDE { Bitnot }

lhs:  
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | e=basic_exp LBRACKET i=basic_exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }
  | e=basic_exp DOT id=IDENT  { loc $startpos $endpos @@ Proj (e, id) }

exp:
  | be=basic_exp        { be }
  | nd=new_data         { nd }

basic_exp:
  | ae=atomic_expr                  { ae }
  | e1=basic_exp b=bop e2=basic_exp { loc $startpos $endpos @@ Bop (b, e1, e2) }
  | u=uop e=basic_exp               { loc $startpos $endpos @@ Uop (u, e) }
  | e=basic_exp LBRACKET i=basic_exp RBRACKET
                                    { loc $startpos $endpos @@ Index (e, i) }
  | e=basic_exp QMARK e_then=basic_exp COLON e_else=basic_exp
                                    { loc $startpos $endpos @@ Ternary(e,e_then,e_else) }
  | e=IDENT(*exp*) LPAREN es=separated_list(COMMA, exp) RPAREN
                        { loc $startpos $endpos @@ CallRaw (e,es) }
  | e=basic_exp DOT id=IDENT  { loc $startpos $endpos @@ Proj(e, id) }
  | LPAREN e=exp RPAREN { e }
  
atomic_expr:
  | i=INT               { loc $startpos $endpos @@ CInt i }
  | t=ty NULL           { loc $startpos $endpos @@ CNull t }
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | s=STRING   { loc $startpos $endpos @@ CStr s}
  | TRUE       { loc $startpos $endpos @@ CBool true}
  | FALSE      { loc $startpos $endpos @@ CBool false}

new_data:
  | NEW t=ty LBRACKET RBRACKET LBRACE es=separated_list(COMMA, exp) RBRACE 
                        {loc $startpos $endpos @@ CArr(t, es)}
  | NEW t=ty LBRACKET e=basic_exp RBRACKET {loc $startpos $endpos @@ NewArr(t,e)}
  | NEW htv=hashtable_variant LBRACKET tyk=ty COMMA tyv=ty RBRACKET
    {loc $startpos $endpos @@ NewHashTable (htv,tyk,tyv)}
  | NEW t=UIDENT LBRACE cs=separated_list(SEMI, field) RBRACE
                        { loc $startpos $endpos @@ CStruct(t, cs) }

%inline hashtable_variant:
  | HASHTABLE { HTVarNaiveConcurrent }
  | HASHTABLE_SEQ { HTVarSequential }
  | HASHTABLE_NAIVE { HTVarNaiveConcurrent }

field:
  | id=IDENT EQ e=exp { (id, e) }

vdecl:
  | ty=ty id=IDENT EQ init=exp { (id, (ty, init)) }

stmt: 
  | d=vdecl SEMI        { loc $startpos $endpos @@ Decl(d) }
  | p=lhs EQ e=exp SEMI { loc $startpos $endpos @@ Assn(p,e) }
  | e=IDENT(*exp*) LPAREN es=separated_list(COMMA, exp) RPAREN SEMI
                        { loc $startpos $endpos @@ SCallRaw (e, es) }
  | ifs=if_stmt         { ifs }
  | RETURN SEMI         { loc $startpos $endpos @@ Ret(None) }
  | RETURN e=exp SEMI   { loc $startpos $endpos @@ Ret(Some e) }
  | WHILE LPAREN e=exp RPAREN b=block  
                        { loc $startpos $endpos @@ While(e, b) }
  | FOR LPAREN vdecls=separated_list(COMMA, vdecl) SEMI e=option(exp) SEMI s=option(stmt) RPAREN b=block
      {loc $startpos $endpos @@ For(vdecls, e, s, b)}
  | variant=commute_variant phi=commute_condition
    LBRACE blocks=nonempty_list(block) RBRACE
    { loc $startpos $endpos @@ Commute(variant,phi,blocks) }
  | RAISE e=exp SEMI { loc $startpos $endpos @@ Raise e }
  | ASSERT e=exp SEMI { loc $startpos $endpos @@ Assert e }
  | ASSUME e=exp SEMI { loc $startpos $endpos @@ Assume e }
  | HAVOC i=IDENT SEMI { loc $startpos $endpos @@ Havoc i }

%inline commute_variant:
  | COMMUTE_SEQ { CommuteVarSeq }
  | COMMUTE_PAR { CommuteVarPar }

commute_condition:
  | LPAREN phi=exp RPAREN { PhiExp(phi) }
  | UNDERSCORE { PhiInf }
  | (* Implied *) { PhiExp(loc $startpos $endpos @@ CBool true) }

block:
  | LBRACE stmts=list(stmt) RBRACE { loc $startpos $endpos @@ stmts }

if_stmt:
  | IF LPAREN e=exp RPAREN b1=block b2=else_stmt
    { loc $startpos $endpos @@ If(e,b1,b2) }

else_stmt:
  | (* empty *)       { loc $startpos $endpos @@ [] }
  | ELSE b=block      { b }
  | ELSE ifs=if_stmt  { loc $startpos $endpos @@ [ ifs ] }
