%token NUM BOOL HOLE LHOLEP RHOLEP LBRA RBRA
%token ARROW
%token <int> INT
%token <string> ID
%token <bool> BOOLLIT
%token IF THEN ELSE
%token FUN LET OFTYPE BE IN
%token COMMA
%token L R LPRJ RPRJ
%token CASE OF
%token PLUS TIMES
%token LPAREN RPAREN
%token EOL

%start <Syntax.Exp.t> main
%{ open Syntax %}

%%

main:
| e = expr EOL
    { e }

expr:
| e = boolean
    { e }
| LET i = id OFTYPE t = ty BE e1 = expr IN e2 = expr
    { Exp.ELet (i, Some(t), e1, e2) }
| LET i = id BE e1 = expr IN e2 = expr
    { Exp.ELet (i, None, e1, e2) }
| IF e1 = expr THEN e2 = expr ELSE e3 = expr
    { Exp.EIf (e1, e2, e3) }
| FUN LPAREN i = id OFTYPE t = ty RPAREN ARROW e = expr
    { Exp.ELamAnn (i, t, e) }
| FUN i = id ARROW e = expr
    { Exp.ELam (i, e) }
| L e = expr
    { Exp.EInjL (e) }
| R e = expr
    { Exp.EInjR (e) }
| CASE e1 = expr OF L LPAREN x = id RPAREN ARROW e2 = expr ELSE R LPAREN y = id RPAREN ARROW e3 = expr
    { Exp.ECase (e1, x, e2, y, e3)}
| LET LPAREN x = id COMMA y = id RPAREN BE e1 = expr IN e2 = expr
    { Exp.ELetPair (x, y, e1, e2)}

boolean:
| e = arith
    { e }

arith:
| e = app
    { e }
| e1 = arith PLUS e2 = app
    { Exp.EBinOp (e1, Exp.OpPlus,e2) }


app:
| e = right
    { e }
| e1 = app e2 = right
    { Exp.EBinOp (e1, OpAp, e2) }


right:
| e = simple
    { e }
| e = right LPRJ
    { Exp.EPrjL (e) }
| e = right RPRJ   
    { Exp.EPrjR (e) }

simple:
| e = id
    { Exp.EVar (e) }
| i = INT
    { Exp.ENumLiteral i }
| b = BOOLLIT
    { Exp.EBoolLiteral b }
| LPAREN e = expr RPAREN
    { e }
| LHOLEP id = INT RHOLEP
    {Exp.EEmptyHole id}
| LHOLEP LBRA id = INT RBRA e = expr RHOLEP
    {Exp.EExpHole (id,e)}
| LPAREN e1 = expr COMMA e2 = expr RPAREN
    { Exp.EPair (e1, e2) }

id:
| i = ID
    { i }

ty:
| t = ty_sum
    { t }
| t1 = ty_sum ARROW t2 = ty
    { Typ.TArrow (t1, t2) }

ty_sum:
| t = ty_prod
    { t }
| t1 = ty_prod PLUS t2 = ty_sum
    { Typ.TSum (t1, t2) }

ty_prod:
| t = base_ty
    { t }
| t1 = base_ty TIMES t2 = ty_prod
    { Typ.TProd (t1, t2) }

base_ty:
| NUM
    { Typ.TNum }
| BOOL
    { Typ.TBool }
| HOLE LBRA id = INT RBRA
    { Typ.THole id }

