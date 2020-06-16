%token NUM HOLE LHOLEP RHOLEP LBRA RBRA
%token ARROW
%token <int> INT
%token <string> ID
%token FUN OFTYPE
%token PLUS
%token LPAREN RPAREN
%token EOL

%start <Syntax.Exp.t> main
%{ open Syntax %}

%%

main:
| e = expr EOL
    { e }

expr:
| e = arith
    { e }
| FUN LPAREN i = id OFTYPE t = ty RPAREN ARROW e = expr
    { Exp.ELamAnn (i, t, e) }
| FUN i = id ARROW e = expr
    { Exp.ELam (i, e) }

arith:
| e = app
    { e }
| e1 = arith PLUS e2 = app
    { Exp.EBinOp (e1, Exp.OpPlus,e2) }


app:
| e = simple
    { e }
| e1 = app e2 = simple
    { Exp.EBinOp (e1, OpAp, e2) }

simple:
| e = id
    { Exp.EVar (e) }
| i = INT
    { Exp.ENumLiteral i }
| LPAREN e = expr RPAREN
    { e }
| LHOLEP id = INT RHOLEP
    {Exp.EEmptyHole id}
| LHOLEP LBRA id = INT RBRA e = expr RHOLEP
    {Exp.EExpHole (id,e)}

id:
| i = ID
    { i }

ty:
| t = base_ty
    { t }
| t1 = base_ty ARROW t2 = ty
    { Typ.TArrow (t1, t2) }

base_ty:
| NUM
    { Typ.TNum }
| HOLE LBRA id = INT RBRA
    { Typ.THole id }

