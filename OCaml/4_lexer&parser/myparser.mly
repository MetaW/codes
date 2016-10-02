%token L_PAREN
%token R_PAREN
%token PLUS
%token EQUAL

%token LET
%token IN

%token <int> NUM
%token <string> ID

%token EOF (* EOF is important in some cases, if we don't add it,
              in this case once it read a expr the parser will stop,
              no matter whether there are chars following.
              Eg: "abc 123 let x = 1 in x" will be trans into (Var_expe "abc"),
                   and the following (123 let x = 1 in x) was omitted without 
                   a parser error!!!*)


%start <Ast.expr> nt_prog (* nt_prog is the start point, the value type it carry is the type of the parse result *)
%%

nt_prog:
    | ast = nt_exp; EOF { ast }

nt_exp:
    | ast = NUM                                                 { Ast.Const_expr ast }
    | L_PAREN; ast1 = nt_exp; PLUS; ast2 = nt_exp; R_PAREN      { Ast.Add_expr (ast1, ast2) } 
    | ast = ID                                                  { Ast.Var_expr ast }
    | LET; ast1 = ID; EQUAL; ast2 = nt_exp; IN; ast3 = nt_exp   { Ast.Let_expr (ast1, ast2, ast3) }