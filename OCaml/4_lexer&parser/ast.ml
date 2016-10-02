type expr = 
    | Const_expr    of int
    | Add_expr      of expr * expr
    | Var_expr      of string
    | Let_expr      of string * expr * expr
