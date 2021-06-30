module LAM-SIMPLY-TYPED-SYNTAX

    syntax Type ::= "unit"
                  | Type "->" Type  [right]
                  | "(" Type ")"    [bracket]

    syntax Term ::= Val
                  | Var
                  | Term Term [left]
                  | "(" Term ")" [bracket]

    syntax Val  ::= "u"
                  | "lam" Type "." Term  [right]

    syntax Var  ::= "z"
                  | "s" Var  [right]

endmodule