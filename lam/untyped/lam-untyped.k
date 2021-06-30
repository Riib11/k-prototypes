requires "substitution.md"

module LAM-UNTYPED-SYNTAX
    imports KVAR-SYNTAX

    syntax Exp ::= Val
                 | Id
                 | Exp Exp                       [strict, left]
                 | "let" Id "=" Exp "in" Exp     [right]
                 | "rec" Id Id "=" Exp "in" Exp  [right]
                 | "(" Exp ")"                   [bracket]

    syntax Val ::= "unit"
                 | "lam" Id "." Exp              [right, latex(\lambda{#1}.{#2})]
                 | "mu"  Id "." Exp              [right, latex(\mu{#1}.{#2})]

    syntax Id  ::= KVar

    syntax KResult ::= Val
endmodule

module LAM-UNTYPED
    imports LAM-UNTYPED-SYNTAX
    imports SUBSTITUTION

    // beta-reduction
    rule (lam X:Id . B:Exp) A:Exp => B [A / X]
    
    // recursive beta-reduction
    rule (mu X:Id . B:Exp) A:Exp => A [(mu X . B) / X]

    // let-abstraction
    rule let X:Id = A:Exp in B:Exp => (lam X . B) A [macro]

    // rec-abstraction
    rule rec F:Id X:Id = A:Exp in B:Exp => let F = mu F . lam X . B in A [macro]
endmodule
