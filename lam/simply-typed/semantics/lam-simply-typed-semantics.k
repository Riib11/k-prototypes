requires "../syntax/lam-simply-typed-syntax.k"

module LAM-SIMPLY-TYPED-SEMANTICS
    imports LAM-SIMPLY-TYPED-SYNTAX

    syntax KResult ::= Term

    syntax TermStack ::= ".TermStack" | Term TermStack  [right]

    // -------------------------------------------------------------------------
    // configuration

    configuration
      <k> $PGM:Term </k>
      <termstack> .TermStack:TermStack </termstack>

    // -------------------------------------------------------------------------
    // application

    syntax Term ::= "#app" "(" Term ")"

    rule <k> F:Term A:Term => F ~> A ... </k>

    rule <k> lam _ . B ~> A:Term => A ~> #app(B) ... </k>

    rule <k> A:Val ~> #app(B) => B ... </k>
         <termstack> Terms => A Terms </termstack>

    // -------------------------------------------------------------------------
    // variable

    rule <k> X:Var => #lookup(X, Terms) ... </k>
         <termstack> Terms </termstack>

    // lookup

    syntax Term ::= "#lookup" "(" Var "," TermStack ")"  [function]
    // -------------------------------------------------------------------------
    rule #lookup(z  , A _)     => A
    rule #lookup(s X, _ Terms) => #lookup(X, Terms)

endmodule