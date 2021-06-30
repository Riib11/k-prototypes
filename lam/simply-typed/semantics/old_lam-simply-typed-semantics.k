requires "../syntax/lam-simply-typed-syntax.k"

module LAM-SIMPLY-TYPED-SEMANTICS
    imports LAM-SIMPLY-TYPED-SYNTAX

    syntax KResult ::= Term

    configuration
      <k> $PGM:Term </k>
      <argmstack> .ArgmStack:ArgmStack </argmstack>
      <funcstack> .FuncStack:FuncStack </funcstack>
      <termstack> .TermStack:TermStack </termstack>

    // beta-reduction

    // focus applicant
    // puts argument onto argmstack
    rule
      <k> F:Term A:Term => F </k>
      <argmstack> Argms => A Argms </argmstack>

    // focus argument
    // pushes applicant onto funcstack
    // pops argument ofof argmstack
    rule 
      <k> lam T . B => A </k>
      <argmstack> A Argms => Argms </argmstack>
      <funcstack> Funcs => (lam T . B) Funcs </funcstack>

    // focus application
    // puts argument onto termstack
    // pops applicant body ofof funcstack
    rule 
      <k> A:Val => B </k>
      <funcstack> (lam _ . B) FS => FS </funcstack>
      <termstack> Terms => A Terms </termstack>

    // substitution

    rule
      <k> X:Var => #lookup(X, Terms) </k>
      <termstack> Terms </termstack>

    // lookup

    syntax Term ::= "#lookup" "(" Var "," TermStack ")"  [function]
    // -------------------------------------------------------------------------
    rule #lookup(z  , A _)     => A
    rule #lookup(s X, _ Terms) => #lookup(X, Terms)

endmodule