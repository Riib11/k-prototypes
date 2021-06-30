requires "../syntax/lam-simply-typed-syntax.k"

module LAM-SIMPLY-TYPED-TYPING
  imports LAM-SIMPLY-TYPED-SYNTAX

  syntax KResult ::= Type

  syntax TypeStack ::= ".TypeStack" | Type TypeStack  [right]

  // -------------------------------------------------------------------------
  // configuration

  configuration
    <k> $PGM:Term </k>
    <typestack> .TypeStack </typestack>

  // -------------------------------------------------------------------------
  // base

  // unit
  rule u => unit

  // -------------------------------------------------------------------------
  // abstraction

  syntax Type ::= "#abs" "(" Type ")"

  rule <k> lam S . B => B ~> #abs(S) ... </k>
        <typestack> Types => S Types </typestack>

  rule <k> T:Type ~> #abs(S) => S -> T ... </k>
        <typestack> S Types => Types </typestack>

  // -------------------------------------------------------------------------
  // application

  syntax Type ::= "#app" "(" Type ")"

  rule <k> F:Term A:Term => F ~> A ... </k>

  rule <k> (S -> T) ~> A:Term => A ~> #app(S -> T) ... </k>

  rule <k> S:Type ~> #app(S -> T) => T ... </k>

  // -------------------------------------------------------------------------
  // variable

  rule <k> X:Var => #lookup(X, Types) ... </k>
        <typestack> Types </typestack>

  // lookup

  syntax Type ::= "#lookup" "(" Var "," TypeStack ")"  [function]
  // -------------------------------------------------------------------------
  rule #lookup(z  , T _)     => T
  rule #lookup(s X, _ Types) => #lookup(X, Types)

endmodule