requires "../syntax/lam-polymorphic-syntax.k"

module LAM-POLYMORPHIC-SEMANTICS
  imports LAM-POLYMORPHIC-SYNTAX

  syntax KResult ::= Term 

  syntax TermEnv ::= ".TermEnv" | Term TermEnv  [right]

  // -------------------------------------------------------------------------
  // configuration

  configuration
    <k> $PGM:Term </k>
    <termenv> .TermEnv:TermEnv </termenv>

  // -------------------------------------------------------------------------
  // type erasure

  rule <k> lambda* . A => A ... </k>
  
  rule <k> A:Term [_] => A ... </k>

  // -------------------------------------------------------------------------
  // base

  // product

  syntax Term ::= "#pi1" | "#pi2"
  // -------------------------------------------------------
  rule <k> pi1 A:Term              => A ~> #pi1 ... </k>
  rule <k> pi2 A:Term              => A ~> #pi2 ... </k>
  rule <k> < A:Val , B:Val > ~> #pi1 => A ... </k>
  rule <k> < A:Val , B:Val > ~> #pi2 => B ... </k>

  // sum

  syntax Term ::= "#match" "(" Term "," Term ")"
  // -------------------------------------------------------
  rule <k> match A:Term with B:Term ; C:Term      => A ~> #match(B, C) ... </k>

  rule <k> iota1 A:Term ~> #match(B:Term, C:Term) => B ... </k> <termenv> Env => A Env </termenv>
  rule <k> iota2 A:Term ~> #match(B:Term, C:Term) => C ... </k> <termenv> Env => A Env </termenv>

  // -------------------------------------------------------------------------
  // application

  syntax Term ::= "#app1" "(" Term ")"
                | "#app2" "(" Term ")"
  // -------------------------------------------------------
  rule <k> F A                      => F ~> #app1(A) ... </k>
  rule <k> lambda _ . B ~> #app1(A) => A ~> #app2(B) ... </k>
  rule <k> A:Val        ~> #app2(B) => B ... </k>             <termenv> Env => A Env </termenv>

  // -------------------------------------------------------------------------
  // variable

  rule <k> X:TermVar => #lookup(X, Env) ... </k> <termenv> Env </termenv>

  // lookup

  syntax Term ::= "#lookup" "(" TermVar "," TermEnv ")"  [function]
  // -------------------------------------------------------------------------
  rule #lookup(z  , A _)   => A
  rule #lookup(s X, _ Env) => #lookup(X, Env)

endmodule