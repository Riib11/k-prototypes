requires "../syntax/lam-polymorphic-syntax.k"

module LAM-POLYMORPHIC-TYPING
  imports LAM-POLYMORPHIC-SYNTAX

  syntax KResult ::= TypeQ

  syntax TypeCtx ::= ".TypeCtx" | Type TypeCtx [right]

  // ---------------------------------------------------------------------------
  // configuration

  configuration
    <k> $PGM:Term </k>
    <typectx> .TypeCtx </typectx>

  // ---------------------------------------------------------------------------
  // base

  // unit
  
  rule u => forall z . unit

  // product

  syntax Term ::= "#pi1"
                | "#pi2"
  // ---------------------------------------------------------------------------
  rule <k> pi1 A:Term               => A ~> #pi1    ... </k>
  rule <k> forall n . S * T ~> #pi1 => forall n . S ... </k>  
  rule <k> pi2 A:Term               => A ~> #pi2    ... </k>
  rule <k> forall n . S * T ~> #pi2 => forall n . T ... </k>  

  syntax Type ::= "#pair1" "(" Term  ")"
                | "#pair2" "(" TypeQ ")"
  // ---------------------------------------------------------------------------
  rule <k> < A:Term , B:Term >                  => A ~> #pair1(B)            ... </k>
  rule <k> forall n . S ~> #pair1(B)            => B ~> #pair2(forall n . S) ... </k>
  rule <k> forall n . T ~> #pair2(forall n . S) => forall n . S * T          ... </k>

  // sum

  syntax Type ::= "#match1" "(" Term  , Term  ")"
                | "#match2" "(" TypeQ , Term  ")"
                | "#match3" "(" TypeQ , TypeQ ")"
  // ---------------------------------------------------------------------------
  rule <k> match A:Term with B:Term ; C:Term                           => A ~> #match1(B, C)                           ... </k>
  rule <k> forall n . S + T ~> #match(B, C)                            => B ~> #match2(forall n . S + T, C)            ... </k> <typectx>   Ctx => S Ctx </typectx>
  rule <k> forall n . R     ~> #match2(forall n . S + T, C)            => C ~> #match3(forall n . S + T, forall n . R) ... </k> <typectx> S Ctx => T Ctx </typectx>
  rule <k> forall n . R     ~> #match3(forall n . S + T, forall n . R) => forall n . R                                 ... </k> <typectx> T Ctx =>   Ctx </typectx>

  syntax Type ::= "#iota1" | "#iota2"
  // ---------------------------------------------------------------------------
  rule <k> iota2 A:Term           => B:Term ~> #iota2    ... </k>
  rule <k> iota1 A:Term           => A:Term ~> #iota1    ... </k>
  rule <k> forall n . S ~> #iota1 => forall n .  S + ?T  ... </k>
  rule <k> forall n . T ~> #iota2 => forall n . ?S +  T  ... </k>

  // ---------------------------------------------------------------------------
  // abstraction

  syntax Type ::= "#abs" "(" Type ")" [function]
  // ---------------------------------------------------------------------------
  rule <k> lambda S . B      => B ~> #abs(S) ... </k> <typectx>   Ctx => S Ctx </typectx> [simplification]
  rule <k> T:Type ~> #abs(S) => S -> T       ... </k> <typectx> S Ctx =>   Ctx </typectx> [simplification]

  // ---------------------------------------------------------------------------
  // type abstraction

  syntax Type ::= "#abs*"
  // ---------------------------------------------------------------------------
  rule <k> lambda* . B           => B ~> #abs*     ... </k>
  rule <k> forall n . T ~> #abs* => forall s n . T ... </k>

  // ---------------------------------------------------------------------------
  // application

  syntax Type ::= "#app1" "(" Term ")" [function]
                | "#app2" "(" Type ")" [function]
  // ---------------------------------------------------------------------------
  rule <k> F:Term A:Term                                 => F ~> #app1(A)                 ... </k> [simplification]
  rule <k> forall n . S -> T ~> #app1(A)                 => A ~> #app2(forall n . S -> T) ... </k> [simplification]
  rule <k> forall n . S      ~> #app2(forall n . S -> T) => T                             ... </k> [simplification]

  // ---------------------------------------------------------------------------
  // type application

  syntax Type ::= "#app*" "(" Type ")" [function]
  // ---------------------------------------------------------------------------
  rule <k> A:Term @ S:Type             => A ~> #app*(S)                       ... </k> [simplification]
  rule <k> forall s n . T  ~> #app*(S) => forall n . #substituteType(n, T, S) ... </k> [simplification]

  // ---------------------------------------------------------------------------
  // type substitution

  syntax Type ::= "#substituteType" "(" Nat "," Type "," Type  ")" [function]
  // ---------------------------------------------------------------------------
  rule #substituteType(n, R, typeVar(n)) => R                                              [simplification]
  rule #substituteType(_, R, typeVar(n)) => termVar(n)                                     [simplification, owise]              
  rule #substituteType(n, R, S *  T )    => #substituteType(R, S) *  #substituteType(R, T) [simplification]
  rule #substituteType(n, R, S +  T )    => #substituteType(R, S) +  #substituteType(R, T) [simplification]
  rule #substituteType(n, R, S -> T )    => #substituteType(R, S) -> #substituteType(R, T) [simplification]

  // ---------------------------------------------------------------------------
  // term variable

  rule <k> X:TermVar => forall z . #lookupTerm(X, Ctx) ... </k> <typectx> Ctx </typectx>

  // lookup term variable

  syntax Type ::= "#lookupTerm" "(" TermVar "," TypeCtx ")" [function]
  // ---------------------------------------------------------------------------
  rule #lookupTerm(z  , T _)   => T                   [simplification]
  rule #lookupTerm(s X, _ Ctx) => #lookupTerm(X, Ctx) [simplification]

endmodule
