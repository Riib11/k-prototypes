requires "../syntax/lam-polymorphic-syntax.k"

module LAM-POLYMORPHIC-TYPING
  imports LAM-POLYMORPHIC-SYNTAX

  syntax Term ::= Type
  syntax Type ::= "#termVar" "(" Nat ")"

  syntax Bool ::= isKResult(K) [function, symbol]
  // ---------------------------------------------------------------------------
  // rule isKResult(unit)         => true
  // rule isKResult(' _)          => true
  // rule isKResult(_ * _)        => true
  // rule isKResult(_ + _)        => true
  // rule isKResult(_ -> _)       => true
  // rule isKResult(forall * . _) => true
  // rule isKResult(_)            => false [owise]

  rule isKResult(_:Type) => true
  rule isKResult(_)      => false [owise]

  // ---------------------------------------------------------------------------
  // configuration

  configuration
    <k> $PGM:Term </k>

  // ---------------------------------------------------------------------------
  // term variable

  rule `N => #termVar(N)

  // ---------------------------------------------------------------------------
  // unit

  rule u => unit

  // ---------------------------------------------------------------------------
  // sum

  // intro
  rule iota1(S) => forall * . S  + 'z
  rule iota2(T) => forall * . 'z + T

  // elim
  rule match R + S with (R -> T) | (S -> T) => T

  // ---------------------------------------------------------------------------
  // product

  // intro
  rule <S, T> => S * T

  // elim
  rule pi1(S * _) => S
  rule pi2(_ * T) => T

  // ---------------------------------------------------------------------------
  // abstraction

  rule lambda S . T => S -> #substTerm(z, S, T)

  // ---------------------------------------------------------------------------
  // application

  rule (S -> T) S => T

  // ---------------------------------------------------------------------------
  // type application

  rule forall * . T @ S => #substType(z, S, T)

  // ---------------------------------------------------------------------------
  // substitution

  syntax Type ::= "#substType" "(" Nat "," Type "," Type ")" [function]
  // ---------------------------------------------------------------------------
  rule #substType(M, S, 'N)           => S  requires M  ==Nat N                     [simplification]
  rule #substType(M, _, 'N)           => 'N requires M =/=Nat N                     [simplification]
  rule #substType(_, _, unit)         => unit                                       [simplification]
  rule #substType(_, _, 'N)           => #termVar(N)                                [simplification]
  rule #substType(M, S, T *  U)       => #substType(M, S, T) *  #substType(M, S, U) [simplification]
  rule #substType(M, S, T +  U)       => #substType(M, S, T) +  #substType(M, S, U) [simplification]
  rule #substType(M, S, T -> U)       => #substType(M, S, T) -> #substType(M, S, U) [simplification]
  rule #substType(M, S, forall * . T) => forall * . #substType(s M, S, T)           [simplification]

  syntax Type ::= "#substTerm" "(" Nat "," Type "," Type ")" [function]
  // ---------------------------------------------------------------------------
  rule #substTerm(_, _, 'N)           => 'N                                           [simplification]
  rule #substTerm(_, _, unit)         => unit                                         [simplification]
  rule #substTerm(M, S, #termVar(N))  => S           requires M  ==Nat N              [simplification]
  rule #substTerm(M, _, #termVar(N))  => #termVar(N) requires M =/=Nat N              [simplification]
  rule #substTerm(M, S, T *  U)       => #substTerm(M, S, T) *  #substTerm(M,   S, U) [simplification]
  rule #substTerm(M, S, T +  U)       => #substTerm(M, S, T) +  #substTerm(M,   S, U) [simplification]
  rule #substTerm(M, S, T -> U)       => #substTerm(M, S, T) -> #substTerm(s M, S, U) [simplification]
  rule #substTerm(M, S, forall * . T) => forall * . #substTerm(M, S, T)               [simplification]

endmodule
