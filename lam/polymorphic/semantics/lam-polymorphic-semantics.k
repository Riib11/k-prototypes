requires "../syntax/lam-polymorphic-syntax.k"

module LAM-POLYMORPHIC-SEMANTICS
  imports LAM-POLYMORPHIC-SYNTAX
  imports BOOL

  syntax Bool ::= isKResult(K) [function, symbol]
  // ---------------------------------------------------------------------------
  rule isKResult(u)            => true
  rule isKResult(_:Nat)        => true
  rule isKResult(lambda _ . _) => true
  rule isKResult(iota1(_))     => true
  rule isKResult(iota2(_))     => true
  rule isKResult(<_,_>)        => true
  rule isKResult(_)            => false [owise]

  // ---------------------------------------------------------------------------
  // configuration

  configuration
    <k> $PGM:Term </k>

  // ---------------------------------------------------------------------------
  // type erasure

  rule lambda* . A => A
  rule A:Term @ _  => A

  // ---------------------------------------------------------------------------
  // application

  rule (lambda _T . B) A => #subst(z, A, B)

  // ---------------------------------------------------------------------------
  // sum

  rule match iota1(A) with K | _ => K A
  rule match iota2(B) with _ | K => K B

  // ---------------------------------------------------------------------------
  // product

  rule pi1(< A, _B>) => A
  rule pi2(<_A,  B>) => B

  // ---------------------------------------------------------------------------
  // substitution

  syntax Term ::= "#subst" "(" Nat "," Val "," Term ")" [function]
  // ---------------------------------------------------------------------------
  rule #subst(M, A, N)                  => A requires M  ==Nat N              [simplification] 
  rule #subst(M, _, N)                  => N requires M =/=Nat N              [simplification] 
  rule #subst(_, _, u)                  => u                                  [simplification]
  rule #subst(N, A, lambda T . B)       => lambda T . #subst(s N, A, B)       [simplification]
  rule #subst(N, A, <B, C>)             => <#subst(N, A, B), #subst(N, A, C)> [simplification]
  rule #subst(N, A, iota1(B))           => iota1(#subst(N, A, B))             [simplification]
  rule #subst(N, A, iota2(C))           => iota2(#subst(N, A, C))             [simplification]
  rule #subst(N, A, F B)                => #subst(N, A, F) #subst(N, A, B)    [simplification]
  rule #subst(N, A, match B with C | D) => match #subst(N, A, B) with 
                                             #subst(s N, A, C)
                                           | #subst(s N, A, D)                [simplification]
  rule #subst(N, A, pi1(B))             => pi1(#subst(N, A, B))               [simplification]
  rule #subst(N, A, pi2(B))             => pi2(#subst(N, A, B))               [simplification]

endmodule