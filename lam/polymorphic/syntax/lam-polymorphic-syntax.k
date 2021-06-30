module NAT-SYNTAX

  syntax Nat ::= "z" | "s" Nat [right]

endmodule

module NAT
  imports NAT-SYNTAX
  imports BOOL

  syntax Bool ::= Nat  "==Nat" Nat [function, strict]
                | Nat "=/=Nat" Nat [function, strict]

  rule z   ==Nat z   => true
  rule z   ==Nat s _ => false
  rule s _ ==Nat z   => false
  rule s M ==Nat s N => M ==Nat N

  rule M =/=Nat N => notBool (M ==Nat N)

endmodule

module LAM-POLYMORPHIC-SYNTAX
  imports NAT

  syntax Type  ::= "unit"
                 | "'" Nat [format(%1%2)]
                 > "(" Type ")" [bracket, format(%1%2%3)]
                 | Type "*" Type [right, strict]
                 > Type "+" Type [right, strict]
                 > Type "->" Type [right, strict]
                 > "forall" "*" "." Type [right, strict]

  syntax Term  ::= "u"
                 | "`" Nat [format(%1%2)]
                 | "(" Term ")" [bracket, format(%1%2%3)]
                 > Term Term [left, strict]
                 > "<" Term "," Term ">" [strict, format(%1%2%3 %4%5%6)]
                 | "iota1" "(" Term ")" [strict, format(%1%2%3%4)]
                 | "iota2" "(" Term ")" [strict, format(%1%2%3%4)]
                 | "pi1" "(" Term ")" [strict, format(%1%2%3%4)]
                 | "pi2" "(" Term ")" [strict, format(%1%2%3%4)]
                 > Term "@" Type [left, strict]
                 > "lambda" Type "." Term [strict]
                 | "lambda" "*" "." Term [strict]
                 > "match" Term "with" Term "|" Term [strict, format(%1 %2 %3%n%i%4%d%n%5%i %6%d)]
  
endmodule
