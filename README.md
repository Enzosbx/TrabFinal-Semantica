# TrabFinal-Semantica

Instruções: O trabalho consiste em implementar um interpretador para a linguagem L1 com
extensões conforme a gramática abstrata abaixo. O interpretador é constituído de uma funcão
que realiza inferência de tipos, e de uma funcão que realiza a avaliação (além de outras funções
auxiliares). A inferência de tipos e o avaliador devem atender o que especificam as regras do
sistema de tipos e as regras da semântica operacional big step, respectivamente.

O trabalho deve ser realizado em grupos de 3 componente. A linguagem de implementação
deve ser OCaml.

Prazo de entrega: O trabalho deverá ser entregue até a meia noite do dia 31 de março.


LINGUAGEM: 

e ∈ Expr

e ::= n | b | e1 op e2 | if e1 then e2 else e3
| x | e1 e2 | fn x : T ⇒ e | let x : T = e1 in e2
| let rec f : T1 → T2 = fn x : T1 ⇒ e1 in e2
| (e1, e2) | fst e | snd e
| nil : T | e1::e2 | hd e | tl e
| match e1 with nil ⇒ e2 | x::xs ⇒ e3
| just e | nothing : T
| match e1 with nothing ⇒ e2 | just x ⇒ e3
op ∈ {+, −, ∗, div, <, ≤, >, ≥, =, and, or}


T ::= int | bool | T1 → T2 | T list | T1 ∗ T2 | maybe T
