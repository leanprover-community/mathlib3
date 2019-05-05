# Maths in Lean : number theory

In addition to the basic operations on `ℤ` and `ℚ`, there are
things on diophantine sets in `number_theory/dioph`, and on Pell's
equation in `number_theory/pell`. Those things are used to prove
Matiyasevič's theorem, which states that the power function is
Diophantine, forming the last and hardest piece of the MRDP theorem of
the unsolvability of Hilbert's 10th problem (asking for algorithmic
solution to all diophantine equations). 

A set `S ⊆ ℕ^α` is diophantine if there exists a polynomial on 
`α ⊕ β` such that `v ∈ S` iff there exists `t : ℕ^β` with `p (v, t) = 0`. 
