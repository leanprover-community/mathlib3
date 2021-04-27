/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import data.nat.prime
import group_theory.subgroup
import data.fintype.basic

/-!
# This is a list of things to do.

1. Define what reducible representations are.
2. Define equivalence between `ℂG`-modules and representations.
3. Define representation homomorphisms.
4. Schur's Lemma
5. Define characters
6. Inner product on class functions and orthogonality relations
7. Define the character table

2. Burnsides Theorem

theorem burnsides {G : Type*} [group G] [fintype G]
  {p q a b : ℕ} (hp : p.prime) (hq : q.prime) (hG : fintype.card G = p ^ a * q ^ b) :
  (is_simple_group G) :=
begin
  sorry
end

-/
