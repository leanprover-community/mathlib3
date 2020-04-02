/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/

import graph_theory.cycle

/-!
# Strong product of graphs
-/

universe variables v v₁ v₂ v₃ u u₁ u₂ u₃

namespace graph

variables {V : Type u} {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃} {W : Type*}
variables {G : graph V} {G₁ : graph V₁} {G₂ : graph V₂} {G₃ : graph V₃}

structure girth_at_least (G : graph V) (n : ℕ+) : Prop :=
(min        : ∀ {m}, cycle m G → n ≤ m)

def girth_at_least.is_loopless {G : graph V} {n : ℕ+} (g : girth_at_least G n) (h : 2 ≤ n) :
  G.is_loopless :=
begin
  assume x e,
  suffices : (2 : ℕ+) ≤ 1, { replace : 2 ≤ 1 := by exact_mod_cast this, linarith },
  apply le_trans h,
  apply g.min,
  refine
  { to_fun    := λ _, x,
    map_edge' := assume _ _ _, e,
    inj       := _ },
  assume _ _ _,
  apply subsingleton.elim,
end

structure girth (G : graph V) (n : ℕ+) extends girth_at_least G n : Prop :=
(cyc_exists : nonempty (cycle n G))

end graph
