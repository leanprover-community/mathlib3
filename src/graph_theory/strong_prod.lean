/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import graph_theory.basic

/-!
# Strong product of graphs
-/

universe variables v v₁ v₂ v₃ u u₁ u₂ u₃

namespace graph

variables {V : Type u} {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃} {W : Type*}
variables {G : graph V} {G₁ : graph V₁} {G₂ : graph V₂} {G₃ : graph V₃}

def strong_prod (G₁ : graph V₁) (G₂ : graph V₂) : graph (V₁ × V₂) :=
{ edge := assume p q,
    ((p.1 ~[G₁] q.1) ∧ (p.2 ~[G₂] q.2)) ∨
    ((p.1 = q.1) ∧ (p.2 ~[G₂] q.2)) ∨
    ((p.1 ~[G₁] q.1) ∧ (p.2 = q.2)),
  symm := assume p q, by
    -- TODO: Scott, diagnose why `solve_by_elim` can't do this
    repeat {apply or.imp <|> apply and.imp <|> apply edge.symm <|> apply eq.symm } }

def prod_hom_strong (G₁ : graph V₁) (G₂ : graph V₂) :
  hom (G₁.prod G₂) (G₁.strong_prod G₂) :=
{ to_fun := id,
  map_edge' := assume x y e, or.inl e }

lemma is_loopless.strong_prod (h₁ : G₁.is_loopless) (h₂ : G₂.is_loopless) :
  (G₁.strong_prod G₂).is_loopless :=
begin
  rintros x (e|e|e),
  { exact h₁ e.1 },
  { exact h₂ e.2 },
  { exact h₁ e.1 }
end

end graph
