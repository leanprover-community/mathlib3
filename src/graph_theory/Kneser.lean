/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import graph_theory.basic
import .to_mathlib

/-!
# Kneser graphs
-/

universes v v₁ v₂ v₃ u u₁ u₂ u₃

namespace graph

variables {V : Type u} {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃} {W : Type*}
variables {G : graph V} {G₁ : graph V₁} {G₂ : graph V₂} {G₃ : graph V₃}

@[simps]
def Kneser (V : Type u) [decidable_eq V] (k : ℕ) :
  graph { s : finset V // s.card = k } :=
{ edge := assume s t, disjoint (s : finset V) (t : finset V),
  symm := assume s t e, e.symm }

def Kneser.map [decidable_eq V₁] [decidable_eq V₂]
  (f : V₁ ↪ V₂) (k : ℕ) :
  hom (Kneser V₁ k) (Kneser V₂ k) :=
{ to_fun    := λ s, ⟨finset.map f s, by { rw finset.card_map f, exact s.2 }⟩,
  map_edge' := assume s t e, show disjoint (finset.map f s) (finset.map f t),
    by rwa [finset.map_disjoint] }

@[simp]
lemma Kneser.map_id [decidable_eq V] (k : ℕ) :
  Kneser.map (function.embedding.refl V) k = hom.id _ :=
by { ext, dsimp [Kneser.map], apply subtype.eq, simp, refl, }

@[simp]
lemma Kneser.map_trans [decidable_eq V₁] [decidable_eq V₂] [decidable_eq V₃]
  (f : V₁ ↪ V₂) (g : V₂ ↪ V₃) (k : ℕ) :
  Kneser.map (f.trans g) k = hom.comp (Kneser.map g k) (Kneser.map f k) :=
by { ext, dsimp [Kneser.map], apply subtype.eq, simp, }

lemma Kneser.is_loopless_iff (V : Type u) [decidable_eq V] (k : ℕ) :
  (Kneser V k).is_loopless ↔ 0 < k :=
begin
  split,
  { unfold is_loopless,
    contrapose!,
    rw nat.le_zero_iff,
    rintro rfl,
    refine ⟨⟨∅, finset.card_empty⟩, disjoint_bot_left⟩ },
  { rintros h ⟨s, rfl⟩ e,
    replace e : s = ∅ := disjoint_self.mp e,
    subst s,
    rw finset.card_empty at h,
    exact nat.not_lt_zero _ h }
end

end graph
