/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import order.rel_iso.basic
import logic.embedding.set

/-!
# Interactions between relation homomorphisms and sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

It is likely that there are better homes for many of these statement,
in files further down the import graph.
-/

open function

universes u v w
variables {α β γ δ : Type*}
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} {u : δ → δ → Prop}

namespace rel_hom_class

variables {F : Type*}

lemma map_inf [semilattice_inf α] [linear_order β]
  [rel_hom_class F ((<) : β → β → Prop) ((<) : α → α → Prop)]
  (a : F) (m n : β) : a (m ⊓ n) = a m ⊓ a n :=
(strict_mono.monotone $ λ x y, map_rel a).map_inf m n

lemma map_sup [semilattice_sup α] [linear_order β]
  [rel_hom_class F ((>) : β → β → Prop) ((>) : α → α → Prop)]
  (a : F) (m n : β) : a (m ⊔ n) = a m ⊔ a n :=
@map_inf αᵒᵈ βᵒᵈ _ _ _ _ _ _ _
end rel_hom_class

namespace rel_iso

@[simp] lemma range_eq (e : r ≃r s) : set.range e = set.univ := e.surjective.range_eq

end rel_iso

/-- `subrel r p` is the inherited relation on a subset. -/
def subrel (r : α → α → Prop) (p : set α) : p → p → Prop :=
(coe : p → α) ⁻¹'o r

@[simp] theorem subrel_val (r : α → α → Prop) (p : set α)
  {a b} : subrel r p a b ↔ r a.1 b.1 := iff.rfl

namespace subrel

/-- The relation embedding from the inherited relation on a subset. -/
protected def rel_embedding (r : α → α → Prop) (p : set α) :
  subrel r p ↪r r := ⟨embedding.subtype _, λ a b, iff.rfl⟩

@[simp] theorem rel_embedding_apply (r : α → α → Prop) (p a) :
  subrel.rel_embedding r p a = a.1 := rfl

instance (r : α → α → Prop) [is_well_order α r] (p : set α) : is_well_order p (subrel r p) :=
rel_embedding.is_well_order (subrel.rel_embedding r p)

instance (r : α → α → Prop) [is_refl α r] (p : set α) : is_refl p (subrel r p) :=
⟨λ x, @is_refl.refl α r _ x⟩

instance (r : α → α → Prop) [is_symm α r] (p : set α) : is_symm p (subrel r p) :=
⟨λ x y, @is_symm.symm α r _ x y⟩

instance (r : α → α → Prop) [is_trans α r] (p : set α) : is_trans p (subrel r p) :=
⟨λ x y z, @is_trans.trans α r _ x y z⟩

instance (r : α → α → Prop) [is_irrefl α r] (p : set α) : is_irrefl p (subrel r p) :=
⟨λ x, @is_irrefl.irrefl α r _ x⟩

end subrel

/-- Restrict the codomain of a relation embedding. -/
def rel_embedding.cod_restrict (p : set β) (f : r ↪r s) (H : ∀ a, f a ∈ p) : r ↪r subrel s p :=
⟨f.to_embedding.cod_restrict p H, λ _ _, f.map_rel_iff'⟩

@[simp] theorem rel_embedding.cod_restrict_apply (p) (f : r ↪r s) (H a) :
  rel_embedding.cod_restrict p f H a = ⟨f a, H a⟩ := rfl
