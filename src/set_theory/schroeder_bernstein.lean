/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import order.fixed_points
import order.zorn

/-!
# Schröder-Bernstein theorem, well-ordering of cardinals

This file proves the Schröder-Bernstein theorem (see `schroeder_bernstein`), the well-ordering of
cardinals (see `min_injective`) and the totality of their order (see `total`).

## Notes

Cardinals are naturally ordered by `α ≤ β ↔ ∃ f : a → β, injective f`:
* `schroeder_bernstein` states that, given injections `α → β` and `β → α`, one can get a
  bijection `α → β`. This corresponds to the antisymmetry of the order.
* The order is also well-founded: any nonempty set of cardinals has a minimal element.
  `min_injective` states that by saying that there exists an element of the set that injects into
  all others.

Cardinals are defined and further developed in the file `set_theory.cardinal`.
-/

open set function
open_locale classical

universes u v

namespace function
namespace embedding

section antisymm
variables {α : Type u} {β : Type v}

/-- **The Schröder-Bernstein Theorem**:
Given injections `α → β` and `β → α`, we can get a bijection `α → β`. -/
theorem schroeder_bernstein {f : α → β} {g : β → α}
  (hf : function.injective f) (hg : function.injective g) : ∃ h : α → β, bijective h :=
begin
  casesI is_empty_or_nonempty β with hβ hβ,
  { haveI : is_empty α, from function.is_empty f,
    exact ⟨_, ((equiv.equiv_empty α).trans (equiv.equiv_empty β).symm).bijective⟩ },
  set F : set α →ₘ set α :=
  { to_fun := λ s, (g '' (f '' s)ᶜ)ᶜ,
    monotone' := λ s t hst, compl_subset_compl.mpr $ image_subset _ $
     compl_subset_compl.mpr $ image_subset _ hst },
  set s : set α := F.lfp,
  have hs : (g '' (f '' s)ᶜ)ᶜ = s, from F.map_lfp,
  have hns : g '' (f '' s)ᶜ = sᶜ, from compl_injective (by simp [hs]),
  set g' := inv_fun g,
  have g'g : left_inverse g' g, from left_inverse_inv_fun hg,
  have hg'ns : g' '' sᶜ = (f '' s)ᶜ, by rw [← hns, g'g.image_image],
  set h : α → β := s.piecewise f g',
  have : surjective h, by rw [← range_iff_surjective, range_piecewise, hg'ns, union_compl_self],
  have : injective h,
  { refine (injective_piecewise_iff _).2 ⟨hf.inj_on _, _, _⟩,
    { intros x hx y hy hxy,
      obtain ⟨x', hx', rfl⟩ : x ∈ g '' (f '' s)ᶜ, by rwa hns,
      obtain ⟨y', hy', rfl⟩ : y ∈ g '' (f '' s)ᶜ, by rwa hns,
      rw [g'g _, g'g _] at hxy, rw hxy },
    { intros x hx y hy hxy,
      obtain ⟨y', hy', rfl⟩ : y ∈ g '' (f '' s)ᶜ, by rwa hns,
      rw [g'g _] at hxy,
      exact hy' ⟨x, hx, hxy⟩ } },
  exact ⟨h, ‹injective h›, ‹surjective h›⟩
end

/-- **The Schröder-Bernstein Theorem**: Given embeddings `α ↪ β` and `β ↪ α`, there exists an
equivalence `α ≃ β`. -/
theorem antisymm : (α ↪ β) → (β ↪ α) → nonempty (α ≃ β)
| ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ :=
  let ⟨f, hf⟩ := schroeder_bernstein h₁ h₂ in
  ⟨equiv.of_bijective f hf⟩

end antisymm

section wo
parameters {ι : Type u} {β : ι → Type v}

@[reducible] private def sets := {s : set (∀ i, β i) |
  ∀ (x ∈ s) (y ∈ s) i, (x : ∀ i, β i) i = y i → x = y}

/-- The cardinals are well-ordered. We express it here by the fact that in any set of cardinals
there is an element that injects into the others. See `cardinal.linear_order` for (one of) the
lattice instance. -/
theorem min_injective (I : nonempty ι) : ∃ i, nonempty (∀ j, β i ↪ β j) :=
let ⟨s, hs, ms⟩ := show ∃ s ∈ sets, ∀ a ∈ sets, s ⊆ a → a = s, from
  zorn.zorn_subset sets (λ c hc hcc, ⟨⋃₀ c,
    λ x ⟨p, hpc, hxp⟩ y ⟨q, hqc, hyq⟩ i hi, (hcc.total hpc hqc).elim
      (λ h, hc hqc x (h hxp) y hyq i hi) (λ h, hc hpc x hxp y (h hyq) i hi),
  λ _, subset_sUnion_of_mem⟩) in
let ⟨i, e⟩ := show ∃ i, ∀ y, ∃ x ∈ s, (x : ∀ i, β i) i = y, from
  classical.by_contradiction $ λ h,
  have h : ∀ i, ∃ y, ∀ x ∈ s, (x : ∀ i, β i) i ≠ y,
    by simpa only [not_exists, not_forall] using h,
  let ⟨f, hf⟩ := classical.axiom_of_choice h in
  have f ∈ s, from
    have insert f s ∈ sets := λ x hx y hy, begin
      cases hx; cases hy, {simp [hx, hy]},
      { subst x, exact λ i e, (hf i y hy e.symm).elim },
      { subst y, exact λ i e, (hf i x hx e).elim },
      { exact hs x hx y hy }
    end, ms _ this (subset_insert f s) ▸ mem_insert _ _,
  let ⟨i⟩ := I in hf i f this rfl in
let ⟨f, hf⟩ := classical.axiom_of_choice e in
⟨i, ⟨λ j, ⟨λ a, f a j, λ a b e',
  let ⟨sa, ea⟩ := hf a, ⟨sb, eb⟩ := hf b in
  by rw [← ea, ← eb, hs _ sa _ sb _ e']⟩⟩⟩

end wo

/-- The cardinals are totally ordered. See `cardinal.linear_order` for (one of) the lattice
instance. -/
theorem total {α : Type u} {β : Type v} : nonempty (α ↪ β) ∨ nonempty (β ↪ α) :=
match @min_injective bool (λ b, cond b (ulift α) (ulift.{(max u v) v} β)) ⟨tt⟩ with
| ⟨tt, ⟨h⟩⟩ := let ⟨f, hf⟩ := h ff in or.inl ⟨embedding.congr equiv.ulift equiv.ulift ⟨f, hf⟩⟩
| ⟨ff, ⟨h⟩⟩ := let ⟨f, hf⟩ := h tt in or.inr ⟨embedding.congr equiv.ulift equiv.ulift ⟨f, hf⟩⟩
end

end embedding
end function
