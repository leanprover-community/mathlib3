/-
Copyright (c) 2022 Daniel Roca González. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Roca González
-/
import order.filter.lift
import topology.subset_properties
import topology.uniform_space.basic
import data.set.prod

/-!
# Coarse spaces

TODO give a good explanation of what a controlled space is.

The usual definition of a controlled space is as a `set (set α×α)`
(whose elements are called *controlled sets*):
this is not a filter, but one would call a *cofilter*.
In order to take advantage of filters,
we define a coarse space in terms of its *cocontrolled sets*,
which are the complements of the controlled sets.

The intuition one should keep in mind is the special case of metric spaces:
a set in a metric space is controlled iff it has coarse_bounded diameter.
# Notations

Localized to `coarse_space`, we define `□` for `cocomp`
(the complements of the composition of the complements of a pair of relations,
needed to define cocontrolled sets).
For a coarse space `α`, localized to `coarse_space`,
we define `𝓒' α` to be the filter of concontrolled sets
and `𝓒 α` to be the set of controlled sets.

# References

Roe geometry

-/

open set filter
open_locale uniformity topological_space filter

variables {α β γ : Type*} {a b : α} {s t : set (α × α)}


/-! ### Relations -/
/- The complement of the identity relation on a set -/
def coid_rel : set (α×α) := {p : α × α | p.1 ≠ p.2}

@[simp]
theorem nmem_coid_rel : (a, b) ∈ (coid_rel : set (α×α)) ↔ a ≠ b := iff.rfl

@[simp]
theorem coid_rel_subset : s ⊆ coid_rel ↔ ∀ a, (a, a) ∉ s :=
by simp [subset_def]; exact forall_congr (λ a, by
begin
  split,
  show (∀ (b : α), (a, b) ∈ s → ¬a = b) → (a, a) ∉ s,
  by {contrapose, simp,},
  show (a, a) ∉ s → (∀ (b : α), (a, b) ∈ s → ¬a = b),
  by {
    intros not_diag b in_s,
    have := not_diag,
    by_contradiction,
    rw ←h at in_s,
    contradiction,
  }
end)

@[simp]
theorem co_of_coid_id_rel : coid_relᶜ = (id_rel : set (α×α)) :=
begin
  ext v,
  unfold coid_rel id_rel,
  simp,
end

/-- The cocomposition of relations:
it is the complement of the composition of the complements of relations.  -/
def cocomp_rel (r₁ r₂ : set (α×α)) := {p : α × α | ∀z:α, (p.1, z) ∈ r₁ ∨ (z, p.2) ∈ r₂}

localized "infix ` □ `:55 := cocomp_rel" in coarse_space

variables {r₁ r₂ : set (α×α)} {x y : α}

@[simp] theorem mem_cocomp_rel : (x, y) ∈ r₁ □ r₂ ↔ ∀ z, (x, z) ∈ r₁ ∨ (z, y) ∈ r₂ := iff.rfl

@[simp] theorem nmem_cocomp_rel : (x, y) ∉ r₁ □ r₂ ↔ ∃ z, (x, z) ∉ r₁ ∧ (z, y) ∉ r₂ :=
begin
  split,
  {
    intro not_in_comp,
    simp at not_in_comp,
    cases not_in_comp with z g,
    by_contra h,
    simp at h,
    have either_r : (x, z) ∈ r₁ ∨ (z, y) ∈ r₂,
    {
      exact or_iff_not_imp_left.mpr (h z),
    },
    contradiction,
  },
  {
    intro exists_in_neither,
    cases exists_in_neither with z hz,
    simp,
    use z,
    exact not_or_distrib.mpr hz,
  }
end

@[simp] lemma co_of_cocomp_eq_comp_of_co : (r₁ □ r₂)ᶜ = r₁ᶜ ○ r₂ᶜ :=
begin
  ext v,
  cases v with x y,
  simp,
  push_neg,
  exact iff.rfl,
end

@[simp] lemma not_comp_iff_cocomp_of_co : (r₁ ○ r₂)ᶜ = r₁ᶜ □ r₂ᶜ :=
begin
  apply compl_inj_iff.mp,
  simp,
  exact boolean_algebra.to_core (set (α × α)),
end

@[simp] theorem swap_coid_rel : prod.swap '' coid_rel = (coid_rel : set (α×α)) :=
set.ext $ assume ⟨a, b⟩, by simp [image_swap_eq_preimage_swap]; rw eq_comm

theorem cocomp_rel.monotone [preorder β] {f g : β → set (α×α)}
  (hf : monotone f) (hg : monotone g) : monotone (λx, (f x) □ (g x)) :=
begin
  unfold monotone,
  intros a b lt,
  unfold cocomp_rel,
  simp,
  intros a' b' h z,
  cases h z,
  {
    left,
    apply hf lt,
    exact h_1,
  },
  {
    right,
    apply hg lt,
    exact h_1,
  }
end

@[mono]
lemma cocomp_rel_mono {f g h k: set (α×α)} (h₁ : h ⊆ f) (h₂ : k ⊆ g) : h □ k ⊆ f □ g  :=
begin
  unfold cocomp_rel, simp,
  intros a b h z,
  have := h z,
  tauto,
end

lemma prod_mk_nmem_cocomp_rel {a b c : α} {s t : set (α×α)} (h₁ : (a, c) ∉ s) (h₂ : (c, b) ∉ t) :
  (a, b) ∉ s □ t :=
begin
  simp,
  use c,
  push_neg,
  split,
  assumption',
end

@[simp] lemma coid_cocomp_rel {r : set (α×α)} : coid_rel □ r = r :=
begin
  apply compl_inj_iff.mp,
  rw co_of_cocomp_eq_comp_of_co,
  simp,
end

@[simp]
lemma cocomp_rel_assoc {r s t : set (α×α)} :
  (r □ s) □ t = r □ (s □ t) :=
begin
  apply compl_inj_iff.mp,
  repeat {rw co_of_cocomp_eq_comp_of_co},
  exact comp_rel_assoc,
end

lemma subset_cocomp_self {s : set (α × α)} (h : s ⊆ coid_rel) : s □ s ⊆ s :=
λ ⟨x, y⟩ xy_in, by {
  simp at h,
  simp at xy_in,
  have := xy_in y,
  cases this,
  assumption,
  have := h y,
  contradiction,
}


/-! ### Coarse spaces -/
variables (α)
class coarse_space :=
(cocontrolled   : filter (α × α))
(corefl     : cocontrolled ≤ 𝓟 coid_rel)
(symm       : tendsto prod.swap cocontrolled cocontrolled)
(cocomp       : cocontrolled ≤ cocontrolled.lift' (λs, s □ s))

variables {α}

def coarse_space.mk' (U : filter (α × α))
  (corefl : coid_rel ∈ U)
  (symm : ∀ r ∈ U, prod.swap ⁻¹' r ∈ U)
  (cocomp : ∀ r ∈ U, r □ r ∈ U) : coarse_space α :=
⟨U, λ r ru, mem_of_superset corefl ru, symm,
  begin
    intros v h,
    rw [mem_lift'_sets] at h,
    rcases h with ⟨w, hw, hcomp⟩,
    have : w □ w ∈ U, by {exact cocomp w hw},
    apply mem_of_superset this, exact hcomp,
    refine cocomp_rel.monotone _ _, tidy,
  end⟩

lemma coarse_space.eq :
  ∀{u₁ u₂ : coarse_space α}, u₁.cocontrolled = u₂.cocontrolled → u₁ = u₂
| ⟨u₁, _, _, _⟩  ⟨u₂, _, _, _⟩ h := by { congr, exact h }



def cocontrolled (α : Type*) [s : coarse_space α] : filter (α × α) :=
  @coarse_space.cocontrolled α s

localized "notation `𝓒'` := cocontrolled" in coarse_space

def controlled (α : Type*) [s : coarse_space α] : set (set (α×α)) :=
  compl '' (𝓒' α).sets

localized "notation `𝓒` := controlled" in coarse_space

namespace coarse_space
variables [coarse_space α]
@[simp]
lemma mem_coarse {s : set (α×α)} : s ∈ 𝓒 α ↔ sᶜ ∈ 𝓒' α :=
begin
  split,
  {rintro h, rcases h with ⟨t, h_h_left, rfl⟩, simpa,},
  {rintro h, use sᶜ, simpa,}
end

lemma cocontrolled_le_corefl : 𝓒' α ≤ 𝓟 coid_rel :=
@coarse_space.corefl α _

lemma corefl_mem_cocontrolled :
  coid_rel ∈ 𝓒' α :=
begin
  have := @coarse_space.corefl α _,
  simpa,
end

lemma mem_cocontrolled_of_eq {x y : α} {s : set (α × α)} (hx : x ≠ y) :
  ∃ s ∈ 𝓒' α, (x, y) ∈ s :=
begin
  use coid_rel,
  split, by {exact corefl_mem_cocontrolled},
  simpa,
end

lemma symm_le_cocontrolled : map (@prod.swap α α) (𝓒' _) ≤ (𝓒' _) :=
(@coarse_space.symm α _)

lemma cocontrolled_le_cocomp : 𝓒' α ≤ (𝓒' α).lift' (λs:set (α×α), s □ s) :=
(@coarse_space.cocomp α _)

lemma tendsto_swap_cocontrolled : tendsto (@prod.swap α α) (𝓒' α) (𝓒' α) :=
symm_le_cocontrolled

lemma cocomp_mem_cocontrolled_sets {s : set (α × α)} (hs : s ∈ 𝓒' α) :
  s □ s ∈ 𝓒' α :=
begin
  apply cocontrolled_le_cocomp,
  rw mem_lift'_sets, use s, split,
  {assumption},
  {intros x h, assumption,},
  {refine cocomp_rel.monotone _ _, tidy,}
end

/-! ### Close and coarse maps -/

@[protected]
def bounded (b : set α) : Prop := (b ×ˢ b : set (α×α)) ∈ 𝓒 α
def proper [coarse_space β] (f : α → β) : Prop := ∀ (b : set β), coarse_bounded b → coarse_bounded (f ⁻¹' b)
def bornologous [coarse_space β] (f : α → β) : Prop := ∀ s ∈ 𝓒' α, prod.map f f '' s ∈ 𝓒' β
lemma bornologous.controlled [coarse_space β] (f : α → β) :
  bornologous f ↔ ∀ s ∈ 𝓒 α, prod.map f f '' s ∈ 𝓒 β := sorry
structure coarse_map (α β : Type*) [coarse_space α] [coarse_space β] :=
  (to_fun : α → β)
  (proper : proper to_fun)
  (bornologous : bornologous to_fun)

infixr ` →c `:25 := coarse_map

instance coarse_map.to_fun_like [coarse_space β] : fun_like (α →c β) α (λ _, β) :=
  { coe := coarse_map.to_fun,
  coe_injective' := λ f g h, sorry}


namespace coarse_map
variables [coarse_space β]

def comp [coarse_space γ] (f : α →c β) (g : γ →c α) : γ →c β :=
  { to_fun := (f ∘ g : γ → β),
  proper := sorry,
  bornologous := sorry}

def id : α →c α :=
 { to_fun := id,
  proper := _,
  bornologous := _ }

def const [coarse_space β] (x : β) : α →c β :=
 { to_fun := (λ _, x),
  proper := _,
  bornologous := _}

end coarse_map

infixr ` ∘c `:25 := coarse_map.comp

/-
Two maps between coarse spaces are close iff the image of the codiagonal is cocontrolled-/
def close_maps [coarse_space β] (f g : α → β) : Prop := prod.map f g '' coid_rel ∈ 𝓒' β

namespace close_maps
variables [coarse_space β] {f g h : α → β}
/-
Two maps between coarse spaces are close iff the image of the diagonal is controlled-/
def iff_controlled : close_maps f g ↔ prod.map f g '' id_rel ∈ 𝓒 β :=
sorry

def refl (f : α → β) : close_maps f f := sorry
def symm (close : close_maps f g) : close_maps g f := sorry
def trans (close_fg : close_maps f g) (close_gh : close_maps g h) : close_maps f h := sorry
def comp_left [coarse_space β] {f g : α → β} (close : close_maps f g) [coarse_space γ] (h : β → γ)
  : close_maps (h ∘ f) (h ∘ g) := sorry
def comp_right [coarse_space β] {f g : α → β} (close : close_maps f g) [coarse_space γ] (h : γ → α)
  : close_maps (f ∘ h) (g ∘ h) := sorry

end close_maps

structure coarse_equiv (α β : Type*) [coarse_space α] [coarse_space β] :=
  (map : α →c β)
  (inv_map : β →c α)
  (close_section : close_maps (map ∘ inv_map) id)
  (close_retraction : close_maps (inv_map ∘ map) id)

infixr ` ≃c `:25 := coarse_equiv

@[protected, instance]
def coarse_equiv.to_coarse_map {α β : Type*} [coarse_space α] [coarse_space β] :
  has_coe (α ≃c β) (α →c β ) :=
  { coe := λ e, e.map }


namespace coarse_equiv
variables [coarse_space β] (f : α ≃c β)

def comp [coarse_space γ] (f : α ≃c β) (g : γ ≃c α) : γ ≃c β := {!!}
def id : α ≃c α := {!!}
def symm (f : α ≃c β) : (β ≃c α) := sorry
def const [coarse_space β] (x : β) : α →c β := {!!}

end coarse_equiv

end coarse_space
