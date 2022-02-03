/-
Copyright (c) 2022 Daniel Roca González. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Roca González
-/
import order.filter.lift
import topology.subset_properties
import topology.uniform_space.basic
import data.real.nnreal
/-!
# Coarse spaces

TODO give a good explanation of what a controlled space is.

The usual definition of a controlled space is as a `set (set α×α)`
(whose elements are called *controlled sets*):
this is not a filter, but one would call a *cofilter*.
In order to take advantage of filters,
we define a coarse space in terms of its *cocontrolled sets*,
which are the complements of the controlled sets.


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

universe u
variables {α : Type*} {a b : α} {s t : set (α × α)} {β : Type*}

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


section coarse_space
variables [coarse_space α]

def cocontrolled (α : Type u) [s : coarse_space α] : filter (α × α) :=
  @coarse_space.cocontrolled α s

localized "notation `𝓒'` := cocontrolled" in coarse_space

def controlled (α : Type u) [s : coarse_space α] : set (set (α×α)) :=
  compl '' (𝓒' α).sets

localized "notation `𝓒` := controlled" in coarse_space

lemma mem_coarse {s : set (α×α)} : s ∈ 𝓒 α ↔ sᶜ ∈ 𝓒' α :=
begin
  split,
  {rintro h, rcases h with ⟨t, h_h_left, rfl⟩, simpa,},
  {rintro h, use sᶜ, simpa,}
end

lemma cocoarse_le_corefl : 𝓒' α ≤ 𝓟 coid_rel :=
@coarse_space.corefl α _

lemma corefl_mem_cocoarse :
  coid_rel ∈ 𝓒' α :=
begin
  have := @coarse_space.corefl α _,
  simpa,
end

lemma mem_cocoarse_of_eq {x y : α} {s : set (α × α)} (hx : x ≠ y) :
  ∃ s ∈ 𝓒' α, (x, y) ∈ s :=
begin
  use coid_rel,
  split, by {exact corefl_mem_cocoarse},
  simpa,
end

lemma symm_le_cocoarse : map (@prod.swap α α) (𝓒' _) ≤ (𝓒' _) :=
(@coarse_space.symm α _)

lemma cocoarse_le_cocomp : 𝓒' α ≤ (𝓒' α).lift' (λs:set (α×α), s □ s) :=
(@coarse_space.cocomp α _)

lemma tendsto_swap_cocoarse : tendsto (@prod.swap α α) (𝓒' α) (𝓒' α) :=
symm_le_cocoarse

lemma cocomp_mem_cocoarse_sets {s : set (α × α)} (hs : s ∈ 𝓒' α) :
  s □ s ∈ 𝓒' α :=
begin
  apply cocoarse_le_cocomp,
  rw mem_lift'_sets, use s, split,
  {assumption},
  {intros x h, assumption,},
  {refine cocomp_rel.monotone _ _, tidy,}
end

end coarse_space
