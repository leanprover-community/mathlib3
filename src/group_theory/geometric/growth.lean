import analysis.normed.group.basic
import data.complex.exponential
import group_theory.free_group
import order.well_founded
import group_theory.geometric.marked_group

/-! growth of groups.
-/

-- TOTALLY WIP

noncomputable theory
open set function real

namespace geometric_group_theory

section group_growth

notation `ℝ₊` := nnreal

--variables {G S : Type*} [group G] [decidable_eq S] (m : marking S G)
variables {m G : Type*} [marked_group m G]

-- this doesn't work, it seems that the instance [has_norm] G] didn't propagate
def ball0 (r : ℝ₊) : set G := { x | ∥x∥ ≤ r }

lemma finite_balls : ∀ r, set.finite (ball0 r) := sorry

def ball (r : ℝ₊) : finset G := (finite_balls G r)


def growth : ℝ₊ → ℝ₊ := λ r, (ball G r).card

def dominates (a : ℝ₊ → ℝ₊) (b : ℝ₊ → ℝ₊) : Prop := ∃K, ∀r, a(r) ≤ b(K*r)
infix `≾`:10 := dominates

def equivalent (a : ℝ₊ → ℝ₊) (b : ℝ₊ → ℝ₊) : Prop := (dominates a b) ∧ (dominates b a)
infix `∼`:10 := equivalent

def is_exponentially_growing (G : Type*) [marked_group G] : Prop := ∃B, growth r ≿ λr, exp(C*r)

def is_polynomially_growing (G : Type*) [marked_group G] : Prop := ∃(d : ℕ), growth ≾ λr, r^d

variables {G H : Type} [marked_group G] [marked_group H]

/-
then lots of basic lemmas: e.g. growth of subgroup is smaller than growth of group.

growth of virtually nilpotent group is polynomial

growth of soluble group is polynomial or exponential

there exists a group of neither polynomial nor exponential growth
-/

end group_growth

end geometric_group_theory
