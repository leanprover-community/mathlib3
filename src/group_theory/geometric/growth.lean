import data.complex.exponential
import group_theory.free_group
import group_theory.geometric.marked_group

/-!
# Growth of groups
-/

-- TOTALLY WIP

noncomputable theory
open function metric real set
open_locale nnreal

namespace geometric_group_theory
variables {G H S : Type*} [group G] (m : marking G S)

lemma finite_balls : ∀ r, set.finite (ball (0 : marked m) r) := sorry

def ball (r : ℝ≥0) : finset (marked m) := (finite_balls m r).to_finset

def growth : ℝ≥0 → ℝ≥0 := λ r, (ball m r).card

def dominates (a : ℝ≥0 → ℝ≥0) (b : ℝ≥0 → ℝ≥0) : Prop := ∃ K, ∀ r, a r ≤ b(K*r)

infix `≾`:10 := dominates

def equivalent (a : ℝ≥0 → ℝ≥0) (b : ℝ≥0 → ℝ≥0) : Prop := dominates a b ∧ dominates b a

infix `∼`:10 := equivalent

def is_exponentially_growing : Prop := ∃ B, (λ r, ⟨exp (B * r), (exp_pos _).le⟩) ≾ growth m

def is_polynomially_growing : Prop := ∃ d : ℕ, growth m ≾ λ r, r^d

/-
then lots of basic lemmas: e.g. growth of subgroup is smaller than growth of group.

growth of virtually nilpotent group is polynomial

growth of soluble group is polynomial or exponential

there exists a group of neither polynomial nor exponential growth
-/

end geometric_group_theory
