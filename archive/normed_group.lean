import topology.algebra.order.intermediate_value
import analysis.normed.group.basic
--import group_theory.basic
import group_theory.free_group

/-! normed groups.
-/

--!! I don't think we want this here
--noncomputable theory
open set function real

namespace normed_group

section

variables {G S : Type*} [group G] [fintype S] [decidable_eq S]

"""a group with a norm and associated left-invariant metric"""
class normed_group extends has_norm G, metric_space G :=
(dist_eq : ∀ x y : G, dist x y = ∥x⁻¹*y∥)

"""an S-generated group"""
class generated_group (G S : Type*) extends group G :=
(marking : free_group S → G)
(is_surjective : function.surjective marking)

"""an S-generated group, with additionally a norm on generators"""
class norm_generated_group (G S : Type*) extends generated_group G S :=
(Snorm : S → ℝ)
(Spos : ∃ε > 0, ∀s : S, Snorm s ≥ ε)

def list_norm (Snorm : S → ℝ) : list (S × bool) → ℝ
| [] := 0
| (s :: tail) := (Snorm s.fst) + (list_norm tail)

--!! why do I have to repeat "decidable_eq S"?
def free_group_norm (Snorm : S → ℝ) [decidable_eq S] : free_group S → ℝ := λf, list_norm Snorm (free_group.to_word f)

instance gg_to_ngg (GS : generated_group G S) : norm_generated_group G S := { Snorm := λ s, 1, Spos := begin use 1,
split, exact zero_lt_one, intro s, finish end, ..GS }

--!! it's useful to have a norm and a metric. However, there will be lots of code duplication if we're not careful
instance ngg_to_ng (GS : norm_generated_group G S) [decidable_eq S] : normed_group := { norm := λ g, Inf{ (free_group_norm GS.Snorm)'' (GS.marking⁻¹' g)},
dist := sorry,
dist_self := sorry,
dist_comm := sorry,
dist_triangle := sorry,
eq_of_dist_eq_zero := sorry,
dist_eq := sorry,
..GS }

--!! the syntax below is completely wrong
lemma independence_of_generating_set [group G] {S₁ S₂} (GS₁ : norm_generated_group G S₁) (GS₂ : norm_generated_group G S₂) : ∃ K, lipschitz_with K ((λ (g : GS₁), (g : GS₂)) : (normed_group G) → (normed_group G)) := sorry

end

end normed_group

namespace group_growth

--!! notation for cardinality?
def growth (G : Type*) [normed_group G] : ℕ → ℝ := λ n, #{x : G | ∥x∥ ≤ n }

--!! notation for ℝ₊, the positive reals?
def dominates (a : ℕ → ℝ) (b : ℕ → ℝ) : Prop := ∃K, ∀n, a(n) ≤ b(K*n)

--!! notation infix:`≾` for dominates, `∼` for equivalent
def equivalent (a : ℕ → ℝ) (b : ℕ → ℝ) : Prop := (dominates a b) ∧ (dominates b a)

/-
define growth types: exponential, polynomial, intermediate

then lots of basic lemmas: growth of subgroup is smaller than growth of group; if finite-index subgroup then the growth relate by at most the index; etc.
-/
end group_growth

