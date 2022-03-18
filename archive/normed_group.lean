import topology.algebra.order.intermediate_value
import analysis.normed.group.basic
import group_theory.basic

/-! normed groups.
-/

--!! I don't think we want this here
--noncomputable theory
open set function real

namespace normed_group

variables {G : Type*}

structure normed_group (G : Type*) extends has_norm G, group G, metric_space G :=
(dist_eq : ∀ x y : G, dist x y = ∥x⁻¹*y∥)

--!! just the fact that there exists a generating set
definition finitely_generated (G : Type*) [group G] : Prop := sorry

--!! also a structure, where we store the group and its generating set

lemma mk_normed_group (G : Type*) [group G] (S : set G) (generates : subgroup.closure S = ⊤) : normed_group G := sorry

-- version of the previous one, where we give length f(s) to s∈S
lemma mk_normed_group_f (G : Type*) [group G] (S : set G) (generates : subgroup.closure S = ⊤) (f : S → ℝ) (pos : ∀(s∈S), f(s) > 0) : normed_group G := sorry

lemma independence_of_generating_set (G : Type*) [group G] (S₁ S₂ : set G) (generates₁ : subgroup.closure S₁ = ⊤) (generates₂ : subgroup.closure S₂ = ⊤) : ∃ K, lipschitz_with K "(id : (mk_normed_group G S₁ generates₁) → (mk_normed_group G S₂ generates₂)" := sorry

end normed_group

namespace group_growth

--!! notation for cardinality?
definition growth (G : Type*) [normed_group G] : ℕ → ℝ := λ n, #{x : G | ∥x∥ ≤ n }

definition dominates (a : ℕ → ℝ) (b : ℕ → ℝ) : Prop := ∃K, ∀n, a(n) ≤ b(K*n)

--!! notation infix:`≾` for dominates
definition equivalent (a : ℕ → ℝ) (b : ℕ → ℝ) : Prop := (dominates a b) ∧ (dominates b a)

lemma growth_independence_of_generating_set (G : Type*) [group G] (S₁ S₂ : set G) (generates₁ : subgroup.closure S₁ = ⊤) (generates₂ : subgroup.closure S₂ = ⊤) : equivalent (growth (mk_normed_group G S₁ generates₁)) (growth (mk_normed_group G S₂ generates₂)) := sorry

--!! define growth types: exponential, polynomial, intermediate

/- then lots of basic lemmas: growth of subgroup is smaller than growth of group; if finite-index subgroup then the growth relate by at most the index; etc.
-/
end group_growth

