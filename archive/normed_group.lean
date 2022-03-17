import topology.algebra.order.intermediate_value
import analysis.normed.group.basic
import group_theory.basic

/-! normed groups.
-/

--!! I don't think we want this here
--noncomputable theory
open set function real

namespace normed_group

variables {E : Type*}

class normed_group (E : Type*) extends has_norm E, group E, metric_space E :=
(dist_eq : ∀ x y : E, dist x y = ∥x*y⁻¹∥)

--!! just the fact that there exists a generating set
definition finitely_generated (E : Type*) [group E] : Prop := sorry

--!! also a structure, where we store the group and its generating set

lemma mk_normed_group (E : Type*) [group E] (S : set E) (generates : subgroup.closure S = ⊤) : normed_group E := sorry

-- version of the previous one, where we give length f(s) to s∈S
lemma mk_normed_group_f (E : Type*) [group E] (S : set E) (generates : subgroup.closure S = ⊤) (f : S → ℝ) (pos : ∀(s∈S), f(s) > 0) : normed_group E := sorry

lemma independence_of_generating_set (E : Type*) [group E] (S₁ S₂ : set E) (generates₁ : subgroup.closure S₁ = ⊤) (generates₂ : subgroup.closure S₂ = ⊤) : ∃ K, lipschitz_with K "(id : (mk_normed_group E S₁ generates₁) → (mk_normed_group E S₂ generates₂)" := sorry

end normed_group

namespace group_growth

--!! notation for cardinality?
definition growth (E : Type*) [normed_group E] : ℕ → ℝ := λ n, #{x : E | ∥x∥ ≤ n }

definition dominates (a : ℕ → ℝ) (b : ℕ → ℝ) : Prop := ∃K, ∀n, a(n) ≤ b(K*n)

--!! notation infix:`≾` for dominates
definition equivalent (a : ℕ → ℝ) (b : ℕ → ℝ) : Prop := (dominates a b) ∧ (dominates b a)

lemma growth_independence_of_generating_set (E : Type*) [group E] (S₁ S₂ : set E) (generates₁ : subgroup.closure S₁ = ⊤) (generates₂ : subgroup.closure S₂ = ⊤) : equivalent (growth (mk_normed_group E S₁ generates₁)) (growth (mk_normed_group E S₂ generates₂)) := sorry

--!! define growth types: exponential, polynomial, intermediate

/- then lots of basic lemmas: growth of subgroup is smaller than growth of group; if finite-index subgroup then the growth relate by at most the index; etc.
-/
end group_growth

