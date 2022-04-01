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

variables {G S : Type*} [group G]

-- maybe a bad idea?
structure normed_group (G : Type*) extends has_norm G, metric_space G :=
(dist_eq : ∀ x y : G, dist x y = ∥x⁻¹*y∥)

"""an S-generated group"""
structure generated_group (G S : Type*) :=
(marking : free_group S → G)

structure norm_generated_group (G S :Type*) extends generated_group G S :=
(Snorm : S → ℝ)

-- norm on free group: ∥w∥ = sum of Snorm(s_i) where w = product s_i^{±1} in reduced form

instance : "coercion from generated_group to norm_generated_group" (generated_group G S) (norm_generated_group G S) := ⟨λ GS, { Snorm := λ s, 1, ..GS }⟩

instance : "coerction from norm_generated_group to normed_group" (generated_group G S) (normed_group G) := ⟨λ GS, {norm := λ g, inf{ ∥w∥ | GS.marking w = g }, .. GS }⟩

--! certainly this is not OK: "S" in treated once as a set and once as a type. How do we make this work?
lemma mk_generated_group (G : Type*) (S : set G) (generates : subgroup.closure S = ⊤) : generated_group G S := sorry

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

also: natural norm on generated_group by declaring each generator to have length 1
-/
end group_growth

