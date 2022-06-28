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

variables {G S : Type*} [group G] [fintype S]

"""a group with a norm and associated left-invariant metric"""
class normed_group (G : Type*) [group G] extends has_norm G, metric_space G :=
(dist_eq : ∀ x y : G, dist x y = ∥x⁻¹*y∥)

"""an S-generated group"""
class generated_group (G S : Type*) [group G] :=
(marking : free_group S → G)
(is_surjective : function.surjective marking)

"""an S-generated group, with additionally a norm on generators"""
class norm_generated_group (G S : Type*) [group G] extends generated_group G S :=
(Snorm : S → ℝ)
(Spos : ∃ε > 0, ∀s : S, Snorm s ≥ ε)

--!! I forgot how to lift an element of F to a list (S × Prop)
def free_group_norm (F : free_group S) (Snorm : S → ℝ) : F → ℝ := λf,
| [] -> 0
| [ (s,_) :: tail ] -> (Snorm s) + (free_group_norm F Snorm) tail

instance gg_to_ngg [group G] (GS : generated_group G S) : norm_generated_group G S := { Snorm := λ s, 1, Spos := begin use 1,
split, exact zero_lt_one, intro s, finish end, ..GS }

instance ngg_to_ng [group G] (GS : norm_generated_group G S) : normed_group G := { norm := λ g, inf{ ∥w∥ | w : free_group S, marking w = g }, ..GS }

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

