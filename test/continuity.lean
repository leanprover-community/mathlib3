import topology.tactic
import topology.algebra.monoid
import topology.instances.real
import analysis.special_functions.trigonometric.basic

example {X Y : Type*} [topological_space X] [topological_space Y]
  (f₁ f₂ : X → Y) (hf₁ : continuous f₁) (hf₂ : continuous f₂)
  (g : Y → ℝ) (hg : continuous g) : continuous (λ x, (max (g (f₁ x)) (g (f₂ x))) + 1) :=
by guard_proof_term { continuity } ((hg.comp hf₁).max (hg.comp hf₂)).add continuous_const

example {κ ι : Type}
  (K : κ → Type) [∀ k, topological_space (K k)] (I : ι → Type) [∀ i, topological_space (I i)]
  (e : κ ≃ ι) (F : Π k, homeomorph (K k) (I (e k))) :
  continuous (λ (f : Π k, K k) (i : ι), F (e.symm i) (f (e.symm i))) :=
by guard_proof_term { continuity }
  @continuous_pi _ _ _ _ _ (λ (f : Π k, K k) i, (F (e.symm i)) (f (e.symm i)))
    (λ (i : ι), ((F (e.symm i)).continuous).comp (continuous_apply (e.symm i)))

open real

local attribute [continuity] continuous_exp continuous_sin continuous_cos

example : continuous (λ x : ℝ, exp ((max x (-x)) + sin x)^2) :=
by guard_proof_term { continuity }
  (continuous_exp.comp ((continuous_id.max continuous_id.neg).add continuous_sin)).pow 2

example : continuous (λ x : ℝ, exp ((max x (-x)) + sin (cos x))^2) :=
by guard_proof_term { continuity }
 (continuous_exp.comp ((continuous_id'.max continuous_id'.neg).add (continuous_sin.comp continuous_cos))).pow 2

-- Without `md := semireducible` in the call to `apply_rules` in `continuity`,
-- this last example would have run off the rails:
-- ```
-- example : continuous (λ x : ℝ, exp ((max x (-x)) + sin (cos x))^2) :=
-- by show_term { continuity! }
-- ```
-- produces lots of subgoals, including many copies of
-- ⊢ continuous complex.re
-- ⊢ continuous complex.exp
-- ⊢ continuous coe
-- ⊢ continuous (λ (x : ℝ), ↑x)
