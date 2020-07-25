/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import measure_theory.probability_mass_function

/-! # Topology on probability mass functions -/

noncomputable theory
open_locale classical

-- move this
def nnreal.pure {X : Type*} (x : X) : (X → nnreal) :=
λ y, if y = x then 1 else 0

namespace pmf

def topological_space (α : Type*) : topological_space (pmf α) :=
subtype.topological_space

local attribute [instance] pmf.topological_space

-- lemma metric_pi_topology {α : Type*} [fintype α] {π : α → Type*} [∀ x, metric_space (π x)] :
--   (@metric_space_pi _ π _ _).to_uniform_space.to_topological_space = @Pi.topological_space _ π _ :=
-- _

open_locale big_operators

lemma map_continuous {X Y : Type*} [fintype X] [fintype Y] (f : X → Y) :
  continuous (map f) :=
begin
  apply continuous_subtype_mk,
  apply continuous_pi,
  intro y,
  have aux : ∀ a : pmf X, (∑' x : X, a x * (pmf.pure ∘ f) x y) = ∑ x, a x * (nnreal.pure ∘ f) x y,
  { intro a, apply tsum_eq_sum,
    intros x, contrapose!, intro, exact finset.mem_univ _, },
  simp_rw aux,
  apply continuous_finset_sum,
  intros x hin,
  rw show (λ (a : pmf X), a x * (nnreal.pure ∘ f) x y) =
    ((λ (p : nnreal × nnreal), p.fst * p.snd) ∘ (λ a : pmf X, (a x, ite (y = f x) 1 0))),
  by funext a; simp [function.comp, nnreal.pure],
  have : continuous (λ (a : pmf X), a x),
  { rw show (λ a : pmf X, a x) = (λ a : X → nnreal, a x) ∘ subtype.val, by refl,
    apply (continuous_apply x).comp continuous_induced_dom, },
  exact continuous.mul this (continuous_snd.comp (continuous.prod_mk this continuous_const)),
end

end pmf
