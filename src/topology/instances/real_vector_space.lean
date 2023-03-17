/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.algebra.module.basic
import topology.instances.rat

/-!
# Continuous additive maps are `ℝ`-linear

In this file we prove that a continuous map `f : E →+ F` between two topological vector spaces
over `ℝ` is `ℝ`-linear
-/

variables {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E]
  [has_continuous_smul ℝ E] {F : Type*} [add_comm_group F] [module ℝ F]
  [topological_space F] [has_continuous_smul ℝ F] [t2_space F]

/-- A continuous additive map between two vector spaces over `ℝ` is `ℝ`-linear. -/
lemma map_real_smul {G} [add_monoid_hom_class G E F] (f : G) (hf : continuous f) (c : ℝ) (x : E) :
  f (c • x) = c • f x :=
suffices (λ c : ℝ, f (c • x)) = λ c : ℝ, c • f x, from _root_.congr_fun this c,
rat.dense_embedding_coe_real.dense.equalizer
  (hf.comp $ continuous_id.smul continuous_const)
  (continuous_id.smul continuous_const)
  (funext $ λ r, map_rat_cast_smul f ℝ ℝ r x)

namespace add_monoid_hom

/-- Reinterpret a continuous additive homomorphism between two real vector spaces
as a continuous real-linear map. -/
def to_real_linear_map (f : E →+ F) (hf : continuous f) : E →L[ℝ] F :=
⟨{ to_fun := f, map_add' := f.map_add, map_smul' := map_real_smul f hf }, hf⟩

@[simp] lemma coe_to_real_linear_map (f : E →+ F) (hf : continuous f) :
  ⇑(f.to_real_linear_map hf) = f := rfl

end add_monoid_hom

/-- Reinterpret a continuous additive equivalence between two real vector spaces
as a continuous real-linear map. -/
def add_equiv.to_real_linear_equiv (e : E ≃+ F) (h₁ : continuous e)
  (h₂ : continuous e.symm) : E ≃L[ℝ] F :=
{ .. e,
  .. e.to_add_monoid_hom.to_real_linear_map h₁ }

/-- A topological group carries at most one structure of a topological `ℝ`-module, so for any
topological `ℝ`-algebra `A` (e.g. `A = ℂ`) and any topological group that is both a topological
`ℝ`-module and a topological `A`-module, these structures agree. -/
@[priority 900]
instance real.is_scalar_tower [t2_space E] {A : Type*} [topological_space A]
  [ring A] [algebra ℝ A] [module A E] [has_continuous_smul ℝ A]
  [has_continuous_smul A E] : is_scalar_tower ℝ A E :=
⟨λ r x y, map_real_smul ((smul_add_hom A E).flip y) (continuous_id.smul continuous_const) r x⟩
