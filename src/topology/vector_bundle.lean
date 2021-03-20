/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sebastien Gouezel.
-/

import topology.topological_fiber_bundle
import analysis.calculus.deriv
import linear_algebra.dual

/-!
# Topological vector bundles

In this file we define topological vector bundles.

Let `B` be the base space. In our formalism, a topological vector bundle is by definition the type
`bundle.total_space E` where `E : B → Type*` is a function associating to
`x : B` the fiber over `x`. This type `bundle.total_space E` is just a type synonym for
`Σ (x : B), E x`, with the interest that one can put another topology than on `Σ (x : B), E x`
which has the disjoint union topology.

To have a topological vector bundle structure on `bundle.total_space E`,
one should addtionally have the following data:

* `F` should be a topological vector space over a field `𝕜`;
* There should be a topology on `bundle.total_space E`, for which the projection to `B` is
a topological fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological vector space over `𝕜`, and the injection
from `E x` to `bundle.total_space F E` should be an embedding;
* The most important condition: around each point, there should be a bundle trivialization which
is a continuous linear equiv in the fibers.

If all these conditions are satisfied, we register the typeclass
`topological_vector_bundle 𝕜 F E`. We emphasize that the data is provided by other classes, and
that the `topological_vector_bundle` class is `Prop`-valued.

The point of this formalism is that it is unbundled in the sense that the total space of the bundle
is a type with a topology, with which one can work or put further structure, and still one can
perform operations on topological vector bundles (which are yet to be formalized). For instance,
assume that `E₁ : B → Type*` and `E₂ : B → Type*` define two topological vector bundles over `𝕜`
with fiber models `F₁` and `F₂` which are normed spaces. Then one can construct the vector bundle of
continuous linear maps from `E₁ x` to `E₂ x` with fiber `E x := (E₁ x →L[𝕜] E₂ x)` (and with the
topology inherited from the norm-topology on `F₁ →L[𝕜] F₂`, without the need to define the strong
topology on continuous linear maps between general topological vector spaces). Let
`vector_bundle_continuous_linear_map 𝕜 F₁ E₁ F₂ E₂ (x : B)` be a type synonym for `E₁ x →L[𝕜] E₂ x`.
Then one can endow
`bundle.total_space (vector_bundle_continuous_linear_map 𝕜 F₁ E₁ F₂ E₂)`
with a topology and a topological vector bundle structure.

Similar constructions can be done for tensor products of topological vector bundles, exterior
algebras, and so on, where the topology can be defined using a norm on the fiber model if this
helps.
-/

noncomputable theory


open bundle

variables (𝕜 : Type*) {B : Type*} (F : Type*) (E : B → Type*)
[normed_field 𝕜] [∀ x, add_comm_group (E x)] [∀ x, semimodule 𝕜 (E x)]
[topological_space F] [add_comm_group F] [semimodule 𝕜 F]
[topological_space (total_space E)] [topological_space B]

section

/-- Local trivialization for vector bundles. -/
@[nolint has_inhabited_instance]
structure topological_vector_bundle.trivialization extends bundle_trivialization F (proj E) :=
(linear : ∀ x ∈ base_set, is_linear_map 𝕜 (λ y : (E x), (to_fun y).2))

instance : has_coe_to_fun (topological_vector_bundle.trivialization 𝕜 F E) :=
⟨λ _, (total_space E → B × F), λ e, e.to_bundle_trivialization⟩

instance : has_coe (topological_vector_bundle.trivialization 𝕜 F E)
  (bundle_trivialization F (proj E)) :=
⟨topological_vector_bundle.trivialization.to_bundle_trivialization⟩

namespace topological_vector_bundle

variables {𝕜 F E}

lemma trivialization.mem_source (e : trivialization 𝕜 F E)
  {x : total_space E} : x ∈ e.source ↔ proj E x ∈ e.base_set := bundle_trivialization.mem_source e

end topological_vector_bundle

end

variables [∀ x, topological_space (E x)]

/-- The space `total_space E` (for `E : B → Type*` such that each `E x` is a topological vector
space) has a topological vector space structure with fiber `F` (denoted with
`topological_vector_bundle 𝕜 F E`) if around every point there is a fiber bundle trivialization
which is linear in the fibers. -/
class topological_vector_bundle : Prop :=
(inducing [] : ∀ (b : B), inducing (λ x : (E b), (id ⟨b, x⟩ : total_space E)))
(locally_trivial [] : ∀ b : B, ∃ e : topological_vector_bundle.trivialization 𝕜 F E, b ∈ e.base_set)

variable [topological_vector_bundle 𝕜 F E]

namespace topological_vector_bundle

/-- `trivialization_at 𝕜 F E b` is some choice of trivialization of a vector bundle whose base set
contains a given point `b`. -/
def trivialization_at : Π b : B, trivialization 𝕜 F E :=
λ b, classical.some (topological_vector_bundle.locally_trivial 𝕜 F E b)

@[simp, mfld_simps] lemma mem_base_set_trivialization_at (b : B) :
  b ∈ (trivialization_at 𝕜 F E b).base_set :=
classical.some_spec (topological_vector_bundle.locally_trivial 𝕜 F E b)

@[simp, mfld_simps] lemma mem_source_trivialization_at (z : total_space E) :
  z ∈ (trivialization_at 𝕜 F E z.1).source :=
by { rw bundle_trivialization.mem_source, apply mem_base_set_trivialization_at }

variables {𝕜 F E}

/-- In a topological vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
def trivialization.continuous_linear_equiv_at (e : trivialization 𝕜 F E) (b : B)
  (hb : b ∈ e.base_set) : continuous_linear_equiv 𝕜 (E b) F :=
{ to_fun := λ y, (e ⟨b, y⟩).2,
  inv_fun := λ z, begin
    have : ((e.to_local_homeomorph.symm) (b, z)).fst = b :=
      bundle_trivialization.proj_symm_apply' _ hb,
    have C : E ((e.to_local_homeomorph.symm) (b, z)).fst = E b, by rw this,
    exact cast C (e.to_local_homeomorph.symm (b, z)).2
  end,
  left_inv := begin
    assume v,
    rw [← heq_iff_eq],
    apply (cast_heq _ _).trans,
    have A : (b, (e ⟨b, v⟩).snd) = e ⟨b, v⟩,
    { refine prod.ext _ rfl,
      symmetry,
      exact bundle_trivialization.coe_fst' _ hb },
    have B : e.to_local_homeomorph.symm (e ⟨b, v⟩) = ⟨b, v⟩,
    { apply local_homeomorph.left_inv_on,
      rw bundle_trivialization.mem_source,
      exact hb },
    rw [A, B],
  end,
  right_inv := begin
    assume v,
    have B : e (e.to_local_homeomorph.symm (b, v)) = (b, v),
    { apply local_homeomorph.right_inv_on,
      rw bundle_trivialization.mem_target,
      exact hb },
    have C : (e (e.to_local_homeomorph.symm (b, v))).2 = v, by rw [B],
    conv_rhs { rw ← C },
    dsimp,
    congr,
    ext,
    { exact (bundle_trivialization.proj_symm_apply' _ hb).symm },
    { exact (cast_heq _ _).trans (by refl) },
  end,
  map_add' := λ v w, (e.linear _ hb).map_add v w,
  map_smul' := λ c v, (e.linear _ hb).map_smul c v,
  continuous_to_fun := begin
    refine continuous_snd.comp _,
    apply continuous_on.comp_continuous e.to_local_homeomorph.continuous_on
      (topological_vector_bundle.inducing 𝕜 F E b).continuous (λ x, _),
    rw bundle_trivialization.mem_source,
    exact hb,
  end,
  continuous_inv_fun := begin
    rw (topological_vector_bundle.inducing 𝕜 F E b).continuous_iff,
    dsimp,
    have : continuous (λ (z : F), (e.to_bundle_trivialization.to_local_homeomorph.symm) (b, z)),
    { apply e.to_local_homeomorph.symm.continuous_on.comp_continuous
        (continuous_const.prod_mk continuous_id') (λ z, _),
      simp only [bundle_trivialization.mem_target, hb, local_equiv.symm_source,
        local_homeomorph.symm_to_local_equiv] },
    convert this,
    ext z,
    { exact (bundle_trivialization.proj_symm_apply' _ hb).symm },
    { exact cast_heq _ _ },
  end }

@[simp] lemma trivialization.continuous_linear_equiv_at_apply (e : trivialization 𝕜 F E) (b : B)
  (hb : b ∈ e.base_set) (y : E b) : e.continuous_linear_equiv_at b hb y = (e ⟨b, y⟩).2 := rfl

@[simp] lemma trivialization.continuous_linear_equiv_at_apply' (e : trivialization 𝕜 F E)
  (x : total_space E) (hx : x ∈ e.source) :
  e.continuous_linear_equiv_at (proj E x) (e.mem_source.1 hx) x.2 = (e x).2 :=
by { cases x, refl }

section
local attribute [reducible] bundle.trivial

instance {B : Type*} {F : Type*} [add_comm_group F] (b : B) :
  add_comm_group (bundle.trivial B F b) := by apply_instance

instance {B : Type*} {F : Type*} [add_comm_group F] [semimodule 𝕜 F] (b : B) :
  semimodule 𝕜 (bundle.trivial B F b) := by apply_instance

end

variables (𝕜 B F)
/-- Local trivialization for trivial bundle. -/
def trivial_bundle_trivialization : trivialization 𝕜 F (bundle.trivial B F) :=
{ to_fun := λ x, (x.fst, x.snd),
  inv_fun := λ y, ⟨y.fst, y.snd⟩,
  source := set.univ,
  target := set.univ,
  map_source' := λ x h, set.mem_univ (x.fst, x.snd),
  map_target' :=λ y h,  set.mem_univ ⟨y.fst, y.snd⟩,
  left_inv' := λ x h, sigma.eq rfl rfl,
  right_inv' := λ x h, prod.ext rfl rfl,
  open_source := is_open_univ,
  open_target := is_open_univ,
  continuous_to_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [prod.topological_space, induced_inf, induced_compose], exact le_refl _, },
  continuous_inv_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [bundle.total_space.topological_space, induced_inf, induced_compose],
    exact le_refl _, },
  base_set := set.univ,
  open_base_set := is_open_univ,
  source_eq := rfl,
  target_eq := by simp only [set.univ_prod_univ],
  proj_to_fun := λ y hy, rfl,
  linear := λ x hx, ⟨λ y z, rfl, λ c y, rfl⟩ }

instance trivial_bundle.topological_vector_bundle :
  topological_vector_bundle 𝕜 F (bundle.trivial B F) :=
{ locally_trivial := λ x, ⟨trivial_bundle_trivialization 𝕜 B F, set.mem_univ x⟩,
  inducing := λ b, ⟨begin
    have : (λ (x : trivial B F b), x) = @id F, by { ext x, refl },
    simp only [total_space.topological_space, induced_inf, induced_compose, function.comp, proj,
      induced_const, top_inf_eq, trivial.proj_snd, id.def, trivial.topological_space, this,
      induced_id],
  end⟩ }

variables {𝕜 B F}

/- Not registered as an instance because of a metavariable. -/
lemma is_topological_vector_bundle_is_topological_fiber_bundle :
  is_topological_fiber_bundle F (proj E) :=
λ x, ⟨(trivialization_at 𝕜 F E x).to_bundle_trivialization, mem_base_set_trivialization_at 𝕜 F E x⟩

end topological_vector_bundle
