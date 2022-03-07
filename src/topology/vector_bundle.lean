/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sebastien Gouezel
-/

import topology.fiber_bundle
import topology.algebra.module.basic

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

* `F` should be a topological space and a module over a semiring `R`;
* There should be a topology on `bundle.total_space E`, for which the projection to `B` is
a topological fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological vector space over `R`, and the injection
from `E x` to `bundle.total_space F E` should be an embedding;
* The most important condition: around each point, there should be a bundle trivialization which
is a continuous linear equiv in the fibers.

If all these conditions are satisfied, we register the typeclass
`topological_vector_bundle R F E`. We emphasize that the data is provided by other classes, and
that the `topological_vector_bundle` class is `Prop`-valued.

The point of this formalism is that it is unbundled in the sense that the total space of the bundle
is a type with a topology, with which one can work or put further structure, and still one can
perform operations on topological vector bundles.  For instance, assume that `E₁ : B → Type*` and
`E₂ : B → Type*` define two topological vector bundles over `R` with fiber models `F₁` and `F₂`
which are normed spaces. Then we construct the vector bundle of direct sums, with fiber
`E x := (E₁ x × E₂ x)`. We let `vector_bundle_prod R F₁ E₁ F₂ E₂ (x : B)` be a type
synonym for `E₁ x × E₂ x`. Then one can endow `bundle.total_space (vector_prod R F₁ E₁ F₂ E₂)`
with a topology `vector_bundle_prod.topological_space`, and a topological vector bundle structure,
`vector_bundle_prod.topological_vector_bundle`.

A similar construction (which is yet to be formalized) can be done for the vector bundle of
continuous linear maps from `E₁ x` to `E₂ x` with fiber `E x := (E₁ x →L[R] E₂ x)` (and with the
topology inherited from the norm-topology on `F₁ →L[R] F₂`, without the need to define the strong
topology on continuous linear maps between general topological vector spaces).  Likewise for tensor
products of topological vector bundles, exterior algebras, and so on, where the topology can be
defined using a norm on the fiber model if this helps.

## Tags
Vector bundle
-/

noncomputable theory

open bundle set

variables (R : Type*) {B : Type*} (F : Type*) (E : B → Type*)
[semiring R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
[topological_space F] [add_comm_monoid F] [module R F] [topological_space B]

section

/-- Local pretrivialization for vector prebundles. -/
@[nolint has_inhabited_instance]
structure topological_vector_bundle.pretrivialization extends to_fiber_bundle_pretrivialization :
  topological_fiber_bundle.pretrivialization F (proj E) :=
(linear : ∀ x ∈ base_set, is_linear_map R (λ y : (E x), (to_fun y).2))

instance : has_coe_to_fun (topological_vector_bundle.pretrivialization R F E) _ := ⟨λ e, e.to_fun⟩

instance : has_coe (topological_vector_bundle.pretrivialization R F E)
  (topological_fiber_bundle.pretrivialization F (proj E)) :=
⟨topological_vector_bundle.pretrivialization.to_fiber_bundle_pretrivialization⟩

variable [topological_space (total_space E)]

/-- Local trivialization for vector bundles. -/
@[nolint has_inhabited_instance]
structure topological_vector_bundle.trivialization extends to_fiber_bundle_trivialization :
  topological_fiber_bundle.trivialization F (proj E) :=
(linear : ∀ x ∈ base_set, is_linear_map R (λ y : (E x), (to_fun y).2))

open topological_vector_bundle

instance : has_coe_to_fun (trivialization R F E) (λ _, total_space E → B × F) := ⟨λ e, e.to_fun⟩

instance : has_coe (trivialization R F E) (topological_fiber_bundle.trivialization F (proj E)) :=
⟨topological_vector_bundle.trivialization.to_fiber_bundle_trivialization⟩

namespace topological_vector_bundle

variables {R F E}

/-- Natural identification as `topological_vector_bundle.pretrivialization`. -/
def trivialization.to_pretrivialization (e : trivialization R F E) :
  topological_vector_bundle.pretrivialization R F E := { ..e }

lemma trivialization.mem_source (e : trivialization R F E)
  {x : total_space E} : x ∈ e.source ↔ proj E x ∈ e.base_set :=
topological_fiber_bundle.trivialization.mem_source e

@[simp, mfld_simps] lemma trivialization.coe_coe (e : trivialization R F E) :
  ⇑e.to_local_homeomorph = e := rfl

@[simp, mfld_simps] lemma trivialization.coe_fst (e : trivialization R F E) {x : total_space E}
  (ex : x ∈ e.source) : (e x).1 = (proj E) x := e.proj_to_fun x ex

end topological_vector_bundle

variables [∀ x, topological_space (E x)]

/-- The space `total_space E` (for `E : B → Type*` such that each `E x` is a topological vector
space) has a topological vector space structure with fiber `F` (denoted with
`topological_vector_bundle R F E`) if around every point there is a fiber bundle trivialization
which is linear in the fibers. -/
class topological_vector_bundle : Prop :=
(total_space_mk_inducing [] : ∀ (b : B), inducing (total_space_mk E b))
(locally_trivial [] : ∀ b : B, ∃ e : topological_vector_bundle.trivialization R F E, b ∈ e.base_set)

variable [topological_vector_bundle R F E]

namespace topological_vector_bundle

/-- `trivialization_at R F E b` is some choice of trivialization of a vector bundle whose base set
contains a given point `b`. -/
def trivialization_at : Π b : B, trivialization R F E :=
λ b, classical.some (locally_trivial R F E b)

@[simp, mfld_simps] lemma mem_base_set_trivialization_at (b : B) :
  b ∈ (trivialization_at R F E b).base_set :=
classical.some_spec (locally_trivial R F E b)

@[simp, mfld_simps] lemma mem_source_trivialization_at (z : total_space E) :
  z ∈ (trivialization_at R F E z.1).source :=
by { rw topological_fiber_bundle.trivialization.mem_source, apply mem_base_set_trivialization_at }

variables {R F E}

namespace trivialization

/-- In a topological vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
def continuous_linear_equiv_at (e : trivialization R F E) (b : B)
  (hb : b ∈ e.base_set) : E b ≃L[R] F :=
{ to_fun := λ y, (e ⟨b, y⟩).2,
  inv_fun := λ z, begin
    have : ((e.to_local_homeomorph.symm) (b, z)).fst = b :=
      topological_fiber_bundle.trivialization.proj_symm_apply' _ hb,
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
      exact topological_fiber_bundle.trivialization.coe_fst' _ hb },
    have B : e.to_local_homeomorph.symm (e ⟨b, v⟩) = ⟨b, v⟩,
    { apply local_homeomorph.left_inv_on,
      rw topological_fiber_bundle.trivialization.mem_source,
      exact hb },
    rw [A, B],
  end,
  right_inv := begin
    assume v,
    have B : e (e.to_local_homeomorph.symm (b, v)) = (b, v),
    { apply local_homeomorph.right_inv_on,
      rw topological_fiber_bundle.trivialization.mem_target,
      exact hb },
    have C : (e (e.to_local_homeomorph.symm (b, v))).2 = v, by rw [B],
    conv_rhs { rw ← C },
    dsimp,
    congr,
    ext,
    { exact (topological_fiber_bundle.trivialization.proj_symm_apply' _ hb).symm },
    { exact (cast_heq _ _).trans (by refl) },
  end,
  map_add' := λ v w, (e.linear _ hb).map_add v w,
  map_smul' := λ c v, (e.linear _ hb).map_smul c v,
  continuous_to_fun := begin
    refine continuous_snd.comp _,
    apply continuous_on.comp_continuous e.to_local_homeomorph.continuous_on
      (topological_vector_bundle.total_space_mk_inducing R F E b).continuous (λ x, _),
    rw topological_fiber_bundle.trivialization.mem_source,
    exact hb,
  end,
  continuous_inv_fun := begin
    rw (topological_vector_bundle.total_space_mk_inducing R F E b).continuous_iff,
    dsimp,
    have : continuous (λ (z : F), e.to_fiber_bundle_trivialization.to_local_homeomorph.symm (b, z)),
    { apply e.to_local_homeomorph.symm.continuous_on.comp_continuous
        (continuous_const.prod_mk continuous_id') (λ z, _),
      simp only [topological_fiber_bundle.trivialization.mem_target, hb, local_equiv.symm_source,
        local_homeomorph.symm_to_local_equiv] },
    convert this,
    ext z,
    { exact (topological_fiber_bundle.trivialization.proj_symm_apply' _ hb).symm },
    { exact cast_heq _ _ },
  end }

@[simp] lemma continuous_linear_equiv_at_apply (e : trivialization R F E) (b : B)
  (hb : b ∈ e.base_set) (y : E b) : e.continuous_linear_equiv_at b hb y = (e ⟨b, y⟩).2 := rfl

@[simp] lemma continuous_linear_equiv_at_apply' (e : trivialization R F E)
  (x : total_space E) (hx : x ∈ e.source) :
  e.continuous_linear_equiv_at (proj E x) (e.mem_source.1 hx) x.2 = (e x).2 := by { cases x, refl }

lemma apply_eq_prod_continuous_linear_equiv_at (e : trivialization R F E) (b : B)
  (hb : b ∈ e.base_set) (z : E b) :
  e.to_local_homeomorph ⟨b, z⟩ = ⟨b, e.continuous_linear_equiv_at b hb z⟩ :=
begin
  ext,
  { convert e.coe_fst _,
    rw e.source_eq,
    exact hb },
  { simp }
end

lemma symm_apply_eq_prod_continuous_linear_equiv_at_symm (e : trivialization R F E) (b : B)
  (hb : b ∈ e.base_set) (z : F) :
  e.to_local_homeomorph.symm ⟨b, z⟩ = ⟨b, (e.continuous_linear_equiv_at b hb).symm z⟩ :=
begin
  have h : (b, z) ∈ e.to_local_homeomorph.target,
  { rw e.target_eq,
    exact ⟨hb, mem_univ _⟩ },
  apply e.to_local_homeomorph.inj_on (e.to_local_homeomorph.map_target h),
  { simp [e.source_eq, hb] },
  simp [-continuous_linear_equiv_at_apply, e.apply_eq_prod_continuous_linear_equiv_at b hb,
    e.to_local_homeomorph.right_inv h],
end

end trivialization

section
local attribute [reducible] bundle.trivial

instance {B : Type*} {F : Type*} [add_comm_monoid F] (b : B) :
  add_comm_monoid (bundle.trivial B F b) := ‹add_comm_monoid F›

instance {B : Type*} {F : Type*} [add_comm_group F] (b : B) :
  add_comm_group (bundle.trivial B F b) := ‹add_comm_group F›

instance {B : Type*} {F : Type*} [add_comm_monoid F] [module R F] (b : B) :
  module R (bundle.trivial B F b) := ‹module R F›

end

variables (R B F)
/-- Local trivialization for trivial bundle. -/
def trivial_topological_vector_bundle.trivialization : trivialization R F (bundle.trivial B F) :=
{ to_fun := λ x, (x.fst, x.snd),
  inv_fun := λ y, ⟨y.fst, y.snd⟩,
  source := univ,
  target := univ,
  map_source' := λ x h, mem_univ (x.fst, x.snd),
  map_target' :=λ y h,  mem_univ ⟨y.fst, y.snd⟩,
  left_inv' := λ x h, sigma.eq rfl rfl,
  right_inv' := λ x h, prod.ext rfl rfl,
  open_source := is_open_univ,
  open_target := is_open_univ,
  continuous_to_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [prod.topological_space, induced_inf, induced_compose], exact le_rfl, },
  continuous_inv_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [bundle.total_space.topological_space, induced_inf, induced_compose],
    exact le_rfl, },
  base_set := univ,
  open_base_set := is_open_univ,
  source_eq := rfl,
  target_eq := by simp only [univ_prod_univ],
  proj_to_fun := λ y hy, rfl,
  linear := λ x hx, ⟨λ y z, rfl, λ c y, rfl⟩ }

instance trivial_bundle.topological_vector_bundle :
  topological_vector_bundle R F (bundle.trivial B F) :=
{ locally_trivial := λ x, ⟨trivial_topological_vector_bundle.trivialization R B F, mem_univ x⟩,
  total_space_mk_inducing := λ b, ⟨begin
    have : (λ (x : trivial B F b), x) = @id F, by { ext x, refl },
    simp only [total_space.topological_space, induced_inf, induced_compose, function.comp, proj,
      induced_const, top_inf_eq, trivial.proj_snd, id.def, trivial.topological_space, this,
      induced_id],
  end⟩ }

variables {R B F}

/- Not registered as an instance because of a metavariable. -/
lemma is_topological_vector_bundle_is_topological_fiber_bundle :
  is_topological_fiber_bundle F (proj E) :=
λ x, ⟨(trivialization_at R F E x).to_fiber_bundle_trivialization,
  mem_base_set_trivialization_at R F E x⟩

variables (R B F)
include R F
@[continuity] lemma continuous_proj : continuous (proj E) :=
begin
  apply @is_topological_fiber_bundle.continuous_proj B F,
  apply @is_topological_vector_bundle_is_topological_fiber_bundle R,
end
omit F

end topological_vector_bundle

/-! ### Constructing topological vector bundles -/

variables (B)

/-- Analogous construction of `topological_fiber_bundle_core` for vector bundles. This
construction gives a way to construct vector bundles from a structure registering how
trivialization changes act on fibers.-/
@[nolint has_inhabited_instance]
structure topological_vector_bundle_core (ι : Type*) :=
(base_set          : ι → set B)
(is_open_base_set  : ∀ i, is_open (base_set i))
(index_at          : B → ι)
(mem_base_set_at   : ∀ x, x ∈ base_set (index_at x))
(coord_change      : ι → ι → B → (F →ₗ[R] F))
(coord_change_self : ∀ i, ∀ x ∈ base_set i, ∀ v, coord_change i i x v = v)
(coord_change_continuous : ∀ i j, continuous_on (λp : B × F, coord_change i j p.1 p.2)
                                               (((base_set i) ∩ (base_set j)) ×ˢ (univ : set F)))
(coord_change_comp : ∀ i j k, ∀ x ∈ (base_set i) ∩ (base_set j) ∩ (base_set k), ∀ v,
  (coord_change j k x) (coord_change i j x v) = coord_change i k x v)

attribute [simp, mfld_simps] topological_vector_bundle_core.mem_base_set_at

namespace topological_vector_bundle_core

variables {R B F} {ι : Type*} (Z : topological_vector_bundle_core R B F ι)

/-- Natural identification to a `topological_fiber_bundle_core`. -/
def to_topological_vector_bundle_core : topological_fiber_bundle_core ι B F :=
{ coord_change := λ i j b, Z.coord_change i j b, ..Z }

instance to_topological_vector_bundle_core_coe : has_coe (topological_vector_bundle_core R B F ι)
  (topological_fiber_bundle_core ι B F) := ⟨to_topological_vector_bundle_core⟩

include Z

lemma coord_change_linear_comp (i j k : ι): ∀ x ∈ (Z.base_set i) ∩ (Z.base_set j) ∩ (Z.base_set k),
  (Z.coord_change j k x).comp (Z.coord_change i j x) = Z.coord_change i k x :=
λ x hx, by { ext v, exact Z.coord_change_comp i j k x hx v }

/-- The index set of a topological vector bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments has_inhabited_instance]
def index := ι

/-- The base space of a topological vector bundle core, as a convenience function for dot notation-/
@[nolint unused_arguments, reducible]
def base := B

/-- The fiber of a topological vector bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_inhabited_instance]
def fiber (x : B) := F

section fiber_instances

local attribute [reducible] fiber --just to record instances

instance topological_space_fiber (x : B) : topological_space (Z.fiber x) := by apply_instance
instance add_comm_monoid_fiber : ∀ (x : B), add_comm_monoid (Z.fiber x) := λ x, by apply_instance
instance module_fiber : ∀ (x : B), module R (Z.fiber x) := λ x, by apply_instance

end fiber_instances

/-- The projection from the total space of a topological fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps] def proj : total_space Z.fiber → B := bundle.proj Z.fiber

/-- Local homeomorphism version of the trivialization change. -/
def triv_change (i j : ι) : local_homeomorph (B × F) (B × F) :=
topological_fiber_bundle_core.triv_change ↑Z i j

@[simp, mfld_simps] lemma mem_triv_change_source (i j : ι) (p : B × F) :
  p ∈ (Z.triv_change i j).source ↔ p.1 ∈ Z.base_set i ∩ Z.base_set j :=
topological_fiber_bundle_core.mem_triv_change_source ↑Z i j p

variable (ι)

/-- Topological structure on the total space of a topological bundle created from core, designed so
that all the local trivialization are continuous. -/
instance to_topological_space : topological_space (total_space Z.fiber) :=
topological_fiber_bundle_core.to_topological_space ι ↑Z

variables {ι} (b : B) (a : F)

@[simp, mfld_simps] lemma coe_cord_change (i j : ι) :
  topological_fiber_bundle_core.coord_change ↑Z i j b = Z.coord_change i j b := rfl

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def local_triv (i : ι) : topological_vector_bundle.trivialization R F Z.fiber :=
{ linear := λ x hx,
  { map_add := λ v w, by simp only [linear_map.map_add] with mfld_simps,
    map_smul := λ r v, by simp only [linear_map.map_smul] with mfld_simps},
  ..topological_fiber_bundle_core.local_triv ↑Z i }

@[simp, mfld_simps] lemma mem_local_triv_source (i : ι) (p : total_space Z.fiber) :
  p ∈ (Z.local_triv i).source ↔ p.1 ∈ Z.base_set i :=
iff.rfl

/-- Preferred local trivialization of a vector bundle constructed from core, at a given point, as
a bundle trivialization -/
def local_triv_at (b : B) : topological_vector_bundle.trivialization R F Z.fiber :=
Z.local_triv (Z.index_at b)

lemma mem_source_at : (⟨b, a⟩ : total_space Z.fiber) ∈ (Z.local_triv_at b).source :=
by { rw [local_triv_at, mem_local_triv_source], exact Z.mem_base_set_at b }

@[simp, mfld_simps] lemma local_triv_at_apply : ((Z.local_triv_at b) ⟨b, a⟩) = ⟨b, a⟩ :=
topological_fiber_bundle_core.local_triv_at_apply Z b a

instance : topological_vector_bundle R F Z.fiber :=
{ total_space_mk_inducing := λ b, ⟨ begin refine le_antisymm _ (λ s h, _),
    { rw ←continuous_iff_le_induced,
      exact topological_fiber_bundle_core.continuous_total_space_mk ↑Z b, },
    { refine is_open_induced_iff.mpr ⟨(Z.local_triv_at b).source ∩ (Z.local_triv_at b) ⁻¹'
        ((Z.local_triv_at b).base_set ×ˢ s), (continuous_on_open_iff
        (Z.local_triv_at b).open_source).mp (Z.local_triv_at b).continuous_to_fun _
        ((Z.local_triv_at b).open_base_set.prod h), _⟩,
      rw [preimage_inter, ←preimage_comp, function.comp],
      simp only [total_space_mk],
      refine ext_iff.mpr (λ a, ⟨λ ha, _, λ ha, ⟨Z.mem_base_set_at b, _⟩⟩),
      { simp only [mem_prod, mem_preimage, mem_inter_eq, local_triv_at_apply] at ha,
        exact ha.2.2, },
      { simp only [mem_prod, mem_preimage, mem_inter_eq, local_triv_at_apply],
        exact ⟨Z.mem_base_set_at b, ha⟩, } } end⟩,
  locally_trivial := λ b, ⟨Z.local_triv_at b, Z.mem_base_set_at b⟩, }

/-- The projection on the base of a topological vector bundle created from core is continuous -/
@[continuity] lemma continuous_proj : continuous Z.proj :=
topological_fiber_bundle_core.continuous_proj Z

/-- The projection on the base of a topological vector bundle created from core is an open map -/
lemma is_open_map_proj : is_open_map Z.proj :=
topological_fiber_bundle_core.is_open_map_proj Z

end topological_vector_bundle_core

end

section

/-! ### Topological vector prebundle -/

variable [∀ x, topological_space (E x)]

open topological_space

/-- This structure permits to define a vector bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space. The total space is hence given a
topology in such a way that there is a fiber bundle structure for which the local equivalences
are also local homeomorphism and hence vector bundle trivializations. -/
@[nolint has_inhabited_instance]
structure topological_vector_prebundle :=
(pretrivialization_at : B → topological_vector_bundle.pretrivialization R F E)
(mem_base_pretrivialization_at : ∀ x : B, x ∈ (pretrivialization_at x).base_set)
(continuous_triv_change : ∀ x y : B, continuous_on ((pretrivialization_at x) ∘
  (pretrivialization_at y).to_local_equiv.symm) ((pretrivialization_at y).target ∩
  ((pretrivialization_at y).to_local_equiv.symm ⁻¹' (pretrivialization_at x).source)))
(total_space_mk_inducing : ∀ (b : B), inducing ((pretrivialization_at b) ∘ (total_space_mk E b)))

namespace topological_vector_prebundle

variables {R E F}

/-- Natural identification of `topological_vector_prebundle` as a `topological_fiber_prebundle`. -/
def to_topological_fiber_prebundle (a : topological_vector_prebundle R F E) :
  topological_fiber_prebundle F (proj E) :=
{ pretrivialization_at := λ x, a.pretrivialization_at x, ..a }

/-- Topology on the total space that will make the prebundle into a bundle. -/
def total_space_topology (a : topological_vector_prebundle R F E) :
  topological_space (total_space E) :=
a.to_topological_fiber_prebundle.total_space_topology

/-- Promotion from a `topologial_vector_prebundle.trivialization` to a
  `topological_vector_bundle.trivialization`. -/
def trivialization_at (a : topological_vector_prebundle R F E) (x : B) :
  @topological_vector_bundle.trivialization R _ F E _ _ _ _ _ _ _ a.total_space_topology :=
begin
  letI := a.total_space_topology,
  exact { linear := (a.pretrivialization_at x).linear,
  ..a.to_topological_fiber_prebundle.trivialization_at x }
end

variable (a : topological_vector_prebundle R F E)

lemma mem_trivialization_at_source (b : B) (x : E b) :
  total_space_mk E b x ∈ (a.pretrivialization_at b).source :=
begin
  simp only [(a.pretrivialization_at b).source_eq, mem_preimage, proj],
  exact a.mem_base_pretrivialization_at b,
end

@[simp] lemma total_space_mk_preimage_source (b : B) :
  (total_space_mk E b) ⁻¹' (a.pretrivialization_at b).source = univ :=
begin
  apply eq_univ_of_univ_subset,
  rw [(a.pretrivialization_at b).source_eq, ←preimage_comp, function.comp],
  simp only [proj],
  rw preimage_const_of_mem _,
  exact a.mem_base_pretrivialization_at b,
end

@[continuity] lemma continuous_total_space_mk (b : B) :
  @continuous _ _ _ a.total_space_topology (total_space_mk E b) :=
begin
  letI := a.total_space_topology,
  rw (a.trivialization_at b).to_local_homeomorph.continuous_iff_continuous_comp_left
    (a.total_space_mk_preimage_source b),
  exact continuous_iff_le_induced.mpr (le_antisymm_iff.mp (a.total_space_mk_inducing b).induced).1,
end

lemma inducing_total_space_mk_of_inducing_comp (b : B)
  (h : inducing ((a.trivialization_at b) ∘ (total_space_mk E b))) :
  @inducing _ _ _ a.total_space_topology (total_space_mk E b) :=
begin
  letI := a.total_space_topology,
  rw ←restrict_comp_cod_restrict (a.mem_trivialization_at_source b) at h,
  apply inducing.of_cod_restrict (a.mem_trivialization_at_source b),
  refine inducing_of_inducing_compose _ (continuous_on_iff_continuous_restrict.mp
    (a.trivialization_at b).continuous_to_fun) h,
  exact (a.continuous_total_space_mk b).cod_restrict (a.mem_trivialization_at_source b),
end

lemma to_topological_vector_bundle :
  @topological_vector_bundle R _ F E _ _ _ _ _ _ _ a.total_space_topology _ :=
{ total_space_mk_inducing := λ b, a.inducing_total_space_mk_of_inducing_comp b
    (a.total_space_mk_inducing b),
  locally_trivial := λ b, ⟨a.trivialization_at b, a.mem_base_pretrivialization_at b⟩ }

end topological_vector_prebundle

end

/-! ### Direct sum of two vector bundles over the same base -/

namespace topological_vector_bundle

/-- The direct sum of the topological vector bundles `E₁` and `E₂`.  Type synonym for
`λ x, E₁ x × E₂ x`. -/
@[derive [topological_space, add_comm_monoid, module R], nolint unused_arguments]
def vector_bundle_prod {B : Type*}
  (F₁ : Type*) (E₁ : B → Type*) [Π x, add_comm_monoid (E₁ x)] [Π x, module R (E₁ x)]
  [Π x : B, topological_space (E₁ x)]
  (F₂ : Type*) (E₂ : B → Type*) [Π x, add_comm_monoid (E₂ x)] [∀ x, module R (E₂ x)]
  [Π x : B, topological_space (E₂ x)]
  (x : B) :=
E₁ x × E₂ x

instance {B : Type*}
  (F₁ : Type*) (E₁ : B → Type*) [Π x, add_comm_monoid (E₁ x)] [Π x, module R (E₁ x)]
  [Π x : B, topological_space (E₁ x)]
  (F₂ : Type*) (E₂ : B → Type*) [Π x, add_comm_monoid (E₂ x)] [∀ x, module R (E₂ x)]
  [Π x : B, topological_space (E₂ x)]
  (x : B) :
  inhabited (vector_bundle_prod R F₁ E₁ F₂ E₂ x) :=
⟨0⟩

variables (F₁ : Type*) [topological_space F₁] [add_comm_monoid F₁] [module R F₁]
  (E₁ : B → Type*) [Π x, add_comm_monoid (E₁ x)] [Π x, module R (E₁ x)]
  [Π x : B, topological_space (E₁ x)] [topological_space (total_space E₁)]

variables (F₂ : Type*) [topological_space F₂] [add_comm_monoid F₂] [module R F₂]
  (E₂ : B → Type*) [Π x, add_comm_monoid (E₂ x)] [Π x, module R (E₂ x)]
  [Π x : B, topological_space (E₂ x)] [topological_space (total_space E₂)]

namespace pretrivialization
variables (e₁ : trivialization R F₁ E₁) (e₂ : trivialization R F₂ E₂)
include e₁ e₂
variables {R F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the forward
function for the construction `topological_vector_bundle.pretrivialization.prod`, the induced
pretrivialization for the direct sum of `E₁` and `E₂`. -/
def prod.to_fun' : total_space (vector_bundle_prod R F₁ E₁ F₂ E₂) → B × (F₁ × F₂) :=
λ ⟨x, v₁, v₂⟩, ⟨x, (e₁ ⟨x, v₁⟩).2, (e₂ ⟨x, v₂⟩).2⟩

variables [topological_vector_bundle R F₁ E₁] [topological_vector_bundle R F₂ E₂]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the inverse
function for the construction `topological_vector_bundle.pretrivialization.prod`, the induced
pretrivialization for the direct sum of `E₁` and `E₂`. -/
def prod.inv_fun' (p : B × (F₁ × F₂)) : total_space (vector_bundle_prod R F₁ E₁ F₂ E₂) :=
begin
  obtain ⟨x, w₁, w₂⟩ := p,
  refine ⟨x, _, _⟩,
  { by_cases h : x ∈ e₁.base_set,
    { exact (e₁.continuous_linear_equiv_at x h).symm w₁ },
    { exact 0 } },
  { by_cases h : x ∈ e₂.base_set,
    { exact (e₂.continuous_linear_equiv_at x h).symm w₂ },
    { exact 0 } },
end

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
pretrivialization for the direct sum of `E₁` and `E₂`.  That is, the map which will later become
a trivialization, after this direct sum is equipped with the right topological vector bundle
structure. -/
def prod : pretrivialization R (F₁ × F₂) (vector_bundle_prod R F₁ E₁ F₂ E₂) :=
{ to_fun := prod.to_fun' e₁ e₂,
  inv_fun := prod.inv_fun' e₁ e₂,
  source := (proj (λ x, E₁ x × E₂ x)) ⁻¹' (e₁.base_set.inter e₂.base_set),
  target := (e₁.base_set.inter e₂.base_set) ×ˢ (set.univ : set (F₁ × F₂)),
  map_source' := λ ⟨x, v₁, v₂⟩ h, ⟨h, set.mem_univ _⟩,
  map_target' := λ ⟨x, w₁, w₂⟩ h, h.1,
  left_inv' := λ ⟨x, v₁, v₂⟩ h,
  begin
    simp only [prod.to_fun', prod.inv_fun', sigma.mk.inj_iff, true_and, eq_self_iff_true,
      prod.mk.inj_iff, heq_iff_eq],
    split,
    { rw [dif_pos, ← e₁.continuous_linear_equiv_at_apply x h.1,
        continuous_linear_equiv.symm_apply_apply] },
    { rw [dif_pos, ← e₂.continuous_linear_equiv_at_apply x h.2,
        continuous_linear_equiv.symm_apply_apply] },
  end,
  right_inv' := λ ⟨x, w₁, w₂⟩ ⟨h, _⟩,
  begin
    dsimp [prod.to_fun', prod.inv_fun'],
    simp only [prod.mk.inj_iff, eq_self_iff_true, true_and],
    split,
    { rw [dif_pos, ← e₁.continuous_linear_equiv_at_apply x h.1,
        continuous_linear_equiv.apply_symm_apply] },
    { rw [dif_pos, ← e₂.continuous_linear_equiv_at_apply x h.2,
        continuous_linear_equiv.apply_symm_apply] },
  end,
  open_target := (e₁.open_base_set.inter e₂.open_base_set).prod is_open_univ,
  base_set := e₁.base_set.inter e₂.base_set,
  open_base_set := e₁.open_base_set.inter e₂.open_base_set,
  source_eq := rfl,
  target_eq := rfl,
  proj_to_fun := λ ⟨x, v₁, v₂⟩ h, rfl,
  linear := λ x ⟨h₁, h₂⟩,
  { map_add := λ ⟨v₁, v₂⟩ ⟨v₁', v₂'⟩,
      congr_arg2 prod.mk ((e₁.linear x h₁).map_add v₁ v₁') ((e₂.linear x h₂).map_add v₂ v₂'),
    map_smul := λ c ⟨v₁, v₂⟩,
      congr_arg2 prod.mk ((e₁.linear x h₁).map_smul c v₁) ((e₂.linear x h₂).map_smul c v₂), } }

@[simp] lemma base_set_prod (e₁ : trivialization R F₁ E₁) (e₂ : trivialization R F₂ E₂) :
  (prod e₁ e₂).base_set = e₁.base_set ∩ e₂.base_set :=
rfl

lemma open_base_set_prod (e₁ : trivialization R F₁ E₁) (e₂ : trivialization R F₂ E₂) :
  is_open (prod e₁ e₂).base_set :=
begin
  rw base_set_prod,
  exact e₁.to_pretrivialization.open_base_set.inter e₂.open_base_set,
end

@[simp] lemma prod_apply {e₁ : trivialization R F₁ E₁}
  {e₂ : trivialization R F₂ E₂} {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set)
  (v₁ : E₁ x) (v₂ : E₂ x) :
  prod e₁ e₂ ⟨x, (v₁, v₂)⟩
  = ⟨x, e₁.continuous_linear_equiv_at x hx₁ v₁, e₂.continuous_linear_equiv_at x hx₂ v₂⟩ :=
rfl

lemma prod_symm_apply {e₁ : trivialization R F₁ E₁}
  {e₂ : trivialization R F₂ E₂} {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set)
  (w₁ : F₁) (w₂ : F₂) :
  (prod e₁ e₂).to_local_equiv.symm (x, (w₁, w₂))
  = ⟨x, ((e₁.continuous_linear_equiv_at x hx₁).symm w₁,
      (e₂.continuous_linear_equiv_at x hx₂).symm w₂)⟩ :=
begin
  dsimp [prod, prod.inv_fun'],
  rw [dif_pos, dif_pos]
end

lemma continuous_triv_change_prod
  (e₁ f₁ : trivialization R F₁ E₁) (e₂ f₂ : trivialization R F₂ E₂) :
  continuous_on ((prod e₁ e₂) ∘ (prod f₁ f₂).to_local_equiv.symm)
    ((prod f₁ f₂).target ∩ ((prod f₁ f₂).to_local_equiv.symm) ⁻¹' (prod e₁ e₂).source) :=
begin
  refine continuous_on.prod' _ _,
  { apply continuous_fst.continuous_on.congr,
    rintros p ⟨hp₁, hp₂⟩,
    convert (prod e₁ e₂).to_fiber_bundle_pretrivialization.coe_fst hp₂,
    rw (prod f₁ f₂).to_fiber_bundle_pretrivialization.proj_symm_apply hp₁ },
  rw [topological_fiber_bundle.pretrivialization.target_inter_preimage_symm_source_eq,
    pretrivialization.base_set_prod, pretrivialization.base_set_prod],
  let ψ₁ := f₁.to_local_homeomorph.symm.trans e₁.to_local_homeomorph,
  let ψ₂ := f₂.to_local_homeomorph.symm.trans e₂.to_local_homeomorph,
  have hψ₁ : ψ₁.source = (e₁.base_set ∩ f₁.base_set) ×ˢ (univ : set F₁) :=
    e₁.to_pretrivialization.to_fiber_bundle_pretrivialization.trans_source f₁,
  have hψ₂ : ψ₂.source = (e₂.base_set ∩ f₂.base_set) ×ˢ (univ : set F₂) :=
    e₂.to_pretrivialization.to_fiber_bundle_pretrivialization.trans_source f₂,
  refine continuous_on.prod' _ _,
  { refine ((continuous_snd.comp_continuous_on ψ₁.continuous_on).comp
      (continuous_id.prod_map continuous_fst).continuous_on _).congr _,
    { rw hψ₁,
      mfld_set_tac },
    { rintros ⟨x, ⟨w₁, w₂⟩⟩ ⟨hx, -⟩,
      have hxe₁ : x ∈ e₁.base_set := hx.1.1,
      have hxe₂ : x ∈ e₂.base_set := hx.1.2,
      dsimp,
      rw [prod_symm_apply hx.2.1 hx.2.2, prod_apply hxe₁ hxe₂],
      dsimp,
      rw [f₁.symm_apply_eq_prod_continuous_linear_equiv_at_symm] } },
  { refine ((continuous_snd.comp_continuous_on ψ₂.continuous_on).comp
      (continuous_id.prod_map continuous_snd).continuous_on _).congr _,
    { rw hψ₂,
      mfld_set_tac },
    { rintros ⟨x, ⟨w₁, w₂⟩⟩ ⟨hx, -⟩,
      have hxe₁ : x ∈ e₁.base_set := hx.1.1,
      have hxe₂ : x ∈ e₂.base_set := hx.1.2,
      dsimp,
      rw [prod_symm_apply hx.2.1 hx.2.2, prod_apply hxe₁ hxe₂],
      dsimp,
      rw [f₂.symm_apply_eq_prod_continuous_linear_equiv_at_symm] } },
end

end pretrivialization

open pretrivialization

variables [topological_vector_bundle R F₁ E₁] [topological_vector_bundle R F₂ E₂]

/-- The direct sum of topological vector bundles is a `topological_vector_prebundle` (this is an
auxiliary construction for the `topological_vector_prebundle` instance, in which the
pretrivializations are collated but no topology on the total space is yet provided). -/
def _root_.vector_bundle_prod.topological_vector_prebundle :
  topological_vector_prebundle R (F₁ × F₂) (vector_bundle_prod R F₁ E₁ F₂ E₂) :=
{ pretrivialization_at := λ x,
    pretrivialization.prod (trivialization_at R F₁ E₁ x) (trivialization_at R F₂ E₂ x),
  mem_base_pretrivialization_at := λ x,
    ⟨mem_base_set_trivialization_at R F₁ E₁ x, mem_base_set_trivialization_at R F₂ E₂ x⟩,
  continuous_triv_change := λ p q, pretrivialization.continuous_triv_change_prod
    (trivialization_at R F₁ E₁ p)
    (trivialization_at R F₁ E₁ q)
    (trivialization_at R F₂ E₂ p)
    (trivialization_at R F₂ E₂ q),
  total_space_mk_inducing := λ b,
  begin
    let e₁ := trivialization_at R F₁ E₁ b,
    let e₂ := trivialization_at R F₂ E₂ b,
    have hb₁ : b ∈ e₁.base_set := mem_base_set_trivialization_at R F₁ E₁ b,
    have hb₂ : b ∈ e₂.base_set := mem_base_set_trivialization_at R F₂ E₂ b,
    have key : inducing (λ w : E₁ b × E₂ b,
      (b, e₁.continuous_linear_equiv_at b hb₁ w.1, e₂.continuous_linear_equiv_at b hb₂ w.2)),
    { refine (inducing_prod_mk b).comp _,
      exact ((e₁.continuous_linear_equiv_at b hb₁).to_homeomorph.inducing.prod_mk
        (e₂.continuous_linear_equiv_at b hb₂).to_homeomorph.inducing) },
    { convert key,
      ext1 w,
      simpa using prod_apply hb₁ hb₂ w.1 w.2 },
  end }

/-- The natural topology on the total space of the product of two vector bundles. -/
instance : topological_space (total_space (vector_bundle_prod R F₁ E₁ F₂ E₂)) :=
(vector_bundle_prod.topological_vector_prebundle R F₁ E₁ F₂ E₂).total_space_topology

/-- The product of two vector bundles is a vector bundle. -/
instance : topological_vector_bundle R (F₁ × F₂) (vector_bundle_prod R F₁ E₁ F₂ E₂) :=
(vector_bundle_prod.topological_vector_prebundle R F₁ E₁ F₂ E₂).to_topological_vector_bundle

variables {R F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
trivialization for the direct sum of `E₁` and `E₂`, whose base set is `e₁.base_set ∩ e₂.base_set`.
-/
def trivialization.prod (e₁ : trivialization R F₁ E₁) (e₂ : trivialization R F₂ E₂) :
  trivialization R (F₁ × F₂) (vector_bundle_prod R F₁ E₁ F₂ E₂) :=
{ open_source := (open_base_set_prod e₁ e₂).preimage
    (topological_vector_bundle.continuous_proj R B (F₁ × F₂)),
  continuous_to_fun :=
  begin
    apply topological_fiber_prebundle.continuous_on_of_comp_right,
    { exact e₁.open_base_set.inter e₂.open_base_set },
    intros b,
    convert continuous_triv_change_prod e₁ (trivialization_at R F₁ E₁ b) e₂
      (trivialization_at R F₂ E₂ b),
    rw topological_fiber_bundle.pretrivialization.target_inter_preimage_symm_source_eq,
    refl,
  end,
  continuous_inv_fun := λ x hx, continuous_at.continuous_within_at
  begin
    let f₁ := trivialization_at R F₁ E₁ x.1,
    let f₂ := trivialization_at R F₂ E₂ x.1,
    have H :
      (prod e₁ e₂).target ∩ (prod e₁ e₂).to_local_equiv.symm ⁻¹' (prod f₁ f₂).source ∈ nhds x,
    { rw topological_fiber_bundle.pretrivialization.target_inter_preimage_symm_source_eq,
      refine is_open.mem_nhds _ ⟨⟨_, hx.1⟩, mem_univ _⟩,
      { exact ((open_base_set_prod f₁ f₂).inter (open_base_set_prod e₁ e₂)).prod is_open_univ },
      { exact ⟨mem_base_set_trivialization_at R F₁ E₁ x.1,
          mem_base_set_trivialization_at R F₂ E₂ x.1⟩ } },
    let a := (vector_bundle_prod.topological_vector_prebundle
      R F₁ E₁ F₂ E₂).to_topological_fiber_prebundle,
    rw (a.trivialization_at x.1).to_local_homeomorph.continuous_at_iff_continuous_at_comp_left,
    { exact (continuous_triv_change_prod f₁ e₁ f₂ e₂).continuous_at H },
    { exact filter.mem_of_superset H (inter_subset_right _ _) },
  end,
  .. pretrivialization.prod e₁ e₂ }

@[simp] lemma trivialization.base_set_prod (e₁ : trivialization R F₁ E₁)
  (e₂ : trivialization R F₂ E₂) :
  (e₁.prod e₂).base_set = e₁.base_set ∩ e₂.base_set :=
rfl

@[simp] lemma trivialization.continuous_linear_equiv_at_prod {e₁ : trivialization R F₁ E₁}
  {e₂ : trivialization R F₂ E₂} {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set) :
  (e₁.prod e₂).continuous_linear_equiv_at x ⟨hx₁, hx₂⟩
  = (e₁.continuous_linear_equiv_at x hx₁).prod (e₂.continuous_linear_equiv_at x hx₂) :=
begin
  ext1,
  funext v,
  obtain ⟨v₁, v₂⟩ := v,
  rw [(e₁.prod e₂).continuous_linear_equiv_at_apply, trivialization.prod],
  exact congr_arg prod.snd (prod_apply hx₁ hx₂ v₁ v₂),
end

end topological_vector_bundle
