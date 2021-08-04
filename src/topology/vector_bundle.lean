/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sebastien Gouezel
-/

import topology.fiber_bundle
import topology.algebra.module
import topology.continuous_function.basic

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
perform operations on topological vector bundles (which are yet to be formalized). For instance,
assume that `E₁ : B → Type*` and `E₂ : B → Type*` define two topological vector bundles over `R`
with fiber models `F₁` and `F₂` which are normed spaces. Then one can construct the vector bundle of
continuous linear maps from `E₁ x` to `E₂ x` with fiber `E x := (E₁ x →L[R] E₂ x)` (and with the
topology inherited from the norm-topology on `F₁ →L[R] F₂`, without the need to define the strong
topology on continuous linear maps between general topological vector spaces). Let
`vector_bundle_continuous_linear_map R F₁ E₁ F₂ E₂ (x : B)` be a type synonym for `E₁ x →L[R] E₂ x`.
Then one can endow
`bundle.total_space (vector_bundle_continuous_linear_map R F₁ E₁ F₂ E₂)`
with a topology and a topological vector bundle structure.

Similar constructions can be done for tensor products of topological vector bundles, exterior
algebras, and so on, where the topology can be defined using a norm on the fiber model if this
helps.

## Tags
Vector bundle
-/

noncomputable theory

open bundle set classical

local attribute [instance] prop_decidable

variables (R : Type*) {B : Type*} (F : Type*) (E : B → Type*)
[semiring R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
[topological_space F] [add_comm_monoid F] [module R F] [topological_space B]

section

/-- Local pretrivialization for vector prebundles. -/
@[nolint has_inhabited_instance]
structure topological_vector_bundle.pretrivialization extends to_fiber_bundle_pretrivialization :
  topological_fiber_bundle.pretrivialization F (proj E) :=
(linear' : ∀ x ∈ base_set, is_linear_map R (λ y : (E x), (to_fun y).2))

instance : has_coe_to_fun (topological_vector_bundle.pretrivialization R F E) := ⟨_, λ e, e.to_fun⟩

instance : has_coe (topological_vector_bundle.pretrivialization R F E)
  (topological_fiber_bundle.pretrivialization F (proj E)) :=
⟨topological_vector_bundle.pretrivialization.to_fiber_bundle_pretrivialization⟩

namespace topological_vector_bundle.pretrivialization

open topological_vector_bundle

variables {R F E} (e : pretrivialization R F E) {x : total_space E} {b : B} {y : E b}

lemma linear : ∀ x ∈ e.base_set, is_linear_map R (λ y : (E x), (e y).2) := e.linear'

@[simp, mfld_simps] lemma coe_coe : ⇑e.to_local_equiv = e := rfl
@[simp, mfld_simps] lemma coe_fst (ex : x ∈ e.source) : (e x).1 = proj E x := e.proj_to_fun x ex
lemma mem_source : x ∈ e.source ↔ proj E x ∈ e.base_set := by rw [e.source_eq, mem_preimage]
lemma mem_source' : ↑y ∈ e.source ↔ b ∈ e.base_set := e.mem_source
lemma coe_fst' (ex : proj E x ∈ e.base_set) : (e x).1 = proj E x := e.coe_fst (e.mem_source.2 ex)
protected lemma eq_on : eq_on (prod.fst ∘ e) (proj E) e.source := λ x hx, e.coe_fst hx
lemma mk_proj_snd (ex : x ∈ e.source) : (proj E x, (e x).2) = e x :=
prod.ext (e.coe_fst ex).symm rfl

@[simp, mfld_simps] lemma coe_fst'' (hb : b ∈ e.base_set) : (e y).1 = b :=
e.coe_fst (e.mem_source.2 hb)

lemma mk_proj_snd' (ex : proj E x ∈ e.base_set) : (proj E x, (e x).2) = e x :=
prod.ext (e.coe_fst' ex).symm rfl

lemma mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.base_set :=
e.to_fiber_bundle_pretrivialization.mem_target

lemma proj_symm_apply {x : B × F} (hx : x ∈ e.target) : proj E (e.to_local_equiv.symm x) = x.1 :=
e.to_fiber_bundle_pretrivialization.proj_symm_apply hx

lemma proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) :
  proj E (e.to_local_equiv.symm (b, x)) = b :=
e.proj_symm_apply (e.mem_target.2 hx)

lemma apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.to_local_equiv.symm x) = x :=
e.to_local_equiv.right_inv hx

lemma symm_apply_apply {x : total_space E} (hx : x ∈ e.source) : e.to_local_equiv.symm (e x) = x :=
e.to_local_equiv.left_inv hx

lemma apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) :
  e (e.to_local_equiv.symm (b, x)) = (b, x) :=
e.apply_symm_apply (e.mem_target.2 hx)

@[simp, mfld_simps] lemma symm_apply_mk_proj (ex : x ∈ e.source) :
  e.to_local_equiv.symm (proj E x, (e x).2) = x :=
by rw [← e.coe_fst ex, prod.mk.eta, ← e.coe_coe, e.to_local_equiv.left_inv ex]

@[simp, mfld_simps] lemma preimage_symm_proj_base_set :
  (e.to_local_equiv.symm ⁻¹' (proj E ⁻¹' e.base_set)) ∩ e.target  = e.target :=
e.to_fiber_bundle_pretrivialization.preimage_symm_proj_base_set

@[simp, mfld_simps] lemma symm_coe_fst' {x : B} {y : F}
  (e : pretrivialization R F E) (h : x ∈ e.base_set) :
  ((e.to_local_equiv.symm) (x, y)).fst = x := e.proj_symm_apply' h

lemma fiber_eq (e : pretrivialization R F E) {x : B} {y : F} (h : x ∈ e.base_set) :
  E ((e.to_local_equiv.symm) (x, y)).fst = E x :=
congr_arg E (e.proj_symm_apply (e.mem_target.mpr h))

end topological_vector_bundle.pretrivialization

variable [topological_space (total_space E)]

/-- Local trivialization for vector bundles. -/
@[nolint has_inhabited_instance]
structure topological_vector_bundle.trivialization extends to_fiber_bundle_trivialization :
  topological_fiber_bundle.trivialization F (proj E) :=
(linear' : ∀ x ∈ base_set, is_linear_map R (λ y : (E x), (to_fun y).2))

open topological_vector_bundle

instance : has_coe_to_fun (trivialization R F E) := ⟨_, λ e, e.to_fun⟩

instance : has_coe (trivialization R F E) (topological_fiber_bundle.trivialization F (proj E)) :=
⟨topological_vector_bundle.trivialization.to_fiber_bundle_trivialization⟩

namespace topological_vector_bundle.trivialization

variables {R F E} (e : trivialization R F E) {x : total_space E} {b : B} {y : E b}

/-- Natural identification as a `pretrivialization`. -/
def to_pretrivialization : topological_vector_bundle.pretrivialization R F E := { ..e }

protected lemma linear : ∀ x ∈ e.base_set, is_linear_map R (λ y : (E x), (e y).2) := e.linear'

protected lemma continuous_on : continuous_on e e.source := e.continuous_to_fun

@[simp, mfld_simps] lemma coe_coe : ⇑e.to_local_equiv = e := rfl
@[simp, mfld_simps] lemma coe_fst (ex : x ∈ e.source) : (e x).1 = proj E x := e.proj_to_fun x ex
lemma mem_source : x ∈ e.source ↔ proj E x ∈ e.base_set := by rw [e.source_eq, mem_preimage]
lemma mem_source' : ↑y ∈ e.source ↔ b ∈ e.base_set := e.mem_source
lemma coe_fst' (ex : proj E x ∈ e.base_set) : (e x).1 = proj E x := e.coe_fst (e.mem_source.2 ex)
protected lemma eq_on : eq_on (prod.fst ∘ e) (proj E) e.source := λ x hx, e.coe_fst hx
lemma mk_proj_snd (ex : x ∈ e.source) : (proj E x, (e x).2) = e x :=
prod.ext (e.coe_fst ex).symm rfl
lemma mk_proj_snd' (ex : proj E x ∈ e.base_set) : (proj E x, (e x).2) = e x :=
prod.ext (e.coe_fst' ex).symm rfl

@[simp, mfld_simps] lemma coe_fst'' (hb : b ∈ e.base_set) : (e y).1 = b :=
e.coe_fst (e.mem_source.2 hb)

lemma source_inter_preimage_target_inter (s : set (B × F)) :
  e.source ∩ (e ⁻¹' (e.target ∩ s)) = e.source ∩ (e ⁻¹' s) :=
e.to_local_homeomorph.source_inter_preimage_target_inter s

lemma mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.base_set :=
e.to_pretrivialization.mem_target

lemma mem_target' {y : F} : (b, y) ∈ e.target ↔ b ∈ e.base_set :=
e.to_pretrivialization.mem_target

lemma map_target {x : B × F} (hx : x ∈ e.target) : e.to_local_homeomorph.symm x ∈ e.source :=
e.to_local_homeomorph.map_target hx

lemma proj_symm_apply {x : B × F} (hx : x ∈ e.target) :
  proj E (e.to_local_homeomorph.symm x) = x.1 :=
e.to_pretrivialization.proj_symm_apply hx

lemma proj_symm_apply' {b : B} {x : F}
  (hx : b ∈ e.base_set) : proj E (e.to_local_homeomorph.symm (b, x)) = b :=
e.to_pretrivialization.proj_symm_apply' hx

lemma apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.to_local_homeomorph.symm x) = x :=
e.to_local_homeomorph.right_inv hx

lemma apply_symm_apply'
  {b : B} {x : F} (hx : b ∈ e.base_set) : e (e.to_local_homeomorph.symm (b, x)) = (b, x) :=
e.to_pretrivialization.apply_symm_apply' hx

lemma symm_apply_apply {x : total_space E} (hx : x ∈ e.source) : e.to_local_equiv.symm (e x) = x :=
e.to_local_equiv.left_inv hx

@[simp, mfld_simps] lemma symm_coe_fst' {x : B} {y : F}
  (e : trivialization R F E) (h : x ∈ e.base_set) :
  ((e.to_local_equiv.symm) (x, y)).fst = x := e.proj_symm_apply' h

end topological_vector_bundle.trivialization

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
  inv_fun := λ z, cast (congr_arg E (e.proj_symm_apply' hb)) (e.to_local_homeomorph.symm (b, z)).2,
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
  map_add' := λ v w, (e.linear' _ hb).map_add v w,
  map_smul' := λ c v, (e.linear' _ hb).map_smul c v,
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
  map_target' := λ y h,  mem_univ ⟨y.fst, y.snd⟩,
  left_inv' := λ x h, sigma.eq rfl rfl,
  right_inv' := λ x h, prod.ext rfl rfl,
  open_source := is_open_univ,
  open_target := is_open_univ,
  continuous_to_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [prod.topological_space, induced_inf, induced_compose], exact le_refl _, },
  continuous_inv_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [bundle.total_space.topological_space, induced_inf, induced_compose],
    exact le_refl _, },
  base_set := univ,
  open_base_set := is_open_univ,
  source_eq := rfl,
  target_eq := by simp only [univ_prod_univ],
  proj_to_fun := λ y hy, rfl,
  linear' := λ x hx, ⟨λ y z, rfl, λ c y, rfl⟩ }

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

include R F

lemma continuous_total_space_mk (x : B) : continuous (total_space_mk E x) :=
(topological_vector_bundle.total_space_mk_inducing R F E x).continuous

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
                                               (set.prod ((base_set i) ∩ (base_set j)) univ))
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
{ linear' := λ x hx,
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
        (Z.local_triv_at b).base_set.prod s, (continuous_on_open_iff
        (Z.local_triv_at b).open_source).mp (Z.local_triv_at b).continuous_to_fun _
        (is_open.prod (Z.local_triv_at b).open_base_set h), _⟩,
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
  `topologial_vector_bundle.trivialization`. -/
def trivialization_at (a : topological_vector_prebundle R F E) (x : B) :
  @topological_vector_bundle.trivialization R _ F E _ _ _ _ _ _ _ a.total_space_topology  :=
begin
  letI := a.total_space_topology,
  exact { linear' := (a.pretrivialization_at x).linear',
  ..a.to_topological_fiber_prebundle.trivialization_at x }
end

variable (a : topological_vector_prebundle R F E)

lemma mem_trivialization_at_source (b : B) (x : E b) :
  total_space_mk E b x ∈ (a.pretrivialization_at b).source :=
begin
  simp only [(a.pretrivialization_at b).source_eq, mem_preimage, proj],
  exact a.mem_base_pretrivialization_at b,
end

lemma total_space_mk_preimage_soure (b : B) :
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
    (univ_subset_iff.mpr (a.total_space_mk_preimage_soure b)),
  exact continuous_iff_le_induced.mpr (le_antisymm_iff.mp (a.total_space_mk_inducing b).induced).1,
end

lemma inducing_total_space_mk_of_inducing_comp (b : B)
  (h : inducing ((a.trivialization_at b) ∘ (total_space_mk E b))) :
  @inducing _ _ _ a.total_space_topology (total_space_mk E b) :=
begin
  letI := a.total_space_topology,
  rw restrict_comp_cod_restrict (a.mem_trivialization_at_source b) at h,
  apply inducing_of_inducing_cod_restrict (a.mem_trivialization_at_source b),
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

section pullback

/-! ### Pullback of topological vector bundles -/

open topological_space topological_vector_bundle

variables {R F} (E) {B' : Type*} [topological_space B'] [topological_space (total_space E)]

/-- Natural embedding of the total space of `E ∘ f` into `B' × (total_space E)`. -/
def pullback_total_space_embedding (f : B' → B) :
  total_space (E ∘ f) → B' × (total_space E) :=
λ z, (z.1, total_space_mk E (f z.1) z.2)

variable {E}

@[priority 90]
instance pullback.total_space.topological_space {f : B' → B} :
  topological_space (total_space (E ∘ f)) :=
induced (pullback_total_space_embedding E f) prod.topological_space

lemma inducing_pullback_total_space_embedding {f : B' → B} :
  inducing (pullback_total_space_embedding E f) := ⟨rfl⟩

lemma continuous_pullback_total_space_embedding {f : B' → B} :
  continuous (pullback_total_space_embedding E f) :=
inducing_pullback_total_space_embedding.continuous

variables (R F)

lemma pullback.continuous_total_space_mk {f : B' → B} {x : B'}
  [∀ x, topological_space (E x)] [topological_vector_bundle R F E] :
  continuous (total_space_mk (λ y, E (f y)) x) :=
begin
  simp only [continuous_iff_le_induced, pullback.total_space.topological_space, induced_compose,
    pullback_total_space_embedding, prod.topological_space, le_inf_iff, induced_inf, function.comp],
  have h := (topological_vector_bundle.total_space_mk_inducing R F E (f x)).induced,
  simp only at h,
  exact ⟨by {rw induced_const, exact le_top}, by {rw h, exact le_of_eq rfl}⟩,
end

variables {R F}

lemma pullback.continuous_proj {f : B' → B} :
  continuous (bundle.proj (E ∘ f)) :=
begin
  rw [continuous_iff_le_induced, pullback.total_space.topological_space,
    pullback_total_space_embedding, prod.topological_space, induced_inf, induced_compose],
  exact inf_le_left,
end

variable (E)

/-- The base map `f : B' → B` lifts to a canonical map on the total spaces. -/
@[reducible, simp] def pullback.lift (f : B' → B) :=
λ (z : total_space (λ (y : B'), E (f y))), total_space_mk E (f z.fst) z.snd

variable {E}

lemma pullback.continuous_lift {f : B' → B} :
  continuous (pullback.lift E f) :=
begin
  rw [continuous_iff_le_induced, pullback.total_space.topological_space,
    pullback_total_space_embedding, prod.topological_space, induced_inf],
  simp only [induced_compose, inf_le_right],
end

variables [∀ x, inhabited (E x)]

/-- A vector bundle trivialization can be pulled back to a trivialization on the pullback bundle. -/
def topological_vector_bundle.trivialization.pullback (e : trivialization R F E) (f : C(B', B)) :
  trivialization R F (λ y, E (f y)) := --WEEIIRD... composition?
{ to_fun := λ z, (z.1, (e (total_space_mk E (f z.1) z.2)).2),
  inv_fun := λ y,
    if hB : nonempty B' then
      if h : f y.1 ∈ e.base_set then
        total_space_mk _ y.1 (cast (congr_arg E (e.symm_coe_fst' h))
        (e.to_local_equiv.symm (f y.1, y.2)).2) -- change to local homeomorph
      else by { letI := hB, inhabit B', exact default _, }
    else false.elim (by { rw [not_nonempty_iff, is_empty_iff] at hB, exact hB y.1, }),
  source := (λ z, (z.1, (total_space_mk E (f z.1) z.2)).2) ⁻¹' e.source,
  base_set := f ⁻¹' e.base_set,
  target := (f ⁻¹' e.base_set).prod univ,
  map_source' := λ x h, begin
    simp only [prod_mk_mem_set_prod_eq, and_true, mem_univ, mem_preimage],
    simp only [mem_preimage, e.source_eq, proj] at h,
    exact h,
  end,
  map_target' := λ y h, begin
    simp only [and_true, mem_univ, mem_prod, mem_preimage] at h,
    simp only [mem_preimage, e.source_eq, proj, dif_pos h],
    by_cases h1 : nonempty B',
    { rw [dif_pos h1], exact h, },
    { exact false.elim (not_nonempty_iff_imp_false.mp h1 y.1), }
  end,
  left_inv' := λ x h, begin
    have hh := h,
    simp only [mem_preimage, e.source_eq, proj] at hh,
    simp only [total_space_mk, mem_preimage] at h,
    simp only [dif_pos hh, total_space_mk, not_nonempty_iff, proj, trivialization.symm_coe_fst'],
    by_cases h1 : nonempty B',
    { rw dif_pos h1,
      ext,
      { refl },
      { apply (cast_heq _ _).trans,
        rw [e.mk_proj_snd h, e.symm_apply_apply h], }},
    { exact false.elim (not_nonempty_iff_imp_false.mp h1 x.1), }
  end,
  right_inv' := λ x h, begin
    simp only [and_true, mem_univ, mem_prod, mem_preimage] at h,
    simp only [total_space_mk, dif_pos h, not_nonempty_iff, proj, trivialization.symm_coe_fst'],
    by_cases h1 : nonempty B',
    { simp only [dif_pos h1],
      ext,
      { refl },
      { dsimp only [total_space_mk],
        rw [dif_pos h1, dif_pos h],
        have : x.snd = (f x.fst, x.snd).snd := rfl,
        rw this,
        congr,
        have h2 : total_space_mk _ _ _ ∈ _ := e.mem_source'.mpr h,
        have hh := (e.to_local_equiv.eq_symm_apply h2 (e.mem_target'.mpr h : (_, x.snd) ∈ _)).symm,
        simp only [trivialization.coe_coe] at hh,
        rw hh,
        ext,
        { dsimp only [proj],
          rw e.symm_coe_fst' h, },
        { apply (cast_heq _ _).trans,
          refl, }}},
    { exact false.elim (not_nonempty_iff_imp_false.mp h1 x.1), }
  end,
  open_source := begin
    dsimp only [proj],
    rw [e.source_eq, ←preimage_comp],
    exact (f.continuous.comp pullback.continuous_proj).is_open_preimage _ e.open_base_set,
  end,
  open_target := (f.continuous.is_open_preimage _ e.open_base_set).prod is_open_univ,
  open_base_set := f.continuous.is_open_preimage _ e.open_base_set,
  continuous_to_fun := pullback.continuous_proj.continuous_on.prod (continuous_on_snd.comp
    (e.continuous_on.comp (continuous.continuous_on pullback.continuous_lift) rfl.subset)
    subset_preimage_univ),
  continuous_inv_fun := begin
    by_cases h1 : nonempty B',
    { simp only [dif_pos h1],
      dsimp only [trivialization.coe_coe, prod_mk_mem_set_prod_eq, and_true, mem_univ,
        mem_prod, mem_preimage, proj, trivialization.symm_coe_fst', cast_heq],
      have h := e.continuous_inv_fun,
      rw e.target_eq at h,
      rw continuous_on_iff at ⊢ h,
      intros x h2 s hs h3,
      simp only [and_true, mem_univ, mem_prod, mem_preimage] at h2,
      simp only [total_space_mk, dif_pos h2, trivialization.symm_coe_fst'] at h3,
      simp only [prod_mk_mem_set_prod_eq, and_true, local_homeomorph.inv_fun_eq_coe, mem_univ,
        prod.forall] at h,
      rw is_open_induced_iff at hs,
      obtain ⟨t, ht, rfl⟩ := hs,
      rw is_open_prod_iff at ht,
      simp only [mem_preimage, pullback_total_space_embedding, e.symm_coe_fst',
        total_space_mk_cast _ (e.symm_coe_fst' h2)] at h3,
      obtain ⟨a, b, ha1, hb1, ha2, hb2, hab⟩:= ht x.1 (e.to_local_equiv.symm (f x.1, x.2)) h3,
      obtain ⟨u, hu1, hu2, hu3⟩ := h (f x.fst) x.snd h2 (b ∩ e.source) (hb1.inter e.open_source)
        ⟨hb2, e.map_target (e.mem_target'.mpr h2)⟩,
      rw is_open_prod_iff at hu1,
      obtain ⟨c, d , hc1, hd1, hc2, hd2, hcd⟩ := hu1 (f x.1) x.2 hu2,
      refine ⟨(f ⁻¹' (c ∩ e.base_set) ∩ a).prod d, _, _, _⟩,
      { exact ((continuous.is_open_preimage f.continuous _
          (hc1.inter e.open_base_set)).inter ha1).prod hd1, },
      { exact ⟨⟨⟨hc2, h2⟩, ha2⟩, hd2⟩, },
      { rw subset_def,
        intros z hz,
        simp only [mem_inter_eq, and_true, mem_univ, mem_prod, mem_preimage] at hz,
        obtain ⟨⟨⟨⟨hz1, hz2⟩, hz3⟩, hz4⟩, hz5⟩ := hz,
        simp only [mem_preimage, trivialization.symm_coe_fst', pullback_total_space_embedding],
        rw [dif_pos hz5],
        refine mem_of_subset_of_mem hab ⟨hz3, _⟩,
        rw total_space_mk_cast _ (e.symm_coe_fst' hz2),
        apply @mem_of_mem_inter_left _ _ _ e.source,
        rw ←image_subset_iff at hu3,
        refine mem_of_subset_of_mem hu3 _,
        simp only [mem_image, local_homeomorph.coe_coe_symm, mem_inter_eq, and_true, mem_univ,
          mem_prod, prod.exists],
        exact ⟨f z.1, z.2, ⟨mem_of_subset_of_mem hcd ⟨hz1, hz4⟩, hz2⟩, rfl⟩, }},
    { rw not_nonempty_iff at h1,
      letI := h1,
      dsimp only [total_space],
      exact (continuous_empty_function _).continuous_on, }
  end,
  source_eq := by { dsimp only [total_space_mk, proj], rw e.source_eq, refl, },
  target_eq := rfl,
  proj_to_fun := λ y h, rfl,
  linear' := λ x h, e.linear' (f x) h }

@[priority 90]
instance pullback [∀ x, topological_space (E x)] [topological_vector_bundle R F E] {f : C(B', B)} :
  topological_vector_bundle R F (λ x : B', E (f x)) :=
{ total_space_mk_inducing := λ x, inducing_of_inducing_compose
    (pullback.continuous_total_space_mk R F) pullback.continuous_lift
    (topological_vector_bundle.total_space_mk_inducing R F E (f x)),
  locally_trivial := λ x, ⟨(topological_vector_bundle.trivialization_at R F E (f x)).pullback f,
    (topological_vector_bundle.mem_base_set_trivialization_at R F E (f x))⟩ }

end pullback
