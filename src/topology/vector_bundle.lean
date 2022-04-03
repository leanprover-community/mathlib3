/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sebastien Gouezel, Heather Macbeth, Patrick Massot
-/

import analysis.normed_space.bounded_linear_maps
import topology.fiber_bundle

/-!
# Topological vector bundles

In this file we define topological vector bundles.

Let `B` be the base space. In our formalism, a topological vector bundle is by definition the type
`bundle.total_space E` where `E : B → Type*` is a function associating to
`x : B` the fiber over `x`. This type `bundle.total_space E` is just a type synonym for
`Σ (x : B), E x`, with the interest that one can put another topology than on `Σ (x : B), E x`
which has the disjoint union topology.

To have a topological vector bundle structure on `bundle.total_space E`, one should
additionally have the following data:

* `F` should be a normed space over a normed field `R`;
* There should be a topology on `bundle.total_space E`, for which the projection to `B` is
a topological fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological vector space over `R`, and the injection
from `E x` to `bundle.total_space F E` should be an embedding;
* There should be a distinguished set of bundle trivializations (which are continuous linear equivs
in the fibres), the "trivialization atlas"
* There should be a choice of bundle trivialization at each point, which belongs to this atlas.

If all these conditions are satisfied, and if moreover for any two trivializations `e`, `e'` in the
atlas the transition function considered as a map from `B` into `F →L[R] F` is continuous on
`e.base_set ∩ e'.base_set` with respect to the operator norm topology on `F →L[R] F`, we register
the typeclass `topological_vector_bundle R F E`.

If `E₁ : B → Type*` and `E₂ : B → Type*` define two topological vector bundles over `R` with fiber
models `F₁` and `F₂`, denote by `E₁ ×ᵇ E₂` the sigma type of direct sums, with fiber
`E x := (E₁ x × E₂ x)`. We can endow `bundle.total_space (E₁ ×ᵇ E₂)` with a topological vector
bundle structure, `bundle.prod.topological_vector_bundle`.

A similar construction (which is yet to be formalized) can be done for the vector bundle of
continuous linear maps from `E₁ x` to `E₂ x` with fiber a type synonym
`vector_bundle_continuous_linear_map R F₁ E₁ F₂ E₂ x := (E₁ x →L[R] E₂ x)` (and with the
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

section topological_vector_space
variables [semiring R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
  [topological_space F] [add_comm_monoid F] [module R F] [topological_space B]

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

end topological_vector_space

section
open topological_vector_bundle

variables (B)
variables [nondiscrete_normed_field R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
  [normed_group F] [normed_space R F] [topological_space B]
  [topological_space (total_space E)] [∀ x, topological_space (E x)]

/-- The valid transition functions for a topological vector bundle over `B` modelled on
a normed space `F`: a transition function must be a local homeomorphism of `B × F` with source and
target both `s ×ˢ univ`, which on this set is of the form `λ (b, v), (b, ε b v)` for some continuous
map `ε` from `s` to `F ≃L[𝕜] F`.  Here continuity is with respect to the operator norm on
`F ≃L[𝕜] F`. -/
def continuous_transitions (e : local_equiv (B × F) (B × F)) : Prop :=
∃ s : set B, e.source = s ×ˢ (univ : set F) ∧ e.target = s ×ˢ (univ : set F)
    ∧ ∃ ε : B → (F ≃L[R] F), continuous_on (λ b, (ε b : F →L[R] F)) s
      ∧ ∀ b ∈ s, ∀ v : F, e (b, v) = (b, ε b v)

variables {B}

/-- The space `total_space E` (for `E : B → Type*` such that each `E x` is a topological vector
space) has a topological vector space structure with fiber `F` (denoted with
`topological_vector_bundle R F E`) if around every point there is a fiber bundle trivialization
which is linear in the fibers. -/
class topological_vector_bundle :=
(total_space_mk_inducing [] : ∀ (b : B), inducing (total_space_mk E b))
(trivialization_atlas [] : set (trivialization R F E))
(trivialization_at [] : B → trivialization R F E)
(mem_base_set_trivialization_at [] : ∀ b : B, b ∈ (trivialization_at b).base_set)
(trivialization_mem_atlas [] : ∀ b : B, trivialization_at b ∈ trivialization_atlas)
(continuous_coord_change : ∀ e e' ∈ trivialization_atlas,
  continuous_transitions R B F (by exact e.to_local_equiv.symm.trans e'.to_local_equiv))
-- what is the `by exact` doing here???

export topological_vector_bundle (trivialization_atlas trivialization_at
  mem_base_set_trivialization_at trivialization_mem_atlas)

variable [topological_vector_bundle R F E]

namespace topological_vector_bundle

@[simp, mfld_simps] lemma mem_source_trivialization_at (z : total_space E) :
  z ∈ (trivialization_at R F E z.1).source :=
by { rw topological_fiber_bundle.trivialization.mem_source, apply mem_base_set_trivialization_at }

variables {R F E}

/-- The co-ordinate change (transition function) between two trivializations of a vector bundle
over `B` modelled on `F`: this is a function from `B` to `F ≃L[R] F` (of course, only meaningful
on the intersection of the domains of definition of the two trivializations). -/
def coord_change {e e' : trivialization R F E} (he : e ∈ trivialization_atlas R F E)
  (he' : e' ∈ trivialization_atlas R F E) :
  B → F ≃L[R] F :=
(topological_vector_bundle.continuous_coord_change e he e' he').some_spec.2.2.some

lemma continuous_on_coord_change {e e' : trivialization R F E} (he : e ∈ trivialization_atlas R F E)
  (he' : e' ∈ trivialization_atlas R F E) :
  continuous_on (λ b, (coord_change he he' b : F →L[R] F)) (e.base_set ∩ e'.base_set) :=
begin
  let s := (continuous_coord_change e he e' he').some,
  let hs := (continuous_coord_change e he e' he').some_spec.1,
  have hs : s = e.base_set ∩ e'.base_set,
  { have : s ×ˢ (univ : set F) = (e.base_set ∩ e'.base_set) ×ˢ (univ : set F) :=
      hs.symm.trans (topological_fiber_bundle.trivialization.symm_trans_source_eq e e'),
    have hF : (univ : set F).nonempty := univ_nonempty,
      rwa prod_eq_iff_eq hF at this },
  rw ← hs,
  exact (continuous_coord_change e he e' he').some_spec.2.2.some_spec.1
end

lemma trans_eq_coord_change {e e' : trivialization R F E} (he : e ∈ trivialization_atlas R F E)
  (he' : e' ∈ trivialization_atlas R F E) {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) (v : F) :
  e' (e.to_local_homeomorph.symm (b, v)) = (b, coord_change he he' b v) :=
begin
  let s := (continuous_coord_change e he e' he').some,
  let hs := (continuous_coord_change e he e' he').some_spec.1,
  have hs : s = e.base_set ∩ e'.base_set,
  { have : s ×ˢ (univ : set F) = (e.base_set ∩ e'.base_set) ×ˢ (univ : set F) :=
      hs.symm.trans (topological_fiber_bundle.trivialization.symm_trans_source_eq e e'),
    have hF : (univ : set F).nonempty := univ_nonempty,
      rwa prod_eq_iff_eq hF at this },
  rw ← hs at hb,
  exact (continuous_coord_change e he e' he').some_spec.2.2.some_spec.2 b hb v
end

attribute [irreducible] coord_change

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
  e.to_local_homeomorph ⟨b, z⟩ = (b, e.continuous_linear_equiv_at b hb z) :=
begin
  ext,
  { convert e.coe_fst _,
    rw e.source_eq,
    exact hb },
  { simp }
end

lemma symm_apply_eq_mk_continuous_linear_equiv_at_symm (e : trivialization R F E) (b : B)
  (hb : b ∈ e.base_set) (z : F) :
  e.to_local_homeomorph.symm ⟨b, z⟩
  = total_space_mk E b ((e.continuous_linear_equiv_at b hb).symm z) :=
begin
  have h : (b, z) ∈ e.to_local_homeomorph.target,
  { rw e.target_eq,
    exact ⟨hb, mem_univ _⟩ },
  apply e.to_local_homeomorph.inj_on (e.to_local_homeomorph.map_target h),
  { simp [e.source_eq, hb] },
  simp [-continuous_linear_equiv_at_apply, e.apply_eq_prod_continuous_linear_equiv_at b hb,
    e.to_local_homeomorph.right_inv h],
end

lemma comp_continuous_linear_equiv_at_eq_coord_change {e e' : trivialization R F E}
  (he : e ∈ trivialization_atlas R F E) (he' : e' ∈ trivialization_atlas R F E) {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) :
  (e.continuous_linear_equiv_at b hb.1).symm.trans (e'.continuous_linear_equiv_at b hb.2)
  = coord_change he he' b :=
begin
  ext v,
  suffices :
    (b, e'.continuous_linear_equiv_at b hb.2 ((e.continuous_linear_equiv_at b hb.1).symm v))
    = (b, coord_change he he' b v),
  { simpa using this },
  rw [← trans_eq_coord_change he he' hb, ← apply_eq_prod_continuous_linear_equiv_at,
    symm_apply_eq_mk_continuous_linear_equiv_at_symm],
  refl,
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

@[simp]
lemma trivial_topological_vector_bundle.trivialization_source :
  (trivial_topological_vector_bundle.trivialization R B F).source = univ := rfl

@[simp]
lemma trivial_topological_vector_bundle.trivialization_target :
  (trivial_topological_vector_bundle.trivialization R B F).target = univ := rfl

instance trivial_bundle.topological_vector_bundle :
  topological_vector_bundle R F (bundle.trivial B F) :=
{ trivialization_atlas := {trivial_topological_vector_bundle.trivialization R B F},
  trivialization_at := λ x, trivial_topological_vector_bundle.trivialization R B F,
  mem_base_set_trivialization_at := mem_univ,
  trivialization_mem_atlas := λ x, mem_singleton _,
  total_space_mk_inducing := λ b, ⟨begin
    have : (λ (x : trivial B F b), x) = @id F, by { ext x, refl },
    simp only [total_space.topological_space, induced_inf, induced_compose, function.comp, proj,
      induced_const, top_inf_eq, trivial.proj_snd, id.def, trivial.topological_space, this,
      induced_id],
  end⟩,
  continuous_coord_change := begin
    intros e he e' he',
    rw [mem_singleton_iff.mp he, mem_singleton_iff.mp he'],
    exact ⟨univ, by simp, by simp, λb, continuous_linear_equiv.refl R F,
           continuous_const.continuous_on, λ b hb v, rfl⟩
  end }

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

end topological_vector_bundle

/-! ### Constructing topological vector bundles -/

variables (B)

/-- Analogous construction of `topological_fiber_bundle_core` for vector bundles. This
construction gives a way to construct vector bundles from a structure registering how
trivialization changes act on fibers. -/
structure topological_vector_bundle_core (ι : Type*) :=
(base_set          : ι → set B)
(is_open_base_set  : ∀ i, is_open (base_set i))
(index_at          : B → ι)
(mem_base_set_at   : ∀ x, x ∈ base_set (index_at x))
(coord_change      : ι → ι → B → (F →L[R] F))
(coord_change_self : ∀ i, ∀ x ∈ base_set i, ∀ v, coord_change i i x v = v)
(coord_change_continuous : ∀ i j, continuous_on (coord_change i j) (base_set i ∩ base_set j))
(coord_change_comp : ∀ i j k, ∀ x ∈ (base_set i) ∩ (base_set j) ∩ (base_set k), ∀ v,
  (coord_change j k x) (coord_change i j x v) = coord_change i k x v)

/-- The trivial topological vector bundle core, in which all the changes of coordinates are the
identity. -/
def trivial_topological_vector_bundle_core (ι : Type*) [inhabited ι] :
  topological_vector_bundle_core R B F ι :=
{ base_set := λ ι, univ,
  is_open_base_set := λ i, is_open_univ,
  index_at := λ x, default,
  mem_base_set_at := λ x, mem_univ x,
  coord_change := λ i j x, continuous_linear_map.id R F,
  coord_change_self := λ i x hx v, rfl,
  coord_change_comp := λ i j k x hx v, rfl,
  coord_change_continuous := λ i j, continuous_on_const, }

instance (ι : Type*) [inhabited ι] : inhabited (topological_vector_bundle_core R B F ι) :=
⟨trivial_topological_vector_bundle_core R B F ι⟩

namespace topological_vector_bundle_core

variables {R B F} {ι : Type*} (Z : topological_vector_bundle_core R B F ι)

/-- Natural identification to a `topological_fiber_bundle_core`. -/
def to_topological_vector_bundle_core : topological_fiber_bundle_core ι B F :=
{ coord_change := λ i j b, Z.coord_change i j b,
  coord_change_continuous := λ i j, is_bounded_bilinear_map_apply.continuous.comp_continuous_on
      ((Z.coord_change_continuous i j).prod_map continuous_on_id),
  ..Z }

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

variable [add_comm_group F]

instance add_comm_group_fiber : ∀ (x : B), add_comm_group (Z.fiber x) := λ x, by apply_instance

end fiber_instances

/-- The projection from the total space of a topological fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps] def proj : total_space Z.fiber → B := bundle.proj Z.fiber

/-- The total space of the topological vector bundle, as a convenience function for dot notation.
It is by definition equal to `bundle.total_space Z.fiber`, a.k.a. `Σ x, Z.fiber x` but with a
different name for typeclass inference. -/
@[nolint unused_arguments, reducible]
def total_space := bundle.total_space Z.fiber

/-- Local homeomorphism version of the trivialization change. -/
def triv_change (i j : ι) : local_homeomorph (B × F) (B × F) :=
topological_fiber_bundle_core.triv_change ↑Z i j

@[simp, mfld_simps] lemma mem_triv_change_source (i j : ι) (p : B × F) :
  p ∈ (Z.triv_change i j).source ↔ p.1 ∈ Z.base_set i ∩ Z.base_set j :=
topological_fiber_bundle_core.mem_triv_change_source ↑Z i j p

variable (ι)

/-- Topological structure on the total space of a topological bundle created from core, designed so
that all the local trivialization are continuous. -/
instance to_topological_space : topological_space (Z.total_space) :=
topological_fiber_bundle_core.to_topological_space ι ↑Z

variables {ι} (b : B) (a : F)

@[simp, mfld_simps] lemma coe_coord_change (i j : ι) :
  topological_fiber_bundle_core.coord_change ↑Z i j b = Z.coord_change i j b := rfl

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def local_triv (i : ι) : topological_vector_bundle.trivialization R F Z.fiber :=
{ linear := λ x hx,
  { map_add := λ v w, by simp only [continuous_linear_map.map_add] with mfld_simps,
    map_smul := λ r v, by simp only [continuous_linear_map.map_smul] with mfld_simps},
  ..topological_fiber_bundle_core.local_triv ↑Z i }

variable (i : ι)

@[simp, mfld_simps] lemma mem_local_triv_source (p : Z.total_space) :
  p ∈ (Z.local_triv i).source ↔ p.1 ∈ Z.base_set i := iff.rfl

@[simp, mfld_simps] lemma base_set_at : Z.base_set i = (Z.local_triv i).base_set := rfl

@[simp, mfld_simps] lemma local_triv_apply (p : Z.total_space) :
  (Z.local_triv i) p = ⟨p.1, Z.coord_change (Z.index_at p.1) i p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma mem_local_triv_target (p : B × F) :
  p ∈ (Z.local_triv i).target ↔ p.1 ∈ (Z.local_triv i).base_set :=
topological_fiber_bundle_core.mem_local_triv_target Z i p

@[simp, mfld_simps] lemma local_triv_symm_fst (p : B × F) :
  (Z.local_triv i).to_local_homeomorph.symm p =
    ⟨p.1, Z.coord_change i (Z.index_at p.1) p.1 p.2⟩ := rfl

/-- Preferred local trivialization of a vector bundle constructed from core, at a given point, as
a bundle trivialization -/
def local_triv_at (b : B) : topological_vector_bundle.trivialization R F Z.fiber :=
Z.local_triv (Z.index_at b)

@[simp, mfld_simps] lemma local_triv_at_def :
  Z.local_triv (Z.index_at b) = Z.local_triv_at b := rfl

@[simp, mfld_simps] lemma mem_source_at : (⟨b, a⟩ : Z.total_space) ∈ (Z.local_triv_at b).source :=
by { rw [local_triv_at, mem_local_triv_source], exact Z.mem_base_set_at b }

@[simp, mfld_simps] lemma local_triv_at_apply : ((Z.local_triv_at b) ⟨b, a⟩) = ⟨b, a⟩ :=
topological_fiber_bundle_core.local_triv_at_apply Z b a

@[simp, mfld_simps] lemma mem_local_triv_at_base_set :
  b ∈ (Z.local_triv_at b).base_set :=
topological_fiber_bundle_core.mem_local_triv_at_base_set Z b

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
  trivialization_atlas := set.range Z.local_triv,
  trivialization_at := Z.local_triv_at,
  mem_base_set_trivialization_at := Z.mem_base_set_at,
  trivialization_mem_atlas := λ b, ⟨Z.index_at b, rfl⟩,
  continuous_coord_change := begin
    classical,
    rintros _ ⟨i, rfl⟩ _ ⟨i', rfl⟩,
    refine ⟨Z.base_set i ∩ Z.base_set i', _, _,
      λ b, if h : b ∈ Z.base_set i ∩ Z.base_set i' then continuous_linear_equiv.equiv_of_inverse
        (Z.coord_change i i' b) (Z.coord_change i' i b) _ _ else continuous_linear_equiv.refl R F,
      _, _⟩,
    { ext ⟨b, f⟩,
      simp },
    { ext ⟨b, f⟩,
      simp [and_comm] },
    { intro f,
      rw [Z.coord_change_comp _ _ _ _ ⟨h, h.1⟩, Z.coord_change_self _ _ h.1] },
    { intro f,
      rw [Z.coord_change_comp _ _ _ _ ⟨⟨h.2, h.1⟩, h.2⟩, Z.coord_change_self _ _ h.2] },
    { apply continuous_on.congr (Z.coord_change_continuous i i'),
      intros b hb,
      simp [hb],
      ext v,
      refl },
    { intros b hb v,
      have : b ∈ Z.base_set i ∩ Z.base_set (Z.index_at b) ∩ Z.base_set i',
      { simp only [base_set_at, local_triv_at_def, mem_inter_eq, mem_local_triv_at_base_set] at *,
        tauto },
      simp [hb, Z.coord_change_comp _ _ _ _ this] }
  end }

/-- The projection on the base of a topological vector bundle created from core is continuous -/
@[continuity] lemma continuous_proj : continuous Z.proj :=
topological_fiber_bundle_core.continuous_proj Z

/-- The projection on the base of a topological vector bundle created from core is an open map -/
lemma is_open_map_proj : is_open_map Z.proj :=
topological_fiber_bundle_core.is_open_map_proj Z

end topological_vector_bundle_core

end

/-! ### Topological vector prebundle -/

section
variables [nondiscrete_normed_field R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
  [normed_group F] [normed_space R F] [topological_space B]
  [∀ x, topological_space (E x)]

open topological_space

/-- This structure permits to define a vector bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space. The total space is hence given a
topology in such a way that there is a fiber bundle structure for which the local equivalences
are also local homeomorphisms and hence vector bundle trivializations. -/
@[nolint has_inhabited_instance]
structure topological_vector_prebundle :=
(pretrivialization_atlas : set (topological_vector_bundle.pretrivialization R F E))
(pretrivialization_at : B → topological_vector_bundle.pretrivialization R F E)
(mem_base_pretrivialization_at : ∀ x : B, x ∈ (pretrivialization_at x).base_set)
(pretrivialization_mem_atlas : ∀ x : B, pretrivialization_at x ∈ pretrivialization_atlas)
(continuous_coord_change : ∀ e e' ∈ pretrivialization_atlas,
  continuous_transitions R B F (e'.to_local_equiv.symm.trans e.to_local_equiv : _))
(total_space_mk_inducing : ∀ (b : B), inducing ((pretrivialization_at b) ∘ (total_space_mk E b)))

namespace topological_vector_prebundle

variables {R E F}

-- The next two lemmas are no longer necessary, but I think they should still go into mathlib

lemma set.inj_on.eq_iff {α β : Type*} (f : α → β) {a a' : α} {s : set α} (h : inj_on f s)
  (ha : a ∈ s) (ha' : a' ∈ s) : f a = f a' ↔ a = a' :=
⟨h ha ha', congr_arg f⟩

lemma local_equiv.eq_iff_symm_eq {α β : Type*} (e : local_equiv α β) {a : α} {b : β}
  (ha : a ∈ e.source) (hb : b ∈ e.target) : e a = b ↔ e.symm b = a :=
begin
  conv_lhs { rw [← local_equiv.right_inv e hb, eq_comm] },
  exact e.inj_on.eq_iff (e.map_target hb) ha
end

/-- Natural identification of `topological_vector_prebundle` as a `topological_fiber_prebundle`. -/
def to_topological_fiber_prebundle (a : topological_vector_prebundle R F E) :
  topological_fiber_prebundle F (proj E) :=
{ pretrivialization_atlas :=
    pretrivialization.to_fiber_bundle_pretrivialization '' a.pretrivialization_atlas,
  pretrivialization_at := λ x, (a.pretrivialization_at x).to_fiber_bundle_pretrivialization,
  pretrivialization_mem_atlas := λ x, ⟨_, a.pretrivialization_mem_atlas x, rfl⟩,
  continuous_triv_change := begin
    rintros _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩,
    obtain ⟨s, hs, hs', ε, hε, heε⟩ := a.continuous_coord_change e he e' he',
    have H : e'.to_fiber_bundle_pretrivialization.to_local_equiv.target ∩
      (e'.to_fiber_bundle_pretrivialization.to_local_equiv.symm) ⁻¹'
      e.to_fiber_bundle_pretrivialization.to_local_equiv.source = s ×ˢ (univ : set F),
    { simpa using hs },
    rw H,
    have : continuous_on (λ p : B × F, (p.1, (ε p.1) p.2)) (s ×ˢ (univ : set F)),
    { apply continuous_on_fst.prod,
      exact is_bounded_bilinear_map_apply.continuous.comp_continuous_on
        (hε.prod_map continuous_on_id) },
    apply this.congr,
    rintros ⟨b, f⟩ ⟨hb : b ∈ s, -⟩,
    exact heε _ hb _,
  end,
  .. a }

/-- Topology on the total space that will make the prebundle into a bundle. -/
def total_space_topology (a : topological_vector_prebundle R F E) :
  topological_space (total_space E) :=
a.to_topological_fiber_prebundle.total_space_topology

/-- Promotion from a `topologial_vector_prebundle.trivialization` to a
  `topological_vector_bundle.trivialization`. -/
def trivialization_of_mem_pretrivialization_atlas (a : topological_vector_prebundle R F E)
  {e : topological_vector_bundle.pretrivialization R F E} (he : e ∈ a.pretrivialization_atlas) :
  @topological_vector_bundle.trivialization R _ F E _ _ _ _ _ _ _ a.total_space_topology :=
begin
  letI := a.total_space_topology,
  exact { linear := e.linear,
  ..a.to_topological_fiber_prebundle.trivialization_of_mem_pretrivialization_atlas ⟨e, he, rfl⟩ }
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
  let e := a.trivialization_of_mem_pretrivialization_atlas (a.pretrivialization_mem_atlas b),
  rw e.to_local_homeomorph.continuous_iff_continuous_comp_left
    (a.total_space_mk_preimage_source b),
  exact continuous_iff_le_induced.mpr (le_antisymm_iff.mp (a.total_space_mk_inducing b).induced).1,
end

lemma inducing_total_space_mk_of_inducing_comp (b : B)
  (h : inducing ((a.pretrivialization_at b) ∘ (total_space_mk E b))) :
  @inducing _ _ _ a.total_space_topology (total_space_mk E b) :=
begin
  letI := a.total_space_topology,
  rw ←restrict_comp_cod_restrict (a.mem_trivialization_at_source b) at h,
  apply inducing.of_cod_restrict (a.mem_trivialization_at_source b),
  refine inducing_of_inducing_compose _ (continuous_on_iff_continuous_restrict.mp
    (a.trivialization_of_mem_pretrivialization_atlas
    (a.pretrivialization_mem_atlas b)).continuous_to_fun) h,
  exact (a.continuous_total_space_mk b).cod_restrict (a.mem_trivialization_at_source b),
end

/-- Make a `topological_vector_bundle` from a `topological_vector_prebundle`.  Concretely this means
that, given a `topological_vector_prebundle` structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`topological_vector_prebundle.total_space_topology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
def to_topological_vector_bundle :
  @topological_vector_bundle R _ F E _ _ _ _ _ _ a.total_space_topology _ :=
{ total_space_mk_inducing := λ b, a.inducing_total_space_mk_of_inducing_comp b
    (a.total_space_mk_inducing b),
  trivialization_atlas := {e | ∃ e₀ (he₀ : e₀ ∈ a.pretrivialization_atlas),
    e = a.trivialization_of_mem_pretrivialization_atlas he₀},
  trivialization_at := λ x, a.trivialization_of_mem_pretrivialization_atlas
    (a.pretrivialization_mem_atlas x),
  mem_base_set_trivialization_at := a.mem_base_pretrivialization_at,
  trivialization_mem_atlas := λ x, ⟨_, a.pretrivialization_mem_atlas x, rfl⟩,
  continuous_coord_change := begin
    rintros _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩,
    exact a.continuous_coord_change e' he' e he,
  end }

end topological_vector_prebundle

end

/-! ### Direct sum of two vector bundles over the same base -/

namespace topological_vector_bundle

section defs
variables (E₁ : B → Type*) (E₂ : B → Type*)
variables [topological_space (total_space E₁)] [topological_space (total_space E₂)]

/-- Equip the total space of the fibrewise product of two topological vector bundles `E₁`, `E₂` with
the induced topology from the diagonal embedding into `(total_space E₁) × (total_space E₂)`. -/
instance prod.topological_space :
  topological_space (total_space (E₁ ×ᵇ E₂)) :=
topological_space.induced
  (λ p, ((⟨p.1, p.2.1⟩ : total_space E₁), (⟨p.1, p.2.2⟩ : total_space E₂)))
  (by apply_instance : topological_space ((total_space E₁) × (total_space E₂)))

/-- The diagonal map from the total space of the fibrewise product of two topological vector bundles
`E₁`, `E₂` into `(total_space E₁) × (total_space E₂)` is `inducing`. -/
lemma prod.inducing_diag : inducing
  (λ p, (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩) :
    total_space (E₁ ×ᵇ E₂) → (total_space E₁) × (total_space E₂)) :=
⟨rfl⟩

end defs

variables [nondiscrete_normed_field R] [topological_space B]

variables (F₁ : Type*) [normed_group F₁] [normed_space R F₁]
  (E₁ : B → Type*) [topological_space (total_space E₁)]
  [Π x, add_comm_monoid (E₁ x)] [Π x, module R (E₁ x)]

variables (F₂ : Type*) [normed_group F₂] [normed_space R F₂]
  (E₂ : B → Type*) [topological_space (total_space E₂)]
  [Π x, add_comm_monoid (E₂ x)] [Π x, module R (E₂ x)]

namespace trivialization
variables (e₁ : trivialization R F₁ E₁) (e₂ : trivialization R F₂ E₂)
include e₁ e₂
variables {R F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the forward
function for the construction `topological_vector_bundle.trivialization.prod`, the induced
trivialization for the direct sum of `E₁` and `E₂`. -/
def prod.to_fun' : total_space (E₁ ×ᵇ E₂) → B × (F₁ × F₂) :=
λ ⟨x, v₁, v₂⟩, ⟨x, (e₁ ⟨x, v₁⟩).2, (e₂ ⟨x, v₂⟩).2⟩

variables {e₁ e₂}

lemma prod.continuous_to_fun :
  continuous_on (prod.to_fun' e₁ e₂) (proj (E₁ ×ᵇ E₂) ⁻¹' (e₁.base_set ∩ e₂.base_set)) :=
begin
  let f₁ : total_space (E₁ ×ᵇ E₂) → total_space E₁ × total_space E₂ :=
    λ p, ((⟨p.1, p.2.1⟩ : total_space E₁), (⟨p.1, p.2.2⟩ : total_space E₂)),
  let f₂ : total_space E₁ × total_space E₂ → (B × F₁) × (B × F₂) := λ p, ⟨e₁ p.1, e₂ p.2⟩,
  let f₃ : (B × F₁) × (B × F₂) → B × F₁ × F₂ := λ p, ⟨p.1.1, p.1.2, p.2.2⟩,
  have hf₁ : continuous f₁ := (prod.inducing_diag E₁ E₂).continuous,
  have hf₂ : continuous_on f₂ (e₁.source ×ˢ e₂.source) :=
    e₁.to_local_homeomorph.continuous_on.prod_map e₂.to_local_homeomorph.continuous_on,
  have hf₃ : continuous f₃ :=
    (continuous_fst.comp continuous_fst).prod_mk (continuous_snd.prod_map continuous_snd),
  refine ((hf₃.comp_continuous_on hf₂).comp hf₁.continuous_on _).congr _,
  { rw [e₁.source_eq, e₂.source_eq],
    exact maps_to_preimage _ _ },
  rintros ⟨b, v₁, v₂⟩ ⟨hb₁, hb₂⟩,
  simp only [prod.to_fun', prod.mk.inj_iff, eq_self_iff_true, and_true],
  rw e₁.coe_fst,
  rw [e₁.source_eq, mem_preimage],
  exact hb₁,
end

variables (e₁ e₂)

variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [topological_vector_bundle R F₁ E₁] [topological_vector_bundle R F₂ E₂]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the inverse
function for the construction `topological_vector_bundle.trivialization.prod`, the induced
trivialization for the direct sum of `E₁` and `E₂`. -/
def prod.inv_fun' (p : B × (F₁ × F₂)) : total_space (E₁ ×ᵇ E₂) :=
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

variables {e₁ e₂}

lemma prod.inv_fun'_apply {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set)
  (w₁ : F₁) (w₂ : F₂) :
  prod.inv_fun' e₁ e₂ ⟨x, w₁, w₂⟩
  = ⟨x, ((e₁.continuous_linear_equiv_at x hx₁).symm w₁,
    (e₂.continuous_linear_equiv_at x hx₂).symm w₂)⟩ :=
begin
  dsimp [prod.inv_fun'],
  rw [dif_pos, dif_pos],
end

lemma prod.left_inv {x : total_space (E₁ ×ᵇ E₂)}
  (h : x ∈ proj (E₁ ×ᵇ E₂) ⁻¹' (e₁.base_set ∩ e₂.base_set)) :
  prod.inv_fun' e₁ e₂ (prod.to_fun' e₁ e₂ x) = x :=
begin
  obtain ⟨x, v₁, v₂⟩ := x,
  simp only [prod.to_fun', prod.inv_fun', sigma.mk.inj_iff, true_and, eq_self_iff_true,
    prod.mk.inj_iff, heq_iff_eq],
  split,
  { rw [dif_pos, ← e₁.continuous_linear_equiv_at_apply x h.1,
      continuous_linear_equiv.symm_apply_apply] },
  { rw [dif_pos, ← e₂.continuous_linear_equiv_at_apply x h.2,
      continuous_linear_equiv.symm_apply_apply] },
end

lemma prod.right_inv {x : B × F₁ × F₂}
  (h : x ∈ (e₁.base_set ∩ e₂.base_set) ×ˢ (univ : set (F₁ × F₂))) :
  prod.to_fun' e₁ e₂ (prod.inv_fun' e₁ e₂ x) = x :=
begin
  obtain ⟨x, w₁, w₂⟩ := x,
  obtain ⟨h, -⟩ := h,
  dsimp only [prod.to_fun', prod.inv_fun'],
  simp only [prod.mk.inj_iff, eq_self_iff_true, true_and],
  split,
  { rw [dif_pos, ← e₁.continuous_linear_equiv_at_apply x h.1,
      continuous_linear_equiv.apply_symm_apply] },
  { rw [dif_pos, ← e₂.continuous_linear_equiv_at_apply x h.2,
      continuous_linear_equiv.apply_symm_apply] },
end

lemma prod.continuous_inv_fun :
  continuous_on (prod.inv_fun' e₁ e₂) ((e₁.base_set ∩ e₂.base_set) ×ˢ (univ : set (F₁ × F₂))) :=
begin
  rw (prod.inducing_diag E₁ E₂).continuous_on_iff,
  suffices : continuous_on (λ p : B × F₁ × F₂,
    (e₁.to_local_homeomorph.symm ⟨p.1, p.2.1⟩, e₂.to_local_homeomorph.symm ⟨p.1, p.2.2⟩))
    ((e₁.base_set ∩ e₂.base_set) ×ˢ (univ : set (F₁ × F₂))),
  { refine this.congr _,
    rintros ⟨b, v₁, v₂⟩ ⟨⟨h₁, h₂⟩, _⟩,
    dsimp at ⊢ h₁ h₂,
    rw [prod.inv_fun'_apply h₁ h₂, e₁.symm_apply_eq_mk_continuous_linear_equiv_at_symm b h₁,
      e₂.symm_apply_eq_mk_continuous_linear_equiv_at_symm b h₂] },
  have H₁ : continuous (λ p : B × F₁ × F₂, ((p.1, p.2.1), (p.1, p.2.2))) :=
    (continuous_id.prod_map continuous_fst).prod_mk (continuous_id.prod_map continuous_snd),
  have H₂ := e₁.to_local_homeomorph.symm.continuous_on.prod_map
    e₂.to_local_homeomorph.symm.continuous_on,
  refine H₂.comp H₁.continuous_on (λ x h, ⟨_, _⟩),
  { dsimp,
    rw e₁.target_eq,
    exact ⟨h.1.1, mem_univ _⟩ },
  { dsimp,
    rw e₂.target_eq,
    exact ⟨h.1.2, mem_univ _⟩ }
end

variables (e₁ e₂)

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
trivialization for the direct sum of `E₁` and `E₂`, whose base set is `e₁.base_set ∩ e₂.base_set`.
-/
def prod : trivialization R (F₁ × F₂) (E₁ ×ᵇ E₂) :=
{ to_fun := prod.to_fun' e₁ e₂,
  inv_fun := prod.inv_fun' e₁ e₂,
  source := (proj (λ x, E₁ x × E₂ x)) ⁻¹' (e₁.base_set ∩ e₂.base_set),
  target := (e₁.base_set ∩ e₂.base_set) ×ˢ (set.univ : set (F₁ × F₂)),
  map_source' := λ ⟨x, v₁, v₂⟩ h, ⟨h, set.mem_univ _⟩,
  map_target' := λ ⟨x, w₁, w₂⟩ h, h.1,
  left_inv' := λ x, prod.left_inv,
  right_inv' := λ x, prod.right_inv,
  open_source := begin
    refine (e₁.open_base_set.inter e₂.open_base_set).preimage _,
    have : continuous (proj E₁) := continuous_proj R B F₁,
    exact this.comp (continuous_fst.comp (prod.inducing_diag E₁ E₂).continuous),
  end,
  open_target := (e₁.open_base_set.inter e₂.open_base_set).prod is_open_univ,
  continuous_to_fun := prod.continuous_to_fun,
  continuous_inv_fun := prod.continuous_inv_fun,
  base_set := e₁.base_set ∩ e₂.base_set,
  open_base_set := e₁.open_base_set.inter e₂.open_base_set,
  source_eq := rfl,
  target_eq := rfl,
  proj_to_fun := λ ⟨x, v₁, v₂⟩ h, rfl,
  linear := λ x ⟨h₁, h₂⟩,
  { map_add := λ ⟨v₁, v₂⟩ ⟨v₁', v₂'⟩,
      congr_arg2 prod.mk ((e₁.linear x h₁).map_add v₁ v₁') ((e₂.linear x h₂).map_add v₂ v₂'),
    map_smul := λ c ⟨v₁, v₂⟩,
      congr_arg2 prod.mk ((e₁.linear x h₁).map_smul c v₁) ((e₂.linear x h₂).map_smul c v₂), } }

-- Patrick is not sure the next two simp lemmas really help. One could also use @[simps] above

@[simp] lemma source_prod :
  (prod e₁ e₂).source = (proj (λ x, E₁ x × E₂ x)) ⁻¹' (e₁.base_set ∩ e₂.base_set) := rfl

@[simp] lemma target_prod :
  (prod e₁ e₂).target = (e₁.base_set ∩ e₂.base_set) ×ˢ (set.univ : set (F₁ × F₂)) := rfl


@[simp] lemma base_set_prod : (prod e₁ e₂).base_set = e₁.base_set ∩ e₂.base_set :=
rfl

variables {e₁ e₂}

lemma prod_apply {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set) (v₁ : E₁ x)
  (v₂ : E₂ x) :
  prod e₁ e₂ ⟨x, (v₁, v₂)⟩
  = ⟨x, e₁.continuous_linear_equiv_at x hx₁ v₁, e₂.continuous_linear_equiv_at x hx₂ v₂⟩ :=
rfl

lemma prod_symm_apply {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set) (w₁ : F₁) (w₂ : F₂) :
  (prod e₁ e₂).to_local_equiv.symm (x, (w₁, w₂))
  = ⟨x, ((e₁.continuous_linear_equiv_at x hx₁).symm w₁,
      (e₂.continuous_linear_equiv_at x hx₂).symm w₂)⟩ :=
prod.inv_fun'_apply hx₁ hx₂ w₁ w₂

end trivialization

open trivialization

variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [topological_vector_bundle R F₁ E₁] [topological_vector_bundle R F₂ E₂]

-- Using explicit universe variables greatly speed up the next two declarations
-- that should be moved to operator_norm.lean and also adapted to continuous_linear_equiv
-- Note that continuous_linear_equiv.prod should also be renamed to continuous_linear_equiv.prod_map
universes u₁ u₂ u₃ u₄ u₅

def continuous_linear_map.prod_mapL
  (R₁ : Type u₁) [nondiscrete_normed_field R₁]
  (M₁ : Type u₂) [normed_group M₁] [normed_space R₁ M₁]
  (M₂ : Type u₃) [normed_group M₂] [normed_space R₁ M₂]
  (M₃ : Type u₄) [normed_group M₃] [normed_space R₁ M₃]
  (M₄ : Type u₅) [normed_group M₄] [normed_space R₁ M₄] :
  ((M₁ →L[R₁] M₂) × (M₃ →L[R₁] M₄)) →L[R₁] ((M₁ × M₃) →L[R₁] (M₂ × M₄)) :=
begin
  have Φ₁ : (M₁ →L[R₁] M₂) →L[R₁] (M₁ →L[R₁] M₂ × M₄) :=
    continuous_linear_map.compL R₁ M₁ M₂ (M₂ × M₄) (continuous_linear_map.inl R₁ M₂ M₄),
  have Φ₂ : (M₃ →L[R₁] M₄) →L[R₁] (M₃ →L[R₁] M₂ × M₄) :=
    continuous_linear_map.compL R₁ M₃ M₄ (M₂ × M₄) (continuous_linear_map.inr R₁ M₂ M₄),
  have Φ₁' := (continuous_linear_map.compL R₁ (M₁ × M₃) M₁ (M₂ × M₄)).flip
    (continuous_linear_map.fst R₁ M₁ M₃),
  have Φ₂' := (continuous_linear_map.compL R₁ (M₁ × M₃) M₃ (M₂ × M₄)).flip
    (continuous_linear_map.snd R₁ M₁ M₃),
  have Ψ₁ : ((M₁ →L[R₁] M₂) × (M₃ →L[R₁] M₄)) →L[R₁] (M₁ →L[R₁] M₂) :=
    continuous_linear_map.fst R₁ (M₁ →L[R₁] M₂) (M₃ →L[R₁] M₄),
  have Ψ₂ : ((M₁ →L[R₁] M₂) × (M₃ →L[R₁] M₄)) →L[R₁] (M₃ →L[R₁] M₄) :=
    continuous_linear_map.snd R₁ (M₁ →L[R₁] M₂) (M₃ →L[R₁] M₄),
  exact Φ₁' ∘L Φ₁ ∘L Ψ₁ + Φ₂' ∘L Φ₂ ∘L Ψ₂,
end

@[simp] lemma continuous_linear_map.prod_mapL_apply
  (R₁ : Type u₁) [nondiscrete_normed_field R₁]
  (M₁ : Type u₂) [normed_group M₁] [normed_space R₁ M₁]
  (M₂ : Type u₃) [normed_group M₂] [normed_space R₁ M₂]
  (M₃ : Type u₄) [normed_group M₃] [normed_space R₁ M₃]
  (M₄ : Type u₅) [normed_group M₄] [normed_space R₁ M₄]
  (p : (M₁ →L[R₁] M₂) × (M₃ →L[R₁] M₄)) :
  continuous_linear_map.prod_mapL R₁ M₁ M₂ M₃ M₄ p
  = p.1.prod_map p.2 :=
continuous_linear_map.ext (λ x, by simp [continuous_linear_map.prod_mapL])

/-- The product of two vector bundles is a vector bundle. -/
instance _root_.bundle.prod.topological_vector_bundle :
  topological_vector_bundle R (F₁ × F₂) (E₁ ×ᵇ E₂) :=
{ total_space_mk_inducing := λ b,
  begin
    rw (prod.inducing_diag E₁ E₂).inducing_iff,
    exact (total_space_mk_inducing R F₁ E₁ b).prod_mk (total_space_mk_inducing R F₂ E₂ b),
  end,
  trivialization_atlas := (λ (p : trivialization R F₁ E₁ × trivialization R F₂ E₂), p.1.prod p.2) ''
    (trivialization_atlas R F₁ E₁ ×ˢ trivialization_atlas R F₂ E₂),
  trivialization_at := λ b, (trivialization_at R F₁ E₁ b).prod (trivialization_at R F₂ E₂ b),
  mem_base_set_trivialization_at :=
    λ b, ⟨mem_base_set_trivialization_at R F₁ E₁ b, mem_base_set_trivialization_at R F₂ E₂ b⟩,
  trivialization_mem_atlas := λ b,
    ⟨(_, _), ⟨trivialization_mem_atlas R F₁ E₁ b, trivialization_mem_atlas R F₂ E₂ b⟩, rfl⟩,
  continuous_coord_change := begin
    rintros _ ⟨⟨e₁, e₂⟩, ⟨he₁, he₂⟩, rfl⟩ _ ⟨⟨e'₁, e'₂⟩, ⟨he'₁, he'₂⟩, rfl⟩,
    let s := e₁.base_set ∩ e'₁.base_set,
    let t := e₂.base_set ∩ e'₂.base_set,
    let ε := coord_change he₁ he'₁,
    let η := coord_change he₂ he'₂,
    have fact : (s ∩ t) ×ˢ (univ : set $ F₁ × F₂) =
        (e₁.base_set ∩ e₂.base_set ∩  (e'₁.base_set ∩ e'₂.base_set)) ×ˢ (univ : set $ F₁ × F₂),
      by mfld_set_tac,
    refine ⟨s ∩ t, _, _, λ b, (ε b).prod (η b), _, _⟩,
    { rw fact,
      apply topological_fiber_bundle.trivialization.symm_trans_source_eq },
    { rw fact,
      apply topological_fiber_bundle.trivialization.symm_trans_target_eq },
    { have hε := (continuous_on_coord_change he₁ he'₁).mono (inter_subset_left s t),
      have hη := (continuous_on_coord_change he₂ he'₂).mono (inter_subset_right s t),
      convert (continuous_linear_map.prod_mapL R F₁ F₁ F₂ F₂).continuous.comp_continuous_on
        (hε.prod hη),
      ext1 b,
      simp, },
    { rintros b ⟨hbs, hbt⟩ ⟨u, v⟩,
      have h : (e₁.prod e₂).to_local_homeomorph.symm _ = _ := prod_symm_apply hbs.1 hbt.1 u v,
      simp only [ε, η, h, prod_apply hbs.2 hbt.2,
        ← comp_continuous_linear_equiv_at_eq_coord_change he₁ he'₁ hbs,
        ← comp_continuous_linear_equiv_at_eq_coord_change he₂ he'₂ hbt,
        eq_self_iff_true, function.comp_app, local_equiv.coe_trans, local_homeomorph.coe_coe,
        local_homeomorph.coe_coe_symm, prod.mk.inj_iff,
        topological_vector_bundle.trivialization.coe_coe, true_and,
        continuous_linear_equiv.prod_apply, continuous_linear_equiv.trans_apply] },
  end }

variables {R F₁ E₁ F₂ E₂}

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
