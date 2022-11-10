/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sebastien Gouezel, Heather Macbeth, Patrick Massot, Floris van Doorn
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

We define constructions on vector bundles like pullbacks and direct sums in other files.
Only the trivial bundle is defined in this file.

## Tags
Vector bundle
-/

noncomputable theory

open bundle set
open_locale classical bundle

variables (R 𝕜 : Type*) {B : Type*} (F : Type*) (E : B → Type*)

section topological_vector_space
variables {B F E} [semiring R]
  [topological_space F]  [topological_space B]

/-- A mixin class for `pretrivialization`, stating that a pretrivialization is fibrewise linear with
respect to given module structures on its fibres and the model fibre. -/
protected class pretrivialization.is_linear [add_comm_monoid F] [module R F]
  [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)] (e : pretrivialization F (π E)) :
  Prop :=
(linear : ∀ b ∈ e.base_set, is_linear_map R (λ x : E b, (e (total_space_mk b x)).2))

namespace pretrivialization

variables {F E} (e : pretrivialization F (π E)) {x : total_space E} {b : B} {y : E b}

lemma linear [add_comm_monoid F] [module R F] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
  [e.is_linear R] {b : B} (hb : b ∈ e.base_set) :
  is_linear_map R (λ x : E b, (e (total_space_mk b x)).2) :=
pretrivialization.is_linear.linear b hb

variables [add_comm_monoid F] [module R F] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]

/-- A fiberwise linear inverse to `e`. -/
@[simps] protected def symmₗ (e : pretrivialization F (π E)) [e.is_linear R] (b : B) :
  F →ₗ[R] E b :=
begin
  refine is_linear_map.mk' (e.symm b) _,
  by_cases hb : b ∈ e.base_set,
  { exact (((e.linear R hb).mk' _).inverse (e.symm b) (e.symm_apply_apply_mk hb)
      (λ v, congr_arg prod.snd $ e.apply_mk_symm hb v)).is_linear },
  { rw [e.coe_symm_of_not_mem hb], exact (0 : F →ₗ[R] E b).is_linear }
end

/-- A pretrivialization for a topological vector bundle defines linear equivalences between the
fibers and the model space. -/
@[simps {fully_applied := ff}] def linear_equiv_at (e : pretrivialization F (π E)) [e.is_linear R]
  (b : B) (hb : b ∈ e.base_set) :
  E b ≃ₗ[R] F :=
{ to_fun := λ y, (e (total_space_mk b y)).2,
  inv_fun := e.symm b,
  left_inv := e.symm_apply_apply_mk hb,
  right_inv := λ v, by simp_rw [e.apply_mk_symm hb v],
  map_add' := λ v w, (e.linear R hb).map_add v w,
  map_smul' := λ c v, (e.linear R hb).map_smul c v }

/-- A fiberwise linear map equal to `e` on `e.base_set`. -/
protected def linear_map_at (e : pretrivialization F (π E)) [e.is_linear R] (b : B) : E b →ₗ[R] F :=
if hb : b ∈ e.base_set then e.linear_equiv_at R b hb else 0

variables {R}

lemma coe_linear_map_at (e : pretrivialization F (π E)) [e.is_linear R] (b : B) :
  ⇑(e.linear_map_at R b) = λ y, if b ∈ e.base_set then (e (total_space_mk b y)).2 else 0 :=
by { rw [pretrivialization.linear_map_at], split_ifs; refl }

lemma coe_linear_map_at_of_mem (e : pretrivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∈ e.base_set) :
  ⇑(e.linear_map_at R b) = λ y, (e (total_space_mk b y)).2 :=
by simp_rw [coe_linear_map_at, if_pos hb]

lemma linear_map_at_apply (e : pretrivialization F (π E)) [e.is_linear R] {b : B} (y : E b) :
  e.linear_map_at R b y = if b ∈ e.base_set then (e (total_space_mk b y)).2 else 0 :=
by rw [coe_linear_map_at]

lemma linear_map_at_def_of_mem (e : pretrivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∈ e.base_set) :
  e.linear_map_at R b = e.linear_equiv_at R b hb :=
dif_pos hb

lemma linear_map_at_def_of_not_mem (e : pretrivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∉ e.base_set) :
  e.linear_map_at R b = 0 :=
dif_neg hb

lemma linear_map_at_eq_zero (e : pretrivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∉ e.base_set) :
  e.linear_map_at R b = 0 :=
dif_neg hb

lemma symmₗ_linear_map_at (e : pretrivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∈ e.base_set) (y : E b) :
  e.symmₗ R b (e.linear_map_at R b y) = y :=
by { rw [e.linear_map_at_def_of_mem hb], exact (e.linear_equiv_at R b hb).left_inv y }

lemma linear_map_at_symmₗ (e : pretrivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∈ e.base_set) (y : F) :
  e.linear_map_at R b (e.symmₗ R b y) = y :=
by { rw [e.linear_map_at_def_of_mem hb], exact (e.linear_equiv_at R b hb).right_inv y }

end pretrivialization

variables (R) [topological_space (total_space E)]

/-- A mixin class for `trivialization`, stating that a trivialization is fibrewise linear with
respect to given module structures on its fibres and the model fibre. -/
protected class trivialization.is_linear [add_comm_monoid F] [module R F]
  [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)] (e : trivialization F (π E)) : Prop :=
(linear : ∀ b ∈ e.base_set, is_linear_map R (λ x : E b, (e (total_space_mk b x)).2))

namespace trivialization

variables (e : trivialization F (π E)) {x : total_space E} {b : B} {y : E b}

protected lemma linear [add_comm_monoid F] [module R F] [∀ x, add_comm_monoid (E x)]
  [∀ x, module R (E x)] [e.is_linear R] {b : B} (hb : b ∈ e.base_set) :
  is_linear_map R (λ y : E b, (e (total_space_mk b y)).2) :=
trivialization.is_linear.linear b hb

instance to_pretrivialization.is_linear [add_comm_monoid F] [module R F]
  [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)] [e.is_linear R] :
  e.to_pretrivialization.is_linear R :=
{ ..(‹_› : e.is_linear R) }

variables [add_comm_monoid F] [module R F] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]

/-- A trivialization for a topological vector bundle defines linear equivalences between the
fibers and the model space. -/
def linear_equiv_at (e : trivialization F (π E)) [e.is_linear R] (b : B) (hb : b ∈ e.base_set) :
  E b ≃ₗ[R] F :=
e.to_pretrivialization.linear_equiv_at R b hb

variables {R}

@[simp]
lemma linear_equiv_at_apply (e : trivialization F (π E)) [e.is_linear R] (b : B)
  (hb : b ∈ e.base_set) (v : E b) :
  e.linear_equiv_at R b hb v = (e (total_space_mk b v)).2 := rfl

@[simp]
lemma linear_equiv_at_symm_apply (e : trivialization F (π E)) [e.is_linear R] (b : B)
  (hb : b ∈ e.base_set) (v : F) :
  (e.linear_equiv_at R b hb).symm v = e.symm b v := rfl

variables (R)

/-- A fiberwise linear inverse to `e`. -/
protected def symmₗ (e : trivialization F (π E)) [e.is_linear R] (b : B) : F →ₗ[R] E b :=
e.to_pretrivialization.symmₗ R b

variables {R}

lemma coe_symmₗ (e : trivialization F (π E)) [e.is_linear R] (b : B) : ⇑(e.symmₗ R b) = e.symm b :=
rfl

variables (R)

/-- A fiberwise linear map equal to `e` on `e.base_set`. -/
protected def linear_map_at (e : trivialization F (π E)) [e.is_linear R] (b : B) : E b →ₗ[R] F :=
e.to_pretrivialization.linear_map_at R b

variables {R}

lemma coe_linear_map_at (e : trivialization F (π E)) [e.is_linear R] (b : B) :
  ⇑(e.linear_map_at R b) = λ y, if b ∈ e.base_set then (e (total_space_mk b y)).2 else 0 :=
e.to_pretrivialization.coe_linear_map_at b

lemma coe_linear_map_at_of_mem (e : trivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∈ e.base_set) :
  ⇑(e.linear_map_at R b) = λ y, (e (total_space_mk b y)).2 :=
by simp_rw [coe_linear_map_at, if_pos hb]

lemma linear_map_at_apply (e : trivialization F (π E)) [e.is_linear R] {b : B} (y : E b) :
  e.linear_map_at R b y = if b ∈ e.base_set then (e (total_space_mk b y)).2 else 0 :=
by rw [coe_linear_map_at]

lemma linear_map_at_def_of_mem (e : trivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∈ e.base_set) :
  e.linear_map_at R b = e.linear_equiv_at R b hb :=
dif_pos hb

lemma linear_map_at_def_of_not_mem (e : trivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∉ e.base_set) :
  e.linear_map_at R b = 0 :=
dif_neg hb

lemma symmₗ_linear_map_at (e : trivialization F (π E)) [e.is_linear R] {b : B} (hb : b ∈ e.base_set)
  (y : E b) :
  e.symmₗ R b (e.linear_map_at R b y) = y :=
e.to_pretrivialization.symmₗ_linear_map_at hb y

lemma linear_map_at_symmₗ (e : trivialization F (π E)) [e.is_linear R] {b : B} (hb : b ∈ e.base_set)
  (y : F) :
  e.linear_map_at R b (e.symmₗ R b y) = y :=
e.to_pretrivialization.linear_map_at_symmₗ hb y

variables (R)

/-- A coordinate change function between two trivializations, as a continuous linear equivalence.
  Defined to be the identity when `b` does not lie in the base set of both trivializations. -/
def coord_changeL (e e' : trivialization F (π E)) [e.is_linear R] [e'.is_linear R] (b : B) :
  F ≃L[R] F :=
{ continuous_to_fun := begin
    by_cases hb : b ∈ e.base_set ∩ e'.base_set,
    { simp_rw [dif_pos hb],
      refine (e'.continuous_on.comp_continuous _ _).snd,
      exact e.continuous_on_symm.comp_continuous (continuous.prod.mk b)
        (λ y, mk_mem_prod hb.1 (mem_univ y)),
      exact (λ y, e'.mem_source.mpr hb.2) },
    { rw [dif_neg hb], exact continuous_id }
  end,
  continuous_inv_fun := begin
    by_cases hb : b ∈ e.base_set ∩ e'.base_set,
    { simp_rw [dif_pos hb],
      refine (e.continuous_on.comp_continuous _ _).snd,
      exact e'.continuous_on_symm.comp_continuous (continuous.prod.mk b)
        (λ y, mk_mem_prod hb.2 (mem_univ y)),
      exact (λ y, e.mem_source.mpr hb.1) },
    { rw [dif_neg hb], exact continuous_id }
  end,
  .. if hb : b ∈ e.base_set ∩ e'.base_set then
     (e.linear_equiv_at R b (hb.1 : _)).symm.trans (e'.linear_equiv_at R b hb.2)
    else linear_equiv.refl R F }

variables {R}

lemma coe_coord_changeL (e e' : trivialization F (π E)) [e.is_linear R] [e'.is_linear R] {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) :
  ⇑(coord_changeL R e e' b)
  = (e.linear_equiv_at R b hb.1).symm.trans (e'.linear_equiv_at R b hb.2) :=
congr_arg linear_equiv.to_fun (dif_pos hb)

lemma coord_changeL_apply (e e' : trivialization F (π E)) [e.is_linear R] [e'.is_linear R] {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  coord_changeL R e e' b y = (e' (total_space_mk b (e.symm b y))).2 :=
congr_arg (λ f, linear_equiv.to_fun f y) (dif_pos hb)

lemma mk_coord_changeL (e e' : trivialization F (π E)) [e.is_linear R] [e'.is_linear R] {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  (b, coord_changeL R e e' b y) = e' (total_space_mk b (e.symm b y)) :=
begin
  ext,
  { rw [e.mk_symm hb.1 y, e'.coe_fst', e.proj_symm_apply' hb.1],
    rw [e.proj_symm_apply' hb.1], exact hb.2 },
  { exact e.coord_changeL_apply e' hb y }
end

/-- A version of `coord_change_apply` that fully unfolds `coord_change`. The right-hand side is
ugly, but has good definitional properties for specifically defined trivializations. -/
lemma coord_changeL_apply' (e e' : trivialization F (π E)) [e.is_linear R] [e'.is_linear R] {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  coord_changeL R e e' b y = (e' (e.to_local_homeomorph.symm (b, y))).2 :=
by rw [e.coord_changeL_apply e' hb, e.mk_symm hb.1]

lemma coord_changeL_symm_apply (e e' : trivialization F (π E)) [e.is_linear R] [e'.is_linear R]
  {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) :
  ⇑(coord_changeL R e e' b).symm
  = (e'.linear_equiv_at R b hb.2).symm.trans (e.linear_equiv_at R b hb.1) :=
congr_arg linear_equiv.inv_fun (dif_pos hb)

end trivialization

end topological_vector_space

section

variables [nontrivially_normed_field R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
  [normed_add_comm_group F] [normed_space R F] [topological_space B]
  [topological_space (total_space E)] [∀ x, topological_space (E x)]

/-- The space `total_space E` (for `E : B → Type*` such that each `E x` is a topological vector
space) has a topological vector space structure with fiber `F` (denoted with
`topological_vector_bundle R F E`) if around every point there is a fiber bundle trivialization
which is linear in the fibers. -/
class topological_vector_bundle :=
(total_space_mk_inducing [] : ∀ (b : B), inducing (@total_space_mk B E b))
(trivialization_atlas [] : set (trivialization F (π E)))
(trivialization_linear' : ∀ (e : trivialization F (π E)) (he : e ∈ trivialization_atlas),
  e.is_linear R)
(trivialization_at [] : B → trivialization F (π E))
(mem_base_set_trivialization_at [] : ∀ b : B, b ∈ (trivialization_at b).base_set)
(trivialization_mem_atlas [] : ∀ b : B, trivialization_at b ∈ trivialization_atlas)
(continuous_on_coord_change' [] : ∀ (e e' : trivialization F (π E)) (he : e ∈ trivialization_atlas)
  (he' : e' ∈ trivialization_atlas),
  have _ := trivialization_linear' e he,
  have _ := trivialization_linear' e' he',
  continuous_on
  (λ b, by exactI trivialization.coord_changeL R e e' b : B → F →L[R] F) (e.base_set ∩ e'.base_set))

export topological_vector_bundle (trivialization_atlas trivialization_at
  mem_base_set_trivialization_at trivialization_mem_atlas)

variables {F E} [topological_vector_bundle R F E]

/-- Given a type `E` equipped with a topological vector bundle structure, this is a `Prop` typeclass
for trivializations of `E`, expressing that a trivialization is in the designated atlas for the
bundle.  This is needed because lemmas about the linearity of trivializations or the continuity (as
functions to `F →L[R] F`, where `F` is the model fibre) of the transition functions are only
expected to hold for trivializations in the designated atlas. -/
@[mk_iff]
class mem_trivialization_atlas (e : trivialization F (π E)) : Prop :=
(out : e ∈ trivialization_atlas R F E)

instance (b : B) : mem_trivialization_atlas R (trivialization_at R F E b) :=
{ out := topological_vector_bundle.trivialization_mem_atlas R F E b }

@[priority 100]
instance trivialization_linear (e : trivialization F (π E)) [he : mem_trivialization_atlas R e] :
  e.is_linear R :=
topological_vector_bundle.trivialization_linear' e he.out

lemma continuous_on_coord_change (e e' : trivialization F (π E))
  [he : mem_trivialization_atlas R e]
  [he' : mem_trivialization_atlas R e'] :
  continuous_on
  (λ b, trivialization.coord_changeL R e e' b : B → F →L[R] F) (e.base_set ∩ e'.base_set) :=
topological_vector_bundle.continuous_on_coord_change' e e' he.out he'.out

namespace trivialization

/-- Forward map of `continuous_linear_equiv_at` (only propositionally equal),
  defined everywhere (`0` outside domain). -/
@[simps apply {fully_applied := ff}]
def continuous_linear_map_at (e : trivialization F (π E)) [e.is_linear R] (b : B) :
  E b →L[R] F :=
{ to_fun := e.linear_map_at R b, -- given explicitly to help `simps`
  cont := begin
    dsimp,
    rw [e.coe_linear_map_at b],
    refine continuous_if_const _ (λ hb, _) (λ _, continuous_zero),
    exact continuous_snd.comp (e.to_local_homeomorph.continuous_on.comp_continuous
      (topological_vector_bundle.total_space_mk_inducing R F E b).continuous
      (λ x, e.mem_source.mpr hb))
  end,
  .. e.linear_map_at R b }

/-- Backwards map of `continuous_linear_equiv_at`, defined everywhere. -/
@[simps apply {fully_applied := ff}]
def symmL (e : trivialization F (π E)) [e.is_linear R] (b : B) : F →L[R] E b :=
{ to_fun := e.symm b, -- given explicitly to help `simps`
  cont := begin
    by_cases hb : b ∈ e.base_set,
    { rw (topological_vector_bundle.total_space_mk_inducing R F E b).continuous_iff,
      exact e.continuous_on_symm.comp_continuous (continuous_const.prod_mk continuous_id)
        (λ x, mk_mem_prod hb (mem_univ x)) },
    { refine continuous_zero.congr (λ x, (e.symm_apply_of_not_mem hb x).symm) },
  end,
  .. e.symmₗ R b }

variables {R}

lemma symmL_continuous_linear_map_at (e : trivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∈ e.base_set) (y : E b) :
  e.symmL R b (e.continuous_linear_map_at R b y) = y :=
e.symmₗ_linear_map_at hb y

lemma continuous_linear_map_at_symmL (e : trivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∈ e.base_set) (y : F) :
  e.continuous_linear_map_at R b (e.symmL R b y) = y :=
e.linear_map_at_symmₗ hb y

variables (R)

/-- In a topological vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
@[simps apply symm_apply {fully_applied := ff}]
def continuous_linear_equiv_at (e : trivialization F (π E)) [e.is_linear R] (b : B)
  (hb : b ∈ e.base_set) : E b ≃L[R] F :=
{ to_fun := λ y, (e (total_space_mk b y)).2, -- given explicitly to help `simps`
  inv_fun := e.symm b, -- given explicitly to help `simps`
  continuous_to_fun := continuous_snd.comp (e.to_local_homeomorph.continuous_on.comp_continuous
    (topological_vector_bundle.total_space_mk_inducing R F E b).continuous
    (λ x, e.mem_source.mpr hb)),
  continuous_inv_fun := (e.symmL R b).continuous,
  .. e.to_pretrivialization.linear_equiv_at R b hb }

variables {R}

lemma coe_continuous_linear_equiv_at_eq (e : trivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∈ e.base_set) :
  (e.continuous_linear_equiv_at R b hb : E b → F) = e.continuous_linear_map_at R b :=
(e.coe_linear_map_at_of_mem hb).symm

lemma symm_continuous_linear_equiv_at_eq (e : trivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∈ e.base_set) :
  ((e.continuous_linear_equiv_at R b hb).symm : F → E b) = e.symmL R b :=
rfl

@[simp] lemma continuous_linear_equiv_at_apply' (e : trivialization F (π E)) [e.is_linear R]
  (x : total_space E) (hx : x ∈ e.source) :
  e.continuous_linear_equiv_at R x.proj (e.mem_source.1 hx) x.2 = (e x).2 := by { cases x, refl }

variables (R)

lemma apply_eq_prod_continuous_linear_equiv_at (e : trivialization F (π E)) [e.is_linear R] (b : B)
  (hb : b ∈ e.base_set) (z : E b) :
  e.to_local_homeomorph ⟨b, z⟩ = (b, e.continuous_linear_equiv_at R b hb z) :=
begin
  ext,
  { refine e.coe_fst _,
    rw e.source_eq,
    exact hb },
  { simp only [coe_coe, continuous_linear_equiv_at_apply] }
end

variables {R}

lemma symm_apply_eq_mk_continuous_linear_equiv_at_symm (e : trivialization F (π E)) [e.is_linear R]
  (b : B) (hb : b ∈ e.base_set) (z : F) :
  e.to_local_homeomorph.symm ⟨b, z⟩
  = total_space_mk b ((e.continuous_linear_equiv_at R b hb).symm z) :=
begin
  have h : (b, z) ∈ e.to_local_homeomorph.target,
  { rw e.target_eq,
    exact ⟨hb, mem_univ _⟩ },
  apply e.to_local_homeomorph.inj_on (e.to_local_homeomorph.map_target h),
  { simp only [e.source_eq, hb, mem_preimage]},
  simp_rw [e.apply_eq_prod_continuous_linear_equiv_at R b hb, e.to_local_homeomorph.right_inv h,
    continuous_linear_equiv.apply_symm_apply],
end

lemma comp_continuous_linear_equiv_at_eq_coord_change (e e' : trivialization F (π E))
  [e.is_linear R] [e'.is_linear R] {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) :
  (e.continuous_linear_equiv_at R b hb.1).symm.trans (e'.continuous_linear_equiv_at R b hb.2)
  = coord_changeL R e e' b :=
by { ext v, rw [coord_changeL_apply e e' hb], refl }

end trivialization

namespace trivial_topological_vector_bundle
variables (R B F)

/-- Local trivialization for trivial bundle. -/
def trivialization : trivialization F (π (bundle.trivial B F)) :=
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
    simp only [prod.topological_space, induced_inf, induced_compose], exact le_rfl, },
  continuous_inv_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [bundle.total_space.topological_space, induced_inf, induced_compose],
    exact le_rfl, },
  base_set := univ,
  open_base_set := is_open_univ,
  source_eq := rfl,
  target_eq := by simp only [univ_prod_univ],
  proj_to_fun := λ y hy, rfl }

instance trivialization.is_linear : (trivialization B F).is_linear R :=
{ linear := λ x hx, ⟨λ y z, rfl, λ c y, rfl⟩ }

variables {R}

lemma trivialization.coord_changeL (b : B) :
  (trivialization B F).coord_changeL R
    (trivialization B F) b = continuous_linear_equiv.refl R F :=
begin
  ext v,
  rw [trivialization.coord_changeL_apply'],
  exacts [rfl, ⟨mem_univ _, mem_univ _⟩]
end

@[simp]
lemma trivialization_source : (trivialization B F).source = univ := rfl

@[simp]
lemma trivialization_target : (trivialization B F).target = univ := rfl

instance topological_vector_bundle :
  topological_vector_bundle R F (bundle.trivial B F) :=
{ trivialization_atlas := {trivial_topological_vector_bundle.trivialization B F},
  trivialization_linear' := begin
    intros e he,
    rw mem_singleton_iff at he,
    subst he,
    apply_instance
  end,
  trivialization_at := λ x, trivial_topological_vector_bundle.trivialization B F,
  mem_base_set_trivialization_at := mem_univ,
  trivialization_mem_atlas := λ x, mem_singleton _,
  total_space_mk_inducing := λ b, ⟨begin
    have : (λ (x : trivial B F b), x) = @id F, by { ext x, refl },
    simp only [total_space.topological_space, induced_inf, induced_compose, function.comp,
      total_space.proj, induced_const, top_inf_eq, trivial.proj_snd, id.def,
      trivial.topological_space, this, induced_id],
  end⟩,
  continuous_on_coord_change' := begin
    intros e e' he he',
    rw mem_singleton_iff at he he',
    subst he,
    subst he',
    simp_rw trivialization.coord_changeL,
    exact continuous_const.continuous_on
  end }

end trivial_topological_vector_bundle

/- Not registered as an instance because of a metavariable. -/
lemma is_topological_vector_bundle_is_topological_fiber_bundle :
  is_topological_fiber_bundle F (@total_space.proj B E) :=
λ x, ⟨trivialization_at R F E x, mem_base_set_trivialization_at R F E x⟩

include R F

namespace topological_vector_bundle

lemma continuous_total_space_mk (x : B) : continuous (@total_space_mk B E x) :=
(topological_vector_bundle.total_space_mk_inducing R F E x).continuous

variables (R B F)

@[continuity] lemma continuous_proj : continuous (@total_space.proj B E) :=
begin
  apply @is_topological_fiber_bundle.continuous_proj B F,
  apply @is_topological_vector_bundle_is_topological_fiber_bundle R,
end

end topological_vector_bundle

/-! ### Constructing topological vector bundles -/

variables (R B F)

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
  index_at := default,
  mem_base_set_at := λ x, mem_univ x,
  coord_change := λ i j x, continuous_linear_map.id R F,
  coord_change_self := λ i x hx v, rfl,
  coord_change_comp := λ i j k x hx v, rfl,
  coord_change_continuous := λ i j, continuous_on_const }

instance (ι : Type*) [inhabited ι] : inhabited (topological_vector_bundle_core R B F ι) :=
⟨trivial_topological_vector_bundle_core R B F ι⟩

namespace topological_vector_bundle_core

variables {R B F} {ι : Type*} (Z : topological_vector_bundle_core R B F ι)

/-- Natural identification to a `topological_fiber_bundle_core`. -/
def to_topological_fiber_bundle_core : topological_fiber_bundle_core ι B F :=
{ coord_change := λ i j b, Z.coord_change i j b,
  coord_change_continuous := λ i j, is_bounded_bilinear_map_apply.continuous.comp_continuous_on
      ((Z.coord_change_continuous i j).prod_map continuous_on_id),
  ..Z }

instance to_topological_fiber_bundle_core_coe : has_coe (topological_vector_bundle_core R B F ι)
  (topological_fiber_bundle_core ι B F) := ⟨to_topological_fiber_bundle_core⟩

include Z

lemma coord_change_linear_comp (i j k : ι): ∀ x ∈ (Z.base_set i) ∩ (Z.base_set j) ∩ (Z.base_set k),
  (Z.coord_change j k x).comp (Z.coord_change i j x) = Z.coord_change i k x :=
λ x hx, by { ext v, exact Z.coord_change_comp i j k x hx v }

/-- The index set of a topological vector bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments has_nonempty_instance]
def index := ι

/-- The base space of a topological vector bundle core, as a convenience function for dot notation-/
@[nolint unused_arguments, reducible]
def base := B

/-- The fiber of a topological vector bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_nonempty_instance]
def fiber : B → Type* := Z.to_topological_fiber_bundle_core.fiber

instance topological_space_fiber (x : B) : topological_space (Z.fiber x) :=
by delta_instance topological_vector_bundle_core.fiber
instance add_comm_monoid_fiber : ∀ (x : B), add_comm_monoid (Z.fiber x) :=
by dsimp [topological_vector_bundle_core.fiber]; delta_instance topological_fiber_bundle_core.fiber
instance module_fiber : ∀ (x : B), module R (Z.fiber x) :=
by dsimp [topological_vector_bundle_core.fiber];  delta_instance topological_fiber_bundle_core.fiber
instance add_comm_group_fiber [add_comm_group F] : ∀ (x : B), add_comm_group (Z.fiber x) :=
by dsimp [topological_vector_bundle_core.fiber];  delta_instance topological_fiber_bundle_core.fiber

/-- The projection from the total space of a topological fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps] def proj : total_space Z.fiber → B := total_space.proj

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
instance to_topological_space : topological_space Z.total_space :=
topological_fiber_bundle_core.to_topological_space ι ↑Z

variables {ι} (b : B) (a : F)

@[simp, mfld_simps] lemma coe_coord_change (i j : ι) :
  Z.to_topological_fiber_bundle_core.coord_change i j b = Z.coord_change i j b := rfl

/-- One of the standard local trivializations of a vector bundle constructed from core, taken by
considering this in particular as a fiber bundle constructed from core. -/
def local_triv (i : ι) : trivialization F (π Z.fiber) :=
by dsimp [topological_vector_bundle_core.total_space, topological_vector_bundle_core.fiber];
  exact Z.to_topological_fiber_bundle_core.local_triv i

/-- The standard local trivializations of a vector bundle constructed from core are linear. -/
instance local_triv.is_linear (i : ι) : (Z.local_triv i).is_linear R :=
{ linear := λ x hx, by dsimp [topological_vector_bundle_core.local_triv]; exact
  { map_add := λ v w, by simp only [continuous_linear_map.map_add] with mfld_simps,
    map_smul := λ r v, by simp only [continuous_linear_map.map_smul] with mfld_simps} }

variables (i j : ι)

@[simp, mfld_simps] lemma mem_local_triv_source (p : Z.total_space) :
  p ∈ (Z.local_triv i).source ↔ p.1 ∈ Z.base_set i :=
by dsimp [topological_vector_bundle_core.fiber]; exact iff.rfl

@[simp, mfld_simps] lemma base_set_at : Z.base_set i = (Z.local_triv i).base_set := rfl

@[simp, mfld_simps] lemma local_triv_apply (p : Z.total_space) :
  (Z.local_triv i) p = ⟨p.1, Z.coord_change (Z.index_at p.1) i p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma mem_local_triv_target (p : B × F) :
  p ∈ (Z.local_triv i).target ↔ p.1 ∈ (Z.local_triv i).base_set :=
Z.to_topological_fiber_bundle_core.mem_local_triv_target i p

@[simp, mfld_simps] lemma local_triv_symm_fst (p : B × F) :
  (Z.local_triv i).to_local_homeomorph.symm p =
    ⟨p.1, Z.coord_change i (Z.index_at p.1) p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma local_triv_symm_apply {b : B} (hb : b ∈ Z.base_set i) (v : F) :
  (Z.local_triv i).symm b v = Z.coord_change i (Z.index_at b) b v :=
by apply (Z.local_triv i).symm_apply hb v

@[simp, mfld_simps] lemma local_triv_coord_change_eq {b : B} (hb : b ∈ Z.base_set i ∩ Z.base_set j)
  (v : F) :
  (Z.local_triv i).coord_changeL R (Z.local_triv j) b v = Z.coord_change i j b v :=
begin
  rw [trivialization.coord_changeL_apply', local_triv_symm_fst, local_triv_apply,
    coord_change_comp],
  exacts [⟨⟨hb.1, Z.mem_base_set_at b⟩, hb.2⟩, hb]
end

/-- Preferred local trivialization of a vector bundle constructed from core, at a given point, as
a bundle trivialization -/
def local_triv_at (b : B) : trivialization F (π Z.fiber) :=
Z.local_triv (Z.index_at b)

@[simp, mfld_simps] lemma local_triv_at_def :
  Z.local_triv (Z.index_at b) = Z.local_triv_at b := rfl

@[simp, mfld_simps] lemma mem_source_at : (⟨b, a⟩ : Z.total_space) ∈ (Z.local_triv_at b).source :=
by { rw [local_triv_at, mem_local_triv_source], exact Z.mem_base_set_at b }

@[simp, mfld_simps] lemma local_triv_at_apply (p : Z.total_space) :
  ((Z.local_triv_at p.1) p) = ⟨p.1, p.2⟩ :=
topological_fiber_bundle_core.local_triv_at_apply Z p

@[simp, mfld_simps] lemma local_triv_at_apply_mk (b : B) (a : F) :
  ((Z.local_triv_at b) ⟨b, a⟩) = ⟨b, a⟩ :=
Z.local_triv_at_apply _

@[simp, mfld_simps] lemma mem_local_triv_at_base_set :
  b ∈ (Z.local_triv_at b).base_set :=
topological_fiber_bundle_core.mem_local_triv_at_base_set Z b

instance : topological_vector_bundle R F Z.fiber :=
{ total_space_mk_inducing := λ b, ⟨ begin refine le_antisymm _ (λ s h, _),
    { rw ←continuous_iff_le_induced,
      exact topological_fiber_bundle_core.continuous_total_space_mk Z b, },
    { refine is_open_induced_iff.mpr ⟨(Z.local_triv_at b).source ∩ (Z.local_triv_at b) ⁻¹'
        ((Z.local_triv_at b).base_set ×ˢ s), (continuous_on_open_iff
        (Z.local_triv_at b).open_source).mp (Z.local_triv_at b).continuous_to_fun _
        ((Z.local_triv_at b).open_base_set.prod h), _⟩,
      rw [preimage_inter, ←preimage_comp, function.comp],
      simp only [total_space_mk],
      refine ext_iff.mpr (λ a, ⟨λ ha, _, λ ha, ⟨Z.mem_base_set_at b, _⟩⟩),
      { simp only [mem_prod, mem_preimage, mem_inter_iff, local_triv_at_apply_mk] at ha,
        exact ha.2.2, },
      { simp only [mem_prod, mem_preimage, mem_inter_iff, local_triv_at_apply_mk],
        exact ⟨Z.mem_base_set_at b, ha⟩, } } end⟩,
  trivialization_atlas := set.range Z.local_triv,
  trivialization_linear' := begin
    rintros _ ⟨i, rfl⟩,
    apply_instance
  end,
  trivialization_at := Z.local_triv_at,
  mem_base_set_trivialization_at := Z.mem_base_set_at,
  trivialization_mem_atlas := λ b, ⟨Z.index_at b, rfl⟩,
  continuous_on_coord_change' := begin
    rintros _ _ ⟨i, rfl⟩ ⟨i', rfl⟩,
    refine (Z.coord_change_continuous i i').congr (λ b hb, _),
    ext v,
    simp_rw [continuous_linear_equiv.coe_coe, Z.local_triv_coord_change_eq i i' hb],
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
variables [nontrivially_normed_field R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
  [normed_add_comm_group F] [normed_space R F] [topological_space B]

open topological_space

open topological_vector_bundle
/-- This structure permits to define a vector bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space or the fibers.
The total space is hence given a topology in such a way that there is a fiber bundle structure for
which the local equivalences are also local homeomorphisms and hence vector bundle trivializations.
The topology on the fibers is induced from the one on the total space.

The field `exists_coord_change` is stated as an existential statement (instead of 3 separate
fields), since it depends on propositional information (namely `e e' ∈ pretrivialization_atlas`).
This makes it inconvenient to explicitly define a `coord_change` function when constructing a
`topological_vector_prebundle`. -/
@[nolint has_nonempty_instance]
structure topological_vector_prebundle :=
(pretrivialization_atlas : set (pretrivialization F (π E)))
(pretrivialization_linear' : ∀ (e : pretrivialization F (π E)) (he : e ∈ pretrivialization_atlas),
  e.is_linear R)
(pretrivialization_at : B → pretrivialization F (π E))
(mem_base_pretrivialization_at : ∀ x : B, x ∈ (pretrivialization_at x).base_set)
(pretrivialization_mem_atlas : ∀ x : B, pretrivialization_at x ∈ pretrivialization_atlas)
(exists_coord_change : ∀ (e e' ∈ pretrivialization_atlas), ∃ f : B → F →L[R] F,
  continuous_on f (e.base_set ∩ e'.base_set) ∧
  ∀ (b : B) (hb : b ∈ e.base_set ∩ e'.base_set) (v : F),
    f b v = (e' (total_space_mk b (e.symm b v))).2)

namespace topological_vector_prebundle

variables {R E F}

/-- A randomly chosen coordinate change on a `topological_vector_prebundle`, given by
  the field `exists_coord_change`. -/
def coord_change (a : topological_vector_prebundle R F E)
  {e e' : pretrivialization F (π E)} (he : e ∈ a.pretrivialization_atlas)
  (he' : e' ∈ a.pretrivialization_atlas) (b : B) : F →L[R] F :=
classical.some (a.exists_coord_change e he e' he') b

lemma continuous_on_coord_change (a : topological_vector_prebundle R F E)
  {e e' : pretrivialization F (π E)} (he : e ∈ a.pretrivialization_atlas)
  (he' : e' ∈ a.pretrivialization_atlas) :
  continuous_on (a.coord_change he he') (e.base_set ∩ e'.base_set) :=
(classical.some_spec (a.exists_coord_change e he e' he')).1

lemma coord_change_apply (a : topological_vector_prebundle R F E)
  {e e' : pretrivialization F (π E)} (he : e ∈ a.pretrivialization_atlas)
  (he' : e' ∈ a.pretrivialization_atlas) {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) (v : F) :
  a.coord_change he he' b v = (e' (total_space_mk b (e.symm b v))).2 :=
(classical.some_spec (a.exists_coord_change e he e' he')).2 b hb v

lemma mk_coord_change (a : topological_vector_prebundle R F E)
  {e e' : pretrivialization F (π E)} (he : e ∈ a.pretrivialization_atlas)
  (he' : e' ∈ a.pretrivialization_atlas) {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) (v : F) :
  (b, a.coord_change he he' b v) = e' (total_space_mk b (e.symm b v)) :=
begin
  ext,
  { rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1],
    rw [e.proj_symm_apply' hb.1], exact hb.2 },
  { exact a.coord_change_apply he he' hb v }
end

/-- Natural identification of `topological_vector_prebundle` as a `topological_fiber_prebundle`. -/
def to_topological_fiber_prebundle (a : topological_vector_prebundle R F E) :
  topological_fiber_prebundle F (@total_space.proj B E) :=
{ pretrivialization_atlas := a.pretrivialization_atlas,
  pretrivialization_at := a.pretrivialization_at,
  pretrivialization_mem_atlas := a.pretrivialization_mem_atlas,
  continuous_triv_change := begin
    intros e he e' he',
    have := is_bounded_bilinear_map_apply.continuous.comp_continuous_on
      ((a.continuous_on_coord_change he' he).prod_map continuous_on_id),
    have H : e'.to_local_equiv.target ∩ e'.to_local_equiv.symm ⁻¹'
      e.to_local_equiv.source =(e'.base_set ∩ e.base_set) ×ˢ univ,
    { rw [e'.target_eq, e.source_eq],
      ext ⟨b, f⟩,
      simp only [-total_space.proj, and.congr_right_iff, e'.proj_symm_apply', iff_self,
        implies_true_iff] with mfld_simps {contextual := tt} },
    rw [H],
    refine (continuous_on_fst.prod this).congr _,
    rintros ⟨b, f⟩ ⟨hb, -⟩,
    dsimp only [function.comp, prod.map],
    rw [a.mk_coord_change _ _ hb, e'.mk_symm hb.1],
    refl,
  end,
  .. a }

/-- Topology on the total space that will make the prebundle into a bundle. -/
def total_space_topology (a : topological_vector_prebundle R F E) :
  topological_space (total_space E) :=
a.to_topological_fiber_prebundle.total_space_topology

/-- Promotion from a `trivialization` in the `pretrivialization_atlas` of a
`topological_vector_prebundle` to a `trivialization`. -/
def trivialization_of_mem_pretrivialization_atlas (a : topological_vector_prebundle R F E)
  {e : pretrivialization F (π E)} (he : e ∈ a.pretrivialization_atlas) :
  @trivialization B F _ _ _ a.total_space_topology (π E) :=
a.to_topological_fiber_prebundle.trivialization_of_mem_pretrivialization_atlas he

lemma linear_of_mem_pretrivialization_atlas (a : topological_vector_prebundle R F E)
  {e : pretrivialization F (π E)} (he : e ∈ a.pretrivialization_atlas) :
  @trivialization.is_linear R B F _ _ _ _ a.total_space_topology _ _ _ _
    (trivialization_of_mem_pretrivialization_atlas a he) :=
{ linear := (a.pretrivialization_linear' e he).linear }

variable (a : topological_vector_prebundle R F E)

lemma mem_trivialization_at_source (b : B) (x : E b) :
  total_space_mk b x ∈ (a.pretrivialization_at b).source :=
begin
  simp only [(a.pretrivialization_at b).source_eq, mem_preimage, total_space.proj],
  exact a.mem_base_pretrivialization_at b,
end

@[simp] lemma total_space_mk_preimage_source (b : B) :
  (total_space_mk b) ⁻¹' (a.pretrivialization_at b).source = univ :=
begin
  apply eq_univ_of_univ_subset,
  rw [(a.pretrivialization_at b).source_eq, ←preimage_comp, function.comp],
  simp only [total_space.proj],
  rw preimage_const_of_mem _,
  exact a.mem_base_pretrivialization_at b,
end

/-- Topology on the fibers `E b` induced by the map `E b → E.total_space`. -/
def fiber_topology (b : B) : topological_space (E b) :=
topological_space.induced (total_space_mk b) a.total_space_topology

@[continuity] lemma inducing_total_space_mk (b : B) :
  @inducing _ _ (a.fiber_topology b) a.total_space_topology (total_space_mk b) :=
by { letI := a.total_space_topology, letI := a.fiber_topology b, exact ⟨rfl⟩ }

@[continuity] lemma continuous_total_space_mk (b : B) :
  @continuous _ _ (a.fiber_topology b) a.total_space_topology (total_space_mk b) :=
begin
  letI := a.total_space_topology, letI := a.fiber_topology b,
  exact (a.inducing_total_space_mk b).continuous
end

/-- Make a `topological_vector_bundle` from a `topological_vector_prebundle`.  Concretely this means
that, given a `topological_vector_prebundle` structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`topological_vector_prebundle.total_space_topology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
def to_topological_vector_bundle :
  @topological_vector_bundle R _ F E _ _ _ _ _ _ a.total_space_topology a.fiber_topology :=
{ total_space_mk_inducing := a.inducing_total_space_mk,
  trivialization_atlas := {e | ∃ e₀ (he₀ : e₀ ∈ a.pretrivialization_atlas),
    e = a.trivialization_of_mem_pretrivialization_atlas he₀},
  trivialization_linear' := begin
    rintros _ ⟨e, he, rfl⟩,
    apply linear_of_mem_pretrivialization_atlas,
  end,
  trivialization_at := λ x, a.trivialization_of_mem_pretrivialization_atlas
    (a.pretrivialization_mem_atlas x),
  mem_base_set_trivialization_at := a.mem_base_pretrivialization_at,
  trivialization_mem_atlas := λ x, ⟨_, a.pretrivialization_mem_atlas x, rfl⟩,
  continuous_on_coord_change' := begin
    rintros _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩,
    refine (a.continuous_on_coord_change he he').congr _,
    intros b hb,
    ext v,
    rw [a.coord_change_apply he he' hb v, continuous_linear_equiv.coe_coe,
      trivialization.coord_changeL_apply],
    exacts [rfl, hb]
  end }

end topological_vector_prebundle

end
