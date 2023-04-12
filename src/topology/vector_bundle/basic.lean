/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sebastien Gouezel, Heather Macbeth, Patrick Massot, Floris van Doorn
-/

import analysis.normed_space.bounded_linear_maps
import topology.fiber_bundle.basic

/-!
# Vector bundles

In this file we define (topological) vector bundles.

Let `B` be the base space, let `F` be a normed space over a normed field `R`, and let
`E : B → Type*` be a `fiber_bundle` with fiber `F`, in which, for each `x`, the fiber `E x` is a
topological vector space over `R`.

To have a vector bundle structure on `bundle.total_space E`, one should additionally have the
following properties:

* The bundle trivializations in the trivialization atlas should be continuous linear equivs in the
fibers;
* For any two trivializations `e`, `e'` in the atlas the transition function considered as a map
from `B` into `F →L[R] F` is continuous on `e.base_set ∩ e'.base_set` with respect to the operator
norm topology on `F →L[R] F`.

If these conditions are satisfied, we register the typeclass `vector_bundle R F E`.

We define constructions on vector bundles like pullbacks and direct sums in other files.

## Implementation notes

The implementation choices in the vector bundle definition are discussed in the "Implementation
notes" section of `topology.fiber_bundle.basic`.

## Tags
Vector bundle
-/

noncomputable theory

open bundle set
open_locale classical bundle

variables (R 𝕜 : Type*) {B : Type*} (F : Type*) (E : B → Type*)

section

namespace bundle

/-- The zero section of a vector bundle -/
def zero_section [∀ x, has_zero (E x)] : B → total_space E :=
λ x, total_space_mk x 0

@[simp, mfld_simps]
lemma zero_section_proj [∀ x, has_zero (E x)] (x : B) : (zero_section E x).proj = x := rfl
@[simp, mfld_simps]
lemma zero_section_snd [∀ x, has_zero (E x)] (x : B) : (zero_section E x).2 = 0 := rfl

end bundle
open bundle

section topological_vector_space
variables {B F E} [semiring R] [topological_space F]  [topological_space B]
variables [add_comm_monoid F] [module R F] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]

/-- A mixin class for `pretrivialization`, stating that a pretrivialization is fiberwise linear with
respect to given module structures on its fibers and the model fiber.

We require linearity even outside the base set (also for the inverse). This makes operations like
`pretrivialization.symmₗ` and `pretrivialization.linear_map_at` simpler and easier to work with.
This is not really an extra condition, since we can set the value of `e` fiberwise to `0` outside
the base set. -/
protected class pretrivialization.is_linear (e : pretrivialization F (π E)) :
  Prop :=
(linear : ∀ b ∈ e.base_set, is_linear_map R (λ x : E b, (e (total_space_mk b x)).2))
(eq_zero : ∀ (b ∉ e.base_set) (x : E b), (e (total_space_mk b x)).2 = 0)
(symm_eq_zero : ∀ (b ∉ e.base_set) (x : F), e.symm b x = 0)

namespace pretrivialization

variables {F E} (e : pretrivialization F (π E)) {x : total_space E} {b : B} {y : E b}

lemma eq_zero [e.is_linear R] {b : B} (hb : b ∉ e.base_set) (x : E b) :
  (e (total_space_mk b x)).2 = 0 :=
pretrivialization.is_linear.eq_zero R b hb x

lemma symm_eq_zero [e.is_linear R] {b : B} (hb : b ∉ e.base_set) (x : F) :
  e.symm b x = 0 :=
pretrivialization.is_linear.symm_eq_zero R b hb x

lemma linear [e.is_linear R] (b : B) :
  is_linear_map R (λ x : E b, (e (total_space_mk b x)).2) :=
begin
  by_cases hb : b ∈ e.base_set,
  { exact pretrivialization.is_linear.linear b hb },
  { convert (0 : E b →ₗ[R] F).is_linear, ext x, rw [e.eq_zero R hb, linear_map.zero_apply] }
end

lemma linear_symm [e.is_linear R] (b : B) :
  is_linear_map R (e.symm b) :=
begin
  by_cases hb : b ∈ e.base_set,
  { exact (((e.linear R b).mk' _).inverse (e.symm b) (e.symm_apply_apply_mk hb)
      (λ v, congr_arg prod.snd $ e.apply_mk_symm hb v)).is_linear },
  { convert (0 : F →ₗ[R] E b).is_linear, ext x, rw [e.symm_eq_zero R hb, linear_map.zero_apply] }
end

/-- A fiberwise linear inverse to `e`. -/
@[simps] protected def symmₗ (e : pretrivialization F (π E)) [e.is_linear R] (b : B) :
  F →ₗ[R] E b :=
is_linear_map.mk' (e.symm b) (e.linear_symm R b)

/-- A pretrivialization for a vector bundle defines linear equivalences between the
fibers and the model space. -/
@[simps {fully_applied := ff}] def linear_equiv_at (e : pretrivialization F (π E)) [e.is_linear R]
  (b : B) (hb : b ∈ e.base_set) :
  E b ≃ₗ[R] F :=
{ to_fun := λ y, (e (total_space_mk b y)).2,
  inv_fun := e.symm b,
  left_inv := e.symm_apply_apply_mk hb,
  right_inv := λ v, by simp_rw [e.apply_mk_symm hb v],
  map_add' := λ v w, (e.linear R b).map_add v w,
  map_smul' := λ c v, (e.linear R b).map_smul c v }

/-- A fiberwise linear map equal to `e` on `e.base_set`. -/
protected def linear_map_at (e : pretrivialization F (π E)) [e.is_linear R] (b : B) : E b →ₗ[R] F :=
is_linear_map.mk' (λ y, (e (total_space_mk b y)).2) (e.linear R b)

variables {R}

lemma linear_map_at_apply (e : pretrivialization F (π E)) [e.is_linear R] (b : B) (y : E b) :
  e.linear_map_at R b y = (e (total_space_mk b y)).2 :=
rfl

lemma symmₗ_linear_map_at (e : pretrivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∈ e.base_set) (y : E b) : e.symmₗ R b (e.linear_map_at R b y) = y :=
(e.linear_equiv_at R b hb).left_inv y

lemma linear_map_at_symmₗ (e : pretrivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∈ e.base_set) (y : F) : e.linear_map_at R b (e.symmₗ R b y) = y :=
(e.linear_equiv_at R b hb).right_inv y

end pretrivialization

variables (R) [topological_space (total_space E)] [∀ x, topological_space (E x)]

/-- A mixin class for `trivialization`, stating that a trivialization is fiberwise linear with
respect to given module structures on its fibers and the model fiber.

We require that the trivialization is a fiberwise continuous linear map even outside the base set
(also for the inverse). This makes operations like `trivialization.symmL` and
`trivialization.continuous_linear_map_at` simpler and easier to work with.
This is not really an extra condition, since we can set the value of `e` fiberwise to `0` outside
the base set. See `trivialization.of_linear_and_zero` for this result. -/
protected class trivialization.is_linear (e : trivialization F (π E)) : Prop :=
(linear : ∀ b, is_linear_map R (λ x : E b, (e (total_space_mk b x)).2))
(linear_symm : ∀ b, is_linear_map R (e.symm b))
(continuous : ∀ b, continuous (λ x : E b, (e (total_space_mk b x)).2))
(continuous_symm : ∀ b, _root_.continuous (e.symm b))

namespace trivialization

variables (e : trivialization F (π E)) {x : total_space E} {b : B} {y : E b}

protected lemma linear [e.is_linear R] (b : B) :
  is_linear_map R (λ y : E b, (e (total_space_mk b y)).2) :=
trivialization.is_linear.linear b

lemma linear_symm [e.is_linear R] (b : B) : is_linear_map R (e.symm b) :=
trivialization.is_linear.linear_symm b

protected lemma continuous [e.is_linear R] (b : B) :
  continuous (λ y : E b, (e (total_space_mk b y)).2) :=
trivialization.is_linear.continuous R b

lemma continuous_symm [e.is_linear R] (b : B) : continuous (e.symm b) :=
trivialization.is_linear.continuous_symm R b

instance to_pretrivialization.is_linear [e.is_linear R] : e.to_pretrivialization.is_linear R :=
{ ..(‹_› : e.is_linear R) }

/-- A trivialization for a vector bundle defines linear equivalences between the
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

lemma linear_map_at_apply (e : trivialization F (π E)) [e.is_linear R] (b : B) (y : E b) :
  e.linear_map_at R b y = (e (total_space_mk b y)).2 :=
rfl

lemma symmₗ_linear_map_at (e : trivialization F (π E)) [e.is_linear R] {b : B} (hb : b ∈ e.base_set)
  (y : E b) :
  e.symmₗ R b (e.linear_map_at R b y) = y :=
e.to_pretrivialization.symmₗ_linear_map_at hb y

lemma linear_map_at_symmₗ (e : trivialization F (π E)) [e.is_linear R] {b : B} (hb : b ∈ e.base_set)
  (y : F) :
  e.linear_map_at R b (e.symmₗ R b y) = y :=
e.to_pretrivialization.linear_map_at_symmₗ hb y

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

lemma coe_coord_changeL' (e e' : trivialization F (π E)) [e.is_linear R] [e'.is_linear R] {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) :
  (coord_changeL R e e' b).to_linear_equiv
  = (e.linear_equiv_at R b hb.1).symm.trans (e'.linear_equiv_at R b hb.2) :=
linear_equiv.coe_injective (coe_coord_changeL _ _ _)

lemma symm_coord_changeL (e e' : trivialization F (π E)) [e.is_linear R] [e'.is_linear R] {b : B}
  (hb : b ∈ e'.base_set ∩ e.base_set) :
  (e.coord_changeL R e' b).symm = e'.coord_changeL R e b :=
begin
  apply continuous_linear_equiv.to_linear_equiv_injective,
  rw [coe_coord_changeL' e' e hb, (coord_changeL R e e' b).symm_to_linear_equiv,
    coe_coord_changeL' e e' hb.symm, linear_equiv.trans_symm, linear_equiv.symm_symm],
end

lemma coord_changeL_apply (e e' : trivialization F (π E)) [e.is_linear R] [e'.is_linear R] {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  coord_changeL R e e' b y = (e' (total_space_mk b (e.symm b y))).2 :=
congr_arg (λ f, linear_equiv.to_fun f y) (dif_pos hb)

lemma mk_coord_changeL (e e' : trivialization F (π E)) [e.is_linear R] [e'.is_linear R] {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  (b, coord_changeL R e e' b y) = e' (total_space_mk b (e.symm b y)) :=
begin
  ext,
  { rw [e.mk_symm, e'.coe_fst, e.proj_symm_apply'] },
  { exact e.coord_changeL_apply e' hb y }
end

lemma apply_symm_apply_eq_coord_changeL (e e' : trivialization F (π E)) [e.is_linear R]
  [e'.is_linear R] {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) (v : F) :
  e' (e.to_local_homeomorph.symm (b, v)) = (b, e.coord_changeL R e' b v) :=
by rw [e.mk_coord_changeL e' hb, e.mk_symm]

/-- A version of `coord_change_apply` that fully unfolds `coord_change`. The right-hand side is
ugly, but has good definitional properties for specifically defined trivializations. -/
lemma coord_changeL_apply' (e e' : trivialization F (π E)) [e.is_linear R] [e'.is_linear R] {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  coord_changeL R e e' b y = (e' (e.to_local_homeomorph.symm (b, y))).2 :=
by rw [e.coord_changeL_apply e' hb, e.mk_symm]

lemma coord_changeL_symm_apply (e e' : trivialization F (π E)) [e.is_linear R] [e'.is_linear R]
  {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) :
  ⇑(coord_changeL R e e' b).symm
  = (e'.linear_equiv_at R b hb.2).symm.trans (e.linear_equiv_at R b hb.1) :=
congr_arg linear_equiv.inv_fun (dif_pos hb)

variables (R)

/-- Forward map of `continuous_linear_equiv_at` (only propositionally equal),
  defined everywhere (`0` outside domain). -/
@[simps apply {fully_applied := ff}]
def continuous_linear_map_at (e : trivialization F (π E)) [e.is_linear R] (b : B) :
  E b →L[R] F :=
{ to_fun := e.linear_map_at R b, -- given explicitly to help `simps`
  cont := e.continuous R b,
  .. e.linear_map_at R b }

/-- Backwards map of `continuous_linear_equiv_at`, defined everywhere. -/
@[simps apply {fully_applied := ff}]
def symmL (e : trivialization F (π E)) [e.is_linear R] (b : B) : F →L[R] E b :=
{ to_fun := e.symm b, -- given explicitly to help `simps`
  cont := e.continuous_symm R b,
  .. e.symmₗ R b }

variables {R}

lemma symmL_continuous_linear_map_at (e : trivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∈ e.base_set) (y : E b) :
  e.symmL R b (e.continuous_linear_map_at R b y) = y :=
e.symmₗ_linear_map_at R hb y

lemma continuous_linear_map_at_symmL (e : trivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∈ e.base_set) (y : F) :
  e.continuous_linear_map_at R b (e.symmL R b y) = y :=
e.linear_map_at_symmₗ R hb y

variables (R)

/-- In a vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
@[simps apply symm_apply {fully_applied := ff}]
def continuous_linear_equiv_at (e : trivialization F (π E)) [e.is_linear R] (b : B)
  (hb : b ∈ e.base_set) : E b ≃L[R] F :=
{ to_fun := λ y, (e (total_space_mk b y)).2, -- given explicitly to help `simps`
  inv_fun := e.symm b, -- given explicitly to help `simps`
  continuous_to_fun := e.continuous R b,
  continuous_inv_fun := e.continuous_symm R b,
  .. e.to_pretrivialization.linear_equiv_at R b hb }

variables {R}

lemma coe_continuous_linear_equiv_at_eq (e : trivialization F (π E)) [e.is_linear R] {b : B}
  (hb : b ∈ e.base_set) :
  (e.continuous_linear_equiv_at R b hb : E b → F) = e.continuous_linear_map_at R b :=
rfl

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
  e ⟨b, z⟩ = (b, e.continuous_linear_equiv_at R b hb z) :=
begin
  ext,
  { exact e.coe_fst _ },
  { simp only [coe_coe, continuous_linear_equiv_at_apply] }
end

protected lemma zero_section (e : trivialization F (π E)) [e.is_linear R]
  {x : B} (hx : x ∈ e.base_set) : e (zero_section E x) = (x, 0) :=
by simp_rw [zero_section, total_space_mk, e.apply_eq_prod_continuous_linear_equiv_at R x hx 0,
  map_zero]

variables {R}

lemma symm_apply_eq_mk_continuous_linear_equiv_at_symm (e : trivialization F (π E)) [e.is_linear R]
  (b : B) (hb : b ∈ e.base_set) (z : F) :
  e.to_local_homeomorph.symm ⟨b, z⟩
  = total_space_mk b ((e.continuous_linear_equiv_at R b hb).symm z) :=
begin
  have h : (b, z) ∈ e.target,
  { rw e.target_eq,
    exact ⟨hb, mem_univ _⟩ },
  apply e.inj_on (e.map_target h),
  { simp only [e.source_eq, hb, mem_preimage] },
  simp_rw [e.right_inv h, coe_coe, e.apply_eq_prod_continuous_linear_equiv_at R b hb,
    continuous_linear_equiv.apply_symm_apply],
end

lemma comp_continuous_linear_equiv_at_eq_coord_change (e e' : trivialization F (π E))
  [e.is_linear R] [e'.is_linear R] {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) :
  (e.continuous_linear_equiv_at R b hb.1).symm.trans (e'.continuous_linear_equiv_at R b hb.2)
  = coord_changeL R e e' b :=
by { ext v, rw [coord_changeL_apply e e' hb], refl }


lemma of_linear_and_zero [fiber_bundle F E] (e : trivialization F (π E))
  (h1 : ∀ b ∈ e.base_set, is_linear_map R (λ x : E b, (e (total_space_mk b x)).2))
  (h2 : ∀ (b ∉ e.base_set) (x : E b), (e (total_space_mk b x)).2 = 0)
  (h3 : ∀ (b ∉ e.base_set) (x : F), (e.to_local_homeomorph.symm (b, x)).2 = 0) : e.is_linear R :=
have this : ∀ (x y : B) (p : x = y), cast (congr_arg E p) 0 = 0,
by { intros x y p, induction p, refl },
have h3 : ∀ (b ∉ e.base_set), e.symm b = 0,
by { intros b hb, ext x, rw [e.symm_apply, h3 b hb, this, pi.zero_apply] },
{ linear := λ b, by {
    by_cases hb : b ∈ e.base_set,
    { exact h1 b hb },
    { simp_rw [h2 b hb], exact (0 : E b →ₗ[R] F).is_linear } },
  linear_symm := λ b, by {
    by_cases hb : b ∈ e.base_set,
    { refine (((h1 b hb).mk' _).inverse (e.symm b) (e.symm_apply_apply_mk hb) _).is_linear,
      exact λ x, congr_arg prod.snd (e.apply_mk_symm hb x) },
    { simp_rw [h3 b hb], exact (0 : F →ₗ[R] E b).is_linear } },
  continuous := λ b, by {
    by_cases hb : b ∈ e.base_set,
    { exact continuous_snd.comp (e.continuous_on.comp_continuous
        (fiber_bundle.total_space_mk_inducing F E b).continuous
        (λ x, e.mem_source.mpr hb)) },
    { simp_rw [h2 b hb], exact continuous_const } },
  continuous_symm := λ b, by {
    by_cases hb : b ∈ e.base_set,
    { rw (fiber_bundle.total_space_mk_inducing F E b).continuous_iff,
      exact e.continuous_on_symm.comp_continuous (continuous_const.prod_mk continuous_id)
        (λ x, mk_mem_prod hb (mem_univ x)) },
    { simp_rw [h3 b hb], exact continuous_zero } }, }

end trivialization

end topological_vector_space

variables [nontrivially_normed_field R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
  [normed_add_comm_group F] [normed_space R F] [topological_space B]
  [topological_space (total_space E)] [∀ x, topological_space (E x)] [fiber_bundle F E]

/-- The space `total_space E` (for `E : B → Type*` such that each `E x` is a topological vector
space) has a topological vector space structure with fiber `F` (denoted with
`vector_bundle R F E`) if around every point there is a fiber bundle trivialization
which is linear in the fibers. -/
class vector_bundle : Prop :=
(trivialization_linear' : ∀ (e : trivialization F (π E)) [mem_trivialization_atlas e],
  e.is_linear R)
(continuous_on_coord_change' [] : ∀ (e e' : trivialization F (π E)) [mem_trivialization_atlas e]
  [mem_trivialization_atlas e'],
  continuous_on
  (λ b, by exactI trivialization.coord_changeL R e e' b : B → F →L[R] F) (e.base_set ∩ e'.base_set))

variables {F E}

@[priority 100]
instance trivialization_linear [vector_bundle R F E] (e : trivialization F (π E))
  [mem_trivialization_atlas e] :
  e.is_linear R :=
vector_bundle.trivialization_linear' e

lemma continuous_on_coord_change [vector_bundle R F E] (e e' : trivialization F (π E))
  [he : mem_trivialization_atlas e]
  [he' : mem_trivialization_atlas e'] :
  continuous_on
  (λ b, trivialization.coord_changeL R e e' b : B → F →L[R] F) (e.base_set ∩ e'.base_set) :=
vector_bundle.continuous_on_coord_change' R e e'

include R F

/-! ### Constructing vector bundles -/

variables (R B F)

/-- Analogous construction of `fiber_bundle_core` for vector bundles. This
construction gives a way to construct vector bundles from a structure registering how
trivialization changes act on fibers. -/
structure vector_bundle_core (ι : Type*) :=
(base_set          : ι → set B)
(is_open_base_set  : ∀ i, is_open (base_set i))
(index_at          : B → ι)
(mem_base_set_at   : ∀ x, x ∈ base_set (index_at x))
(coord_change      : ι → ι → B → F →L[R] F)
(coord_change_self : ∀ i, ∀ x ∈ base_set i, ∀ v, coord_change i i x v = v)
(continuous_on_coord_change : ∀ i j, continuous_on (coord_change i j) (base_set i ∩ base_set j))
(coord_change_comp : ∀ i j k, ∀ x ∈ (base_set i) ∩ (base_set j) ∩ (base_set k), ∀ v,
  (coord_change j k x) (coord_change i j x v) = coord_change i k x v)

/-- The trivial vector bundle core, in which all the changes of coordinates are the
identity. -/
def trivial_vector_bundle_core (ι : Type*) [inhabited ι] :
  vector_bundle_core R B F ι :=
{ base_set := λ ι, univ,
  is_open_base_set := λ i, is_open_univ,
  index_at := default,
  mem_base_set_at := λ x, mem_univ x,
  coord_change := λ i j x, continuous_linear_map.id R F,
  coord_change_self := λ i x hx v, rfl,
  coord_change_comp := λ i j k x hx v, rfl,
  continuous_on_coord_change := λ i j, continuous_on_const }

instance (ι : Type*) [inhabited ι] : inhabited (vector_bundle_core R B F ι) :=
⟨trivial_vector_bundle_core R B F ι⟩

namespace vector_bundle_core

variables {R B F} {ι : Type*} (Z : vector_bundle_core R B F ι)

/-- Natural identification to a `fiber_bundle_core`. -/
@[simps (mfld_cfg)] def to_fiber_bundle_core : fiber_bundle_core ι B F :=
{ coord_change := λ i j b, Z.coord_change i j b,
  continuous_on_coord_change := λ i j, is_bounded_bilinear_map_apply.continuous.comp_continuous_on
      ((Z.continuous_on_coord_change i j).prod_map continuous_on_id),
  ..Z }

instance to_fiber_bundle_core_coe : has_coe (vector_bundle_core R B F ι)
  (fiber_bundle_core ι B F) := ⟨to_fiber_bundle_core⟩

include Z

lemma coord_change_linear_comp (i j k : ι): ∀ x ∈ (Z.base_set i) ∩ (Z.base_set j) ∩ (Z.base_set k),
  (Z.coord_change j k x).comp (Z.coord_change i j x) = Z.coord_change i k x :=
λ x hx, by { ext v, exact Z.coord_change_comp i j k x hx v }

/-- The index set of a vector bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments has_nonempty_instance]
def index := ι

/-- The base space of a vector bundle core, as a convenience function for dot notation-/
@[nolint unused_arguments, reducible]
def base := B

/-- The fiber of a vector bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_nonempty_instance]
def fiber : B → Type* := Z.to_fiber_bundle_core.fiber

instance topological_space_fiber (x : B) : topological_space (Z.fiber x) :=
by delta_instance vector_bundle_core.fiber
instance add_comm_monoid_fiber : ∀ (x : B), add_comm_monoid (Z.fiber x) :=
by dsimp [vector_bundle_core.fiber]; delta_instance fiber_bundle_core.fiber
instance module_fiber : ∀ (x : B), module R (Z.fiber x) :=
by dsimp [vector_bundle_core.fiber];  delta_instance fiber_bundle_core.fiber
instance add_comm_group_fiber [add_comm_group F] : ∀ (x : B), add_comm_group (Z.fiber x) :=
by dsimp [vector_bundle_core.fiber];  delta_instance fiber_bundle_core.fiber

/-- The projection from the total space of a fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps] def proj : total_space Z.fiber → B := total_space.proj

/-- The total space of the vector bundle, as a convenience function for dot notation.
It is by definition equal to `bundle.total_space Z.fiber`, a.k.a. `Σ x, Z.fiber x` but with a
different name for typeclass inference. -/
@[nolint unused_arguments, reducible]
def total_space := bundle.total_space Z.fiber

/-- Local homeomorphism version of the trivialization change. -/
def triv_change (i j : ι) : local_homeomorph (B × F) (B × F) :=
fiber_bundle_core.triv_change ↑Z i j

@[simp, mfld_simps] lemma mem_triv_change_source (i j : ι) (p : B × F) :
  p ∈ (Z.triv_change i j).source ↔ p.1 ∈ Z.base_set i ∩ Z.base_set j :=
fiber_bundle_core.mem_triv_change_source ↑Z i j p

/-- Topological structure on the total space of a vector bundle created from core, designed so
that all the local trivialization are continuous. -/
instance to_topological_space : topological_space Z.total_space :=
Z.to_fiber_bundle_core.to_topological_space

instance fiber_bundle : fiber_bundle F Z.fiber := Z.to_fiber_bundle_core.fiber_bundle

variables (b : B) (a : F)

@[simp, mfld_simps] lemma coe_coord_change (i j : ι) :
  Z.to_fiber_bundle_core.coord_change i j b = Z.coord_change i j b := rfl

/-- One of the standard local trivializations of a vector bundle constructed from core, taken by
considering this in particular as a fiber bundle constructed from core. -/
def local_triv (i : ι) : trivialization F (π Z.fiber) :=
by exact Z.to_fiber_bundle_core.local_triv i

/-- The standard local trivializations of a vector bundle constructed from core are linear. -/
instance local_triv.is_linear (i : ι) : (Z.local_triv i).is_linear R :=
{ linear := λ x, (Z.coord_change (Z.index_at x) i x).is_linear,
  linear_symm := sorry, -- λ x, (Z.coord_change (Z.index_at x) i x).is_linear,
  continuous := λ x, (Z.coord_change (Z.index_at x) i x).continuous,
  continuous_symm := λ x, sorry }

variables (i j : ι)

@[simp, mfld_simps] lemma mem_local_triv_source (p : Z.total_space) :
  p ∈ (Z.local_triv i).source ↔ p.1 ∈ Z.base_set i :=
by dsimp [vector_bundle_core.fiber]; exact iff.rfl

@[simp, mfld_simps] lemma base_set_at : Z.base_set i = (Z.local_triv i).base_set := rfl

@[simp, mfld_simps] lemma local_triv_apply (p : Z.total_space) :
  (Z.local_triv i) p = ⟨p.1, Z.coord_change (Z.index_at p.1) i p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma mem_local_triv_target (p : B × F) :
  p ∈ (Z.local_triv i).target ↔ p.1 ∈ (Z.local_triv i).base_set :=
Z.to_fiber_bundle_core.mem_local_triv_target i p

@[simp, mfld_simps] lemma local_triv_symm_fst (p : B × F) :
  (Z.local_triv i).to_local_homeomorph.symm p =
    ⟨p.1, Z.coord_change i (Z.index_at p.1) p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma local_triv_symm_apply (b : B) (v : F) :
  (Z.local_triv i).symm b v = Z.coord_change i (Z.index_at b) b v :=
by apply (Z.local_triv i).symm_apply b v

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
fiber_bundle_core.local_triv_at_apply Z p

@[simp, mfld_simps] lemma local_triv_at_apply_mk (b : B) (a : F) :
  ((Z.local_triv_at b) ⟨b, a⟩) = ⟨b, a⟩ :=
Z.local_triv_at_apply _

@[simp, mfld_simps] lemma mem_local_triv_at_base_set :
  b ∈ (Z.local_triv_at b).base_set :=
fiber_bundle_core.mem_local_triv_at_base_set Z b

instance vector_bundle : vector_bundle R F Z.fiber :=
{ trivialization_linear' := begin
    rintros _ ⟨i, rfl⟩,
    apply local_triv.is_linear,
  end,
  continuous_on_coord_change' := begin
    rintros _ _ ⟨i, rfl⟩ ⟨i', rfl⟩,
    refine (Z.continuous_on_coord_change i i').congr (λ b hb, _),
    ext v,
    exact Z.local_triv_coord_change_eq i i' hb v,
  end }

/-- The projection on the base of a vector bundle created from core is continuous -/
@[continuity] lemma continuous_proj : continuous Z.proj :=
fiber_bundle_core.continuous_proj Z

/-- The projection on the base of a vector bundle created from core is an open map -/
lemma is_open_map_proj : is_open_map Z.proj :=
fiber_bundle_core.is_open_map_proj Z

end vector_bundle_core

end

/-! ### Vector prebundle -/

section
variables [nontrivially_normed_field R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
  [normed_add_comm_group F] [normed_space R F] [topological_space B]

open topological_space

open vector_bundle
/-- This structure permits to define a vector bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space or the fibers.
The total space is hence given a topology in such a way that there is a fiber bundle structure for
which the local equivalences are also local homeomorphisms and hence vector bundle trivializations.
The topology on the fibers is induced from the one on the total space.

The field `exists_coord_change` is stated as an existential statement (instead of 3 separate
fields), since it depends on propositional information (namely `e e' ∈ pretrivialization_atlas`).
This makes it inconvenient to explicitly define a `coord_change` function when constructing a
`vector_prebundle`. -/
@[nolint has_nonempty_instance]
structure vector_prebundle :=
(pretrivialization_atlas : set (pretrivialization F (π E)))
(pretrivialization_linear : ∀ (e : pretrivialization F (π E)) (he : e ∈ pretrivialization_atlas),
  e.is_linear R)
(pretrivialization_at : B → pretrivialization F (π E))
(mem_base_pretrivialization_at : ∀ x : B, x ∈ (pretrivialization_at x).base_set)
(pretrivialization_mem_atlas : ∀ x : B, pretrivialization_at x ∈ pretrivialization_atlas)
(exists_coord_change : ∀ (e e' ∈ pretrivialization_atlas), ∃ f : B → F →L[R] F,
  continuous_on f (e.base_set ∩ e'.base_set) ∧
  ∀ (b : B) (hb : b ∈ e.base_set ∩ e'.base_set) (v : F),
    f b v = (e' (total_space_mk b (e.symm b v))).2)

namespace vector_prebundle

variables {R E F} (a : vector_prebundle R F E) {e e' : pretrivialization F (π E)}


/-- A randomly chosen coordinate change on a `vector_prebundle`, given by
  the field `exists_coord_change`. -/
def coord_change (he : e ∈ a.pretrivialization_atlas)
  (he' : e' ∈ a.pretrivialization_atlas) (b : B) : F →L[R] F :=
classical.some (a.exists_coord_change e he e' he') b

lemma continuous_on_coord_change (he : e ∈ a.pretrivialization_atlas)
  (he' : e' ∈ a.pretrivialization_atlas) :
  continuous_on (a.coord_change he he') (e.base_set ∩ e'.base_set) :=
(classical.some_spec (a.exists_coord_change e he e' he')).1

lemma coord_change_apply (he : e ∈ a.pretrivialization_atlas)
  (he' : e' ∈ a.pretrivialization_atlas) {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) (v : F) :
  a.coord_change he he' b v = (e' (total_space_mk b (e.symm b v))).2 :=
(classical.some_spec (a.exists_coord_change e he e' he')).2 b hb v

lemma mk_coord_change (he : e ∈ a.pretrivialization_atlas)
  (he' : e' ∈ a.pretrivialization_atlas) {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) (v : F) :
  (b, a.coord_change he he' b v) = e' (total_space_mk b (e.symm b v)) :=
begin
  ext,
  { rw [e.mk_symm b v, e'.coe_fst, e.proj_symm_apply'] },
  { exact a.coord_change_apply he he' hb v }
end

/-- Natural identification of `vector_prebundle` as a `fiber_prebundle`. -/
def to_fiber_prebundle : fiber_prebundle F E :=
{ continuous_triv_change := begin
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
    rw [a.mk_coord_change _ _ hb, e'.mk_symm],
    refl,
  end,
  .. a }

/-- Topology on the total space that will make the prebundle into a bundle. -/
def total_space_topology : topological_space (total_space E) :=
a.to_fiber_prebundle.total_space_topology

/-- Topology on the fibers `E b` induced by the map `E b → E.total_space`. -/
def fiber_topology (b : B) : topological_space (E b) :=
a.to_fiber_prebundle.fiber_topology b

/-- Promotion from a `trivialization` in the `pretrivialization_atlas` of a
`vector_prebundle` to a `trivialization`. -/
def trivialization_of_mem_pretrivialization_atlas (a : vector_prebundle R F E)
  {e : pretrivialization F (π E)} (he : e ∈ a.pretrivialization_atlas) :
  @trivialization B F _ _ _ a.total_space_topology (π E) :=
a.to_fiber_prebundle.trivialization_of_mem_pretrivialization_atlas he

lemma linear_of_mem_pretrivialization_atlas (a : vector_prebundle R F E)
  {e : pretrivialization F (π E)} (he : e ∈ a.pretrivialization_atlas) :
  @trivialization.is_linear R B F _ _ _ _ _ _ _ _ a.total_space_topology a.fiber_topology
    (trivialization_of_mem_pretrivialization_atlas a he) :=
{ linear := (a.pretrivialization_linear e he).linear,
  linear_symm := (a.pretrivialization_linear e he).linear_symm,
  continuous := λ b, sorry, -- not true
  continuous_symm := λ b, sorry } -- not true


lemma mem_trivialization_at_source (b : B) (x : E b) :
  total_space_mk b x ∈ (a.pretrivialization_at b).source :=
a.to_fiber_prebundle.mem_trivialization_at_source b x

@[simp] lemma total_space_mk_preimage_source (b : B) :
  (total_space_mk b) ⁻¹' (a.pretrivialization_at b).source = univ :=
a.to_fiber_prebundle.total_space_mk_preimage_source b

@[continuity] lemma inducing_total_space_mk (b : B) :
  @inducing _ _ (a.fiber_topology b) a.total_space_topology (total_space_mk b) :=
a.to_fiber_prebundle.inducing_total_space_mk b

@[continuity] lemma continuous_total_space_mk (b : B) :
  @continuous _ _ (a.fiber_topology b) a.total_space_topology (total_space_mk b) :=
a.to_fiber_prebundle.continuous_total_space_mk b

/-- Make a `fiber_bundle` from a `vector_prebundle`; auxiliary construction for
`vector_prebundle.vector_bundle`. -/
def to_fiber_bundle : @fiber_bundle B F _ _ _ a.total_space_topology a.fiber_topology :=
a.to_fiber_prebundle.to_fiber_bundle

/-- Make a `vector_bundle` from a `vector_prebundle`.  Concretely this means
that, given a `vector_prebundle` structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`vector_prebundle.total_space_topology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
lemma to_vector_bundle :
  @vector_bundle R _ F E _ _ _ _ _ _ a.total_space_topology a.fiber_topology a.to_fiber_bundle :=
{ trivialization_linear' := begin
    rintros _ ⟨e, he, rfl⟩,
    apply linear_of_mem_pretrivialization_atlas,
  end,
  continuous_on_coord_change' := begin
    rintros _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩,
    refine (a.continuous_on_coord_change he he').congr _,
    intros b hb,
    ext v,
    rw [a.coord_change_apply he he' hb v, continuous_linear_equiv.coe_coe,
      trivialization.coord_changeL_apply],
    exacts [rfl, hb]
  end }

end vector_prebundle

end
