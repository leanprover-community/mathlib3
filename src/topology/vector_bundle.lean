/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sebastien Gouezel, Heather Macbeth, Patrick Massot
-/

import analysis.normed_space.bounded_linear_maps
import topology.fiber_bundle
import topology.continuous_function.basic

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
bundle structure, `bundle.prod.topological_vector_bundle`.  Similarly we construct the pullback
bundle for a map `f : B' → B` whose fiber map is given simply by `f *ᵖ E = E ∘ f` (the type synonym
is there for typeclass instance problems).

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
open_locale classical

variables (R 𝕜 : Type*) {B : Type*} (F : Type*) (E : B → Type*)

section topological_vector_space
variables [semiring R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
  [topological_space F] [add_comm_monoid F] [module R F] [topological_space B]

/-- A pretrivialization for a (yet to be defined) topological vector bundle `total_space E` is a
local equiv between sets of the form `proj ⁻¹' base_set` and `base_set × F` which respects the
first coordinate, and is linear in each fiber. -/
@[nolint has_inhabited_instance]
structure topological_vector_bundle.pretrivialization extends to_fiber_bundle_pretrivialization :
  topological_fiber_bundle.pretrivialization F (@total_space.proj B E) :=
(linear' : ∀ x ∈ base_set, is_linear_map R (λ y : E x, (to_fun (total_space_mk x y)).2))

instance : has_coe_to_fun (topological_vector_bundle.pretrivialization R F E) _ := ⟨λ e, e.to_fun⟩

instance : has_coe (topological_vector_bundle.pretrivialization R F E)
  (topological_fiber_bundle.pretrivialization F (@total_space.proj B E)) :=
⟨topological_vector_bundle.pretrivialization.to_fiber_bundle_pretrivialization⟩

namespace topological_vector_bundle.pretrivialization

open topological_vector_bundle

variables {R F E} (e : pretrivialization R F E) {x : total_space E} {b : B} {y : E b}

protected lemma linear (hb : b ∈ e.base_set) :
  is_linear_map R (λ y : E b, (e (total_space_mk b y)).2) :=
e.linear' b hb

@[simp, mfld_simps] lemma coe_coe : ⇑e.to_local_equiv = e := rfl
@[simp, mfld_simps] lemma coe_fst (ex : x ∈ e.source) : (e x).1 = x.proj := e.proj_to_fun x ex
lemma mem_source : x ∈ e.source ↔ x.proj ∈ e.base_set := by rw [e.source_eq, mem_preimage]
lemma coe_mem_source : ↑y ∈ e.source ↔ b ∈ e.base_set := e.mem_source
lemma coe_fst' (ex : x.proj ∈ e.base_set) : (e x).1 = x.proj :=
e.coe_fst (e.mem_source.2 ex)

protected lemma eq_on : eq_on (prod.fst ∘ e) total_space.proj e.source := λ x hx, e.coe_fst hx
lemma mk_proj_snd (ex : x ∈ e.source) : (x.proj, (e x).2) = e x :=
prod.ext (e.coe_fst ex).symm rfl

@[simp, mfld_simps] lemma coe_coe_fst (hb : b ∈ e.base_set) : (e y).1 = b :=
e.coe_fst (e.mem_source.2 hb)

lemma mk_proj_snd' (ex : x.proj ∈ e.base_set) : (x.proj, (e x).2) = e x :=
prod.ext (e.coe_fst' ex).symm rfl

lemma mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.base_set :=
e.to_fiber_bundle_pretrivialization.mem_target

lemma mk_mem_target {x : B} {y : F} : (x, y) ∈ e.target ↔ x ∈ e.base_set :=
e.mem_target

lemma proj_symm_apply {x : B × F} (hx : x ∈ e.target) : (e.to_local_equiv.symm x).proj = x.1 :=
e.to_fiber_bundle_pretrivialization.proj_symm_apply hx

lemma proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) :
  (e.to_local_equiv.symm (b, x)).proj = b :=
e.proj_symm_apply (e.mem_target.2 hx)

lemma apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.to_local_equiv.symm x) = x :=
e.to_local_equiv.right_inv hx

lemma symm_apply_apply {x : total_space E} (hx : x ∈ e.source) : e.to_local_equiv.symm (e x) = x :=
e.to_local_equiv.left_inv hx

lemma apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) :
  e (e.to_local_equiv.symm (b, x)) = (b, x) :=
e.apply_symm_apply (e.mem_target.2 hx)

@[simp, mfld_simps] lemma symm_apply_mk_proj (ex : x ∈ e.source) :
  e.to_local_equiv.symm (x.proj, (e x).2) = x :=
by rw [← e.coe_fst ex, prod.mk.eta, ← e.coe_coe, e.to_local_equiv.left_inv ex]

@[simp, mfld_simps] lemma preimage_symm_proj_base_set :
  (e.to_local_equiv.symm ⁻¹' (total_space.proj ⁻¹' e.base_set)) ∩ e.target  = e.target :=
e.to_fiber_bundle_pretrivialization.preimage_symm_proj_base_set

lemma symm_coe_proj {x : B} {y : F} (e : pretrivialization R F E) (h : x ∈ e.base_set) :
  (e.to_local_equiv.symm (x, y)).1 = x :=
e.proj_symm_apply' h

/-- A fiberwise inverse to `e`. This is the function `F → E b` that induces a local inverse
`B × F → total_space E` of `e` on `e.base_set`. It is defined to be `0` outside `e.base_set`. -/
protected def symm (e : pretrivialization R F E) (b : B) (y : F) : E b :=
if hb : b ∈ e.base_set
then cast (congr_arg E (e.proj_symm_apply' hb)) (e.to_local_equiv.symm (b, y)).2
else 0

lemma symm_apply (e : pretrivialization R F E) {b : B} (hb : b ∈ e.base_set) (y : F) :
  e.symm b y = cast (congr_arg E (e.symm_coe_proj hb)) (e.to_local_equiv.symm (b, y)).2 :=
dif_pos hb

lemma symm_apply_of_not_mem (e : pretrivialization R F E) {b : B} (hb : b ∉ e.base_set) (y : F) :
  e.symm b y = 0 :=
dif_neg hb

lemma coe_symm_of_not_mem (e : pretrivialization R F E) {b : B} (hb : b ∉ e.base_set) :
  (e.symm b : F → E b) = 0 :=
funext $ λ y, dif_neg hb

lemma mk_symm (e : pretrivialization R F E) {b : B} (hb : b ∈ e.base_set) (y : F) :
  total_space_mk b (e.symm b y) = e.to_local_equiv.symm (b, y) :=
by rw [e.symm_apply hb, total_space.mk_cast, total_space.eta]

lemma symm_proj_apply (e : pretrivialization R F E) (z : total_space E)
  (hz : z.proj ∈ e.base_set) : e.symm z.proj (e z).2 = z.2 :=
by rw [e.symm_apply hz, cast_eq_iff_heq, e.mk_proj_snd' hz,
  e.symm_apply_apply (e.mem_source.mpr hz)]

lemma symm_apply_apply_mk (e : pretrivialization R F E) {b : B} (hb : b ∈ e.base_set) (y : E b) :
  e.symm b (e (total_space_mk b y)).2 = y :=
e.symm_proj_apply (total_space_mk b y) hb

lemma apply_mk_symm (e : pretrivialization R F E) {b : B} (hb : b ∈ e.base_set) (y : F) :
  e (total_space_mk b (e.symm b y)) = (b, y) :=
by rw [e.mk_symm hb, e.apply_symm_apply (e.mk_mem_target.mpr hb)]

/-- A fiberwise linear inverse to `e`. -/
@[simps] protected def symmₗ (e : pretrivialization R F E) (b : B) : F →ₗ[R] E b :=
begin
  refine is_linear_map.mk' (e.symm b) _,
  by_cases hb : b ∈ e.base_set,
  { exact (((e.linear hb).mk' _).inverse (e.symm b) (e.symm_apply_apply_mk hb)
      (λ v, congr_arg prod.snd $ e.apply_mk_symm hb v)).is_linear },
  { rw [e.coe_symm_of_not_mem hb], exact (0 : F →ₗ[R] E b).is_linear }
end

/-- A pretrivialization for a topological vector bundle defines linear equivalences between the
fibers and the model space. -/
@[simps {fully_applied := ff}] def linear_equiv_at (e : pretrivialization R F E) (b : B)
  (hb : b ∈ e.base_set) :
  E b ≃ₗ[R] F :=
{ to_fun := λ y, (e (total_space_mk b y)).2,
  inv_fun := e.symm b,
  left_inv := e.symm_apply_apply_mk hb,
  right_inv := λ v, by simp_rw [e.apply_mk_symm hb v],
  map_add' := λ v w, (e.linear hb).map_add v w,
  map_smul' := λ c v, (e.linear hb).map_smul c v }

/-- A fiberwise linear map equal to `e` on `e.base_set`. -/
protected def linear_map_at (e : pretrivialization R F E) (b : B) : E b →ₗ[R] F :=
if hb : b ∈ e.base_set then e.linear_equiv_at b hb else 0

lemma coe_linear_map_at (e : pretrivialization R F E) (b : B) :
  ⇑(e.linear_map_at b) = λ y, if b ∈ e.base_set then (e (total_space_mk b y)).2 else 0 :=
by { rw [pretrivialization.linear_map_at], split_ifs; refl }

lemma coe_linear_map_at_of_mem (e : pretrivialization R F E) {b : B} (hb : b ∈ e.base_set) :
  ⇑(e.linear_map_at b) = λ y, (e (total_space_mk b y)).2 :=
by simp_rw [coe_linear_map_at, if_pos hb]

lemma linear_map_at_apply (e : pretrivialization R F E) {b : B} (y : E b) :
  e.linear_map_at b y = if b ∈ e.base_set then (e (total_space_mk b y)).2 else 0 :=
by rw [coe_linear_map_at]

lemma linear_map_at_def_of_mem (e : pretrivialization R F E) {b : B} (hb : b ∈ e.base_set) :
  e.linear_map_at b = e.linear_equiv_at b hb :=
dif_pos hb

lemma linear_map_at_def_of_not_mem (e : pretrivialization R F E) {b : B} (hb : b ∉ e.base_set) :
  e.linear_map_at b = 0 :=
dif_neg hb

lemma linear_map_at_eq_zero (e : pretrivialization R F E) {b : B} (hb : b ∉ e.base_set) :
  e.linear_map_at b = 0 :=
dif_neg hb

lemma symmₗ_linear_map_at (e : pretrivialization R F E) {b : B} (hb : b ∈ e.base_set) (y : E b) :
  e.symmₗ b (e.linear_map_at b y) = y :=
by { rw [e.linear_map_at_def_of_mem hb], exact (e.linear_equiv_at b hb).left_inv y }

lemma linear_map_at_symmₗ (e : pretrivialization R F E) {b : B} (hb : b ∈ e.base_set) (y : F) :
  e.linear_map_at b (e.symmₗ b y) = y :=
by { rw [e.linear_map_at_def_of_mem hb], exact (e.linear_equiv_at b hb).right_inv y }


end topological_vector_bundle.pretrivialization

variable [topological_space (total_space E)]

/--
A structure extending local homeomorphisms, defining a local trivialization of the projection
`proj : total_space E → B` with fiber `F`, as a local homeomorphism between `total_space E`
and `B × F` defined between two sets of the form `proj ⁻¹' base_set` and `base_set × F`,
acting trivially on the first coordinate and linear in the fibers.
-/
@[nolint has_inhabited_instance]
structure topological_vector_bundle.trivialization extends to_fiber_bundle_trivialization :
  topological_fiber_bundle.trivialization F (@total_space.proj B E) :=
(linear' : ∀ x ∈ base_set, is_linear_map R (λ y : E x, (to_fun (total_space_mk x y)).2))

open topological_vector_bundle

instance : has_coe_to_fun (trivialization R F E) (λ _, total_space E → B × F) := ⟨λ e, e.to_fun⟩

instance : has_coe (trivialization R F E)
  (topological_fiber_bundle.trivialization F (@total_space.proj B E)) :=
⟨topological_vector_bundle.trivialization.to_fiber_bundle_trivialization⟩

namespace topological_vector_bundle.trivialization

variables {R F E} (e : trivialization R F E) {x : total_space E} {b : B} {y : E b}

/-- Natural identification as `topological_vector_bundle.pretrivialization`. -/
def to_pretrivialization (e : trivialization R F E) :
  topological_vector_bundle.pretrivialization R F E := { ..e }

protected lemma linear (hb : b ∈ e.base_set) :
  is_linear_map R (λ y : E b, (e (total_space_mk b y)).2) :=
e.linear' b hb

protected lemma continuous_on : continuous_on e e.source := e.continuous_to_fun

@[simp, mfld_simps] lemma coe_coe : ⇑e.to_local_homeomorph = e := rfl
@[simp, mfld_simps] lemma coe_fst (ex : x ∈ e.source) : (e x).1 = x.proj := e.proj_to_fun x ex
lemma mem_source : x ∈ e.source ↔ x.proj ∈ e.base_set := by rw [e.source_eq, mem_preimage]
lemma coe_mem_source : ↑y ∈ e.source ↔ b ∈ e.base_set := e.mem_source
lemma coe_fst' (ex : x.proj ∈ e.base_set) : (e x).1 = x.proj :=
e.coe_fst (e.mem_source.2 ex)

protected lemma eq_on : eq_on (prod.fst ∘ e) total_space.proj e.source := λ x hx, e.coe_fst hx
lemma mk_proj_snd (ex : x ∈ e.source) : (x.proj, (e x).2) = e x :=
prod.ext (e.coe_fst ex).symm rfl
lemma mk_proj_snd' (ex : x.proj ∈ e.base_set) : (x.proj, (e x).2) = e x :=
prod.ext (e.coe_fst' ex).symm rfl

lemma open_target : is_open e.target :=
by { rw e.target_eq, exact e.open_base_set.prod is_open_univ }

@[simp, mfld_simps] lemma coe_coe_fst (hb : b ∈ e.base_set) : (e y).1 = b :=
e.coe_fst (e.mem_source.2 hb)

lemma source_inter_preimage_target_inter (s : set (B × F)) :
  e.source ∩ (e ⁻¹' (e.target ∩ s)) = e.source ∩ (e ⁻¹' s) :=
e.to_local_homeomorph.source_inter_preimage_target_inter s

lemma mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.base_set :=
e.to_pretrivialization.mem_target

lemma mk_mem_target {y : F} : (b, y) ∈ e.target ↔ b ∈ e.base_set :=
e.to_pretrivialization.mem_target

lemma map_target {x : B × F} (hx : x ∈ e.target) : e.to_local_homeomorph.symm x ∈ e.source :=
e.to_local_homeomorph.map_target hx

lemma proj_symm_apply {x : B × F} (hx : x ∈ e.target) :
  (e.to_local_homeomorph.symm x).proj = x.1 :=
e.to_pretrivialization.proj_symm_apply hx

lemma proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) :
  (e.to_local_homeomorph.symm (b, x)).proj  = b :=
e.to_pretrivialization.proj_symm_apply' hx

lemma apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.to_local_homeomorph.symm x) = x :=
e.to_local_homeomorph.right_inv hx

lemma apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) :
  e (e.to_local_homeomorph.symm (b, x)) = (b, x) :=
e.to_pretrivialization.apply_symm_apply' hx

lemma symm_apply_apply {x : total_space E} (hx : x ∈ e.source) :
  e.to_local_homeomorph.symm (e x) = x :=
e.to_local_equiv.left_inv hx

@[simp, mfld_simps] lemma symm_coe_proj {x : B} {y : F}
  (e : trivialization R F E) (h : x ∈ e.base_set) :
  (e.to_local_homeomorph.symm (x, y)).1 = x := e.proj_symm_apply' h

/-- A fiberwise inverse to `e`. The function `F → E x` that induces a local inverse
  `B × F → total_space E` of `e` on `e.base_set`. It is defined to be `0` outside `e.base_set`. -/
protected def symm (e : trivialization R F E) (b : B) (y : F) : E b :=
e.to_pretrivialization.symm b y

lemma symm_apply (e : trivialization R F E) {b : B} (hb : b ∈ e.base_set) (y : F) :
  e.symm b y = cast (congr_arg E (e.symm_coe_proj hb)) (e.to_local_homeomorph.symm (b, y)).2 :=
dif_pos hb

lemma symm_apply_of_not_mem (e : trivialization R F E) {b : B} (hb : b ∉ e.base_set) (y : F) :
  e.symm b y = 0 :=
dif_neg hb

lemma mk_symm (e : trivialization R F E) {b : B} (hb : b ∈ e.base_set) (y : F) :
  total_space_mk b (e.symm b y) = e.to_local_homeomorph.symm (b, y) :=
e.to_pretrivialization.mk_symm hb y

lemma symm_proj_apply (e : trivialization R F E) (z : total_space E)
  (hz : z.proj ∈ e.base_set) : e.symm z.proj (e z).2 = z.2 :=
e.to_pretrivialization.symm_proj_apply z hz

lemma symm_apply_apply_mk (e : trivialization R F E) {b : B} (hb : b ∈ e.base_set) (y : E b) :
  e.symm b (e (total_space_mk b y)).2 = y :=
e.symm_proj_apply (total_space_mk b y) hb

lemma apply_mk_symm (e : trivialization R F E) {b : B} (hb : b ∈ e.base_set) (y : F) :
  e (total_space_mk b (e.symm b y)) = (b, y) :=
e.to_pretrivialization.apply_mk_symm hb y

lemma continuous_on_symm (e : trivialization R F E) :
  continuous_on (λ z : B × F, total_space_mk z.1 (e.symm z.1 z.2))
    (e.base_set ×ˢ (univ : set F)) :=
begin
  have : ∀ (z : B × F) (hz : z ∈ e.base_set ×ˢ (univ : set F)),
    total_space_mk z.1 (e.symm z.1 z.2) = e.to_local_homeomorph.symm z,
  { rintro x ⟨hx : x.1 ∈ e.base_set, _⟩, simp_rw [e.mk_symm hx, prod.mk.eta] },
  refine continuous_on.congr _ this,
  rw [← e.target_eq],
  exact e.to_local_homeomorph.continuous_on_symm
end

/-- A trivialization for a topological vector bundle defines linear equivalences between the
fibers and the model space. -/
def linear_equiv_at (e : trivialization R F E) (b : B) (hb : b ∈ e.base_set) :
  E b ≃ₗ[R] F :=
e.to_pretrivialization.linear_equiv_at b hb

/-- A coordinate change function between two trivializations, as a continuous linear equivalence.
  Defined to be the identity when `b` does not lie in the base set of both trivializations. -/
def coord_change (e e' : trivialization R F E) (b : B) : F ≃L[R] F :=
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
     (e.linear_equiv_at b (hb.1 : _)).symm.trans (e'.linear_equiv_at b hb.2)
    else linear_equiv.refl R F }

lemma coe_coord_change (e e' : trivialization R F E) {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) :
  ⇑(coord_change e e' b) = (e.linear_equiv_at b hb.1).symm.trans (e'.linear_equiv_at b hb.2) :=
congr_arg linear_equiv.to_fun (dif_pos hb)

lemma coord_change_apply (e e' : trivialization R F E) {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  coord_change e e' b y = (e' (total_space_mk b (e.symm b y))).2 :=
congr_arg (λ f, linear_equiv.to_fun f y) (dif_pos hb)

lemma mk_coord_change (e e' : trivialization R F E) {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  (b, coord_change e e' b y) = e' (total_space_mk b (e.symm b y)) :=
begin
  ext,
  { rw [e.mk_symm hb.1 y, e'.coe_fst', e.proj_symm_apply' hb.1],
    rw [e.proj_symm_apply' hb.1], exact hb.2 },
  { exact e.coord_change_apply e' hb y }
end

/-- A version of `coord_change_apply` that fully unfolds `coord_change`. The right-hand side is
ugly, but has good definitional properties for specifically defined trivializations. -/
lemma coord_change_apply' (e e' : trivialization R F E) {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  coord_change e e' b y = (e' (e.to_local_homeomorph.symm (b, y))).2 :=
by rw [e.coord_change_apply e' hb, e.mk_symm hb.1]

lemma coord_change_symm_apply (e e' : trivialization R F E) {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) :
  ⇑(coord_change e e' b).symm = (e'.linear_equiv_at b hb.2).symm.trans (e.linear_equiv_at b hb.1) :=
congr_arg linear_equiv.inv_fun (dif_pos hb)

@[simp]
lemma linear_equiv_at_apply (e : trivialization R F E) (b : B) (hb : b ∈ e.base_set) (v : E b) :
  e.linear_equiv_at b hb v = (e (total_space_mk b v)).2 := rfl

@[simp]
lemma linear_equiv_at_symm_apply (e : trivialization R F E) (b : B) (hb : b ∈ e.base_set) (v : F) :
  (e.linear_equiv_at b hb).symm v = e.symm b v := rfl

/-- A fiberwise linear inverse to `e`. -/
protected def symmₗ (e : trivialization R F E) (b : B) : F →ₗ[R] E b :=
e.to_pretrivialization.symmₗ b

lemma coe_symmₗ (e : trivialization R F E) (b : B) : ⇑(e.symmₗ b) = e.symm b :=
rfl

/-- A fiberwise linear map equal to `e` on `e.base_set`. -/
protected def linear_map_at (e : trivialization R F E) (b : B) : E b →ₗ[R] F :=
e.to_pretrivialization.linear_map_at b

lemma coe_linear_map_at (e : trivialization R F E) (b : B) :
  ⇑(e.linear_map_at b) = λ y, if b ∈ e.base_set then (e (total_space_mk b y)).2 else 0 :=
e.to_pretrivialization.coe_linear_map_at b

lemma coe_linear_map_at_of_mem (e : trivialization R F E) {b : B} (hb : b ∈ e.base_set) :
  ⇑(e.linear_map_at b) = λ y, (e (total_space_mk b y)).2 :=
by simp_rw [coe_linear_map_at, if_pos hb]

lemma linear_map_at_apply (e : trivialization R F E) {b : B} (y : E b) :
  e.linear_map_at b y = if b ∈ e.base_set then (e (total_space_mk b y)).2 else 0 :=
by rw [coe_linear_map_at]

lemma linear_map_at_def_of_mem (e : trivialization R F E) {b : B} (hb : b ∈ e.base_set) :
  e.linear_map_at b = e.linear_equiv_at b hb :=
dif_pos hb

lemma linear_map_at_def_of_not_mem (e : trivialization R F E) {b : B} (hb : b ∉ e.base_set) :
  e.linear_map_at b = 0 :=
dif_neg hb

lemma symmₗ_linear_map_at (e : trivialization R F E) {b : B} (hb : b ∈ e.base_set) (y : E b) :
  e.symmₗ b (e.linear_map_at b y) = y :=
e.to_pretrivialization.symmₗ_linear_map_at hb y

lemma linear_map_at_symmₗ (e : trivialization R F E) {b : B} (hb : b ∈ e.base_set) (y : F) :
  e.linear_map_at b (e.symmₗ b y) = y :=
e.to_pretrivialization.linear_map_at_symmₗ hb y

end topological_vector_bundle.trivialization

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
map `ε` from `s` to `F ≃L[R] F`. Here continuity is with respect to the operator norm on
`F →L[R] F`. -/
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
(total_space_mk_inducing [] : ∀ (b : B), inducing (@total_space_mk B E b))
(trivialization_atlas [] : set (trivialization R F E))
(trivialization_at [] : B → trivialization R F E)
(mem_base_set_trivialization_at [] : ∀ b : B, b ∈ (trivialization_at b).base_set)
(trivialization_mem_atlas [] : ∀ b : B, trivialization_at b ∈ trivialization_atlas)
(continuous_on_coord_change [] : ∀ (e e' ∈ trivialization_atlas), continuous_on
  (λ b, trivialization.coord_change e e' b : B → F →L[R] F) (e.base_set ∩ e'.base_set))

export topological_vector_bundle (trivialization_atlas trivialization_at
  mem_base_set_trivialization_at trivialization_mem_atlas continuous_on_coord_change)

variables {R F E} [topological_vector_bundle R F E]

namespace topological_vector_bundle

namespace trivialization

lemma _root_.continuous.if_const' {α β : Type*} [topological_space α] [topological_space β] (p : Prop)
  {f g : α → β} [decidable p]
  (hf : p → continuous f) (hg : ¬ p → continuous g) :
  continuous (λ a, if p then f a else g a) :=
by { split_ifs, exact hf h, exact hg h }


/-- Forward map of `continuous_linear_equiv_at` (only propositionally equal),
  defined everywhere (`0` outside domain). -/
@[simps apply {fully_applied := ff}]
def continuous_linear_map_at (e : trivialization R F E) (b : B) :
  E b →L[R] F :=
{ cont := by { dsimp, rw [e.coe_linear_map_at b],
  refine continuous.if_const' _ (λ hb, _) (λ _, continuous_zero),
  refine continuous_snd.comp (e.to_local_homeomorph.continuous_on.comp_continuous
    (total_space_mk_inducing R F E b).continuous (λ x, e.mem_source.mpr hb)) },
  .. e.linear_map_at b }

/-- Backwards map of `continuous_linear_equiv_at`, defined everywhere. -/
@[simps apply {fully_applied := ff}]
def symmL (e : trivialization R F E) (b : B) : F →L[R] E b :=
{ cont := begin
    by_cases hb : b ∈ e.base_set,
    { rw (topological_vector_bundle.total_space_mk_inducing R F E b).continuous_iff,
      exact e.continuous_on_symm.comp_continuous (continuous_const.prod_mk continuous_id)
        (λ x, mk_mem_prod hb (mem_univ x)) },
    { refine continuous_zero.congr (λ x, (e.symm_apply_of_not_mem hb x).symm) },
  end,
  .. e.symmₗ b }

lemma symmL_continuous_linear_map_at (e : trivialization R F E) {b : B} (hb : b ∈ e.base_set)
  (y : E b) :
  e.symmL b (e.continuous_linear_map_at b y) = y :=
e.symmₗ_linear_map_at hb y

lemma continuous_linear_map_at_symmL (e : trivialization R F E) {b : B} (hb : b ∈ e.base_set)
  (y : F) :
  e.continuous_linear_map_at b (e.symmL b y) = y :=
e.linear_map_at_symmₗ hb y

/-- In a topological vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
@[simps apply symm_apply {fully_applied := ff}]
def continuous_linear_equiv_at (e : trivialization R F E) (b : B)
  (hb : b ∈ e.base_set) : E b ≃L[R] F :=
{ to_fun := λ y, (e (total_space_mk b y)).2,
  inv_fun := e.symm b,
  continuous_to_fun := continuous_snd.comp (e.to_local_homeomorph.continuous_on.comp_continuous
    (total_space_mk_inducing R F E b).continuous (λ x, e.mem_source.mpr hb)),
  continuous_inv_fun := (e.symmL b).continuous,
  .. e.to_pretrivialization.linear_equiv_at b hb }

lemma coe_continuous_linear_equiv_at_eq (e : trivialization R F E) {b : B} (hb : b ∈ e.base_set) :
  (e.continuous_linear_equiv_at b hb : E b → F) = e.continuous_linear_map_at b :=
(e.coe_linear_map_at_of_mem hb).symm

lemma symm_continuous_linear_equiv_at_eq (e : trivialization R F E) {b : B} (hb : b ∈ e.base_set) :
  ((e.continuous_linear_equiv_at b hb).symm : F → E b) = e.symmL b :=
rfl

@[simp] lemma continuous_linear_equiv_at_apply' (e : trivialization R F E)
  (x : total_space E) (hx : x ∈ e.source) :
  e.continuous_linear_equiv_at x.proj (e.mem_source.1 hx) x.2 = (e x).2 := by { cases x, refl }

lemma apply_eq_prod_continuous_linear_equiv_at (e : trivialization R F E) (b : B)
  (hb : b ∈ e.base_set) (z : E b) :
  e.to_local_homeomorph ⟨b, z⟩ = (b, e.continuous_linear_equiv_at b hb z) :=
begin
  ext,
  { refine e.coe_fst _,
    rw e.source_eq,
    exact hb },
  { simp only [coe_coe, continuous_linear_equiv_at_apply] }
end

lemma symm_apply_eq_mk_continuous_linear_equiv_at_symm (e : trivialization R F E) (b : B)
  (hb : b ∈ e.base_set) (z : F) :
  e.to_local_homeomorph.symm ⟨b, z⟩
  = total_space_mk b ((e.continuous_linear_equiv_at b hb).symm z) :=
begin
  have h : (b, z) ∈ e.to_local_homeomorph.target,
  { rw e.target_eq,
    exact ⟨hb, mem_univ _⟩ },
  apply e.to_local_homeomorph.inj_on (e.to_local_homeomorph.map_target h),
  { simp only [e.source_eq, hb, mem_preimage]},
  simp_rw [e.apply_eq_prod_continuous_linear_equiv_at b hb, e.to_local_homeomorph.right_inv h,
    continuous_linear_equiv.apply_symm_apply],
end

lemma comp_continuous_linear_equiv_at_eq_coord_change (e e' : trivialization R F E) {b : B}
  (hb : b ∈ e.1.base_set ∩ e'.1.base_set) :
  (e.continuous_linear_equiv_at b hb.1).symm.trans (e'.continuous_linear_equiv_at b hb.2)
  = coord_change e e' b :=
by { ext v, rw [coord_change_apply e e' hb], refl }

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

namespace trivial_topological_vector_bundle
variables (R B F)

/-- Local trivialization for trivial bundle. -/
def trivialization : trivialization R F (bundle.trivial B F) :=
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
  proj_to_fun := λ y hy, rfl,
  linear' := λ x hx, ⟨λ y z, rfl, λ c y, rfl⟩ }

lemma trivialization.coord_change (b : B) :
  (trivialization R B F).coord_change
    (trivialization R B F) b = continuous_linear_equiv.refl R F :=
begin
  ext v,
  rw [trivialization.coord_change_apply'],
  exacts [rfl, ⟨mem_univ _, mem_univ _⟩]
end

@[simp]
lemma trivialization_source : (trivialization R B F).source = univ := rfl

@[simp]
lemma trivialization_target : (trivialization R B F).target = univ := rfl

instance topological_vector_bundle :
  topological_vector_bundle R F (bundle.trivial B F) :=
{ trivialization_atlas := {trivial_topological_vector_bundle.trivialization R B F},
  trivialization_at := λ x, trivial_topological_vector_bundle.trivialization R B F,
  mem_base_set_trivialization_at := mem_univ,
  trivialization_mem_atlas := λ x, mem_singleton _,
  total_space_mk_inducing := λ b, ⟨begin
    have : (λ (x : trivial B F b), x) = @id F, by { ext x, refl },
    simp only [total_space.topological_space, induced_inf, induced_compose, function.comp,
      total_space.proj, induced_const, top_inf_eq, trivial.proj_snd, id.def,
      trivial.topological_space, this, induced_id],
  end⟩,
  continuous_on_coord_change := begin
    intros e he e' he',
    rw [mem_singleton_iff.mp he, mem_singleton_iff.mp he'],
    simp_rw [trivial_topological_vector_bundle.trivialization.coord_change],
    exact continuous_const.continuous_on
  end }

end trivial_topological_vector_bundle

/- Not registered as an instance because of a metavariable. -/
lemma is_topological_vector_bundle_is_topological_fiber_bundle :
  is_topological_fiber_bundle F (@total_space.proj B E) :=
λ x, ⟨(trivialization_at R F E x).to_fiber_bundle_trivialization,
  mem_base_set_trivialization_at R F E x⟩

include R F

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
  index_at := λ x, default,
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
instance to_topological_space : topological_space (Z.total_space) :=
topological_fiber_bundle_core.to_topological_space ι ↑Z

variables {ι} (b : B) (a : F)

@[simp, mfld_simps] lemma coe_coord_change (i j : ι) :
  topological_fiber_bundle_core.coord_change ↑Z i j b = Z.coord_change i j b := rfl

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def local_triv (i : ι) : topological_vector_bundle.trivialization R F Z.fiber :=
{ linear' := λ x hx,
  { map_add := λ v w, by simp only [continuous_linear_map.map_add] with mfld_simps,
    map_smul := λ r v, by simp only [continuous_linear_map.map_smul] with mfld_simps},
  ..topological_fiber_bundle_core.local_triv ↑Z i }

variables (i j : ι)

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

@[simp, mfld_simps] lemma local_triv_symm_apply {b : B} (hb : b ∈ Z.base_set i) (v : F) :
  (Z.local_triv i).symm b v = Z.coord_change i (Z.index_at b) b v :=
by apply (Z.local_triv i).symm_apply hb v

@[simp, mfld_simps] lemma local_triv_coord_change_eq {b : B} (hb : b ∈ Z.base_set i ∩ Z.base_set j)
  (v : F) :
  (Z.local_triv i).coord_change (Z.local_triv j) b v = Z.coord_change i j b v :=
begin
  rw [trivialization.coord_change_apply', local_triv_symm_fst, local_triv_apply,
    coord_change_comp],
  exacts [⟨⟨hb.1, Z.mem_base_set_at b⟩, hb.2⟩, hb]
end

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
  continuous_on_coord_change := begin
    rintros _ ⟨i, rfl⟩ _ ⟨i', rfl⟩,
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
variables [nondiscrete_normed_field R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
  [normed_group F] [normed_space R F] [topological_space B]

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
@[nolint has_inhabited_instance]
structure topological_vector_prebundle :=
(pretrivialization_atlas : set (pretrivialization R F E))
(pretrivialization_at : B → pretrivialization R F E)
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
  {e e' : pretrivialization R F E} (he : e ∈ a.pretrivialization_atlas)
  (he' : e' ∈ a.pretrivialization_atlas) (b : B) : F →L[R] F :=
classical.some (a.exists_coord_change e he e' he') b

lemma continuous_on_coord_change (a : topological_vector_prebundle R F E)
  {e e' : pretrivialization R F E} (he : e ∈ a.pretrivialization_atlas)
  (he' : e' ∈ a.pretrivialization_atlas) :
  continuous_on (a.coord_change he he') (e.base_set ∩ e'.base_set) :=
(classical.some_spec (a.exists_coord_change e he e' he')).1

lemma coord_change_apply (a : topological_vector_prebundle R F E)
  {e e' : pretrivialization R F E} (he : e ∈ a.pretrivialization_atlas)
  (he' : e' ∈ a.pretrivialization_atlas) {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) (v : F) :
  a.coord_change he he' b v = (e' (total_space_mk b (e.symm b v))).2 :=
(classical.some_spec (a.exists_coord_change e he e' he')).2 b hb v

lemma mk_coord_change (a : topological_vector_prebundle R F E)
  {e e' : pretrivialization R F E} (he : e ∈ a.pretrivialization_atlas)
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
{ pretrivialization_atlas :=
    pretrivialization.to_fiber_bundle_pretrivialization '' a.pretrivialization_atlas,
  pretrivialization_at := λ x, (a.pretrivialization_at x).to_fiber_bundle_pretrivialization,
  pretrivialization_mem_atlas := λ x, ⟨_, a.pretrivialization_mem_atlas x, rfl⟩,
  continuous_triv_change := begin
    rintros _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩,
    have := is_bounded_bilinear_map_apply.continuous.comp_continuous_on
      ((a.continuous_on_coord_change he' he).prod_map continuous_on_id),
    have H : e'.to_fiber_bundle_pretrivialization.to_local_equiv.target ∩
      e'.to_fiber_bundle_pretrivialization.to_local_equiv.symm ⁻¹'
      e.to_fiber_bundle_pretrivialization.to_local_equiv.source =
      (e'.base_set ∩ e.base_set) ×ˢ (univ : set F),
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

/-- Promotion from a `topologial_vector_prebundle.trivialization` to a
  `topological_vector_bundle.trivialization`. -/
def trivialization_of_mem_pretrivialization_atlas (a : topological_vector_prebundle R F E)
  {e : topological_vector_bundle.pretrivialization R F E} (he : e ∈ a.pretrivialization_atlas) :
  @topological_vector_bundle.trivialization R _ F E _ _ _ _ _ _ _ a.total_space_topology :=
begin
  letI := a.total_space_topology,
  exact { linear' := λ b, e.linear,
  ..a.to_topological_fiber_prebundle.trivialization_of_mem_pretrivialization_atlas ⟨e, he, rfl⟩ }
end

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
  trivialization_at := λ x, a.trivialization_of_mem_pretrivialization_atlas
    (a.pretrivialization_mem_atlas x),
  mem_base_set_trivialization_at := a.mem_base_pretrivialization_at,
  trivialization_mem_atlas := λ x, ⟨_, a.pretrivialization_mem_atlas x, rfl⟩,
  continuous_on_coord_change := begin
    rintros _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩,
    refine (a.continuous_on_coord_change he he').congr _,
    intros b hb,
    ext v,
    rw [a.coord_change_apply he he' hb v, continuous_linear_equiv.coe_coe,
      trivialization.coord_change_apply],
    exacts [rfl, hb]
  end }

end topological_vector_prebundle

end

section pullback

/-! ### Pullback of topological vector bundles -/

open topological_space topological_vector_bundle

variables {B' : Type*} (f : B' → B) (E' : B → Type*)

section

local attribute [reducible] pullback

instance [∀ (x : B), topological_space (E' x)] : ∀ (x : B'), topological_space ((f *ᵖ E') x) :=
by apply_instance

instance [∀ (x : B), add_comm_monoid (E' x)] : ∀ (x : B'), add_comm_monoid ((f *ᵖ E') x) :=
by apply_instance

instance [semiring R] [∀ (x : B), add_comm_monoid (E' x)] [∀ x, module R (E' x)] :
  ∀ (x : B'), module R ((f *ᵖ E') x) :=
by apply_instance

end

variables [topological_space B'] [topological_space (total_space E)]

/-- Definition of `pullback.total_space.topological_space`, which we make irreducible. -/
@[irreducible] def pullback_topology : topological_space (total_space (f *ᵖ E)) :=
induced total_space.proj ‹topological_space B'› ⊓
induced (pullback.lift f) ‹topological_space (total_space E)›

/-- The topology on the total space of a pullback bundle is the coarsest topology for which both
the projections to the base and the map to the original bundle are continuous. -/
instance pullback.total_space.topological_space :
  topological_space (total_space (f *ᵖ E)) :=
pullback_topology E f

lemma pullback.continuous_proj (f : B' → B) :
  continuous (@total_space.proj _ (f *ᵖ E)) :=
begin
  rw [continuous_iff_le_induced, pullback.total_space.topological_space, pullback_topology],
  exact inf_le_left,
end

lemma pullback.continuous_lift (f : B' → B) :
  continuous (@pullback.lift B E B' f) :=
begin
  rw [continuous_iff_le_induced, pullback.total_space.topological_space, pullback_topology],
  exact inf_le_right,
end

lemma inducing_pullback_total_space_embedding (f : B' → B) :
  inducing (@pullback_total_space_embedding B E B' f) :=
begin
  constructor,
  simp_rw [prod.topological_space, induced_inf, induced_compose,
    pullback.total_space.topological_space, pullback_topology],
  refl
end

variables (F) [nondiscrete_normed_field 𝕜]
  [normed_group F] [normed_space 𝕜 F] [topological_space B]
  [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)]

lemma pullback.continuous_total_space_mk [∀ x, topological_space (E x)]
  [topological_vector_bundle 𝕜 F E] {f : B' → B} {x : B'} :
  continuous (@total_space_mk _ (f *ᵖ E) x) :=
begin
  simp only [continuous_iff_le_induced, pullback.total_space.topological_space, induced_compose,
    induced_inf, function.comp, total_space_mk, total_space.proj, induced_const, top_inf_eq,
    pullback_topology],
  exact le_of_eq (topological_vector_bundle.total_space_mk_inducing 𝕜 F E (f x)).induced,
end

variables {E 𝕜 F} {K : Type*} [continuous_map_class K B' B]

/-- A vector bundle trivialization can be pulled back to a trivialization on the pullback bundle. -/
def topological_vector_bundle.trivialization.pullback (e : trivialization 𝕜 F E) (f : K) :
  trivialization 𝕜 F ((f : B' → B) *ᵖ E) :=
{ to_fun := λ z, (z.proj, (e (pullback.lift f z)).2),
  inv_fun := λ y, @total_space_mk _ (f *ᵖ E) y.1 (e.symm (f y.1) y.2),
  source := pullback.lift f ⁻¹' e.source,
  base_set := f ⁻¹' e.base_set,
  target := (f ⁻¹' e.base_set) ×ˢ (univ : set F),
  map_source' := λ x h, by { simp_rw [e.source_eq, mem_preimage, pullback.proj_lift] at h,
    simp_rw [prod_mk_mem_set_prod_eq, mem_univ, and_true, mem_preimage, h] },
  map_target' := λ y h, by { rw [mem_prod, mem_preimage] at h,
    simp_rw [e.source_eq, mem_preimage, pullback.proj_lift, h.1] },
  left_inv' := λ x h, by { simp_rw [mem_preimage, e.mem_source, pullback.proj_lift] at h,
    simp_rw [pullback.lift, e.symm_apply_apply_mk h, total_space.eta] },
  right_inv' := λ x h, by { simp_rw [mem_prod, mem_preimage, mem_univ, and_true] at h,
    simp_rw [total_space.proj_mk, pullback.lift_mk, e.apply_mk_symm h, prod.mk.eta] },
  open_source := by { simp_rw [e.source_eq, ← preimage_comp], exact ((map_continuous f).comp $
    pullback.continuous_proj E f).is_open_preimage _ e.open_base_set },
  open_target := ((map_continuous f).is_open_preimage _ e.open_base_set).prod is_open_univ,
  open_base_set := (map_continuous f).is_open_preimage _ e.open_base_set,
  continuous_to_fun := (pullback.continuous_proj E f).continuous_on.prod
    (continuous_snd.comp_continuous_on $
    e.continuous_on.comp (pullback.continuous_lift E f).continuous_on subset.rfl),
  continuous_inv_fun := begin
    dsimp only,
    simp_rw [(inducing_pullback_total_space_embedding E f).continuous_on_iff, function.comp,
      pullback_total_space_embedding, total_space.proj_mk],
    dsimp only [total_space.proj_mk],
    refine continuous_on_fst.prod (e.continuous_on_symm.comp
      ((map_continuous f).prod_map continuous_id).continuous_on subset.rfl)
  end,
  source_eq := by { dsimp only, rw e.source_eq, refl, },
  target_eq := rfl,
  proj_to_fun := λ y h, rfl,
  linear' := λ x h, e.linear h }

instance pullback [∀ x, topological_space (E x)] [topological_vector_bundle 𝕜 F E] (f : K) :
  topological_vector_bundle 𝕜 F ((f : B' → B) *ᵖ E) :=
{ total_space_mk_inducing := λ x, inducing_of_inducing_compose
    (pullback.continuous_total_space_mk 𝕜 F E) (pullback.continuous_lift E f)
    (total_space_mk_inducing 𝕜 F E (f x)),
  trivialization_atlas := (λ e : trivialization 𝕜 F E, e.pullback f) '' trivialization_atlas 𝕜 F E,
  trivialization_at := λ x, (trivialization_at 𝕜 F E (f x)).pullback f,
  mem_base_set_trivialization_at := λ x, mem_base_set_trivialization_at 𝕜 F E (f x),
  trivialization_mem_atlas := λ x, mem_image_of_mem _ (trivialization_mem_atlas 𝕜 F E (f x)),
  continuous_on_coord_change := begin
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩,
    refine ((continuous_on_coord_change e he e' he').comp (map_continuous f).continuous_on
      (λ b hb, hb)).congr _,
    rintro b (hb : f b ∈ e.base_set ∩ e'.base_set), ext v,
    show ((e.pullback f).coord_change (e'.pullback f) b) v = (e.coord_change e' (f b)) v,
    rw [e.coord_change_apply e' hb, (e.pullback f).coord_change_apply' _],
    exacts [rfl, hb]
  end }

end pullback

/-! ### Direct sum of two vector bundles over the same base -/

namespace topological_vector_bundle

section defs
variables (E₁ : B → Type*) (E₂ : B → Type*)
variables [topological_space (total_space E₁)] [topological_space (total_space E₂)]

/-- Equip the total space of the fibrewise product of two topological vector bundles `E₁`, `E₂` with
the induced topology from the diagonal embedding into `total_space E₁ × total_space E₂`. -/
instance prod.topological_space :
  topological_space (total_space (E₁ ×ᵇ E₂)) :=
topological_space.induced
  (λ p, ((⟨p.1, p.2.1⟩ : total_space E₁), (⟨p.1, p.2.2⟩ : total_space E₂)))
  (by apply_instance : topological_space (total_space E₁ × total_space E₂))

/-- The diagonal map from the total space of the fibrewise product of two topological vector bundles
`E₁`, `E₂` into `total_space E₁ × total_space E₂` is `inducing`. -/
lemma prod.inducing_diag : inducing
  (λ p, (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩) :
    total_space (E₁ ×ᵇ E₂) → total_space E₁ × total_space E₂) :=
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
λ p, ⟨p.1, (e₁ ⟨p.1, p.2.1⟩).2, (e₂ ⟨p.1, p.2.2⟩).2⟩

variables {e₁ e₂}

lemma prod.continuous_to_fun : continuous_on (prod.to_fun' e₁ e₂)
  (@total_space.proj B (E₁ ×ᵇ E₂) ⁻¹' (e₁.base_set ∩ e₂.base_set)) :=
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

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the inverse
function for the construction `topological_vector_bundle.trivialization.prod`, the induced
trivialization for the direct sum of `E₁` and `E₂`. -/
def prod.inv_fun' (p : B × (F₁ × F₂)) : total_space (E₁ ×ᵇ E₂) :=
⟨p.1, e₁.symm p.1 p.2.1, e₂.symm p.1 p.2.2⟩

variables {e₁ e₂}

lemma prod.left_inv {x : total_space (E₁ ×ᵇ E₂)}
  (h : x ∈ @total_space.proj B (E₁ ×ᵇ E₂) ⁻¹' (e₁.base_set ∩ e₂.base_set)) :
  prod.inv_fun' e₁ e₂ (prod.to_fun' e₁ e₂ x) = x :=
begin
  obtain ⟨x, v₁, v₂⟩ := x,
  obtain ⟨h₁ : x ∈ e₁.base_set, h₂ : x ∈ e₂.base_set⟩ := h,
  simp only [prod.to_fun', prod.inv_fun', symm_apply_apply_mk, h₁, h₂]
end

lemma prod.right_inv {x : B × F₁ × F₂}
  (h : x ∈ (e₁.base_set ∩ e₂.base_set) ×ˢ (univ : set (F₁ × F₂))) :
  prod.to_fun' e₁ e₂ (prod.inv_fun' e₁ e₂ x) = x :=
begin
  obtain ⟨x, w₁, w₂⟩ := x,
  obtain ⟨⟨h₁ : x ∈ e₁.base_set, h₂ : x ∈ e₂.base_set⟩, -⟩ := h,
  simp only [prod.to_fun', prod.inv_fun', apply_mk_symm, h₁, h₂]
end

lemma prod.continuous_inv_fun :
  continuous_on (prod.inv_fun' e₁ e₂) ((e₁.base_set ∩ e₂.base_set) ×ˢ (univ : set (F₁ × F₂))) :=
begin
  rw (prod.inducing_diag E₁ E₂).continuous_on_iff,
  have H₁ : continuous (λ p : B × F₁ × F₂, ((p.1, p.2.1), (p.1, p.2.2))) :=
    (continuous_id.prod_map continuous_fst).prod_mk (continuous_id.prod_map continuous_snd),
  refine (e₁.continuous_on_symm.prod_map e₂.continuous_on_symm).comp H₁.continuous_on _,
  exact λ x h, ⟨⟨h.1.1, mem_univ _⟩, ⟨h.1.2, mem_univ _⟩⟩
end

variables (e₁ e₂)
variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [topological_vector_bundle R F₁ E₁] [topological_vector_bundle R F₂ E₂]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
trivialization for the direct sum of `E₁` and `E₂`, whose base set is `e₁.base_set ∩ e₂.base_set`.
-/
@[nolint unused_arguments]
def prod : trivialization R (F₁ × F₂) (E₁ ×ᵇ E₂) :=
{ to_fun := prod.to_fun' e₁ e₂,
  inv_fun := prod.inv_fun' e₁ e₂,
  source := (@total_space.proj B (E₁ ×ᵇ E₂)) ⁻¹' (e₁.base_set ∩ e₂.base_set),
  target := (e₁.base_set ∩ e₂.base_set) ×ˢ (set.univ : set (F₁ × F₂)),
  map_source' := λ x h, ⟨h, set.mem_univ _⟩,
  map_target' := λ x h, h.1,
  left_inv' := λ x, prod.left_inv,
  right_inv' := λ x, prod.right_inv,
  open_source := begin
    refine (e₁.open_base_set.inter e₂.open_base_set).preimage _,
    have : continuous (@total_space.proj B E₁) := continuous_proj R B F₁,
    exact this.comp (prod.inducing_diag E₁ E₂).continuous.fst,
  end,
  open_target := (e₁.open_base_set.inter e₂.open_base_set).prod is_open_univ,
  continuous_to_fun := prod.continuous_to_fun,
  continuous_inv_fun := prod.continuous_inv_fun,
  base_set := e₁.base_set ∩ e₂.base_set,
  open_base_set := e₁.open_base_set.inter e₂.open_base_set,
  source_eq := rfl,
  target_eq := rfl,
  proj_to_fun := λ x h, rfl,
  linear' := λ x ⟨h₁, h₂⟩, (((e₁.linear h₁).mk' _).prod_map ((e₂.linear h₂).mk' _)).is_linear }

@[simp] lemma base_set_prod : (prod e₁ e₂).base_set = e₁.base_set ∩ e₂.base_set :=
rfl

variables {e₁ e₂}

lemma prod_apply {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set) (v₁ : E₁ x)
  (v₂ : E₂ x) :
  prod e₁ e₂ ⟨x, (v₁, v₂)⟩
  = ⟨x, e₁.continuous_linear_equiv_at x hx₁ v₁, e₂.continuous_linear_equiv_at x hx₂ v₂⟩ :=
rfl

lemma prod_symm_apply (x : B) (w₁ : F₁) (w₂ : F₂) : (prod e₁ e₂).to_local_equiv.symm (x, w₁, w₂)
  = ⟨x, e₁.symm x w₁, e₂.symm x w₂⟩ :=
rfl

end trivialization

open trivialization

variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [topological_vector_bundle R F₁ E₁] [topological_vector_bundle R F₂ E₂]

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
  continuous_on_coord_change := begin
    rintros _ ⟨⟨e₁, e₂⟩, ⟨he₁, he₂⟩, rfl⟩ _ ⟨⟨e₁', e₂'⟩, ⟨he₁', he₂'⟩, rfl⟩,
    have := continuous_on_coord_change e₁ he₁ e₁' he₁',
    have := continuous_on_coord_change e₂ he₂ e₂' he₂',
    refine (((continuous_on_coord_change e₁ he₁ e₁' he₁').mono _).prod_mapL R
      ((continuous_on_coord_change e₂ he₂ e₂' he₂').mono _)).congr _;
    dsimp only [base_set_prod] with mfld_simps,
    { mfld_set_tac },
    { mfld_set_tac },
    { rintro b hb,
      rw [continuous_linear_map.ext_iff],
      rintro ⟨v₁, v₂⟩,
      show (e₁.prod e₂).coord_change (e₁'.prod e₂') b (v₁, v₂) =
        (e₁.coord_change e₁' b v₁, e₂.coord_change e₂' b v₂),
      rw [e₁.coord_change_apply e₁', e₂.coord_change_apply e₂', (e₁.prod e₂).coord_change_apply'],
      exacts [rfl, hb, ⟨hb.1.2, hb.2.2⟩, ⟨hb.1.1, hb.2.1⟩] }
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
  exact (congr_arg prod.snd (prod_apply hx₁ hx₂ v₁ v₂) : _)
end

end topological_vector_bundle
