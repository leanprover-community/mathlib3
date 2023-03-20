/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import data.bundle
import topology.algebra.order.field
import topology.local_homeomorph

/-!
# Trivializations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

### Basic definitions

* `trivialization F p` : structure extending local homeomorphisms, defining a local
                  trivialization of a topological space `Z` with projection `p` and fiber `F`.

* `pretrivialization F proj` : trivialization as a local equivalence, mainly used when the
                                      topology on the total space has not yet been defined.

### Operations on bundles

We provide the following operations on `trivialization`s.

* `trivialization.comp_homeomorph`: given a local trivialization `e` of a fiber bundle
  `p : Z → B` and a homeomorphism `h : Z' ≃ₜ Z`, returns a local trivialization of the fiber bundle
  `p ∘ h`.

## Implementation notes

Previously, in mathlib, there was a structure `topological_vector_bundle.trivialization` which
extended another structure `topological_fiber_bundle.trivialization` by a linearity hypothesis. As
of PR #17359, we have changed this to a single structure `trivialization` (no namespace), together
with a mixin class `trivialization.is_linear`.

This permits all the *data* of a vector bundle to be held at the level of fiber bundles, so that the
same trivializations can underlie an object's structure as (say) a vector bundle over `ℂ` and as a
vector bundle over `ℝ`, as well as its structure simply as a fiber bundle.

This might be a little surprising, given the general trend of the library to ever-increased
bundling.  But in this case the typical motivation for more bundling does not apply: there is no
algebraic or order structure on the whole type of linear (say) trivializations of a bundle.
Indeed, since trivializations only have meaning on their base sets (taking junk values outside), the
type of linear trivializations is not even particularly well-behaved.

-/

open topological_space filter set bundle
open_locale topology classical bundle

variables {ι : Type*} {B : Type*} {F : Type*} {E : B → Type*}
variables (F) {Z : Type*} [topological_space B] [topological_space F] {proj : Z → B}

/-- This structure contains the information left for a local trivialization (which is implemented
below as `trivialization F proj`) if the total space has not been given a topology, but we
have a topology on both the fiber and the base space. Through the construction
`topological_fiber_prebundle F proj` it will be possible to promote a
`pretrivialization F proj` to a `trivialization F proj`. -/
@[ext, nolint has_nonempty_instance]
structure pretrivialization (proj : Z → B) extends local_equiv Z (B × F) :=
(open_target   : is_open target)
(base_set      : set B)
(open_base_set : is_open base_set)
(source_eq     : source = proj ⁻¹' base_set)
(target_eq     : target = base_set ×ˢ univ)
(proj_to_fun   : ∀ p ∈ source, (to_fun p).1 = proj p)

namespace pretrivialization

instance : has_coe_to_fun (pretrivialization F proj) (λ _, Z → (B × F)) := ⟨λ e, e.to_fun⟩

variables {F} (e : pretrivialization F proj) {x : Z}

@[simp, mfld_simps] lemma coe_coe : ⇑e.to_local_equiv = e := rfl
@[simp, mfld_simps] lemma coe_fst (ex : x ∈ e.source) : (e x).1 = proj x := e.proj_to_fun x ex
lemma mem_source : x ∈ e.source ↔ proj x ∈ e.base_set := by rw [e.source_eq, mem_preimage]
lemma coe_fst' (ex : proj x ∈ e.base_set) : (e x).1 = proj x := e.coe_fst (e.mem_source.2 ex)
protected lemma eq_on : eq_on (prod.fst ∘ e) proj e.source := λ x hx, e.coe_fst hx
lemma mk_proj_snd (ex : x ∈ e.source) : (proj x, (e x).2) = e x := prod.ext (e.coe_fst ex).symm rfl
lemma mk_proj_snd' (ex : proj x ∈ e.base_set) : (proj x, (e x).2) = e x :=
prod.ext (e.coe_fst' ex).symm rfl

/-- Composition of inverse and coercion from the subtype of the target. -/
def set_symm : e.target → Z := e.target.restrict e.to_local_equiv.symm

lemma mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.base_set :=
by rw [e.target_eq, prod_univ, mem_preimage]

lemma proj_symm_apply {x : B × F} (hx : x ∈ e.target) : proj (e.to_local_equiv.symm x) = x.1 :=
begin
  have := (e.coe_fst (e.to_local_equiv.map_target hx)).symm,
  rwa [← e.coe_coe, e.to_local_equiv.right_inv hx] at this
end

lemma proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) :
  proj (e.to_local_equiv.symm (b, x)) = b :=
e.proj_symm_apply (e.mem_target.2 hx)

lemma proj_surj_on_base_set [nonempty F] : set.surj_on proj e.source e.base_set :=
λ b hb, let ⟨y⟩ := ‹nonempty F› in ⟨e.to_local_equiv.symm (b, y),
  e.to_local_equiv.map_target $ e.mem_target.2 hb, e.proj_symm_apply' hb⟩

lemma apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.to_local_equiv.symm x) = x :=
e.to_local_equiv.right_inv hx

lemma apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) :
  e (e.to_local_equiv.symm (b, x)) = (b, x) :=
e.apply_symm_apply (e.mem_target.2 hx)

lemma symm_apply_apply {x : Z} (hx : x ∈ e.source) : e.to_local_equiv.symm (e x) = x :=
e.to_local_equiv.left_inv hx

@[simp, mfld_simps] lemma symm_apply_mk_proj {x : Z} (ex : x ∈ e.source) :
  e.to_local_equiv.symm (proj x, (e x).2) = x :=
by rw [← e.coe_fst ex, prod.mk.eta, ← e.coe_coe, e.to_local_equiv.left_inv ex]

@[simp, mfld_simps] lemma preimage_symm_proj_base_set :
  (e.to_local_equiv.symm ⁻¹' (proj ⁻¹' e.base_set)) ∩ e.target  = e.target :=
begin
  refine inter_eq_right_iff_subset.mpr (λ x hx, _),
  simp only [mem_preimage, local_equiv.inv_fun_as_coe, e.proj_symm_apply hx],
  exact e.mem_target.mp hx,
end

@[simp, mfld_simps] lemma preimage_symm_proj_inter (s : set B) :
  (e.to_local_equiv.symm ⁻¹' (proj ⁻¹' s)) ∩ e.base_set ×ˢ univ = (s ∩ e.base_set) ×ˢ univ :=
begin
  ext ⟨x, y⟩,
  suffices : x ∈ e.base_set → (proj (e.to_local_equiv.symm (x, y)) ∈ s ↔ x ∈ s),
    by simpa only [prod_mk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ, and.congr_left_iff],
  intro h,
  rw [e.proj_symm_apply' h]
end

lemma target_inter_preimage_symm_source_eq (e f : pretrivialization F proj) :
  f.target ∩ (f.to_local_equiv.symm) ⁻¹' e.source = (e.base_set ∩ f.base_set) ×ˢ univ :=
by rw [inter_comm, f.target_eq, e.source_eq, f.preimage_symm_proj_inter]

lemma trans_source (e f : pretrivialization F proj) :
  (f.to_local_equiv.symm.trans e.to_local_equiv).source = (e.base_set ∩ f.base_set) ×ˢ univ :=
by rw [local_equiv.trans_source, local_equiv.symm_source, e.target_inter_preimage_symm_source_eq]

lemma symm_trans_symm (e e' : pretrivialization F proj) :
  (e.to_local_equiv.symm.trans e'.to_local_equiv).symm =
  e'.to_local_equiv.symm.trans e.to_local_equiv :=
by rw [local_equiv.trans_symm_eq_symm_trans_symm, local_equiv.symm_symm]

lemma symm_trans_source_eq (e e' : pretrivialization F proj) :
  (e.to_local_equiv.symm.trans e'.to_local_equiv).source = (e.base_set ∩ e'.base_set) ×ˢ univ :=
by rw [local_equiv.trans_source, e'.source_eq, local_equiv.symm_source, e.target_eq, inter_comm,
  e.preimage_symm_proj_inter, inter_comm]

lemma symm_trans_target_eq (e e' : pretrivialization F proj) :
  (e.to_local_equiv.symm.trans e'.to_local_equiv).target = (e.base_set ∩ e'.base_set) ×ˢ univ :=
by rw [← local_equiv.symm_source, symm_trans_symm, symm_trans_source_eq, inter_comm]

variables {B F} (e' : pretrivialization F (π E)) {x' : total_space E} {b : B} {y : E b}

lemma coe_mem_source : ↑y ∈ e'.source ↔ b ∈ e'.base_set := e'.mem_source

@[simp, mfld_simps] lemma coe_coe_fst (hb : b ∈ e'.base_set) : (e' y).1 = b :=
e'.coe_fst (e'.mem_source.2 hb)

lemma mk_mem_target {x : B} {y : F} : (x, y) ∈ e'.target ↔ x ∈ e'.base_set :=
e'.mem_target

lemma symm_coe_proj {x : B} {y : F} (e' : pretrivialization F (π E)) (h : x ∈ e'.base_set) :
  (e'.to_local_equiv.symm (x, y)).1 = x :=
e'.proj_symm_apply' h

section has_zero
variables [∀ x, has_zero (E x)]

/-- A fiberwise inverse to `e`. This is the function `F → E b` that induces a local inverse
`B × F → total_space E` of `e` on `e.base_set`. It is defined to be `0` outside `e.base_set`. -/
protected noncomputable def symm (e : pretrivialization F (π E)) (b : B) (y : F) : E b :=
if hb : b ∈ e.base_set
then cast (congr_arg E (e.proj_symm_apply' hb)) (e.to_local_equiv.symm (b, y)).2
else 0

lemma symm_apply (e : pretrivialization F (π E)) {b : B} (hb : b ∈ e.base_set) (y : F) :
  e.symm b y = cast (congr_arg E (e.symm_coe_proj hb)) (e.to_local_equiv.symm (b, y)).2 :=
dif_pos hb

lemma symm_apply_of_not_mem (e : pretrivialization F (π E)) {b : B} (hb : b ∉ e.base_set) (y : F) :
  e.symm b y = 0 :=
dif_neg hb

lemma coe_symm_of_not_mem (e : pretrivialization F (π E)) {b : B} (hb : b ∉ e.base_set) :
  (e.symm b : F → E b) = 0 :=
funext $ λ y, dif_neg hb

lemma mk_symm (e : pretrivialization F (π E)) {b : B} (hb : b ∈ e.base_set) (y : F) :
  total_space_mk b (e.symm b y) = e.to_local_equiv.symm (b, y) :=
by rw [e.symm_apply hb, total_space.mk_cast, total_space.eta]

lemma symm_proj_apply (e : pretrivialization F (π E)) (z : total_space E)
  (hz : z.proj ∈ e.base_set) : e.symm z.proj (e z).2 = z.2 :=
by rw [e.symm_apply hz, cast_eq_iff_heq, e.mk_proj_snd' hz,
  e.symm_apply_apply (e.mem_source.mpr hz)]

lemma symm_apply_apply_mk (e : pretrivialization F (π E)) {b : B} (hb : b ∈ e.base_set) (y : E b) :
  e.symm b (e (total_space_mk b y)).2 = y :=
e.symm_proj_apply (total_space_mk b y) hb

lemma apply_mk_symm (e : pretrivialization F (π E)) {b : B} (hb : b ∈ e.base_set) (y : F) :
  e (total_space_mk b (e.symm b y)) = (b, y) :=
by rw [e.mk_symm hb, e.apply_symm_apply (e.mk_mem_target.mpr hb)]

end has_zero

end pretrivialization

variables [topological_space Z] [topological_space (total_space E)]

/--
A structure extending local homeomorphisms, defining a local trivialization of a projection
`proj : Z → B` with fiber `F`, as a local homeomorphism between `Z` and `B × F` defined between two
sets of the form `proj ⁻¹' base_set` and `base_set × F`, acting trivially on the first coordinate.
-/
@[ext, nolint has_nonempty_instance]
structure trivialization (proj : Z → B)
  extends local_homeomorph Z (B × F) :=
(base_set      : set B)
(open_base_set : is_open base_set)
(source_eq     : source = proj ⁻¹' base_set)
(target_eq     : target = base_set ×ˢ univ)
(proj_to_fun   : ∀ p ∈ source, (to_local_homeomorph p).1 = proj p)

namespace trivialization

variables {F} (e : trivialization F proj) {x : Z}

/-- Natural identification as a `pretrivialization`. -/
def to_pretrivialization : pretrivialization F proj := { ..e }

instance : has_coe_to_fun (trivialization F proj) (λ _, Z → B × F) := ⟨λ e, e.to_fun⟩
instance : has_coe (trivialization F proj) (pretrivialization F proj) :=
⟨to_pretrivialization⟩

lemma to_pretrivialization_injective :
  function.injective (λ e : trivialization F proj, e.to_pretrivialization) :=
by { intros e e', rw [pretrivialization.ext_iff, trivialization.ext_iff,
  ← local_homeomorph.to_local_equiv_injective.eq_iff], exact id }

@[simp, mfld_simps] lemma coe_coe : ⇑e.to_local_homeomorph = e := rfl
@[simp, mfld_simps] lemma coe_fst (ex : x ∈ e.source) : (e x).1 = proj x := e.proj_to_fun x ex
protected lemma eq_on : eq_on (prod.fst ∘ e) proj e.source := λ x hx, e.coe_fst hx
lemma mem_source : x ∈ e.source ↔ proj x ∈ e.base_set := by rw [e.source_eq, mem_preimage]
lemma coe_fst' (ex : proj x ∈ e.base_set) : (e x).1 = proj x := e.coe_fst (e.mem_source.2 ex)
lemma mk_proj_snd (ex : x ∈ e.source) : (proj x, (e x).2) = e x := prod.ext (e.coe_fst ex).symm rfl
lemma mk_proj_snd' (ex : proj x ∈ e.base_set) : (proj x, (e x).2) = e x :=
prod.ext (e.coe_fst' ex).symm rfl

lemma source_inter_preimage_target_inter (s : set (B × F)) :
  e.source ∩ (e ⁻¹' (e.target ∩ s)) = e.source ∩ (e ⁻¹' s) :=
e.to_local_homeomorph.source_inter_preimage_target_inter s

@[simp, mfld_simps] lemma coe_mk (e : local_homeomorph Z (B × F)) (i j k l m) (x : Z) :
  (trivialization.mk e i j k l m : trivialization F proj) x = e x := rfl

lemma mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.base_set :=
e.to_pretrivialization.mem_target

lemma map_target {x : B × F} (hx : x ∈ e.target) : e.to_local_homeomorph.symm x ∈ e.source :=
e.to_local_homeomorph.map_target hx

lemma proj_symm_apply {x : B × F} (hx : x ∈ e.target) : proj (e.to_local_homeomorph.symm x) = x.1 :=
e.to_pretrivialization.proj_symm_apply hx

lemma proj_symm_apply' {b : B} {x : F}
  (hx : b ∈ e.base_set) : proj (e.to_local_homeomorph.symm (b, x)) = b :=
e.to_pretrivialization.proj_symm_apply' hx

lemma proj_surj_on_base_set [nonempty F] : set.surj_on proj e.source e.base_set :=
e.to_pretrivialization.proj_surj_on_base_set

lemma apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.to_local_homeomorph.symm x) = x :=
e.to_local_homeomorph.right_inv hx

lemma apply_symm_apply'
  {b : B} {x : F} (hx : b ∈ e.base_set) : e (e.to_local_homeomorph.symm (b, x)) = (b, x) :=
e.to_pretrivialization.apply_symm_apply' hx

@[simp, mfld_simps] lemma symm_apply_mk_proj (ex : x ∈ e.source) :
  e.to_local_homeomorph.symm (proj x, (e x).2) = x :=
e.to_pretrivialization.symm_apply_mk_proj ex

lemma symm_trans_source_eq (e e' : trivialization F proj) :
  (e.to_local_equiv.symm.trans e'.to_local_equiv).source = (e.base_set ∩ e'.base_set) ×ˢ univ :=
pretrivialization.symm_trans_source_eq e.to_pretrivialization e'

lemma symm_trans_target_eq (e e' : trivialization F proj) :
  (e.to_local_equiv.symm.trans e'.to_local_equiv).target = (e.base_set ∩ e'.base_set) ×ˢ univ :=
pretrivialization.symm_trans_target_eq e.to_pretrivialization e'

lemma coe_fst_eventually_eq_proj (ex : x ∈ e.source) : prod.fst ∘ e =ᶠ[𝓝 x] proj  :=
mem_nhds_iff.2 ⟨e.source, λ y hy, e.coe_fst hy, e.open_source, ex⟩

lemma coe_fst_eventually_eq_proj' (ex : proj x ∈ e.base_set) : prod.fst ∘ e =ᶠ[𝓝 x] proj :=
e.coe_fst_eventually_eq_proj (e.mem_source.2 ex)

lemma map_proj_nhds (ex : x ∈ e.source) : map proj (𝓝 x) = 𝓝 (proj x) :=
by rw [← e.coe_fst ex, ← map_congr (e.coe_fst_eventually_eq_proj ex), ← map_map, ← e.coe_coe,
  e.to_local_homeomorph.map_nhds_eq ex, map_fst_nhds]

lemma preimage_subset_source {s : set B} (hb : s ⊆ e.base_set) : proj ⁻¹' s ⊆ e.source :=
λ p hp, e.mem_source.mpr (hb hp)

lemma image_preimage_eq_prod_univ {s : set B} (hb : s ⊆ e.base_set) :
  e '' (proj ⁻¹' s) = s ×ˢ univ :=
subset.antisymm (image_subset_iff.mpr (λ p hp,
  ⟨(e.proj_to_fun p (e.preimage_subset_source hb hp)).symm ▸ hp, trivial⟩)) (λ p hp,
  let hp' : p ∈ e.target := e.mem_target.mpr (hb hp.1) in
  ⟨e.inv_fun p, mem_preimage.mpr ((e.proj_symm_apply hp').symm ▸ hp.1), e.apply_symm_apply hp'⟩)

/-- The preimage of a subset of the base set is homeomorphic to the product with the fiber. -/
def preimage_homeomorph {s : set B} (hb : s ⊆ e.base_set) : proj ⁻¹' s ≃ₜ s × F :=
(e.to_local_homeomorph.homeomorph_of_image_subset_source (e.preimage_subset_source hb)
  (e.image_preimage_eq_prod_univ hb)).trans
  ((homeomorph.set.prod s univ).trans ((homeomorph.refl s).prod_congr (homeomorph.set.univ F)))

@[simp] lemma preimage_homeomorph_apply {s : set B} (hb : s ⊆ e.base_set) (p : proj ⁻¹' s) :
  e.preimage_homeomorph hb p = (⟨proj p, p.2⟩, (e p).2) :=
prod.ext (subtype.ext (e.proj_to_fun p (e.mem_source.mpr (hb p.2)))) rfl

@[simp] lemma preimage_homeomorph_symm_apply {s : set B} (hb : s ⊆ e.base_set) (p : s × F) :
  (e.preimage_homeomorph hb).symm p = ⟨e.symm (p.1, p.2), ((e.preimage_homeomorph hb).symm p).2⟩ :=
rfl

/-- The source is homeomorphic to the product of the base set with the fiber. -/
def source_homeomorph_base_set_prod : e.source ≃ₜ e.base_set × F :=
(homeomorph.set_congr e.source_eq).trans (e.preimage_homeomorph subset_rfl)

@[simp] lemma source_homeomorph_base_set_prod_apply (p : e.source) :
  e.source_homeomorph_base_set_prod p = (⟨proj p, e.mem_source.mp p.2⟩, (e p).2) :=
e.preimage_homeomorph_apply subset_rfl ⟨p, e.mem_source.mp p.2⟩

@[simp] lemma source_homeomorph_base_set_prod_symm_apply (p : e.base_set × F) :
  e.source_homeomorph_base_set_prod.symm p =
    ⟨e.symm (p.1, p.2), (e.source_homeomorph_base_set_prod.symm p).2⟩ :=
rfl

/-- Each fiber of a trivialization is homeomorphic to the specified fiber. -/
def preimage_singleton_homeomorph {b : B} (hb : b ∈ e.base_set) : proj ⁻¹' {b} ≃ₜ F :=
(e.preimage_homeomorph (set.singleton_subset_iff.mpr hb)).trans (((homeomorph.homeomorph_of_unique
  ({b} : set B) punit).prod_congr (homeomorph.refl F)).trans (homeomorph.punit_prod F))

@[simp] lemma preimage_singleton_homeomorph_apply {b : B} (hb : b ∈ e.base_set)
  (p : proj ⁻¹' {b}) : e.preimage_singleton_homeomorph hb p = (e p).2 :=
rfl

@[simp] lemma preimage_singleton_homeomorph_symm_apply {b : B} (hb : b ∈ e.base_set) (p : F) :
  (e.preimage_singleton_homeomorph hb).symm p =
    ⟨e.symm (b, p), by rw [mem_preimage, e.proj_symm_apply' hb, mem_singleton_iff]⟩ :=
rfl

/-- In the domain of a bundle trivialization, the projection is continuous-/
lemma continuous_at_proj (ex : x ∈ e.source) : continuous_at proj x :=
(e.map_proj_nhds ex).le

/-- Composition of a `trivialization` and a `homeomorph`. -/
protected def comp_homeomorph {Z' : Type*} [topological_space Z'] (h : Z' ≃ₜ Z) :
  trivialization F (proj ∘ h) :=
{ to_local_homeomorph := h.to_local_homeomorph.trans e.to_local_homeomorph,
  base_set := e.base_set,
  open_base_set := e.open_base_set,
  source_eq := by simp [e.source_eq, preimage_preimage],
  target_eq := by simp [e.target_eq],
  proj_to_fun := λ p hp,
    have hp : h p ∈ e.source, by simpa using hp,
    by simp [hp] }

/-- Read off the continuity of a function `f : Z → X` at `z : Z` by transferring via a
trivialization of `Z` containing `z`. -/
lemma continuous_at_of_comp_right {X : Type*} [topological_space X] {f : Z → X} {z : Z}
  (e : trivialization F proj) (he : proj z ∈ e.base_set)
  (hf : continuous_at (f ∘ e.to_local_equiv.symm) (e z)) :
  continuous_at f z :=
begin
  have hez : z ∈ e.to_local_equiv.symm.target,
  { rw [local_equiv.symm_target, e.mem_source],
    exact he },
  rwa [e.to_local_homeomorph.symm.continuous_at_iff_continuous_at_comp_right hez,
   local_homeomorph.symm_symm]
end

/-- Read off the continuity of a function `f : X → Z` at `x : X` by transferring via a
trivialization of `Z` containing `f x`. -/
lemma continuous_at_of_comp_left {X : Type*} [topological_space X] {f : X → Z} {x : X}
  (e : trivialization F proj) (hf_proj : continuous_at (proj ∘ f) x) (he : proj (f x) ∈ e.base_set)
  (hf : continuous_at (e ∘ f) x) :
  continuous_at f x :=
begin
  rw e.to_local_homeomorph.continuous_at_iff_continuous_at_comp_left,
  { exact hf },
  rw [e.source_eq, ← preimage_comp],
  exact hf_proj.preimage_mem_nhds (e.open_base_set.mem_nhds he),
end

variables {E} (e' : trivialization F (π E)) {x' : total_space E} {b : B} {y : E b}

protected lemma continuous_on : continuous_on e' e'.source := e'.continuous_to_fun

lemma coe_mem_source : ↑y ∈ e'.source ↔ b ∈ e'.base_set := e'.mem_source

lemma open_target : is_open e'.target :=
by { rw e'.target_eq, exact e'.open_base_set.prod is_open_univ }

@[simp, mfld_simps] lemma coe_coe_fst (hb : b ∈ e'.base_set) : (e' y).1 = b :=
e'.coe_fst (e'.mem_source.2 hb)

lemma mk_mem_target {y : F} : (b, y) ∈ e'.target ↔ b ∈ e'.base_set :=
e'.to_pretrivialization.mem_target

lemma symm_apply_apply {x : total_space E} (hx : x ∈ e'.source) :
  e'.to_local_homeomorph.symm (e' x) = x :=
e'.to_local_equiv.left_inv hx

@[simp, mfld_simps] lemma symm_coe_proj {x : B} {y : F}
  (e : trivialization F (π E)) (h : x ∈ e.base_set) :
  (e.to_local_homeomorph.symm (x, y)).1 = x := e.proj_symm_apply' h

section has_zero
variables [∀ x, has_zero (E x)]

/-- A fiberwise inverse to `e'`. The function `F → E x` that induces a local inverse
`B × F → total_space E` of `e'` on `e'.base_set`. It is defined to be `0` outside `e'.base_set`. -/
protected noncomputable def symm (e : trivialization F (π E)) (b : B) (y : F) : E b :=
e.to_pretrivialization.symm b y

lemma symm_apply (e : trivialization F (π E)) {b : B} (hb : b ∈ e.base_set) (y : F) :
  e.symm b y = cast (congr_arg E (e.symm_coe_proj hb)) (e.to_local_homeomorph.symm (b, y)).2 :=
dif_pos hb

lemma symm_apply_of_not_mem (e : trivialization F (π E)) {b : B} (hb : b ∉ e.base_set) (y : F) :
  e.symm b y = 0 :=
dif_neg hb

lemma mk_symm (e : trivialization F (π E)) {b : B} (hb : b ∈ e.base_set) (y : F) :
  total_space_mk b (e.symm b y) = e.to_local_homeomorph.symm (b, y) :=
e.to_pretrivialization.mk_symm hb y

lemma symm_proj_apply (e : trivialization F (π E)) (z : total_space E)
  (hz : z.proj ∈ e.base_set) : e.symm z.proj (e z).2 = z.2 :=
e.to_pretrivialization.symm_proj_apply z hz

lemma symm_apply_apply_mk (e : trivialization F (π E)) {b : B} (hb : b ∈ e.base_set) (y : E b) :
  e.symm b (e (total_space_mk b y)).2 = y :=
e.symm_proj_apply (total_space_mk b y) hb

lemma apply_mk_symm (e : trivialization F (π E)) {b : B} (hb : b ∈ e.base_set) (y : F) :
  e (total_space_mk b (e.symm b y)) = (b, y) :=
e.to_pretrivialization.apply_mk_symm hb y

lemma continuous_on_symm (e : trivialization F (π E)) :
  continuous_on (λ z : B × F, total_space_mk z.1 (e.symm z.1 z.2)) (e.base_set ×ˢ univ) :=
begin
  have : ∀ (z : B × F) (hz : z ∈ e.base_set ×ˢ (univ : set F)),
    total_space_mk z.1 (e.symm z.1 z.2) = e.to_local_homeomorph.symm z,
  { rintro x ⟨hx : x.1 ∈ e.base_set, _⟩, simp_rw [e.mk_symm hx, prod.mk.eta] },
  refine continuous_on.congr _ this,
  rw [← e.target_eq],
  exact e.to_local_homeomorph.continuous_on_symm
end

end has_zero

/-- If `e` is a `trivialization` of `proj : Z → B` with fiber `F` and `h` is a homeomorphism
`F ≃ₜ F'`, then `e.trans_fiber_homeomorph h` is the trivialization of `proj` with the fiber `F'`
that sends `p : Z` to `((e p).1, h (e p).2)`. -/
def trans_fiber_homeomorph {F' : Type*} [topological_space F']
  (e : trivialization F proj) (h : F ≃ₜ F') : trivialization F' proj :=
{ to_local_homeomorph := e.to_local_homeomorph.trans_homeomorph $ (homeomorph.refl _).prod_congr h,
  base_set := e.base_set,
  open_base_set := e.open_base_set,
  source_eq := e.source_eq,
  target_eq := by simp [e.target_eq, prod_univ, preimage_preimage],
  proj_to_fun := e.proj_to_fun }

@[simp] lemma trans_fiber_homeomorph_apply {F' : Type*} [topological_space F']
  (e : trivialization F proj) (h : F ≃ₜ F') (x : Z) :
  e.trans_fiber_homeomorph h x = ((e x).1, h (e x).2) :=
rfl

/-- Coordinate transformation in the fiber induced by a pair of bundle trivializations. See also
`trivialization.coord_change_homeomorph` for a version bundled as `F ≃ₜ F`. -/
def coord_change (e₁ e₂ : trivialization F proj) (b : B) (x : F) : F :=
(e₂ $ e₁.to_local_homeomorph.symm (b, x)).2

lemma mk_coord_change
  (e₁ e₂ : trivialization F proj) {b : B}
  (h₁ : b ∈ e₁.base_set) (h₂ : b ∈ e₂.base_set) (x : F) :
  (b, e₁.coord_change e₂ b x) = e₂ (e₁.to_local_homeomorph.symm (b, x)) :=
begin
  refine prod.ext _ rfl,
  rw [e₂.coe_fst', ← e₁.coe_fst', e₁.apply_symm_apply' h₁],
  { rwa [e₁.proj_symm_apply' h₁] },
  { rwa [e₁.proj_symm_apply' h₁] }
end

lemma coord_change_apply_snd
  (e₁ e₂ : trivialization F proj) {p : Z}
  (h : proj p ∈ e₁.base_set) :
  e₁.coord_change e₂ (proj p) (e₁ p).snd = (e₂ p).snd :=
by rw [coord_change, e₁.symm_apply_mk_proj (e₁.mem_source.2 h)]

lemma coord_change_same_apply
  (e : trivialization F proj) {b : B} (h : b ∈ e.base_set) (x : F) :
  e.coord_change e b x = x :=
by rw [coord_change, e.apply_symm_apply' h]

lemma coord_change_same
  (e : trivialization F proj) {b : B} (h : b ∈ e.base_set) :
  e.coord_change e b = id :=
funext $ e.coord_change_same_apply h

lemma coord_change_coord_change
  (e₁ e₂ e₃ : trivialization F proj) {b : B}
  (h₁ : b ∈ e₁.base_set) (h₂ : b ∈ e₂.base_set) (x : F) :
  e₂.coord_change e₃ b (e₁.coord_change e₂ b x) = e₁.coord_change e₃ b x :=
begin
  rw [coord_change, e₁.mk_coord_change _ h₁ h₂, ← e₂.coe_coe,
    e₂.to_local_homeomorph.left_inv, coord_change],
  rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]
end

lemma continuous_coord_change (e₁ e₂ : trivialization F proj) {b : B}
  (h₁ : b ∈ e₁.base_set) (h₂ : b ∈ e₂.base_set) :
  continuous (e₁.coord_change e₂ b) :=
begin
  refine continuous_snd.comp (e₂.to_local_homeomorph.continuous_on.comp_continuous
    (e₁.to_local_homeomorph.continuous_on_symm.comp_continuous _ _) _),
  { exact continuous_const.prod_mk continuous_id },
  { exact λ x, e₁.mem_target.2 h₁ },
  { intro x,
    rwa [e₂.mem_source, e₁.proj_symm_apply' h₁] }
end

/-- Coordinate transformation in the fiber induced by a pair of bundle trivializations,
as a homeomorphism. -/
protected def coord_change_homeomorph
  (e₁ e₂ : trivialization F proj) {b : B} (h₁ : b ∈ e₁.base_set) (h₂ : b ∈ e₂.base_set) :
  F ≃ₜ F :=
{ to_fun := e₁.coord_change e₂ b,
  inv_fun := e₂.coord_change e₁ b,
  left_inv := λ x, by simp only [*, coord_change_coord_change, coord_change_same_apply],
  right_inv := λ x, by simp only [*, coord_change_coord_change, coord_change_same_apply],
  continuous_to_fun := e₁.continuous_coord_change e₂ h₁ h₂,
  continuous_inv_fun := e₂.continuous_coord_change e₁ h₂ h₁ }

@[simp] lemma coord_change_homeomorph_coe
  (e₁ e₂ : trivialization F proj) {b : B} (h₁ : b ∈ e₁.base_set) (h₂ : b ∈ e₂.base_set) :
  ⇑(e₁.coord_change_homeomorph e₂ h₁ h₂) = e₁.coord_change e₂ b :=
rfl

variables {F} {B' : Type*} [topological_space B']

lemma is_image_preimage_prod (e : trivialization F proj) (s : set B) :
  e.to_local_homeomorph.is_image (proj ⁻¹' s) (s ×ˢ univ) :=
λ x hx, by simp [e.coe_fst', hx]

/-- Restrict a `trivialization` to an open set in the base. `-/
protected def restr_open (e : trivialization F proj) (s : set B)
  (hs : is_open s) : trivialization F proj :=
{ to_local_homeomorph := ((e.is_image_preimage_prod s).symm.restr
    (is_open.inter e.open_target (hs.prod is_open_univ))).symm,
  base_set := e.base_set ∩ s,
  open_base_set := is_open.inter e.open_base_set hs,
  source_eq := by simp [e.source_eq],
  target_eq := by simp [e.target_eq, prod_univ],
  proj_to_fun := λ p hp, e.proj_to_fun p hp.1 }

section piecewise

lemma frontier_preimage (e : trivialization F proj) (s : set B) :
  e.source ∩ frontier (proj ⁻¹' s) = proj ⁻¹' (e.base_set ∩ frontier s) :=
by rw [← (e.is_image_preimage_prod s).frontier.preimage_eq, frontier_prod_univ_eq,
  (e.is_image_preimage_prod _).preimage_eq, e.source_eq, preimage_inter]

/-- Given two bundle trivializations `e`, `e'` of `proj : Z → B` and a set `s : set B` such that
the base sets of `e` and `e'` intersect `frontier s` on the same set and `e p = e' p` whenever
`proj p ∈ e.base_set ∩ frontier s`, `e.piecewise e' s Hs Heq` is the bundle trivialization over
`set.ite s e.base_set e'.base_set` that is equal to `e` on `proj ⁻¹ s` and is equal to `e'`
otherwise. -/
noncomputable def piecewise (e e' : trivialization F proj) (s : set B)
  (Hs : e.base_set ∩ frontier s = e'.base_set ∩ frontier s)
  (Heq : eq_on e e' $ proj ⁻¹' (e.base_set ∩ frontier s)) :
  trivialization F proj :=
{ to_local_homeomorph := e.to_local_homeomorph.piecewise e'.to_local_homeomorph
    (proj ⁻¹' s) (s ×ˢ univ) (e.is_image_preimage_prod s) (e'.is_image_preimage_prod s)
    (by rw [e.frontier_preimage, e'.frontier_preimage, Hs])
    (by rwa e.frontier_preimage),
  base_set := s.ite e.base_set e'.base_set,
  open_base_set := e.open_base_set.ite e'.open_base_set Hs,
  source_eq := by simp [e.source_eq, e'.source_eq],
  target_eq := by simp [e.target_eq, e'.target_eq, prod_univ],
  proj_to_fun := by rintro p (⟨he, hs⟩|⟨he, hs⟩); simp * }

/-- Given two bundle trivializations `e`, `e'` of a topological fiber bundle `proj : Z → B`
over a linearly ordered base `B` and a point `a ∈ e.base_set ∩ e'.base_set` such that
`e` equals `e'` on `proj ⁻¹' {a}`, `e.piecewise_le_of_eq e' a He He' Heq` is the bundle
trivialization over `set.ite (Iic a) e.base_set e'.base_set` that is equal to `e` on points `p`
such that `proj p ≤ a` and is equal to `e'` otherwise. -/
noncomputable def piecewise_le_of_eq [linear_order B] [order_topology B]
  (e e' : trivialization F proj) (a : B) (He : a ∈ e.base_set) (He' : a ∈ e'.base_set)
  (Heq : ∀ p, proj p = a → e p = e' p) :
  trivialization F proj :=
e.piecewise e' (Iic a)
  (set.ext $ λ x, and.congr_left_iff.2 $ λ hx,
    by simp [He, He', mem_singleton_iff.1 (frontier_Iic_subset _ hx)])
  (λ p hp, Heq p $ frontier_Iic_subset _ hp.2)

/-- Given two bundle trivializations `e`, `e'` of a topological fiber bundle `proj : Z → B` over a
linearly ordered base `B` and a point `a ∈ e.base_set ∩ e'.base_set`, `e.piecewise_le e' a He He'`
is the bundle trivialization over `set.ite (Iic a) e.base_set e'.base_set` that is equal to `e` on
points `p` such that `proj p ≤ a` and is equal to `((e' p).1, h (e' p).2)` otherwise, where
`h = `e'.coord_change_homeomorph e _ _` is the homeomorphism of the fiber such that
`h (e' p).2 = (e p).2` whenever `e p = a`. -/
noncomputable def piecewise_le [linear_order B] [order_topology B]
  (e e' : trivialization F proj) (a : B) (He : a ∈ e.base_set) (He' : a ∈ e'.base_set) :
  trivialization F proj :=
e.piecewise_le_of_eq (e'.trans_fiber_homeomorph (e'.coord_change_homeomorph e He' He))
  a He He' $ by { unfreezingI {rintro p rfl },
    ext1,
    { simp [e.coe_fst', e'.coe_fst', *] },
    { simp [e'.coord_change_apply_snd, *] } }

/-- Given two bundle trivializations `e`, `e'` over disjoint sets, `e.disjoint_union e' H` is the
bundle trivialization over the union of the base sets that agrees with `e` and `e'` over their
base sets. -/
noncomputable def disjoint_union (e e' : trivialization F proj)
  (H : disjoint e.base_set e'.base_set) :
  trivialization F proj :=
{ to_local_homeomorph := e.to_local_homeomorph.disjoint_union e'.to_local_homeomorph
    (by { rw [e.source_eq, e'.source_eq], exact H.preimage _, })
    (by { rw [e.target_eq, e'.target_eq, disjoint_iff_inf_le],
          intros x hx, exact H.le_bot ⟨hx.1.1, hx.2.1⟩ }),
  base_set := e.base_set ∪ e'.base_set,
  open_base_set := is_open.union e.open_base_set e'.open_base_set,
  source_eq := congr_arg2 (∪) e.source_eq e'.source_eq,
  target_eq := (congr_arg2 (∪) e.target_eq e'.target_eq).trans union_prod.symm,
  proj_to_fun :=
    begin
      rintro p (hp|hp'),
      { show (e.source.piecewise e e' p).1 = proj p,
        rw [piecewise_eq_of_mem, e.coe_fst]; exact hp },
      { show (e.source.piecewise e e' p).1 = proj p,
        rw [piecewise_eq_of_not_mem, e'.coe_fst hp'],
        simp only [e.source_eq, e'.source_eq] at hp' ⊢,
        exact λ h, H.le_bot ⟨h, hp'⟩ }
    end }

end piecewise

end trivialization
