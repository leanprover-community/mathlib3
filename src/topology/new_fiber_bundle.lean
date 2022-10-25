/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import data.bundle
import topology.local_homeomorph

/-!
# Fiber bundles

Given a "base" topological space `B` and a family `E : B → Type*` for which `bundle.total_space E`
(a type synonym for `Σ b, E b`) carries a topological space structure, a topological fiber bundle
structure for `total_space E` with fiber `F` is a system of local homeomorphisms to `B × F`, each
respecting the fiber structure ("local trivializations" of `total_space E`). We define an object
`fiber_bundle F p` carrying the data of these local trivializations.

-/

variables {ι : Type*} {B : Type*} {F : Type*}

open topological_space filter set bundle
open_locale topological_space classical

noncomputable theory

/-! ### Pretrivializations -/

section general

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

end pretrivialization

/-! ### Trivializations -/

variable [topological_space Z]

/--
A structure extending local homeomorphisms, defining a local trivialization of a projection
`proj : Z → B` with fiber `F`, as a local homeomorphism between `Z` and `B × F` defined between two
sets of the form `proj ⁻¹' base_set` and `base_set × F`, acting trivially on the first coordinate.
-/
@[ext, nolint has_nonempty_instance]
structure trivialization (proj : Z → B) extends local_homeomorph Z (B × F) :=
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
def comp_homeomorph {Z' : Type*} [topological_space Z'] (h : Z' ≃ₜ Z) :
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

end trivialization

/-! ### Pretrivializations and trivializations for a sigma-type -/

variables (E : B → Type*)

section zero

namespace pretrivialization
variables {E B F} [∀ b, has_zero (E b)] (e : pretrivialization F (@total_space.proj B E))

/-- A fiberwise inverse to `e`. This is the function `F → E b` that induces a local inverse
`B × F → total_space E` of `e` on `e.base_set`. It is defined to be `0` outside `e.base_set`. -/
protected def symm (b : B) (y : F) : E b :=
if hb : b ∈ e.base_set
then cast (congr_arg E (e.proj_symm_apply' hb)) (e.to_local_equiv.symm (b, y)).2
else 0

lemma symm_apply {b : B} (hb : b ∈ e.base_set) (y : F) :
  e.symm b y = cast (congr_arg E (e.proj_symm_apply' hb)) (e.to_local_equiv.symm (b, y)).2 :=
dif_pos hb

lemma symm_apply_of_not_mem {b : B} (hb : b ∉ e.base_set) (y : F) :
  e.symm b y = 0 :=
dif_neg hb

lemma coe_symm_of_not_mem {b : B} (hb : b ∉ e.base_set) :
  (e.symm b : F → E b) = 0 :=
funext $ λ y, dif_neg hb

lemma mk_symm {b : B} (hb : b ∈ e.base_set) (y : F) :
  total_space_mk b (e.symm b y) = e.to_local_equiv.symm (b, y) :=
by rw [e.symm_apply hb, total_space.mk_cast, total_space.eta]

lemma symm_proj_apply (z : total_space E)
  (hz : z.proj ∈ e.base_set) : e.symm z.proj (e z).2 = z.2 :=
by rw [e.symm_apply hz, cast_eq_iff_heq, e.mk_proj_snd' hz,
  e.symm_apply_apply (e.mem_source.mpr hz)]

lemma symm_apply_apply_mk {b : B} (hb : b ∈ e.base_set) (y : E b) :
  e.symm b (e (total_space_mk b y)).2 = y :=
e.symm_proj_apply (total_space_mk b y) hb

lemma apply_mk_symm {b : B} (hb : b ∈ e.base_set) (y : F) :
  e (total_space_mk b (e.symm b y)) = (b, y) :=
by { rw [e.mk_symm hb, e.apply_symm_apply (e.mem_target.mpr _)], exact hb }

end pretrivialization

namespace trivialization
variables [topological_space (total_space E)]
variables {E B F} [∀ b, has_zero (E b)] (e : trivialization F (@total_space.proj B E))

/-- A fiberwise inverse to `e`. The function `F → E x` that induces a local inverse
  `B × F → total_space E` of `e` on `e.base_set`. It is defined to be `0` outside `e.base_set`. -/
protected def symm (b : B) (y : F) : E b :=
e.to_pretrivialization.symm b y

lemma symm_apply {b : B} (hb : b ∈ e.base_set) (y : F) :
  e.symm b y = cast (congr_arg E (e.proj_symm_apply' hb)) (e.to_local_homeomorph.symm (b, y)).2 :=
dif_pos hb

lemma symm_apply_of_not_mem {b : B} (hb : b ∉ e.base_set) (y : F) :
  e.symm b y = 0 :=
dif_neg hb

lemma mk_symm {b : B} (hb : b ∈ e.base_set) (y : F) :
  total_space_mk b (e.symm b y) = e.to_local_homeomorph.symm (b, y) :=
e.to_pretrivialization.mk_symm hb y

lemma symm_proj_apply (z : total_space E)
  (hz : z.proj ∈ e.base_set) : e.symm z.proj (e z).2 = z.2 :=
e.to_pretrivialization.symm_proj_apply z hz

lemma symm_apply_apply_mk {b : B} (hb : b ∈ e.base_set) (y : E b) :
  e.symm b (e (total_space_mk b y)).2 = y :=
e.symm_proj_apply (total_space_mk b y) hb

lemma apply_mk_symm {b : B} (hb : b ∈ e.base_set) (y : F) :
  e (total_space_mk b (e.symm b y)) = (b, y) :=
e.to_pretrivialization.apply_mk_symm hb y

lemma continuous_on_symm :
  continuous_on (λ z : B × F, total_space_mk z.1 (e.symm z.1 z.2)) (e.base_set ×ˢ univ) :=
begin
  have : ∀ (z : B × F) (hz : z ∈ e.base_set ×ˢ (univ : set F)),
    total_space_mk z.1 (e.symm z.1 z.2) = e.to_local_homeomorph.symm z,
  { rintro x ⟨hx : x.1 ∈ e.base_set, _⟩, simp_rw [e.mk_symm hx, prod.mk.eta] },
  refine continuous_on.congr _ this,
  rw [← e.target_eq],
  exact e.to_local_homeomorph.continuous_on_symm
end

end trivialization

end zero

/-! ### Fiber bundles -/

variables [topological_space (total_space E)] [∀ b, topological_space (E b)]

class fiber_bundle :=
(total_space_mk_inducing [] : ∀ (b : B), inducing (@total_space_mk B E b))
(trivialization_atlas [] : set (trivialization F (total_space.proj : total_space E → B)))
(trivialization_at [] : B → trivialization F (total_space.proj : total_space E → B))
(mem_base_set_trivialization_at [] : ∀ b : B, b ∈ (trivialization_at b).base_set)
(trivialization_mem_atlas [] : ∀ b : B, trivialization_at b ∈ trivialization_atlas)

export fiber_bundle

variables {F E} [fiber_bundle F E]

@[class] def mem_trivialization_atlas (e : trivialization F (@total_space.proj B E)) : Prop :=
e ∈ trivialization_atlas F E

namespace fiber_bundle

variables (F)
lemma map_proj_nhds (x : total_space E) : map (@total_space.proj B E) (𝓝 x) = 𝓝 (total_space.proj x) :=
(trivialization_at F E (total_space.proj x)).map_proj_nhds $
  (trivialization_at F E (total_space.proj x)).mem_source.2 $
  mem_base_set_trivialization_at F E (total_space.proj x)

variables (E)
/-- The projection from a topological fiber bundle to its base is continuous. -/
@[continuity] lemma continuous_proj : continuous (@total_space.proj B E) :=
continuous_iff_continuous_at.2 $ λ x, (map_proj_nhds F x).le

/-- The projection from a topological fiber bundle to its base is an open map. -/
lemma is_open_map_proj : is_open_map (@total_space.proj B E) :=
is_open_map.of_nhds_le $ λ x, (map_proj_nhds F x).ge

/-- The projection from a topological fiber bundle with a nonempty fiber to its base is a surjective
map. -/
lemma surjective_proj [nonempty F] : function.surjective (@total_space.proj B E) :=
λ b, let ⟨p, _, hpb⟩ :=
  (trivialization_at F E b).proj_surj_on_base_set (mem_base_set_trivialization_at F E b) in ⟨p, hpb⟩

/-- The projection from a topological fiber bundle with a nonempty fiber to its base is a quotient
map. -/
lemma quotient_map_proj [nonempty F] : quotient_map (@total_space.proj B E) :=
(is_open_map_proj F E).to_quotient_map (continuous_proj F E) (surjective_proj F E)

lemma continuous_total_space_mk (x : B) : continuous (@total_space_mk B E x) :=
(total_space_mk_inducing F E x).continuous

end fiber_bundle

/-- Core data defining a locally trivial topological bundle with fiber `F` over a topological
space `B`. Note that "bundle" is used in its mathematical sense. This is the (computer science)
bundled version, i.e., all the relevant data is contained in the following structure. A family of
local trivializations is indexed by a type `ι`, on open subsets `base_set i` for each `i : ι`.
Trivialization changes from `i` to `j` are given by continuous maps `coord_change i j` from
`base_set i ∩ base_set j` to the set of homeomorphisms of `F`, but we express them as maps
`B → F → F` and require continuity on `(base_set i ∩ base_set j) × F` to avoid the topology on the
space of continuous maps on `F`. -/
@[nolint has_nonempty_instance]
structure fiber_bundle_core (ι : Type*) (B : Type*) [topological_space B]
  (F : Type*) [topological_space F] :=
(base_set          : ι → set B)
(is_open_base_set  : ∀ i, is_open (base_set i))
(index_at          : B → ι)
(mem_base_set_at   : ∀ x, x ∈ base_set (index_at x))
(coord_change      : ι → ι → B → F → F)
(coord_change_self : ∀ i, ∀ x ∈ base_set i, ∀ v, coord_change i i x v = v)
(continuous_on_coord_change : ∀ i j, continuous_on (λp : B × F, coord_change i j p.1 p.2)
                                               (((base_set i) ∩ (base_set j)) ×ˢ univ))
(coord_change_comp : ∀ i j k, ∀ x ∈ (base_set i) ∩ (base_set j) ∩ (base_set k), ∀ v,
  (coord_change j k x) (coord_change i j x v) = coord_change i k x v)

namespace fiber_bundle_core

variables [topological_space B] [topological_space F] (C : fiber_bundle_core ι B F)

include C

/-- The index set of a topological fiber bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments has_nonempty_instance]
def index := ι

/-- The base space of a topological fiber bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments, reducible]
def base := B

/-- The fiber of a topological fiber bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_nonempty_instance]
def fiber (x : B) := F

section fiber_instances
local attribute [reducible] fiber

instance topological_space_fiber (x : B) : topological_space (C.fiber x) := by apply_instance

end fiber_instances

/-- The total space of the topological fiber bundle, as a convenience function for dot notation.
It is by definition equal to `bundle.total_space C.fiber`, a.k.a. `Σ x, C.fiber x` but with a
different name for typeclass inference. -/
@[nolint unused_arguments, reducible]
def total_space := bundle.total_space C.fiber

/-- The projection from the total space of a topological fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps] def proj : C.total_space → B := bundle.total_space.proj

/-- Local homeomorphism version of the trivialization change. -/
def triv_change (i j : ι) : local_homeomorph (B × F) (B × F) :=
{ source      := (C.base_set i ∩ C.base_set j) ×ˢ univ,
  target      := (C.base_set i ∩ C.base_set j) ×ˢ univ,
  to_fun      := λp, ⟨p.1, C.coord_change i j p.1 p.2⟩,
  inv_fun     := λp, ⟨p.1, C.coord_change j i p.1 p.2⟩,
  map_source' := λp hp, by simpa using hp,
  map_target' := λp hp, by simpa using hp,
  left_inv'   := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx,
    rw [C.coord_change_comp, C.coord_change_self],
    { exact hx.1 },
    { simp [hx] }
  end,
  right_inv'  := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx,
    rw [C.coord_change_comp, C.coord_change_self],
    { exact hx.2 },
    { simp [hx] },
  end,
  open_source :=
    (is_open.inter (C.is_open_base_set i) (C.is_open_base_set j)).prod is_open_univ,
  open_target :=
    (is_open.inter (C.is_open_base_set i) (C.is_open_base_set j)).prod is_open_univ,
  continuous_to_fun  :=
    continuous_on.prod continuous_fst.continuous_on (C.continuous_on_coord_change i j),
  continuous_inv_fun := by simpa [inter_comm]
    using continuous_on.prod continuous_fst.continuous_on (C.continuous_on_coord_change j i) }

@[simp, mfld_simps] lemma mem_triv_change_source (i j : ι) (p : B × F) :
  p ∈ (C.triv_change i j).source ↔ p.1 ∈ C.base_set i ∩ C.base_set j :=
by { erw [mem_prod], simp }

/-- Associate to a trivialization index `i : ι` the corresponding trivialization, i.e., a bijection
between `proj ⁻¹ (base_set i)` and `base_set i × F`. As the fiber above `x` is `F` but read in the
chart with index `index_at x`, the trivialization in the fiber above x is by definition the
coordinate change from i to `index_at x`, so it depends on `x`.
The local trivialization will ultimately be a local homeomorphism. For now, we only introduce the
local equiv version, denoted with a prime. In further developments, avoid this auxiliary version,
and use `C.local_triv` instead.
-/
def local_triv_as_local_equiv (i : ι) : local_equiv C.total_space (B × F) :=
{ source      := C.proj ⁻¹' (C.base_set i),
  target      := C.base_set i ×ˢ univ,
  inv_fun     := λp, ⟨p.1, C.coord_change i (C.index_at p.1) p.1 p.2⟩,
  to_fun      := λp, ⟨p.1, C.coord_change (C.index_at p.1) i p.1 p.2⟩,
  map_source' := λp hp,
    by simpa only [set.mem_preimage, and_true, set.mem_univ, set.prod_mk_mem_set_prod_eq] using hp,
  map_target' := λp hp,
    by simpa only [set.mem_preimage, and_true, set.mem_univ, set.mem_prod] using hp,
  left_inv'   := begin
    rintros ⟨x, v⟩ hx,
    change x ∈ C.base_set i at hx,
    dsimp only,
    rw [C.coord_change_comp, C.coord_change_self],
    { exact C.mem_base_set_at _ },
    { simp only [hx, mem_inter_iff, and_self, mem_base_set_at] }
  end,
  right_inv' := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, and_true, mem_univ] at hx,
    rw [C.coord_change_comp, C.coord_change_self],
    { exact hx },
    { simp only [hx, mem_inter_iff, and_self, mem_base_set_at] }
  end }

variable (i : ι)

lemma mem_local_triv_as_local_equiv_source (p : C.total_space) :
  p ∈ (C.local_triv_as_local_equiv i).source ↔ p.1 ∈ C.base_set i :=
iff.rfl

lemma mem_local_triv_as_local_equiv_target (p : B × F) :
  p ∈ (C.local_triv_as_local_equiv i).target ↔ p.1 ∈ C.base_set i :=
by { erw [mem_prod], simp only [and_true, mem_univ] }

lemma local_triv_as_local_equiv_apply (p : C.total_space) :
  (C.local_triv_as_local_equiv i) p = ⟨p.1, C.coord_change (C.index_at p.1) i p.1 p.2⟩ := rfl

/-- The composition of two local trivializations is the trivialization change C.triv_change i j. -/
lemma local_triv_as_local_equiv_trans (i j : ι) :
  (C.local_triv_as_local_equiv i).symm.trans
    (C.local_triv_as_local_equiv j) ≈ (C.triv_change i j).to_local_equiv :=
begin
  split,
  { ext x, simp only [mem_local_triv_as_local_equiv_target] with mfld_simps, refl, },
  { rintros ⟨x, v⟩ hx,
    simp only [triv_change, local_triv_as_local_equiv, local_equiv.symm, true_and, prod.mk.inj_iff,
      prod_mk_mem_set_prod_eq, local_equiv.trans_source, mem_inter_iff, and_true, mem_preimage,
      proj, mem_univ, local_equiv.coe_mk, eq_self_iff_true, local_equiv.coe_trans,
      total_space.proj] at hx ⊢,
    simp only [C.coord_change_comp, hx, mem_inter_iff, and_self, mem_base_set_at], }
end

variable (ι)

/-- Topological structure on the total space of a topological bundle created from core, designed so
that all the local trivialization are continuous. -/
instance to_topological_space : topological_space (bundle.total_space C.fiber) :=
topological_space.generate_from $ ⋃ (i : ι) (s : set (B × F)) (s_open : is_open s),
  {(C.local_triv_as_local_equiv i).source ∩ (C.local_triv_as_local_equiv i) ⁻¹' s}

variable {ι}

lemma open_source' (i : ι) : is_open (C.local_triv_as_local_equiv i).source :=
begin
  apply topological_space.generate_open.basic,
  simp only [exists_prop, mem_Union, mem_singleton_iff],
  refine ⟨i, C.base_set i ×ˢ univ, (C.is_open_base_set i).prod is_open_univ, _⟩,
  ext p,
  simp only [local_triv_as_local_equiv_apply, prod_mk_mem_set_prod_eq, mem_inter_iff, and_self,
    mem_local_triv_as_local_equiv_source, and_true, mem_univ, mem_preimage],
end

open fiber_bundle

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def local_triv (i : ι) : trivialization F C.proj :=
{ base_set      := C.base_set i,
  open_base_set := C.is_open_base_set i,
  source_eq     := rfl,
  target_eq     := rfl,
  proj_to_fun   := λ p hp, by { simp only with mfld_simps, refl },
  open_source := C.open_source' i,
  open_target := (C.is_open_base_set i).prod is_open_univ,
  continuous_to_fun := begin
    rw continuous_on_open_iff (C.open_source' i),
    assume s s_open,
    apply topological_space.generate_open.basic,
    simp only [exists_prop, mem_Union, mem_singleton_iff],
    exact ⟨i, s, s_open, rfl⟩
  end,
  continuous_inv_fun := begin
    apply continuous_on_open_of_generate_from ((C.is_open_base_set i).prod is_open_univ),
    assume t ht,
    simp only [exists_prop, mem_Union, mem_singleton_iff] at ht,
    obtain ⟨j, s, s_open, ts⟩ : ∃ j s, is_open s ∧ t =
      (C.local_triv_as_local_equiv j).source ∩ (C.local_triv_as_local_equiv j) ⁻¹' s := ht,
    rw ts,
    simp only [local_equiv.right_inv, preimage_inter, local_equiv.left_inv],
    let e := C.local_triv_as_local_equiv i,
    let e' := C.local_triv_as_local_equiv j,
    let f := e.symm.trans e',
    have : is_open (f.source ∩ f ⁻¹' s),
    { rw [(C.local_triv_as_local_equiv_trans i j).source_inter_preimage_eq],
      exact (continuous_on_open_iff (C.triv_change i j).open_source).1
        ((C.triv_change i j).continuous_on) _ s_open },
    convert this using 1,
    dsimp [local_equiv.trans_source],
    rw [← preimage_comp, inter_assoc],
    refl,
  end,
  to_local_equiv := C.local_triv_as_local_equiv i }

/-- Preferred local trivialization of a fiber bundle constructed from core, at a given point, as
a bundle trivialization -/
def local_triv_at (b : B) : trivialization F C.proj :=
C.local_triv (C.index_at b)

@[simp, mfld_simps] lemma local_triv_at_def (b : B) :
  C.local_triv (C.index_at b) = C.local_triv_at b := rfl

/-- If an element of `F` is invariant under all coordinate changes, then one can define a
corresponding section of the fiber bundle, which is continuous. This applies in particular to the
zero section of a vector bundle. Another example (not yet defined) would be the identity
section of the endomorphism bundle of a vector bundle. -/
lemma continuous_const_section (v : F)
  (h : ∀ i j, ∀ x ∈ (C.base_set i) ∩ (C.base_set j), C.coord_change i j x v = v) :
  continuous (show B → C.total_space, from λ x, ⟨x, v⟩) :=
begin
  apply continuous_iff_continuous_at.2 (λ x, _),
  have A : C.base_set (C.index_at x) ∈ 𝓝 x :=
    is_open.mem_nhds (C.is_open_base_set (C.index_at x)) (C.mem_base_set_at x),
  apply ((C.local_triv_at x).to_local_homeomorph.continuous_at_iff_continuous_at_comp_left _).2,
  { simp only [(∘)] with mfld_simps,
    apply continuous_at_id.prod,
    have : continuous_on (λ (y : B), v) (C.base_set (C.index_at x)) := continuous_on_const,
    apply (this.congr _).continuous_at A,
    assume y hy,
    simp only [h, hy, mem_base_set_at] with mfld_simps },
  { exact A }
end

@[simp, mfld_simps] lemma local_triv_as_local_equiv_coe :
  ⇑(C.local_triv_as_local_equiv i) = C.local_triv i := rfl

@[simp, mfld_simps] lemma local_triv_as_local_equiv_source :
  (C.local_triv_as_local_equiv i).source = (C.local_triv i).source := rfl

@[simp, mfld_simps] lemma local_triv_as_local_equiv_target :
  (C.local_triv_as_local_equiv i).target = (C.local_triv i).target := rfl

@[simp, mfld_simps] lemma local_triv_as_local_equiv_symm :
  (C.local_triv_as_local_equiv i).symm = (C.local_triv i).to_local_equiv.symm := rfl

@[simp, mfld_simps] lemma base_set_at : C.base_set i = (C.local_triv i).base_set := rfl

@[simp, mfld_simps] lemma local_triv_apply (p : C.total_space) :
  (C.local_triv i) p = ⟨p.1, C.coord_change (C.index_at p.1) i p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma local_triv_at_apply (p : C.total_space) :
  ((C.local_triv_at p.1) p) = ⟨p.1, p.2⟩ :=
by { rw [local_triv_at, local_triv_apply, coord_change_self], exact C.mem_base_set_at p.1 }

@[simp, mfld_simps] lemma local_triv_at_apply_mk (b : B) (a : F) :
  ((C.local_triv_at b) ⟨b, a⟩) = ⟨b, a⟩ :=
C.local_triv_at_apply _

@[simp, mfld_simps] lemma mem_local_triv_source (p : C.total_space) :
  p ∈ (C.local_triv i).source ↔ p.1 ∈ (C.local_triv i).base_set := iff.rfl

@[simp, mfld_simps] lemma mem_local_triv_at_source (p : C.total_space) (b : B) :
  p ∈ (C.local_triv_at b).source ↔ p.1 ∈ (C.local_triv_at b).base_set := iff.rfl

@[simp, mfld_simps] lemma mem_local_triv_target (p : B × F) :
  p ∈ (C.local_triv i).target ↔ p.1 ∈ (C.local_triv i).base_set :=
trivialization.mem_target _

@[simp, mfld_simps] lemma mem_local_triv_at_target (p : B × F) (b : B) :
  p ∈ (C.local_triv_at b).target ↔ p.1 ∈ (C.local_triv_at b).base_set :=
trivialization.mem_target _

@[simp, mfld_simps] lemma local_triv_symm_apply (p : B × F) :
  (C.local_triv i).to_local_homeomorph.symm p =
    ⟨p.1, C.coord_change i (C.index_at p.1) p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma mem_local_triv_at_base_set (b : B) :
  b ∈ (C.local_triv_at b).base_set :=
by { rw [local_triv_at, ←base_set_at], exact C.mem_base_set_at b, }

/-- The inclusion of a fiber into the total space is a continuous map. -/
@[continuity]
lemma continuous_total_space_mk (b : B) :
  continuous (total_space_mk b : C.fiber b → bundle.total_space C.fiber) :=
begin
  rw [continuous_iff_le_induced, fiber_bundle_core.to_topological_space],
  apply le_induced_generate_from,
  simp only [total_space_mk, mem_Union, mem_singleton_iff, local_triv_as_local_equiv_source,
    local_triv_as_local_equiv_coe],
  rintros s ⟨i, t, ht, rfl⟩,
  rw [←((C.local_triv i).source_inter_preimage_target_inter t), preimage_inter, ←preimage_comp,
    trivialization.source_eq],
  apply is_open.inter,
  { simp only [total_space.proj, proj, ←preimage_comp],
    by_cases (b ∈ (C.local_triv i).base_set),
    { rw preimage_const_of_mem h, exact is_open_univ, },
    { rw preimage_const_of_not_mem h, exact is_open_empty, }},
  { simp only [function.comp, local_triv_apply],
    rw [preimage_inter, preimage_comp],
    by_cases (b ∈ C.base_set i),
    { have hc : continuous (λ (x : C.fiber b), (C.coord_change (C.index_at b) i b) x),
        from (C.continuous_on_coord_change (C.index_at b) i).comp_continuous
          (continuous_const.prod_mk continuous_id) (λ x, ⟨⟨C.mem_base_set_at b, h⟩, mem_univ x⟩),
      exact (((C.local_triv i).open_target.inter ht).preimage (continuous.prod.mk b)).preimage hc },
    { rw [(C.local_triv i).target_eq, ←base_set_at, mk_preimage_prod_right_eq_empty h,
        preimage_empty, empty_inter],
      exact is_open_empty, }}
end

/-- A topological fiber bundle constructed from core is indeed a topological fiber bundle. -/
instance fiber_bundle : fiber_bundle F C.fiber :=
{ total_space_mk_inducing := λ b, ⟨ begin refine le_antisymm _ (λ s h, _),
    { rw ←continuous_iff_le_induced,
      exact continuous_total_space_mk C b, },
    { refine is_open_induced_iff.mpr ⟨(C.local_triv_at b).source ∩ (C.local_triv_at b) ⁻¹'
        ((C.local_triv_at b).base_set ×ˢ s), (continuous_on_open_iff
        (C.local_triv_at b).open_source).mp (C.local_triv_at b).continuous_to_fun _
        ((C.local_triv_at b).open_base_set.prod h), _⟩,
      rw [preimage_inter, ←preimage_comp, function.comp],
      simp only [total_space_mk],
      refine ext_iff.mpr (λ a, ⟨λ ha, _, λ ha, ⟨C.mem_base_set_at b, _⟩⟩),
      { simp only [mem_prod, mem_preimage, mem_inter_iff, local_triv_at_apply_mk] at ha,
        exact ha.2.2, },
      { simp only [mem_prod, mem_preimage, mem_inter_iff, local_triv_at_apply_mk],
        exact ⟨C.mem_base_set_at b, ha⟩, } } end⟩,
  trivialization_atlas := range C.local_triv,
  trivialization_at := λ x, C.local_triv (C.index_at x),
  mem_base_set_trivialization_at := C.mem_base_set_at,
  trivialization_mem_atlas := λ x, mem_range_self _ }

/-- The projection on the base of a topological bundle created from core is continuous -/
lemma continuous_proj : continuous C.proj :=
by { haveI := C.fiber_bundle, exact continuous_proj F C.fiber }

/-- The projection on the base of a topological bundle created from core is an open map -/
lemma is_open_map_proj : is_open_map C.proj :=
by { haveI := C.fiber_bundle, exact is_open_map_proj F C.fiber }

end fiber_bundle_core

end general

namespace bundle
instance [I : topological_space F] : ∀ x : B, topological_space (trivial B F x) := λ x, I

instance [t₁ : topological_space B] [t₂ : topological_space F] :
  topological_space (total_space (trivial B F)) :=
induced total_space.proj t₁ ⊓ induced (trivial.proj_snd B F) t₂

/-! ### The trivial fiber bundle -/
namespace trivial

variables (B F) [topological_space B] [topological_space F]

/-- Local trivialization for trivial bundle. -/
def trivialization : trivialization F (@total_space.proj B (bundle.trivial B F)) :=
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

@[simp]
lemma trivialization_source : (trivialization B F).source = univ := rfl

@[simp]
lemma trivialization_target : (trivialization B F).target = univ := rfl

instance : fiber_bundle F (bundle.trivial B F) :=
{ trivialization_atlas := {trivialization B F},
  trivialization_at := λ x, trivialization B F,
  mem_base_set_trivialization_at := mem_univ,
  trivialization_mem_atlas := λ x, mem_singleton _,
  total_space_mk_inducing := λ b, ⟨begin
    have : (λ (x : trivial B F b), x) = @id F, by { ext x, refl },
    simp only [total_space.topological_space, induced_inf, induced_compose, function.comp,
      total_space.proj, induced_const, top_inf_eq, trivial.proj_snd, id.def,
      trivial.topological_space, this, induced_id],
  end⟩ }

-- instance : mem_trivialization_atlas (trivialization B F) := ⟨mem_singleton _⟩
variables {B F}
lemma eq_trivialization (e : _root_.trivialization F (@total_space.proj B (bundle.trivial B F)))
  [he : mem_trivialization_atlas e] : e = trivialization B F :=
mem_singleton_iff.mp he

end trivial

end bundle

/-! ### The fibrewise product of two fibre bundles -/

open trivialization
namespace bundle

variables (E₁ : B → Type*) (E₂ : B → Type*)
variables [topological_space (total_space E₁)] [topological_space (total_space E₂)]

/-- Equip the total space of the fibrewise product of two topological fiber bundles `E₁`, `E₂` with
the induced topology from the diagonal embedding into `total_space E₁ × total_space E₂`. -/
instance prod.topological_space :
  topological_space (total_space (E₁ ×ᵇ E₂)) :=
topological_space.induced
  (λ p, ((⟨p.1, p.2.1⟩ : total_space E₁), (⟨p.1, p.2.2⟩ : total_space E₂)))
  (by apply_instance : topological_space (total_space E₁ × total_space E₂))

/-- The diagonal map from the total space of the fibrewise product of two topological fiber bundles
`E₁`, `E₂` into `total_space E₁ × total_space E₂` is `inducing`. -/
lemma prod.inducing_diag : inducing
  (λ p, (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩) :
    total_space (E₁ ×ᵇ E₂) → total_space E₁ × total_space E₂) :=
⟨rfl⟩

end bundle

open bundle

variables [topological_space B]

variables (F₁ : Type*) [topological_space F₁]
  (E₁ : B → Type*) [topological_space (total_space E₁)]

variables (F₂ : Type*) [topological_space F₂]
  (E₂ : B → Type*) [topological_space (total_space E₂)]

namespace trivialization
variables (e₁ : trivialization F₁ (total_space.proj : total_space E₁ → B))
variables (e₂ : trivialization F₂ (total_space.proj : total_space E₂ → B))

include e₁ e₂
variables {F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, the forward
function for the construction `trivialization.prod`, the induced
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

variables (e₁ e₂) [∀ b, has_zero (E₁ b)] [∀ b, has_zero (E₂ b)]

/-- Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, the inverse
function for the construction `trivialization.prod`, the induced
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
  continuous_on (prod.inv_fun' e₁ e₂) ((e₁.base_set ∩ e₂.base_set) ×ˢ univ) :=
begin
  rw (prod.inducing_diag E₁ E₂).continuous_on_iff,
  have H₁ : continuous (λ p : B × F₁ × F₂, ((p.1, p.2.1), (p.1, p.2.2))) :=
    (continuous_id.prod_map continuous_fst).prod_mk (continuous_id.prod_map continuous_snd),
  refine (e₁.continuous_on_symm.prod_map e₂.continuous_on_symm).comp H₁.continuous_on _,
  exact λ x h, ⟨⟨h.1.1, mem_univ _⟩, ⟨h.1.2, mem_univ _⟩⟩
end

variables (e₁ e₂)
variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂]

/-- Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, the induced
trivialization for the direct sum of `E₁` and `E₂`, whose base set is `e₁.base_set ∩ e₂.base_set`.

Either one of `[∀ b, has_zero (E₁ b)] [∀ b, has_zero (E₂ b)]` would suffice for this, as would either
one of `[fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂]`.  We `nolint unused_arguments` to require both for
symmetry.
-/
-- @[nolint unused_arguments]
def prod : trivialization (F₁ × F₂) (@total_space.proj B (E₁ ×ᵇ E₂)) :=
{ to_fun := prod.to_fun' e₁ e₂,
  inv_fun := prod.inv_fun' e₁ e₂,
  source := (@total_space.proj B (E₁ ×ᵇ E₂)) ⁻¹' (e₁.base_set ∩ e₂.base_set),
  target := (e₁.base_set ∩ e₂.base_set) ×ˢ set.univ,
  map_source' := λ x h, ⟨h, set.mem_univ _⟩,
  map_target' := λ x h, h.1,
  left_inv' := λ x, prod.left_inv,
  right_inv' := λ x, prod.right_inv,
  open_source := begin
    refine (e₁.open_base_set.inter e₂.open_base_set).preimage _,
    exact (continuous_proj F₁ E₁).comp (prod.inducing_diag E₁ E₂).continuous.fst,
  end,
  open_target := (e₁.open_base_set.inter e₂.open_base_set).prod is_open_univ,
  continuous_to_fun := prod.continuous_to_fun,
  continuous_inv_fun := prod.continuous_inv_fun,
  base_set := e₁.base_set ∩ e₂.base_set,
  open_base_set := e₁.open_base_set.inter e₂.open_base_set,
  source_eq := rfl,
  target_eq := rfl,
  proj_to_fun := λ x h, rfl }

@[simp] lemma base_set_prod : (prod e₁ e₂).base_set = e₁.base_set ∩ e₂.base_set :=
rfl

variables {e₁ e₂}

lemma prod_symm_apply (x : B) (w₁ : F₁) (w₂ : F₂) : (prod e₁ e₂).to_local_equiv.symm (x, w₁, w₂)
  = ⟨x, e₁.symm x w₁, e₂.symm x w₂⟩ :=
rfl

end trivialization

open trivialization

variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂] [Π b, has_zero (E₁ b)] [Π b, has_zero (E₂ b)]

/-- The product of two fiber bundles is a fiber bundle. -/
instance _root_.bundle.prod.fiber_bundle : fiber_bundle (F₁ × F₂) (E₁ ×ᵇ E₂) :=
{ total_space_mk_inducing := λ b,
  begin
    rw (prod.inducing_diag E₁ E₂).inducing_iff,
    exact (total_space_mk_inducing F₁ E₁ b).prod_mk (total_space_mk_inducing F₂ E₂ b),
  end,
  trivialization_atlas := (λ (p : trivialization F₁ (@total_space.proj B E₁) × trivialization F₂ (@total_space.proj B E₂)), p.1.prod p.2) ''
    (trivialization_atlas F₁ E₁ ×ˢ trivialization_atlas F₂ E₂),
  trivialization_at := λ b, (trivialization_at F₁ E₁ b).prod (trivialization_at F₂ E₂ b),
  mem_base_set_trivialization_at :=
    λ b, ⟨mem_base_set_trivialization_at F₁ E₁ b, mem_base_set_trivialization_at F₂ E₂ b⟩,
  trivialization_mem_atlas := λ b,
    ⟨(_, _), ⟨trivialization_mem_atlas F₁ E₁ b, trivialization_mem_atlas F₂ E₂ b⟩, rfl⟩}
