/-
Copyright (c) 2022 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import analysis.normed_space.bounded_linear_maps
import topology.new_fiber_bundle

open topological_space filter set bundle
open_locale topological_space classical

noncomputable theory

variables {R 𝕜 B F : Type*} {E : B → Type*}

section

variables [semiring R] [topological_space B]

namespace pretrivialization

variables [topological_space F] (e : pretrivialization F (total_space.proj : total_space E → B))
  (R) [add_comm_monoid F] [module R F] [∀ b, add_comm_monoid (E b)] [∀ b, module R (E b)]

protected class is_linear (e : pretrivialization F (@total_space.proj B E)) : Prop :=
(linear : ∀ b ∈ e.base_set, is_linear_map R (λ x : E b, (e (total_space_mk b x)).2))

variables [e.is_linear R]

lemma linear {b : B} (hb : b ∈ e.base_set) :
  is_linear_map R (λ x : E b, (e (total_space_mk b x)).2) :=
pretrivialization.is_linear.linear b hb

include e R
variables (R)

/-- A fiberwise linear inverse to `e`. -/
@[simps] protected def symmₗ (b : B) : F →ₗ[R] E b :=
begin
  refine is_linear_map.mk' (e.symm b) _,
  by_cases hb : b ∈ e.base_set,
  { exact (((e.linear R hb).mk' _).inverse (e.symm b) (e.symm_apply_apply_mk hb)
      (λ v, congr_arg prod.snd $ e.apply_mk_symm hb v)).is_linear },
  { rw [e.coe_symm_of_not_mem hb], exact (0 : F →ₗ[R] E b).is_linear }
end

/-- A pretrivialization for a topological vector bundle defines linear equivalences between the
fibers and the model space. -/
@[simps {fully_applied := ff}] def linear_equiv_at (b : B)
  (hb : b ∈ e.base_set) : E b ≃ₗ[R] F :=
{ to_fun := λ y, (e (total_space_mk b y)).2,
  inv_fun := e.symm b,
  left_inv := e.symm_apply_apply_mk hb,
  right_inv := λ v, by simp_rw [e.apply_mk_symm hb v],
  map_add' := λ v w, (e.linear R hb).map_add v w,
  map_smul' := λ c v, (e.linear R hb).map_smul c v }

/-- A fiberwise linear map equal to `e` on `e.base_set`. -/
protected def linear_map_at (b : B) : E b →ₗ[R] F :=
if hb : b ∈ e.base_set then e.linear_equiv_at R b hb else 0

lemma coe_linear_map_at (b : B) :
  ⇑(e.linear_map_at R b) = λ y, if b ∈ e.base_set then (e (total_space_mk b y)).2 else 0 :=
by { rw [pretrivialization.linear_map_at], split_ifs; refl }

lemma coe_linear_map_at_of_mem {b : B} (hb : b ∈ e.base_set) :
  ⇑(e.linear_map_at R b) = λ y, (e (total_space_mk b y)).2 :=
by simp_rw [coe_linear_map_at, if_pos hb]

lemma linear_map_at_apply {b : B} (y : E b) :
  e.linear_map_at R b y = if b ∈ e.base_set then (e (total_space_mk b y)).2 else 0 :=
by rw [coe_linear_map_at]

lemma linear_map_at_def_of_mem {b : B} (hb : b ∈ e.base_set) :
  e.linear_map_at R b = e.linear_equiv_at R b hb :=
dif_pos hb

lemma linear_map_at_def_of_not_mem {b : B} (hb : b ∉ e.base_set) :
  e.linear_map_at R b = 0 :=
dif_neg hb

lemma linear_map_at_eq_zero {b : B} (hb : b ∉ e.base_set) :
  e.linear_map_at R b = 0 :=
dif_neg hb

lemma symmₗ_linear_map_at {b : B} (hb : b ∈ e.base_set) (y : E b) :
  e.symmₗ R b (e.linear_map_at R b y) = y :=
by { rw [e.linear_map_at_def_of_mem R hb], exact (e.linear_equiv_at R b hb).left_inv y }

lemma linear_map_at_symmₗ {b : B} (hb : b ∈ e.base_set) (y : F) :
  e.linear_map_at R b (e.symmₗ R b y) = y :=
by { rw [e.linear_map_at_def_of_mem R hb], exact (e.linear_equiv_at R b hb).right_inv y }

end pretrivialization

namespace trivialization

variables [topological_space F] [add_comm_monoid F] [module R F] [∀ b, add_comm_monoid (E b)] [∀ b, module R (E b)]
variables (R) [topological_space (total_space E)]

class is_linear (e : trivialization F (total_space.proj : total_space E → B)) : Prop :=
(linear : ∀ x ∈ e.base_set, is_linear_map R (λ y : E x, (e (total_space_mk x y)).2))

variables (e e' : trivialization F (total_space.proj : total_space E → B))
variables [e.is_linear R] [e'.is_linear R]

lemma linear {b : B} (hb : b ∈ e.base_set) :
  is_linear_map R (λ x : E b, (e (total_space_mk b x)).2) :=
trivialization.is_linear.linear b hb

instance to_pretrivialization.is_linear : e.to_pretrivialization.is_linear R :=
{ ..(‹_› : e.is_linear R) }

/-- A trivialization for a topological vector bundle defines linear equivalences between the
fibers and the model space. -/
def linear_equiv_at (b : B) (hb : b ∈ e.base_set) :
  E b ≃ₗ[R] F :=
e.to_pretrivialization.linear_equiv_at R b hb

@[simp]
lemma linear_equiv_at_apply (b : B) (hb : b ∈ e.base_set) (v : E b) :
  e.linear_equiv_at R b hb v = (e (total_space_mk b v)).2 := rfl

@[simp]
lemma linear_equiv_at_symm_apply (b : B) (hb : b ∈ e.base_set) (v : F) :
  (e.linear_equiv_at R b hb).symm v = e.symm b v := rfl

/-- A fiberwise linear inverse to `e`. -/
protected def symmₗ (b : B) : F →ₗ[R] E b :=
e.to_pretrivialization.symmₗ R b

lemma coe_symmₗ (b : B) : ⇑(e.symmₗ R b) = e.symm b :=
rfl

/-- A fiberwise linear map equal to `e` on `e.base_set`. -/
protected def linear_map_at (b : B) : E b →ₗ[R] F :=
e.to_pretrivialization.linear_map_at R b

lemma coe_linear_map_at (b : B) :
  ⇑(e.linear_map_at R b) = λ y, if b ∈ e.base_set then (e (total_space_mk b y)).2 else 0 :=
e.to_pretrivialization.coe_linear_map_at R b

lemma coe_linear_map_at_of_mem {b : B} (hb : b ∈ e.base_set) :
  ⇑(e.linear_map_at R b) = λ y, (e (total_space_mk b y)).2 :=
by simp_rw [coe_linear_map_at, if_pos hb]

lemma linear_map_at_apply {b : B} (y : E b) :
  e.linear_map_at R b y = if b ∈ e.base_set then (e (total_space_mk b y)).2 else 0 :=
by rw [coe_linear_map_at]

lemma linear_map_at_def_of_mem {b : B} (hb : b ∈ e.base_set) :
  e.linear_map_at R b = e.linear_equiv_at R b hb :=
dif_pos hb

lemma linear_map_at_def_of_not_mem {b : B} (hb : b ∉ e.base_set) :
  e.linear_map_at R b = 0 :=
dif_neg hb

lemma symmₗ_linear_map_at {b : B} (hb : b ∈ e.base_set) (y : E b) :
  e.symmₗ R b (e.linear_map_at R b y) = y :=
e.to_pretrivialization.symmₗ_linear_map_at R hb y

lemma linear_map_at_symmₗ {b : B} (hb : b ∈ e.base_set) (y : F) :
  e.linear_map_at R b (e.symmₗ R b y) = y :=
e.to_pretrivialization.linear_map_at_symmₗ R hb y

/-- A coordinate change function between two trivializations, as a continuous linear equivalence.
  Defined to be the identity when `b` does not lie in the base set of both trivializations. -/
def coord_change (b : B) : F ≃L[R] F :=
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

lemma coe_coord_change {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) :
  ⇑(coord_change R e e' b) =
  (e.linear_equiv_at R b hb.1).symm.trans (e'.linear_equiv_at R b hb.2) :=
congr_arg linear_equiv.to_fun (dif_pos hb)

lemma coord_change_apply {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  coord_change R e e' b y = (e' (total_space_mk b (e.symm b y))).2 :=
congr_arg (λ f, linear_equiv.to_fun f y) (dif_pos hb)

lemma mk_coord_change {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  (b, coord_change R e e' b y) = e' (total_space_mk b (e.symm b y)) :=
begin
  ext,
  { rw [e.mk_symm hb.1 y, e'.coe_fst', e.proj_symm_apply' hb.1],
    rw [e.proj_symm_apply' hb.1], exact hb.2 },
  { exact e.coord_change_apply R e' hb y }
end

/-- A version of `coord_change_apply` that fully unfolds `coord_change`. The right-hand side is
ugly, but has good definitional properties for specifically defined trivializations. -/
lemma coord_change_apply' {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  coord_change R e e' b y = (e' (e.to_local_homeomorph.symm (b, y))).2 :=
by rw [e.coord_change_apply R e' hb, e.mk_symm hb.1]

lemma coord_change_symm_apply {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) :
  ⇑(coord_change R e e' b).symm =
  (e'.linear_equiv_at R b hb.2).symm.trans (e.linear_equiv_at R b hb.1) :=
congr_arg linear_equiv.inv_fun (dif_pos hb)

lemma symm_coord_change {b : B} (hb : b ∈ e'.base_set ∩ e.base_set) :
  (e.coord_change R e' b).symm = e'.coord_change R e b :=
begin
  sorry,
end

lemma apply_symm_apply_eq_coord_change {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) (v : F) :
  e' ((e.to_local_homeomorph.symm) (b, v)) = (b, e.coord_change R e' b v) :=
begin
  sorry,
end

end trivialization



variables [topological_space (total_space E)]
variables [nontrivially_normed_field 𝕜]
variables [normed_add_comm_group F] [∀ b, add_comm_monoid (E b)] [∀ b, topological_space (E b)]
variables [normed_space 𝕜 F] [∀ b, module 𝕜 (E b)]
variables (𝕜) (e e' : trivialization F (@total_space.proj B E))

variables (F E) [fiber_bundle F E]

class vector_bundle  : Prop :=
(trivialization_linear : ∀ e [mem_trivialization_atlas e], trivialization.is_linear 𝕜 e)
(continuous_on_coord_change : ∀ (e e' : trivialization F (@total_space.proj B E))
  [he : mem_trivialization_atlas e]
  [he' : mem_trivialization_atlas e'], by {
  haveI : e.is_linear 𝕜 := @trivialization_linear e he,
  haveI : e'.is_linear 𝕜 := @trivialization_linear e' he',
  exactI continuous_on
  (λ b, trivialization.coord_change 𝕜 e e' b : B → F →L[𝕜] F) (e.base_set ∩ e'.base_set) })

export vector_bundle (continuous_on_coord_change)
attribute [instance] vector_bundle.trivialization_linear

variables [vector_bundle 𝕜 F E]

-- instance vector_bundle.trivialization_linear' [mem_trivialization_atlas e] : e.is_linear 𝕜 :=
-- vector_bundle.trivialization_linear e ‹_›

example [fiber_bundle F E] [vector_bundle 𝕜 F E] (e e' : trivialization F (@total_space.proj B E))
  [mem_trivialization_atlas e] [mem_trivialization_atlas e'] :
  continuous_on
  (λ b, trivialization.coord_change 𝕜 e e' b : B → F →L[𝕜] F) (e.base_set ∩ e'.base_set) :=
vector_bundle.continuous_on_coord_change e e'


variables {𝕜 F E}

namespace trivialization

variables [e.is_linear 𝕜] [e'.is_linear 𝕜]

variables (𝕜)

/-- Forward map of `continuous_linear_equiv_at` (only propositionally equal),
  defined everywhere (`0` outside domain). -/
@[simps apply {fully_applied := ff}]
def continuous_linear_map_at (b : B) : E b →L[𝕜] F :=
{ to_fun := e.linear_map_at 𝕜 b, -- given explicitly to help `simps`
  cont := begin
    dsimp,
    rw [e.coe_linear_map_at 𝕜 b],
    refine continuous_if_const _ (λ hb, _) (λ _, continuous_zero),
    exact continuous_snd.comp (e.to_local_homeomorph.continuous_on.comp_continuous
      (total_space_mk_inducing F E b).continuous (λ x, e.mem_source.mpr hb))
  end,
  .. e.linear_map_at 𝕜 b }

/-- Backwards map of `continuous_linear_equiv_at`, defined everywhere. -/
@[simps apply {fully_applied := ff}]
def symmL (b : B) : F →L[𝕜] E b :=
{ to_fun := e.symm b, -- given explicitly to help `simps`
  cont := begin
    by_cases hb : b ∈ e.base_set,
    { rw (total_space_mk_inducing F E b).continuous_iff,
      exact e.continuous_on_symm.comp_continuous (continuous_const.prod_mk continuous_id)
        (λ x, mk_mem_prod hb (mem_univ x)) },
    { refine continuous_zero.congr (λ x, (e.symm_apply_of_not_mem hb x).symm) },
  end,
  .. e.symmₗ 𝕜 b }

lemma symmL_continuous_linear_map_at {b : B} (hb : b ∈ e.base_set)
  (y : E b) :
  e.symmL 𝕜 b (e.continuous_linear_map_at 𝕜 b y) = y :=
e.symmₗ_linear_map_at 𝕜 hb y

lemma continuous_linear_map_at_symmL {b : B} (hb : b ∈ e.base_set)
  (y : F) :
  e.continuous_linear_map_at 𝕜 b (e.symmL 𝕜 b y) = y :=
e.linear_map_at_symmₗ 𝕜 hb y

/-- In a topological vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
@[simps apply symm_apply {fully_applied := ff}]
def continuous_linear_equiv_at (b : B)
  (hb : b ∈ e.base_set) : E b ≃L[𝕜] F :=
{ to_fun := λ y, (e (total_space_mk b y)).2, -- given explicitly to help `simps`
  inv_fun := e.symm b, -- given explicitly to help `simps`
  continuous_to_fun := continuous_snd.comp (e.to_local_homeomorph.continuous_on.comp_continuous
    (total_space_mk_inducing F E b).continuous (λ x, e.mem_source.mpr hb)),
  continuous_inv_fun := (e.symmL 𝕜 b).continuous,
  .. e.to_pretrivialization.linear_equiv_at 𝕜 b hb }

lemma coe_continuous_linear_equiv_at_eq {b : B} (hb : b ∈ e.base_set) :
  (e.continuous_linear_equiv_at 𝕜 b hb : E b → F) = e.continuous_linear_map_at 𝕜 b :=
(e.coe_linear_map_at_of_mem 𝕜 hb).symm

lemma symm_continuous_linear_equiv_at_eq {b : B} (hb : b ∈ e.base_set) :
  ((e.continuous_linear_equiv_at 𝕜 b hb).symm : F → E b) = e.symmL 𝕜 b :=
rfl

@[simp] lemma continuous_linear_equiv_at_apply'
  (x : total_space E) (hx : x ∈ e.source) :
  e.continuous_linear_equiv_at 𝕜 x.proj (e.mem_source.1 hx) x.2 = (e x).2 := by { cases x, refl }

lemma apply_eq_prod_continuous_linear_equiv_at (b : B)
  (hb : b ∈ e.base_set) (z : E b) :
  e.to_local_homeomorph ⟨b, z⟩ = (b, e.continuous_linear_equiv_at 𝕜 b hb z) :=
begin
  ext,
  { refine e.coe_fst _,
    rw e.source_eq,
    exact hb },
  { simp only [coe_coe, continuous_linear_equiv_at_apply] }
end

lemma symm_apply_eq_mk_continuous_linear_equiv_at_symm (b : B)
  (hb : b ∈ e.base_set) (z : F) :
  e.to_local_homeomorph.symm ⟨b, z⟩
  = total_space_mk b ((e.continuous_linear_equiv_at 𝕜 b hb).symm z) :=
begin
  have h : (b, z) ∈ e.to_local_homeomorph.target,
  { rw e.target_eq,
    exact ⟨hb, mem_univ _⟩ },
  apply e.to_local_homeomorph.inj_on (e.to_local_homeomorph.map_target h),
  { simp only [e.source_eq, hb, mem_preimage]},
  simp_rw [e.apply_eq_prod_continuous_linear_equiv_at 𝕜 b hb, e.to_local_homeomorph.right_inv h,
    continuous_linear_equiv.apply_symm_apply],
end

lemma comp_continuous_linear_equiv_at_eq_coord_change {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) :
  (e.continuous_linear_equiv_at 𝕜 b hb.1).symm.trans (e'.continuous_linear_equiv_at 𝕜 b hb.2)
  = coord_change 𝕜 e e' b :=
by { ext v, rw [coord_change_apply 𝕜 e e' hb], refl }

end trivialization

variables (𝕜 B F)
/-- Analogous construction of `fiber_bundle_core` for vector bundles. This
construction gives a way to construct vector bundles from a structure registering how
trivialization changes act on fibers. -/
structure vector_bundle_core (ι : Type*) :=
(base_set          : ι → set B)
(is_open_base_set  : ∀ i, is_open (base_set i))
(index_at          : B → ι)
(mem_base_set_at   : ∀ x, x ∈ base_set (index_at x))
(coord_change      : ι → ι → B → (F →L[𝕜] F))
(coord_change_self : ∀ i, ∀ x ∈ base_set i, ∀ v, coord_change i i x v = v)
(continuous_on_coord_change : ∀ i j, continuous_on (coord_change i j) (base_set i ∩ base_set j))
(coord_change_comp : ∀ i j k, ∀ x ∈ (base_set i) ∩ (base_set j) ∩ (base_set k), ∀ v,
  (coord_change j k x) (coord_change i j x v) = coord_change i k x v)

namespace vector_bundle_core

variables {𝕜 B F} {ι : Type*} (Z : vector_bundle_core 𝕜 B F ι)

include Z

/-- Natural identification to a `fiber_bundle_core`. -/
def to_fiber_bundle_core : fiber_bundle_core ι B F :=
{ coord_change := λ i j b, Z.coord_change i j b,
  continuous_on_coord_change := λ i j, is_bounded_bilinear_map_apply.continuous.comp_continuous_on
      ((Z.continuous_on_coord_change i j).prod_map continuous_on_id),
  ..Z }

lemma coord_change_linear_comp (i j k : ι): ∀ x ∈ (Z.base_set i) ∩ (Z.base_set j) ∩ (Z.base_set k),
  (Z.coord_change j k x).comp (Z.coord_change i j x) = Z.coord_change i k x :=
λ x hx, by { ext v, exact Z.coord_change_comp i j k x hx v }

instance add_comm_monoid_fiber : ∀ (x : B), add_comm_monoid (Z.to_fiber_bundle_core.fiber x) :=
by delta_instance fiber_bundle_core.fiber
instance module_fiber : ∀ (x : B), module 𝕜 (Z.to_fiber_bundle_core.fiber x) :=
by delta_instance fiber_bundle_core.fiber
instance add_comm_group_fiber [add_comm_group F] : ∀ (x : B), add_comm_group (Z.to_fiber_bundle_core.fiber x) :=
by delta_instance fiber_bundle_core.fiber

variables (b : B) (a : F)

@[simp, mfld_simps] lemma coe_coord_change (i j : ι) :
  Z.to_fiber_bundle_core.coord_change i j b = Z.coord_change i j b := rfl

instance is_linear_local_triv (i : ι) : (Z.to_fiber_bundle_core.local_triv i).is_linear 𝕜 :=
⟨λ x hx,
  { map_add := λ v w, by simp only [continuous_linear_map.map_add] with mfld_simps,
    map_smul := λ r v, by simp only [continuous_linear_map.map_smul] with mfld_simps}⟩

variables (i j : ι)

@[simp, mfld_simps] lemma local_triv_apply (p : Z.to_fiber_bundle_core.total_space) :
  (Z.to_fiber_bundle_core.local_triv i) p = ⟨p.1, Z.coord_change (Z.index_at p.1) i p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma local_triv_symm_fst (p : B × F) :
  (Z.to_fiber_bundle_core.local_triv i).to_local_homeomorph.symm p =
    ⟨p.1, Z.coord_change i (Z.index_at p.1) p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma local_triv_coord_change_eq {b : B} (hb : b ∈ Z.base_set i ∩ Z.base_set j)
  (v : F) :
  (Z.to_fiber_bundle_core.local_triv i).coord_change 𝕜 (Z.to_fiber_bundle_core.local_triv j) b v =
  Z.coord_change i j b v :=
begin
  rw [trivialization.coord_change_apply', local_triv_symm_fst, local_triv_apply,
    coord_change_comp],
  exacts [⟨⟨hb.1, Z.mem_base_set_at b⟩, hb.2⟩, hb]
end

instance : vector_bundle 𝕜 F Z.to_fiber_bundle_core.fiber :=
{ trivialization_linear := begin
    rintro _ ⟨i, rfl⟩,
    exact Z.is_linear_local_triv i,
  end,
  continuous_on_coord_change := begin
    rintros _ _ ⟨i, rfl⟩ ⟨i', rfl⟩,
    refine (Z.continuous_on_coord_change i i').congr (λ b hb, _),
    ext v,
    simp_rw [continuous_linear_equiv.coe_coe, Z.local_triv_coord_change_eq i i' hb],
  end }

end vector_bundle_core









namespace bundle.trivial
variables (𝕜 B F)

/-- Local trivialization for trivial bundle. -/
instance trivialization.linear : (trivialization B F).is_linear 𝕜 :=
{ linear := λ x hx, ⟨λ y z, rfl, λ c y, rfl⟩ }

lemma trivialization.coord_change (b : B) :
  (trivialization B F).coord_change 𝕜 (trivialization B F) b = continuous_linear_equiv.refl 𝕜 F :=
begin
  ext v,
  rw [trivialization.coord_change_apply'],
  exacts [rfl, ⟨mem_univ _, mem_univ _⟩]
end

instance : vector_bundle 𝕜 F (bundle.trivial B F) :=
{ trivialization_linear := by { introsI e he, rw [eq_trivialization e], apply_instance },
  continuous_on_coord_change := begin
    introsI e e' he he',
    simp_rw [eq_trivialization e, eq_trivialization e'],
    simp_rw [trivialization.coord_change],
    exact continuous_const.continuous_on
  end }

end bundle.trivial

end




open trivialization
open bundle

variables [nontrivially_normed_field R] [topological_space B]

variables (F₁ : Type*) [normed_add_comm_group F₁] [normed_space R F₁]
  (E₁ : B → Type*) [topological_space (total_space E₁)]
  [Π x, add_comm_monoid (E₁ x)] [Π x, module R (E₁ x)]

variables (F₂ : Type*) [normed_add_comm_group F₂] [normed_space R F₂]
  (E₂ : B → Type*) [topological_space (total_space E₂)]
  [Π x, add_comm_monoid (E₂ x)] [Π x, module R (E₂ x)]

namespace trivialization
variables (e₁ : trivialization F₁ (total_space.proj : total_space E₁ → B))
variables (e₂ : trivialization F₂ (total_space.proj : total_space E₂ → B))
variables [e₁.is_linear R] [e₂.is_linear R]

include e₁ e₂
variables {R F₁ E₁ F₂ E₂}

variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂]

variables [vector_bundle R F₁ E₁] [vector_bundle R F₂ E₂]

instance prod.is_linear [e₁.is_linear R] [e₂.is_linear R] : (e₁.prod e₂).is_linear R :=
{ linear := λ x ⟨h₁, h₂⟩, (((e₁.linear R h₁).mk' _).prod_map ((e₂.linear R h₂).mk' _)).is_linear }

variables {e₁ e₂} (R)

lemma prod_apply {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set) (v₁ : E₁ x)
  (v₂ : E₂ x) :
  prod e₁ e₂ ⟨x, (v₁, v₂)⟩
  = ⟨x, e₁.continuous_linear_equiv_at R x hx₁ v₁, e₂.continuous_linear_equiv_at R x hx₂ v₂⟩ :=
rfl

end trivialization

open trivialization

variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂]
  [vector_bundle R F₁ E₁] [vector_bundle R F₂ E₂]

/-- The product of two vector bundles is a vector bundle. -/
instance _root_.bundle.prod.vector_bundle :
  vector_bundle R (F₁ × F₂) (E₁ ×ᵇ E₂) :=
{ trivialization_linear := begin
    rintros - ⟨⟨e₁, e₂⟩, ⟨i₁ : mem_trivialization_atlas e₁, i₂ : mem_trivialization_atlas e₂⟩, rfl⟩,
    resetI,
    apply prod.is_linear,
  end,
  continuous_on_coord_change := begin
    rintros - -
      ⟨⟨e₁, e₂⟩, ⟨i₁ : mem_trivialization_atlas e₁, i₂ : mem_trivialization_atlas e₂⟩, rfl⟩
      ⟨⟨e₁', e₂'⟩, ⟨i₁' : mem_trivialization_atlas e₁', i₂' : mem_trivialization_atlas e₂'⟩, rfl⟩,
    resetI,
    refine (((continuous_on_coord_change e₁ e₁').mono _).prod_mapL R
      ((continuous_on_coord_change e₂ e₂').mono _)).congr _;
    dsimp only [base_set_prod] with mfld_simps,
    { mfld_set_tac },
    { mfld_set_tac },
    { rintro b hb,
      rw [continuous_linear_map.ext_iff],
      rintro ⟨v₁, v₂⟩,
      show (e₁.prod e₂).coord_change R (e₁'.prod e₂') b (v₁, v₂) =
        (e₁.coord_change R e₁' b v₁, e₂.coord_change R e₂' b v₂),
      rw [e₁.coord_change_apply R e₁', e₂.coord_change_apply R e₂',
        (e₁.prod e₂).coord_change_apply' R],
      exacts [rfl, hb, ⟨hb.1.2, hb.2.2⟩, ⟨hb.1.1, hb.2.1⟩] }
  end }

variables {R F₁ E₁ F₂ E₂}

@[simp] lemma trivialization.continuous_linear_equiv_at_prod
  (e₁ : trivialization F₁ (@total_space.proj B E₁)) [is_linear R e₁]
  (e₂ : trivialization F₂ (@total_space.proj B E₂)) [is_linear R e₂]
  {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set) :
  (e₁.prod e₂).continuous_linear_equiv_at R x ⟨hx₁, hx₂⟩
  = (e₁.continuous_linear_equiv_at R x hx₁).prod (e₂.continuous_linear_equiv_at R x hx₂) :=
begin
  ext1,
  funext v,
  obtain ⟨v₁, v₂⟩ := v,
  rw [(e₁.prod e₂).continuous_linear_equiv_at_apply R, trivialization.prod],
  dsimp,
  exact (congr_arg prod.snd (prod_apply R hx₁ hx₂ v₁ v₂) : _)
end
