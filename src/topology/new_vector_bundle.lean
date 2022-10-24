import analysis.normed_space.bounded_linear_maps
import topology.new_bundle

open topological_space filter set bundle
open_locale topological_space classical

noncomputable theory

variables {R 𝕜 B F : Type*} {E : B → Type*}

section

variables [semiring R] [topological_space B]

namespace pretrivialization

variables [topological_space F] (e : pretrivialization F (total_space.proj : total_space E → B))

section zero
variables [∀ b, has_zero (E b)]

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

end zero

variables (R) [add_comm_monoid F] [module R F] [∀ b, add_comm_monoid (E b)] [∀ b, module R (E b)]
-- variables {Z : Type*} (proj : Z → B) [∀ b, add_comm_monoid (proj ⁻¹' {b})]
--   [∀ b, module R (proj ⁻¹' {b})]

-- class pretrivialization.is_linear' (e : pretrivialization F proj) : Prop :=
-- (is_linear : ∀ x ∈ e.base_set, is_linear_map R (λ y : proj ⁻¹' {x}, (e (y : Z)).2))

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
namespace bundle

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

end bundle
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

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
trivialization for the direct sum of `E₁` and `E₂`, whose base set is `e₁.base_set ∩ e₂.base_set`.
-/
@[nolint unused_arguments]
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

variables [vector_bundle R F₁ E₁] [vector_bundle R F₂ E₂]

instance prod.is_linear [e₁.is_linear R] [e₂.is_linear R] : (e₁.prod e₂).is_linear R :=
{ linear := λ x ⟨h₁, h₂⟩, (((e₁.linear R h₁).mk' _).prod_map ((e₂.linear R h₂).mk' _)).is_linear }

@[simp] lemma base_set_prod : (prod e₁ e₂).base_set = e₁.base_set ∩ e₂.base_set :=
rfl

variables {e₁ e₂}

lemma prod_apply {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set) (v₁ : E₁ x)
  (v₂ : E₂ x) :
  prod e₁ e₂ ⟨x, (v₁, v₂)⟩
  = ⟨x, e₁.continuous_linear_equiv_at R x hx₁ v₁, e₂.continuous_linear_equiv_at R x hx₂ v₂⟩ :=
rfl

lemma prod_symm_apply (x : B) (w₁ : F₁) (w₂ : F₂) : (prod e₁ e₂).to_local_equiv.symm (x, w₁, w₂)
  = ⟨x, e₁.symm x w₁, e₂.symm x w₂⟩ :=
rfl

end trivialization

open trivialization

variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂]
  [vector_bundle R F₁ E₁] [vector_bundle R F₂ E₂]

/-- The product of two vector bundles is a vector bundle. -/
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

-- lemma eq_prod (e : _root_.trivialization (F₁ × F₂) (@total_space.proj B (E₁ ×ᵇ E₂)))
--   [he : mem_trivialization_atlas e] : e = trivialization B F :=
-- mem_singleton_iff.mp he.1

/-- The product of two vector bundles is a vector bundle. -/
instance _root_.bundle.prod.vector_bundle :
  vector_bundle R (F₁ × F₂) (E₁ ×ᵇ E₂) :=
{ trivialization_linear := sorry,
  continuous_on_coord_change := begin
    rintros _ _ ⟨⟨e₁, e₂⟩, ⟨he₁, he₂⟩, rfl⟩ ⟨⟨e₁', e₂'⟩, ⟨he₁', he₂'⟩, rfl⟩,
    dsimp only at *,
    resetI,
    have := continuous_on_coord_change e₁ e₁',
    have := continuous_on_coord_change R e₂ e₂' he₂ he₂',
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




end
