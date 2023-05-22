/-
Copyright © 2022 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sébastien Gouëzel, Heather Macbeth, Floris van Doorn
-/
import topology.fiber_bundle.basic

/-!
# Standard constructions on fiber bundles

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains several standard constructions on fiber bundles:

* `bundle.trivial.fiber_bundle 𝕜 B F`: the trivial fiber bundle with model fiber `F` over the base
  `B`

* `fiber_bundle.prod`: for fiber bundles `E₁` and `E₂` over a common base, a fiber bundle structure
  on their fiberwise product `E₁ ×ᵇ E₂` (the notation stands for `λ x, E₁ x × E₂ x`).

* `fiber_bundle.pullback`: for a fiber bundle `E` over `B`, a fiber bundle structure on its
  pullback `f *ᵖ E` by a map `f : B' → B` (the notation is a type synonym for `E ∘ f`).

## Tags

fiber bundle, fibre bundle, fiberwise product, pullback

-/
open topological_space filter set bundle
open_locale topology classical bundle

/-! ### The trivial bundle -/

namespace bundle
namespace trivial

variables (B : Type*) (F : Type*)

instance [I : topological_space F] : ∀ x : B, topological_space (trivial B F x) := λ x, I

instance [t₁ : topological_space B] [t₂ : topological_space F] :
  topological_space (total_space (trivial B F)) :=
induced total_space.proj t₁ ⊓ induced (trivial.proj_snd B F) t₂

variables [topological_space B] [topological_space F]

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

@[simp]
lemma trivialization_source : (trivialization B F).source = univ := rfl

@[simp]
lemma trivialization_target : (trivialization B F).target = univ := rfl

/-- Fiber bundle instance on the trivial bundle. -/
instance fiber_bundle : fiber_bundle F (bundle.trivial B F) :=
{ trivialization_atlas := {bundle.trivial.trivialization B F},
  trivialization_at := λ x, bundle.trivial.trivialization B F,
  mem_base_set_trivialization_at := mem_univ,
  trivialization_mem_atlas := λ x, mem_singleton _,
  total_space_mk_inducing := λ b, ⟨begin
    have : (λ (x : trivial B F b), x) = @id F, by { ext x, refl },
    simp only [total_space.topological_space, induced_inf, induced_compose, function.comp,
      total_space.proj, induced_const, top_inf_eq, trivial.proj_snd, id.def,
      trivial.topological_space, this, induced_id],
  end⟩ }

lemma eq_trivialization (e : _root_.trivialization F (π (bundle.trivial B F)))
  [i : mem_trivialization_atlas e] :
  e = trivialization B F :=
i.out

end trivial
end bundle

/-! ### Fibrewise product of two bundles -/

section prod

variables {B : Type*}

section defs
variables (E₁ : B → Type*) (E₂ : B → Type*)
variables [topological_space (total_space E₁)] [topological_space (total_space E₂)]

/-- Equip the total space of the fiberwise product of two fiber bundles `E₁`, `E₂` with
the induced topology from the diagonal embedding into `total_space E₁ × total_space E₂`. -/
instance fiber_bundle.prod.topological_space : topological_space (total_space (E₁ ×ᵇ E₂)) :=
topological_space.induced
  (λ p, ((⟨p.1, p.2.1⟩ : total_space E₁), (⟨p.1, p.2.2⟩ : total_space E₂)))
  (by apply_instance : topological_space (total_space E₁ × total_space E₂))

/-- The diagonal map from the total space of the fiberwise product of two fiber bundles
`E₁`, `E₂` into `total_space E₁ × total_space E₂` is `inducing`. -/
lemma fiber_bundle.prod.inducing_diag : inducing
  (λ p, (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩) :
    total_space (E₁ ×ᵇ E₂) → total_space E₁ × total_space E₂) :=
⟨rfl⟩

end defs

open fiber_bundle

variables [topological_space B]
  (F₁ : Type*) [topological_space F₁] (E₁ : B → Type*) [topological_space (total_space E₁)]
  (F₂ : Type*) [topological_space F₂] (E₂ : B → Type*) [topological_space (total_space E₂)]

namespace trivialization
variables {F₁ E₁ F₂ E₂} (e₁ : trivialization F₁ (π E₁)) (e₂ : trivialization F₂ (π E₂))

/-- Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, the forward
function for the construction `trivialization.prod`, the induced
trivialization for the fiberwise product of `E₁` and `E₂`. -/
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

variables (e₁ e₂) [Π x, has_zero (E₁ x)] [∀ x, has_zero (E₂ x)]

/-- Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, the inverse
function for the construction `trivialization.prod`, the induced
trivialization for the fiberwise product of `E₁` and `E₂`. -/
noncomputable def prod.inv_fun' (p : B × (F₁ × F₂)) : total_space (E₁ ×ᵇ E₂) :=
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

variables (e₁ e₂ e₁ e₂)

/-- Given trivializations `e₁`, `e₂` for bundle types `E₁`, `E₂` over a base `B`, the induced
trivialization for the fiberwise product of `E₁` and `E₂`, whose base set is
`e₁.base_set ∩ e₂.base_set`. -/
noncomputable def prod : trivialization (F₁ × F₂) (π (E₁ ×ᵇ E₂)) :=
{ to_fun := prod.to_fun' e₁ e₂,
  inv_fun := prod.inv_fun' e₁ e₂,
  source := (@total_space.proj B (E₁ ×ᵇ E₂)) ⁻¹' (e₁.base_set ∩ e₂.base_set),
  target := (e₁.base_set ∩ e₂.base_set) ×ˢ set.univ,
  map_source' := λ x h, ⟨h, set.mem_univ _⟩,
  map_target' := λ x h, h.1,
  left_inv' := λ x, prod.left_inv,
  right_inv' := λ x, prod.right_inv,
  open_source := begin
    convert (e₁.open_source.prod e₂.open_source).preimage
      (fiber_bundle.prod.inducing_diag E₁ E₂).continuous,
    ext x,
    simp only [trivialization.source_eq] with mfld_simps,
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

lemma prod_symm_apply (x : B) (w₁ : F₁) (w₂ : F₂) : (prod e₁ e₂).to_local_equiv.symm (x, w₁, w₂)
  = ⟨x, e₁.symm x w₁, e₂.symm x w₂⟩ :=
rfl

end trivialization

open trivialization

variables [Π x, has_zero (E₁ x)] [∀ x, has_zero (E₂ x)]
  [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂]

/-- The product of two fiber bundles is a fiber bundle. -/
noncomputable instance fiber_bundle.prod : fiber_bundle (F₁ × F₂) (E₁ ×ᵇ E₂) :=
{ total_space_mk_inducing := λ b,
  begin
    rw (prod.inducing_diag E₁ E₂).inducing_iff,
    exact (total_space_mk_inducing F₁ E₁ b).prod_mk (total_space_mk_inducing F₂ E₂ b),
  end,
  trivialization_atlas :=
    {e |  ∃ (e₁ : trivialization F₁ (π E₁)) (e₂ : trivialization F₂ (π E₂))
    [mem_trivialization_atlas e₁] [mem_trivialization_atlas e₂], by exactI
    e = trivialization.prod e₁ e₂},
  trivialization_at := λ b, (trivialization_at F₁ E₁ b).prod (trivialization_at F₂ E₂ b),
  mem_base_set_trivialization_at :=
    λ b, ⟨mem_base_set_trivialization_at F₁ E₁ b, mem_base_set_trivialization_at F₂ E₂ b⟩,
  trivialization_mem_atlas := λ b, ⟨trivialization_at F₁ E₁ b, trivialization_at F₂ E₂ b,
    by apply_instance, by apply_instance, rfl⟩ }

instance {e₁ : trivialization F₁ (π E₁)} {e₂ : trivialization F₂ (π E₂)}
  [mem_trivialization_atlas e₁] [mem_trivialization_atlas e₂] :
  mem_trivialization_atlas (e₁.prod e₂ : trivialization (F₁ × F₂) (π (E₁ ×ᵇ E₂))) :=
{ out := ⟨e₁, e₂, by apply_instance, by apply_instance, rfl⟩ }

end prod

/-! ### Pullbacks of fiber bundles -/

section
variables {B : Type*} (F : Type*) (E : B → Type*) {B' : Type*} (f : B' → B)

instance [∀ (x : B), topological_space (E x)] : ∀ (x : B'), topological_space ((f *ᵖ E) x) :=
by delta_instance bundle.pullback

variables [topological_space B'] [topological_space (total_space E)]

/-- Definition of `pullback.total_space.topological_space`, which we make irreducible. -/
@[irreducible] def pullback_topology : topological_space (total_space (f *ᵖ E)) :=
induced total_space.proj ‹topological_space B'› ⊓
induced (pullback.lift f) ‹topological_space (total_space E)›

/-- The topology on the total space of a pullback bundle is the coarsest topology for which both
the projections to the base and the map to the original bundle are continuous. -/
instance pullback.total_space.topological_space : topological_space (total_space (f *ᵖ E)) :=
pullback_topology E f

lemma pullback.continuous_proj (f : B' → B) : continuous (@total_space.proj _ (f *ᵖ E)) :=
begin
  rw [continuous_iff_le_induced, pullback.total_space.topological_space, pullback_topology],
  exact inf_le_left,
end

lemma pullback.continuous_lift (f : B' → B) : continuous (@pullback.lift B E B' f) :=
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

section fiber_bundle
variables (F) [topological_space F] [topological_space B]

lemma pullback.continuous_total_space_mk [∀ x, topological_space (E x)]
  [fiber_bundle F E] {f : B' → B} {x : B'} :
  continuous (@total_space_mk _ (f *ᵖ E) x) :=
begin
  simp only [continuous_iff_le_induced, pullback.total_space.topological_space, induced_compose,
    induced_inf, function.comp, total_space_mk, total_space.proj, induced_const, top_inf_eq,
    pullback_topology],
  exact le_of_eq (fiber_bundle.total_space_mk_inducing F E (f x)).induced,
end

variables {E F} [∀ b, has_zero (E b)] {K : Type*} [continuous_map_class K B' B]

/-- A fiber bundle trivialization can be pulled back to a trivialization on the pullback bundle. -/
noncomputable def trivialization.pullback (e : trivialization F (π E)) (f : K) :
  trivialization F (π ((f : B' → B) *ᵖ E)) :=
{ to_fun := λ z, (z.proj, (e (pullback.lift f z)).2),
  inv_fun := λ y, @total_space_mk _ (f *ᵖ E) y.1 (e.symm (f y.1) y.2),
  source := pullback.lift f ⁻¹' e.source,
  base_set := f ⁻¹' e.base_set,
  target := (f ⁻¹' e.base_set) ×ˢ univ,
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
  proj_to_fun := λ y h, rfl }

noncomputable instance fiber_bundle.pullback [∀ x, topological_space (E x)]
  [fiber_bundle F E] (f : K) : fiber_bundle F ((f : B' → B) *ᵖ E) :=
{ total_space_mk_inducing := λ x, inducing_of_inducing_compose
    (pullback.continuous_total_space_mk F E) (pullback.continuous_lift E f)
    (total_space_mk_inducing F E (f x)),
  trivialization_atlas :=
    {ef | ∃ (e : trivialization F (π E)) [mem_trivialization_atlas e], ef = e.pullback f},
  trivialization_at := λ x, (trivialization_at F E (f x)).pullback f,
  mem_base_set_trivialization_at := λ x, mem_base_set_trivialization_at F E (f x),
  trivialization_mem_atlas := λ x, ⟨trivialization_at F E (f x), by apply_instance, rfl⟩ }

end fiber_bundle
end
