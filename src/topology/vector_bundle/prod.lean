/-
Copyright © 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn
-/

import topology.vector_bundle.basic

/-!
# Direct sum of two vector bundles

If `E₁ : B → Type*` and `E₂ : B → Type*` define two topological vector bundles over `R` with fiber
models `F₁` and `F₂`, we define the bundle of direct sums `E₁ ×ᵇ E₂ := λ x, E₁ x × E₂ x`.
We can endow `E₁ ×ᵇ E₂` with a topological vector bundle structure:
`bundle.prod.topological_vector_bundle`.

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

variables [nontrivially_normed_field R] [topological_space B]

variables (F₁ : Type*) [normed_add_comm_group F₁] [normed_space R F₁]
  (E₁ : B → Type*) [topological_space (total_space E₁)]
  [Π x, add_comm_monoid (E₁ x)] [Π x, module R (E₁ x)]

variables (F₂ : Type*) [normed_add_comm_group F₂] [normed_space R F₂]
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
  [topological_vector_bundle R F₁ E₁] [topological_vector_bundle R F₂ E₂]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
trivialization for the direct sum of `E₁` and `E₂`, whose base set is `e₁.base_set ∩ e₂.base_set`.
-/
@[nolint unused_arguments]
def prod : trivialization R (F₁ × F₂) (E₁ ×ᵇ E₂) :=
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

section sections

/-! ### Sections of topological vector bundles

## Sections

In this file we also prove that sections of vector bundles inherit the algebraic structures of the
fibers. The proofs of this are the standard mathematical proofs: continuity is read through
trivializations on the fibers, where checking the continuity of algebraic operations is
straightforward.

-/

open topological_vector_bundle

variables {R B E F} [nondiscrete_normed_field R] [topological_space (total_space E)]
  [∀ x, topological_space (E x)] [Π (x : B), add_comm_monoid (E x)]
  [Π (x : B), module R (E x)] [normed_group F] [normed_space R F]
  [topological_space B] [topological_vector_bundle R F E]

lemma right_inv.image_mem_trivialization_at_source (f : right_inv (proj E)) (b : B) :
  f b ∈ (trivialization_at R F E b).source :=
f.mem_base_set_image_mem_source (mem_base_set_trivialization_at R F E b)

variables (R F E)

lemma bundle_section.continuous_at_iff_continuous_within_at_triv_at (f : bundle_section E) (b : B) :
  continuous_at f b ↔ continuous_within_at (λ x, ((trivialization_at R F E b) (f x)).snd)
  (trivialization_at R F E b).base_set b :=
(f : right_inv (proj E)).continuous_at_iff_continuous_within_at (trivialization_at R F E b)
  (mem_base_set_trivialization_at R F E b)

lemma bundle_section.continuous_within_at_iff_continuous_within_at_triv_at
  (f : bundle_section E) (U : set B) (b : B) :
  continuous_within_at f U b ↔ continuous_within_at (λ x, ((trivialization_at R F E b) (f x)).snd)
  (U ∩ (trivialization_at R F E b).base_set) b :=
(f : right_inv (proj E)).continuous_within_at_iff_continuous_within_at (trivialization_at R F E b)
  (mem_base_set_trivialization_at R F E b)

variables {E}

section

include R F

lemma continuous_within_at.add_section [has_continuous_add F] {g h : bundle_section E} {U : set B}
  {b : B} (hg : continuous_within_at g U b) (hh : continuous_within_at h U b) :
  continuous_within_at ⇑(g + h) U b :=
((g + h).continuous_within_at_iff_continuous_within_at_triv_at R F E U b).mpr
  ((continuous_add.continuous_at.comp_continuous_within_at
  (((g.continuous_within_at_iff_continuous_within_at_triv_at R F E U b).mp hg).prod
  ((h.continuous_within_at_iff_continuous_within_at_triv_at R F E U b).mp hh))).congr
  (λ y hy, trivialization.snd_map_add hy.2)
  (trivialization.snd_map_add (mem_base_set_trivialization_at R F E b)))

lemma continuous_at.add_section [has_continuous_add F] {g h : bundle_section E} {b : B}
  (hg : continuous_at g b) (hh : continuous_at h b) :
  continuous_at (↑(g + h) : B → total_space E) b :=
by { rw ←continuous_within_at_univ at hg hh ⊢, exact hg.add_section R F hh }

lemma continuous_on.add_section [has_continuous_add F] {g h : bundle_section E} {U : set B}
  (hg : continuous_on g U) (hh : continuous_on h U) :
  continuous_on (↑(g + h) : B → total_space E) U :=
λ b hb, (hg.continuous_within_at hb).add_section R F (hh.continuous_within_at hb)

lemma continuous.add_section [has_continuous_add F] {g h : bundle_section E} (hg : continuous g)
  (hh : continuous h) : continuous ⇑(g + h) :=
continuous_iff_continuous_at.mpr (λ b, hg.continuous_at.add_section R F hh.continuous_at)

lemma continuous_within_at.zero_section (U : set B) (b : B) :
  continuous_within_at ⇑(0 : bundle_section E) U b :=
((0 : bundle_section E).continuous_within_at_iff_continuous_within_at_triv_at R F E U b).mpr
  (continuous_within_at_const.congr (λ y hy, trivialization.snd_map_zero hy.2)
  (trivialization.snd_map_zero (mem_base_set_trivialization_at R F E b)))

lemma continuous_at.zero_section (b : B) : continuous_at ⇑(0 : bundle_section E) b :=
(continuous_within_at_univ _ b).mp (continuous_within_at.zero_section R F univ b)

lemma continuous_on.zero_section (U : set B) : continuous_on ⇑(0 : bundle_section E) U :=
λ b hb, continuous_within_at.zero_section R F U b

lemma continuous.zero_section : continuous ⇑(0 : bundle_section E) :=
continuous_iff_continuous_at.mpr (λ b, continuous_at.zero_section R F b)

variables {R} [topological_space R] [has_continuous_smul R F]

lemma continuous_within_at.smul_section {g : bundle_section E} {U : set B} {b : B}
  (hg : continuous_within_at g U b) (r : R) :
  continuous_within_at ⇑(r • g : bundle_section E) U b :=
((r • g).continuous_within_at_iff_continuous_within_at_triv_at R F E U b).mpr
  ((((g.continuous_within_at_iff_continuous_within_at_triv_at R F E U b).mp hg).const_smul r).congr
  (λ y hy, trivialization.snd_map_smul hy.2) (trivialization.snd_map_smul
  (mem_base_set_trivialization_at R F E b)))

lemma continuous_at.smul_section {g : bundle_section E} {b : B}
  (hg : continuous_at g b) (r : R) : continuous_at ⇑(r • g : bundle_section E) b :=
by { rw ←continuous_within_at_univ at hg ⊢, exact hg.smul_section F r }

lemma continuous_on.smul_section {g : bundle_section E} {U : set B}
  (hg : continuous_on g U) (r : R) : continuous_on ⇑(r • g : bundle_section E) U :=
λ b hb, (hg.continuous_within_at hb).smul_section F r

lemma continuous.smul_section {g : bundle_section E} (hg : continuous g) (r : R) :
  continuous ⇑(r • g : bundle_section E) :=
continuous_iff_continuous_at.mpr (λ b, hg.continuous_at.smul_section F r)

end

end sections

section group

open topological_vector_bundle

variables {E R F}
variables [nondiscrete_normed_field R] [∀ x, add_comm_group (E x)] [∀ x, module R (E x)]
  [normed_group F] [normed_space R F] [topological_space B]
  [topological_space (total_space E)] [∀ x, topological_space (E x)]
  [topological_vector_bundle R F E]

namespace trivialization

lemma map_neg {g : bundle_section E}
  {e : trivialization R F E} {b : B} (hb : b ∈ e.base_set) :
  (e ((- (g : bundle_section E)) b)).snd = - (e ((g : right_inv (proj E)) b)).snd :=
begin

  rw [(trivialization.continuous_linear_equiv_apply hb).symm, pi.neg_apply,
    continuous_linear_equiv.map_neg],
  refl,
end

lemma snd_map_sub {g h : bundle_section E} {e : trivialization R F E} {b : B}
  (hb : b ∈ e.base_set) : (e ((g - h) b)).snd = (e (g b)).snd - (e (h b)).snd :=
begin
  rw [(trivialization.continuous_linear_equiv_apply hb).symm, pi.sub_apply,
    continuous_linear_equiv.map_sub],
  refl,
end

end trivialization

include R F

section neg

variables (R F) [has_continuous_neg F]

lemma continuous_within_at.neg_section {g : bundle_section E} {U : set B} {b : B}
  (hg : continuous_within_at g U b) : continuous_within_at ⇑(- g) U b :=
((- g).continuous_within_at_iff_continuous_within_at_triv_at R F E U b).mpr
  ((((g.continuous_within_at_iff_continuous_within_at_triv_at R F E U b).mp hg).neg).congr (λ y hy,
  trivialization.map_neg hy.2) (trivialization.map_neg (mem_base_set_trivialization_at R F E b)))

lemma continuous_at.neg_section {g : bundle_section E} {b : B}
  (hg : continuous_at g b) : continuous_at ⇑(- g) b :=
by { rw ←continuous_within_at_univ at hg ⊢, exact hg.neg_section R F }

lemma continuous_on.neg_section {g : bundle_section E} {U : set B}
  (hg : continuous_on g U) : continuous_on ⇑(- g) U :=
λ b hb, (hg.continuous_within_at hb).neg_section R F

lemma continuous.neg_section {g : bundle_section E}
  (hg : continuous g) : continuous ⇑(- g) :=
continuous_iff_continuous_at.mpr (λ b, hg.continuous_at.neg_section R F)

end neg

section sub

variables (R F) [has_continuous_sub F]

lemma continuous_within_at.sub_section {g h : bundle_section E} {U : set B} {b : B}
  (hg : continuous_within_at g U b) (hh : continuous_within_at h U b) :
  continuous_within_at ⇑(g - h) U b :=
((g - h).continuous_within_at_iff_continuous_within_at_triv_at R F E U b).mpr
  ((continuous_sub.continuous_at.comp_continuous_within_at
  (((g.continuous_within_at_iff_continuous_within_at_triv_at R F E U b).mp hg).prod
  ((h.continuous_within_at_iff_continuous_within_at_triv_at R F E U b).mp hh))).congr
  (λ y hy, trivialization.snd_map_sub hy.2) (trivialization.snd_map_sub
  (mem_base_set_trivialization_at R F E b)))

lemma continuous_at.sub_section {g h : bundle_section E} {b : B}
  (hg : continuous_at g b) (hh : continuous_at h b) :
  continuous_at (↑(g - h) : B → total_space E) b :=
by { rw ←continuous_within_at_univ at hg hh ⊢, exact hg.sub_section R F hh }

lemma continuous_on.sub_section {g h : bundle_section E} {U : set B}
  (hg : continuous_on g U) (hh : continuous_on h U) :
  continuous_on (↑(g - h) : B → total_space E) U :=
λ b hb, (hg.continuous_within_at hb).sub_section R F (hh.continuous_within_at hb)

lemma continuous.sub_section {g h : bundle_section E} (hg : continuous g)
  (hh : continuous h) : continuous ⇑(g - h) :=
continuous_iff_continuous_at.mpr (λ b, hg.continuous_at.sub_section R F hh.continuous_at)

end sub

end group
