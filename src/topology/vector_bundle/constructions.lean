/-
Copyright © 2022 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sébastien Gouëzel, Heather Macbeth, Floris van Doorn
-/
import topology.fiber_bundle.constructions
import topology.vector_bundle.basic

/-!
# Standard constructions on vector bundles

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains several standard constructions on vector bundles:

* `bundle.trivial.vector_bundle 𝕜 B F`: the trivial vector bundle with scalar field `𝕜` and model
  fiber `F` over the base `B`

* `vector_bundle.prod`: for vector bundles `E₁` and `E₂` with scalar field `𝕜` over a common base,
  a vector bundle structure on their direct sum `E₁ ×ᵇ E₂` (the notation stands for
  `λ x, E₁ x × E₂ x`).

* `vector_bundle.pullback`: for a vector bundle `E` over `B`, a vector bundle structure on its
  pullback `f *ᵖ E` by a map `f : B' → B` (the notation is a type synonym for `E ∘ f`).

## Tags
Vector bundle, direct sum, pullback
-/

noncomputable theory

open bundle set fiber_bundle
open_locale classical bundle

/-! ### The trivial vector bundle -/

namespace bundle.trivial
variables (𝕜 : Type*) (B : Type*) (F : Type*)
  [nontrivially_normed_field 𝕜] [normed_add_comm_group F] [normed_space 𝕜 F] [topological_space B]

instance trivialization.is_linear : (trivialization B F).is_linear 𝕜 :=
{ linear := λ x hx, ⟨λ y z, rfl, λ c y, rfl⟩ }

variables {𝕜}

lemma trivialization.coord_changeL (b : B) :
  (trivialization B F).coord_changeL 𝕜 (trivialization B F) b = continuous_linear_equiv.refl 𝕜 F :=
begin
  ext v,
  rw [trivialization.coord_changeL_apply'],
  exacts [rfl, ⟨mem_univ _, mem_univ _⟩]
end

variables (𝕜)

instance vector_bundle : vector_bundle 𝕜 F (bundle.trivial B F) :=
{ trivialization_linear' := begin
    introsI e he,
    rw eq_trivialization B F e,
    apply_instance
  end,
  continuous_on_coord_change' := begin
    introsI e e' he he',
    unfreezingI { obtain rfl := eq_trivialization B F e },
    unfreezingI { obtain rfl := eq_trivialization B F e' },
    simp_rw trivialization.coord_changeL,
    exact continuous_const.continuous_on
  end }

end bundle.trivial

/-! ### Direct sum of two vector bundles -/

section
variables (𝕜 : Type*) {B : Type*} [nontrivially_normed_field 𝕜] [topological_space B]
  (F₁ : Type*) [normed_add_comm_group F₁] [normed_space 𝕜 F₁]
  (E₁ : B → Type*) [topological_space (total_space E₁)]
  (F₂ : Type*) [normed_add_comm_group F₂] [normed_space 𝕜 F₂]
  (E₂ : B → Type*) [topological_space (total_space E₂)]

namespace trivialization
variables {F₁ E₁ F₂ E₂}
  [Π x, add_comm_monoid (E₁ x)] [Π x, module 𝕜 (E₁ x)]
  [Π x, add_comm_monoid (E₂ x)] [Π x, module 𝕜 (E₂ x)]
  (e₁ e₁' : trivialization F₁ (π E₁)) (e₂ e₂' : trivialization F₂ (π E₂))

instance prod.is_linear [e₁.is_linear 𝕜] [e₂.is_linear 𝕜] : (e₁.prod e₂).is_linear 𝕜 :=
{ linear := λ x ⟨h₁, h₂⟩, (((e₁.linear 𝕜 h₁).mk' _).prod_map ((e₂.linear 𝕜 h₂).mk' _)).is_linear }

@[simp]
lemma coord_changeL_prod [e₁.is_linear 𝕜] [e₁'.is_linear 𝕜] [e₂.is_linear 𝕜] [e₂'.is_linear 𝕜] ⦃b⦄
  (hb : b ∈ ((e₁.prod e₂).base_set ∩ (e₁'.prod e₂').base_set)) :
  ((e₁.prod e₂).coord_changeL 𝕜 (e₁'.prod e₂') b : F₁ × F₂ →L[𝕜] F₁ × F₂) =
  (e₁.coord_changeL 𝕜 e₁' b : F₁ →L[𝕜] F₁).prod_map (e₂.coord_changeL 𝕜 e₂' b) :=
begin
  rw [continuous_linear_map.ext_iff, continuous_linear_map.coe_prod_map'],
  rintro ⟨v₁, v₂⟩,
  show (e₁.prod e₂).coord_changeL 𝕜 (e₁'.prod e₂') b (v₁, v₂) =
    (e₁.coord_changeL 𝕜 e₁' b v₁, e₂.coord_changeL 𝕜 e₂' b v₂),
  rw [e₁.coord_changeL_apply e₁', e₂.coord_changeL_apply e₂', (e₁.prod e₂).coord_changeL_apply'],
  exacts [rfl, hb, ⟨hb.1.2, hb.2.2⟩, ⟨hb.1.1, hb.2.1⟩]
end

variables {e₁ e₂} [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂]

lemma prod_apply [e₁.is_linear 𝕜] [e₂.is_linear 𝕜] {x : B} (hx₁ : x ∈ e₁.base_set)
  (hx₂ : x ∈ e₂.base_set) (v₁ : E₁ x) (v₂ : E₂ x) :
  prod e₁ e₂ ⟨x, (v₁, v₂)⟩
  = ⟨x, e₁.continuous_linear_equiv_at 𝕜 x hx₁ v₁, e₂.continuous_linear_equiv_at 𝕜 x hx₂ v₂⟩ :=
rfl

end trivialization

open trivialization

variables [Π x, add_comm_monoid (E₁ x)] [Π x, module 𝕜 (E₁ x)]
  [Π x, add_comm_monoid (E₂ x)] [Π x, module 𝕜 (E₂ x)]
  [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂]

/-- The product of two vector bundles is a vector bundle. -/
instance vector_bundle.prod  [vector_bundle 𝕜 F₁ E₁] [vector_bundle 𝕜 F₂ E₂] :
  vector_bundle 𝕜 (F₁ × F₂) (E₁ ×ᵇ E₂) :=
{ trivialization_linear' := begin
    rintros _ ⟨e₁, e₂, he₁, he₂, rfl⟩, resetI,
    apply_instance
  end,
  continuous_on_coord_change' := begin
    rintros _ _ ⟨e₁, e₂, he₁, he₂, rfl⟩ ⟨e₁', e₂', he₁', he₂', rfl⟩, resetI,
    refine (((continuous_on_coord_change 𝕜 e₁ e₁').mono _).prod_mapL 𝕜
      ((continuous_on_coord_change 𝕜 e₂ e₂').mono _)).congr _;
    dsimp only [base_set_prod] with mfld_simps,
    { mfld_set_tac },
    { mfld_set_tac },
    { rintro b hb,
      rw [continuous_linear_map.ext_iff],
      rintro ⟨v₁, v₂⟩,
      show (e₁.prod e₂).coord_changeL 𝕜 (e₁'.prod e₂') b (v₁, v₂) =
        (e₁.coord_changeL 𝕜 e₁' b v₁, e₂.coord_changeL 𝕜 e₂' b v₂),
      rw [e₁.coord_changeL_apply e₁', e₂.coord_changeL_apply e₂',
        (e₁.prod e₂).coord_changeL_apply'],
      exacts [rfl, hb, ⟨hb.1.2, hb.2.2⟩, ⟨hb.1.1, hb.2.1⟩] }
  end }

variables {𝕜 F₁ E₁ F₂ E₂}

@[simp] lemma trivialization.continuous_linear_equiv_at_prod {e₁ : trivialization F₁ (π E₁)}
  {e₂ : trivialization F₂ (π E₂)} [e₁.is_linear 𝕜] [e₂.is_linear 𝕜] {x : B} (hx₁ : x ∈ e₁.base_set)
  (hx₂ : x ∈ e₂.base_set) :
  (e₁.prod e₂).continuous_linear_equiv_at 𝕜 x ⟨hx₁, hx₂⟩
  = (e₁.continuous_linear_equiv_at 𝕜 x hx₁).prod (e₂.continuous_linear_equiv_at 𝕜 x hx₂) :=
begin
  ext1,
  funext v,
  obtain ⟨v₁, v₂⟩ := v,
  rw [(e₁.prod e₂).continuous_linear_equiv_at_apply 𝕜, trivialization.prod],
  exact (congr_arg prod.snd (prod_apply 𝕜 hx₁ hx₂ v₁ v₂) : _)
end

end

/-! ### Pullbacks of vector bundles -/

section
variables (R 𝕜 : Type*) {B : Type*} (F : Type*) (E : B → Type*) {B' : Type*} (f : B' → B)

instance [∀ (x : B), add_comm_monoid (E x)] : ∀ (x : B'), add_comm_monoid ((f *ᵖ E) x) :=
by delta_instance bundle.pullback
instance [semiring R] [∀ (x : B), add_comm_monoid (E x)] [∀ x, module R (E x)] :
  ∀ (x : B'), module R ((f *ᵖ E) x) :=
by delta_instance bundle.pullback

variables {E F} [topological_space B'] [topological_space (total_space E)]
  [nontrivially_normed_field 𝕜] [normed_add_comm_group F] [normed_space 𝕜 F] [topological_space B]
  [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)]
  {K : Type*} [continuous_map_class K B' B]

instance trivialization.pullback_linear (e : trivialization F (π E)) [e.is_linear 𝕜] (f : K) :
  (@trivialization.pullback _ _ _ B' _ _ _ _ _ _ _ e f).is_linear 𝕜 :=
{ linear := λ x h, e.linear 𝕜 h }

instance vector_bundle.pullback [∀ x, topological_space (E x)]
  [fiber_bundle F E] [vector_bundle 𝕜 F E] (f : K) : vector_bundle 𝕜 F ((f : B' → B) *ᵖ E) :=
{ trivialization_linear' := begin
    rintro _ ⟨e, he, rfl⟩, resetI,
    apply_instance,
  end,
  continuous_on_coord_change' := begin
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩, resetI,
    refine ((continuous_on_coord_change 𝕜 e e').comp (map_continuous f).continuous_on
      (λ b hb, hb)).congr _,
    rintro b (hb : f b ∈ e.base_set ∩ e'.base_set), ext v,
    show ((e.pullback f).coord_changeL 𝕜 (e'.pullback f) b) v = (e.coord_changeL 𝕜 e' (f b)) v,
    rw [e.coord_changeL_apply e' hb, (e.pullback f).coord_changeL_apply' _],
    exacts [rfl, hb]
  end }

end
