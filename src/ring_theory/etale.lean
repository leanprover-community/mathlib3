/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import ring_theory.ideal.operations
import ring_theory.nilpotent
import ring_theory.tensor_product
import linear_algebra.isomorphisms

/-!

# Formally étale morphisms

An `R` algebra `A` is formally étale (resp. unramified, smooth) if for every `R`-algebra,
every square-zero ideal `I : ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
exactly (resp. at most, at least) one lift `A →ₐ[R] B`.

We show that the property extends onto nilpotent ideals, and that these properties are stable
under `R`-algebra homomorphisms and compositions.

-/

universes u

namespace algebra

section

variables (R : Type u) [comm_semiring R]
variables (A : Type u) [semiring A] [algebra R A]
variables {B : Type u} [comm_ring B] [algebra R B] (I : ideal B)

include R A

/-- An `R` algebra `A` is formally unramified if for every `R`-algebra, every square-zero ideal
`I : ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at most one lift `A →ₐ[R] B`. -/
def formally_unramified : Prop :=
∀ ⦃B : Type u⦄ [comm_ring B], by exactI ∀ [algebra R B] (I : ideal B) (hI : I ^ 2 = ⊥), by exactI
  function.injective ((ideal.quotient.mkₐ R I).comp : (A →ₐ[R] B) → (A →ₐ[R] B ⧸ I))

/-- An `R` algebra `A` is formally smooth if for every `R`-algebra, every square-zero ideal
`I : ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at least one lift `A →ₐ[R] B`. -/
def formally_smooth : Prop :=
∀ ⦃B : Type u⦄ [comm_ring B], by exactI ∀ [algebra R B] (I : ideal B) (hI : I ^ 2 = ⊥), by exactI
  function.surjective ((ideal.quotient.mkₐ R I).comp : (A →ₐ[R] B) → (A →ₐ[R] B ⧸ I))

/-- An `R` algebra `A` is formally étale if for every `R`-algebra, every square-zero ideal
`I : ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists exactly one lift `A →ₐ[R] B`. -/
def formally_etale : Prop :=
∀ ⦃B : Type u⦄ [comm_ring B], by exactI ∀ [algebra R B] (I : ideal B) (hI : I ^ 2 = ⊥), by exactI
  function.bijective ((ideal.quotient.mkₐ R I).comp : (A →ₐ[R] B) → (A →ₐ[R] B ⧸ I))

variables {R A}

lemma formally_etale.iff_unramified_and_smooth :
  formally_etale R A ↔ formally_unramified R A ∧ formally_smooth R A :=
begin
  delta formally_unramified formally_smooth,
  simp_rw ← forall_and_distrib,
  refl
end

lemma formally_etale.to_unramified (h : formally_etale R A) : formally_unramified R A :=
(formally_etale.iff_unramified_and_smooth.mp h).1

lemma formally_etale.to_smooth (h : formally_etale R A) : formally_smooth R A :=
(formally_etale.iff_unramified_and_smooth.mp h).2

omit R A

lemma formally_unramified.lift_unique (h : formally_unramified R A) (I : ideal B)
  (hI : is_nilpotent I) (g₁ g₂ : A →ₐ[R] B) (h : (ideal.quotient.mkₐ R I).comp g₁ =
  (ideal.quotient.mkₐ R I).comp g₂) : g₁ = g₂ :=
begin
  revert g₁ g₂,
  change function.injective (ideal.quotient.mkₐ R I).comp,
  unfreezingI { revert _inst_5 },
  apply ideal.is_nilpotent.induction_on I hI,
  { introsI B _ I hI _, exact h I hI },
  { introsI B _ I J hIJ h₁ h₂ _ g₁ g₂ e,
    apply h₁,
    apply h₂,
    ext x,
    replace e := alg_hom.congr_fun e x,
    dsimp only [alg_hom.comp_apply, ideal.quotient.mkₐ_eq_mk] at e ⊢,
    rwa [ideal.quotient.eq, ← map_sub, ideal.mem_quotient_iff_mem hIJ, ← ideal.quotient.eq] },
end

lemma formally_unramified.ext (h : formally_unramified R A) (hI : is_nilpotent I)
  {g₁ g₂ : A →ₐ[R] B} (H : ∀ x, ideal.quotient.mk I (g₁ x) = ideal.quotient.mk I (g₂ x)) :
  g₁ = g₂ :=
h.lift_unique I hI g₁ g₂ (alg_hom.ext H)

lemma formally_smooth.exists_lift (h : formally_smooth R A) (I : ideal B)
  (hI : is_nilpotent I) (g : A →ₐ[R] B ⧸ I) :
    ∃ f : A →ₐ[R] B, (ideal.quotient.mkₐ R I).comp f = g :=
begin
  revert g,
  change function.surjective (ideal.quotient.mkₐ R I).comp,
  unfreezingI { revert _inst_5 },
  apply ideal.is_nilpotent.induction_on I hI,
  { introsI B _ I hI _, exact h I hI },
  { introsI B _ I J hIJ h₁ h₂ _ g,
    let : ((B ⧸ I) ⧸ J.map (ideal.quotient.mk I)) ≃ₐ[R] B ⧸ J :=
      { commutes' := λ x, rfl,
        ..((double_quot.quot_quot_equiv_quot_sup I J).trans
          (ideal.quot_equiv_of_eq (sup_eq_right.mpr hIJ))) },
    obtain ⟨g', e⟩ := h₂ (this.symm.to_alg_hom.comp g),
    obtain ⟨g', rfl⟩ := h₁ g',
    replace e := congr_arg this.to_alg_hom.comp e,
    conv_rhs at e { rw [← alg_hom.comp_assoc, alg_equiv.to_alg_hom_eq_coe,
      alg_equiv.to_alg_hom_eq_coe, alg_equiv.comp_symm, alg_hom.id_comp] },
    exact ⟨g', e⟩ }
end

noncomputable
def formally_smooth.lift (h : formally_smooth R A) (I : ideal B)
  (hI : is_nilpotent I) (g : A →ₐ[R] B ⧸ I) : A →ₐ[R] B :=
(h.exists_lift I hI g).some

@[simp]
lemma formally_smooth.comp_lift (h : formally_smooth R A) (I : ideal B)
  (hI : is_nilpotent I) (g : A →ₐ[R] B ⧸ I) : (ideal.quotient.mkₐ R I).comp (h.lift I hI g) = g :=
(h.exists_lift I hI g).some_spec

@[simp]
lemma formally_smooth.mk_lift (h : formally_smooth R A) (I : ideal B)
  (hI : is_nilpotent I) (g : A →ₐ[R] B ⧸ I) (x : A) :
    ideal.quotient.mk I (h.lift I hI g x) = g x :=
alg_hom.congr_fun (h.comp_lift I hI g) x

end

section of_equiv

variables {R : Type u} [comm_semiring R]
variables {A B : Type u} [semiring A] [algebra R A] [semiring B] [algebra R B]

lemma formally_smooth.of_equiv (h : formally_smooth R A) (e : A ≃ₐ[R] B) : formally_smooth R B :=
begin
  introsI C _ _ I hI f,
  obtain ⟨f', e'⟩ := h I hI (f.comp e),
  use f'.comp e.symm,
  rw [← alg_hom.comp_assoc, e', alg_hom.comp_assoc, alg_equiv.comp_symm, alg_hom.comp_id],
end

lemma formally_unramified.of_equiv (h : formally_unramified R A) (e : A ≃ₐ[R] B) :
  formally_unramified R B :=
begin
  introsI C _ _ I hI f₁ f₂ e',
  rw [← f₁.comp_id, ← f₂.comp_id, ← e.comp_symm, ← alg_hom.comp_assoc, ← alg_hom.comp_assoc],
  congr' 1,
  apply h I hI,
  rw [← alg_hom.comp_assoc, e', alg_hom.comp_assoc],
end

lemma formally_etale.of_equiv (h : formally_etale R A) (e : A ≃ₐ[R] B) : formally_etale R B :=
formally_etale.iff_unramified_and_smooth.mpr ⟨h.to_unramified.of_equiv e, h.to_smooth.of_equiv e⟩

end of_equiv

section polynomial

variables (R : Type u) [comm_semiring R]

lemma formally_smooth.mv_polynomial (σ : Type u) : formally_smooth R (mv_polynomial σ R) :=
begin
  introsI C _ _ I hI f,
  have : ∀ (s : σ), ∃ c : C, ideal.quotient.mk I c = f (mv_polynomial.X s),
  { exact λ s, ideal.quotient.mk_surjective _ },
  choose g hg,
  refine ⟨mv_polynomial.aeval g, _⟩,
  ext s,
  rw [← hg, alg_hom.comp_apply, mv_polynomial.aeval_X],
  refl,
end

lemma formally_smooth.polynomial : formally_smooth R (polynomial R) :=
(formally_smooth.mv_polynomial R punit).of_equiv (mv_polynomial.punit_alg_equiv R)

end polynomial

section comp

variables {R : Type u} [comm_semiring R]
variables {A : Type u} [comm_semiring A] [algebra R A]
variables {B : Type u} [semiring B] [algebra R B] [algebra A B] [is_scalar_tower R A B]

lemma formally_smooth.comp (h : formally_smooth R A) (h' : formally_smooth A B) :
  formally_smooth R B :=
begin
  introsI C _ _ I hI f,
  obtain ⟨f', e⟩ := h I hI (f.comp (is_scalar_tower.to_alg_hom R A B)),
  letI := f'.to_ring_hom.to_algebra,
  obtain ⟨f'', e'⟩ := h' I hI { commutes' := alg_hom.congr_fun e.symm, ..f.to_ring_hom },
  apply_fun (alg_hom.restrict_scalars R) at e',
  exact ⟨f''.restrict_scalars _, e'.trans (alg_hom.ext $ λ _, rfl)⟩,
end

lemma formally_unramified.comp (h : formally_unramified R A) (h' : formally_unramified A B) :
  formally_unramified R B :=
begin
  introsI C _ _ I hI f₁ f₂ e,
  have e' := h.lift_unique I ⟨2, hI⟩ (f₁.comp $ is_scalar_tower.to_alg_hom R A B)
    (f₂.comp $ is_scalar_tower.to_alg_hom R A B)
    (by rw [← alg_hom.comp_assoc, e, alg_hom.comp_assoc]),
  letI := (f₁.comp (is_scalar_tower.to_alg_hom R A B)).to_ring_hom.to_algebra,
  let F₁ : B →ₐ[A] C := { commutes' := λ r, rfl, ..f₁ },
  let F₂ : B →ₐ[A] C := { commutes' := alg_hom.congr_fun e'.symm, ..f₂ },
  suffices : F₁ = F₂, { ext1, change F₁ x = F₂ x, rw this },
  apply h'.ext I ⟨2, hI⟩,
  exact alg_hom.congr_fun e,
end

lemma formally_etale.comp (h : formally_etale R A) (h' : formally_etale A B) : formally_etale R B :=
formally_etale.iff_unramified_and_smooth.mpr
  ⟨h.to_unramified.comp h'.to_unramified, h.to_smooth.comp h'.to_smooth⟩

end comp

end algebra
