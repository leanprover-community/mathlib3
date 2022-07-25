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

An `R`-algebra `A` is formally étale (resp. unramified, smooth) if for every `R`-algebra,
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

/-- An `R`-algebra `A` is formally unramified if for every `R`-algebra, every square-zero ideal
`I : ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at most one lift `A →ₐ[R] B`. -/
@[mk_iff]
class formally_unramified : Prop :=
(comp_injective :
  ∀ ⦃B : Type u⦄ [comm_ring B], by exactI ∀ [algebra R B] (I : ideal B) (hI : I ^ 2 = ⊥), by exactI
    function.injective ((ideal.quotient.mkₐ R I).comp : (A →ₐ[R] B) → (A →ₐ[R] B ⧸ I)))

/-- An `R` algebra `A` is formally smooth if for every `R`-algebra, every square-zero ideal
`I : ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at least one lift `A →ₐ[R] B`. -/
@[mk_iff]
class formally_smooth : Prop :=
(comp_surjective :
  ∀ ⦃B : Type u⦄ [comm_ring B], by exactI ∀ [algebra R B] (I : ideal B) (hI : I ^ 2 = ⊥), by exactI
  function.surjective ((ideal.quotient.mkₐ R I).comp : (A →ₐ[R] B) → (A →ₐ[R] B ⧸ I)))

/-- An `R` algebra `A` is formally étale if for every `R`-algebra, every square-zero ideal
`I : ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists exactly one lift `A →ₐ[R] B`. -/
@[mk_iff]
class formally_etale : Prop :=
(comp_bijective :
  ∀ ⦃B : Type u⦄ [comm_ring B], by exactI ∀ [algebra R B] (I : ideal B) (hI : I ^ 2 = ⊥), by exactI
  function.bijective ((ideal.quotient.mkₐ R I).comp : (A →ₐ[R] B) → (A →ₐ[R] B ⧸ I)))

variables {R A}

lemma formally_etale.iff_unramified_and_smooth :
  formally_etale R A ↔ formally_unramified R A ∧ formally_smooth R A :=
begin
  rw [formally_unramified_iff, formally_smooth_iff, formally_etale_iff],
  simp_rw ← forall_and_distrib,
  refl
end

@[priority 100]
instance formally_etale.to_unramified [h : formally_etale R A] : formally_unramified R A :=
(formally_etale.iff_unramified_and_smooth.mp h).1

@[priority 100]
instance formally_etale.to_smooth [h : formally_etale R A] : formally_smooth R A :=
(formally_etale.iff_unramified_and_smooth.mp h).2

lemma formally_etale.of_unramified_and_smooth [h₁ : formally_unramified R A]
  [h₂ : formally_smooth R A] : formally_etale R A :=
formally_etale.iff_unramified_and_smooth.mpr ⟨h₁, h₂⟩

omit R A

lemma formally_unramified.lift_unique [formally_unramified R A] (I : ideal B)
  (hI : is_nilpotent I) (g₁ g₂ : A →ₐ[R] B) (h : (ideal.quotient.mkₐ R I).comp g₁ =
  (ideal.quotient.mkₐ R I).comp g₂) : g₁ = g₂ :=
begin
  revert g₁ g₂,
  change function.injective (ideal.quotient.mkₐ R I).comp,
  unfreezingI { revert _inst_5 },
  apply ideal.is_nilpotent.induction_on I hI,
  { introsI B _ I hI _, exact formally_unramified.comp_injective I hI },
  { introsI B _ I J hIJ h₁ h₂ _ g₁ g₂ e,
    apply h₁,
    apply h₂,
    ext x,
    replace e := alg_hom.congr_fun e x,
    dsimp only [alg_hom.comp_apply, ideal.quotient.mkₐ_eq_mk] at e ⊢,
    rwa [ideal.quotient.eq, ← map_sub, ideal.mem_quotient_iff_mem hIJ, ← ideal.quotient.eq] },
end

lemma formally_unramified.ext [formally_unramified R A] (hI : is_nilpotent I)
  {g₁ g₂ : A →ₐ[R] B} (H : ∀ x, ideal.quotient.mk I (g₁ x) = ideal.quotient.mk I (g₂ x)) :
  g₁ = g₂ :=
formally_unramified.lift_unique I hI g₁ g₂ (alg_hom.ext H)

lemma formally_smooth.exists_lift [formally_smooth R A] (I : ideal B)
  (hI : is_nilpotent I) (g : A →ₐ[R] B ⧸ I) :
    ∃ f : A →ₐ[R] B, (ideal.quotient.mkₐ R I).comp f = g :=
begin
  revert g,
  change function.surjective (ideal.quotient.mkₐ R I).comp,
  unfreezingI { revert _inst_5 },
  apply ideal.is_nilpotent.induction_on I hI,
  { introsI B _ I hI _, exact formally_smooth.comp_surjective I hI },
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

/-- For a formally smooth `R`-algebra `A` and a map `f : A →ₐ[R] B ⧸ I` with `I` square-zero,
this is an arbitrary lift `A →ₐ[R] B`. -/
noncomputable
def formally_smooth.lift [formally_smooth R A] (I : ideal B)
  (hI : is_nilpotent I) (g : A →ₐ[R] B ⧸ I) : A →ₐ[R] B :=
(formally_smooth.exists_lift I hI g).some

@[simp]
lemma formally_smooth.comp_lift [formally_smooth R A] (I : ideal B)
  (hI : is_nilpotent I) (g : A →ₐ[R] B ⧸ I) :
    (ideal.quotient.mkₐ R I).comp (formally_smooth.lift I hI g) = g :=
(formally_smooth.exists_lift I hI g).some_spec

@[simp]
lemma formally_smooth.mk_lift [formally_smooth R A] (I : ideal B)
  (hI : is_nilpotent I) (g : A →ₐ[R] B ⧸ I) (x : A) :
    ideal.quotient.mk I (formally_smooth.lift I hI g x) = g x :=
alg_hom.congr_fun (formally_smooth.comp_lift I hI g : _) x

end

section of_equiv

variables {R : Type u} [comm_semiring R]
variables {A B : Type u} [semiring A] [algebra R A] [semiring B] [algebra R B]

lemma formally_smooth.of_equiv [formally_smooth R A] (e : A ≃ₐ[R] B) : formally_smooth R B :=
begin
  constructor,
  introsI C _ _ I hI f,
  use (formally_smooth.lift I ⟨2, hI⟩ (f.comp e : A →ₐ[R] C ⧸ I)).comp e.symm,
  rw [← alg_hom.comp_assoc, formally_smooth.comp_lift, alg_hom.comp_assoc, alg_equiv.comp_symm,
    alg_hom.comp_id],
end

lemma formally_unramified.of_equiv [formally_unramified R A] (e : A ≃ₐ[R] B) :
  formally_unramified R B :=
begin
  constructor,
  introsI C _ _ I hI f₁ f₂ e',
  rw [← f₁.comp_id, ← f₂.comp_id, ← e.comp_symm, ← alg_hom.comp_assoc, ← alg_hom.comp_assoc],
  congr' 1,
  refine formally_unramified.comp_injective I hI _,
  rw [← alg_hom.comp_assoc, e', alg_hom.comp_assoc],
end

lemma formally_etale.of_equiv [formally_etale R A] (e : A ≃ₐ[R] B) : formally_etale R B :=
formally_etale.iff_unramified_and_smooth.mpr
  ⟨formally_unramified.of_equiv e, formally_smooth.of_equiv e⟩

end of_equiv

section polynomial

variables (R : Type u) [comm_semiring R]

instance formally_smooth.mv_polynomial (σ : Type u) : formally_smooth R (mv_polynomial σ R) :=
begin
  constructor,
  introsI C _ _ I hI f,
  have : ∀ (s : σ), ∃ c : C, ideal.quotient.mk I c = f (mv_polynomial.X s),
  { exact λ s, ideal.quotient.mk_surjective _ },
  choose g hg,
  refine ⟨mv_polynomial.aeval g, _⟩,
  ext s,
  rw [← hg, alg_hom.comp_apply, mv_polynomial.aeval_X],
  refl,
end

instance formally_smooth.polynomial : formally_smooth R (polynomial R) :=
@@formally_smooth.of_equiv _ _ _ _ _
  (formally_smooth.mv_polynomial R punit) (mv_polynomial.punit_alg_equiv R)

end polynomial

section comp

variables (R : Type u) [comm_semiring R]
variables (A : Type u) [comm_semiring A] [algebra R A]
variables (B : Type u) [semiring B] [algebra R B] [algebra A B] [is_scalar_tower R A B]

lemma formally_smooth.comp [formally_smooth R A] [formally_smooth A B] :
  formally_smooth R B :=
begin
  constructor,
  introsI C _ _ I hI f,
  obtain ⟨f', e⟩ := formally_smooth.comp_surjective I hI
    (f.comp (is_scalar_tower.to_alg_hom R A B)),
  letI := f'.to_ring_hom.to_algebra,
  obtain ⟨f'', e'⟩ := formally_smooth.comp_surjective I hI
    { commutes' := alg_hom.congr_fun e.symm, ..f.to_ring_hom },
  apply_fun (alg_hom.restrict_scalars R) at e',
  exact ⟨f''.restrict_scalars _, e'.trans (alg_hom.ext $ λ _, rfl)⟩,
end

lemma formally_unramified.comp [formally_unramified R A] [formally_unramified A B] :
  formally_unramified R B :=
begin
  constructor,
  introsI C _ _ I hI f₁ f₂ e,
  have e' := formally_unramified.lift_unique I ⟨2, hI⟩ (f₁.comp $ is_scalar_tower.to_alg_hom R A B)
    (f₂.comp $ is_scalar_tower.to_alg_hom R A B)
    (by rw [← alg_hom.comp_assoc, e, alg_hom.comp_assoc]),
  letI := (f₁.comp (is_scalar_tower.to_alg_hom R A B)).to_ring_hom.to_algebra,
  let F₁ : B →ₐ[A] C := { commutes' := λ r, rfl, ..f₁ },
  let F₂ : B →ₐ[A] C := { commutes' := alg_hom.congr_fun e'.symm, ..f₂ },
  ext1,
  change F₁ x = F₂ x,
  congr,
  exact formally_unramified.ext I ⟨2, hI⟩ (alg_hom.congr_fun e),
end

lemma formally_etale.comp [formally_etale R A] [formally_etale A B] : formally_etale R B :=
formally_etale.iff_unramified_and_smooth.mpr
  ⟨formally_unramified.comp R A B, formally_smooth.comp R A B⟩

end comp

end algebra
