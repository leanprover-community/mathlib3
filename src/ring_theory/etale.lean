/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import ring_theory.quotient_nilpotent
import ring_theory.derivation

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

lemma formally_unramified.lift_unique {B : Type u} [comm_ring B] [_RB : algebra R B]
  [formally_unramified R A] (I : ideal B)
  (hI : is_nilpotent I) (g₁ g₂ : A →ₐ[R] B) (h : (ideal.quotient.mkₐ R I).comp g₁ =
  (ideal.quotient.mkₐ R I).comp g₂) : g₁ = g₂ :=
begin
  revert g₁ g₂,
  change function.injective (ideal.quotient.mkₐ R I).comp,
  unfreezingI { revert _RB },
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

lemma formally_unramified.lift_unique_of_ring_hom [formally_unramified R A]
  {C : Type u} [comm_ring C] (f : B →+* C) (hf : is_nilpotent f.ker)
  (g₁ g₂ : A →ₐ[R] B) (h : f.comp ↑g₁ = f.comp (g₂ : A →+* B)) : g₁ = g₂ :=
formally_unramified.lift_unique _ hf _ _
begin
  ext x,
  have := ring_hom.congr_fun h x,
  simpa only [ideal.quotient.eq, function.comp_app, alg_hom.coe_comp, ideal.quotient.mkₐ_eq_mk,
    ring_hom.mem_ker, map_sub, sub_eq_zero],
end

lemma formally_unramified.ext' [formally_unramified R A]
  {C : Type u} [comm_ring C] (f : B →+* C) (hf : is_nilpotent f.ker)
  (g₁ g₂ : A →ₐ[R] B) (h : ∀ x, f (g₁ x) = f (g₂ x)) : g₁ = g₂ :=
formally_unramified.lift_unique_of_ring_hom f hf g₁ g₂ (ring_hom.ext h)

lemma formally_unramified.lift_unique' [formally_unramified R A]
  {C : Type u} [comm_ring C] [algebra R C] (f : B →ₐ[R] C) (hf : is_nilpotent (f : B →+* C).ker)
  (g₁ g₂ : A →ₐ[R] B) (h : f.comp g₁ = f.comp g₂) : g₁ = g₂ :=
formally_unramified.ext' _ hf g₁ g₂ (alg_hom.congr_fun h)

lemma formally_smooth.exists_lift {B : Type u} [comm_ring B] [_RB : algebra R B]
  [formally_smooth R A] (I : ideal B)
  (hI : is_nilpotent I) (g : A →ₐ[R] B ⧸ I) :
    ∃ f : A →ₐ[R] B, (ideal.quotient.mkₐ R I).comp f = g :=
begin
  revert g,
  change function.surjective (ideal.quotient.mkₐ R I).comp,
  unfreezingI { revert _RB },
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

variables {C : Type u} [comm_ring C] [algebra R C]

/-- For a formally smooth `R`-algebra `A` and a map `f : A →ₐ[R] B ⧸ I` with `I` nilpotent,
this is an arbitrary lift `A →ₐ[R] B`. -/
noncomputable
def formally_smooth.lift_of_surjective [formally_smooth R A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
  (hg : function.surjective g) (hg' : is_nilpotent (g : B →+* C).ker) : A →ₐ[R] B :=
formally_smooth.lift _ hg'
  ((ideal.quotient_ker_alg_equiv_of_surjective hg).symm.to_alg_hom.comp f)

@[simp]
lemma formally_smooth.lift_of_surjective_apply [formally_smooth R A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
  (hg : function.surjective g) (hg' : is_nilpotent (g : B →+* C).ker) (x : A) :
    g (formally_smooth.lift_of_surjective f g hg hg' x) = f x :=
begin
  apply (ideal.quotient_ker_alg_equiv_of_surjective hg).symm.injective,
  change _ = ((ideal.quotient_ker_alg_equiv_of_surjective hg).symm.to_alg_hom.comp f) x,
  rw [← formally_smooth.mk_lift _ hg'
    ((ideal.quotient_ker_alg_equiv_of_surjective hg).symm.to_alg_hom.comp f)],
  apply (ideal.quotient_ker_alg_equiv_of_surjective hg).injective,
  rw [alg_equiv.apply_symm_apply, ideal.quotient_ker_alg_equiv_of_surjective,
    ideal.quotient_ker_alg_equiv_of_right_inverse.apply],
  exact (ideal.ker_lift_alg_mk _ _).symm
end

@[simp]
lemma formally_smooth.comp_lift_of_surjective [formally_smooth R A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
  (hg : function.surjective g) (hg' : is_nilpotent (g : B →+* C).ker) :
    g.comp (formally_smooth.lift_of_surjective f g hg hg') = f :=
alg_hom.ext (formally_smooth.lift_of_surjective_apply f g hg hg')

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

open_locale polynomial
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

instance formally_smooth.polynomial : formally_smooth R R[X] :=
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

lemma formally_unramified.of_comp [formally_unramified R B] :
  formally_unramified A B :=
begin
  constructor,
  introsI Q _ _ I e f₁ f₂ e',
  letI := ((algebra_map A Q).comp (algebra_map R A)).to_algebra,
  letI : is_scalar_tower R A Q := is_scalar_tower.of_algebra_map_eq' rfl,
  refine alg_hom.restrict_scalars_injective R _,
  refine formally_unramified.ext I ⟨2, e⟩ _,
  intro x,
  exact alg_hom.congr_fun e' x
end

lemma formally_etale.comp [formally_etale R A] [formally_etale A B] : formally_etale R B :=
formally_etale.iff_unramified_and_smooth.mpr
  ⟨formally_unramified.comp R A B, formally_smooth.comp R A B⟩

end comp

section of_surjective

variables {R S : Type u} [comm_ring R] [comm_semiring S]
variables {P A : Type u} [comm_ring A] [algebra R A] [comm_ring P] [algebra R P]
variables (I : ideal P) (f : P →ₐ[R] A) (hf : function.surjective f)

lemma formally_smooth.of_split [formally_smooth R P] (g : A →ₐ[R] P ⧸ f.to_ring_hom.ker ^ 2)
  (hg : f.ker_square_lift.comp g = alg_hom.id R A) :
  formally_smooth R A :=
begin
  constructor,
  introsI C _ _ I hI i,
  let l : P ⧸ f.to_ring_hom.ker ^ 2 →ₐ[R] C,
  { refine ideal.quotient.liftₐ _ (formally_smooth.lift I ⟨2, hI⟩ (i.comp f)) _,
    have : ring_hom.ker f ≤ I.comap (formally_smooth.lift I ⟨2, hI⟩ (i.comp f)),
    { rintros x (hx : f x = 0),
      have : _ = i (f x) := (formally_smooth.mk_lift I ⟨2, hI⟩ (i.comp f) x : _),
      rwa [hx, map_zero, ← ideal.quotient.mk_eq_mk, submodule.quotient.mk_eq_zero] at this },
    intros x hx,
    have := (ideal.pow_mono this 2).trans (ideal.le_comap_pow _ 2) hx,
    rwa hI at this },
  have : i.comp f.ker_square_lift = (ideal.quotient.mkₐ R _).comp l,
  { apply alg_hom.coe_ring_hom_injective,
    apply ideal.quotient.ring_hom_ext,
    ext x,
    exact (formally_smooth.mk_lift I ⟨2, hI⟩ (i.comp f) x).symm },
  exact ⟨l.comp g, by rw [← alg_hom.comp_assoc, ← this, alg_hom.comp_assoc, hg, alg_hom.comp_id]⟩
end

include hf

/-- Let `P →ₐ[R] A` be a surjection with kernel `J`, and `P` a formally smooth `R`-algebra,
then `A` is formally smooth over `R` iff the surjection `P ⧸ J ^ 2 →ₐ[R] A` has a section.

Geometric intuition: we require that a first-order thickening of `Spec A` inside `Spec P` admits
a retraction. -/
lemma formally_smooth.iff_split_surjection [formally_smooth R P] :
  formally_smooth R A ↔ ∃ g, f.ker_square_lift.comp g = alg_hom.id R A :=
begin
  split,
  { introI,
    have surj : function.surjective f.ker_square_lift :=
      λ x, ⟨submodule.quotient.mk (hf x).some, (hf x).some_spec⟩,
    have sqz : ring_hom.ker f.ker_square_lift.to_ring_hom ^ 2 = 0,
    { rw [alg_hom.ker_ker_sqare_lift, ideal.cotangent_ideal_square, ideal.zero_eq_bot] },
    refine ⟨formally_smooth.lift _ ⟨2, sqz⟩
      (ideal.quotient_ker_alg_equiv_of_surjective surj).symm.to_alg_hom, _⟩,
    ext x,
    have := (ideal.quotient_ker_alg_equiv_of_surjective surj).to_alg_hom.congr_arg
      (formally_smooth.mk_lift _ ⟨2, sqz⟩
        (ideal.quotient_ker_alg_equiv_of_surjective surj).symm.to_alg_hom x),
    dsimp at this,
    rw [alg_equiv.apply_symm_apply] at this,
    conv_rhs { rw [← this, alg_hom.id_apply] },
    obtain ⟨y, e⟩ := ideal.quotient.mk_surjective (formally_smooth.lift _ ⟨2, sqz⟩
      (ideal.quotient_ker_alg_equiv_of_surjective surj).symm.to_alg_hom x),
    dsimp at e ⊢,
    rw ← e,
    refl },
  { rintro ⟨g, hg⟩, exact formally_smooth.of_split f g hg }
end

end of_surjective

section unramified_derivation

open_locale tensor_product

variables {R S : Type u} [comm_ring R] [comm_ring S] [algebra R S]

instance formally_unramified.subsingleton_kaehler_differential [formally_unramified R S] :
  subsingleton Ω[S⁄R] :=
begin
  rw ← not_nontrivial_iff_subsingleton,
  introsI h,
  obtain ⟨f₁, f₂, e⟩ := (kaehler_differential.End_equiv R S).injective.nontrivial,
  apply e,
  ext1,
  apply formally_unramified.lift_unique' _ _ _ _ (f₁.2.trans f₂.2.symm),
  rw [← alg_hom.to_ring_hom_eq_coe, alg_hom.ker_ker_sqare_lift],
  exact ⟨_, ideal.cotangent_ideal_square _⟩,
end

lemma formally_unramified.iff_subsingleton_kaehler_differential :
  formally_unramified R S ↔ subsingleton Ω[S⁄R] :=
begin
  split,
  { introsI, apply_instance },
  { introI H,
    constructor,
    introsI B _ _ I hI f₁ f₂ e,
    letI := f₁.to_ring_hom.to_algebra,
    haveI := is_scalar_tower.of_algebra_map_eq' (f₁.comp_algebra_map).symm,
    have := ((kaehler_differential.linear_map_equiv_derivation R S).to_equiv.trans
      (derivation_to_square_zero_equiv_lift I hI)).surjective.subsingleton,
    exact subtype.ext_iff.mp (@@subsingleton.elim this ⟨f₁, rfl⟩ ⟨f₂, e.symm⟩) }
end

end unramified_derivation

section base_change

open_locale tensor_product

variables {R : Type u} [comm_semiring R]
variables {A : Type u} [semiring A] [algebra R A]
variables (B : Type u) [comm_semiring B] [algebra R B]


instance formally_unramified.base_change [formally_unramified R A] :
  formally_unramified B (B ⊗[R] A) :=
begin
  constructor,
  introsI C _ _ I hI f₁ f₂ e,
  letI := ((algebra_map B C).comp (algebra_map R B)).to_algebra,
  haveI : is_scalar_tower R B C := is_scalar_tower.of_algebra_map_eq' rfl,
  apply alg_hom.restrict_scalars_injective R,
  apply tensor_product.ext,
  any_goals { apply_instance },
  intros b a,
  have : b ⊗ₜ[R] a = b • (1 ⊗ₜ a), by { rw [tensor_product.smul_tmul', smul_eq_mul, mul_one] },
  rw [this, alg_hom.restrict_scalars_apply, alg_hom.restrict_scalars_apply, map_smul, map_smul],
  congr' 1,
  change ((f₁.restrict_scalars R).comp tensor_product.include_right) a =
    ((f₂.restrict_scalars R).comp tensor_product.include_right) a,
  congr' 1,
  refine formally_unramified.ext I ⟨2, hI⟩ _,
  intro x,
  exact alg_hom.congr_fun e (1 ⊗ₜ x)
end

instance formally_smooth.base_change [formally_smooth R A] :
  formally_smooth B (B ⊗[R] A) :=
begin
  constructor,
  introsI C _ _ I hI f,
  letI := ((algebra_map B C).comp (algebra_map R B)).to_algebra,
  haveI : is_scalar_tower R B C := is_scalar_tower.of_algebra_map_eq' rfl,
  refine ⟨tensor_product.product_left_alg_hom (algebra.of_id B C) _, _⟩,
  { exact formally_smooth.lift I ⟨2, hI⟩
      ((f.restrict_scalars R).comp tensor_product.include_right) },
  { apply alg_hom.restrict_scalars_injective R,
    apply tensor_product.ext,
    any_goals { apply_instance },
    intros b a,
    suffices : algebra_map B _ b * f (1 ⊗ₜ[R] a) = f (b ⊗ₜ[R] a),
    { simpa [algebra.of_id_apply] },
    rw [← algebra.smul_def, ← map_smul, tensor_product.smul_tmul', smul_eq_mul, mul_one] },
end

instance formally_etale.base_change [formally_etale R A] :
  formally_etale B (B ⊗[R] A) :=
formally_etale.iff_unramified_and_smooth.mpr ⟨infer_instance, infer_instance⟩

end base_change

section localization

variables {R S Rₘ Sₘ : Type u} [comm_ring R] [comm_ring S] [comm_ring Rₘ] [comm_ring Sₘ]
variables (M : submonoid R)
variables [algebra R S] [algebra R Sₘ] [algebra S Sₘ] [algebra R Rₘ] [algebra Rₘ Sₘ]
variables [is_scalar_tower R Rₘ Sₘ] [is_scalar_tower R S Sₘ]
variables [is_localization M Rₘ] [is_localization (M.map (algebra_map R S)) Sₘ]
local attribute [elab_as_eliminator] ideal.is_nilpotent.induction_on

include M

lemma formally_smooth.of_is_localization : formally_smooth R Rₘ :=
begin
  constructor,
  introsI Q _ _ I e f,
  have : ∀ x : M, is_unit (algebra_map R Q x),
  { intro x,
    apply (is_nilpotent.is_unit_quotient_mk_iff ⟨2, e⟩).mp,
    convert (is_localization.map_units Rₘ x).map f,
    simp only [ideal.quotient.mk_algebra_map, alg_hom.commutes] },
  let : Rₘ →ₐ[R] Q := { commutes' := is_localization.lift_eq this, ..(is_localization.lift this) },
  use this,
  apply alg_hom.coe_ring_hom_injective,
  refine is_localization.ring_hom_ext M _,
  ext,
  simp,
end

/-- This holds in general for epimorphisms. -/
lemma formally_unramified.of_is_localization : formally_unramified R Rₘ :=
begin
  constructor,
  introsI Q _ _ I e f₁ f₂ e,
  apply alg_hom.coe_ring_hom_injective,
  refine is_localization.ring_hom_ext M _,
  ext,
  simp,
end

lemma formally_etale.of_is_localization : formally_etale R Rₘ :=
formally_etale.iff_unramified_and_smooth.mpr
  ⟨formally_unramified.of_is_localization M, formally_smooth.of_is_localization M⟩

lemma formally_smooth.localization_base [formally_smooth R Sₘ] : formally_smooth Rₘ Sₘ :=
begin
  constructor,
  introsI Q _ _ I e f,
  letI := ((algebra_map Rₘ Q).comp (algebra_map R Rₘ)).to_algebra,
  letI : is_scalar_tower R Rₘ Q := is_scalar_tower.of_algebra_map_eq' rfl,
  let f : Sₘ →ₐ[Rₘ] Q,
  { refine { commutes' := _, ..(formally_smooth.lift I ⟨2, e⟩ (f.restrict_scalars R)) },
    intro r,
    change (ring_hom.comp (formally_smooth.lift I ⟨2, e⟩ (f.restrict_scalars R) : Sₘ →+* Q)
      (algebra_map _ _)) r = algebra_map _ _ r,
    congr' 1,
    refine is_localization.ring_hom_ext M _,
    rw [ring_hom.comp_assoc, ← is_scalar_tower.algebra_map_eq, ← is_scalar_tower.algebra_map_eq,
      alg_hom.comp_algebra_map] },
  use f,
  ext,
  simp,
end

/-- This actually does not need the localization instance, and is stated here again for
consistency. See `algebra.formally_unramified.of_comp` instead.

 The intended use is for copying proofs between `formally_{unramified, smooth, etale}`
 without the need to change anything (including removing redundant arguments). -/
@[nolint unused_arguments]
lemma formally_unramified.localization_base [formally_unramified R Sₘ] :
  formally_unramified Rₘ Sₘ :=
formally_unramified.of_comp R Rₘ Sₘ

lemma formally_etale.localization_base [formally_etale R Sₘ] : formally_etale Rₘ Sₘ :=
formally_etale.iff_unramified_and_smooth.mpr
  ⟨formally_unramified.localization_base M, formally_smooth.localization_base M⟩

lemma formally_smooth.localization_map [formally_smooth R S] : formally_smooth Rₘ Sₘ :=
begin
  haveI : formally_smooth S Sₘ := formally_smooth.of_is_localization (M.map (algebra_map R S)),
  haveI : formally_smooth R Sₘ := formally_smooth.comp R S Sₘ,
  exact formally_smooth.localization_base M
end

lemma formally_unramified.localization_map [formally_unramified R S] : formally_unramified Rₘ Sₘ :=
begin
  haveI : formally_unramified S Sₘ :=
    formally_unramified.of_is_localization (M.map (algebra_map R S)),
  haveI : formally_unramified R Sₘ := formally_unramified.comp R S Sₘ,
  exact formally_unramified.localization_base M
end

lemma formally_etale.localization_map [formally_etale R S] : formally_etale Rₘ Sₘ :=
begin
  haveI : formally_etale S Sₘ := formally_etale.of_is_localization (M.map (algebra_map R S)),
  haveI : formally_etale R Sₘ := formally_etale.comp R S Sₘ,
  exact formally_etale.localization_base M
end

end localization

end algebra
