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

variables {C : Type u} [comm_ring C] [algebra R C]

/-- For a formally smooth `R`-algebra `A` and a map `f : A →ₐ[R] B ⧸ I` with `I` square-zero,
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

section of_surjective

variables {R S : Type u} [comm_ring R] [comm_semiring S]
variables {P A : Type u} [comm_ring A] [algebra R A] [comm_ring P] [algebra R P]
variables (I : ideal P) (f : P →ₐ[R] A) (hf : function.surjective f)

local notation `P⧸J^2→A` :=
(ideal.quotient.liftₐ (f.to_ring_hom.ker ^ 2) f (λ a ha, ideal.pow_le_self two_ne_zero ha))

lemma formally_smooth.of_split [formally_smooth R P] (g : A →ₐ[R] P ⧸ f.to_ring_hom.ker ^ 2)
  (hg : P⧸J^2→A .comp g = alg_hom.id R A) :
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
  have : i.comp P⧸J^2→A = (ideal.quotient.mkₐ R _).comp l,
  { apply alg_hom.coe_ring_hom_injective,
    apply ideal.quotient.ring_hom_ext,
    ext,
    simp only [alg_hom.comp_apply, ring_hom.comp_apply, alg_hom.coe_to_ring_hom,
      ideal.quotient.liftₐ_apply, ring_hom.to_fun_eq_coe, ideal.quotient.lift_mk,
      formally_smooth.mk_lift, ideal.quotient.mkₐ_eq_mk] },
  exact ⟨l.comp g, by rw [← alg_hom.comp_assoc, ← this, alg_hom.comp_assoc, hg, alg_hom.comp_id]⟩
end

include hf

/-- Given a surjective `f : P →ₐ[R] A` to a formally smooth `R`-algebra, this is the section
of the surjection `P ⧸ (ker f)² →ₐ[R] A`. -/
noncomputable
def formally_smooth.section_of_surjective (h : f.to_ring_hom.ker ^ 2 = ⊥) [formally_smooth R A] :
  A →ₐ[R] P :=
begin
  refine formally_smooth.lift _ ⟨2, h⟩
    (ideal.quotient_ker_alg_equiv_of_surjective hf).symm.to_alg_hom,
  { intros a ha, exact (submodule.quotient.mk_eq_zero _).mpr (ideal.pow_le_self two_ne_zero ha) },
  { refine @function.surjective.of_comp _ _ _ _ (ideal.quotient.mkₐ R _) _,
    exact ideal.quotient.mk_surjective },
  { use 2,
    rw [ideal.zero_eq_bot, eq_bot_iff],
    rintros x hx,
    let I := _, change x ∈ I ^ 2 at hx,
    replace hx : x ∈ I * I := by rwa ← pow_two I,
    apply submodule.smul_induction_on hx; clear hx x,
    { intros r₁ hr₁ r₂ hr₂,
      obtain ⟨r₁, rfl⟩ := ideal.quotient.mk_surjective r₁,
      obtain ⟨r₂, rfl⟩ := ideal.quotient.mk_surjective r₂,
      rw [smul_eq_mul, ← map_mul, pow_two],
      apply (submodule.quotient.mk_eq_zero _).mpr,
      exact ideal.mul_mem_mul ((submodule.quotient.mk_eq_zero _).mp hr₁)
        ((submodule.quotient.mk_eq_zero _).mp hr₂) },
    { intros x y hx hy, exact add_mem hx hy } }
end

lemma formally_smooth.section_of_surjective_comp_liftₐ [formally_smooth R A] :
  P⧸J^2→A .comp (formally_smooth.section_of_surjective f hf) = alg_hom.id R A :=
begin
  ext x,
  apply (ideal.quotient_ker_alg_equiv_of_surjective hf).symm.injective,
  change (ideal.quotient_ker_alg_equiv_of_surjective hf).symm.to_alg_hom _ =
    (ideal.quotient_ker_alg_equiv_of_surjective hf).symm.to_alg_hom x,
  rw [← alg_hom.comp_apply, ← alg_hom.comp_assoc],
  congr' 1,
  rw ← formally_smooth.comp_lift_of_surjective
    (ideal.quotient_ker_alg_equiv_of_surjective hf).symm.to_alg_hom _ _ _,
  congr' 1,
  rw formally_smooth.comp_lift_of_surjective,
  ext y,
  obtain ⟨y, rfl⟩ := ideal.quotient.mk_surjective y,
  apply (ideal.quotient_ker_alg_equiv_of_surjective hf).injective,
  rw [alg_hom.comp_apply, alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom,
    alg_equiv.apply_symm_apply, ideal.quotient_ker_alg_equiv_of_surjective,
    ideal.quotient_ker_alg_equiv_of_right_inverse.apply, ideal.quotient.liftₐ_apply,
    ideal.quotient.liftₐ_apply, ideal.quotient.lift_mk, ideal.quotient.lift_mk],
  exact (ideal.ker_lift_alg_mk _ _).symm
end

/-- Let `P →ₐ[R] A` be a surjection with `P` a formally smooth `R`-algebra and kernel `J`,
then `A` is formally smooth over `R` iff the surjection `P ⧸ J ^ 2 →ₐ[R] A` has a section. -/
lemma formally_smooth.iff_split_surjection [formally_smooth R P] :
  formally_smooth R A ↔ ∃ g, P⧸J^2→A .comp g = alg_hom.id R A :=
begin
  split,
  { introI,
    have : function.surjective P⧸J^2→A :=
      λ x, ⟨submodule.quotient.mk (hf x).some, (hf x).some_spec⟩,
    refine ⟨formally_smooth.lift _ ⟨2, _⟩
      (ideal.quotient_ker_alg_equiv_of_surjective this).symm.to_alg_hom, _⟩,
    { refine (pow_two _).trans _,
      rw [ideal.zero_eq_bot, ← smul_eq_mul, eq_bot_iff],
      rintros x hx,
      apply submodule.smul_induction_on hx,
      { intros a ha b hb,
        obtain ⟨a, rfl⟩ := submodule.mkq_surjective _ a,
        obtain ⟨b, rfl⟩ := submodule.mkq_surjective _ b,
        sorry

      }  },
  -- { intros a ha, exact (submodule.quotient.mk_eq_zero _).mpr (ideal.pow_le_self two_ne_zero ha),
  --   exact ⟨_, formally_smooth.section_of_surjective_comp_liftₐ f hf⟩ },
  },
  { rintro ⟨g, hg⟩, exact formally_smooth.of_split f g hg }
end

end of_surjective

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

end algebra
