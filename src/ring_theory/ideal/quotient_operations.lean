/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ring_theory.ideal.operations
import ring_theory.ideal.quotient
/-!
# More operations on modules and ideals related to quotients
-/

universes u v w

namespace ring_hom

variables {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] (f : R →+* S)

/-- The induced map from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotient_ker_equiv_of_right_inverse`) /
is surjective (`quotient_ker_equiv_of_surjective`).
-/
def ker_lift (f : R →+* S) : R ⧸ f.ker →+* S :=
ideal.quotient.lift _ f $ λ r, f.mem_ker.mp

@[simp]
lemma ker_lift_mk (f : R →+* S) (r : R) : ker_lift f (ideal.quotient.mk f.ker r) = f r :=
ideal.quotient.lift_mk _ _ _

/-- The induced map from the quotient by the kernel is injective. -/
lemma ker_lift_injective (f : R →+* S) : function.injective (ker_lift f) :=
assume a b, quotient.induction_on₂' a b $
  assume a b (h : f a = f b), ideal.quotient.eq.2 $
show a - b ∈ ker f, by rw [mem_ker, map_sub, h, sub_self]

lemma lift_injective_of_ker_le_ideal (I : ideal R) {f : R →+* S}
  (H : ∀ (a : R), a ∈ I → f a = 0) (hI : f.ker ≤ I) :
  function.injective (ideal.quotient.lift I f H) :=
begin
  rw [ring_hom.injective_iff_ker_eq_bot, ring_hom.ker_eq_bot_iff_eq_zero],
  intros u hu,
  obtain ⟨v, rfl⟩ := ideal.quotient.mk_surjective u,
  rw ideal.quotient.lift_mk at hu,
  rw [ideal.quotient.eq_zero_iff_mem],
  exact hI ((ring_hom.mem_ker f).mpr hu),
end

variable {f}

/-- The **first isomorphism theorem** for commutative rings, computable version. -/
def quotient_ker_equiv_of_right_inverse
  {g : S → R} (hf : function.right_inverse g f) :
  R ⧸ f.ker ≃+* S :=
{ to_fun := ker_lift f,
  inv_fun := (ideal.quotient.mk f.ker) ∘ g,
  left_inv := begin
    rintro ⟨x⟩,
    apply ker_lift_injective,
    simp [hf (f x)],
  end,
  right_inv := hf,
  ..ker_lift f}

@[simp]
lemma quotient_ker_equiv_of_right_inverse.apply {g : S → R} (hf : function.right_inverse g f)
  (x : R ⧸ f.ker) : quotient_ker_equiv_of_right_inverse hf x = ker_lift f x := rfl

@[simp]
lemma quotient_ker_equiv_of_right_inverse.symm.apply {g : S → R} (hf : function.right_inverse g f)
  (x : S) : (quotient_ker_equiv_of_right_inverse hf).symm x = ideal.quotient.mk f.ker (g x) := rfl

/-- The **first isomorphism theorem** for commutative rings. -/
noncomputable def quotient_ker_equiv_of_surjective (hf : function.surjective f) :
  R ⧸ f.ker ≃+* S :=
quotient_ker_equiv_of_right_inverse (classical.some_spec hf.has_right_inverse)

end ring_hom

namespace ideal

variables {R : Type u} {S : Type v} {F : Type w} [comm_ring R] [comm_ring S]

@[simp] lemma map_quotient_self (I : ideal R) :
  map (quotient.mk I) I = ⊥ :=
eq_bot_iff.2 $ ideal.map_le_iff_le_comap.2 $ λ x hx,
(submodule.mem_bot (R ⧸ I)).2 $ ideal.quotient.eq_zero_iff_mem.2 hx

@[simp] lemma mk_ker {I : ideal R} : (quotient.mk I).ker = I :=
by ext; rw [ring_hom.ker, mem_comap, submodule.mem_bot, quotient.eq_zero_iff_mem]

lemma map_mk_eq_bot_of_le {I J : ideal R} (h : I ≤ J) : I.map (J^.quotient.mk) = ⊥ :=
by { rw [map_eq_bot_iff_le_ker, mk_ker], exact h }

lemma ker_quotient_lift {S : Type v} [comm_ring S] {I : ideal R} (f : R →+* S) (H : I ≤ f.ker) :
  (ideal.quotient.lift I f H).ker = (f.ker).map I^.quotient.mk :=
begin
  ext x,
  split,
  { intro hx,
    obtain ⟨y, hy⟩ := quotient.mk_surjective x,
    rw [ring_hom.mem_ker, ← hy, ideal.quotient.lift_mk, ← ring_hom.mem_ker] at hx,
    rw [← hy, mem_map_iff_of_surjective I^.quotient.mk quotient.mk_surjective],
    exact ⟨y, hx, rfl⟩ },
  { intro hx,
    rw mem_map_iff_of_surjective I^.quotient.mk quotient.mk_surjective at hx,
    obtain ⟨y, hy⟩ := hx,
    rw [ring_hom.mem_ker, ← hy.right, ideal.quotient.lift_mk, ← (ring_hom.mem_ker f)],
    exact hy.left },
end

@[simp] lemma bot_quotient_is_maximal_iff (I : ideal R) :
  (⊥ : ideal (R ⧸ I)).is_maximal ↔ I.is_maximal :=
⟨λ hI, (@mk_ker _ _ I) ▸
  @comap_is_maximal_of_surjective _ _ _ _ _ _ (quotient.mk I) quotient.mk_surjective ⊥ hI,
 λ hI, by { resetI, letI := quotient.field I, exact bot_is_maximal }⟩

/-- See also `ideal.mem_quotient_iff_mem` in case `I ≤ J`. -/
@[simp]
lemma mem_quotient_iff_mem_sup {I J : ideal R} {x : R} :
  quotient.mk I x ∈ J.map (quotient.mk I) ↔ x ∈ J ⊔ I :=
by rw [← mem_comap, comap_map_of_surjective (quotient.mk I) quotient.mk_surjective,
       ← ring_hom.ker_eq_comap_bot, mk_ker]

/-- See also `ideal.mem_quotient_iff_mem_sup` if the assumption `I ≤ J` is not available. -/
lemma mem_quotient_iff_mem {I J : ideal R} (hIJ : I ≤ J) {x : R} :
  quotient.mk I x ∈ J.map (quotient.mk I) ↔ x ∈ J :=
by rw [mem_quotient_iff_mem_sup, sup_eq_left.mpr hIJ]

section quotient_algebra

variables (R₁ R₂ : Type*) {A B : Type*}
variables [comm_semiring R₁] [comm_semiring R₂] [comm_ring A] [comm_ring B]
variables [algebra R₁ A] [algebra R₂ A] [algebra R₁ B]

/-- The `R₁`-algebra structure on `A/I` for an `R₁`-algebra `A` -/
instance quotient.algebra {I : ideal A} : algebra R₁ (A ⧸ I) :=
{ to_fun := λ x, ideal.quotient.mk I (algebra_map R₁ A x),
  smul := (•),
  smul_def' := λ r x, quotient.induction_on' x $ λ x,
      ((quotient.mk I).congr_arg $ algebra.smul_def _ _).trans (ring_hom.map_mul _ _ _),
  commutes' := λ _ _, mul_comm _ _,
  .. ring_hom.comp (ideal.quotient.mk I) (algebra_map R₁ A) }

-- Lean can struggle to find this instance later if we don't provide this shortcut
instance quotient.is_scalar_tower [has_smul R₁ R₂] [is_scalar_tower R₁ R₂ A] (I : ideal A) :
  is_scalar_tower R₁ R₂ (A ⧸ I) :=
by apply_instance

/-- The canonical morphism `A →ₐ[R₁] A ⧸ I` as morphism of `R₁`-algebras, for `I` an ideal of
`A`, where `A` is an `R₁`-algebra. -/
def quotient.mkₐ (I : ideal A) : A →ₐ[R₁] A ⧸ I :=
⟨λ a, submodule.quotient.mk a, rfl, λ _ _, rfl, rfl, λ _ _, rfl, λ _, rfl⟩

lemma quotient.alg_hom_ext {I : ideal A} {S} [semiring S] [algebra R₁ S] ⦃f g : A ⧸ I →ₐ[R₁] S⦄
  (h : f.comp (quotient.mkₐ R₁ I) = g.comp (quotient.mkₐ R₁ I)) : f = g :=
alg_hom.ext $ λ x, quotient.induction_on' x $ alg_hom.congr_fun h

lemma quotient.alg_map_eq (I : ideal A) :
  algebra_map R₁ (A ⧸ I) = (algebra_map A (A ⧸ I)).comp (algebra_map R₁ A) :=
rfl

lemma quotient.mkₐ_to_ring_hom (I : ideal A) :
  (quotient.mkₐ R₁ I).to_ring_hom = ideal.quotient.mk I := rfl

@[simp] lemma quotient.mkₐ_eq_mk (I : ideal A) :
  ⇑(quotient.mkₐ R₁ I) = ideal.quotient.mk I := rfl

@[simp] lemma quotient.algebra_map_eq (I : ideal R) :
  algebra_map R (R ⧸ I) = I^.quotient.mk :=
rfl

@[simp] lemma quotient.mk_comp_algebra_map (I : ideal A) :
  (quotient.mk I).comp (algebra_map R₁ A) = algebra_map R₁ (A ⧸ I) :=
rfl

@[simp] lemma quotient.mk_algebra_map (I : ideal A) (x : R₁) :
  quotient.mk I (algebra_map R₁ A x) = algebra_map R₁ (A ⧸ I) x :=
rfl

/-- The canonical morphism `A →ₐ[R₁] I.quotient` is surjective. -/
lemma quotient.mkₐ_surjective (I : ideal A) : function.surjective (quotient.mkₐ R₁ I) :=
surjective_quot_mk _

/-- The kernel of `A →ₐ[R₁] I.quotient` is `I`. -/
@[simp]
lemma quotient.mkₐ_ker (I : ideal A) : (quotient.mkₐ R₁ I : A →+* A ⧸ I).ker = I :=
ideal.mk_ker

variables {R₁}

/-- `ideal.quotient.lift` as an `alg_hom`. -/
def quotient.liftₐ (I : ideal A) (f : A →ₐ[R₁] B) (hI : ∀ (a : A), a ∈ I → f a = 0) :
  A ⧸ I →ₐ[R₁] B :=
{ commutes' := λ r, begin
    -- this is is_scalar_tower.algebra_map_apply R₁ A (A ⧸ I) but the file `algebra.algebra.tower`
    -- imports this file.
    have : algebra_map R₁ (A ⧸ I) r = algebra_map A (A ⧸ I) (algebra_map R₁ A r),
    { simp_rw [algebra.algebra_map_eq_smul_one, smul_assoc, one_smul] },
    rw [this, ideal.quotient.algebra_map_eq,
      ring_hom.to_fun_eq_coe, ideal.quotient.lift_mk, alg_hom.coe_to_ring_hom,
      algebra.algebra_map_eq_smul_one, algebra.algebra_map_eq_smul_one, map_smul, map_one],
  end
  ..(ideal.quotient.lift I (f : A →+* B) hI) }

@[simp]
lemma quotient.liftₐ_apply (I : ideal A) (f : A →ₐ[R₁] B) (hI : ∀ (a : A), a ∈ I → f a = 0) (x) :
  ideal.quotient.liftₐ I f hI x = ideal.quotient.lift I (f : A →+* B) hI x :=
rfl

lemma quotient.liftₐ_comp (I : ideal A) (f : A →ₐ[R₁] B) (hI : ∀ (a : A), a ∈ I → f a = 0) :
  (ideal.quotient.liftₐ I f hI).comp (ideal.quotient.mkₐ R₁ I) = f :=
alg_hom.ext (λ x, (ideal.quotient.lift_mk I (f : A →+* B) hI : _))


lemma ker_lift.map_smul (f : A →ₐ[R₁] B) (r : R₁) (x : A ⧸ f.to_ring_hom.ker) :
  f.to_ring_hom.ker_lift (r • x) = r • f.to_ring_hom.ker_lift x :=
begin
  obtain ⟨a, rfl⟩ := quotient.mkₐ_surjective R₁ _ x,
  rw [← alg_hom.map_smul, quotient.mkₐ_eq_mk, ring_hom.ker_lift_mk],
  exact f.map_smul _ _
end

/-- The induced algebras morphism from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotient_ker_alg_equiv_of_right_inverse`) /
is surjective (`quotient_ker_alg_equiv_of_surjective`).
-/
def ker_lift_alg (f : A →ₐ[R₁] B) : (A ⧸ f.to_ring_hom.ker) →ₐ[R₁] B :=
alg_hom.mk' f.to_ring_hom.ker_lift (λ _ _, ker_lift.map_smul f _ _)

@[simp]
lemma ker_lift_alg_mk (f : A →ₐ[R₁] B) (a : A) :
  ker_lift_alg f (quotient.mk f.to_ring_hom.ker a) = f a := rfl

@[simp]
lemma ker_lift_alg_to_ring_hom (f : A →ₐ[R₁] B) :
  (ker_lift_alg f).to_ring_hom = ring_hom.ker_lift f := rfl

/-- The induced algebra morphism from the quotient by the kernel is injective. -/
lemma ker_lift_alg_injective (f : A →ₐ[R₁] B) : function.injective (ker_lift_alg f) :=
ring_hom.ker_lift_injective f

/-- The **first isomorphism** theorem for algebras, computable version. -/
def quotient_ker_alg_equiv_of_right_inverse
  {f : A →ₐ[R₁] B} {g : B → A} (hf : function.right_inverse g f) :
  (A ⧸ f.to_ring_hom.ker) ≃ₐ[R₁] B :=
{ ..ring_hom.quotient_ker_equiv_of_right_inverse (λ x, show f.to_ring_hom (g x) = x, from hf x),
  ..ker_lift_alg f}

@[simp]
lemma quotient_ker_alg_equiv_of_right_inverse.apply {f : A →ₐ[R₁] B} {g : B → A}
  (hf : function.right_inverse g f) (x : A ⧸ f.to_ring_hom.ker) :
  quotient_ker_alg_equiv_of_right_inverse hf x = ker_lift_alg f x := rfl

@[simp]
lemma quotient_ker_alg_equiv_of_right_inverse_symm.apply {f : A →ₐ[R₁] B} {g : B → A}
  (hf : function.right_inverse g f) (x : B) :
  (quotient_ker_alg_equiv_of_right_inverse hf).symm x = quotient.mkₐ R₁ f.to_ring_hom.ker (g x) :=
  rfl

/-- The **first isomorphism theorem** for algebras. -/
noncomputable def quotient_ker_alg_equiv_of_surjective
  {f : A →ₐ[R₁] B} (hf : function.surjective f) : (A ⧸ f.to_ring_hom.ker) ≃ₐ[R₁] B :=
quotient_ker_alg_equiv_of_right_inverse (classical.some_spec hf.has_right_inverse)

/-- The ring hom `R/I →+* S/J` induced by a ring hom `f : R →+* S` with `I ≤ f⁻¹(J)` -/
def quotient_map {I : ideal R} (J : ideal S) (f : R →+* S) (hIJ : I ≤ J.comap f) :
  R ⧸ I →+* S ⧸ J :=
(quotient.lift I ((quotient.mk J).comp f) (λ _ ha,
  by simpa [function.comp_app, ring_hom.coe_comp, quotient.eq_zero_iff_mem] using hIJ ha))

@[simp]
lemma quotient_map_mk {J : ideal R} {I : ideal S} {f : R →+* S} {H : J ≤ I.comap f}
  {x : R} : quotient_map I f H (quotient.mk J x) = quotient.mk I (f x) :=
quotient.lift_mk J _ _

@[simp]
lemma quotient_map_algebra_map {J : ideal A} {I : ideal S} {f : A →+* S} {H : J ≤ I.comap f}
  {x : R₁} :
  quotient_map I f H (algebra_map R₁ (A ⧸ J) x) = quotient.mk I (f (algebra_map _ _ x)) :=
quotient.lift_mk J _ _

lemma quotient_map_comp_mk {J : ideal R} {I : ideal S} {f : R →+* S} (H : J ≤ I.comap f) :
  (quotient_map I f H).comp (quotient.mk J) = (quotient.mk I).comp f :=
ring_hom.ext (λ x, by simp only [function.comp_app, ring_hom.coe_comp, ideal.quotient_map_mk])

/-- The ring equiv `R/I ≃+* S/J` induced by a ring equiv `f : R ≃+** S`,  where `J = f(I)`. -/
@[simps]
def quotient_equiv (I : ideal R) (J : ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S)) :
  R ⧸ I ≃+* S ⧸ J :=
{ inv_fun := quotient_map I ↑f.symm (by {rw hIJ, exact le_of_eq (map_comap_of_equiv I f)}),
  left_inv := by {rintro ⟨r⟩, simp },
  right_inv := by {rintro ⟨s⟩, simp },
  ..quotient_map J ↑f (by {rw hIJ, exact @le_comap_map _ S _ _ _ _ _ _}) }

@[simp]
lemma quotient_equiv_mk (I : ideal R) (J : ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S))
  (x : R) : quotient_equiv I J f hIJ (ideal.quotient.mk I x) = ideal.quotient.mk J (f x) := rfl

@[simp]
lemma quotient_equiv_symm_mk (I : ideal R) (J : ideal S) (f : R ≃+* S)
  (hIJ : J = I.map (f : R →+* S)) (x : S) :
  (quotient_equiv I J f hIJ).symm (ideal.quotient.mk J x) = ideal.quotient.mk I (f.symm x) := rfl

/-- `H` and `h` are kept as separate hypothesis since H is used in constructing the quotient map. -/
lemma quotient_map_injective' {J : ideal R} {I : ideal S} {f : R →+* S} {H : J ≤ I.comap f}
  (h : I.comap f ≤ J) : function.injective (quotient_map I f H) :=
begin
  refine (injective_iff_map_eq_zero (quotient_map I f H)).2 (λ a ha, _),
  obtain ⟨r, rfl⟩ := quotient.mk_surjective a,
  rw [quotient_map_mk, quotient.eq_zero_iff_mem] at ha,
  exact (quotient.eq_zero_iff_mem).mpr (h ha),
end

/-- If we take `J = I.comap f` then `quotient_map` is injective automatically. -/
lemma quotient_map_injective {I : ideal S} {f : R →+* S} :
  function.injective (quotient_map I f le_rfl) :=
quotient_map_injective' le_rfl

lemma quotient_map_surjective {J : ideal R} {I : ideal S} {f : R →+* S} {H : J ≤ I.comap f}
  (hf : function.surjective f) : function.surjective (quotient_map I f H) :=
λ x, let ⟨x, hx⟩ := quotient.mk_surjective x in
  let ⟨y, hy⟩ := hf x in ⟨(quotient.mk J) y, by simp [hx, hy]⟩

/-- Commutativity of a square is preserved when taking quotients by an ideal. -/
lemma comp_quotient_map_eq_of_comp_eq {R' S' : Type*} [comm_ring R'] [comm_ring S']
  {f : R →+* S} {f' : R' →+* S'} {g : R →+* R'} {g' : S →+* S'} (hfg : f'.comp g = g'.comp f)
  (I : ideal S') : (quotient_map I g' le_rfl).comp (quotient_map (I.comap g') f le_rfl) =
    (quotient_map I f' le_rfl).comp (quotient_map (I.comap f') g
      (le_of_eq (trans (comap_comap f g') (hfg ▸ (comap_comap g f'))))) :=
begin
  refine ring_hom.ext (λ a, _),
  obtain ⟨r, rfl⟩ := quotient.mk_surjective a,
  simp only [ring_hom.comp_apply, quotient_map_mk],
  exact congr_arg (quotient.mk I) (trans (g'.comp_apply f r).symm (hfg ▸ (f'.comp_apply g r))),
end

/-- The algebra hom `A/I →+* B/J` induced by an algebra hom `f : A →ₐ[R₁] B` with `I ≤ f⁻¹(J)`. -/
def quotient_mapₐ {I : ideal A} (J : ideal B) (f : A →ₐ[R₁] B) (hIJ : I ≤ J.comap f) :
  A ⧸ I →ₐ[R₁] B ⧸ J :=
{ commutes' := λ r, by simp,
  ..quotient_map J (f : A →+* B) hIJ }

@[simp]
lemma quotient_map_mkₐ {I : ideal A} (J : ideal B) (f : A →ₐ[R₁] B) (H : I ≤ J.comap f)
  {x : A} : quotient_mapₐ J f H (quotient.mk I x) = quotient.mkₐ R₁ J (f x) := rfl

lemma quotient_map_comp_mkₐ {I : ideal A} (J : ideal B) (f : A →ₐ[R₁] B) (H : I ≤ J.comap f) :
  (quotient_mapₐ J f H).comp (quotient.mkₐ R₁ I) = (quotient.mkₐ R₁ J).comp f :=
alg_hom.ext (λ x, by simp only [quotient_map_mkₐ, quotient.mkₐ_eq_mk, alg_hom.comp_apply])

/-- The algebra equiv `A/I ≃ₐ[R] B/J` induced by an algebra equiv `f : A ≃ₐ[R] B`,
where`J = f(I)`. -/
def quotient_equiv_alg (I : ideal A) (J : ideal B) (f : A ≃ₐ[R₁] B)
  (hIJ : J = I.map (f : A →+* B)) :
  (A ⧸ I) ≃ₐ[R₁] B ⧸ J :=
{ commutes' := λ r, by simp,
  ..quotient_equiv I J (f : A ≃+* B) hIJ }

@[priority 100]
instance quotient_algebra {I : ideal A} [algebra R A] :
  algebra (R ⧸ I.comap (algebra_map R A)) (A ⧸ I) :=
(quotient_map I (algebra_map R A) (le_of_eq rfl)).to_algebra

lemma algebra_map_quotient_injective {I : ideal A} [algebra R A]:
  function.injective (algebra_map (R ⧸ I.comap (algebra_map R A)) (A ⧸ I)) :=
begin
  rintros ⟨a⟩ ⟨b⟩ hab,
  replace hab := quotient.eq.mp hab,
  rw ← ring_hom.map_sub at hab,
  exact quotient.eq.mpr hab
end

variable (R₁)

/-- Quotienting by equal ideals gives equivalent algebras. -/
def quotient_equiv_alg_of_eq {I J : ideal A} (h : I = J) : (A ⧸ I) ≃ₐ[R₁] A ⧸ J :=
quotient_equiv_alg I J alg_equiv.refl $ h ▸ (map_id I).symm

@[simp] lemma quotient_equiv_alg_of_eq_mk {I J : ideal A} (h : I = J) (x : A) :
  quotient_equiv_alg_of_eq R₁ h (ideal.quotient.mk I x) = ideal.quotient.mk J x :=
rfl

@[simp] lemma quotient_equiv_alg_of_eq_symm {I J : ideal A} (h : I = J) :
  (quotient_equiv_alg_of_eq R₁ h).symm = quotient_equiv_alg_of_eq R₁ h.symm :=
by ext; refl

end quotient_algebra

end ideal

namespace double_quot
open ideal
variable {R : Type u}

section

variables [comm_ring R] (I J : ideal R)

/-- The obvious ring hom `R/I → R/(I ⊔ J)` -/
def quot_left_to_quot_sup : R ⧸ I →+* R ⧸ (I ⊔ J) :=
ideal.quotient.factor I (I ⊔ J) le_sup_left

/-- The kernel of `quot_left_to_quot_sup` -/
lemma ker_quot_left_to_quot_sup :
  (quot_left_to_quot_sup I J).ker = J.map (ideal.quotient.mk I) :=
by simp only [mk_ker, sup_idem, sup_comm, quot_left_to_quot_sup, quotient.factor, ker_quotient_lift,
    map_eq_iff_sup_ker_eq_of_surjective I^.quotient.mk quotient.mk_surjective, ← sup_assoc]

/-- The ring homomorphism `(R/I)/J' -> R/(I ⊔ J)` induced by `quot_left_to_quot_sup` where `J'`
  is the image of `J` in `R/I`-/
def quot_quot_to_quot_sup : (R ⧸ I) ⧸ J.map (ideal.quotient.mk I) →+* R ⧸ I ⊔ J :=
by exact ideal.quotient.lift (J.map (ideal.quotient.mk I)) (quot_left_to_quot_sup I J)
  (ker_quot_left_to_quot_sup I J).symm.le

/-- The composite of the maps `R → (R/I)` and `(R/I) → (R/I)/J'` -/
def quot_quot_mk : R →+* ((R ⧸ I) ⧸ J.map I^.quotient.mk) :=
by exact ((J.map I^.quotient.mk)^.quotient.mk).comp I^.quotient.mk

/-- The kernel of `quot_quot_mk` -/
lemma ker_quot_quot_mk : (quot_quot_mk I J).ker = I ⊔ J :=
by rw [ring_hom.ker_eq_comap_bot, quot_quot_mk, ← comap_comap, ← ring_hom.ker, mk_ker,
  comap_map_of_surjective (ideal.quotient.mk I) (quotient.mk_surjective), ← ring_hom.ker, mk_ker,
  sup_comm]

/-- The ring homomorphism `R/(I ⊔ J) → (R/I)/J' `induced by `quot_quot_mk` -/
def lift_sup_quot_quot_mk (I J : ideal R) :
  R ⧸ (I ⊔ J) →+* (R ⧸ I) ⧸ J.map (ideal.quotient.mk I) :=
ideal.quotient.lift (I ⊔ J) (quot_quot_mk I J) (ker_quot_quot_mk I J).symm.le

/-- `quot_quot_to_quot_add` and `lift_sup_double_qot_mk` are inverse isomorphisms. In the case where
    `I ≤ J`, this is the Third Isomorphism Theorem (see `quot_quot_equiv_quot_of_le`)-/
def quot_quot_equiv_quot_sup : (R ⧸ I) ⧸ J.map (ideal.quotient.mk I) ≃+* R ⧸ I ⊔ J :=
ring_equiv.of_hom_inv (quot_quot_to_quot_sup I J) (lift_sup_quot_quot_mk I J)
  (by { ext z, refl }) (by { ext z, refl })

@[simp]
lemma quot_quot_equiv_quot_sup_quot_quot_mk (x : R) :
  quot_quot_equiv_quot_sup I J (quot_quot_mk I J x) = ideal.quotient.mk (I ⊔ J) x :=
rfl

@[simp]
lemma quot_quot_equiv_quot_sup_symm_quot_quot_mk (x : R) :
  (quot_quot_equiv_quot_sup I J).symm (ideal.quotient.mk (I ⊔ J) x) = quot_quot_mk I J x :=
rfl

/-- The obvious isomorphism `(R/I)/J' → (R/J)/I' `   -/
def quot_quot_equiv_comm :
  (R ⧸ I) ⧸ J.map I^.quotient.mk ≃+* (R ⧸ J) ⧸ I.map J^.quotient.mk :=
((quot_quot_equiv_quot_sup I J).trans (quot_equiv_of_eq sup_comm)).trans
  (quot_quot_equiv_quot_sup J I).symm

@[simp]
lemma quot_quot_equiv_comm_quot_quot_mk (x : R) :
  quot_quot_equiv_comm I J (quot_quot_mk I J x) = quot_quot_mk J I x :=
rfl

@[simp]
lemma quot_quot_equiv_comm_comp_quot_quot_mk :
  ring_hom.comp ↑(quot_quot_equiv_comm I J) (quot_quot_mk I J) = quot_quot_mk J I :=
ring_hom.ext $ quot_quot_equiv_comm_quot_quot_mk I J

@[simp]
lemma quot_quot_equiv_comm_symm :
  (quot_quot_equiv_comm I J).symm = quot_quot_equiv_comm J I :=
rfl

variables {I J}

/-- **The Third Isomorphism theorem** for rings. See `quot_quot_equiv_quot_sup` for a version
    that does not assume an inclusion of ideals. -/
def quot_quot_equiv_quot_of_le (h : I ≤ J) : (R ⧸ I) ⧸ (J.map I^.quotient.mk) ≃+* R ⧸ J :=
    (quot_quot_equiv_quot_sup I J).trans (ideal.quot_equiv_of_eq $ sup_eq_right.mpr h)

@[simp]
lemma quot_quot_equiv_quot_of_le_quot_quot_mk (x : R) (h : I ≤ J) :
  quot_quot_equiv_quot_of_le h (quot_quot_mk I J x) = J^.quotient.mk x := rfl

@[simp]
lemma quot_quot_equiv_quot_of_le_symm_mk (x : R) (h : I ≤ J) :
  (quot_quot_equiv_quot_of_le h).symm (J^.quotient.mk x) = (quot_quot_mk I J x) := rfl

lemma quot_quot_equiv_quot_of_le_comp_quot_quot_mk (h : I ≤ J) :
  ring_hom.comp ↑(quot_quot_equiv_quot_of_le h) (quot_quot_mk I J) = J^.quotient.mk :=
by ext ; refl

lemma quot_quot_equiv_quot_of_le_symm_comp_mk (h : I ≤ J) :
  ring_hom.comp ↑(quot_quot_equiv_quot_of_le h).symm J^.quotient.mk = quot_quot_mk I J :=
by ext ; refl

end

section algebra

@[simp]
lemma quot_quot_equiv_comm_mk_mk [comm_ring R] (I J : ideal R) (x : R) :
  quot_quot_equiv_comm I J (ideal.quotient.mk _ (ideal.quotient.mk _ x)) =
    algebra_map R _ x := rfl

variables [comm_semiring R] {A : Type v} [comm_ring A] [algebra R A] (I J : ideal A)

@[simp]
lemma quot_quot_equiv_quot_sup_quot_quot_algebra_map (x : R) :
  double_quot.quot_quot_equiv_quot_sup I J (algebra_map R _ x) = algebra_map _ _ x :=
rfl

@[simp]
lemma quot_quot_equiv_comm_algebra_map (x : R) :
  quot_quot_equiv_comm I J (algebra_map R _ x) = algebra_map _ _ x := rfl

end algebra

end double_quot
