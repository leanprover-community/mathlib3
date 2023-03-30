/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro, Anne Baanen
-/
import algebra.ring.fin
import algebra.ring.prod
import linear_algebra.quotient
import ring_theory.congruence
import ring_theory.ideal.basic
import tactic.fin_cases
/-!
# Ideal quotients

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines ideal quotients as a special case of submodule quotients and proves some basic
results about these quotients.

See `algebra.ring_quot` for quotients of non-commutative rings.

## Main definitions

 - `ideal.quotient`: the quotient of a commutative ring `R` by an ideal `I : ideal R`

## Main results

 - `ideal.quotient_inf_ring_equiv_pi_quotient`: the **Chinese Remainder Theorem**
-/

universes u v w

namespace ideal

open set
open_locale big_operators

variables {R : Type u} [comm_ring R] (I : ideal R) {a b : R}
variables {S : Type v}

/-- The quotient `R/I` of a ring `R` by an ideal `I`.

The ideal quotient of `I` is defined to equal the quotient of `I` as an `R`-submodule of `R`.
This definition is marked `reducible` so that typeclass instances can be shared between
`ideal.quotient I` and `submodule.quotient I`.
-/
-- Note that at present `ideal` means a left-ideal,
-- so this quotient is only useful in a commutative ring.
-- We should develop quotients by two-sided ideals as well.
@[reducible]
instance : has_quotient R (ideal R) := submodule.has_quotient

namespace quotient
variables {I} {x y : R}

instance has_one (I : ideal R) : has_one (R ⧸ I) := ⟨submodule.quotient.mk 1⟩

/-- On `ideal`s, `submodule.quotient_rel` is a ring congruence. -/
protected def ring_con (I : ideal R) : ring_con R :=
{ mul' := λ a₁ b₁ a₂ b₂ h₁ h₂, begin
    rw submodule.quotient_rel_r_def at h₁ h₂ ⊢,
    have F := I.add_mem (I.mul_mem_left a₂ h₁) (I.mul_mem_right b₁ h₂),
    have : a₁ * a₂ - b₁ * b₂ = a₂ * (a₁ - b₁) + (a₂ - b₂) * b₁,
    { rw [mul_sub, sub_mul, sub_add_sub_cancel, mul_comm, mul_comm b₁] },
    rw ← this at F,
    change _ ∈ _, convert F,
  end,
  .. quotient_add_group.con I.to_add_subgroup }

instance comm_ring (I : ideal R) : comm_ring (R ⧸ I) :=
{ ..submodule.quotient.add_comm_group I,  -- to help with unification
  ..(quotient.ring_con I)^.quotient.comm_ring }

/-- The ring homomorphism from a ring `R` to a quotient ring `R/I`. -/
def mk (I : ideal R) : R →+* (R ⧸ I) :=
⟨λ a, submodule.quotient.mk a, rfl, λ _ _, rfl, rfl, λ _ _, rfl⟩

/- Two `ring_homs`s from the quotient by an ideal are equal if their
compositions with `ideal.quotient.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
lemma ring_hom_ext [non_assoc_semiring S] ⦃f g : R ⧸ I →+* S⦄
  (h : f.comp (mk I) = g.comp (mk I)) : f = g :=
ring_hom.ext $ λ x, quotient.induction_on' x $ (ring_hom.congr_fun h : _)

instance inhabited : inhabited (R ⧸ I) := ⟨mk I 37⟩

protected theorem eq : mk I x = mk I y ↔ x - y ∈ I := submodule.quotient.eq I

@[simp] theorem mk_eq_mk (x : R) : (submodule.quotient.mk x : R ⧸ I) = mk I x := rfl

lemma eq_zero_iff_mem {I : ideal R} : mk I a = 0 ↔ a ∈ I :=
submodule.quotient.mk_eq_zero _

theorem zero_eq_one_iff {I : ideal R} : (0 : R ⧸ I) = 1 ↔ I = ⊤ :=
eq_comm.trans $ eq_zero_iff_mem.trans (eq_top_iff_one _).symm

theorem zero_ne_one_iff {I : ideal R} : (0 : R ⧸ I) ≠ 1 ↔ I ≠ ⊤ :=
not_congr zero_eq_one_iff

protected theorem nontrivial {I : ideal R} (hI : I ≠ ⊤) : nontrivial (R ⧸ I) :=
⟨⟨0, 1, zero_ne_one_iff.2 hI⟩⟩

lemma subsingleton_iff {I : ideal R} : subsingleton (R ⧸ I) ↔ I = ⊤ :=
by rw [eq_top_iff_one, ← subsingleton_iff_zero_eq_one, eq_comm,
       ← I^.quotient.mk^.map_one, quotient.eq_zero_iff_mem]

instance : unique (R ⧸ (⊤ : ideal R)) :=
⟨⟨0⟩, by rintro ⟨x⟩; exact quotient.eq_zero_iff_mem.mpr submodule.mem_top⟩

lemma mk_surjective : function.surjective (mk I) :=
λ y, quotient.induction_on' y (λ x, exists.intro x rfl)

instance : ring_hom_surjective (mk I) := ⟨mk_surjective⟩

/-- If `I` is an ideal of a commutative ring `R`, if `q : R → R/I` is the quotient map, and if
`s ⊆ R` is a subset, then `q⁻¹(q(s)) = ⋃ᵢ(i + s)`, the union running over all `i ∈ I`. -/
lemma quotient_ring_saturate (I : ideal R) (s : set R) :
  mk I ⁻¹' (mk I '' s) = (⋃ x : I, (λ y, x.1 + y) '' s) :=
begin
  ext x,
  simp only [mem_preimage, mem_image, mem_Union, ideal.quotient.eq],
  exact ⟨λ ⟨a, a_in, h⟩, ⟨⟨_, I.neg_mem h⟩, a, a_in, by simp⟩,
         λ ⟨⟨i, hi⟩, a, ha, eq⟩,
           ⟨a, ha, by rw [← eq, sub_add_eq_sub_sub_swap, sub_self, zero_sub]; exact I.neg_mem hi⟩⟩
end

instance no_zero_divisors (I : ideal R) [hI : I.is_prime] : no_zero_divisors (R ⧸ I) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b,
    quotient.induction_on₂' a b $ λ a b hab,
      (hI.mem_or_mem (eq_zero_iff_mem.1 hab)).elim
        (or.inl ∘ eq_zero_iff_mem.2)
        (or.inr ∘ eq_zero_iff_mem.2) }

instance is_domain (I : ideal R) [hI : I.is_prime] : is_domain (R ⧸ I) :=
let _ := quotient.nontrivial hI.1 in by exactI no_zero_divisors.to_is_domain _

lemma is_domain_iff_prime (I : ideal R) : is_domain (R ⧸ I) ↔ I.is_prime :=
begin
  refine ⟨λ H, ⟨zero_ne_one_iff.1 _, λ x y h, _⟩, λ h, by { resetI, apply_instance }⟩,
  { haveI : nontrivial (R ⧸ I) := ⟨H.3⟩,
    exact zero_ne_one },
  { simp only [←eq_zero_iff_mem, (mk I).map_mul] at ⊢ h,
    haveI := @is_domain.to_no_zero_divisors (R ⧸ I) _ H,
    exact eq_zero_or_eq_zero_of_mul_eq_zero h }
end

lemma exists_inv {I : ideal R} [hI : I.is_maximal] :
  ∀ {a : (R ⧸ I)}, a ≠ 0 → ∃ b : (R ⧸ I), a * b = 1 :=
begin
  rintro ⟨a⟩ h,
  rcases hI.exists_inv (mt eq_zero_iff_mem.2 h) with ⟨b, c, hc, abc⟩,
  rw [mul_comm] at abc,
  refine ⟨mk _ b, quot.sound _⟩, --quot.sound hb
  rw ← eq_sub_iff_add_eq' at abc,
  rw [abc, ← neg_mem_iff, neg_sub] at hc,
  rw submodule.quotient_rel_r_def,
  convert hc,
end

open_locale classical

/-- quotient by maximal ideal is a field. def rather than instance, since users will have
computable inverses in some applications.
See note [reducible non-instances]. -/
@[reducible]
protected noncomputable def field (I : ideal R) [hI : I.is_maximal] : field (R ⧸ I) :=
{ inv := λ a, if ha : a = 0 then 0 else classical.some (exists_inv ha),
  mul_inv_cancel := λ a (ha : a ≠ 0), show a * dite _ _ _ = _,
    by rw dif_neg ha;
    exact classical.some_spec (exists_inv ha),
  inv_zero := dif_pos rfl,
  ..quotient.comm_ring I,
  ..quotient.is_domain I }

/-- If the quotient by an ideal is a field, then the ideal is maximal. -/
theorem maximal_of_is_field (I : ideal R)
  (hqf : is_field (R ⧸ I)) : I.is_maximal :=
begin
  apply ideal.is_maximal_iff.2,
  split,
  { intro h,
    rcases hqf.exists_pair_ne with ⟨⟨x⟩, ⟨y⟩, hxy⟩,
    exact hxy (ideal.quotient.eq.2 (mul_one (x - y) ▸ I.mul_mem_left _ h)) },
  { intros J x hIJ hxnI hxJ,
    rcases hqf.mul_inv_cancel (mt ideal.quotient.eq_zero_iff_mem.1 hxnI) with ⟨⟨y⟩, hy⟩,
    rw [← zero_add (1 : R), ← sub_self (x * y), sub_add],
    refine J.sub_mem (J.mul_mem_right _ hxJ) (hIJ (ideal.quotient.eq.1 hy)) }
end

/-- The quotient of a ring by an ideal is a field iff the ideal is maximal. -/
theorem maximal_ideal_iff_is_field_quotient (I : ideal R) : I.is_maximal ↔ is_field (R ⧸ I) :=
⟨λ h, by { letI := @quotient.field _ _ I h, exact field.to_is_field _ }, maximal_of_is_field _⟩

variable [comm_ring S]

/-- Given a ring homomorphism `f : R →+* S` sending all elements of an ideal to zero,
lift it to the quotient by this ideal. -/
def lift (I : ideal R) (f : R →+* S) (H : ∀ (a : R), a ∈ I → f a = 0) :
  R ⧸ I →+* S :=
{ map_one' := f.map_one,
  map_zero' := f.map_zero,
  map_add' := λ a₁ a₂, quotient.induction_on₂' a₁ a₂ f.map_add,
  map_mul' := λ a₁ a₂, quotient.induction_on₂' a₁ a₂ f.map_mul,
  .. quotient_add_group.lift I.to_add_subgroup f.to_add_monoid_hom H }

@[simp] lemma lift_mk (I : ideal R) (f : R →+* S) (H : ∀ (a : R), a ∈ I → f a = 0) :
  lift I f H (mk I a) = f a := rfl

lemma lift_surjective_of_surjective (I : ideal R) {f : R →+* S} (H : ∀ (a : R), a ∈ I → f a = 0)
  (hf : function.surjective f) : function.surjective (ideal.quotient.lift I f H) :=
begin
  intro y,
  obtain ⟨x, rfl⟩ := hf y,
  use ideal.quotient.mk I x,
  simp only [ideal.quotient.lift_mk],
end

/-- The ring homomorphism from the quotient by a smaller ideal to the quotient by a larger ideal.

This is the `ideal.quotient` version of `quot.factor` -/
def factor (S T : ideal R) (H : S ≤ T) : R ⧸ S →+* R ⧸ T :=
ideal.quotient.lift S (T^.quotient.mk) (λ x hx, eq_zero_iff_mem.2 (H hx))

@[simp] lemma factor_mk (S T : ideal R) (H : S ≤ T) (x : R) :
  factor S T H (mk S x) = mk T x := rfl

@[simp] lemma factor_comp_mk (S T : ideal R) (H : S ≤ T) : (factor S T H).comp (mk S) = mk T :=
by { ext x, rw [ring_hom.comp_apply, factor_mk] }

end quotient

/-- Quotienting by equal ideals gives equivalent rings.

See also `submodule.quot_equiv_of_eq` and `ideal.quotient_equiv_alg_of_eq`.
-/
def quot_equiv_of_eq {R : Type*} [comm_ring R] {I J : ideal R} (h : I = J) :
  (R ⧸ I) ≃+* R ⧸ J :=
{ map_mul' := by { rintro ⟨x⟩ ⟨y⟩, refl },
  .. submodule.quot_equiv_of_eq I J h }

@[simp]
lemma quot_equiv_of_eq_mk {R : Type*} [comm_ring R] {I J : ideal R} (h : I = J) (x : R) :
  quot_equiv_of_eq h (ideal.quotient.mk I x) = ideal.quotient.mk J x :=
rfl

@[simp]
lemma quot_equiv_of_eq_symm {R : Type*} [comm_ring R] {I J : ideal R} (h : I = J) :
  (ideal.quot_equiv_of_eq h).symm = ideal.quot_equiv_of_eq h.symm :=
by ext; refl

section pi
variables (ι : Type v)

/-- `R^n/I^n` is a `R/I`-module. -/
instance module_pi : module (R ⧸ I) ((ι → R) ⧸ I.pi ι) :=
{ smul := λ c m, quotient.lift_on₂' c m (λ r m, submodule.quotient.mk $ r • m) begin
    intros c₁ m₁ c₂ m₂ hc hm,
    apply ideal.quotient.eq.2,
    rw submodule.quotient_rel_r_def at hc hm,
    intro i,
    exact I.mul_sub_mul_mem hc (hm i),
  end,
  one_smul := begin
    rintro ⟨a⟩,
    convert_to ideal.quotient.mk _ _ = ideal.quotient.mk _ _,
    congr' with i, exact one_mul (a i),
  end,
  mul_smul := begin
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩,
    convert_to ideal.quotient.mk _ _ = ideal.quotient.mk _ _,
    simp only [(•)],
    congr' with i, exact mul_assoc a b (c i),
  end,
  smul_add := begin
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩,
    convert_to ideal.quotient.mk _ _ = ideal.quotient.mk _ _,
    congr' with i, exact mul_add a (b i) (c i),
  end,
  smul_zero := begin
    rintro ⟨a⟩,
    convert_to ideal.quotient.mk _ _ = ideal.quotient.mk _ _,
    congr' with i, exact mul_zero a,
  end,
  add_smul := begin
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩,
    convert_to ideal.quotient.mk _ _ = ideal.quotient.mk _ _,
    congr' with i, exact add_mul a b (c i),
  end,
  zero_smul := begin
    rintro ⟨a⟩,
    convert_to ideal.quotient.mk _ _ = ideal.quotient.mk _ _,
    congr' with i, exact zero_mul (a i),
  end, }

/-- `R^n/I^n` is isomorphic to `(R/I)^n` as an `R/I`-module. -/
noncomputable def pi_quot_equiv : ((ι → R) ⧸ I.pi ι) ≃ₗ[(R ⧸ I)] (ι → (R ⧸ I)) :=
{ to_fun := λ x, quotient.lift_on' x (λ f i, ideal.quotient.mk I (f i)) $
    λ a b hab, funext (λ i, (submodule.quotient.eq' _).2
      (quotient_add_group.left_rel_apply.mp hab i)),
  map_add' := by { rintros ⟨_⟩ ⟨_⟩, refl },
  map_smul' := by { rintros ⟨_⟩ ⟨_⟩, refl },
  inv_fun := λ x, ideal.quotient.mk (I.pi ι) $ λ i, quotient.out' (x i),
  left_inv :=
  begin
    rintro ⟨x⟩,
    exact ideal.quotient.eq.2 (λ i, ideal.quotient.eq.1 (quotient.out_eq' _))
  end,
  right_inv :=
  begin
    intro x,
    ext i,
    obtain ⟨r, hr⟩ := @quot.exists_rep _ _ (x i),
    simp_rw ←hr,
    convert quotient.out_eq' _
  end }

/-- If `f : R^n → R^m` is an `R`-linear map and `I ⊆ R` is an ideal, then the image of `I^n` is
    contained in `I^m`. -/
lemma map_pi {ι : Type*} [finite ι] {ι' : Type w} (x : ι → R) (hi : ∀ i, x i ∈ I)
  (f : (ι → R) →ₗ[R] (ι' → R)) (i : ι') : f x i ∈ I :=
begin
  classical,
  casesI nonempty_fintype ι,
  rw pi_eq_sum_univ x,
  simp only [finset.sum_apply, smul_eq_mul, linear_map.map_sum, pi.smul_apply, linear_map.map_smul],
  exact I.sum_mem (λ j hj, I.mul_mem_right _ (hi j))
end

end pi

section chinese_remainder
variables {ι : Type v}

theorem exists_sub_one_mem_and_mem (s : finset ι) {f : ι → ideal R}
  (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i ⊔ f j = ⊤) (i : ι) (his : i ∈ s) :
  ∃ r : R, r - 1 ∈ f i ∧ ∀ j ∈ s, j ≠ i → r ∈ f j :=
begin
  have : ∀ j ∈ s, j ≠ i → ∃ r : R, ∃ H : r - 1 ∈ f i, r ∈ f j,
  { intros j hjs hji, specialize hf i his j hjs hji.symm,
    rw [eq_top_iff_one, submodule.mem_sup] at hf,
    rcases hf with ⟨r, hri, s, hsj, hrs⟩, refine ⟨1 - r, _, _⟩,
    { rw [sub_right_comm, sub_self, zero_sub], exact (f i).neg_mem hri },
    { rw [← hrs, add_sub_cancel'], exact hsj } },
  classical,
  have : ∃ g : ι → R, (∀ j, g j - 1 ∈ f i) ∧ ∀ j ∈ s, j ≠ i → g j ∈ f j,
  { choose g hg1 hg2,
    refine ⟨λ j, if H : j ∈ s ∧ j ≠ i then g j H.1 H.2 else 1, λ j, _, λ j, _⟩,
    { split_ifs with h, { apply hg1 }, rw sub_self, exact (f i).zero_mem },
    { intros hjs hji, rw dif_pos, { apply hg2 }, exact ⟨hjs, hji⟩ } },
  rcases this with ⟨g, hgi, hgj⟩, use (∏ x in s.erase i, g x), split,
  { rw [← quotient.eq, ring_hom.map_one, ring_hom.map_prod],
    apply finset.prod_eq_one, intros, rw [← ring_hom.map_one, quotient.eq], apply hgi },
  intros j hjs hji, rw [← quotient.eq_zero_iff_mem, ring_hom.map_prod],
  refine finset.prod_eq_zero (finset.mem_erase_of_ne_of_mem hji hjs) _,
  rw quotient.eq_zero_iff_mem, exact hgj j hjs hji
end

theorem exists_sub_mem [finite ι] {f : ι → ideal R} (hf : ∀ i j, i ≠ j → f i ⊔ f j = ⊤)
  (g : ι → R) :
  ∃ r : R, ∀ i, r - g i ∈ f i :=
begin
  casesI nonempty_fintype ι,
  have : ∃ φ : ι → R, (∀ i, φ i - 1 ∈ f i) ∧ (∀ i j, i ≠ j → φ i ∈ f j),
  { have := exists_sub_one_mem_and_mem (finset.univ : finset ι) (λ i _ j _ hij, hf i j hij),
    choose φ hφ,
    existsi λ i, φ i (finset.mem_univ i),
    exact ⟨λ i, (hφ i _).1, λ i j hij, (hφ i _).2 j (finset.mem_univ j) hij.symm⟩ },
  rcases this with ⟨φ, hφ1, hφ2⟩,
  use ∑ i, g i * φ i,
  intros i,
  rw [← quotient.eq, ring_hom.map_sum],
  refine eq.trans (finset.sum_eq_single i _ _) _,
  { intros j _ hji, rw quotient.eq_zero_iff_mem, exact (f i).mul_mem_left _ (hφ2 j i hji) },
  { intros hi, exact (hi $ finset.mem_univ i).elim },
  specialize hφ1 i, rw [← quotient.eq, ring_hom.map_one] at hφ1,
  rw [ring_hom.map_mul, hφ1, mul_one]
end

/-- The homomorphism from `R/(⋂ i, f i)` to `∏ i, (R / f i)` featured in the Chinese
  Remainder Theorem. It is bijective if the ideals `f i` are comaximal. -/
def quotient_inf_to_pi_quotient (f : ι → ideal R) :
  R ⧸ (⨅ i, f i) →+* Π i, R ⧸ f i :=
quotient.lift (⨅ i, f i)
  (pi.ring_hom (λ i : ι, (quotient.mk (f i) : _))) $
  λ r hr, begin
    rw submodule.mem_infi at hr,
    ext i,
    exact quotient.eq_zero_iff_mem.2 (hr i)
  end

theorem quotient_inf_to_pi_quotient_bijective [finite ι] {f : ι → ideal R}
  (hf : ∀ i j, i ≠ j → f i ⊔ f j = ⊤) :
  function.bijective (quotient_inf_to_pi_quotient f) :=
⟨λ x y, quotient.induction_on₂' x y $ λ r s hrs, quotient.eq.2 $
  (submodule.mem_infi _).2 $ λ i, quotient.eq.1 $
  show quotient_inf_to_pi_quotient f (quotient.mk' r) i = _, by rw hrs; refl,
λ g, let ⟨r, hr⟩ := exists_sub_mem hf (λ i, quotient.out' (g i)) in
⟨quotient.mk _ r, funext $ λ i, quotient.out_eq' (g i) ▸ quotient.eq.2 (hr i)⟩⟩

/-- Chinese Remainder Theorem. Eisenbud Ex.2.6. Similar to Atiyah-Macdonald 1.10 and Stacks 00DT -/
noncomputable def quotient_inf_ring_equiv_pi_quotient [finite ι] (f : ι → ideal R)
  (hf : ∀ i j, i ≠ j → f i ⊔ f j = ⊤) :
  R ⧸ (⨅ i, f i) ≃+* Π i, R ⧸ f i :=
{ .. equiv.of_bijective _ (quotient_inf_to_pi_quotient_bijective hf),
  .. quotient_inf_to_pi_quotient f }

end chinese_remainder

/-- **Chinese remainder theorem**, specialized to two ideals. -/
noncomputable def quotient_inf_equiv_quotient_prod (I J : ideal R)
  (coprime : I ⊔ J = ⊤) :
  (R ⧸ (I ⊓ J)) ≃+* (R ⧸ I) × R ⧸ J :=
let f : fin 2 → ideal R := ![I, J] in
have hf : ∀ (i j : fin 2), i ≠ j → f i ⊔ f j = ⊤,
by { intros i j h,
  fin_cases i; fin_cases j; try { contradiction }; simpa [f, sup_comm] using coprime },
(ideal.quot_equiv_of_eq (by simp [infi, inf_comm])).trans $
(ideal.quotient_inf_ring_equiv_pi_quotient f hf).trans $
ring_equiv.pi_fin_two (λ i, R ⧸ f i)

@[simp] lemma quotient_inf_equiv_quotient_prod_fst (I J : ideal R) (coprime : I ⊔ J = ⊤)
  (x : R ⧸ (I ⊓ J)) : (quotient_inf_equiv_quotient_prod I J coprime x).fst =
  ideal.quotient.factor (I ⊓ J) I inf_le_left x :=
quot.induction_on x (λ x, rfl)

@[simp] lemma quotient_inf_equiv_quotient_prod_snd (I J : ideal R) (coprime : I ⊔ J = ⊤)
  (x : R ⧸ (I ⊓ J)) : (quotient_inf_equiv_quotient_prod I J coprime x).snd =
  ideal.quotient.factor (I ⊓ J) J inf_le_right x :=
quot.induction_on x (λ x, rfl)

@[simp] lemma fst_comp_quotient_inf_equiv_quotient_prod (I J : ideal R) (coprime : I ⊔ J = ⊤) :
  (ring_hom.fst _ _).comp
    (quotient_inf_equiv_quotient_prod I J coprime : R ⧸ I ⊓ J →+* (R ⧸ I) × R ⧸ J) =
  ideal.quotient.factor (I ⊓ J) I inf_le_left :=
by ext; refl

@[simp] lemma snd_comp_quotient_inf_equiv_quotient_prod (I J : ideal R) (coprime : I ⊔ J = ⊤) :
  (ring_hom.snd _ _).comp
    (quotient_inf_equiv_quotient_prod I J coprime : R ⧸ I ⊓ J →+* (R ⧸ I) × R ⧸ J) =
  ideal.quotient.factor (I ⊓ J) J inf_le_right :=
by ext; refl

end ideal
