import ring_theory.dedekind_domain
import ring_theory.ideal.operations
import algebraic_number_theory.class_number.fractional_ideal
import algebraic_number_theory.class_number.unique_factorization_monoid

open ring
open ring.fractional_ideal

section comm_ring

variables {R : Type*} [comm_ring R]

lemma ideal.le_of_dvd {I J : ideal R} : I ∣ J → J ≤ I
| ⟨H, hH⟩ := le_trans (le_of_eq hH) ideal.mul_le_right

lemma ideal.associated_iff_eq {I J : ideal R} :
  associated I J ↔ I = J :=
begin
  split,
  { intro h,
    obtain ⟨I_dvd_J, J_dvd_I⟩ := dvd_dvd_of_associated h,
    exact le_antisymm (ideal.le_of_dvd J_dvd_I) (ideal.le_of_dvd I_dvd_J) },
  { intro h,
    rw h }
end

/-- Ideals modulo units are just the ideals.

Since the `associates.mk` direction is nicer to work with, we'll use that as `to_fun`.
-/
noncomputable def associates_ideal_equiv : ideal R ≃* associates (ideal R) :=
{ to_fun := λ I, associates.mk I,
  inv_fun := λ I, quot.out I,
  left_inv := λ I, ideal.associated_iff_eq.mp (associates.mk_eq_mk_iff_associated.mp
    (quot.out_eq (associates.mk I))),
  right_inv := λ I, quot.out_eq I,
  map_mul' := λ I J, associates.mk_mul_mk }

end comm_ring

section is_dedekind_domain

variables {R : Type*} [integral_domain R] [is_dedekind_domain R]

/-- For ideals in a dedekind domain, to contain is to divide. -/
lemma ideal.dvd_iff_le {I J : ideal R} :
(I ∣ J) ↔ J ≤ I :=
⟨ideal.le_of_dvd,
 λ h, begin
   by_cases hI : I = ⊥,
   { have hJ : J = ⊥,
     { rw hI at h,
       exact eq_bot_iff.mpr h },
     rw [hI, hJ] },
   set f := fraction_ring.of R,
   have hI' : (I : fractional_ideal f) ≠ 0 :=
     (fractional_ideal.coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors R))).mpr hI,
   have : (I : fractional_ideal f)⁻¹ * J ≤ 1 := le_trans
     (fractional_ideal.mul_left_mono _ (coe_ideal_le_coe_ideal.mpr h))
     (le_of_eq (inv_mul_cancel hI')),
   obtain ⟨H, hH⟩ := fractional_ideal.le_one_iff_exists_coe_ideal.mp this,
   use H,
   refine coe_to_fractional_ideal_injective (le_refl (non_zero_divisors R))
     (show (J : fractional_ideal f) = _, from _),
   rw [fractional_ideal.coe_ideal_mul, hH, ← mul_assoc, mul_inv_cancel hI', one_mul]
 end⟩


lemma ideal.mul_left_cancel' {H I J : ideal R} (hH : H ≠ 0) (hIJ : H * I = H * J) :
  I = J :=
coe_to_fractional_ideal_injective
  (le_refl (non_zero_divisors R))
  (show (I : fractional_ideal (fraction_ring.of R)) = J,
   from mul_left_cancel'
    ((coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors R))).mpr hH)
    (by simpa only [← fractional_ideal.coe_ideal_mul] using congr_arg coe hIJ))

instance : comm_cancel_monoid_with_zero (ideal R) :=
{ mul_left_cancel_of_ne_zero := λ H I J hH hIJ, ideal.mul_left_cancel' hH hIJ,
  mul_right_cancel_of_ne_zero := λ H I J hI hHJ,
    ideal.mul_left_cancel' hI (by rwa [mul_comm I H, mul_comm I J]),
.. ideal.comm_semiring }

lemma ideal.is_unit_iff {I : ideal R} :
  is_unit I ↔ I = ⊤ :=
by rw [is_unit_iff_dvd_one, ideal.one_eq_top, ideal.dvd_iff_le, eq_top_iff]

lemma ideal.dvd_not_unit_iff_lt {I J : ideal R} :
  dvd_not_unit I J ↔ J < I :=
⟨λ ⟨hI, H, hunit, hmul⟩, lt_of_le_of_ne (ideal.dvd_iff_le.mp ⟨H, hmul⟩)
  (mt (λ h, have H = 1, from mul_left_cancel' hI (by rw [← hmul, h, mul_one]),
            show is_unit H, from this.symm ▸ is_unit_one) hunit),
 λ h, dvd_not_unit_of_dvd_of_not_dvd (ideal.dvd_iff_le.mpr (le_of_lt h))
   (mt ideal.dvd_iff_le.mp (not_le_of_lt h))⟩

lemma ideal.dvd_not_unit_eq_gt : (dvd_not_unit : ideal R → ideal R → Prop) = (>) :=
by { ext, exact ideal.dvd_not_unit_iff_lt }

instance : wf_dvd_monoid (ideal R) :=
{ well_founded_dvd_not_unit :=
  have well_founded ((>) : ideal R → ideal R → Prop) :=
  is_noetherian_iff_well_founded.mp (is_dedekind_domain.to_is_noetherian_ring),
  by rwa ideal.dvd_not_unit_eq_gt }

instance ideal.unique_factorization_monoid :
  unique_factorization_monoid (ideal R) :=
{ irreducible_iff_prime := λ P,
    ⟨λ hirr, ⟨hirr.ne_zero, hirr.not_unit, λ I J, begin
      have : P.is_maximal,
      { use mt ideal.is_unit_iff.mpr hirr.not_unit,
        intros J hJ,
        obtain ⟨J_ne, H, hunit, P_eq⟩ := ideal.dvd_not_unit_iff_lt.mpr hJ,
        exact ideal.is_unit_iff.mp ((hirr.is_unit_or_is_unit P_eq).resolve_right hunit) },
      simp only [ideal.dvd_iff_le, has_le.le, preorder.le, partial_order.le],
      contrapose!,
      rintros ⟨⟨x, x_mem, x_not_mem⟩, ⟨y, y_mem, y_not_mem⟩⟩,
      exact ⟨x * y, ideal.mul_mem_mul x_mem y_mem, mt this.is_prime.mem_or_mem (not_or x_not_mem y_not_mem)⟩,
    end⟩,
     λ h, irreducible_of_prime h⟩,
  .. ideal.wf_dvd_monoid }

/-- In a Dedekind domain, each ideal has finitely many divisors. -/
noncomputable def ideal.finite_divisors (I : ideal R) (hI : I ≠ ⊥) : fintype {J // J ∣ I} :=
begin
  apply @fintype.of_equiv _ _ (unique_factorization_monoid.finite_divisors hI),
  refine equiv.symm (equiv.subtype_congr associates_ideal_equiv.to_equiv _),
  intro J,
  simp [associates_ideal_equiv, associates.mk_dvd_mk],
end

end is_dedekind_domain
