import number_theory.number_field.embeddings
import group_theory.torsion
import number_theory.number_field.norm

open_locale classical

variables (K : Type*) [field K]

localized "notation `𝓤`K := (number_field.ring_of_integers K)ˣ" in units

localized "notation `𝓞`K := (number_field.ring_of_integers K)" in units

open number_field

namespace units

variable {K}

def to_field : (𝓤 K) →* K := monoid_hom.comp (coe_hom K) (map (algebra_map (𝓞 K) K))

lemma to_field_injective : function.injective (@to_field K _) :=
begin
  have t1 : function.injective (coe_hom K) := by ext,
  have t2 : function.injective (units.map (algebra_map (𝓞 K) K).to_monoid_hom) :=
  begin
    intros x y hxy,
    rw units.ext_iff,
    have t1 := congr_arg (coe : Kˣ → K) hxy,
    simp_rw [units.coe_map] at t1,
    exact (no_zero_smul_divisors.algebra_map_injective (𝓞 K) K) t1,
  end,
  rw [to_field,monoid_hom.coe_comp],
  exact function.injective.comp t1 t2,
end


lemma to_field_ext (x y : 𝓤 K) :
  x = y ↔ x.to_field = y.to_field :=
⟨λ h, congr_arg to_field  h, λ h, to_field_injective h⟩

lemma to_field_coe (x : 𝓤 K) :
  x.to_field = ((x : 𝓞 K) : K) := rfl

end units

namespace number_field

open units

-- TODO. That should be tautological
lemma is_unit_iff (x : 𝓞 K) (hx : x ≠ 0):
  is_unit x ↔ is_integral ℤ (x⁻¹ : K) :=
begin
  split,
  { rintros ⟨u, rfl⟩,
    convert ring_of_integers.is_integral_coe u.inv,
    simp_rw [units.inv_eq_coe_inv, ← to_field_coe, map_inv], },
  { intro h,
    rw is_unit_iff_exists_inv,
    use ⟨x⁻¹, h⟩,
    apply @subtype.coe_injective K (λ x, x ∈ 𝓞 K),
    simp only [mul_mem_class.coe_mul, subtype.coe_mk, algebra_map.coe_one],
    refine mul_inv_cancel _,
    exact (@subtype.coe_injective K (λ x, x ∈ 𝓞 K)).ne hx, },
end

-- TODO. Make that an iff and simplify the proof
lemma unit.norm [number_field K] (u : 𝓤 K) :
  abs (ring_of_integers.norm ℚ (u : 𝓞 K)) = 1 :=
begin
  have t1 := congr_arg (λ x, (ring_of_integers.norm ℚ) x) u.val_inv,
  have t2 := congr_arg rat.ring_of_integers_equiv t1,
  have t3 := congr_arg abs t2,
  simp_rw [map_mul, abs_mul, map_one, abs_one] at t3,
  have t4 := dvd.intro _ t3,
  have t5 :=  int.eq_one_of_dvd_one (abs_nonneg _) t4,
  rw ← abs_one at t5 ⊢,
  rw abs_eq_abs at t5 ⊢,
  cases t5,
  { left,
    have := congr_arg rat.ring_of_integers_equiv.symm t5,
    rw ring_equiv.symm_apply_apply _ _ at this,
    rwa map_one at this, },
  { right,
    have := congr_arg rat.ring_of_integers_equiv.symm t5,
    rw ring_equiv.symm_apply_apply _ _ at this,
    rwa ring_equiv.map_neg_one at this, }
end

section roots_of_unity

open number_field number_field.infinite_place

def roots_of_unity : subgroup 𝓤 K := comm_group.torsion (𝓤 K)

lemma mem_roots_of_unity [number_field K] (x : (𝓤 K)) :
  x ∈ roots_of_unity K ↔ ∀ w : infinite_place K, w x = 1 :=
begin
  rw ( eq_iff_eq x 1 : (∀ w : infinite_place K, w x = 1) ↔ ∀ (φ : K →+* ℂ), ‖φ (x : K)‖ = 1),
  rw [roots_of_unity, comm_group.mem_torsion, is_of_fin_order_iff_pow_eq_one],
  split,
  { rintros ⟨n, ⟨hn1, hn2⟩⟩ φ,
    lift n to ℕ+ using hn1,
    rw [to_field_ext, map_pow, to_field_coe, map_one] at hn2,
    exact norm_map_one_of_pow_eq_one φ.to_monoid_hom hn2, },
  { intro h,
    obtain ⟨n , ⟨hn, hx⟩⟩ := embeddings.pow_eq_one_of_norm_eq_one K ℂ x.1.2 h,
    exact ⟨n, ⟨hn, by { rwa [to_field_ext, map_pow], }⟩⟩, },
end

lemma finite_roots_of_unity [number_field K]: finite (roots_of_unity K) :=
begin
  suffices : ((coe : (𝓤 K) → K) '' { x : (𝓤 K) | x ∈ (roots_of_unity K )}).finite,
  { exact set.finite_coe_iff.mpr (set.finite.of_finite_image this (to_field_injective.inj_on _)), },
  refine (embeddings.finite_of_norm_le K ℂ 1).subset _,
  rintros a ⟨⟨u, _, _, _⟩, ⟨hu, rfl⟩⟩,
  split,
  { exact u.2, },
  { rw ← le_iff_le,
    convert λ w, le_of_eq (((mem_roots_of_unity K _).mp hu) w) using 1, },
end

lemma roots_of_unity_cyclic [number_field K]: is_cyclic (roots_of_unity K) :=
begin
  haveI := finite_roots_of_unity K,
  exact subgroup_units_cyclic _,
end

end roots_of_unity

end number_field
