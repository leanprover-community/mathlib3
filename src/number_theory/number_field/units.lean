import number_theory.number_field.embeddings
import group_theory.torsion

open_locale classical

variables (K : Type*) [field K]

localized "notation `𝓤`K := (number_field.ring_of_integers K)ˣ" in units

namespace number_field.unit

section to_field_unit

open number_field

def to_field_unit : (𝓤 K) →* Kˣ := units.map (algebra_map (ring_of_integers K) K)

lemma injective.to_field_unit : function.injective (to_field_unit K) :=
begin
  intros x y hxy,
  rw units.ext_iff,
  have t1 := congr_arg (coe : Kˣ → K) hxy,
  simp_rw [to_field_unit, units.coe_map] at t1,
  exact (no_zero_smul_divisors.algebra_map_injective (ring_of_integers K) K) t1,
end

lemma ext.to_field_unit (x y : (𝓤 K)) :
  x = y ↔ to_field_unit K x = to_field_unit K y :=
⟨λ h, congr_arg (to_field_unit K) h, λ h, (injective.to_field_unit K) h⟩

instance : has_coe (𝓤 K) Kˣ := ⟨to_field_unit K⟩

lemma coe_injective : function.injective (coe : (𝓤 K) → Kˣ) :=
injective.to_field_unit K

@[simp]
lemma coe_ext (x y : (𝓤 K)) : x = y ↔ (x : Kˣ) = (y : Kˣ) :=
ext.to_field_unit K _ _

@[simp]
lemma coe_inv (x : (𝓤 K)) : ((x⁻¹ : (𝓤 K)): Kˣ) = (x : Kˣ)⁻¹ :=
map_inv (to_field_unit K) _

@[simp]
lemma coe_pow (x : (𝓤 K)) (n : ℕ) : ((x ^ n : (𝓤 K)) : Kˣ) = (x : Kˣ) ^ n :=
map_pow (to_field_unit K) _ _

def unit_subgroup : subgroup Kˣ := monoid_hom.range (to_field_unit K)

lemma mem_unit_subgroup (x : Kˣ) :
  x ∈ unit_subgroup K ↔ is_integral ℤ (x : K) ∧ is_integral ℤ (x⁻¹ : K) :=
begin
  split,
  { rintros ⟨x, rfl⟩,
    exact ⟨x.val.2, by { convert x.inv.2, rw ← units.coe_inv, refl, }⟩ },
  { exact λ ⟨hx, hxi⟩, ⟨⟨⟨x.1, hx⟩, ⟨x.1⁻¹, hxi⟩,
      by { simpa only [units.val_eq_coe, units.mul_inv', mul_mem_class.mk_mul_mk], },
      by { simpa only [units.val_eq_coe, units.inv_mul', mul_mem_class.mk_mul_mk], }⟩,
      by { simpa only [units.ext_iff], }⟩, },
end

end to_field_unit

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
    rw [coe_ext, coe_pow, units.ext_iff, units.coe_pow] at hn2,
    exact norm_map_one_of_pow_eq_one φ.to_monoid_hom hn2, },
  { intro h,
    obtain ⟨n , ⟨hn, hx⟩⟩ := embeddings.pow_eq_one_of_norm_eq_one K ℂ x.1.2 h,
    exact ⟨n, ⟨hn, by { rwa [coe_ext, coe_pow, units.ext_iff, units.coe_pow], }⟩⟩},
end

lemma finite_roots_of_unity [number_field K]: finite (roots_of_unity K) :=
begin
  suffices : ((coe : (𝓤 K) → K) '' { x : (𝓤 K) | x ∈ (roots_of_unity K )}).finite,
  { refine set.finite_coe_iff.mpr (set.finite.of_finite_image this (set.inj_on_of_injective _ _)),
    rw ( rfl : coe = (coe : Kˣ → K) ∘ (coe : (𝓤 K) → Kˣ)),
    exact (function.injective.of_comp_iff units.ext _).mpr (unit.coe_injective K), },
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

end number_field.unit
