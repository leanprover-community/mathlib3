import number_theory.number_field.canonical_embedding

open_locale classical

namespace number_field.unit

open number_field

variables (K : Type*) [field K]

localized "notation (name := ring_of_integers)
  `𝓞` := number_field.ring_of_integers" in units

@[simp]
lemma coe_pow (x : (𝓞 K)ˣ) (n : ℕ) : ((x ^ n: (𝓞 K)ˣ) : Kˣ) = (x : Kˣ) ^ n :=
by simp only [coe_coe, units.coe_pow, subsemiring_class.coe_pow]

@[simp]
lemma coe_inv (x : (𝓞 K)ˣ) : ((x⁻¹ : (𝓞 K)ˣ) : Kˣ) = (x : Kˣ)⁻¹ :=
begin
  simp [coe_coe, units.coe_inv, *],
end

@[simp]
lemma eq_iff (x y : (𝓞 K)ˣ) : x = y ↔ (x : K) = (y : K) :=
by simp only [← units.eq_iff, coe_coe, set_like.coe_eq_coe]

lemma pow_eq_one_iff [number_field K] (x : (𝓞 K)ˣ) :
  (∃ (n : ℕ) (hn : 0 < n), x ^ n = 1) ↔ ∀ φ : K →+* ℂ, ‖φ x‖ = 1 :=
begin
  split,
  { rintros ⟨n, ⟨hn, h⟩⟩ φ,
    lift n to ℕ+ using hn,
    suffices : (x : K) ^ (n : ℕ) = 1,
    { exact norm_map_one_of_pow_eq_one φ.to_monoid_hom this, },
    rwa [eq_iff, coe_pow] at h, },
  { intro h,
    convert embeddings.pow_eq_one_of_norm_eq_one K ℂ x.1.2 h,
    suffices : ∀ n : ℕ, x ^ n = 1 ↔ x.val.val ^ n = 1, { simp_rw this, },
    intro n,
    simp only [coe_coe, units.coe_one, algebra_map.coe_one, units.val_eq_coe, eq_iff,
      units.coe_pow, subsemiring_class.coe_pow, subtype.val_eq_coe], },
end

def to_units_of : (𝓞 K)ˣ →* Kˣ := units.map (subalgebra.val (𝓞 K))

lemma injective.to_units_of : function.injective (to_units_of K):=
begin
  rw injective_iff_map_eq_one,
  rintros a ha,
  rw units.ext_iff at ha,
  rwa eq_iff,
end

lemma mem_range.to_units_of_iff (x : Kˣ) :
  x ∈ set.range (to_units_of K) ↔ is_integral ℤ (x : K) ∧ is_integral ℤ (x⁻¹ : K) :=
begin
  split,
  { rintros ⟨x, rfl⟩,
    split,
    { exact x.val.2, },
    { convert x.inv.2,
      exact (coe_inv K x).symm, }},
  { exact λ ⟨hx, hxi⟩, ⟨⟨⟨x.1, hx⟩, ⟨x.1⁻¹, hxi⟩,
      by { simpa only [units.val_eq_coe, units.mul_inv', mul_mem_class.mk_mul_mk], },
      by { simpa only [units.val_eq_coe, units.inv_mul', mul_mem_class.mk_mul_mk], }⟩,
      by { simpa only [units.ext_iff], }⟩, },
end

-- TODO add coercion to Kˣ

end number_field.unit

section log_embedding

open number_field fintype number_field.infinite_place finite_dimensional

variables (K : Type*) [field K]

noncomputable def log_embedding : Kˣ → (infinite_place K → ℝ) :=
λ x w, real.log (w x)

namespace number_field.log_embedding

variable {K}

lemma map_one : log_embedding K 1 = 0 :=
by simpa only [log_embedding, infinite_place.map_one, real.log_one, units.coe_one, coe_coe,
  algebra_map.coe_one]

lemma map_mul (x y : Kˣ) :
  log_embedding K (x * y) = log_embedding K x + log_embedding K y :=
by simpa only [log_embedding, infinite_place.map_mul, real.log_mul, units.coe_mul, ne.def,
  infinite_place.eq_zero, units.ne_zero, not_false_iff]

lemma map_inv (x : Kˣ) : log_embedding K x⁻¹ = - log_embedding K x :=
by simpa [log_embedding, infinite_place.map_inv, real.log_inv]

lemma eq_zero_iff (x : Kˣ) :
  log_embedding K x = 0 ↔ (∀ w : infinite_place K, w x = 1) :=
begin
  dsimp only [log_embedding],
  rw function.funext_iff,
  simp_rw pi.zero_apply,
  split,
  { exact λ h w, real.eq_one_of_pos_of_log_eq_zero ((w.pos_iff x).mpr (units.ne_zero x)) (h w), },
  { intros h w,
    simp [← coe_coe, h w, real.log_one], },
end

localized "notation (name := lattice) `Λ` := (log_embedding K) '' set.range (unit.to_units_of K)"
  in log_embedding

-- define a subgroup instead
lemma toto : add_comm_group Λ :=
{ add :=
  begin
    rintros ⟨a, ha⟩ ⟨b, hb⟩,
    let ux := Exists.some (Exists.some_spec ha).1,
    let uy := Exists.some (Exists.some_spec hb).1,
    refine ⟨a + b, _⟩,
    use ux * uy,
    sorry,
    sorry,
    sorry,
    dsimp *,
  end,

}
#exit


lemma units.eq_zero_iff [number_field K] (x : (𝓞 K)ˣ) :
  log_embedding K x = 0 ↔ ∃ (n : ℕ) (H : 0 < n), x ^ n = 1 :=
begin
  rw eq_zero_iff,
  rw group_of_units.coe_coe_eq_coe,
  rw ( _ : (∀ w : infinite_place K, w x = 1) ↔ (∀ φ : K →+* ℂ, ‖φ x‖ = 1)),

--   have : (∃ (n : ℕ) (hn : 0 < n), x^n = 1) ↔ (∀ φ : K →+* ℂ, ‖φ x‖ = 1),
--   { split,
--     { rintros ⟨n, ⟨hn, h⟩⟩ φ,
--       lift n to ℕ+ using hn,
--       convert norm_map_one_of_pow_eq_one φ.to_monoid_hom _,
--       use n,
--       simp_rw subtype.ext_iff_val at h,
--       simp_rw subtype.val_eq_coe at h,


-- --      simp [h, units.coe_pow, subtype.ext_iff_val, subtype.val_eq_coe, subgroup.coe_pow,
-- --        subgroup.coe_one, units.coe_eq_one],
--       sorry, },
--     { intro h,
--       convert embeddings.pow_eq_one_of_norm_eq_one K ℂ x.2.1 h,
--       simp only [← units.coe_pow, subtype.ext_iff_val, subtype.val_eq_coe, subgroup.coe_pow,
--         subgroup.coe_one, units.coe_eq_one], }},
--   rw this,
--   have : (∀ φ : K →+* ℂ, ‖φ x‖ = 1) ↔ (∀ w : infinite_place K, w x = 1),
--   { sorry, },
--   rw this,
--   dsimp only [log_embedding],
--   rw function.funext_iff,
--   simp_rw pi.zero_apply,
--   split,
--   { exact λ h w, real.eq_one_of_pos_of_log_eq_zero ((w.pos_iff x).mpr (units.ne_zero x)) (h w), },
--   { intros h w,
--     simp [← coe_coe, h w, real.log_one], },
end

lemma units.discrete : discrete_topology (Λ K) := by sorry

lemma units.free_module : module.free ℤ (Λ K) := by sorry

lemma units.rank_le [number_field K] : finrank ℤ (Λ K) ≤  card (infinite_place K) - 1 := by sorry

lemma units.le_rank [number_field K] : card (infinite_place K) - 1 ≤ finrank ℤ (Λ K)  := by sorry

lemma units.rank [number_field K] :
  finrank ℤ (Λ K) = card (infinite_place K) - 1 := le_antisymm (units.rank_le K) (units.le_rank K)

end number_field.log_embedding

end log_embedding
