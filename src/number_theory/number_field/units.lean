import number_theory.number_field.canonical_embedding

open_locale classical

namespace number_field.unit

open number_field

variables (K : Type*) [field K]

localized "notation (name := ring_of_integers)
  `𝓞` := number_field.ring_of_integers" in units

def to_field_unit : (𝓞 K)ˣ →* Kˣ := units.map (algebra_map (𝓞 K) K)

lemma injective.to_field_unit : function.injective (to_field_unit K) :=
begin
  intros x y hxy,
  rw to_field_unit at hxy,
  have t1 := congr_arg (coe : Kˣ → K) hxy,
  simp_rw units.coe_map at t1,
  have t2 : function.injective (algebra_map (𝓞 K) K) :=
    no_zero_smul_divisors.algebra_map_injective (𝓞 K) K,
  have := t2 t1,
  rwa ← units.ext_iff at this,
end

lemma ext.to_field_unit (x y : (𝓞 K)ˣ) :
  x = y ↔ to_field_unit K x = to_field_unit K y :=
⟨λ h, congr_arg (to_field_unit K) h, λ h, (injective.to_field_unit K) h⟩

instance : has_coe (𝓞 K)ˣ Kˣ := ⟨to_field_unit K⟩

lemma coe_injective : function.injective (coe : (𝓞 K)ˣ → Kˣ) :=
injective.to_field_unit K

lemma coe_ext (x y : (𝓞 K)ˣ) : x = y ↔ (x : Kˣ) = (y : Kˣ) :=
ext.to_field_unit K _ _

lemma coe_inv (x : (𝓞 K)ˣ) : ((x⁻¹ : (𝓞 K)ˣ): Kˣ) = (x : Kˣ)⁻¹ :=
map_inv (to_field_unit K) _

lemma coe_zpow (x : (𝓞 K)ˣ) (n : ℤ) : ((x ^ n : (𝓞 K)ˣ) : Kˣ) = (x : Kˣ) ^ n :=
map_zpow (to_field_unit K) _ _

#exit

lemma coe_pow (x : (𝓞 K)ˣ) (n : ℕ) : ((x ^ n : (𝓞 K)ˣ) : Kˣ) = (x : Kˣ) ^ n := by sorry

lemma pow_eq_one_iff [number_field K] (x : (𝓞 K)ˣ) :
  (∃ (n : ℕ) (hn : 0 < n), x ^ n = 1) ↔ ∀ w : infinite_place K, w x = 1 :=
begin
  split,
  { rintros ⟨n, ⟨hn, h⟩⟩ w,
    lift n to ℕ+ using hn,
    suffices : (x : K) ^ (n : ℕ) = 1,
    { rw [← congr_fun (congr_arg coe_fn (infinite_place.mk_embedding w)) _, infinite_place.coe_mk,
        place_apply],
      exact norm_map_one_of_pow_eq_one (w.embedding).to_monoid_hom this, },
    rwa [ext, coe_pow] at h, },
  { intro h,
    have : ∀ φ : K →+* ℂ, ‖φ x‖ = 1,
    { intro φ,
      simp only [←h (infinite_place.mk φ), infinite_place.apply, complex.norm_eq_abs], },
    convert embeddings.pow_eq_one_of_norm_eq_one K ℂ x.1.2 this,
    suffices : ∀ n : ℕ, x ^ n = 1 ↔ x.val.val ^ n = 1, { simp_rw this, },
    intro n,
    simp only [coe_coe, units.coe_one, algebra_map.coe_one, units.val_eq_coe, eq_iff,
      units.coe_pow, subsemiring_class.coe_pow, subtype.val_eq_coe], },
end

lemma pow_eq_one_iff0 [number_field K] (x : (𝓞 K)ˣ) :
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



lemma mem_range.to_units_of_iff (x : Kˣ) :
  x ∈ set.range (coe : (𝓞 K)ˣ → Kˣ) ↔ is_integral ℤ (x : K) ∧ is_integral ℤ (x⁻¹ : K) :=
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

-- TODO add coercion to Kˣ?

end number_field.unit

section log_embedding

open number_field fintype number_field.infinite_place finite_dimensional

variables (K : Type*) [field K]

noncomputable def log_embedding : Kˣ → (infinite_place K → ℝ) :=
λ x w, real.log (w x)

namespace number_field.log_embedding

variable {K}

lemma map_one : log_embedding K 1 = 0 :=
by simpa only [log_embedding, map_one, real.log_one, units.coe_one, coe_coe, algebra_map.coe_one]

lemma map_mul (x y : Kˣ) :
  log_embedding K (x * y) = log_embedding K x + log_embedding K y :=
by simpa only [log_embedding, map_mul, real.log_mul, units.coe_mul, ne.def, map_eq_zero,
  units.ne_zero, not_false_iff]

lemma map_inv (x : Kˣ) : log_embedding K x⁻¹ = - log_embedding K x :=
by simpa [log_embedding, map_inv, real.log_inv]

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

lemma nnnorm_eq [number_field K] (x : Kˣ) :
  ‖log_embedding K x‖₊ = finset.univ.sup (λ w : infinite_place K, ‖real.log (w x)‖₊ ) :=
by simp only [pi.nnnorm_def, log_embedding]

example (x r : ℝ) : (‖x‖₊ : ℝ) = ‖x‖ := coe_nnnorm x

lemma le_of_le [number_field K] (x : Kˣ) (r : ℝ) :
  ‖log_embedding K x‖ ≤ r ↔ ∀ w : infinite_place K, real.exp (- r) ≤ w x ∧ w x ≤ real.exp r :=
begin
   obtain hr | hr := lt_or_le r 0,
  { split,
    { intro h, exfalso,
      exact (not_le.mpr (lt_of_le_of_lt h hr)) (norm_nonneg _), },
    { intro h, exfalso,
      obtain ⟨w⟩ := infinite_place.nonempty K,
      have := real.exp_le_exp.mp (le_trans (h w).1 (h w).2),
      linarith, }},
  { lift r to nnreal using hr,
    simp_rw [← coe_nnnorm, nnnorm_eq, nnreal.coe_le_coe, finset.sup_le_iff, finset.mem_univ,
      forall_true_left, ← nnreal.coe_le_coe, coe_nnnorm, real.norm_eq_abs, abs_le],
    split,
    { intros h w,
      specialize h w,
      rwa [← real.log_le_iff_le_exp, ← real.le_log_iff_exp_le],
      all_goals { exact (infinite_place.pos_iff w x).mpr (units.ne_zero x), }},
    { intros h w,
      specialize h w,
      rwa [real.log_le_iff_le_exp, real.le_log_iff_exp_le],
      all_goals { exact (infinite_place.pos_iff w x).mpr (units.ne_zero x), }}}
end

variable (K)
def unit_subgroup : subgroup Kˣ := monoid_hom.range (coe : (ring_of_integers K)ˣ → Kˣ)

def unit_lattice : add_subgroup (infinite_place K → ℝ) :=
{ carrier := (log_embedding K) '' (unit_subgroup K),
  add_mem' :=
  begin
    rintros _ _ ⟨u, ⟨hu, rfl⟩⟩ ⟨v, ⟨hv, rfl⟩⟩,
    exact ⟨u * v, ⟨(unit_subgroup K).mul_mem hu hv, map_mul u v⟩⟩,
  end,
  zero_mem' := ⟨1, ⟨(unit_subgroup K).one_mem, map_one⟩⟩,
  neg_mem' :=
  begin
    rintros _ ⟨u, ⟨hu, rfl⟩⟩,
    refine ⟨u⁻¹, ⟨(unit_subgroup K).inv_mem hu, map_inv u⟩⟩,
  end }

lemma units.discrete [number_field K]: discrete_topology (unit_lattice K) :=
begin
  suffices : (metric.closed_ball (0 : (unit_lattice K)) 1).finite,
  { exact
    add_group.discrete_of_finite_ball (by norm_num) (this.subset metric.ball_subset_closed_ball), },
  refine set.finite.of_finite_image _ (subtype.coe_injective.inj_on _),
  rw (_ : coe '' (metric.closed_ball (0 : (unit_lattice K)) 1) =
    ((unit_lattice K : set (infinite_place K → ℝ)) ∩ (metric.closed_ball 0 1))),
  { refine set.finite_of_finite_preimage _ _,
    use Kˣ,
    use log_embedding K,
    {
      sorry, },
    { have : (unit_lattice K : set (infinite_place K → ℝ)) ⊆ set.range (log_embedding K),
      { rw unit_lattice,
        dsimp,
        simp only [unit_lattice, set.image_subset_iff, set.preimage_range, set.subset_univ], },
      exact subset_trans (set.inter_subset_left _ _) this, }},
   ext, split,
  { rintros ⟨x, ⟨hx, rfl⟩⟩,
    exact ⟨subtype.mem x, hx⟩, },
  { rintros ⟨hx1, hx2⟩,
    use [x, hx1, ⟨hx2, rfl⟩], },
end


#exit

lemma units.free_module : module.free ℤ (Λ K) := by sorry

lemma units.rank_le [number_field K] : finrank ℤ (Λ K) ≤  card (infinite_place K) - 1 := by sorry

lemma units.le_rank [number_field K] : card (infinite_place K) - 1 ≤ finrank ℤ (Λ K)  := by sorry

lemma units.rank [number_field K] :
  finrank ℤ (Λ K) = card (infinite_place K) - 1 := le_antisymm (units.rank_le K) (units.le_rank K)

end number_field.log_embedding

end log_embedding
