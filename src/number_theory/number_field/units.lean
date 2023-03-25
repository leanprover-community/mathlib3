/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import group_theory.torsion
import linear_algebra.matrix.to_linear_equiv
import number_theory.number_field.norm
import number_theory.number_field.canonical_embedding
import ring_theory.ideal.norm
import ring_theory.roots_of_unity

/-!
 # Units of a number field
This file defines and proves results about the group `𝓤 K` of units of the ring of integers `𝓞 K`
of a number field `K`.

 ## Tags
number field, units
 -/

-- TODO. Need to backport changes to xfr-unit

open_locale classical number_field

noncomputable theory

variables (K : Type*) [field K]

localized "notation `𝓤`K := (number_field.ring_of_integers K)ˣ" in number_field.units

namespace number_field

open number_field units

/-- The `monoid_hom` from the group of units `𝓤 K` to the field `K`. -/
def units_to_field : (𝓤 K) →* K := monoid_hom.comp (coe_hom K) (map (algebra_map (𝓞 K) K))

lemma units_to_field.injective : function.injective (units_to_field K) :=
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
  rw [units_to_field, monoid_hom.coe_comp],
  exact function.injective.comp t1 t2,
end

instance ring_of_integers.units.has_coe : has_coe (𝓤 K) K := ⟨units_to_field K⟩

section to_field

variable {K}

@[simp]
lemma units_to_field.ext {x y : 𝓤 K} : (x : K) = (y : K) ↔ x = y :=
  (units_to_field.injective K).eq_iff

@[simp]
lemma units_to_field.map_inv {x : 𝓤 K} : ((x⁻¹ : 𝓤 K) : K) = (x : K)⁻¹ :=
map_inv (units_to_field K) x

@[simp]
lemma units_to_field.map_pow {x : 𝓤 K} {n : ℕ} : ((x ^ n : 𝓤 K) : K) = (x : K) ^ n :=
map_pow (units_to_field K) x n

@[simp]
lemma units_to_field.map_zpow {x : 𝓤 K} {n : ℤ} : ((x ^ n : 𝓤 K) : K) = (x : K) ^ n :=
map_zpow (units_to_field K) x n

@[simp]
lemma units_to_field.map_mul {x y : 𝓤 K} : ((x * y : 𝓤 K) : K) = (x : K) * (y : K) := rfl

-- @[simp]
-- lemma coe_coe_eq_to_field {x : 𝓤 K} : ((x : 𝓞 K) : K) = (x : K) := rfl

@[simp]
lemma units_to_field.map_one : ((1 : 𝓤 K) : K) = (1 : K) := rfl

@[simp]
lemma units_to_field.ne_zero {x : 𝓤 K} : (x : K) ≠ 0 :=
subtype.coe_injective.ne_iff.2 (units.ne_zero x)

end to_field

namespace units

-- TODO. That should be tautological
lemma is_unit_iff (x : 𝓞 K) (hx : x ≠ 0):
  is_unit x ↔ is_integral ℤ (x⁻¹ : K) :=
begin
  split,
  { rintros ⟨u, rfl⟩,
    convert ring_of_integers.is_integral_coe u.inv,
    simp only [← coe_coe, inv_eq_coe_inv, units_to_field.map_inv], },
  { intro h,
    rw is_unit_iff_exists_inv,
    use ⟨x⁻¹, h⟩,
    apply @subtype.coe_injective K (λ x, x ∈ 𝓞 K),
    simp only [mul_mem_class.coe_mul, subtype.coe_mk, algebra_map.coe_one],
    refine mul_inv_cancel _,
    exact (@subtype.coe_injective K (λ x, x ∈ 𝓞 K)).ne hx, },
end

-- TODO. Make that an iff and simplify the proof
lemma unit.abs_norm [number_field K] (u : 𝓤 K) :
  abs (ring_of_integers.norm ℚ (u : 𝓞 K) : ℚ) = 1 :=
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
    rw map_one at this,
    exact congr_arg (coe : (𝓞 ℚ) → ℚ) this, },
  { right,
    have := congr_arg rat.ring_of_integers_equiv.symm t5,
    rw ring_equiv.symm_apply_apply _ _ at this,
    rw ring_equiv.map_neg_one at this,
    exact congr_arg (coe : (𝓞 ℚ) → ℚ) this, }
end

section torsion

open number_field number_field.infinite_place

/-- The torsion subgroup of the group of units. -/
def torsion : subgroup 𝓤 K := comm_group.torsion (𝓤 K)

lemma mem_torsion (x : (𝓤 K)) [number_field K] :
  x ∈ torsion K ↔ ∀ w : infinite_place K, w x = 1 :=
begin
  rw (eq_iff_eq x 1 : (∀ w : infinite_place K, w x = 1) ↔ ∀ (φ : K →+* ℂ), ‖φ (x : K)‖ = 1),
  rw [torsion, comm_group.mem_torsion, is_of_fin_order_iff_pow_eq_one],
  split,
  { rintros ⟨n, ⟨hn1, hn2⟩⟩ φ,
    lift n to ℕ+ using hn1,
    rw [← units_to_field.ext, units_to_field.map_pow] at hn2,
    exact norm_map_one_of_pow_eq_one φ.to_monoid_hom hn2, },
  { intro h,
    obtain ⟨n , ⟨hn, hx⟩⟩ := embeddings.pow_eq_one_of_norm_eq_one K ℂ x.1.2 h,
    exact ⟨n, ⟨hn, by { rwa [← units_to_field.ext, units_to_field.map_pow], }⟩⟩, },
end

lemma torsion_finite [number_field K] : finite (torsion K) :=
begin
  suffices : ((coe : (𝓤 K) → K) '' { x : (𝓤 K) | x ∈ (torsion K )}).finite,
  { exact set.finite_coe_iff.mpr (set.finite.of_finite_image this
      ((units_to_field.injective K).inj_on _)), },
  refine (embeddings.finite_of_norm_le K ℂ 1).subset _,
  rintros a ⟨⟨u, _, _, _⟩, ⟨hu, rfl⟩⟩,
  split,
  { exact u.2, },
  { rw ← le_iff_le,
    convert λ w, le_of_eq (((mem_torsion K _).mp hu) w) using 1, },
end

instance [number_field K] : fintype (torsion K) :=
@fintype.of_finite (torsion K) (torsion_finite K)

lemma torsion_cyclic [number_field K] : is_cyclic (torsion K) := subgroup_units_cyclic _

/-- The order of the torsion group of the units of `K`. -/
def torsion_order [number_field K] : ℕ+ :=
begin
  haveI : fintype (torsion K) := fintype.of_finite (torsion K),
  refine ⟨fintype.card (torsion K), _⟩,
  exact fintype.card_pos,
end

lemma torsion_eq_roots_of_unity [number_field K]  :
  torsion K = roots_of_unity (torsion_order K) (𝓞 K) :=
begin
  ext,
  rw mem_roots_of_unity',
  rw torsion_order,
  split,
  { intro hx,
    have := @pow_card_eq_one (torsion K) ⟨x, hx⟩ _ _,
    simp only [submonoid_class.mk_pow, subgroup.mk_eq_one_iff] at this,
    have := congr_arg (coe : (𝓤 K) → (𝓞 K)) this,
    rw units.coe_pow at this,
    convert this, },
  { intro hx,
    rw torsion,
    rw comm_group.mem_torsion,
    rw is_of_fin_order_iff_pow_eq_one,
    use fintype.card (torsion K),
    split,
    { exact fintype.card_pos, },
    { rw units.ext_iff,
      rw units.coe_pow,
      convert hx, }},
end

end torsion

end units

namespace units.dirichlet

open number_field.canonical_embedding number_field finite_dimensional

/-- The multiplicity of an infinite place: it is equal to `1` if the place is real and `2` if
the place is complex. -/
def mult : (infinite_place K) → ℝ := λ w, ite (w.is_real) 1 2

lemma mult_pos (w : infinite_place K) : 0 < mult K w :=
by { simp only [mult], split_ifs; norm_num, }

section log_embedding

variables {K} [number_field K]

/-- A distinguished infinite place. -/
def w₀  : infinite_place K := (infinite_place.nonempty K).some

variable (K)

/-- The logarithmic embedding of the units. -/
@[reducible]
def log_embedding : (𝓤 K) → ({w : infinite_place K // w ≠ w₀} → ℝ) :=
λ x w, mult K w.1 * real.log (w.1 x)

open number_field number_field.infinite_place finite_dimensional number_field.units

lemma log_embedding.map_one : log_embedding K 1 = 0 :=
by simpa [log_embedding, units_to_field.map_one, map_one, real.log_one]

lemma log_embedding.map_mul (x y : 𝓤 K) :
  log_embedding K (x * y) = log_embedding K x + log_embedding K y :=
by simpa only [log_embedding, real.log_mul, units_to_field.map_mul, units_to_field.ne_zero,
    map_mul, mul_add, ne.def, map_eq_zero, not_false_iff]

lemma log_embedding.map_inv (x : 𝓤 K) : log_embedding K x⁻¹ = - log_embedding K x :=
by simpa only [log_embedding, units_to_field.map_inv, map_inv₀, real.log_inv, mul_neg]

-- lemma log_embedding.map_zpow (x : 𝓤 K) (n : ℤ) :
-- log_embedding K (x ^ n) = n • log_embedding K x :=
-- sorry -- by simpa only [log_embedding, units_to_field.map_zpow, map_zpow₀, real.log_zpow]

@[simp]
lemma log_embedding.component {w : infinite_place K} (hw : w ≠ w₀) (x : 𝓤 K) :
  (log_embedding K x) ⟨w, hw⟩ = mult K w * real.log (w x) := rfl

lemma log_embedding.sum_component (x : 𝓤 K) :
  finset.univ.sum (λ w, (log_embedding K x) w) = - mult K w₀ * real.log (w₀ (x : K)) :=
begin
  rw (_ : finset.univ.sum (λ (w : {w // w ≠ w₀}), _) =
    (finset.univ.erase w₀).sum (λ (w : infinite_place K), mult K w * real.log (w x))),
  { rw [neg_mul, eq_neg_iff_add_eq_zero, finset.sum_erase_add _ _ (finset.mem_univ _)],
    convert congr_arg real.log (prod_eq_abs_norm K x),
    { rw [real.log_prod _ _ (λ w _, _), finset.sum_congr rfl (λ w _, _)],
      { simp [mult, apply_ite real.log, real.log_pow, nat.cast_two, ite_mul, one_mul], },
      { rw ne.def,
        split_ifs;
        simp only [map_eq_zero, units_to_field.ne_zero, not_false_iff, pow_eq_zero_iff,
          nat.succ_pos'], }},
    { convert (congr_arg real.log (congr_arg (coe : ℚ → ℝ) (unit.abs_norm K x))).symm,
      { simp only [algebra_map.coe_one, real.log_one], },
      { simpa only [rat.cast_abs], }}},
  { rw @finset.sum_subtype _ _ _ (λ w, w ≠ w₀) infer_instance (finset.univ.erase w₀) (λ _, _)
      (λ w, mult K w * real.log (w x)),
    { refine finset.sum_congr rfl (λ w _, _),
      simp only [log_embedding, subtype.val_eq_coe], },
    { simp only [finset.mem_erase, finset.mem_univ, and_true], }},
end

lemma log_embedding.eq_zero_iff (x : 𝓤 K) :
  log_embedding K x = 0 ↔ (∀ w : infinite_place K, w x = 1) :=
begin
  rw function.funext_iff,
  refine ⟨λ h w, _, λ h w, _⟩,
  { by_cases hw : w = w₀,
    { suffices : mult K w₀ * real.log (w₀ (x : K)) = 0,
      { rw hw,
        exact real.eq_one_of_pos_of_log_eq_zero (pos_iff.mpr units_to_field.ne_zero)
          ((mul_eq_zero.mp this).resolve_left (ne_of_gt (mult_pos K _))), },
      { rw [← neg_eq_zero, ← neg_mul, ← log_embedding.sum_component],
        exact finset.sum_eq_zero (λ w _, h w), }},
    { specialize h ⟨w, hw⟩,
      rw [log_embedding.component, pi.zero_apply] at h,
      exact real.eq_one_of_pos_of_log_eq_zero (pos_iff.mpr units_to_field.ne_zero)
        ((mul_eq_zero.mp h).resolve_left (ne_of_gt (mult_pos K _))), }},
  { simp only [log_embedding, h w, pi.zero_apply, real.log_one, subtype.val_eq_coe, mul_zero], },
end

lemma log_embedding.nnnorm_eq (x : 𝓤 K) :
  ‖log_embedding K x‖₊ =
    finset.univ.sup (λ w : { w : infinite_place K // w ≠ w₀}, ‖mult K w.1 * real.log (w.1 x)‖₊) :=
by simp [pi.nnnorm_def, log_embedding]

/-- The lattice formed by the image of the logarithmic embedding. -/
noncomputable def unit_lattice : add_subgroup ({w : infinite_place K // w ≠ w₀} → ℝ) :=
{ carrier := set.range (log_embedding K),
  add_mem' :=
    by { rintros _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩, exact ⟨u * v, log_embedding.map_mul K u v⟩, },
  zero_mem' := ⟨1, log_embedding.map_one K⟩,
  neg_mem' := by { rintros _ ⟨u, rfl⟩, exact ⟨u⁻¹, log_embedding.map_inv K _⟩, }}

lemma log_embedding_ker (x : 𝓤 K) :
  log_embedding K x = 0 ↔ x ∈ torsion K :=
by rw [log_embedding.eq_zero_iff, mem_torsion K x]

-- Break this proof?
lemma unit_lattice.inter_ball_finite (r : ℝ) :
  ((unit_lattice K : set ({w : infinite_place K // w ≠ w₀} → ℝ)) ∩
    (metric.closed_ball 0 r)).finite :=
begin
  obtain hr | hr := lt_or_le r 0,
  { convert set.finite_empty,
    rw metric.closed_ball_eq_empty.mpr hr,
    exact set.inter_empty _, },
  { suffices : {x : 𝓤 K | is_integral ℤ (x : K) ∧
      ∀ φ : (K →+* ℂ), ‖φ x‖ ≤ real.exp (fintype.card (infinite_place K) * r)}.finite,
    { refine (set.finite.image (log_embedding K) this).subset _,
      rintros _ ⟨⟨u, rfl⟩, hu⟩,
      refine ⟨u, ⟨ring_of_integers.is_integral_coe u, (infinite_place.le_iff_le _ _).mp _⟩, rfl⟩,
      lift r to nnreal using hr,
      rw [mem_closed_ball_zero_iff, ← coe_nnnorm, nnreal.coe_le_coe,
        log_embedding.nnnorm_eq K u] at hu,
      have w_bound : ∀ w : infinite_place K, w ≠ w₀ →
        -(r : ℝ) ≤ mult K w * real.log (w u) ∧ mult K w * real.log (w u) ≤ r,
      { intros w hw,
        rw [← abs_le, ← real.norm_eq_abs, ← coe_nnnorm, nnreal.coe_le_coe],
        convert finset.sup_le_iff.mp hu ⟨w, hw⟩ (finset.mem_univ _), },
      have one_le_mult : ∀ w : infinite_place K, 1 ≤ mult K w,
      { intro w, simp only [mult], split_ifs; norm_num, },
      intro w,
      rw ← (real.log_le_iff_le_exp (infinite_place.pos_iff.mpr units_to_field.ne_zero)),
      by_cases hw : w = w₀,
      { rw [hw, ← mul_le_mul_left (lt_of_lt_of_le one_pos (one_le_mult w₀)), ← neg_le_neg_iff,
          ← neg_mul, ← neg_mul, ← log_embedding.sum_component K u],
        refine le_trans _ (@finset.sum_le_sum _ _ _ ( λ _, -(r : ℝ)) _ _ (λ w hw, _)),
        { rw [finset.sum_neg_distrib, finset.sum_const, nsmul_eq_mul, neg_mul, neg_le_neg_iff],
          calc
            _   ≤ (fintype.card (infinite_place K) : ℝ) * r : mul_le_mul_of_nonneg_right
              (by { rw [← fintype.card, fintype.card_subtype_compl, fintype.card_subtype_eq],
                norm_num, }) (nnreal.coe_nonneg r)
            ... ≤ dirichlet.mult K dirichlet.w₀ * ((fintype.card (infinite_place K)) * r) :
              le_mul_of_one_le_left _ (one_le_mult w₀),
          exact mul_nonneg (fintype.card (infinite_place K)).cast_nonneg (nnreal.coe_nonneg r), },
        { erw log_embedding.component K w.prop u,
          exact (w_bound w.val w.prop).1, }},
      { rw ← mul_le_mul_left (mult_pos K w),
        refine le_trans (w_bound w hw).2 _,
        rw ← mul_assoc,
        refine le_mul_of_one_le_left (nnreal.coe_nonneg r) _,
        exact one_le_mul_of_one_le_of_one_le (one_le_mult w)
          (nat.one_le_cast.mpr fintype.card_pos), }},
    { refine set.finite.of_finite_image _ (set.inj_on_of_injective (units_to_field.injective K) _),
      refine (embeddings.finite_of_norm_le K ℂ
        (real.exp (fintype.card (infinite_place K) * r))).subset _,
      rintros _ ⟨u, hu, rfl⟩,
      exact ⟨ring_of_integers.is_integral_coe u.val, hu.2⟩, }},
end

/-- The unit rank of the number field `K`, that is `card (infinite_place K) - 1`. -/
def unit_rank : ℕ := fintype.card (infinite_place K) - 1

lemma rank_space : finrank ℝ ({w : infinite_place K // w ≠ w₀} → ℝ) = unit_rank K :=
by { convert @module.free.finrank_pi ℝ _ _ {w : infinite_place K // w ≠ w₀} _,
    simp only [unit_rank, fintype.card_subtype_compl, fintype.card_subtype_eq] }

end log_embedding

open number_field.infinite_place

-- Construction of suitable units

section seq

variable {K}

variables (w : infinite_place K) {f : infinite_place K → nnreal}

/-- The function  `g : infinite_place K → nnreal` obtained from `f : infinite_place K → nnreal`
by setting `g v = f v` if `v` is real and `g v = (f v) ^ 2` otherwise and by replacing the
value `f w` by `C`. -/
@[reducible]
def seq.update (f : infinite_place K → nnreal) (C : nnreal) : infinite_place K → nnreal :=
λ v, ite (v.is_real) (f.update w C v) ((f.update w C v) ^ 2)

variable [number_field K]

lemma seq.exists_bound (hf : ∀ z, z ≠ w → f z ≠ 0) (B : ℕ) :
    ∃ C : nnreal, finset.univ.prod (seq.update w f C) = B :=
begin
  let S := (finset.univ.erase w).prod (λ v : infinite_place K, ite (v.is_real) (f v) (f v ^ 2)),
  have S_nonzero : S ≠ 0,
  { refine finset.prod_ne_zero_iff.mpr (λ z hz, _),
    split_ifs,
    exacts [hf z (finset.mem_erase.mp hz).1, pow_ne_zero 2 (hf z (finset.mem_erase.mp hz).1)], },
  have C_subst : ∀ C, ∀ v : infinite_place K, v ∈ finset.univ.erase w →
    ite v.is_real (ite (v = w) C (f v)) (ite (v = w) C (f v) ^ 2) = ite v.is_real (f v) (f v ^ 2),
  { intros _ v hv,
    simp_rw if_neg (finset.mem_erase.mp hv).1, },
  simp_rw [← finset.mul_prod_erase finset.univ _ (finset.mem_univ w), function.update_same,
    function.update_apply],
  by_cases hw : w.is_real,
  { use B * S⁻¹,
    simp_rw [if_pos hw, finset.prod_congr rfl (C_subst _)],
    exact inv_mul_cancel_right₀ S_nonzero _, },
  { use nnreal.sqrt (B * S⁻¹),
    simp_rw [if_neg hw, nnreal.sq_sqrt, finset.prod_congr rfl (C_subst _)],
    exact inv_mul_cancel_right₀ S_nonzero _, },
end

lemma seq.volume (hf : ∀ z, z ≠ w → f z ≠ 0) (B : ℕ) :
  (unit_measure K) (convex_body K (f.update w (seq.exists_bound w hf B).some)) =
    (constant_volume K) * B :=
by { rw convex_body.volume, rw_mod_cast (seq.exists_bound w hf B).some_spec, refl, }

variables {B : ℕ} (hB : minkowski_bound K < (constant_volume K) * B)

include hB

lemma seq.next {x : 𝓞 K} (hx : x ≠ 0) :
  ∃ a : (𝓞 K), a ≠ 0 ∧ (∀ z, z ≠ w → z a < (z x) / 2) ∧ abs (algebra.norm ℚ (a : K)) ≤ B :=
begin
  let f : infinite_place K → nnreal := λ v, ⟨(v x) / 2, div_nonneg (map_nonneg _ _) (by norm_num)⟩,
  have hf : ∀ z, z ≠ w → f z ≠ 0,
  { simp only [hx, ne.def, nonneg.mk_eq_zero, div_eq_zero_iff, map_eq_zero, or_self, not_false_iff,
      zero_mem_class.coe_eq_zero, bit0_eq_zero, one_ne_zero, implies_true_iff], },
  rw ← (seq.volume w hf B) at hB,
  have exists_sol := exists_ne_zero_mem_ring_of_integers_le K hB,
  refine ⟨exists_sol.some, exists_sol.some_spec.1, _, _⟩,
  { intros z hz,
    convert exists_sol.some_spec.2 z,
    simp_rw [function.update_apply f, apply_ite (coe : _ → ℝ), if_neg hz, f, subtype.coe_mk], },
  { rw [← @rat.cast_le ℝ, rat.cast_abs, ← prod_eq_abs_norm K (exists_sol.some : K)],
    refine le_of_le_of_eq (finset.prod_le_prod (λ _ _, _) (λ z _, _)) _,
    { exact (coe : _ → ℝ) ∘ (seq.update w f (seq.exists_bound w hf B).some), },
    { split_ifs; positivity, },
    { rw [seq.update, function.comp_apply],
      split_ifs,
      exact le_of_lt (exists_sol.some_spec.2 z),
      exact pow_le_pow_of_le_left (map_nonneg _ _) (le_of_lt (exists_sol.some_spec.2 z)) _, },
    { convert congr_arg (coe : _ → ℝ) (seq.exists_bound w hf B).some_spec,
      rw [← nnreal.coe_to_real_hom, map_prod nnreal.to_real_hom], }}
end

/-- An infinite sequence of non-zero algebraic integers of `K` satisfying the following properties:
1) `seq n` is non-zero;
2) for `v : infinite_place K`, `v ≠ w → v (seq n+1) < v (seq n) /2 `;
3) `∣norm (seq n)∣ ≤ B`. -/
def seq (n : ℕ) : { x : 𝓞 K // x ≠ 0 } :=
nat.rec_on n ⟨(1 : 𝓞 K), (by norm_num)⟩
  (λ _ a, ⟨(seq.next w hB a.prop).some, (seq.next w hB a.prop).some_spec.1⟩)

lemma seq.ne_zero (n : ℕ) : (seq w hB n : K) ≠ 0 :=
(map_ne_zero_iff (algebra_map (𝓞 K) K) subtype.val_injective).mpr (seq w hB n).prop

lemma seq.antitone (n m : ℕ) (h : n < m) :
  ∀ v : infinite_place K, v ≠ w → v (seq w hB m) < v (seq w hB n) :=
begin
  induction m with m hm,
  { exfalso, exact nat.not_lt_zero _ h, },
  { intros v hv,
    suffices : v (seq w hB m.succ) < v (seq w hB m),
    { cases nat.eq_or_lt_of_le (nat.le_of_succ_le_succ h) with h1 h2,
      { rwa h1, },
      { exact this.trans (hm h2 v hv), }},
    { refine lt_trans ((seq.next w hB (seq w hB m).prop).some_spec.2.1 v hv) _,
      exact half_lt_self (pos_iff.mpr (seq.ne_zero w hB m)), }},
end

lemma seq.norm_bdd (n : ℕ) :
   1 ≤ (algebra.norm ℤ (seq w hB n : 𝓞 K)).nat_abs ∧
    (algebra.norm ℤ (seq w hB n : 𝓞 K)).nat_abs ≤ B :=
begin
  cases n,
  { erw [map_one (algebra.norm ℤ), int.nat_abs_one],
    refine ⟨le_rfl, _⟩,
    contrapose! hB,
    simp only [nat.lt_one_iff.mp hB, algebra_map.coe_zero, mul_zero, zero_le'], },
  { refine ⟨nat.succ_le_iff.mpr (int.nat_abs_pos_of_ne_zero _), _⟩,
    { exact (algebra.norm_ne_zero_iff.mpr (seq w hB _).prop), },
    { rw [← @nat.cast_le ℚ, int.cast_nat_abs],
      change |algebra_map ℤ ℚ ((algebra.norm ℤ) (seq w hB n.succ : 𝓞 K))| ≤ B,
      rw ← @algebra.norm_localization ℤ (𝓞 K) _ _ _ ℚ K _ _ _ _ (non_zero_divisors ℤ),
      exact (seq.next w hB (seq w hB n).prop).some_spec.2.2, }},
end

end seq

variable [number_field K]

-- open number_field.canonical_embedding

lemma exists_unit (w : infinite_place K ) :
  ∃ u : 𝓤 K, (∀ z : infinite_place K, z ≠ w → real.log (z u) < 0) :=
begin
  obtain ⟨B, hB⟩ : ∃ B : ℕ, minkowski_bound K < (constant_volume K) * B,
  { conv { congr, funext, rw mul_comm, },
    exact ennreal.exists_nat_mul_gt (pos_iff_ne_zero.mp (constant_volume_pos K))
      (ne_of_lt (minkowski_bound_lt_top K)), },
  rsuffices ⟨n, m, hnm, h⟩ : ∃ n m : ℕ, n < m ∧
    ideal.span ({ seq w hB n } : set (𝓞 K)) = ideal.span { seq w hB m },
  { obtain ⟨u, hu⟩ := ideal.span_singleton_eq_span_singleton.mp h,
    refine ⟨u, λ z hz, real.log_neg _ _⟩,
    { exact pos_iff.mpr units_to_field.ne_zero, },
    { refine (mul_lt_iff_lt_one_right ((@pos_iff _ _ z _).mpr (seq.ne_zero w hB n))).mp _,
      convert seq.antitone w hB n m hnm z hz,
      rw ← map_mul,
      congr,
      exact (congr_arg (coe : _ → K) hu), }},
  { refine set.finite.exists_lt_map_eq_of_forall_mem (λ n, _) _,
    { exact { I : ideal (𝓞 K) | 1 ≤ ideal.abs_norm I ∧ ideal.abs_norm I ≤ B }, },
    { simpa only [ideal.abs_norm_span_singleton, set.mem_set_of_eq] using seq.norm_bdd w hB n, },
    { rw (_ : { I : ideal (𝓞 K) | 1 ≤ ideal.abs_norm I ∧ ideal.abs_norm I ≤ B } =
          (⋃ n ∈ set.Icc 1 B, { I : ideal (𝓞 K) | ideal.abs_norm I = n })),
      { refine set.finite.bUnion (set.Icc 1 B).to_finite (λ n hn, _),
        exact ideal.finite_set_of_abs_norm_eq hn.1, },
      { ext I,
        simp only [set.mem_set_of_eq, set.mem_Icc, set.mem_Union, exists_prop,
          exists_eq_right'], }}},
end

lemma unit_lattice.span_eq_top :
  submodule.span ℝ (unit_lattice K : set ({w : infinite_place K // w ≠ w₀} → ℝ)) = ⊤ :=
begin
  let B := pi.basis_fun ℝ {w : infinite_place K // w ≠ w₀},
  set v := λ w : { w : infinite_place K // w ≠ w₀ }, log_embedding K ((exists_unit K w).some)
    with v_def,
  refine le_antisymm (le_top) _,
  suffices : B.det v ≠ 0,
  { rw ← ((is_basis_iff_det B).mpr (is_unit_iff_ne_zero.mpr this)).2,
    exact submodule.span_monotone (by { rintros _ ⟨w, rfl⟩, exact ⟨(exists_unit K w).some, rfl⟩ })},
  rw basis.det_apply,
  refine matrix.det_ne_zero_of_neg (λ w z h, _) (λ w, _),
  { rw [basis.coe_pi_basis_fun.to_matrix_eq_transpose, matrix.transpose_apply, v_def],
    simp_rw log_embedding.component,
    refine mul_neg_of_pos_of_neg (mult_pos K _) _,
    exact (exists_unit K z.1).some_spec w (subtype.ext_iff_val.not.mp h), },
  { simp_rw [basis.coe_pi_basis_fun.to_matrix_eq_transpose, matrix.transpose_apply, v_def,
      log_embedding.sum_component],
    exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr (mult_pos K _))
      ((exists_unit K w.1).some_spec w₀ w.prop.symm), },
end

lemma unit_lattice.module.free : module.free ℤ (unit_lattice K) :=
zlattice.module.free ℝ ((unit_lattice.inter_ball_finite K)) (unit_lattice.span_eq_top K)

lemma unit_lattice.rank : finrank ℤ (unit_lattice K) = unit_rank K :=
by { rw ← rank_space K,
  exact zlattice.rank ℝ (unit_lattice.inter_ball_finite K) (unit_lattice.span_eq_top K), }

end units.dirichlet

end number_field
