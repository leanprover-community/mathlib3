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

instance [number_field K] : is_cyclic (torsion K) :=
subgroup_units_cyclic _

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

variables {K} [number_field K]

/-- A distinguished infinite place.-/
def w₀  : infinite_place K := (infinite_place.nonempty K).some

variable (K)

def mult : (infinite_place K) → ℝ := λ w, ite (w.is_real) 1 2

-- TODO. Keep only one of the two
lemma mult_pos (w : infinite_place K) : 0 < mult K w :=
by { simp only [mult], split_ifs; norm_num, }

lemma mult_ge_one (w : infinite_place K) : 1 ≤ mult K w :=
by { simp only [mult], split_ifs; norm_num, }

/-- The logarithmic embedding of the units.-/
@[reducible]
def log_embedding : (𝓤 K) → ({w : infinite_place K // w ≠ w₀} → ℝ) :=
λ x w, (mult K w.1) * real.log (w.1 x)

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
  (log_embedding K x) ⟨w, hw⟩ = (mult K w) * real.log (w x) := rfl

lemma log_embedding.sum_component (x : 𝓤 K) :
  finset.univ.sum (λ w, (log_embedding K x) w) = - (mult K w₀) * real.log (w₀ (x : K)) :=
begin
  rw (_ : finset.univ.sum (λ (w : {w // w ≠ w₀}), _) =
    (finset.univ.erase w₀).sum (λ (w : infinite_place K), (mult K w) * real.log (w x))),
  { rw [neg_mul, eq_neg_iff_add_eq_zero, finset.sum_erase_add _ _ (finset.mem_univ _)],
    convert congr_arg real.log (prod_eq_abs_norm K x),
    { rw [real.log_prod _ _ (λ w _, _), finset.sum_congr rfl (λ w _, _)],
      { simp only [mult, apply_ite real.log, real.log_pow, nat.cast_two, ite_mul, one_mul], },
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
  refine ⟨ λ h w, _, λ h w, _⟩,
  { by_cases hw : w = w₀,
    { suffices : mult K w₀ * real.log (w₀ (x : K)) = 0,
      { rw hw,
        have t1 := (mul_eq_zero.mp this).resolve_left _,
        exact real.eq_one_of_pos_of_log_eq_zero (pos_iff.mpr units_to_field.ne_zero) t1,
        exact ne_of_gt (mult_pos K _), },
      { rw ← neg_eq_zero,
        rw ← neg_mul,
        rw ← log_embedding.sum_component,
        exact finset.sum_eq_zero (λ w _, h w), }},
    { specialize h ⟨w, hw⟩,
      rw log_embedding.component at h,
      rw pi.zero_apply at h,
      have := (mul_eq_zero.mp h).resolve_left _,
      exact real.eq_one_of_pos_of_log_eq_zero (pos_iff.mpr units_to_field.ne_zero) this,
      exact ne_of_gt (mult_pos K _), }},
  { simp only [log_embedding, h w, pi.zero_apply, real.log_one, subtype.val_eq_coe, mul_zero], },
end

lemma log_embedding.nnnorm_eq (x : 𝓤 K) :
  ‖log_embedding K x‖₊ =
    finset.univ.sup (λ w : { w : infinite_place K // w ≠ w₀} , ‖(mult K w.1)* real.log (w.1 x)‖₊) :=
by simp [pi.nnnorm_def, log_embedding]

/-- The lattice formed by the image of the logarithmic embedding.-/
noncomputable def unit_lattice : add_subgroup ({w : infinite_place K // w ≠ w₀} → ℝ) :=
{ carrier := set.range (log_embedding K),
  add_mem' :=
    by { rintros _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩, exact ⟨u * v, log_embedding.map_mul K u v⟩, },
  zero_mem' := ⟨1, log_embedding.map_one K⟩,
  neg_mem' := by { rintros _ ⟨u, rfl⟩, exact ⟨u⁻¹, log_embedding.map_inv K _⟩, }
}

lemma log_embedding_ker (x : 𝓤 K) :
  log_embedding K x = 0 ↔ x ∈ torsion K :=
by rw [log_embedding.eq_zero_iff, mem_torsion K x]

-- TODO. This proof is too complicated
lemma unit_lattice.inter_ball_finite (r : ℝ) :
  ((unit_lattice K : set ({w : infinite_place K // w ≠ w₀} → ℝ)) ∩
    (metric.closed_ball 0 r)).finite :=
begin
  obtain hr | hr := lt_or_le r 0,
  { convert set.finite_empty,
    rw metric.closed_ball_eq_empty.mpr hr,
    exact set.inter_empty _, },
  { let A := {x : 𝓤 K | is_integral ℤ (x : K) ∧
      ∀ φ : (K →+* ℂ), ‖φ x‖ ≤ real.exp (fintype.card (infinite_place K) * r) },
    have t1 : A.finite,
    { suffices : ((coe : (𝓤 K) → K) '' A).finite,
      { refine this.of_finite_image (set.inj_on_of_injective (units_to_field.injective K) _), },
      refine set.finite.subset (embeddings.finite_of_norm_le K ℂ
        (real.exp (fintype.card (infinite_place K) * r))) _,
      rintros _ ⟨x, ⟨hx, rfl ⟩⟩,
      exact hx, },
    have t2 : ((log_embedding K) '' A).finite := set.finite.image _ t1,
    refine t2.subset _,
    rintros _ ⟨⟨u, rfl⟩, hu⟩,
    refine ⟨u, ⟨ring_of_integers.is_integral_coe u, _⟩, rfl⟩,
    rw ← infinite_place.le_iff_le,
    rw mem_closed_ball_zero_iff at hu,
    -- TODO. this is not really needed?
    have bound : ∀ w : infinite_place K, w ≠ w₀ →
      -r ≤ mult K w * real.log (w u) ∧ mult K w * real.log (w u) ≤ r,
    { intros w hw,
      lift r to nnreal using hr,
      rw [← abs_le, ← real.norm_eq_abs, ← coe_nnnorm, nnreal.coe_le_coe],
      rw [← coe_nnnorm, log_embedding.nnnorm_eq K u, nnreal.coe_le_coe] at hu,
      convert finset.sup_le_iff.mp hu ⟨w, hw⟩ (finset.mem_univ _), },
    intro w,
    rw ← real.log_le_iff_le_exp (infinite_place.pos_iff.mpr units_to_field.ne_zero),
    by_cases hw : w = w₀,
    { rw hw,
      rw ← mul_le_mul_left (lt_of_lt_of_le one_pos (mult_ge_one K w₀)),
      rw ← neg_le_neg_iff,
            have := log_embedding.sum_component K u,
      rw ← neg_mul,
      rw ← neg_mul,
      rw ← this,
      suffices : - mult K w₀ * ((fintype.card (infinite_place K)) * r) ≤
        - (fintype.card {w : infinite_place K // w ≠ w₀}) * r,
      { refine le_trans this _,
        rw neg_mul_comm,
        rw fintype.card,
        rw ← nsmul_eq_mul,
        rw ← finset.sum_const,
        refine finset.sum_le_sum (λ w hw, _),
        lift r to nnreal using hr,
        rw ← coe_nnnorm at hu,
        rw pi.nnnorm_def at hu,
        rw nnreal.coe_le_coe at hu,
        have := finset.sup_le_iff.mp hu w (finset.mem_univ _),
        rw ← nnreal.coe_le_coe at this,
        rw coe_nnnorm at this,
        rw real.norm_eq_abs at this,
        rw abs_le at this,
        exact this.1, },
      { rw neg_mul,
        rw neg_mul,
        rw neg_le_neg_iff,
        simp only [fintype.card_subtype_compl, fintype.card_subtype_eq],
        calc
          _   ≤ ↑(fintype.card (infinite_place K)) * r : mul_le_mul_of_nonneg_right _ hr
          ... ≤  mult K dirichlet.w₀ * ((fintype.card (infinite_place K)) * r)
            : le_mul_of_one_le_left (by positivity) (mult_ge_one K w₀),
        simp only [nat.cast_le, tsub_le_self], }},
    { obtain hs | hs := lt_or_le (real.log (w u)) 0,
      { refine le_of_lt (lt_of_lt_of_le hs (by positivity)), },
      { calc
          _   ≤ mult K w * real.log (w u) : le_mul_of_one_le_left hs (mult_ge_one K w)
          ... ≤ r                         : (bound w hw).2
          ... ≤ (fintype.card (infinite_place K)) * r
            : le_mul_of_one_le_left hr (nat.one_le_cast.mpr fintype.card_pos), }}}
end

/-- The unit rank of the number field `K`, that is `card (infinite_place K) - 1`.-/
def unit_rank : ℕ := fintype.card (infinite_place K) - 1

lemma rank_logspace : finrank ℝ ({w : infinite_place K // w ≠ w₀} → ℝ) = unit_rank K :=
begin
  convert @module.free.finrank_pi ℝ _ _ {w : infinite_place K // w ≠ w₀} _,
  simp only [unit_rank, fintype.card_subtype_compl, fintype.card_subtype_eq],
end

-- Construction of suitable units

lemma seq.exists (w : infinite_place K) {f : infinite_place K → nnreal}
  (hf : ∀ z, z ≠ w → f z ≠ 0) (B : ℕ) :
    ∃ C : nnreal, finset.univ.prod (λ v : infinite_place K, ite (v.is_real) (f.update w C v)
    ((f.update w C v) ^ 2)) = B :=
begin
  let S := (finset.univ.erase w).prod (λ v : infinite_place K, ite (v.is_real) (f v) (f v ^ 2)),
  have hS : S ≠ 0,
  { refine finset.prod_ne_zero_iff.mpr _,
    intros z hz,
    split_ifs,
    exacts [hf z (finset.mem_erase.mp hz).1, pow_ne_zero 2 (hf z (finset.mem_erase.mp hz).1)], },
  have Hsub : ∀ C : nnreal, ∀ x : infinite_place K, x ∈ finset.univ.erase w →
    ite x.is_real (ite (x = w) C (f x)) (ite (x = w) C (f x) ^ 2) = ite x.is_real (f x) (f x ^ 2),
  { intros _ x hx,
    simp_rw if_neg (finset.mem_erase.mp hx).1, },
  by_cases hw : w.is_real,
  { use B * S⁻¹,
    rw ← finset.mul_prod_erase finset.univ _ (finset.mem_univ w),
    rw if_pos hw,
    rw function.update_same,
    simp_rw function.update_apply,
    rw finset.prod_congr rfl (Hsub _),
    exact inv_mul_cancel_right₀ hS _, },
  { use nnreal.sqrt (B * S⁻¹),
    rw ← finset.mul_prod_erase finset.univ _ (finset.mem_univ w),
    rw if_neg hw,
    rw function.update_same,
    rw nnreal.sq_sqrt,
    simp_rw function.update_apply,
    rw finset.prod_congr rfl (Hsub _),
    exact inv_mul_cancel_right₀ hS _, },
end

lemma seq.volume (w : infinite_place K) {f : infinite_place K → nnreal} (hf : ∀ z, z ≠ w → f z ≠ 0)
  (B : ℕ) :
  (unit_measure K) (convex_body K (λ v : infinite_place K,
    (f.update w (seq.exists K w hf B).some v))) = (constant_volume K) * B :=
begin
  rw convex_body.volume,
  rw_mod_cast (seq.exists K w hf B).some_spec,
  refl,
end

lemma seq.next {B : ℕ} (w : infinite_place K) (hB : minkowski_bound K < (constant_volume K) * B)
  {x : 𝓞 K} (hx : x ≠ 0) :
  ∃ a : (𝓞 K), a ≠ 0 ∧ (∀ z, z ≠ w → z a < (z x) / 2) ∧ abs (algebra.norm ℚ (a : K)) ≤ B :=
begin
  let f : infinite_place K → nnreal := λ v, ⟨(v x) / 2, div_nonneg (map_nonneg _ _) (by norm_num)⟩,
  have hf : ∀ z, z ≠ w → f z ≠ 0,
  { intros z hz,
    apply (nonneg.mk_eq_zero _).not.mpr,
    simp only [hx, div_eq_zero_iff, map_eq_zero, zero_mem_class.coe_eq_zero, bit0_eq_zero,
      one_ne_zero, or_self, not_false_iff, coe_coe], },
  rw ← (seq.volume K w hf B) at hB,
  have t2 := exists_ne_zero_mem_ring_of_integers_le K hB,
  use t2.some,
  split,
  { exact t2.some_spec.1, },
  { split,
    { intros z hz,
      simp only [*, coe_coe, ne.def, subtype.coe_mk],
      convert t2.some_spec.2 z,
      simp [function.update_apply f _ _ _, hz, if_false, subtype.coe_mk], },
    { rw ← @rat.cast_le ℝ _ _ _,
      rw rat.cast_abs,
      have := prod_eq_abs_norm K (t2.some : K),
      rw ← prod_eq_abs_norm K (t2.some : K),
      have t5 := congr_arg nnreal.to_real_hom (seq.exists K w hf B).some_spec,
      rw map_prod nnreal.to_real_hom _ _ at t5,
      simp_rw apply_ite nnreal.to_real_hom _ _ _ at t5,
      simp_rw map_pow at t5,
      rw nnreal.coe_to_real_hom at t5,
      rw nnreal.coe_nat_cast at t5,
      rw rat.cast_coe_nat,
      refine le_of_le_of_eq (finset.prod_le_prod _ _) t5,
      { intros _ _,
        split_ifs; simp only [pow_nonneg, map_nonneg], },
      { intros z _,
        split_ifs,
        { exact le_of_lt (t2.some_spec.2 z), },
        { refine pow_le_pow_of_le_left (map_nonneg _ _) (le_of_lt (t2.some_spec.2 z)) _, }}}},
end

/-- An infinite sequence of non-zero algebraic integers of `K` satisfying the following properties:
TBC.-/
def seq {B : ℕ} (w : infinite_place K) (hB : minkowski_bound K < (constant_volume K) * B) (n : ℕ) :
  { x : 𝓞 K // x ≠ 0 } :=
begin
  refine nat.rec_on n _ _,
  use ⟨(1 : 𝓞 K), (by norm_num)⟩,
  intros _ a,
  use (seq.next K w hB a.prop).some,
  exact (seq.next K w hB a.prop).some_spec.1,
end

lemma seq.ne_zero {B : ℕ} (w : infinite_place K) (hB : minkowski_bound K < (constant_volume K) * B)
  (n : ℕ) : (seq K w hB n : K) ≠ 0 :=
(map_ne_zero_iff (algebra_map (𝓞 K) K) subtype.val_injective).mpr (seq K w hB n).prop

lemma seq.antitone {B : ℕ} (w : infinite_place K) (hB : minkowski_bound K < (constant_volume K) * B)
  (n m : ℕ) (h : n < m) :
  ∀ v : infinite_place K, v ≠ w → v (seq K w hB m) < v (seq K w hB n) :=
begin
  induction m with m hm,
  { exfalso,
    exact nat.not_lt_zero _ h, },
  { intros v hv,
    have hs : v (seq K w hB m.succ) < v (seq K w hB m),
    { have t1 := (seq.next K w hB (seq K w hB m).prop).some_spec.2.1 v hv,
      have t2 : v (seq K w hB m) / 2 < v (seq K w hB m),
      { exact half_lt_self (pos_iff.mpr (seq.ne_zero K w hB m)), },
      exact t1.trans t2, },
    cases nat.eq_or_lt_of_le (nat.le_of_succ_le_succ h) with h1 h2,
    { rwa h1, },
    { exact hs.trans (hm h2 v hv), }},
end

lemma seq.norm_bdd {B : ℕ} (w : infinite_place K) (hB : minkowski_bound K < (constant_volume K) * B)
  (n : ℕ) :
   1 ≤ (algebra.norm ℤ (seq K w hB n : 𝓞 K)).nat_abs ∧
    (algebra.norm ℤ (seq K w hB n : 𝓞 K)).nat_abs ≤ B :=
begin
  cases n,
  { have : algebra.norm ℤ (1 : 𝓞 K) = 1 := map_one (algebra.norm ℤ),
    simp only [seq, this, subtype.coe_mk, int.nat_abs_one, le_refl, true_and],
    contrapose! hB,
    simp only [nat.lt_one_iff.mp hB, algebra_map.coe_zero, mul_zero, zero_le'], },
  { split,
    { refine nat.succ_le_iff.mpr _,
      refine int.nat_abs_pos_of_ne_zero _,
      rw algebra.norm_ne_zero_iff,
      exact (seq K w hB _).prop, },
    { rw ← @nat.cast_le ℚ _ _ _ _,
      rw int.cast_nat_abs,
      change |algebra_map ℤ ℚ ((algebra.norm ℤ) (seq K w hB n.succ : 𝓞 K))| ≤ B,
      rw ← @algebra.norm_localization ℤ (𝓞 K) _ _ _ ℚ K _ _ _ _ (non_zero_divisors ℤ) _ _ _
        _ _ _ _ _ (seq K w hB n.succ : 𝓞 K),
      exact (seq.next K w hB (seq K w hB n).prop).some_spec.2.2, }},
end

lemma exists_unit (w : infinite_place K ) :
  ∃ u : 𝓤 K, (∀ z : infinite_place K, z ≠ w → real.log (z u) < 0) :=
begin
  rsuffices ⟨B, hB⟩ : ∃ B: ℕ, minkowski_bound K < (constant_volume K) * B,
  { have : ∃ n m, n < m ∧
      ideal.span { (seq K w hB n : 𝓞 K) } = ideal.span { (seq K w hB m : 𝓞 K) },
    { obtain ⟨n, -, m, -, hnm, h⟩ :=
        @set.infinite.exists_ne_map_eq_of_maps_to ℕ (ideal (𝓞 K)) _
          { I : ideal (𝓞 K) | 1 ≤ ideal.abs_norm I ∧ ideal.abs_norm I ≤ B }
          (λ n, ideal.span { seq K w hB n}) set.infinite_univ _ _,
      { by_cases hlt : n < m,
        { exact ⟨n, m, ⟨hlt, h⟩⟩, },
        { refine ⟨m, n, ⟨hnm.lt_or_lt.resolve_left hlt, h.symm⟩⟩, }},
      { intros n _,
        have := seq.norm_bdd K w hB n,
        simp only [this, set.mem_set_of_eq, ideal.abs_norm_span_singleton, and_self], },
      { rw (_ : { I : ideal (𝓞 K) | 1 ≤ ideal.abs_norm I ∧ ideal.abs_norm I ≤ B } =
          (⋃ n ∈ set.Icc 1 B, { I : ideal (𝓞 K) | ideal.abs_norm I = n })),
        { refine set.finite.bUnion (set.Icc 1 B).to_finite _,
          intros n hn,
          exact ideal.finite_set_of_abs_norm_eq hn.1, },
        { ext x,
          simp only [set.mem_set_of_eq, set.mem_Icc, set.mem_Union, exists_prop,
            exists_eq_right'], }}},
    obtain ⟨n, m, hnm, hid⟩ := this,
    rw ideal.span_singleton_eq_span_singleton at hid,
    obtain ⟨u, hu⟩ := hid,
    use u,
    intros z hz,
    have t1 := congr_arg z (congr_arg (coe : (𝓞 K) → K) hu),
    have t2 := seq.antitone K w hB n m hnm z hz,
    simp [coe_coe, mul_mem_class.coe_mul, coe_coe, map_mul, coe_coe, mul_mem_class.coe_mul,
      coe_coe, map_mul] at t1 t2,
    rw ← t1 at t2,
    refine real.log_neg _ _,
    { rw pos_iff,
      exact units_to_field.ne_zero, },
    { refine (mul_lt_iff_lt_one_right _).mp t2,
      exact pos_iff.mpr (seq.ne_zero K w hB n), }},
  { have t2 : 0 < (constant_volume K).to_nnreal,
    { refine ennreal.to_nnreal_pos_iff.mpr ⟨_, _⟩,
      exact constant_volume_pos K,
      exact constant_volume_lt_top K, },
    have A := nnreal.archimedean.arch (minkowski_bound K).to_nnreal t2,
    use A.some + 1,
    suffices : minkowski_bound K ≤ constant_volume K * A.some,
    { refine lt_of_le_of_lt this _,
      simp only [nsmul_eq_mul, nat.cast_add, algebra_map.coe_one, mul_add, mul_one],
      refine ennreal.lt_add_right _ _,
      { refine ennreal.mul_ne_top _ _,
        exact ne_of_lt (constant_volume_lt_top K),
        exact ennreal.nat_ne_top _, },
      { exact (ne_of_lt (constant_volume_pos K)).symm, }},
    have h := A.some_spec,
    simp only [nsmul_eq_mul] at h,
    rw mul_comm,
    rw ← ennreal.coe_le_coe at h,
    simp [ne_of_lt (minkowski_bound_lt_top K), ne_of_lt (constant_volume_lt_top K)] at h,
    convert h,
    ext,
    simp only [nsmul_eq_mul], },
end

lemma unit_lattice.full_lattice :
  submodule.span ℝ (unit_lattice K : set ({w : infinite_place K // w ≠ w₀} → ℝ)) = ⊤ :=
begin
  refine le_antisymm (le_top) _,
  let B := pi.basis_fun ℝ {w : infinite_place K // w ≠ w₀},
  let u : (infinite_place K) → (𝓤 K) := λ w, (exists_unit K w).some,
  let v : { w : infinite_place K // w ≠ w₀ } → ({w : infinite_place K // w ≠ w₀} → ℝ) :=
    λ w, log_embedding K (u w),
  suffices : B.det v ≠ 0,
  { rw ← is_unit_iff_ne_zero at this,
    rw ← ((is_basis_iff_det B).mpr this).2,
    refine submodule.span_monotone _,
    rintros _ ⟨w, rfl⟩,
    exact ⟨u w, rfl⟩, },
  rw basis.det_apply,
  refine matrix.det_ne_zero_of_neg _ _,
  { intros w z h,
    rw basis.coe_pi_basis_fun.to_matrix_eq_transpose,
    rw matrix.transpose_apply,
    dsimp [v],
    rw log_embedding.component,
    refine mul_neg_of_pos_of_neg (mult_pos K _) _,
    { refine (exists_unit K z.1).some_spec w _,
      exact subtype.ext_iff_val.not.mp h, },
    { exact w.prop, }},
  { intro w,
    rw basis.coe_pi_basis_fun.to_matrix_eq_transpose,
    simp_rw  matrix.transpose_apply,
    rw (_ : finset.univ.sum (λ i, v w i) = finset.univ.sum (λ i, (log_embedding K (u w)) i)),
    { rw log_embedding.sum_component,
      refine mul_pos_of_neg_of_neg _ _,
      { rw neg_lt_zero,
        exact mult_pos K _, },
      { refine (exists_unit K w.1).some_spec w₀ _,
        exact w.prop.symm, }},
    { simp_rw log_embedding.component, }},
end

lemma unit_lattice.module.free : module.free ℤ (unit_lattice K) :=
zlattice.module.free ℝ ((unit_lattice.inter_ball_finite K)) (unit_lattice.full_lattice K)

lemma unit_lattice.dim : finrank ℤ (unit_lattice K) = unit_rank K :=
begin
  rw ← rank_logspace K,
  exact zlattice.rank ℝ (unit_lattice.inter_ball_finite K) (unit_lattice.full_lattice K),
end

end units.dirichlet

end number_field
