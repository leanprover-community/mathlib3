/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/

import algebra.gcd_monoid.basic
import linear_algebra.finsupp
import ring_theory.int.basic

/-!
# An example of a non-normalizable `gcd_monoid`

Idea: for a `cancel_comm_monoid_with_zero M`, `1 → Mˣ → M \ {0} → associates M \ {0} → 1` is an
"exact sequence" (after replacing `M \ {0}` and `associates M \ {0}` by their group completions).
`normalization_monoid_of_monoid_hom_right_inverse` shows that if the sequence is right split, then
`M` can be equipped with a `normalization_monoid` structure. In order for `M` to admit no
`normalization_monoid` structure, `associates M \ {0}` must not be projective, and infinitely
generated subgroups of ℚ serve as such examples. (Since `associates M \ {0}` is always
torsion free, it's always free if it's finitely generated.)

-/

section preparation

/- not used -/
def cancel_comm_monoid_with_zero_of_cancel {α} [comm_monoid_with_zero α]
  (h : ∀ a b c : α, a ≠ 0 → a * b = a * c → b = c) : cancel_comm_monoid_with_zero α :=
{ mul_left_cancel_of_ne_zero := h,
  mul_right_cancel_of_ne_zero := λ a b c hb, by { simp_rw ← mul_comm b, exact h _ _ _ hb },
  .. ‹comm_monoid_with_zero α› }

instance submonoid.cancel_monoid {α} [cancel_monoid α] (S : submonoid α) : cancel_monoid S :=
{ mul_left_cancel := λ a b c h, by { rw [subtype.ext_iff] at h ⊢, exact mul_left_cancel h },
  mul_right_cancel := λ a b c h, by { rw [subtype.ext_iff] at h ⊢, exact mul_right_cancel h },
  .. (by apply_instance : monoid S) }

instance submonoid.cancel_comm_monoid {α} [cancel_comm_monoid α] (S : submonoid α) :
  cancel_comm_monoid S :=
{ .. (by apply_instance : cancel_monoid S), .. (by apply_instance : comm_monoid S) }

theorem map_dvd' {M N F} [semigroup M] [semigroup N] [mul_hom_class F M N] (f : F) {a b : M} :
  a ∣ b → f a ∣ f b := λ ⟨c, hc⟩, ⟨f c, by rw [hc, map_mul]⟩

lemma int.eq_zero_of_forall_pow_dvd (m n : ℤ)
  (hm : m.nat_abs ≠ 1) (hd : ∀ k : ℕ, m ^ k ∣ n) : n = 0 :=
begin
  rw [← multiplicity.not_finite_iff_forall, multiplicity.finite_int_iff] at hd,
  contrapose! hd, exact ⟨hm, hd⟩,
end

section with_zero

lemma with_zero.eq_zero_or_coe {α} (x : with_zero α) : x = 0 ∨ ∃ a : α, ↑a = x :=
(em _).imp id with_zero.ne_zero_iff_exists.1

instance {α} [cancel_monoid α] : cancel_monoid_with_zero (with_zero α) :=
begin
  refine_struct { .. (by apply_instance : monoid_with_zero $ with_zero α) },
  intros a b, swap, intros b a,
  all_goals { intros c ha he,
    obtain ⟨a, rfl⟩ := with_zero.ne_zero_iff_exists.1 ha,
    obtain rfl | ⟨b, rfl⟩ := b.eq_zero_or_coe; obtain rfl | ⟨c, rfl⟩ := c.eq_zero_or_coe,
    { refl }, all_goals { simp only [← with_zero.coe_mul] at he },
    iterate 2 { simp only [zero_mul, mul_zero] at he, cases he },
    rw [with_zero.coe_inj] at he ⊢ },
  exacts [mul_right_cancel he, mul_left_cancel he],
end

instance {α} [cancel_comm_monoid α] : cancel_comm_monoid_with_zero (with_zero α) :=
{ .. (by apply_instance : cancel_monoid_with_zero $ with_zero α),
  .. (by apply_instance : comm_monoid_with_zero $ with_zero α) }

@[simps] def with_zero.mul_hom (α) [semigroup α] : α →ₙ* with_zero α :=
{ to_fun := coe, map_mul' := λ a b, rfl }

@[simps] def with_zero.monoid_hom (α) [monoid α] : α →* with_zero α :=
{ to_fun := coe, map_mul' := λ a b, rfl, map_one' := rfl }

lemma with_zero.coe_dvd_iff {G} [semigroup G] {a b : G} : (a : with_zero G) ∣ b ↔ a ∣ b :=
⟨λ ⟨c, hc⟩, begin
  obtain rfl | h := eq_or_ne c 0,
  { cases hc.trans (mul_zero _) },
  { rw [← with_zero.coe_unzero h, ← with_zero.coe_mul, with_zero.coe_inj] at hc, exact ⟨_, hc⟩ },
end, map_dvd' (with_zero.mul_hom G)⟩

def with_zero.units_equiv (α) [monoid α] : αˣ ≃* (with_zero α)ˣ :=
{ inv_fun   := λ a, begin
    refine ⟨with_zero.unzero a.ne_zero, with_zero.unzero a⁻¹.ne_zero, _, _⟩;
      rw [← with_zero.coe_inj, with_zero.coe_mul]; simp_rw with_zero.coe_unzero,
    exacts [a.mul_inv, a.inv_mul],
  end,
  left_inv  := λ _, units.ext rfl,
  right_inv := λ _, units.ext $ with_zero.coe_unzero _,
  .. units.map (with_zero.monoid_hom α) }

end with_zero

section normalization_with_zero

variables (α : Type*) [cancel_comm_monoid α] [normalization_monoid (with_zero α)]

@[simps] def normalize_nonzero : α →* αˣ :=
{ to_fun := λ a, (with_zero.units_equiv α).symm (norm_unit $ with_zero.monoid_hom α a)⁻¹,
  map_one' := by { rw [with_zero.monoid_hom_apply, with_zero.coe_one, norm_unit_one], refl },
  map_mul' := λ a b, begin
    rw [with_zero.monoid_hom_apply, with_zero.coe_mul, norm_unit_mul, mul_inv],
    { apply map_mul }, all_goals { intro h, cases h },
  end }

variable {α}

lemma normalize_nonzero_splits (a : αˣ) : normalize_nonzero α a = a :=
begin
  rw [normalize_nonzero_apply, ← units.coe_map, norm_unit_coe_units, inv_inv],
  apply (with_zero.units_equiv α).left_inv,
end

lemma coe_normalize_nonzero_of_is_unit {a : α} (ha : is_unit a) : ↑(normalize_nonzero α a) = a :=
by rw [← ha.unit_spec, normalize_nonzero_splits]

end normalization_with_zero

noncomputable def mul_equiv_of_left_splits {α β} [group α] [monoid β]
  (f : α →* β) (S : submonoid β) (g : S.comap f →* f.ker)
  (h : ∀ a, g (submonoid.inclusion (submonoid.monotone_comap bot_le) a) = a) :
  S.comap f ≃* f.ker × (S ⊓ f.mrange : submonoid β) :=
mul_equiv.of_bijective
  (g.prod $ (f.restrict _).cod_restrict (_ ⊓ f.mrange) $ λ x, ⟨x.2, x, rfl⟩)
begin
  refine ⟨λ a₁ a₂, _, _⟩,
  work_on_goal 2 { rintro ⟨a, _, ha', a', rfl⟩ },
  all_goals { simp only [monoid_hom.prod_apply, monoid_hom.restrict_apply,
      monoid_hom.cod_restrict_apply, prod.mk.inj_iff, subtype.mk_eq_mk] },
  { intro ha,
    have : f (a₁ * a₂⁻¹) = 1,
    { rw [f.map_mul, ha.2, ← f.map_mul, mul_inv_self, f.map_one] },
    specialize h ⟨_, this⟩,
    change g ⟨a₁ * a₂⁻¹, _⟩ = _ at h,
    simp only [subtype.ext_iff, subtype.coe_mk] at h ⊢,
    rw [← mul_inv_eq_one, ← h, ← @mul_left_eq_self _ _ _ ↑(g a₂),
      ← submonoid.coe_mul, ← g.map_mul, ← ha.1],
    congr, ext1, apply inv_mul_cancel_right },
  { refine ⟨⟨a', ha'⟩ * submonoid.inclusion (submonoid.monotone_comap bot_le) (_ * a), _, _⟩,
    { exact ((g ⟨a', ha'⟩)⁻¹ : f.ker) },
    { rw [g.map_mul, h, ← mul_assoc, mul_inv_self, one_mul] },
    { rw [submonoid.coe_mul, f.map_mul], convert mul_one _,
      change _ ∈ f.ker, apply set_like.coe_mem } },
end

end preparation

noncomputable theory

@[reducible] def rat_hom : (ℕ →₀ ℤ) →+ ℚ := (finsupp.lift ℚ ℤ ℕ $ λ n, (2 ^ n)⁻¹).to_add_monoid_hom

def nnrat : add_submonoid ℚ :=
{ carrier := {r | 0 ≤ r},
  add_mem' := λ r s, by { simp only [set.mem_set_of], exact add_nonneg },
  zero_mem' := le_refl (0 : ℚ) }

/- not used -/
lemma nnrat.le_iff_exists_add (a b : nnrat) : a ≤ b ↔ ∃ c, b = a + c :=
⟨λ h, ⟨⟨b - a, sub_nonneg.2 h⟩, subtype.ext (add_sub_cancel'_right _ _).symm⟩,
 by { rintro ⟨c, rfl⟩, exact le_add_of_nonneg_right c.2 }⟩

@[reducible] def M := nnrat.to_submonoid.comap rat_hom.to_multiplicative

example : cancel_comm_monoid_with_zero (with_zero M) := infer_instance

def M_of_ker : rat_hom.to_multiplicative.ker →* M :=
submonoid.inclusion (submonoid.monotone_comap bot_le)

lemma coe_units_M_mem_ker (x : Mˣ) :
  (x : multiplicative (ℕ →₀ ℤ)) ∈ rat_hom.to_multiplicative.ker :=
begin
  have hx : 0 ≤ rat_hom _ := x.1.2,
  have hxi : 0 ≤ rat_hom _ := x.2.2,
  have := ((le_add_of_nonneg_right hxi).trans_eq _).antisymm hx, { exact this },
  simp_rw [← rat_hom.map_add, ← to_add_mul, subtype.val_eq_coe, ← submonoid.coe_mul, x.3],
  exact rat_hom.map_zero,
end

def seq (n : ℕ) : ↥(nnrat ⊓ rat_hom.mrange) :=
⟨(2 ^ n)⁻¹, (@inv_nonneg ℚ _ _).2 (pow_nonneg zero_le_two _), finsupp.single n 1, begin
  rw [linear_map.to_add_monoid_hom_coe, finsupp.lift_apply, finsupp.sum_single_index],
  { apply one_smul }, { apply zero_smul },
end⟩

def ker_mul_equiv_units_M : rat_hom.to_multiplicative.ker ≃* Mˣ :=
{ inv_fun := λ x, ⟨x, coe_units_M_mem_ker x⟩,
  left_inv := λ ⟨_, _⟩, rfl,
  right_inv := λ x, by { ext1, ext1, refl },
  .. (units.map M_of_ker).comp to_units.to_monoid_hom }

lemma nnrat_inf_range_hom_finsupp_apply_seq_zero (f : ↥(nnrat ⊓ rat_hom.mrange) →+ ℕ →₀ ℤ) :
  f (seq 0) = 0 :=
begin
  ext1 n,
  refine int.eq_zero_of_forall_pow_dvd 2 _ (by norm_num) (λ k, ⟨f (seq k) n, _⟩),
  rw [← nat.cast_two, ← nat.cast_pow, ← nsmul_eq_mul, ← finsupp.smul_apply, ← map_nsmul],
  congr, ext1,
  rw [add_submonoid.coe_nsmul, nsmul_eq_mul, seq, seq],
  norm_cast, rw mul_inv_cancel; norm_num [pow_ne_zero],
end

lemma rat_hom_le_iff_dvd {a b : M} :
  rat_hom (multiplicative.to_add ↑a) ≤ rat_hom (multiplicative.to_add ↑b) ↔ a ∣ b :=
begin
  rw [← sub_nonneg, ← map_sub], refine
    ⟨λ h, ⟨⟨multiplicative.of_add (multiplicative.to_add ↑b - multiplicative.to_add ↑a), h⟩, _⟩, _⟩,
  { ext1, exact (mul_div_cancel'_right _ _).symm },
  { rintro ⟨c, rfl⟩, convert c.2, apply add_sub_cancel' },
end

def gcd_M (a b : M) : M :=
if rat_hom (multiplicative.to_add ↑a) ≤ rat_hom (multiplicative.to_add ↑b) then a else b

lemma gcd_M_dvd_left (a b : M) : gcd_M a b ∣ a :=
by { rw gcd_M, split_ifs, exacts [dvd_rfl, rat_hom_le_iff_dvd.1 (le_of_not_le h)] }

lemma gcd_M_dvd_right (a b : M) : gcd_M a b ∣ b :=
by { rw gcd_M, split_ifs, exacts [rat_hom_le_iff_dvd.1 h, dvd_rfl] }

lemma dvd_gcd_M {a b c : M} (ha : c ∣ a) (hb : c ∣ b) : c ∣ gcd_M a b :=
by { rw gcd_M, split_ifs, exacts [ha, hb] }

open with_zero

instance gcd_with_zero_M : gcd_monoid (with_zero M) :=
begin
  classical, refine gcd_monoid_of_gcd (λ a b,
    if ha : a = 0 then b else if hb : b = 0 then a else gcd_M (unzero ha) (unzero hb)) _ _ _;
  intros a b, work_on_goal 3 { intros c hc hb }, all_goals { split_ifs with h1 h2 },
  { rw h1, apply dvd_zero },
  { exact dvd_rfl },
  { convert ← (with_zero.monoid_hom M).map_dvd (gcd_M_dvd_left _ _), apply coe_unzero },
  { exact dvd_rfl },
  { rw h2, apply dvd_zero },
  { convert ← (with_zero.monoid_hom M).map_dvd (gcd_M_dvd_right _ _), apply coe_unzero },
  { exact hb },
  { exact hc },
  { have := coe_unzero (ne_zero_of_dvd_ne_zero h1 hc),
    rw ← coe_unzero h1 at hc, rw ← coe_unzero h2 at hb,
    rw [← this, with_zero.coe_dvd_iff] at hb hc ⊢,
    exact dvd_gcd_M hc hb, },
end

section normalization_with_zero_M
variable [normalization_monoid (with_zero M)]

def M_mul_equiv_prod : M ≃* Mˣ × ↥(nnrat.to_submonoid ⊓ rat_hom.to_multiplicative.mrange) :=
(mul_equiv_of_left_splits _ _ (ker_mul_equiv_units_M.symm.to_monoid_hom.comp $ normalize_nonzero M)
begin
  show ∀ x : rat_hom.to_multiplicative.ker, _,
  intro x, conv_lhs
  { rw [← coe_to_units x, ← units.coe_map, monoid_hom.comp_apply, normalize_nonzero_splits] },
  cases x, refl,
end).trans $ ker_mul_equiv_units_M.prod_congr $ mul_equiv.refl _

def right_split_monoid_hom : ↥(nnrat.to_submonoid ⊓ rat_hom.to_multiplicative.mrange) →* M :=
M_mul_equiv_prod.symm.to_monoid_hom.comp $ monoid_hom.prod 1 $ monoid_hom.id _

lemma right_split (x) : rat_hom.to_multiplicative (right_split_monoid_hom x) = x :=
subtype.ext_iff.1 (prod.mk.inj_iff.1 $ M_mul_equiv_prod.apply_symm_apply (1, x)).2

def right_split_add_monoid_hom : ↥(nnrat ⊓ rat_hom.mrange) →+ ℕ →₀ ℤ :=
{ to_fun := λ x, multiplicative.to_add ↑(right_split_monoid_hom ⟨multiplicative.of_add ↑x, x.2⟩),
  map_zero' := by { simp_rw [add_submonoid.coe_zero, of_add_zero],
    erw right_split_monoid_hom.map_one, refl },
  map_add' := λ ⟨a, _⟩ ⟨b, _⟩, by { simp_rw [add_submonoid.coe_add, of_add_add],
    erw right_split_monoid_hom.map_mul, refl } }

lemma right_split_add (x) : rat_hom (right_split_add_monoid_hom x) = x := right_split ⟨x.1, _⟩

lemma not_normalization_M : false :=
begin
  have := congr_arg rat_hom (nnrat_inf_range_hom_finsupp_apply_seq_zero right_split_add_monoid_hom),
  rw [map_zero, right_split_add] at this, cases this,
end

end normalization_with_zero_M

lemma not_normalized_gcd_M [normalized_gcd_monoid (with_zero M)] : false := not_normalization_M
