/-
Copyright (c) 2019 Casper Putz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sander Dahmen, Casper Putz
-/

import algebra data.real.basic data.finset ring_theory.integral_closure ring_theory.polynomial
import field_theory.field_extension
import analysis.complex.exponential

universes u v

namespace valuation

/-- A *valued ring* is an integral domain `α` together with a valuation `val : α → ℝ`,
which is positive definite, multiplicative, and satisfies the (weak) triangle inequality. -/
class valued_ring (α : Type u) [integral_domain α] :=
(val : α → ℝ)
(nonneg : ∀ a, val a ≥ 0)
(definite : ∀ a, val a = 0 ↔ a = 0)
(val_mul : ∀ a b, val (a * b) = val a * val b)
(val_add : ∀ a b, val (a + b) ≤ val a + val b)

/-- A *nonarchimedian valued ring* is a valued ring satisfying the strong (i.e nonarchimedian)
triangle inequality. -/
class nonarch_valued_ring (α : Type u) [integral_domain α] extends valued_ring α :=
(nonarch : ∀ a b, val (a + b) ≤ max (val a) (val b))

section valued_ring

open valued_ring

section integral_domain

variables {α : Type u} [integral_domain α] [valued_ring α]

@[simp] lemma nonneg   : ∀ a : α, valued_ring.val a ≥ 0 := valued_ring.nonneg
@[simp] lemma definite : ∀ a : α, valued_ring.val a = 0 ↔ a = 0:= valued_ring.definite
@[simp] lemma val_mul  : ∀ a b : α, valued_ring.val (a * b) = valued_ring.val a * val b:= valued_ring.val_mul
@[simp] lemma val_add  : ∀ a b : α, valued_ring.val (a + b) ≤ valued_ring.val a + val b:= valued_ring.val_add

/-- Shows that the valuation of a nonzero element is nonzero. -/
lemma val_ne_zero {x : α} (h : x ≠ 0) : val x ≠ 0 := (mt (definite x).mp) h

/-- Shows that the valuation of a nonzero element is > 0. -/
lemma val_pos {x : α} (h : x ≠ 0) : val x > 0 := lt_of_le_of_ne (nonneg x) (ne.symm $ val_ne_zero h)

/-- Shows that the valuation of 0 equals 0. -/
lemma val_zero : val (0 : α) = 0 := by rw [definite]

/-- Shows that the valuation of 1 equals 1. -/
lemma val_one : val (1 : α) = 1 :=
have h : val (1 : α) * val (1 : α) = val (1 : α), by rw[←val_mul, mul_one],
(domain.mul_left_inj (val_ne_zero (one_ne_zero : (1 : α) ≠ 0))).mp (by rw [h, mul_one])

/-- Shows that the valuation of -1 equals -1. -/
lemma val_neg_one : val (-1 : α) = 1 :=
have val (-1 : α) * val (-1 : α) = 1, by rw[←val_mul, neg_one_mul, neg_neg, val_one],
or.resolve_right
  ((mul_self_eq_one_iff _).mp this)
  (ne_of_gt (lt_of_lt_of_le zero_gt_neg_one (nonneg (-1 : α))))

/-- Shows that the valuation of -x equals x. -/
lemma val_neg (x : α) : val (-x) = val x := by rw[←mul_neg_one, val_mul, val_neg_one, mul_one]

/-- Shows that the valuation of x^n equals the n-th power of the valuation of x. -/
lemma val_pow (x : α) (n : ℕ) : val (x^n) = (val x)^n :=
begin
  induction n,
  { rw [pow_zero, pow_zero, val_one] },
  { rw [pow_succ, pow_succ, val_mul, n_ih] }
end

end integral_domain

section field

variables {α : Type u} [discrete_field α] [valued_ring α]

/-- Shows that the valuation of the inverse is the inverse of the valuation. -/
lemma val_inv {x : α} (h : x ≠ 0) : valued_ring.val x⁻¹ = (valued_ring.val x)⁻¹ :=
begin
  apply eq_of_mul_eq_mul_right (val_ne_zero h),
  rw [inv_mul_cancel (val_ne_zero h), ←valued_ring.val_mul, inv_mul_cancel h, val_one]
end

/-- Shows that taking valuations and dividing by non-zero elements commutes -/
lemma val_div (x y : α) (hy : y ≠ 0) : val x / val y = val (x / y) :=
by rw [div_eq_mul_inv, div_eq_mul_inv, val_mul, val_inv hy]

end field

end valued_ring

section nonarch_valued_ring

open valued_ring

variables {α : Type u} [integral_domain α] [nonarch_valued_ring α]

lemma nonarch : ∀ a b : α, val (a + b) ≤ max (val a) (val b) := nonarch_valued_ring.nonarch

@[simp] lemma nonarch_or : ∀ a b : α, val (a + b) ≤ val a ∨ val (a + b) ≤ val b :=
λ a b, by rw [←le_max_iff]; exact nonarch a b

/-- The valuation of a sum is bounded by the maximum of the valuations. -/
lemma val_sum (s : multiset α) (b : ℝ) (hb : b ≥ 0) : (∀ x ∈ s, val x ≤ b) → val (multiset.sum s) ≤ b :=
multiset.induction_on s
  (λ _, by rw[multiset.sum_zero, val_zero]; exact hb)
  (assume x s h hs,
  have hbx : val x ≤ b, from hs x (multiset.mem_cons_self x s),
  have hbs : ∀ y ∈ s, val y ≤ b, from λ y hy, hs y (multiset.mem_cons_of_mem hy),
  calc val (multiset.sum (x :: s)) ≤ val (x + multiset.sum s)           : by rw [multiset.sum_cons]
                               ... ≤ max (val x) (val (multiset.sum s)) : nonarch x _
                               ... ≤ b                                  : max_le hbx (h hbs))

end nonarch_valued_ring

/-- The *valuation ring* of a nonarchimedien valued field is the subring of all
elements of valuation ≤ 1. -/
def valuation_ring (α : Type u) [discrete_field α] [nonarch_valued_ring α] : set α :=
    {x : α | valued_ring.val x ≤ 1}

section valuation_ring

open valued_ring

variables {α : Type u} [discrete_field α] [nonarch_valued_ring α]

lemma mem_def (x : α) : x ∈ valuation_ring α = (val x ≤ 1) := rfl

/-- The addition on a valuation ring. -/
def add : valuation_ring α → valuation_ring α → valuation_ring α
| ⟨x, hx⟩ ⟨y, hy⟩ := ⟨x+y,
    le_trans (nonarch_valued_ring.nonarch _ _) (max_le_iff.2 ⟨hx,hy⟩)⟩

/-- The multiplication on a valuation ring. -/
def mul : valuation_ring α → valuation_ring α → valuation_ring α
| ⟨x, hx⟩ ⟨y, hy⟩ := ⟨x*y,
  begin rw [mem_def, val_mul], apply mul_le_one; {assumption <|> apply nonneg} end⟩

/-- The subtraction on a valuation ring. -/
def neg : valuation_ring α → valuation_ring α
| ⟨x, hx⟩ := ⟨-x, by rw[mem_def, val_neg]; exact hx⟩

/-- The valuating ring is a subring -/
instance : is_subring (valuation_ring α) :=
{ zero_mem := by rw [mem_def, val_zero]; exact zero_le_one,
  one_mem := by rw [mem_def, val_one]; refl,
  add_mem := λ x y hx hy,
    by cases nonarch_or x y with h h;
    exact le_trans h (by assumption),
  neg_mem := λ x hx, by rw [mem_def] at ⊢ hx; rwa [val_neg],
  mul_mem := λ x y hx hy,
    by rw [mem_def] at ⊢ hx hy; rw [val_mul]; exact mul_le_one hx (nonneg _) hy }

lemma zero_def : ∀ x : valuation_ring α, x = 0 ↔ x.val = 0
| ⟨x, _⟩ := ⟨subtype.mk.inj, λ h, by simp at h; simp only [h]; refl⟩

@[simp] lemma add_def : ∀ (x y : valuation_ring α), (x+y).val = x.val + y.val
| ⟨x, hx⟩ ⟨y, hy⟩ := rfl

@[simp] lemma mul_def : ∀ (x y : valuation_ring α), (x*y).val = x.val * y.val
| ⟨x, hx⟩ ⟨y, hy⟩ := rfl

@[simp] lemma mk_zero {h} : (⟨0, h⟩ : valuation_ring α) = (0 : valuation_ring α) := rfl

/-- The valuation ring is itself a valued ring -/
instance : nonarch_valued_ring (valuation_ring α) :=
{ val := λ x, valued_ring.val (x : α),
  nonneg := λ x, valued_ring.nonneg x,
  definite := λ x, by rw[subtype.ext]; exact definite x,
  val_mul := λ x y, by rw [is_submonoid.coe_mul]; exact val_mul x y,
  val_add := λ x y, by rw [is_add_submonoid.coe_add]; exact val_add x y,
  nonarch := λ x y, nonarch x y }

/-- Shows that for x in a valued field, either x or x⁻¹ is in the valuation ring. -/
lemma mem_or_inv_mem (x : α) (h : x ≠ 0) : x ∈ valuation_ring α ∨ x⁻¹ ∈ valuation_ring α :=
suffices valued_ring.val x ≤ 1 ∨ valued_ring.val x⁻¹ < 1, from
  or.elim this (λ hr, or.inl hr) (λ hl, or.inr (le_of_lt hl)),
begin
  rw [val_inv h, inv_lt (val_pos h) zero_lt_one, inv_one],
  exact le_or_gt _ _
end

open polynomial valued_ring

/-- Shows that the valuation ring is integrally closed. -/
lemma integrally_closed (x : α) (hi : is_integral (valuation_ring α) x) : val x ≤ 1 :=
let ⟨p, hm, hp⟩ := hi in
begin
  -- We assume that val x > 1
	by_contradiction hnx,
  -- We have p(x) = 0 where p is some polynomial with integral coefficients
  change p.eval₂ subtype.val x = 0 at hp,
  let X : polynomial (valuation_ring α) := X,
  -- p and x are non-zero and therefore val x > 0
  have hp0 : p ≠ 0, from ne_zero_of_monic hm,
  have hx0 : x ≠ 0, from λ hx0, by rw [hx0, val_zero] at hnx; exact hnx zero_le_one,
  have hvx : 0 < val x, from val_pos (λ hn, by rw [hn, val_zero] at hnx; exact hnx zero_le_one),
  -- We have x^n = x^n - ∑_i^n a_i * x^i where p(X) = ∑_i^n a_i * X^i
  have h : val x^p.nat_degree = val ((X^p.nat_degree + -p).eval₂ subtype.val x),
    begin letI : is_ring_hom (subtype.val : valuation_ring α → α) := by apply_instance,
      rw [←val_pow, eval₂_add, eval₂_neg, hp, neg_zero, add_zero, eval₂_X_pow] end,
  -- Since p is monic we get x^n = -∑_i^{n-1} a_i * x^i. Since val a_i ≤ 1 for i = 1..n, we may
  -- conclude that val x^n ≤ val x^{n-1} using the strong triangle inequality
  have h1 : val x^p.nat_degree ≤ val x^p.nat_degree * (val x)⁻¹,
  begin
    conv_lhs { rw [h] },
    apply val_sum,
    { cases nat.eq_zero_or_pos p.nat_degree with _ h1,
      swap, rw [←zero_pow h1, zero_pow h1],
      repeat { rw [←val_inv hx0, ←val_pow, ←val_mul], exact nonneg _ } },
    { intros y hy,
      cases multiset.mem_map.mp hy with a ha,
      have hd : a + 1 ≤ p.nat_degree,
        begin
          rw [←finset.mem_def] at ha,
          have ha1 : a ∈ (X ^ nat_degree p + -p).support := ha.1,
          have hna : a ≠ p.nat_degree, from λ hna,
            begin
              rw [finsupp.mem_support_iff, hna] at ha1,
              change coeff (X ^ nat_degree p + -p) (nat_degree p) ≠ 0 at ha1,
              rw [monic.def] at hm,
              unfold leading_coeff at hm,
              rw [coeff_add, coeff_neg, coeff_X_pow, if_pos rfl, hm, add_neg_self] at ha1,
              contradiction
            end,
          have : a ≤ p.nat_degree, from with_bot.coe_le_coe.mp
          (calc ↑a ≤ (X^p.nat_degree - p).degree            : finset.le_sup ha1
                ... ≤ max (X^p.nat_degree).degree (-p).degree : degree_add_le _ _
                ... = max ↑p.nat_degree p.degree              : by rw [degree_X_pow, degree_neg]
                ... = ↑(p.nat_degree) : by rw [←degree_eq_nat_degree hp0, degree_eq_nat_degree hp0, max_self]),
          exact nat.succ_le_of_lt (lt_of_le_of_ne this hna)
        end,
      rw [←ha.2, val_mul, ←mul_le_mul_right hvx, mul_assoc, ←val_mul, ←pow_succ', mul_assoc,
          inv_mul_cancel (val_ne_zero hx0), mul_one],
      calc val (((X ^ nat_degree p - p).to_fun a).val) * val (x ^ (a + 1))
          ≤ val (x ^ (a + 1))    : mul_le_of_le_one_left (nonneg _) (((X ^ nat_degree p - p).to_fun a).property)
      ... ≤ val x ^ p.nat_degree : by rw [val_pow]; exact pow_le_pow (le_of_not_ge hnx) hd }
  end,
  rw [←mul_le_mul_right hvx, mul_assoc, inv_mul_cancel (val_ne_zero hx0), mul_one] at h1,
  have : val x ^ nat_degree p > 0, from
    lt_of_not_ge (λ hlt, begin
      rw [←val_pow] at hlt,
      have : val (x ^ nat_degree p) = 0, from le_antisymm hlt (nonneg _),
      rw [definite] at this,
      exact hx0 (pow_eq_zero this)
    end),
  -- We cancel (val x)^{n-1} on both sides to obtain val x ≤ 1
  have : val x ≤ 1, from (mul_le_iff_le_one_right this).mp h1,
  -- This contradicts the assumption that val x < 1
  contradiction
end

/-- The unique maximal ideal of the valuation ring. -/
def max_ideal (α : Type u) [discrete_field α] [nonarch_valued_ring α] : ideal (valuation_ring α) :=
{ carrier := { x | val x < 1 },
  zero := show val (0 : α) < 1, by rw [val_zero]; exact zero_lt_one,
  add := λ x y (hx : _ < 1) (hy : _ < 1),
    show val (x + y) < 1,
    by cases nonarch_or x y with h h; exact lt_of_le_of_lt h (by assumption),
  smul := λ c x (hx : _ < 1),
    show val (c * x) < 1,
    by rw [val_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right c.property (nonneg _) hx }

/-- The max_ideal is indeed a maximal ideal -/
lemma is_maximal : ideal.is_maximal (max_ideal α) :=
begin
 rw [ideal.is_maximal_iff],
 split,
 { exact λ (h : val 1 < 1), ne_of_lt h val_one},
 { rintros I ⟨x,_⟩ _ _ hxinI,
   have hv : val x = 1, by rw [eq_iff_le_not_lt]; split; assumption,
   have hx0 : x ≠ 0, by intro h; rw [h, val_zero] at hv; exact zero_ne_one hv,
   have hxinv : val x⁻¹ ≤ 1, by rw [val_inv hx0, hv, one_inv_eq],
   convert I.smul_mem ⟨x⁻¹, hxinv⟩ hxinI,
   symmetry,
   exact subtype.val_injective (inv_mul_cancel hx0) }
end

end valuation_ring

end valuation

namespace henselian

open valuation polynomial field_extension finite_dimensional

/-- A *henselian field* is a valued field `α` such that any irreducible polyomial
over this field . -/
class henselian_field (α : Type u) [discrete_field α] [valued_ring α] :=
(henselian : ∀ p : polynomial α, irreducible p →
  ∀ k ≤ nat_degree p, valued_ring.val (p.coeff k) ≤ max (valued_ring.val (p.coeff 0)) (valued_ring.val (p.leading_coeff)))

section
variables {α : Type u} [discrete_field α] [nonarch_valued_ring α] [henselian_field α]

lemma integral_coeffs (p : polynomial α) (hp : irreducible p) (hm : monic p)
  (h0 : valued_ring.val (p.coeff 0) ≤ 1) : ∀ n, valued_ring.val (p.coeff n) ≤ 1 :=
λ k, or.elim (le_or_gt ↑k (degree p))
	(λ hk, begin
		rw[degree_eq_nat_degree (ne_zero_of_irreducible hp), with_bot.coe_le_coe] at hk,
		have h : valued_ring.val (p.coeff k) ≤
			max (valued_ring.val (p.coeff 0)) (valued_ring.val (p.leading_coeff)),
			from henselian_field.henselian p hp k hk,
		rwa [monic.def.mp hm, val_one, max_eq_right h0] at h
	end)
	(λ hk, by	rw [coeff_eq_zero_of_degree_lt hk, val_zero]; exact zero_le_one)

end

variables (α : Type u) [discrete_field α] [nonarch_valued_ring α] [henselian_field α]
variables {β : Type v} [discrete_field β] [field_extension α β] [finite_dimensional α β]

-- TODO: move
lemma rpow_zero_iff {x y : ℝ} (hx : x ≥ 0) (hy : y ≠ 0) : x ^ y = 0 ↔ x = 0 :=
⟨λ h, by { rw [←real.rpow_one x, ←mul_inv_cancel hy, real.rpow_mul hx, h],
  exact real.zero_rpow (inv_ne_zero hy) },
λ h, by { rw [h], exact real.zero_rpow hy }⟩

-- TODO
lemma findim_ne_zero : findim α β ≠ 0 := sorry

/-- The weak triangle inequality follows from the strong triangle inequality -/
lemma weak_triangle_of_nonarch {α : Type u} [discrete_field α] (f : α → ℝ) (h0 : ∀ a, f a ≥ 0)
  (h : ∀ a b : α, f (a + b) ≤ f a ∨ f (a + b) ≤ f b) :
  ∀ a b : α, f (a + b) ≤ f a + f b :=
begin
  intros a b,
  cases h a b,
  { transitivity (f a), assumption, exact le_add_of_nonneg_right (h0 _)},
  { transitivity (f b), assumption, exact le_add_of_nonneg_left (h0 _)},
end

noncomputable def val_ext : β → ℝ := λ b, (valued_ring.val (field_norm α b)) ^ (1 / findim α β : ℝ)

lemma val_ext_nonneg (b : β) : val_ext α b ≥ 0 := real.rpow_nonneg_of_nonneg (nonneg _) _

lemma val_ext_definite (b : β) : val_ext α b = 0 ↔ b = 0 :=
begin
  have : (1 / findim α β : ℝ) ≠ 0, from
    by { rw [←inv_eq_one_div], refine inv_ne_zero _, norm_cast, exact findim_ne_zero α },
  unfold val_ext,
  rw [rpow_zero_iff (nonneg _) this, definite, norm_zero_iff_zero]
end

lemma val_ext_mul (b c : β) : val_ext α (b * c) = val_ext α b * val_ext α c :=
by { unfold val_ext, rw [norm_mul, val_mul, real.mul_rpow (nonneg _) (nonneg _)] }

lemma val_ext_one : val_ext α (1 : β) = 1 :=
by { unfold val_ext, rw [norm_one, val_one, real.one_rpow] }

lemma val_ext_inv {b : β} (h : b ≠ 0) : val_ext α b⁻¹ = (val_ext α b)⁻¹ :=
begin
  apply eq_of_mul_eq_mul_right (mt (val_ext_definite α b).mp h),
  rw [inv_mul_cancel (mt (val_ext_definite α b).mp h), ←val_ext_mul, inv_mul_cancel h, val_ext_one]
end

lemma val_ext_div (b : β) {c : β} (h : c ≠ 0) : val_ext α (b / c) = val_ext α b / val_ext α c :=
by rw [div_eq_mul_inv, div_eq_mul_inv, ←val_ext_inv _ h, val_ext_mul]

lemma max_div (x y : ℝ) {z : ℝ} (hz : z > 0) : (max x y) / z = max (x / z) (y / z) := sorry

lemma test1 (b : β) : val_ext α b ≤ 1 ↔ valued_ring.val (field_norm α b) ≤ 1 := sorry

noncomputable instance extend_valuation : nonarch_valued_ring β :=
{ val := val_ext α,
  nonneg := val_ext_nonneg α,
  definite := val_ext_definite α,
  val_mul := val_ext_mul α,
  nonarch := λ a b,
  suffices h : ∀ c : β, val_ext α c ≤ 1 → val_ext α (c + 1) ≤ max (val_ext α c) 1, from
  begin
    by_cases hb : b = 0,
    { rw [hb, val_zero, add_zero], exact le_max_left _ _ },
    { have : val_ext α b ≠ 0, by rwa [ne.def, val_ext_definite α],
      have hb0 : val_ext α b > 0, from lt_of_le_of_ne (val_ext_nonneg α _) (ne.symm this),
      rw [←div_le_div_right hb0, val_div, max_div _ _ hb0, val_div, val_div],
      rw [add_div, div_self hb, val_one],
      have : val_ext α a ≤ val_ext α b, from sorry, --wlog
      have hc : val_ext α (a / b) ≤ 1, by rwa [val_ext_div α _ hb, div_le_one_iff_le hb0],
      exact h (a / b) hc,
      assumption' }
  end,
  begin
    intros c hc,
    rw [max_eq_right hc],
    rw [test1, ←valuation.mem_def] at hc ⊢,

    -- Construct the integral closure of valuation_ring α in β
    letI : algebra (valuation_ring α) β := algebra.comap.algebra (valuation_ring α) α β,
    let O := integral_closure (valuation_ring α) β,
    -- O is the inverse image of the valuation ring of α under the norm map
    --TODO: make this a seperate lemma
    have hO : O.carrier = set.preimage (field_norm α) (valuation_ring α),
    { ext x,
      rw [set.mem_preimage],
      split,
      { intro hx,
        sorry },
      { intro hx,
        --change is_integral (valuation_ring α) x,
        -- Minimal polynomial of x over α
        have hb : ∃ f : polynomial α, irreducible f ∧ (monic f ∧ aeval α β x f = 0), from sorry,
        cases hb with f hf,
        -- follows from henselian_field.henselian, field norms and minimal polynomials
        have : valued_ring.val (f.coeff 0) ≤ 1, from sorry,
        have h : ∀ n : ℕ, valued_ring.val (f.coeff n) ≤ 1, from integral_coeffs f hf.1 hf.2.1 this,
        have hr : ↑(finsupp.frange f) ⊆ valuation_ring α, from
          λ _ hy, let ⟨n, hn⟩ := (finsupp.mem_frange.mp hy).2 in hn ▸ h n,
        let fo := f.to_subring (valuation_ring α) hr,
        existsi fo,
        split,
        { exact (monic_to_subring _ _ _).mpr hf.2.1 },
        { rw [←hf.2.2],
          exact eq.symm (to_subring_eval₂ f (valuation_ring α) hr _ x) } } },
    rw [←set.mem_preimage, ←hO] at hc ⊢,
    exact is_add_submonoid.add_mem hc (is_submonoid.one_mem _)
  end,
  val_add := sorry,
}



end henselian
