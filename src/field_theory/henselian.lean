/-
Copyright (c) 2019 Casper Putz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sander Dahmen, Casper Putz
-/

import algebra data.real.basic data.finset
import ring_theory.integral_closure ring_theory.polynomial ring_theory.adjoin_root
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

/-- The valuation of the inverse of a unit is the inverse of its valuation. -/
lemma val_inv_unit (u : units α) : val (u.inv : α) = (val (u : α))⁻¹ :=
eq_of_mul_eq_mul_left (val_ne_zero $ units.ne_zero u)
(calc val ↑u * val (u.inv) = val (↑u * u.inv)    : eq.symm $ val_mul _ _
                       ... = val (1 : α)         : congr_arg _ u.mul_inv
                       ... = 1                   : val_one
                       ... = val ↑u * (val ↑u)⁻¹ : eq.symm $ mul_inv_cancel $ val_ne_zero $ units.ne_zero u)

end integral_domain

section field

variables {α : Type u} [discrete_field α] [valued_ring α]

/-- The valuation of the inverse is the inverse of the valuation. -/
lemma val_inv {x : α} (h : x ≠ 0) : valued_ring.val x⁻¹ = (valued_ring.val x)⁻¹ :=
by rw [←units.mk0_val h, ←val_inv_unit]; refl

/-- Taking valuations and dividing by non-zero elements commutes -/
lemma val_div (x y : α) (hy : y ≠ 0) : val (x / y) = val x / val y :=
by rw [div_eq_mul_inv, div_eq_mul_inv, val_mul, val_inv hy]

end field

end valued_ring

section nonarch_valued_ring

open valued_ring

variables {α : Type u} [integral_domain α] [nonarch_valued_ring α]

lemma nonarch : ∀ a b : α, val (a + b) ≤ max (val a) (val b) := nonarch_valued_ring.nonarch

@[simp] lemma nonarch_or : ∀ a b : α, val (a + b) ≤ val a ∨ val (a + b) ≤ val b :=
λ a b, by rw [←le_max_iff]; exact nonarch a b

--TODO: should use finset.sup (but then val should land in a lattice.semilattice_sup_bot)
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

example {p : polynomial α} {a : ℕ} (h : a ∈ ((p - X ^ nat_degree p).support).val) (hp0 : p ≠ 0) (hm : monic p) :
  a + 1 ≤ p.nat_degree := nat.succ_le_of_lt (by { rw [←with_bot.coe_lt_coe, ←degree_eq_nat_degree hp0],
    refine lt_of_le_of_lt (_ : ↑a ≤ degree (p - X ^ nat_degree p)) _,
    { exact le_degree_of_ne_zero (finsupp.mem_support_iff.mp $ finset.mem_def.mpr h) },
    { refine degree_sub_lt _ hp0 _,
      rw [degree_X_pow, degree_eq_nat_degree hp0],
      rw [leading_coeff_X_pow], exact hm } })

/-- The valuation ring is integrally closed. -/
lemma integrally_closed {x : α} (hi : is_integral (valuation_ring α) x) : val x ≤ 1 :=
begin
  rcases hi with ⟨p, hm, hp⟩,
  -- We assume that val x > 1
	by_contradiction hnx,
  -- We have p(x) = 0 where p is some polynomial with integral coefficients
  change p.eval₂ subtype.val x = 0 at hp,
  -- p and x are non-zero and therefore val x > 0
  have hp0 : p ≠ 0, from ne_zero_of_monic hm,
  have hx0 : x ≠ 0, { intro hx0, rw [hx0, val_zero] at hnx, exact hnx zero_le_one },
  have hvx : 0 < val x, from val_pos hx0,
  -- We have val x^n = val (p(x) - x^n) since p(x) = 0
  have h : val x^p.nat_degree = val ((p - X^p.nat_degree).eval₂ subtype.val x),
  { letI : is_ring_hom (subtype.val : valuation_ring α → α) := by apply_instance,
    rw [←val_pow, eval₂_sub, hp, zero_sub, val_neg, eval₂_X_pow] },
  -- Since p is monic we get x^n = -∑_i^{n-1} a_i * x^i. Since val a_i ≤ 1 for i = 1..n, we may
  -- conclude that val x^n ≤ val x^{n-1} using the strong triangle inequality
  have h1 : val x^p.nat_degree ≤ val x^p.nat_degree * (val x)⁻¹,
  { conv_lhs { rw [h] },
    apply val_sum,
    { cases nat.eq_zero_or_pos p.nat_degree with _ h1,
      swap, rw [←zero_pow h1, zero_pow h1],
      repeat { rw [←val_inv hx0, ←val_pow, ←val_mul], exact nonneg _ } },
    { intros y hy,
      cases multiset.mem_map.mp hy with a ha,
      have hd : a + 1 ≤ p.nat_degree,
      { apply nat.succ_le_of_lt,
        rw [←with_bot.coe_lt_coe, ←degree_eq_nat_degree hp0],
        refine lt_of_le_of_lt (_ : ↑a ≤ degree (p - X^p.nat_degree)) _,
        { exact le_degree_of_ne_zero (finsupp.mem_support_iff.mp $ finset.mem_def.mpr ha.1) },
        { refine degree_sub_lt _ hp0 _,
          rw [degree_X_pow, degree_eq_nat_degree hp0],
          rw [leading_coeff_X_pow], exact hm } },
      rw [←ha.2, val_mul, ←mul_le_mul_right hvx, mul_assoc, ←val_mul, ←pow_succ', mul_assoc,
        inv_mul_cancel (val_ne_zero hx0), mul_one],
      calc val (((p - X ^ nat_degree p).to_fun a).val) * val (x ^ (a + 1))
          ≤ val (x ^ (a + 1))    : mul_le_of_le_one_left (nonneg _) (((p - X ^ nat_degree p).to_fun a).property)
      ... ≤ val x ^ p.nat_degree : by { rw [val_pow], exact pow_le_pow (le_of_not_ge hnx) hd } } },
  rw [←mul_le_mul_right hvx, mul_assoc, inv_mul_cancel (val_ne_zero hx0), mul_one] at h1,
  have hpos : (val x) ^ p.nat_degree > 0,
  { rw [←real.rpow_nat_cast], exact real.rpow_pos_of_pos hvx _ },
  -- We cancel (val x)^{n-1} on both sides to obtain val x ≤ 1
  have : val x ≤ 1, from (mul_le_iff_le_one_right hpos).mp h1,
  -- This contradicts the assumption that val x > 1
  contradiction
end

open field_extension
--hint
instance {β : Type*} [discrete_field β] [field_extension α β] : algebra (valuation_ring α) β :=
algebra.comap.algebra (valuation_ring α) α β

--TODO: lemma is wrong, put power in there
lemma minimal_polynomial.constant_eq {β : Type*} [discrete_field β] [field_extension α β] [finite_dimensional α β]
  {x : β} (hx : is_integral α x) : (minimal_polynomial hx).coeff 0 = (field_norm α x) ^ 2 := sorry

/-- The valuation ring is integrally closed. -/
lemma integrally_closed' {β : Type*} [discrete_field β] [field_extension α β] [finite_dimensional α β]
  {x : β} (hx : is_integral (valuation_ring α) x) : val (field_norm α x) ≤ 1 :=
begin
  have hiα : is_integral α x, from is_integral_of_noetherian' (by apply_instance) x,
  let f := minimal_polynomial hiα,
  have hm : (minimal_polynomial hx).of_subring (valuation_ring α) = f,
  { refine minimal_polynomial.unique _ _ (minimal_polynomial.aeval hx) _,
    { rw [monic_of_subring], exact minimal_polynomial.monic hx },
    { intros q hqm hq0, rw [degree_of_subring], rw [←degree_to_subring q (valuation_ring α)],
      refine minimal_polynomial.min hx _ hq0, sorry, sorry } },
  have h0 : f.coeff 0 ∈ valuation_ring α,
  { rw [←hm, of_subring], simp only [subtype.val_prop, polynomial.coeff_mk] },
  exact calc valued_ring.val (field_norm α x)
    = ((valued_ring.val (field_norm α x))^2) ^ (1/2 : ℝ) :
      by { rw [←real.rpow_nat_cast, ←real.rpow_mul (nonneg _)], norm_num }
  ... = (valued_ring.val ((field_norm α x)^2)) ^ (1/2 : ℝ) : by rw [val_pow]
  ... ≤ 1 ^ (1/2 : ℝ) : real.rpow_le_rpow (nonneg _) (minimal_polynomial.constant_eq hiα ▸ h0) (by norm_num)
  ... = 1             : by norm_num
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
		rw[degree_eq_nat_degree (ne_zero_of_monic hm), with_bot.coe_le_coe] at hk,
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

lemma val_ext_zero : val_ext α (0 : β) = 0 := sorry

--hint
instance : algebra (valuation_ring α) β := algebra.comap.algebra (valuation_ring α) α β

/-noncomputable instance {x : β} (hx : is_integral α x) :
  discrete_field (adjoin_root (minimal_polynomial hx)) :=
{..@adjoin_root.field α _ _ (minimal_polynomial.irreducible hx) }-/

--TODO: move
/-- The integral closure of the valuation ring of `α` in `β` is equal to the preimage of the
valuation ring of `α` under norm map from `α` to `β`. -/
lemma integral_closure_valuation_ring (β : Type v) [discrete_field β] [field_extension α β] [finite_dimensional α β] :
  (integral_closure (valuation_ring α) β).carrier = set.preimage (field_norm α) (valuation_ring α) :=
begin
  ext x,
  rw [set.mem_preimage],
  have hiα : is_integral α x, from is_integral_of_noetherian' (by apply_instance) x,
  let f := minimal_polynomial hiα,
  split,
  { intro hx,
    -- The minimal polynomial of x over α is equal to its minimal polynomial over the valuation ring of α
    have hm : (minimal_polynomial hx).of_subring (valuation_ring α) = f,
    { refine minimal_polynomial.unique _ _ (minimal_polynomial.aeval hx) _,
      { rw [monic_of_subring], exact minimal_polynomial.monic hx },
      { intros q hqm hq0, rw [degree_of_subring], rw [←degree_to_subring q (valuation_ring α)],
        refine minimal_polynomial.min hx _ hq0, sorry, sorry } },
    have h0 : f.coeff 0 ∈ valuation_ring α,
    { rw [←hm, of_subring], simp only [subtype.val_prop, polynomial.coeff_mk] },
    exact calc valued_ring.val (field_norm α x)
      = ((valued_ring.val (field_norm α x))^2) ^ (1/2 : ℝ) :
        by { rw [←real.rpow_nat_cast, ←real.rpow_mul (nonneg _)], norm_num }
  ... = (valued_ring.val ((field_norm α x)^2)) ^ (1/2 : ℝ) : by rw [val_pow]
  ... ≤ 1 ^ (1/2 : ℝ) : real.rpow_le_rpow (nonneg _) (minimal_polynomial.constant_eq hiα ▸ h0) (by norm_num)
  ... = 1             : by norm_num },
  { intro hx,
    have : valued_ring.val (f.coeff 0) ≤ 1, from
    calc valued_ring.val (f.coeff 0)
      = valued_ring.val ((field_norm α x) ^ 2) : congr_arg _ $ minimal_polynomial.constant_eq _
  ... = (valued_ring.val $ field_norm α x) ^ 2 : val_pow _ _
  ... ≤ 1 ^ 2 : pow_le_pow_of_le_left (nonneg _) hx 2
  ... = 1 : by norm_num,
    have h : ∀ n : ℕ, valued_ring.val (f.coeff n) ≤ 1,
    { apply integral_coeffs f (minimal_polynomial.irreducible hiα) (minimal_polynomial.monic hiα),
      exact this },
    have hr : ↑(finsupp.frange f) ⊆ valuation_ring α, from
      λ _ hy, let ⟨n, hn⟩ := (finsupp.mem_frange.mp hy).2 in hn ▸ h n,
    let fo := f.to_subring (valuation_ring α) hr,
    existsi fo,
    split,
    { exact (monic_to_subring _ _ _).mpr (minimal_polynomial.monic hiα) },
    { rw [←minimal_polynomial.aeval hiα],
      exact eq.symm (to_subring_eval₂ f (valuation_ring α) hr _ x) } }
end

lemma val_ext_nonarch (a b : β) : val_ext α (a + b) ≤ max (val_ext α a) (val_ext α b) :=
suffices h : ∀ c : β, val_ext α c ≤ 1 → val_ext α (c + 1) ≤ 1, begin
  by_cases hb : b = 0,
  { rw [hb, val_ext_zero, add_zero], exact le_max_left _ _ },
  { wlog h : val_ext α a ≤ val_ext α b using a b,
    { have : val_ext α b ≠ 0, by rwa [ne.def, val_ext_definite α],
      have hb0 : val_ext α b > 0, from lt_of_le_of_ne (val_ext_nonneg α _) (ne.symm this),
      have hc : val_ext α (a / b) ≤ 1, by rwa [val_ext_div α _ hb, div_le_one_iff_le hb0],
      rw [←div_le_div_right hb0, ←val_ext_div, max_div _ _ hb0, ←val_ext_div, ←val_ext_div],
      rw [add_div, div_self hb, val_ext_one, max_eq_right hc],
      exact h (a / b) hc,
      assumption' },
    { by_cases ha : a = 0, { rw [ha, val_ext_zero, zero_add], exact le_max_right _ _ },
      rw [add_comm, max_comm],
      exact this ha } }
end,
begin
  intros c hc,
  rw [test1, ←valuation.mem_def, ←set.mem_preimage, ←integral_closure_valuation_ring] at hc ⊢,
  letI : algebra (valuation_ring α) β := algebra.comap.algebra (valuation_ring α) α β, --hint
  exact is_add_submonoid.add_mem hc (is_submonoid.one_mem _)
end

noncomputable instance extend_valuation : nonarch_valued_ring β :=
{ val := val_ext α,
  nonneg := val_ext_nonneg α,
  definite := val_ext_definite α,
  val_mul := val_ext_mul α,
  nonarch := val_ext_nonarch α,
  val_add := λ a b, begin
    cases le_max_iff.mp (val_ext_nonarch α a b),
    { transitivity (val_ext α a), assumption, exact le_add_of_nonneg_right (val_ext_nonneg α _)},
    { transitivity (val_ext α b), assumption, exact le_add_of_nonneg_left  (val_ext_nonneg α _)},
  end
}



end henselian
