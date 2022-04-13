/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import ring_theory.valuation.valuation_ring
import ring_theory.localization.as_subring
import algebraic_geometry.prime_spectrum.basic

/-!

# Valuation subrings of a field

# Projects

The order structure on `valuation_subring K`.

-/

variables (K : Type*) [field K]

/-- A valuation subring of a field `K` is a subring `A` such that for every `x : K`,
either `x ∈ A` or `x⁻¹ ∈ K`. -/
structure valuation_subring extends subring K :=
(mem_or_inv_mem' : ∀ x : K, x ∈ carrier ∨ x⁻¹ ∈ carrier)

namespace valuation_subring

variables {K} (A : valuation_subring K)

instance : set_like (valuation_subring K) K :=
{ coe := λ A, A.to_subring,
  coe_injective' := begin
    intros A B h,
    cases A, cases B, congr, apply set_like.ext,
    exact set.ext_iff.mp h,
  end }

@[simp] lemma mem_carrier (x : K) : x ∈ A.carrier ↔ x ∈ A := iff.refl _
@[simp] lemma mem_to_subring (x : K) : x ∈ A.to_subring ↔ x ∈ A := iff.refl _

@[ext] lemma ext (A B : valuation_subring K)
  (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B := set_like.ext h

lemma mem_or_inv_mem (x : K) : x ∈ A ∨ x⁻¹ ∈ A := A.mem_or_inv_mem' _

instance : comm_ring A := show comm_ring A.to_subring, by apply_instance
instance : is_domain A := show is_domain A.to_subring, by apply_instance

instance : has_top (valuation_subring K) := has_top.mk $
{ mem_or_inv_mem' := λ x, or.inl trivial,
  ..(⊤ : subring K) }

lemma mem_top (x : K) : x ∈ (⊤ : valuation_subring K) := trivial

lemma le_top : A ≤ ⊤ := λ a ha, mem_top _

instance : order_top (valuation_subring K) :=
{ top := ⊤,
  le_top := le_top }

instance : inhabited (valuation_subring K) := ⟨⊤⟩

instance : valuation_ring A :=
begin
  constructor,
  intros a b,
  by_cases (b : K) = 0, { use 0, left, rw mul_zero, exact_mod_cast h.symm },
  by_cases (a : K) = 0, { use 0, right, rw mul_zero, exact_mod_cast h.symm },
  cases A.mem_or_inv_mem (a/b) with hh hh,
  { use ⟨a/b,hh⟩, right, apply subtype.ext, field_simp, ring },
  { rw (show ((a : K)/b)⁻¹ = b/a, by field_simp) at hh,
    use ⟨b/a,hh⟩, left, apply subtype.ext, field_simp, ring }
end

instance : algebra A K :=
show algebra A.to_subring K, by apply_instance

@[simp]
lemma algebra_map_apply (a : A) : algebra_map A K a = a := rfl

instance : is_fraction_ring A K :=
{ map_units := λ ⟨y,hy⟩,
    (units.mk0 (y : K)
      (λ c, non_zero_divisors.ne_zero hy (by exact_mod_cast c))).is_unit,
  surj := begin
    intros z,
    by_cases z = 0, { use (0,1), simp [h] },
    cases A.mem_or_inv_mem z with hh hh,
    { use (⟨z,hh⟩,1), simp },
    { refine ⟨⟨1,⟨⟨_,hh⟩,_⟩⟩,_⟩,
      { rw mem_non_zero_divisors_iff_ne_zero,
        intro c, apply h,
        exact inv_eq_zero.mp (congr_arg coe c) },
      { dsimp, exact mul_inv_cancel h } }
  end,
  eq_iff_exists := begin
    intros a b,
    dsimp,
    split,
    { intro h, use 1, simp only [submonoid.coe_one, mul_one], exact_mod_cast h },
    { rintro ⟨c,h⟩,
      simp only [mul_eq_mul_right_iff] at h,
      cases h,
      { exact_mod_cast h },
      { exact false.elim (non_zero_divisors.ne_zero c.2 h) } },
  end }

/-- Any valuation subring of `K` induces a natural valuation on `K`. -/
def valuation := valuation_ring.valuation A K

lemma valuation_le_one (a : A) : A.valuation a ≤ 1 :=
begin
  change (a : K) ∈ A.valuation.integer,
  erw valuation_ring.mem_integer_iff,
  use a, refl,
end

lemma mem_of_valuation_le_one (x : K) : A.valuation x ≤ 1 → x ∈ A :=
begin
  rintro (h : x ∈ A.valuation.integer),
  erw valuation_ring.mem_integer_iff at h,
  obtain ⟨a,ha⟩ := h,
  rw ← ha, exact a.2,
end

lemma valuation_le_one_iff (x : K) : A.valuation x ≤ 1 ↔ x ∈ A :=
⟨mem_of_valuation_le_one _ _, λ ha, A.valuation_le_one ⟨x,ha⟩⟩

lemma valuation_eq_iff (x y : K) : A.valuation x = A.valuation y ↔
  ∃ a : Aˣ, (a : K) * y = x :=
begin
  change quotient.mk' _ = quotient.mk' _ ↔ _,
  rw quotient.eq', apply iff.refl,
end

lemma valuation_le_iff (x y : K) : A.valuation x ≤ A.valuation y ↔
  ∃ a : A, (a : K) * y = x := iff.rfl

lemma valuation_surjective : function.surjective A.valuation := surjective_quot_mk _

lemma valuation_unit (a : Aˣ) : A.valuation a = 1 :=
begin
  rw [← A.valuation.map_one, valuation_eq_iff],
  use a, simp,
end

lemma valuation_eq_one_iff (a : A) : is_unit a ↔ A.valuation a = 1 :=
begin
  split,
  { intros h, exact A.valuation_unit h.unit, },
  { intros h,
    have ha : (a : K) ≠ 0,
    { intro c, rw [c, A.valuation.map_zero] at h, exact zero_ne_one h },
    have ha' : (a : K)⁻¹ ∈ A,
    { rw [← valuation_le_one_iff, A.valuation.map_inv, h, inv_one] },
    use [a, a⁻¹, ha'],
    { ext, field_simp },
    { ext, field_simp },
    { ext, refl } }
end

lemma valuation_lt_one_or_eq_one (a : A) : A.valuation a < 1 ∨ A.valuation a = 1 :=
lt_or_eq_of_le (A.valuation_le_one a)

lemma valuation_lt_one_iff (a : A) : a ∈ local_ring.maximal_ideal A ↔ A.valuation a < 1 :=
begin
  rw local_ring.mem_maximal_ideal,
  dsimp [nonunits], rw valuation_eq_one_iff,
  cases A.valuation_lt_one_or_eq_one a; split,
  { intro _, exact h },
  { intro _, exact ne_of_lt h },
  { contradiction },
  { intros hh c, exact ne_of_lt hh c }
end

/-- A subring `R` of `K` such that for all `x : K` either `x ∈ R` or `x⁻¹ ∈ R` is
  a valuation subring of `K`. -/
def of_subring (R : subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) : valuation_subring K :=
{ mem_or_inv_mem' := hR, ..R }

@[simp]
lemma mem_of_subring (R : subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) (x : K) :
  x ∈ of_subring R hR ↔ x ∈ R := iff.refl _

def of_le (R : valuation_subring K) (S : subring K) (h : R.to_subring ≤ S) :
  valuation_subring K :=
{ mem_or_inv_mem' := begin
    intros x, cases R.mem_or_inv_mem x with hx hx,
    { left, exact h hx, },
    { right, exact h hx, },
  end, ..S}

section order

instance : semilattice_sup (valuation_subring K) :=
{ sup := λ R S, of_le R (R.to_subring ⊔ S.to_subring) $ le_sup_left,
  le_sup_left := λ R S x hx, (le_sup_left : R.to_subring ≤ R.to_subring ⊔ S.to_subring) hx,
  le_sup_right := λ R S x hx, (le_sup_right : S.to_subring ≤ R.to_subring ⊔ S.to_subring) hx,
  sup_le := λ R S T hR hT x hx, (sup_le hR hT : R.to_subring ⊔ S.to_subring ≤ T.to_subring) hx,
  ..(infer_instance : partial_order (valuation_subring K)) }

def ideal_of_le (R S : valuation_subring K) (h : R ≤ S) : ideal R :=
{ carrier := { r | S.valuation r < 1 },
  add_mem' := begin
    rintros a b (ha : S.valuation _ < _) (hb : S.valuation _ < _ ),
    have hu := S.valuation.map_add a b,
    refine lt_of_le_of_lt hu _,
    exact max_lt ha hb,
  end,
  zero_mem' := by { dsimp, rw S.valuation.map_zero, exact zero_lt_one₀ },
  smul_mem' := begin
    rintros c a (ha : S.valuation _ < _), rw smul_eq_mul,
    let t : S := ⟨c, h c.2⟩,
    change S.valuation (c * a) < _,
    rw S.valuation.map_mul,
    refine lt_of_le_of_lt _ ha,
    refine mul_le_of_le_one_left' _,
    rw S.valuation_le_one_iff,
    exact h c.2
  end }

instance prime_ideal_of_le (R S : valuation_subring K) (h : R ≤ S) :
  (ideal_of_le R S h).is_prime :=
begin
  constructor,
  { rw ideal.ne_top_iff_one, rintro (c : S.valuation _ < _),
    push_cast at c, rw S.valuation.map_one at c, exact ne_of_lt c rfl },
  { rintros x y (hh : S.valuation _ < _), push_cast at hh,
    rw S.valuation.map_mul at hh,
    by_cases hx : S.valuation x < 1, { exact or.inl hx },
    right,
    have : S.valuation x = 1,
    { cases S.valuation_lt_one_or_eq_one ⟨x, h x.2⟩ with h1 h1,
      { contradiction },
      { assumption } },
    { rwa [this, one_mul] at hh, } }
end

def of_prime (A : valuation_subring K) (P : ideal A) [hP : P.is_prime] :
  valuation_subring K :=
of_le A (localization.subring K P.prime_compl $
  le_non_zero_divisors_of_no_zero_divisors $ not_not_intro P.zero_mem)
begin
  rintros a ha,
  refine ⟨⟨a, ha⟩, 1, P.prime_compl.one_mem, by simp⟩,
end

lemma le_of_prime (A : valuation_subring K) (P : ideal A) [hP : P.is_prime] :
  A ≤ of_prime A P :=
begin
  intros a ha,
  refine ⟨⟨a, ha⟩, 1, P.prime_compl.one_mem, by simp⟩,
end

@[simp]
lemma ideal_of_le_of_prime (A : valuation_subring K) (P : ideal A) [hP : P.is_prime] :
  ideal_of_le A (of_prime A P) (le_of_prime A P) = P :=
sorry

@[simp]
lemma of_prime_ideal_of_le (R S : valuation_subring K) (h : R ≤ S) :
  of_prime R (ideal_of_le R S h) = S :=
sorry

def prime_spectrum_equiv :
  prime_spectrum A ≃ { S | A ≤ S } :=
{ to_fun := λ P, ⟨of_prime A P.as_ideal, le_of_prime _ _⟩,
  inv_fun := λ S, ⟨ideal_of_le _ S S.2, infer_instance⟩,
  left_inv := λ P, by { ext1, simpa },
  right_inv := λ S, by { ext1, simp } }

end order

end valuation_subring
