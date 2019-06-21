/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import data.finsupp order.complete_lattice algebra.ordered_group data.mv_polynomial

namespace finsupp
open lattice
variables {σ : Type*} {α : Type*} [decidable_eq σ]

instance [preorder α] [has_zero α] : preorder (σ →₀ α) :=
{ le := λ f g, ∀ s, f s ≤ g s,
  le_refl := λ f s, le_refl _,
  le_trans := λ f g h Hfg Hgh s, le_trans (Hfg s) (Hgh s) }

instance [partial_order α] [has_zero α] : partial_order (σ →₀ α) :=
{ le_antisymm := λ f g hfg hgf, finsupp.ext $ λ s, le_antisymm (hfg s) (hgf s),
  .. finsupp.preorder }

instance [canonically_ordered_monoid α] : order_bot (σ →₀ α) :=
{ bot := 0,
  bot_le := λ f s, zero_le _,
  .. finsupp.partial_order }

lemma le_iff [canonically_ordered_monoid α] (f g : σ →₀ α) :
  f ≤ g ↔ ∀ s ∈ f.support, f s ≤ g s :=
⟨λ h s hs, h s,
λ h s, if H : s ∈ f.support then h s H else (not_mem_support_iff.1 H).symm ▸ zero_le (g s)⟩

def nat_downset (f : σ →₀ ℕ) : finset (σ →₀ ℕ) :=
(f.support.pi (λ x, finset.range $ f x + 1)).image $
λ g, f.support.attach.sum $ λ i, finsupp.single i.1 $ g i.1 i.2

@[simp] lemma nat_downset_zero : nat_downset (0 : σ →₀ ℕ) = {0} :=
begin
  sorry
end

theorem sum_apply' [decidable_eq α] [add_comm_monoid α] {β : Type*} {f : β → σ →₀ α} {ι : finset β} {i : σ} :
  ι.sum f i = ι.sum (λ x, f x i) :=
by classical; exact finset.induction_on ι rfl (λ x s hxs ih,
by rw [finset.sum_insert hxs, add_apply, ih, finset.sum_insert hxs])

lemma mem_nat_downset_iff_le (f g : σ →₀ ℕ) :
  f ∈ (nat_downset g) ↔ f ≤ g :=
begin
  delta nat_downset, rw finset.mem_image, split,
  { rintros ⟨g', hg', rfl⟩ i,
    rw [finset.mem_pi] at hg',
    rw [sum_apply'],
    by_cases hi : i ∈ g.support,
    { rw finset.sum_eq_single (⟨i, hi⟩ : (↑g.support : set σ)),
      rw [single_apply, if_pos rfl],
      specialize hg' i hi,
      rw [finset.mem_range, nat.lt_succ_iff] at hg',
      exact hg',
      { intros j hj hji, rw [single_apply, if_neg], refine mt _ hji, intros hji', exact subtype.eq hji' },
      { intro hi', exact hi'.elim (finset.mem_attach _ _) } },
    { rw finset.sum_eq_zero, exact nat.zero_le _,
      intros j hj, rw [single_apply, if_neg], rintros rfl, exact hi j.2 } },
  { intros hf, refine ⟨λ i hi, f i, _, _⟩,
    { rw finset.mem_pi, intros i hi, rw [finset.mem_range, nat.lt_succ_iff], exact hf i },
    { ext i, rw sum_apply',
      by_cases hi : i ∈ g.support,
      { rw finset.sum_eq_single (⟨i, hi⟩ : (↑g.support : set σ)),
        rw [single_apply, if_pos rfl],
        { intros j hj hji, rw [single_apply, if_neg], refine mt _ hji, intros hji', exact subtype.eq hji' },
        { intro hi', exact hi'.elim (finset.mem_attach _ _) } },
      { rw finset.sum_eq_zero, rw not_mem_support_iff at hi, symmetry,
        exact nat.eq_zero_of_le_zero (hi ▸ hf i),
        { intros j hj, rw [single_apply, if_neg], rintros rfl, exact hi j.2 } } } }
end

end finsupp

/-- Multivariate power series, where `σ` is the index set of the variables
and `α` is the coefficient ring.-/
def mv_power_series (σ : Type*) (α : Type*) := (σ →₀ ℕ) → α

namespace mv_power_series
open finsupp
variables {σ : Type*} {α : Type*} [decidable_eq σ] [comm_semiring α]

def coeff (n : σ →₀ ℕ) (φ : mv_power_series σ α) := φ n

@[extensionality] lemma ext {φ ψ : mv_power_series σ α} (h : ∀ n, coeff n φ = coeff n ψ) : φ = ψ :=
funext h

lemma ext_iff {φ ψ : mv_power_series σ α} : φ = ψ ↔ (∀ n, coeff n φ = coeff n ψ) :=
⟨congr_fun, ext⟩

def monomial (n : σ →₀ ℕ) (a : α) : mv_power_series σ α := λ m, if m = n then a else 0

lemma coeff_monomial (m n : σ →₀ ℕ) (a : α) :
  coeff m (monomial n a) = if m = n then a else 0 := rfl

@[simp] lemma coeff_monomial' (n : σ →₀ ℕ) (a : α) :
  coeff n (monomial n a) = a := if_pos rfl

def C (a : α) : mv_power_series σ α := monomial 0 a

lemma coeff_C (n : σ →₀ ℕ) (a : α) :
  coeff n (C a : mv_power_series σ α) = if n = 0 then a else 0 := rfl

@[simp] lemma coeff_C_zero (a : α) : coeff 0 (C a : mv_power_series σ α) = a :=
coeff_monomial' 0 a

@[simp] lemma monomial_zero (a : α) : (monomial 0 a : mv_power_series σ α) = C a := rfl

def X (s : σ) : mv_power_series σ α := monomial (single s 1) 1

lemma coeff_X (n : σ →₀ ℕ) (s : σ) :
  coeff n (X s : mv_power_series σ α) = if n = (single s 1) then 1 else 0 := rfl

lemma coeff_X' (s t : σ) :
  coeff (single t 1) (X s : mv_power_series σ α) = if t = s then 1 else 0 :=
if h : t = s then by simp [h, coeff_X] else
begin
  rw [coeff_X, if_neg h],
  split_ifs with H,
  { have := @finsupp.single_apply σ ℕ _ _ _ t s 1,
    rw [if_neg h, H, finsupp.single_apply, if_pos rfl] at this,
    exfalso, exact one_ne_zero this, },
  { refl }
end

@[simp] lemma coeff_X'' (s : σ) :
  coeff (single s 1) (X s : mv_power_series σ α) = 1 :=
by rw [coeff_X', if_pos rfl]

section ring
variables (σ) (α) (n : σ →₀ ℕ) (φ ψ : mv_power_series σ α)

def zero : mv_power_series σ α := λ n, 0

instance : has_zero (mv_power_series σ α) := ⟨zero σ α⟩

@[simp] lemma coeff_zero : coeff n (0 : mv_power_series σ α) = 0 := rfl

@[simp] lemma C_zero : (C 0 : mv_power_series σ α) = 0 :=
ext $ λ n, if h : n = 0 then by simp [h] else by rw [coeff_C, if_neg h, coeff_zero]

def one : mv_power_series σ α := C 1

instance : has_one (mv_power_series σ α) := ⟨one σ α⟩

@[simp] lemma coeff_one :
  coeff n (1 : mv_power_series σ α) = if n = 0 then 1 else 0 := rfl

@[simp] lemma coeff_one_zero : coeff 0 (1 : mv_power_series σ α) = 1 :=
coeff_C_zero 1

@[simp] lemma C_one : (C 1 : mv_power_series σ α) = 1 := rfl

def add (φ ψ : mv_power_series σ α) : mv_power_series σ α :=
λ n, coeff n φ + coeff n ψ

instance : has_add (mv_power_series σ α) := ⟨add σ α⟩

variables {σ α}

@[simp] lemma coeff_add : coeff n (φ + ψ) = coeff n φ + coeff n ψ := rfl

@[simp] lemma zero_add : (0 : mv_power_series σ α) + φ = φ := ext $ λ n, zero_add _

@[simp] lemma add_zero : φ + 0 = φ := ext $ λ n, add_zero _

lemma add_comm : φ + ψ = ψ + φ := ext $ λ n, add_comm _ _

lemma add_assoc (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  (φ₁ + φ₂) + φ₃ = φ₁ + (φ₂ + φ₃) :=
ext $ λ n, by simp

@[simp] lemma monomial_add (n : σ →₀ ℕ) (a b : α) :
  (monomial n (a + b) : mv_power_series σ α) = monomial n a + monomial n b :=
ext $ λ m, if h : m = n then by simp [h] else by simp [coeff_monomial, if_neg h]

@[simp] lemma C_add (a b : α) : (C (a + b) : mv_power_series σ α) = C a + C b :=
monomial_add 0 a b

variables (σ α)

def mul (φ ψ : mv_power_series σ α) : mv_power_series σ α :=
λ n, (nat_downset n).sum $ λ m, coeff m φ * coeff (n-m) ψ

instance : has_mul (mv_power_series σ α) := ⟨mul σ α⟩

lemma coeff_mul :
  coeff n (φ * ψ) = (nat_downset n).sum (λ m, coeff m φ * coeff (n-m) ψ) := rfl

variables {σ α}

@[simp] lemma zero_mul : (0 : mv_power_series σ α) * φ = 0 :=
ext $ λ n, by simp [coeff_mul]

@[simp] lemma mul_zero : φ * 0 = 0 :=
ext $ λ n, by simp [coeff_mul]

lemma mul_comm : φ * ψ = ψ * φ :=
ext $ λ n, finset.sum_bij (λ m hm, n - m)
(λ m hm, by { rw mem_nat_downset_iff_le at hm ⊢, intro s, apply nat.sub_le_self })
(λ m hm, by { rw mem_nat_downset_iff_le at hm, rw mul_comm,
  have : (n - (n - m)) = m := finsupp.ext (λ s, nat.sub_sub_self (hm s)),
  rw this })
(λ m₁ m₂ hm₁ hm₂ H, finsupp.ext $ λ s,
  begin
    rw mem_nat_downset_iff_le at hm₁ hm₂,
    rw finsupp.ext_iff at H,
    rw [← nat.sub_sub_self (hm₁ s), ← nat.sub_sub_self (hm₂ s)],
    show n s - (n - m₁) s = n s - (n - m₂) s,
    rw H
  end)
(λ m hm, ⟨(n - m), (by { rw mem_nat_downset_iff_le at hm ⊢, intro s, apply nat.sub_le_self }),
  (by { rw mem_nat_downset_iff_le at hm, apply finsupp.ext, intro s,
    rw ← nat.sub_sub_self (hm s), refl })⟩)

@[simp] lemma one_mul : (1 : mv_power_series σ α) * φ = φ :=
ext $ λ n,
begin
  have H : (0 : σ →₀ ℕ) ∈ (nat_downset n) :=
  (mem_nat_downset_iff_le 0 n).mpr (λ s, zero_le _),
  rw [coeff_mul, ← finset.insert_erase H, finset.sum_insert (finset.not_mem_erase _ _)],
  replace H : n - 0 = n := finsupp.ext (λ s, nat.sub_zero _),
  rw [H, coeff_one_zero, one_mul, finset.sum_eq_zero, _root_.add_zero],
  intros m hm, rw finset.mem_erase at hm,
  rw [coeff_one, if_neg hm.1, _root_.zero_mul]
end

@[simp] lemma mul_one : φ * 1 = φ :=
by rw [mul_comm, one_mul]

lemma mul_add (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃ :=
ext $ λ n, by simp only [coeff_mul, coeff_add, mul_add, finset.sum_add_distrib]

lemma add_mul (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃ :=
ext $ λ n, by simp only [coeff_mul, coeff_add, add_mul, finset.sum_add_distrib]

lemma mul_assoc (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  (φ₁ * φ₂) * φ₃ = φ₁ * (φ₂ * φ₃) :=
ext $ λ n,
begin
  have := @finset.sum_bind ((σ →₀ ℕ) × (σ →₀ ℕ)) α (σ →₀ ℕ) _ _ _ (nat_downset n)
  (λ m, finset.product {m} (nat_downset m)) _,
  swap,
  { intro p, exact (coeff p.2 φ₁ * coeff (p.1-p.2) φ₂) * coeff (n-p.1) φ₃ },
  swap,
  { intros, dsimp,
    rw finset.eq_empty_iff_forall_not_mem,
    intros p hp,
    simp [finset.mem_inter, finset.mem_product] at hp,
    rcases hp with ⟨⟨rfl, _⟩, ⟨rfl, _⟩⟩,
    contradiction },
  simp only [coeff_mul],
  convert this.symm using 1; clear this,
  { apply finset.sum_congr rfl,
    intros m hm,
    rw finset.sum_mul, symmetry,
    apply finset.sum_bij (λ (p : (σ →₀ ℕ) × (σ →₀ ℕ)) hp, p.2),
    { intros p hp, exact (finset.mem_product.1 hp).2 },
    { intros p hp, erw [finset.mem_product, finset.mem_singleton] at hp, cases hp, subst m },
    { rintros ⟨m₁,i₁⟩ ⟨m₂,i₂⟩ h₁ h₂ H, dsimp at *,
      erw [finset.mem_product, finset.mem_singleton] at h₁ h₂,
      dsimp at *, erw [h₁.1, h₂.1, H] },
    { intros i hi, refine ⟨(m,i), _, rfl⟩,
      { erw finset.mem_product, exact ⟨finset.mem_singleton_self m, hi⟩ } } },
  sorry
end

instance : comm_semiring (mv_power_series σ α) :=
{ mul_one := mul_one,
  one_mul := one_mul,
  add_assoc := add_assoc,
  zero_add := zero_add,
  add_zero := add_zero,
  add_comm := add_comm,
  mul_assoc := mul_assoc,
  mul_zero := mul_zero,
  zero_mul := zero_mul,
  mul_comm := mul_comm,
  left_distrib := mul_add,
  right_distrib := add_mul,
  .. mv_power_series.has_zero σ α,
  .. mv_power_series.has_one σ α,
  .. mv_power_series.has_add σ α,
  .. mv_power_series.has_mul σ α }

end ring

end mv_power_series

namespace mv_polynomial
open finsupp
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [comm_semiring α]

lemma coeff_mul (φ ψ : mv_polynomial σ α) (n) :
  coeff n (φ * ψ) = finset.sum (finsupp.nat_downset n) (λ m, coeff m φ * coeff (n - m) ψ) :=
begin
  have helper : ∀ (m : σ →₀ ℕ), m - 0 = m := λ m, finsupp.ext (λ s, nat.sub_zero _),
  revert n,
  apply mv_polynomial.induction_on φ,
  { apply mv_polynomial.induction_on ψ,
    { intros a b n, rw [← C_mul, coeff_C],
      split_ifs,
      { subst n, erw [nat_downset_zero, finset.sum_singleton],
        simp [helper] },
      { rw finset.sum_eq_zero,
        intros m hm,
        by_cases H : m = 0,
        { subst m, simp [helper, h] },
        { rw ← ne_from_not_eq at H, simp [H.symm] } } },
    { intros p q hp hq a, specialize hp a, specialize hq a,
      simp [coeff_C_mul, coeff_add, mul_add, finset.sum_add_distrib, *] at * },
    { intros p s hp a n, specialize hp a,
      rw [coeff_C_mul, coeff_mul_X'],
      split_ifs,
      { rw [← coeff_C_mul, hp], sorry },
      { rw [mul_zero, finset.sum_eq_zero],
        intros m hm,
        rw coeff_mul_X',
        have : s ∉ (n - m).support,
        { rw not_mem_support_iff at h ⊢,
          show n s - m s = 0,
          rw h,
          apply nat.zero_sub },
        rw [if_neg this, mul_zero] } } },
  { intros p q hp hq n,
    rw [add_mul, coeff_add, hp, hq, ← finset.sum_add_distrib],
    apply finset.sum_congr rfl,
    intros m hm, rw [coeff_add, add_mul] },
  { intros p s hp n,
    conv_lhs { rw [mul_assoc, mul_comm (X s), ← mul_assoc] },
    rw coeff_mul_X',
    split_ifs,
    { rw hp, sorry },
    { rw finset.sum_eq_zero,
      intros m hm,
      have : s ∉ m.support,
      { rw not_mem_support_iff at h ⊢,
        rw mem_nat_downset_iff_le at hm,
        specialize hm s, rw h at hm,
        exact nat.eq_zero_of_le_zero hm },
      rw [coeff_mul_X', if_neg this, zero_mul] } }
end

def to_mv_power_series (φ : mv_polynomial σ α) : mv_power_series σ α :=
λ n, coeff n φ

@[simp] lemma to_mv_power_series_coeff (φ : mv_polynomial σ α) (n) :
mv_power_series.coeff n (φ.to_mv_power_series) = coeff n φ := rfl

namespace to_mv_power_series

instance : is_semiring_hom (to_mv_power_series : mv_polynomial σ α → mv_power_series σ α) :=
{ map_zero := mv_power_series.ext $ λ n, by simp,
  map_one := mv_power_series.ext $ λ n,
  begin
    rw [to_mv_power_series_coeff, mv_power_series.coeff_one],
    split_ifs; rw ← C_1; simp [-C_1, h],
    { rw ← ne_from_not_eq at h, simp [h.symm] }
  end,
  map_add := λ φ ψ, mv_power_series.ext $ λ n, by simp,
  map_mul := λ φ ψ, mv_power_series.ext $ λ n,
  by simp only [to_mv_power_series_coeff, mv_power_series.coeff_mul, coeff_mul] }

end to_mv_power_series

end mv_polynomial
