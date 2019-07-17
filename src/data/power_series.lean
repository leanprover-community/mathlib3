/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import data.finsupp order.complete_lattice algebra.ordered_group data.mv_polynomial
import algebra.order_functions
import ring_theory.ideal_operations
import linear_algebra.basis
import algebra.CommRing.limits

namespace discrete_field
variables {α : Type*} [discrete_field α]

instance : local_ring α :=
{ is_local := λ a,
  if h : a = 0
  then or.inr (by rw [h, sub_zero]; exact is_unit_one)
  else or.inl $ is_unit_of_mul_one a a⁻¹ $ div_self h }

end discrete_field

namespace finsupp
variables {α : Type*} [decidable_eq α] [add_comm_monoid α]

lemma single_punit_eq (x : punit) (f : punit →₀ α) : single x (f x) = f :=
ext $ λ y,
match x, y with
| punit.star, punit.star := by { rw [single_apply, if_pos rfl] }
end

lemma single_punit_eq_single_punit_iff (x y : punit) (a b : α) :
  single x a = single y b ↔ a = b :=
begin
  rw [single_eq_single_iff],
  split,
  { rintros (⟨_, rfl⟩ | ⟨rfl, rfl⟩); refl },
  { intro h, left, exact ⟨subsingleton.elim _ _, h⟩ }
end

end finsupp

namespace finsupp
variables {σ : Type*} {α : Type*} [decidable_eq σ]

lemma le_iff [canonically_ordered_monoid α] (f g : σ →₀ α) :
  f ≤ g ↔ ∀ s ∈ f.support, f s ≤ g s :=
⟨λ h s hs, h s,
λ h s, if H : s ∈ f.support then h s H else (not_mem_support_iff.1 H).symm ▸ zero_le (g s)⟩

attribute [simp] to_multiset_zero to_multiset_add

lemma to_multiset_strict_mono : strict_mono (@to_multiset σ _) :=
λ m n h,
begin
  rw lt_iff_le_and_ne at h ⊢, cases h with h₁ h₂,
  split,
  { rw multiset.le_iff_count, intro s, rw [count_to_multiset, count_to_multiset], exact h₁ s },
  { intro H, apply h₂, replace H := congr_arg multiset.to_finsupp H, simpa using H }
end

lemma sum_lt_of_lt (m n : σ →₀ ℕ) (h : m < n) :
  m.sum (λ _, id) < n.sum (λ _, id) :=
begin
  rw [← card_to_multiset, ← card_to_multiset],
  apply multiset.card_lt_of_lt,
  exact to_multiset_strict_mono _ _ h
end

lemma single_eq_single_of_ne_zero [has_zero α] [decidable_eq α] {s t : σ} {a : α} (h : a ≠ 0) :
  single s a = single t a ↔ s = t :=
⟨λ H, by simpa [h, single_eq_single_iff] using H, λ H, by rw [H]⟩

lemma single_eq_zero [has_zero α] [decidable_eq α] {s : σ} {a : α} :
  single s a = 0 ↔ a = 0 :=
⟨λ h, by { rw ext_iff at h, simpa only [finsupp.single_eq_same, finsupp.zero_apply] using h s },
λ h, by rw [h, single_zero]⟩

variable (σ)

def lt_wf : well_founded (@has_lt.lt (σ →₀ ℕ) _) :=
subrelation.wf (sum_lt_of_lt) $ inv_image.wf _ nat.lt_wf

instance decidable_lt : decidable_rel (@has_lt.lt (σ →₀ ℕ) _) :=
λ m n,
begin
  have h : _ := _,
  rw lt_iff_le_and_ne, refine @and.decidable _ _ h _,
  rw le_iff, apply_instance
end

end finsupp

/-- Multivariate power series, where `σ` is the index set of the variables
and `α` is the coefficient ring.-/
def mv_power_series (σ : Type*) (α : Type*) := (σ →₀ ℕ) → α

namespace mv_power_series
open finsupp
variables {σ : Type*} {α : Type*} [decidable_eq σ]

def coeff (n : σ →₀ ℕ) (φ : mv_power_series σ α) := φ n

@[extensionality] lemma ext {φ ψ : mv_power_series σ α} (h : ∀ n, coeff n φ = coeff n ψ) :
  φ = ψ :=
funext h

lemma ext_iff {φ ψ : mv_power_series σ α} :
  φ = ψ ↔ (∀ n, coeff n φ = coeff n ψ) :=
⟨λ h n, congr_arg (coeff n) h, ext⟩

variables [comm_semiring α]

def monomial (n : σ →₀ ℕ) (a : α) : mv_power_series σ α :=
λ m, if m = n then a else 0

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
by { simp only [coeff_X, single_eq_single_of_ne_zero one_ne_zero], split_ifs; refl }

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
  (φ₁ + φ₂) + φ₃ = φ₁ + (φ₂ + φ₃) := ext $ λ n, add_assoc _ _ _

@[simp] lemma monomial_add (n : σ →₀ ℕ) (a b : α) :
  (monomial n (a + b) : mv_power_series σ α) = monomial n a + monomial n b :=
ext $ λ m, if h : m = n then by simp [h] else by simp [coeff_monomial, if_neg h]

@[simp] lemma C_add (a b : α) : (C (a + b) : mv_power_series σ α) = C a + C b :=
monomial_add 0 a b

variables (σ α)

def mul (φ ψ : mv_power_series σ α) : mv_power_series σ α :=
λ n, (finsupp.antidiagonal n).support.sum (λ p, coeff p.1 φ * coeff p.2 ψ)

instance : has_mul (mv_power_series σ α) := ⟨mul σ α⟩

variables {σ α}

lemma coeff_mul :
  coeff n (φ * ψ) = (finsupp.antidiagonal n).support.sum (λ p, coeff p.1 φ * coeff p.2 ψ) := rfl

@[simp] lemma C_mul (a b : α) : (C (a * b) : mv_power_series σ α) = C a * C b :=
ext $ λ n,
begin
  rw [coeff_C, coeff_mul],
  split_ifs,
  { subst n, erw [antidiagonal_zero, finset.sum_singleton, coeff_C_zero, coeff_C_zero] },
  { rw finset.sum_eq_zero,
    rintros ⟨i,j⟩ hij,
    rw mem_antidiagonal_support at hij, rw [coeff_C, coeff_C],
    split_ifs; try {simp * at *; done} }
end

@[simp] lemma zero_mul : (0 : mv_power_series σ α) * φ = 0 :=
ext $ λ n, by simp [coeff_mul]

@[simp] lemma mul_zero : φ * 0 = 0 :=
ext $ λ n, by simp [coeff_mul]

lemma mul_comm : φ * ψ = ψ * φ :=
ext $ λ n, finset.sum_bij (λ p hp, p.swap)
  (λ p hp, swap_mem_antidiagonal_support hp)
  (λ p hp, mul_comm _ _)
  (λ p q hp hq H, by simpa using congr_arg prod.swap H)
  (λ p hp, ⟨p.swap, swap_mem_antidiagonal_support hp, p.swap_swap.symm⟩)

@[simp] lemma one_mul : (1 : mv_power_series σ α) * φ = φ :=
ext $ λ n,
begin
  have H : ((0 : σ →₀ ℕ), n) ∈ (antidiagonal n).support := by simp [mem_antidiagonal_support],
  rw [coeff_mul, ← finset.insert_erase H, finset.sum_insert (finset.not_mem_erase _ _),
    coeff_one_zero, one_mul, finset.sum_eq_zero, _root_.add_zero],
  rintros ⟨i,j⟩ hij,
  rw [finset.mem_erase, mem_antidiagonal_support] at hij,
  rw [coeff_one, if_neg, _root_.zero_mul],
  intro H, apply hij.1, simp * at *
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
  simp only [coeff_mul],
  have := @finset.sum_sigma ((σ →₀ ℕ) × (σ →₀ ℕ)) α _ _ (antidiagonal n).support
    (λ p, (antidiagonal (p.1)).support) (λ x, coeff x.2.1 φ₁ * coeff x.2.2 φ₂ * coeff x.1.2 φ₃),
  convert this.symm using 1; clear this,
  { apply finset.sum_congr rfl,
    intros p hp, exact finset.sum_mul },
  have := @finset.sum_sigma ((σ →₀ ℕ) × (σ →₀ ℕ)) α _ _ (antidiagonal n).support
    (λ p, (antidiagonal (p.2)).support) (λ x, coeff x.1.1 φ₁ * (coeff x.2.1 φ₂ * coeff x.2.2 φ₃)),
  convert this.symm using 1; clear this,
  { apply finset.sum_congr rfl, intros p hp, rw finset.mul_sum },
  apply finset.sum_bij,
  swap 5,
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, exact ⟨(k, l+j), (l, j)⟩ },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H,
    simp only [finset.mem_sigma, mem_antidiagonal_support] at H ⊢, finish },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, rw mul_assoc },
  { rintros ⟨⟨a,b⟩, ⟨c,d⟩⟩ ⟨⟨i,j⟩, ⟨k,l⟩⟩ H₁ H₂,
    simp only [finset.mem_sigma, mem_antidiagonal_support,
      and_imp, prod.mk.inj_iff, add_comm, heq_iff_eq] at H₁ H₂ ⊢,
    finish },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, refine ⟨⟨(i+k, l), (i, k)⟩, _, _⟩;
    { simp only [finset.mem_sigma, mem_antidiagonal_support] at H ⊢, finish } }
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

instance C.is_semiring_hom : is_semiring_hom (C : α → mv_power_series σ α) :=
{ map_zero := C_zero _ _,
  map_one := C_one _ _,
  map_add := C_add,
  map_mul := C_mul }

instance coeff.is_add_monoid_hom : is_add_monoid_hom (coeff n : mv_power_series σ α → α) :=
{ map_zero := coeff_zero _ _ _,
  map_add := coeff_add n }

instance coeff_zero.is_semiring_hom : is_semiring_hom (coeff 0 : mv_power_series σ α → α) :=
{ map_one := coeff_one_zero _ _,
  map_mul := λ φ ψ, by simp [coeff_mul, support_single_ne_zero],
  .. coeff.is_add_monoid_hom 0 }

lemma unit_coeff_zero (h : is_unit φ) : is_unit (coeff 0 φ) :=
by { rcases h with ⟨φ, rfl⟩, exact ⟨units.map (coeff 0) φ, rfl⟩ }

instance : semimodule α (mv_power_series σ α) :=
{ smul := λ a φ, C a * φ,
  one_smul := λ φ, one_mul _,
  mul_smul := λ a b φ, by simp only [C_mul, mul_assoc],
  smul_add := λ a φ ψ, mul_add _ _ _,
  smul_zero := λ a, mul_zero _,
  add_smul := λ a b φ, by simp only [C_add, add_mul],
  zero_smul := λ φ, by simp only [zero_mul, C_zero] }

section map
variables {β : Type*} {γ : Type*} [comm_semiring β] [comm_semiring γ]
variables (f : α → β) (g : β → γ) [is_semiring_hom f] [is_semiring_hom g]

def map : mv_power_series σ α → mv_power_series σ β :=
λ φ n, f $ coeff n φ

@[simp] lemma map_id : (map (id : α → α) : mv_power_series σ α → mv_power_series σ α) = id := rfl

lemma map_comp : (map (g ∘ f) : mv_power_series σ α → mv_power_series σ γ) = map g ∘ map f := rfl

@[simp] lemma coeff_map (n) (φ : mv_power_series σ α) :
  coeff n (map f φ) = f (coeff n φ) := rfl

@[simp] lemma map_zero : map f (0 : mv_power_series σ α) = 0 :=
ext $ λ n, is_semiring_hom.map_zero f

@[simp] lemma map_one : map f (1 : mv_power_series σ α) = 1 :=
ext $ λ n,
if h : n = 0
then by rw [coeff_map, h, coeff_one_zero, is_semiring_hom.map_one f, coeff_one_zero]
else by rw [coeff_map, coeff_one, if_neg h, is_semiring_hom.map_zero f, coeff_one, if_neg h]

@[simp] lemma map_add (φ ψ : mv_power_series σ α) : map f (φ + ψ) = map f φ + map f ψ :=
ext $ λ n, by rw [coeff_map, coeff_add, is_semiring_hom.map_add f, coeff_add, coeff_map, coeff_map]

@[simp] lemma map_mul (φ ψ : mv_power_series σ α) : map f (φ * ψ) = map f φ * map f ψ :=
ext $ λ n,
begin
  rw [coeff_map, coeff_mul, ← finset.sum_hom f, coeff_mul, finset.sum_congr rfl],
  rintros ⟨i,j⟩ hij, rw [is_semiring_hom.map_mul f, coeff_map, coeff_map]
end

instance map.is_semiring_hom :
  is_semiring_hom (map f : mv_power_series σ α → mv_power_series σ β) :=
{ map_zero := map_zero f,
  map_one := map_one f,
  map_add := map_add f,
  map_mul := map_mul f }

end map

end ring

-- TODO(jmc): once adic topology lands, show that this is complete

end mv_power_series

namespace mv_power_series
variables {σ : Type*} {α : Type*} [decidable_eq σ] [comm_ring α]

protected def neg (φ : mv_power_series σ α) : mv_power_series σ α := λ n, - coeff n φ

instance : has_neg (mv_power_series σ α) := ⟨mv_power_series.neg⟩

@[simp] lemma coeff_neg (φ : mv_power_series σ α) (n) : coeff n (- φ) = - coeff n φ := rfl

lemma add_left_neg (φ : mv_power_series σ α) : (-φ) + φ = 0 :=
ext $ λ n, by rw [coeff_add, coeff_zero, coeff_neg, add_left_neg]

instance : comm_ring (mv_power_series σ α) :=
{ add_left_neg := add_left_neg,
  .. mv_power_series.has_neg, .. mv_power_series.comm_semiring }

instance C.is_ring_hom : is_ring_hom (C : α → mv_power_series σ α) :=
{ map_one := C_one _ _,
  map_add := C_add,
  map_mul := C_mul }

instance coeff.is_add_group_hom (n : σ →₀ ℕ) :
  is_add_group_hom (coeff n : mv_power_series σ α → α) :=
{ map_add := coeff_add n }

instance map.is_ring_hom {β : Type*} [comm_ring β] (f : α → β) [is_ring_hom f] :
  is_ring_hom (map f : mv_power_series σ α → mv_power_series σ β) :=
{ .. map.is_semiring_hom f }

instance : module α (mv_power_series σ α) :=
{ ..mv_power_series.semimodule }

instance : algebra α (mv_power_series σ α) :=
{ to_fun := C,
  commutes' := λ _ _, mul_comm _ _,
  smul_def' := λ c p, rfl,
  .. mv_power_series.module }

def inv.aux (a : α) (φ : mv_power_series σ α) : mv_power_series σ α
| n := if n = 0 then a else
- a * n.antidiagonal.support.sum (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
    if h : x.2 < n then coeff x.1 φ * inv.aux x.2 else 0)
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨_, finsupp.lt_wf σ⟩],
  dec_tac := tactic.assumption }

lemma coeff_inv_aux (n : σ →₀ ℕ) (a : α) (φ : mv_power_series σ α) :
  coeff n (inv.aux a φ) = if n = 0 then a else
  - a * n.antidiagonal.support.sum (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
    if x.2 < n then coeff x.1 φ * coeff x.2 (inv.aux a φ) else 0) :=
by rw [coeff, inv.aux]; refl

def inv_of_unit (φ : mv_power_series σ α) (u : units α) : mv_power_series σ α :=
inv.aux (↑u⁻¹) φ

lemma coeff_inv_of_unit (n : σ →₀ ℕ) (φ : mv_power_series σ α) (u : units α) :
  coeff n (inv_of_unit φ u) = if n = 0 then ↑u⁻¹ else
  - ↑u⁻¹ * n.antidiagonal.support.sum (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
    if x.2 < n then coeff x.1 φ * coeff x.2 (inv_of_unit φ u) else 0) :=
coeff_inv_aux n (↑u⁻¹) φ

@[simp] lemma coeff_zero_inv_of_unit (φ : mv_power_series σ α) (u : units α) :
  coeff (0 : σ →₀ ℕ) (inv_of_unit φ u) = ↑u⁻¹ :=
by rw [coeff_inv_of_unit, if_pos rfl]

lemma mul_inv_of_unit (φ : mv_power_series σ α) (u : units α) (h : coeff 0 φ = u) :
  φ * inv_of_unit φ u = 1 :=
ext $ λ n,
if H : n = 0 then
by rw [H, coeff_mul, coeff_one_zero, finsupp.antidiagonal_zero, finset.insert_empty_eq_singleton,
  finset.sum_singleton, coeff_zero_inv_of_unit, h, units.mul_inv]
else
begin
  have : ((0 : σ →₀ ℕ), n) ∈ n.diagonal,
  { rw [finsupp.mem_diagonal], simp },
  rw [coeff_one, if_neg H, coeff_mul,
    ← finset.insert_erase this, finset.sum_insert (finset.not_mem_erase _ _),
    coeff_inv_of_unit, if_neg H, h,
    neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, units.mul_inv_cancel_left,
    ← finset.insert_erase this, finset.sum_insert (finset.not_mem_erase _ _),
    finset.insert_erase this, if_neg (not_lt_of_ge $ le_refl _), _root_.add_comm, _root_.zero_add,
    ← sub_eq_add_neg, sub_eq_zero, finset.sum_congr rfl],
  rintros ⟨i,j⟩ hij, rw [finset.mem_erase, finsupp.mem_diagonal] at hij, cases hij with h₁ h₂,
  subst n, rw if_pos,
  split,
  { intro s, exact nat.le_add_left (j s) (i s) },
  { intro H, apply h₁,
    suffices : i = 0, { simp [this] },
    ext1 s, specialize H s, rw ← _root_.zero_add (j s) at H,
    apply nat.eq_zero_of_le_zero,
    exact (add_le_add_iff_right (j s)).mp H }
end

section local_ring

def is_local_ring (h : is_local_ring α) : is_local_ring (mv_power_series σ α) :=
begin
  split,
  { intro this, apply ‹is_local_ring α›.1, simpa using congr_arg (coeff 0) this },
  { intro φ, let c := coeff 0 φ,
    have : is_unit c ∨ is_unit (1 - c) := ‹is_local_ring α›.2 c,
    cases this with h h; [left, right]; cases h with u h;
    { apply is_unit_of_mul_one _,
      { apply mul_inv_of_unit, { exact h } } } }
end

end local_ring

end mv_power_series

namespace mv_power_series
variables {σ : Type*} {α : Type*} {β : Type*} (f : α → β)
variables [decidable_eq σ] [local_ring α] [local_ring β] [is_local_ring_hom f]

instance : local_ring (mv_power_series σ α) :=
local_of_is_local_ring $ is_local_ring ⟨zero_ne_one, local_ring.is_local⟩

instance map.is_local_ring_hom : is_local_ring_hom (map f : mv_power_series σ α → mv_power_series σ β) :=
{ map_nonunit :=
  begin
    rintros φ ⟨ψ, h⟩,
    replace h := congr_arg (coeff 0) h,
    rw coeff_map at h,
    have : is_unit (coeff 0 ↑ψ) := @unit_coeff_zero σ β _ _ (↑ψ) (is_unit_unit ψ),
    rw ← h at this,
    rcases is_unit_of_map_unit f _ this with ⟨c, hc⟩,
    refine is_unit_of_mul_one φ (inv_of_unit φ c) (mul_inv_of_unit φ c hc),
  end,
  .. map.is_ring_hom f }

end mv_power_series

namespace mv_power_series
variables {σ : Type*} {α : Type*} [decidable_eq σ] [discrete_field α]

def inv (φ : mv_power_series σ α) : mv_power_series σ α :=
inv.aux (coeff 0 φ)⁻¹ φ

instance : has_inv (mv_power_series σ α) := ⟨inv⟩

lemma coeff_inv (n) (φ : mv_power_series σ α) :
  coeff n (φ⁻¹) = if n = 0 then (coeff 0 φ)⁻¹ else
  - (coeff 0 φ)⁻¹ * finset.sum (n.diagonal) (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
    if x.2 < n then coeff x.1 φ * coeff x.2 (φ⁻¹) else 0) :=
coeff_inv_aux n _ φ

@[simp] lemma coeff_zero_inv (φ : mv_power_series σ α) :
  coeff 0 (φ⁻¹) = (coeff 0 φ)⁻¹ :=
by rw [coeff_inv, if_pos rfl]

lemma inv_eq_zero (φ : mv_power_series σ α) (h : coeff 0 φ = 0) :
  φ⁻¹ = 0 :=
ext $ λ n, by { rw coeff_inv, split_ifs; simp [h] }

@[simp] lemma inv_of_unit_eq (φ : mv_power_series σ α) (h : coeff 0 φ ≠ 0) :
  inv_of_unit φ (units.mk0 _ h) = φ⁻¹ := rfl

@[simp] lemma inv_of_unit_eq' (φ : mv_power_series σ α) (u : units α) (h : coeff 0 φ = u) :
  inv_of_unit φ u = φ⁻¹ :=
begin
  rw ← inv_of_unit_eq,
  { congr' 1, rw [units.ext_iff, ← h], refl },
  { rw h, exact units.ne_zero _ }
end

@[simp] lemma mul_inv (φ : mv_power_series σ α) (h : coeff 0 φ ≠ 0) :
  φ * φ⁻¹ = 1 :=
by rw [← inv_of_unit_eq φ h, mul_inv_of_unit φ (units.mk0 _ h) rfl]

@[simp] lemma inv_mul (φ : mv_power_series σ α) (h : coeff 0 φ ≠ 0) :
  φ⁻¹ * φ = 1 :=
by rw [mul_comm, mul_inv _ h]

end mv_power_series

def power_series (α : Type*) := mv_power_series unit α

namespace power_series
open finsupp (single)
variable {α : Type*}

def coeff (n : ℕ) : power_series α → α := mv_power_series.coeff (single () n)

@[extensionality] lemma ext {φ ψ : power_series α} (h : ∀ n, coeff n φ = coeff n ψ) : φ = ψ :=
mv_power_series.ext $ λ n,
begin
  have : n = single () (n ()),
  { ext x, exact match x with | () := by { rw [finsupp.single_apply, if_pos rfl] } end },
  convert h (n ())
end

lemma ext_iff {φ ψ : power_series α} : φ = ψ ↔ (∀ n, coeff n φ = coeff n ψ) :=
⟨λ h n, congr_arg (coeff n) h, ext⟩

def mk (f : ℕ → α) : power_series α := λ s, f (s ())

@[simp] lemma coeff_mk (n : ℕ) (f : ℕ → α) : coeff n (mk f) = f n := rfl

section comm_semiring
variable [comm_semiring α]

instance : comm_semiring (power_series α) := by delta power_series; apply_instance

def monomial (n : ℕ) : α → power_series α := mv_power_series.monomial (single () n)

def C : α → power_series α := mv_power_series.C

def X : power_series α := mv_power_series.X ()

lemma coeff_monomial (m n : ℕ) (a : α) :
  coeff m (monomial n a) = if m = n then a else 0 :=
calc coeff m (monomial n a) = _ : mv_power_series.coeff_monomial _ _ _
    ... = if m = n then a else 0 :
by { simp only [finsupp.single_punit_eq_single_punit_iff], split_ifs; refl }

lemma monomial_eq_mk (n : ℕ) (a : α) :
  monomial n a = mk (λ m, if m = n then a else 0) :=
ext $ λ m, coeff_monomial _ _ _

@[simp] lemma coeff_monomial' (n : ℕ) (a : α) :
  coeff n (monomial n a) = a := if_pos rfl

lemma coeff_C (n : ℕ) (a : α) :
  coeff n (C a : power_series α) = if n = 0 then a else 0 :=
calc coeff n (C a) = _ : mv_power_series.coeff_C _ _
    ... = if n = 0 then a else 0 :
by { simp only [finsupp.single_eq_zero], split_ifs; refl }

@[simp] lemma coeff_C_zero (a : α) : coeff 0 (C a) = a :=
coeff_monomial' 0 a

@[simp] lemma monomial_zero (a : α) : (monomial 0 a : power_series α) = C a := rfl

lemma coeff_X (n : ℕ) :
  coeff n (X : power_series α) = if n = 1 then 1 else 0 :=
calc coeff n (X : power_series α) = _ : mv_power_series.coeff_X _ _
    ... = if n = 1 then 1 else 0 :
by { simp only [finsupp.single_punit_eq_single_punit_iff], split_ifs; refl }

@[simp] lemma coeff_X' : coeff 1 (X : power_series α) = 1 :=
by rw [coeff_X, if_pos rfl]

@[simp] lemma coeff_zero (n : ℕ) : coeff n (0 : power_series α) = 0 := rfl

@[simp] lemma C_zero : (C 0 : power_series α) = 0 := mv_power_series.C_zero _ _

@[simp] lemma coeff_one (n : ℕ) :
  coeff n (1 : power_series α) = if n = 0 then 1 else 0 :=
calc coeff n (1 : power_series α) = _ : mv_power_series.coeff_one _ _ _
    ... = if n = 0 then 1 else 0 :
by { simp only [finsupp.single_eq_zero], split_ifs; refl }

@[simp] lemma coeff_one_zero : coeff 0 (1 : power_series α) = 1 :=
coeff_C_zero 1

@[simp] lemma C_one : (C 1 : power_series α) = 1 := rfl

@[simp] lemma coeff_add (n : ℕ) (φ ψ : power_series α) :
  coeff n (φ + ψ) = coeff n φ + coeff n ψ := rfl

@[simp] lemma monomial_add (n : ℕ) (a b : α) :
  (monomial n (a + b) : power_series α) = monomial n a + monomial n b :=
mv_power_series.monomial_add _ _ _

@[simp] lemma C_add (a b : α) : (C (a + b) : power_series α) = C a + C b :=
monomial_add 0 a b

-- lemma coeff_mul (n : ℕ) (φ ψ : power_series α) :
--   coeff n (φ * ψ) = (nat.diagonal n).sum (λ p, coeff p.1 φ * coeff p.2 ψ) := rfl

@[simp] lemma C_mul (a b : α) : (C (a * b) : power_series α) = C a * C b :=
mv_power_series.C_mul _ _

instance C.is_semiring_hom : is_semiring_hom (C : α → power_series α) :=
mv_power_series.C.is_semiring_hom

instance coeff.is_add_monoid_hom (n : ℕ) : is_add_monoid_hom (coeff n : power_series α → α) :=
{ map_zero := coeff_zero n,
  map_add := coeff_add n }

instance : semimodule α (power_series α) :=
mv_power_series.semimodule

section map
variables {β : Type*} {γ : Type*} [comm_semiring β] [comm_semiring γ]
variables (f : α → β) (g : β → γ) [is_semiring_hom f] [is_semiring_hom g]

def map : power_series α → power_series β :=
mv_power_series.map f

@[simp] lemma map_id : (map (id : α → α) : power_series α → power_series α) = id := rfl

lemma map_comp : (map (g ∘ f) : power_series α → power_series γ) = map g ∘ map f := rfl

@[simp] lemma coeff_map (n : ℕ) (φ : power_series α) :
  coeff n (map f φ) = f (coeff n φ) := rfl

@[simp] lemma map_zero : map f (0 : power_series α) = 0 :=
mv_power_series.map_zero f

@[simp] lemma map_one : map f (1 : power_series α) = 1 :=
mv_power_series.map_one f

@[simp] lemma map_add (φ ψ : power_series α) : map f (φ + ψ) = map f φ + map f ψ :=
mv_power_series.map_add f φ ψ

@[simp] lemma map_mul (φ ψ : power_series α) : map f (φ * ψ) = map f φ * map f ψ :=
mv_power_series.map_mul f φ ψ

instance map.is_semiring_hom :
  is_semiring_hom (map f : power_series α → power_series β) :=
mv_power_series.map.is_semiring_hom f

end map

end comm_semiring

section comm_ring
variables [comm_ring α]

instance : comm_ring (power_series α) := by delta power_series; apply_instance

instance C.is_ring_hom : is_ring_hom (C : α → power_series α) :=
mv_power_series.C.is_ring_hom

instance map.is_ring_hom {β : Type*} [comm_ring β] (f : α → β) [is_ring_hom f] :
  is_ring_hom (map f : power_series α → power_series β) :=
{ .. map.is_semiring_hom f }

instance : module α (power_series α) :=
mv_power_series.module

instance : algebra α (power_series α) :=
mv_power_series.algebra

end comm_ring

section local_ring
variables [comm_ring α] [is_local_ring α]

instance : is_local_ring (power_series α) :=
_

end local_ring

end power_series
