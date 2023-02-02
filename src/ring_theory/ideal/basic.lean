/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import algebra.associated
import linear_algebra.basic
import order.atoms
import order.compactly_generated
import tactic.abel
import data.nat.choose.sum
import linear_algebra.finsupp
/-!

# Ideals over a ring

This file defines `ideal R`, the type of (left) ideals over a ring `R`.
Note that over commutative rings, left ideals and two-sided ideals are equivalent.

## Implementation notes

`ideal R` is implemented using `submodule R R`, where `•` is interpreted as `*`.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/

universes u v w
variables {α : Type u} {β : Type v}
open set function

open_locale classical big_operators pointwise

/-- A (left) ideal in a semiring `R` is an additive submonoid `s` such that
`a * b ∈ s` whenever `b ∈ s`. If `R` is a ring, then `s` is an additive subgroup.  -/
@[reducible] def ideal (R : Type u) [semiring R] := submodule R R

section semiring

namespace ideal
variables [semiring α] (I : ideal α) {a b : α}

protected lemma zero_mem : (0 : α) ∈ I := I.zero_mem

protected lemma add_mem : a ∈ I → b ∈ I → a + b ∈ I := I.add_mem

variables (a)
lemma mul_mem_left : b ∈ I → a * b ∈ I := I.smul_mem a
variables {a}

@[ext] lemma ext {I J : ideal α} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
submodule.ext h

lemma sum_mem (I : ideal α) {ι : Type*} {t : finset ι} {f : ι → α} :
  (∀c∈t, f c ∈ I) → (∑ i in t, f i) ∈ I := submodule.sum_mem I

theorem eq_top_of_unit_mem
  (x y : α) (hx : x ∈ I) (h : y * x = 1) : I = ⊤ :=
eq_top_iff.2 $ λ z _, calc
    z = z * (y * x) : by simp [h]
  ... = (z * y) * x : eq.symm $ mul_assoc z y x
  ... ∈ I : I.mul_mem_left _ hx

theorem eq_top_of_is_unit_mem {x} (hx : x ∈ I) (h : is_unit x) : I = ⊤ :=
let ⟨y, hy⟩ := h.exists_left_inv in eq_top_of_unit_mem I x y hx hy

theorem eq_top_iff_one : I = ⊤ ↔ (1:α) ∈ I :=
⟨by rintro rfl; trivial,
 λ h, eq_top_of_unit_mem _ _ 1 h (by simp)⟩

theorem ne_top_iff_one : I ≠ ⊤ ↔ (1:α) ∉ I :=
not_congr I.eq_top_iff_one

@[simp]
theorem unit_mul_mem_iff_mem {x y : α} (hy : is_unit y) : y * x ∈ I ↔ x ∈ I :=
begin
  refine ⟨λ h, _, λ h, I.mul_mem_left y h⟩,
  obtain ⟨y', hy'⟩ := hy.exists_left_inv,
  have := I.mul_mem_left y' h,
  rwa [← mul_assoc, hy', one_mul] at this,
end

/-- The ideal generated by a subset of a ring -/
def span (s : set α) : ideal α := submodule.span α s

@[simp] lemma submodule_span_eq {s : set α} :
  submodule.span α s = ideal.span s :=
rfl

@[simp] lemma span_empty : span (∅ : set α) = ⊥ := submodule.span_empty

@[simp] lemma span_univ : span (set.univ : set α) = ⊤ := submodule.span_univ

lemma span_union (s t : set α) : span (s ∪ t) = span s ⊔ span t :=
submodule.span_union _ _

lemma span_Union {ι} (s : ι → set α) : span (⋃ i, s i) = ⨆ i, span (s i) :=
submodule.span_Union _

lemma mem_span {s : set α} (x) : x ∈ span s ↔ ∀ p : ideal α, s ⊆ p → x ∈ p :=
mem_Inter₂

lemma subset_span {s : set α} : s ⊆ span s := submodule.subset_span

lemma span_le {s : set α} {I} : span s ≤ I ↔ s ⊆ I := submodule.span_le

lemma span_mono {s t : set α} : s ⊆ t → span s ≤ span t := submodule.span_mono

@[simp] lemma span_eq : span (I : set α) = I := submodule.span_eq _

@[simp] lemma span_singleton_one : span ({1} : set α) = ⊤ :=
(eq_top_iff_one _).2 $ subset_span $ mem_singleton _

lemma mem_span_insert {s : set α} {x y} :
  x ∈ span (insert y s) ↔ ∃ a (z ∈ span s), x = a * y + z := submodule.mem_span_insert

lemma mem_span_singleton' {x y : α} :
  x ∈ span ({y} : set α) ↔ ∃ a, a * y = x := submodule.mem_span_singleton

lemma span_singleton_le_iff_mem {x : α} : span {x} ≤ I ↔ x ∈ I :=
submodule.span_singleton_le_iff_mem _ _

lemma span_singleton_mul_left_unit {a : α} (h2 : is_unit a) (x : α) :
  span ({a * x} : set α) = span {x} := 
begin
  apply le_antisymm; rw [span_singleton_le_iff_mem, mem_span_singleton'],
  exacts [⟨a, rfl⟩, ⟨_, h2.unit.inv_mul_cancel_left x⟩],
end

lemma span_insert (x) (s : set α) : span (insert x s) = span ({x} : set α) ⊔ span s :=
submodule.span_insert x s

lemma span_eq_bot {s : set α} : span s = ⊥ ↔ ∀ x ∈ s, (x:α) = 0 := submodule.span_eq_bot

@[simp] lemma span_singleton_eq_bot {x} : span ({x} : set α) = ⊥ ↔ x = 0 :=
submodule.span_singleton_eq_bot

lemma span_singleton_ne_top {α : Type*} [comm_semiring α] {x : α} (hx : ¬ is_unit x) :
  ideal.span ({x} : set α) ≠ ⊤ :=
(ideal.ne_top_iff_one _).mpr $ λ h1, let ⟨y, hy⟩ := ideal.mem_span_singleton'.mp h1 in
  hx ⟨⟨x, y, mul_comm y x ▸ hy, hy⟩, rfl⟩

@[simp] lemma span_zero : span (0 : set α) = ⊥ := by rw [←set.singleton_zero, span_singleton_eq_bot]

@[simp] lemma span_one : span (1 : set α) = ⊤ := by rw [←set.singleton_one, span_singleton_one]

lemma span_eq_top_iff_finite (s : set α) :
  span s = ⊤ ↔ ∃ s' : finset α, ↑s' ⊆ s ∧ span (s' : set α) = ⊤ :=
begin
  simp_rw eq_top_iff_one,
  exact ⟨submodule.mem_span_finite_of_mem_span, λ ⟨s', h₁, h₂⟩, span_mono h₁ h₂⟩
end

lemma mem_span_singleton_sup {S : Type*} [comm_semiring S] {x y : S} {I : ideal S} :
  x ∈ ideal.span {y} ⊔ I ↔ ∃ (a : S) (b ∈ I), a * y + b = x :=
begin
  rw submodule.mem_sup,
  split,
  { rintro ⟨ya, hya, b, hb, rfl⟩,
    obtain ⟨a, rfl⟩ := mem_span_singleton'.mp hya,
    exact ⟨a, b, hb, rfl⟩ },
  { rintro ⟨a, b, hb, rfl⟩,
    exact ⟨a * y, ideal.mem_span_singleton'.mpr ⟨a, rfl⟩, b, hb, rfl⟩ }
end

/--
The ideal generated by an arbitrary binary relation.
-/
def of_rel (r : α → α → Prop) : ideal α :=
submodule.span α { x | ∃ (a b) (h : r a b), x + b = a }

/-- An ideal `P` of a ring `R` is prime if `P ≠ R` and `xy ∈ P → x ∈ P ∨ y ∈ P` -/
class is_prime (I : ideal α) : Prop :=
(ne_top' : I ≠ ⊤)
(mem_or_mem' : ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I)

theorem is_prime_iff {I : ideal α} :
  is_prime I ↔ I ≠ ⊤ ∧ ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I :=
⟨λ h, ⟨h.1, λ _ _, h.2⟩, λ h, ⟨h.1, λ _ _, h.2⟩⟩

theorem is_prime.ne_top {I : ideal α} (hI : I.is_prime) : I ≠ ⊤ := hI.1

theorem is_prime.mem_or_mem {I : ideal α} (hI : I.is_prime) {x y : α} :
  x * y ∈ I → x ∈ I ∨ y ∈ I := hI.2

theorem is_prime.mem_or_mem_of_mul_eq_zero {I : ideal α} (hI : I.is_prime)
  {x y : α} (h : x * y = 0) : x ∈ I ∨ y ∈ I :=
hI.mem_or_mem (h.symm ▸ I.zero_mem)

theorem is_prime.mem_of_pow_mem {I : ideal α} (hI : I.is_prime)
  {r : α} (n : ℕ) (H : r^n ∈ I) : r ∈ I :=
begin
  induction n with n ih,
  { rw pow_zero at H, exact (mt (eq_top_iff_one _).2 hI.1).elim H },
  { rw pow_succ at H, exact or.cases_on (hI.mem_or_mem H) id ih }
end

lemma not_is_prime_iff {I : ideal α} : ¬ I.is_prime ↔ I = ⊤ ∨ ∃ (x ∉ I) (y ∉ I), x * y ∈ I :=
begin
  simp_rw [ideal.is_prime_iff, not_and_distrib, ne.def, not_not, not_forall, not_or_distrib],
  exact or_congr iff.rfl
    ⟨λ ⟨x, y, hxy, hx, hy⟩, ⟨x, hx, y, hy, hxy⟩, λ ⟨x, hx, y, hy, hxy⟩, ⟨x, y, hxy, hx, hy⟩⟩
end

theorem zero_ne_one_of_proper {I : ideal α} (h : I ≠ ⊤) : (0:α) ≠ 1 :=
λ hz, I.ne_top_iff_one.1 h $ hz ▸ I.zero_mem

lemma bot_prime {R : Type*} [ring R] [is_domain R] : (⊥ : ideal R).is_prime :=
⟨λ h, one_ne_zero (by rwa [ideal.eq_top_iff_one, submodule.mem_bot] at h),
 λ x y h, mul_eq_zero.mp (by simpa only [submodule.mem_bot] using h)⟩

/-- An ideal is maximal if it is maximal in the collection of proper ideals. -/
class is_maximal (I : ideal α) : Prop := (out : is_coatom I)

theorem is_maximal_def {I : ideal α} : I.is_maximal ↔ is_coatom I := ⟨λ h, h.1, λ h, ⟨h⟩⟩

theorem is_maximal.ne_top {I : ideal α} (h : I.is_maximal) : I ≠ ⊤ := (is_maximal_def.1 h).1

theorem is_maximal_iff {I : ideal α} : I.is_maximal ↔
  (1:α) ∉ I ∧ ∀ (J : ideal α) x, I ≤ J → x ∉ I → x ∈ J → (1:α) ∈ J :=
is_maximal_def.trans $ and_congr I.ne_top_iff_one $ forall_congr $ λ J,
by rw [lt_iff_le_not_le]; exact
 ⟨λ H x h hx₁ hx₂, J.eq_top_iff_one.1 $
    H ⟨h, not_subset.2 ⟨_, hx₂, hx₁⟩⟩,
  λ H ⟨h₁, h₂⟩, let ⟨x, xJ, xI⟩ := not_subset.1 h₂ in
   J.eq_top_iff_one.2 $ H x h₁ xI xJ⟩

theorem is_maximal.eq_of_le {I J : ideal α}
  (hI : I.is_maximal) (hJ : J ≠ ⊤) (IJ : I ≤ J) : I = J :=
eq_iff_le_not_lt.2 ⟨IJ, λ h, hJ (hI.1.2 _ h)⟩

instance : is_coatomic (ideal α) :=
begin
  apply complete_lattice.coatomic_of_top_compact,
  rw ←span_singleton_one,
  exact submodule.singleton_span_is_compact_element 1,
end

lemma is_maximal.coprime_of_ne {M M' : ideal α} (hM : M.is_maximal) (hM' : M'.is_maximal)
  (hne : M ≠ M') : M ⊔ M' = ⊤ :=
begin
  contrapose! hne with h,
  exact hM.eq_of_le hM'.ne_top (le_sup_left.trans_eq (hM'.eq_of_le h le_sup_right).symm)
end

/-- **Krull's theorem**: if `I` is an ideal that is not the whole ring, then it is included in some
    maximal ideal. -/
theorem exists_le_maximal (I : ideal α) (hI : I ≠ ⊤) :
  ∃ M : ideal α, M.is_maximal ∧ I ≤ M :=
let ⟨m, hm⟩ := (eq_top_or_exists_le_coatom I).resolve_left hI in ⟨m, ⟨⟨hm.1⟩, hm.2⟩⟩

variables (α)

/-- Krull's theorem: a nontrivial ring has a maximal ideal. -/
theorem exists_maximal [nontrivial α] : ∃ M : ideal α, M.is_maximal :=
let ⟨I, ⟨hI, _⟩⟩ := exists_le_maximal (⊥ : ideal α) bot_ne_top in ⟨I, hI⟩

variables {α}

instance [nontrivial α] : nontrivial (ideal α) :=
begin
  rcases @exists_maximal α _ _ with ⟨M, hM, _⟩,
  exact nontrivial_of_ne M ⊤ hM
end

/-- If P is not properly contained in any maximal ideal then it is not properly contained
  in any proper ideal -/
lemma maximal_of_no_maximal {R : Type u} [semiring R] {P : ideal R}
(hmax : ∀ m : ideal R, P < m → ¬is_maximal m) (J : ideal R) (hPJ : P < J) : J = ⊤ :=
begin
  by_contradiction hnonmax,
  rcases exists_le_maximal J hnonmax with ⟨M, hM1, hM2⟩,
  exact hmax M (lt_of_lt_of_le hPJ hM2) hM1,
end

lemma span_pair_comm {x y : α} : (span {x, y} : ideal α) = span {y, x} :=
by simp only [span_insert, sup_comm]

theorem mem_span_pair {x y z : α} :
  z ∈ span ({x, y} : set α) ↔ ∃ a b, a * x + b * y = z :=
submodule.mem_span_pair

@[simp] lemma span_pair_add_mul_left {R : Type u} [comm_ring R] {x y : R} (z : R) :
  (span {x + y * z, y} : ideal R) = span {x, y} :=
begin
  ext,
  rw [mem_span_pair, mem_span_pair],
  exact ⟨λ ⟨a, b, h⟩, ⟨a, b + a * z, by { rw [← h], ring1 }⟩,
         λ ⟨a, b, h⟩, ⟨a, b - a * z, by { rw [← h], ring1 }⟩⟩
end

@[simp] lemma span_pair_add_mul_right {R : Type u} [comm_ring R] {x y : R} (z : R) :
  (span {x, y + x * z} : ideal R) = span {x, y} :=
by rw [span_pair_comm, span_pair_add_mul_left, span_pair_comm]

theorem is_maximal.exists_inv {I : ideal α}
  (hI : I.is_maximal) {x} (hx : x ∉ I) : ∃ y, ∃ i ∈ I, y * x + i = 1 :=
begin
  cases is_maximal_iff.1 hI with H₁ H₂,
  rcases mem_span_insert.1 (H₂ (span (insert x I)) x
    (set.subset.trans (subset_insert _ _) subset_span)
    hx (subset_span (mem_insert _ _))) with ⟨y, z, hz, hy⟩,
  refine ⟨y, z, _, hy.symm⟩,
  rwa ← span_eq I,
end

section lattice
variables {R : Type u} [semiring R]

lemma mem_sup_left {S T : ideal R} : ∀ {x : R}, x ∈ S → x ∈ S ⊔ T :=
show S ≤ S ⊔ T, from le_sup_left

lemma mem_sup_right {S T : ideal R} : ∀ {x : R}, x ∈ T → x ∈ S ⊔ T :=
show T ≤ S ⊔ T, from le_sup_right

lemma mem_supr_of_mem {ι : Sort*} {S : ι → ideal R} (i : ι) :
  ∀ {x : R}, x ∈ S i → x ∈ supr S :=
show S i ≤ supr S, from le_supr _ _

lemma mem_Sup_of_mem {S : set (ideal R)} {s : ideal R}
  (hs : s ∈ S) : ∀ {x : R}, x ∈ s → x ∈ Sup S :=
show s ≤ Sup S, from le_Sup hs

theorem mem_Inf {s : set (ideal R)} {x : R} :
  x ∈ Inf s ↔ ∀ ⦃I⦄, I ∈ s → x ∈ I :=
⟨λ hx I his, hx I ⟨I, infi_pos his⟩, λ H I ⟨J, hij⟩, hij ▸ λ S ⟨hj, hS⟩, hS ▸ H hj⟩

@[simp] lemma mem_inf {I J : ideal R} {x : R} : x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J := iff.rfl

@[simp] lemma mem_infi {ι : Sort*} {I : ι → ideal R} {x : R} : x ∈ infi I ↔ ∀ i, x ∈ I i :=
submodule.mem_infi _

@[simp] lemma mem_bot {x : R} : x ∈ (⊥ : ideal R) ↔ x = 0 :=
submodule.mem_bot _

end lattice

section pi
variables (ι : Type v)

/-- `I^n` as an ideal of `R^n`. -/
def pi : ideal (ι → α) :=
{ carrier := { x | ∀ i, x i ∈ I },
  zero_mem' := λ i, I.zero_mem,
  add_mem' := λ a b ha hb i, I.add_mem (ha i) (hb i),
  smul_mem' := λ a b hb i, I.mul_mem_left (a i) (hb i) }

lemma mem_pi (x : ι → α) : x ∈ I.pi ι ↔ ∀ i, x i ∈ I := iff.rfl

end pi

lemma Inf_is_prime_of_is_chain {s : set (ideal α)} (hs : s.nonempty) (hs' : is_chain (≤) s)
  (H : ∀ p ∈ s, ideal.is_prime p) :
  (Inf s).is_prime :=
⟨λ e, let ⟨x, hx⟩ := hs in (H x hx).ne_top (eq_top_iff.mpr (e.symm.trans_le (Inf_le hx))),
  λ x y e, or_iff_not_imp_left.mpr $ λ hx, begin
    rw ideal.mem_Inf at hx ⊢ e,
    push_neg at hx,
    obtain ⟨I, hI, hI'⟩ := hx,
    intros J hJ,
    cases hs'.total hI hJ,
    { exact h (((H I hI).mem_or_mem (e hI)).resolve_left hI') },
    { exact ((H J hJ).mem_or_mem (e hJ)).resolve_left (λ x, hI' $ h x) },
  end⟩

end ideal

end semiring

section comm_semiring

variables {a b : α}

-- A separate namespace definition is needed because the variables were historically in a different
-- order.
namespace ideal
variables [comm_semiring α] (I : ideal α)

@[simp]
theorem mul_unit_mem_iff_mem {x y : α} (hy : is_unit y) : x * y ∈ I ↔ x ∈ I :=
mul_comm y x ▸ unit_mul_mem_iff_mem I hy

lemma mem_span_singleton {x y : α} : x ∈ span ({y} : set α) ↔ y ∣ x :=
mem_span_singleton'.trans $ exists_congr $ λ _, by rw [eq_comm, mul_comm]

lemma mem_span_singleton_self (x : α) : x ∈ span ({x} : set α) := mem_span_singleton.mpr dvd_rfl

lemma span_singleton_le_span_singleton {x y : α} :
  span ({x} : set α) ≤ span ({y} : set α) ↔ y ∣ x :=
span_le.trans $ singleton_subset_iff.trans mem_span_singleton

lemma span_singleton_eq_span_singleton {α : Type u} [comm_ring α] [is_domain α] {x y : α} :
  span ({x} : set α) = span ({y} : set α) ↔ associated x y :=
begin
  rw [←dvd_dvd_iff_associated, le_antisymm_iff, and_comm],
  apply and_congr;
  rw span_singleton_le_span_singleton,
end

lemma span_singleton_mul_right_unit {a : α} (h2 : is_unit a) (x : α) :
  span ({x * a} : set α) = span {x} := by rw [mul_comm, span_singleton_mul_left_unit h2]

lemma span_singleton_eq_top {x} : span ({x} : set α) = ⊤ ↔ is_unit x :=
by rw [is_unit_iff_dvd_one, ← span_singleton_le_span_singleton, span_singleton_one,
  eq_top_iff]

theorem span_singleton_prime {p : α} (hp : p ≠ 0) :
  is_prime (span ({p} : set α)) ↔ prime p :=
by simp [is_prime_iff, prime, span_singleton_eq_top, hp, mem_span_singleton]

theorem is_maximal.is_prime {I : ideal α} (H : I.is_maximal) : I.is_prime :=
⟨H.1.1, λ x y hxy, or_iff_not_imp_left.2 $ λ hx, begin
  let J : ideal α := submodule.span α (insert x ↑I),
  have IJ : I ≤ J  := (set.subset.trans (subset_insert _ _) subset_span),
  have xJ : x ∈ J := ideal.subset_span (set.mem_insert x I),
  cases is_maximal_iff.1 H with _ oJ,
  specialize oJ J x IJ hx xJ,
  rcases submodule.mem_span_insert.mp oJ with ⟨a, b, h, oe⟩,
  obtain (F : y * 1 = y * (a • x + b)) := congr_arg (λ g : α, y * g) oe,
  rw [← mul_one y, F, mul_add, mul_comm, smul_eq_mul, mul_assoc],
  refine submodule.add_mem I (I.mul_mem_left a hxy) (submodule.smul_mem I y _),
  rwa submodule.span_eq at h,
end⟩

@[priority 100] -- see Note [lower instance priority]
instance is_maximal.is_prime' (I : ideal α) : ∀ [H : I.is_maximal], I.is_prime :=
is_maximal.is_prime

lemma span_singleton_lt_span_singleton [comm_ring β] [is_domain β] {x y : β} :
  span ({x} : set β) < span ({y} : set β) ↔ dvd_not_unit y x :=
by rw [lt_iff_le_not_le, span_singleton_le_span_singleton, span_singleton_le_span_singleton,
  dvd_and_not_dvd_iff]

lemma factors_decreasing [comm_ring β] [is_domain β]
  (b₁ b₂ : β) (h₁ : b₁ ≠ 0) (h₂ : ¬ is_unit b₂) :
  span ({b₁ * b₂} : set β) < span {b₁} :=
lt_of_le_not_le (ideal.span_le.2 $ singleton_subset_iff.2 $
  ideal.mem_span_singleton.2 ⟨b₂, rfl⟩) $ λ h,
h₂ $ is_unit_of_dvd_one _ $ (mul_dvd_mul_iff_left h₁).1 $
by rwa [mul_one, ← ideal.span_singleton_le_span_singleton]

variables (b)
lemma mul_mem_right (h : a ∈ I) : a * b ∈ I := mul_comm b a ▸ I.mul_mem_left b h
variables {b}

lemma pow_mem_of_mem (ha : a ∈ I) (n : ℕ) (hn : 0 < n) : a ^ n ∈ I :=
nat.cases_on n (not.elim dec_trivial) (λ m hm, (pow_succ a m).symm ▸ I.mul_mem_right (a^m) ha) hn

theorem is_prime.mul_mem_iff_mem_or_mem {I : ideal α} (hI : I.is_prime) :
  ∀ {x y : α}, x * y ∈ I ↔ x ∈ I ∨ y ∈ I :=
λ x y, ⟨hI.mem_or_mem, by { rintro (h | h), exacts [I.mul_mem_right y h, I.mul_mem_left x h] }⟩

theorem is_prime.pow_mem_iff_mem {I : ideal α} (hI : I.is_prime)
  {r : α} (n : ℕ) (hn : 0 < n) : r ^ n ∈ I ↔ r ∈ I :=
⟨hI.mem_of_pow_mem n, (λ hr, I.pow_mem_of_mem hr n hn)⟩

theorem pow_multiset_sum_mem_span_pow (s : multiset α) (n : ℕ) :
  s.sum ^ (s.card * n + 1) ∈ span ((s.map (λ x, x ^ (n + 1))).to_finset : set α) :=
begin
  induction s using multiset.induction_on with a s hs,
  { simp },
  simp only [finset.coe_insert, multiset.map_cons, multiset.to_finset_cons, multiset.sum_cons,
    multiset.card_cons, add_pow],
  refine submodule.sum_mem _ _,
  intros c hc,
  rw mem_span_insert,
  by_cases h : n+1 ≤ c,
  { refine ⟨a ^ (c - (n + 1)) * s.sum ^ ((s.card + 1) * n + 1 - c) *
      (((s.card + 1) * n + 1).choose c), 0, submodule.zero_mem _, _⟩,
    rw mul_comm _ (a ^ (n + 1)),
    simp_rw ← mul_assoc,
    rw [← pow_add, add_zero, add_tsub_cancel_of_le h], },
  { use 0,
    simp_rw [zero_mul, zero_add],
    refine ⟨_,_,rfl⟩,
    replace h : c ≤ n := nat.lt_succ_iff.mp (not_le.mp h),
    have : (s.card + 1) * n + 1 - c = s.card * n + 1 + (n - c),
    { rw [add_mul, one_mul, add_assoc, add_comm n 1, ← add_assoc, add_tsub_assoc_of_le h] },
    rw [this, pow_add],
    simp_rw [mul_assoc, mul_comm (s.sum ^ (s.card * n + 1)), ← mul_assoc],
    exact mul_mem_left _ _ hs }
end

theorem sum_pow_mem_span_pow {ι} (s : finset ι) (f : ι → α) (n : ℕ) :
  (∑ i in s, f i) ^ (s.card * n + 1) ∈ span ((λ i, f i ^ (n + 1)) '' s) :=
begin
  convert pow_multiset_sum_mem_span_pow (s.1.map f) n,
  { rw multiset.card_map, refl },
  rw [multiset.map_map, multiset.to_finset_map, finset.val_to_finset, finset.coe_image]
end

theorem span_pow_eq_top (s : set α)
  (hs : span s = ⊤) (n : ℕ) : span ((λ x, x ^ n) '' s) = ⊤ :=
begin
  rw eq_top_iff_one,
  cases n,
  { obtain rfl | ⟨x, hx⟩ := eq_empty_or_nonempty s,
    { rw [set.image_empty, hs],
      trivial },
    { exact subset_span ⟨_, hx, pow_zero _⟩ } },
  rw [eq_top_iff_one, span, finsupp.mem_span_iff_total] at hs,
  rcases hs with ⟨f, hf⟩,
  change f.support.sum (λ a, f a * a) = 1 at hf,
  have := sum_pow_mem_span_pow f.support (λ a, f a * a) n,
  rw [hf, one_pow] at this,
  refine (span_le).mpr _ this,
  rintros _ hx,
  simp_rw [finset.mem_coe, set.mem_image] at hx,
  rcases hx with ⟨x, hx, rfl⟩,
  have : span ({x ^ (n + 1)} : set α) ≤ span ((λ (x : α), x ^ (n + 1)) '' s),
  { rw [span_le, set.singleton_subset_iff],
    exact subset_span ⟨x, x.prop, rfl⟩ },
  refine this _,
  rw [mul_pow, mem_span_singleton],
  exact ⟨f x ^ (n + 1), mul_comm _ _⟩
end

end ideal

end comm_semiring

section ring

namespace ideal

variables [ring α] (I : ideal α) {a b : α}

protected lemma neg_mem_iff : -a ∈ I ↔ a ∈ I := neg_mem_iff
protected lemma add_mem_iff_left : b ∈ I → (a + b ∈ I ↔ a ∈ I) := I.add_mem_iff_left
protected lemma add_mem_iff_right : a ∈ I → (a + b ∈ I ↔ b ∈ I) := I.add_mem_iff_right
protected lemma sub_mem : a ∈ I → b ∈ I → a - b ∈ I := sub_mem

lemma mem_span_insert' {s : set α} {x y} :
  x ∈ span (insert y s) ↔ ∃a, x + a * y ∈ span s := submodule.mem_span_insert'

@[simp] lemma span_singleton_neg (x : α) : (span {-x} : ideal α) = span {x} :=
by { ext, simp only [mem_span_singleton'],
     exact ⟨λ ⟨y, h⟩, ⟨-y, h ▸ neg_mul_comm y x⟩, λ ⟨y, h⟩, ⟨-y, h ▸ neg_mul_neg y x⟩⟩ }

end ideal

end ring

section division_semiring
variables {K : Type u} [division_semiring K] (I : ideal K)

namespace ideal

/-- All ideals in a division (semi)ring are trivial. -/
lemma eq_bot_or_top : I = ⊥ ∨ I = ⊤ :=
begin
  rw or_iff_not_imp_right,
  change _ ≠ _ → _,
  rw ideal.ne_top_iff_one,
  intro h1,
  rw eq_bot_iff,
  intros r hr,
  by_cases H : r = 0, {simpa},
  simpa [H, h1] using I.mul_mem_left r⁻¹ hr,
end

/-- Ideals of a `division_semiring` are a simple order. Thanks to the way abbreviations work,
this automatically gives a `is_simple_module K` instance. -/
instance : is_simple_order (ideal K) := ⟨eq_bot_or_top⟩

lemma eq_bot_of_prime [h : I.is_prime] : I = ⊥ :=
or_iff_not_imp_right.mp I.eq_bot_or_top h.1

lemma bot_is_maximal : is_maximal (⊥ : ideal K) :=
⟨⟨λ h, absurd ((eq_top_iff_one (⊤ : ideal K)).mp rfl) (by rw ← h; simp),
λ I hI, or_iff_not_imp_left.mp (eq_bot_or_top I) (ne_of_gt hI)⟩⟩

end ideal

end division_semiring

section comm_ring

namespace ideal

theorem mul_sub_mul_mem {R : Type*} [comm_ring R] (I : ideal R) {a b c d : R}
  (h1 : a - b ∈ I) (h2 : c - d ∈ I) : a * c - b * d ∈ I :=
begin
  rw (show a * c - b * d = (a - b) * c + b * (c - d), by {rw [sub_mul, mul_sub], abel}),
  exact I.add_mem (I.mul_mem_right _ h1) (I.mul_mem_left _ h2),
end

end ideal

end comm_ring

-- TODO: consider moving the lemmas below out of the `ring` namespace since they are
-- about `comm_semiring`s.
namespace ring

variables {R : Type*} [comm_semiring R]

lemma exists_not_is_unit_of_not_is_field [nontrivial R] (hf : ¬ is_field R) :
  ∃ x ≠ (0 : R), ¬ is_unit x :=
begin
  have : ¬ _ := λ h, hf ⟨exists_pair_ne R, mul_comm, h⟩,
  simp_rw is_unit_iff_exists_inv,
  push_neg at ⊢ this,
  obtain ⟨x, hx, not_unit⟩ := this,
  exact ⟨x, hx, not_unit⟩
end

lemma not_is_field_iff_exists_ideal_bot_lt_and_lt_top [nontrivial R] :
  ¬ is_field R ↔ ∃ I : ideal R, ⊥ < I ∧ I < ⊤ :=
begin
  split,
  { intro h,
    obtain ⟨x, nz, nu⟩ := exists_not_is_unit_of_not_is_field h,
    use ideal.span {x},
    rw [bot_lt_iff_ne_bot, lt_top_iff_ne_top],
    exact ⟨mt ideal.span_singleton_eq_bot.mp nz, mt ideal.span_singleton_eq_top.mp nu⟩ },
  { rintros ⟨I, bot_lt, lt_top⟩ hf,
    obtain ⟨x, mem, ne_zero⟩ := set_like.exists_of_lt bot_lt,
    rw submodule.mem_bot at ne_zero,
    obtain ⟨y, hy⟩ := hf.mul_inv_cancel ne_zero,
    rw [lt_top_iff_ne_top, ne.def, ideal.eq_top_iff_one, ← hy] at lt_top,
    exact lt_top (I.mul_mem_right _ mem), }
end

lemma not_is_field_iff_exists_prime [nontrivial R] :
  ¬ is_field R ↔ ∃ p : ideal R, p ≠ ⊥ ∧ p.is_prime :=
not_is_field_iff_exists_ideal_bot_lt_and_lt_top.trans
  ⟨λ ⟨I, bot_lt, lt_top⟩, let ⟨p, hp, le_p⟩ := I.exists_le_maximal (lt_top_iff_ne_top.mp lt_top) in
    ⟨p, bot_lt_iff_ne_bot.mp (lt_of_lt_of_le bot_lt le_p), hp.is_prime⟩,
   λ ⟨p, ne_bot, prime⟩, ⟨p, bot_lt_iff_ne_bot.mpr ne_bot, lt_top_iff_ne_top.mpr prime.1⟩⟩

/-- Also see `ideal.is_simple_order` for the forward direction as an instance when `R` is a
division (semi)ring. 

This result actually holds for all division semirings, but we lack the predicate to state it. -/
lemma is_field_iff_is_simple_order_ideal :
  is_field R ↔ is_simple_order (ideal R) :=
begin
  casesI subsingleton_or_nontrivial R,
  { exact ⟨λ h, (not_is_field_of_subsingleton _ h).elim,
      λ h, by exactI (false_of_nontrivial_of_subsingleton $ ideal R).elim⟩ },
  rw [← not_iff_not, ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top, ← not_iff_not],
  push_neg,
  simp_rw [lt_top_iff_ne_top, bot_lt_iff_ne_bot, ← or_iff_not_imp_left, not_ne_iff],
  exact ⟨λ h, ⟨h⟩, λ h, h.2⟩
end

/-- When a ring is not a field, the maximal ideals are nontrivial. -/
lemma ne_bot_of_is_maximal_of_not_is_field [nontrivial R] {M : ideal R} (max : M.is_maximal)
  (not_field : ¬ is_field R) : M ≠ ⊥ :=
begin
  rintros h,
  rw h at max,
  rcases max with ⟨⟨h1, h2⟩⟩,
  obtain ⟨I, hIbot, hItop⟩ := not_is_field_iff_exists_ideal_bot_lt_and_lt_top.mp not_field,
  exact ne_of_lt hItop (h2 I hIbot),
end

end ring

namespace ideal

/-- Maximal ideals in a non-field are nontrivial. -/
variables {R : Type u} [comm_ring R] [nontrivial R]
lemma bot_lt_of_maximal (M : ideal R) [hm : M.is_maximal] (non_field : ¬ is_field R) : ⊥ < M :=
begin
  rcases (ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top.1 non_field)
    with ⟨I, Ibot, Itop⟩,
  split, { simp },
  intro mle,
  apply @irrefl _ (<) _ (⊤ : ideal R),
  have : M = ⊥ := eq_bot_iff.mpr mle,
  rw this at *,
  rwa hm.1.2 I Ibot at Itop,
end

end ideal

variables {a b : α}

/-- The set of non-invertible elements of a monoid. -/
def nonunits (α : Type u) [monoid α] : set α := { a | ¬is_unit a }

@[simp] theorem mem_nonunits_iff [monoid α] : a ∈ nonunits α ↔ ¬ is_unit a := iff.rfl

theorem mul_mem_nonunits_right [comm_monoid α] :
  b ∈ nonunits α → a * b ∈ nonunits α :=
mt is_unit_of_mul_is_unit_right

theorem mul_mem_nonunits_left [comm_monoid α] :
  a ∈ nonunits α → a * b ∈ nonunits α :=
mt is_unit_of_mul_is_unit_left

theorem zero_mem_nonunits [semiring α] : 0 ∈ nonunits α ↔ (0:α) ≠ 1 :=
not_congr is_unit_zero_iff

@[simp] theorem one_not_mem_nonunits [monoid α] : (1:α) ∉ nonunits α :=
not_not_intro is_unit_one

theorem coe_subset_nonunits [semiring α] {I : ideal α} (h : I ≠ ⊤) :
  (I : set α) ⊆ nonunits α :=
λ x hx hu, h $ I.eq_top_of_is_unit_mem hx hu

lemma exists_max_ideal_of_mem_nonunits [comm_semiring α] (h : a ∈ nonunits α) :
  ∃ I : ideal α, I.is_maximal ∧ a ∈ I :=
begin
  have : ideal.span ({a} : set α) ≠ ⊤,
  { intro H, rw ideal.span_singleton_eq_top at H, contradiction },
  rcases ideal.exists_le_maximal _ this with ⟨I, Imax, H⟩,
  use [I, Imax], apply H, apply ideal.subset_span, exact set.mem_singleton a
end
