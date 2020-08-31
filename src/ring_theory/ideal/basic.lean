/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import algebra.associated
import linear_algebra.basic
import order.zorn
/-!

# Ideals over a ring

This file defines `ideal R`, the type of ideals over a commutative ring `R`.

## Implementation notes

`ideal R` is implemented using `submodule R R`, where `•` is interpreted as `*`.

## TODO

Support one-sided ideals, and ideals over non-commutative rings
-/

universes u v w
variables {α : Type u} {β : Type v}
open set function

open_locale classical big_operators

/-- Ideal in a commutative ring is an additive subgroup `s` such that
`a * b ∈ s` whenever `b ∈ s`. -/
@[reducible] def ideal (R : Type u) [comm_ring R] := submodule R R

namespace ideal
variables [comm_ring α] (I : ideal α) {a b : α}

protected lemma zero_mem : (0 : α) ∈ I := I.zero_mem

protected lemma add_mem : a ∈ I → b ∈ I → a + b ∈ I := I.add_mem

lemma neg_mem_iff : -a ∈ I ↔ a ∈ I := I.neg_mem_iff

lemma add_mem_iff_left : b ∈ I → (a + b ∈ I ↔ a ∈ I) := I.add_mem_iff_left

lemma add_mem_iff_right : a ∈ I → (a + b ∈ I ↔ b ∈ I) := I.add_mem_iff_right

protected lemma sub_mem : a ∈ I → b ∈ I → a - b ∈ I := I.sub_mem

lemma mul_mem_left : b ∈ I → a * b ∈ I := I.smul_mem _

lemma mul_mem_right (h : a ∈ I) : a * b ∈ I := mul_comm b a ▸ I.mul_mem_left h
end ideal

variables {a b : α}

-- A separate namespace definition is needed because the variables were historically in a different order
namespace ideal
variables [comm_ring α] (I : ideal α)

@[ext] lemma ext {I J : ideal α} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
submodule.ext h

theorem eq_top_of_unit_mem
  (x y : α) (hx : x ∈ I) (h : y * x = 1) : I = ⊤ :=
eq_top_iff.2 $ λ z _, calc
    z = z * (y * x) : by simp [h]
  ... = (z * y) * x : eq.symm $ mul_assoc z y x
  ... ∈ I : I.mul_mem_left hx

theorem eq_top_of_is_unit_mem {x} (hx : x ∈ I) (h : is_unit x) : I = ⊤ :=
let ⟨y, hy⟩ := is_unit_iff_exists_inv'.1 h in eq_top_of_unit_mem I x y hx hy

theorem eq_top_iff_one : I = ⊤ ↔ (1:α) ∈ I :=
⟨by rintro rfl; trivial,
 λ h, eq_top_of_unit_mem _ _ 1 h (by simp)⟩

theorem ne_top_iff_one : I ≠ ⊤ ↔ (1:α) ∉ I :=
not_congr I.eq_top_iff_one

@[simp]
theorem unit_mul_mem_iff_mem {x y : α} (hy : is_unit y) : y * x ∈ I ↔ x ∈ I :=
begin
  refine ⟨λ h, _, λ h,  I.smul_mem y h⟩,
  obtain ⟨y', hy'⟩ := is_unit_iff_exists_inv.1 hy,
  have := I.smul_mem y' h,
  rwa [smul_eq_mul, ← mul_assoc, mul_comm y' y, hy', one_mul] at this,
end

@[simp]
theorem mul_unit_mem_iff_mem {x y : α} (hy : is_unit y) : x * y ∈ I ↔ x ∈ I :=
mul_comm y x ▸ unit_mul_mem_iff_mem I hy

/-- The ideal generated by a subset of a ring -/
def span (s : set α) : ideal α := submodule.span α s

lemma subset_span {s : set α} : s ⊆ span s := submodule.subset_span

lemma span_le {s : set α} {I} : span s ≤ I ↔ s ⊆ I := submodule.span_le

lemma span_mono {s t : set α} : s ⊆ t → span s ≤ span t := submodule.span_mono

@[simp] lemma span_eq : span (I : set α) = I := submodule.span_eq _

@[simp] lemma span_singleton_one : span (1 : set α) = ⊤ :=
(eq_top_iff_one _).2 $ subset_span $ mem_singleton _

lemma mem_span_insert {s : set α} {x y} :
  x ∈ span (insert y s) ↔ ∃ a (z ∈ span s), x = a * y + z := submodule.mem_span_insert

lemma mem_span_insert' {s : set α} {x y} :
  x ∈ span (insert y s) ↔ ∃a, x + a * y ∈ span s := submodule.mem_span_insert'

lemma mem_span_singleton' {x y : α} :
  x ∈ span ({y} : set α) ↔ ∃ a, a * y = x := submodule.mem_span_singleton

lemma mem_span_singleton {x y : α} :
  x ∈ span ({y} : set α) ↔ y ∣ x :=
mem_span_singleton'.trans $ exists_congr $ λ _, by rw [eq_comm, mul_comm]

lemma span_singleton_le_span_singleton {x y : α} :
  span ({x} : set α) ≤ span ({y} : set α) ↔ y ∣ x :=
span_le.trans $ singleton_subset_iff.trans mem_span_singleton

lemma span_singleton_eq_span_singleton {α : Type u} [integral_domain α] {x y : α} :
  span ({x} : set α) = span ({y} : set α) ↔ associated x y :=
begin
  rw [←dvd_dvd_iff_associated, le_antisymm_iff, and_comm],
  apply and_congr;
  rw span_singleton_le_span_singleton,
end

lemma span_eq_bot {s : set α} : span s = ⊥ ↔ ∀ x ∈ s, (x:α) = 0 := submodule.span_eq_bot

@[simp] lemma span_singleton_eq_bot {x} : span ({x} : set α) = ⊥ ↔ x = 0 :=
submodule.span_singleton_eq_bot

@[simp] lemma span_zero : span (0 : set α) = ⊥ := by rw [←set.singleton_zero, span_singleton_eq_bot]

lemma span_singleton_eq_top {x} : span ({x} : set α) = ⊤ ↔ is_unit x :=
by rw [is_unit_iff_dvd_one, ← span_singleton_le_span_singleton, singleton_one, span_singleton_one,
  eq_top_iff]

lemma span_singleton_mul_right_unit {a : α} (h2 : is_unit a) (x : α) :
  span ({x * a} : set α) = span {x} :=
begin
  apply le_antisymm,
  { rw span_singleton_le_span_singleton, use a},
  { rw span_singleton_le_span_singleton, rw is_unit.mul_right_dvd h2}
end

lemma span_singleton_mul_left_unit {a : α} (h2 : is_unit a) (x : α) :
  span ({a * x} : set α) = span {x} := by rw [mul_comm, span_singleton_mul_right_unit h2]

/-- An ideal `P` of a ring `R` is prime if `P ≠ R` and `xy ∈ P → x ∈ P ∨ y ∈ P` -/
@[class] def is_prime (I : ideal α) : Prop :=
I ≠ ⊤ ∧ ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I

theorem is_prime.mem_or_mem {I : ideal α} (hI : I.is_prime) :
  ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I := hI.2

theorem is_prime.mem_or_mem_of_mul_eq_zero {I : ideal α} (hI : I.is_prime)
  {x y : α} (h : x * y = 0) : x ∈ I ∨ y ∈ I :=
hI.2 (h.symm ▸ I.zero_mem)

theorem is_prime.mem_of_pow_mem {I : ideal α} (hI : I.is_prime)
  {r : α} (n : ℕ) (H : r^n ∈ I) : r ∈ I :=
begin
  induction n with n ih,
  { exact (mt (eq_top_iff_one _).2 hI.1).elim H },
  exact or.cases_on (hI.mem_or_mem H) id ih
end

theorem zero_ne_one_of_proper {I : ideal α} (h : I ≠ ⊤) : (0:α) ≠ 1 :=
λ hz, I.ne_top_iff_one.1 h $ hz ▸ I.zero_mem

theorem span_singleton_prime {p : α} (hp : p ≠ 0) :
  is_prime (span ({p} : set α)) ↔ prime p :=
by simp [is_prime, prime, span_singleton_eq_top, hp, mem_span_singleton]

lemma bot_prime {R : Type*} [integral_domain R] : (⊥ : ideal R).is_prime :=
⟨λ h, one_ne_zero (by rwa [ideal.eq_top_iff_one, submodule.mem_bot] at h),
 λ x y h, mul_eq_zero.mp (by simpa only [submodule.mem_bot] using h)⟩

/-- An ideal is maximal if it is maximal in the collection of proper ideals. -/
@[class] def is_maximal (I : ideal α) : Prop :=
I ≠ ⊤ ∧ ∀ J, I < J → J = ⊤

theorem is_maximal_iff {I : ideal α} : I.is_maximal ↔
  (1:α) ∉ I ∧ ∀ (J : ideal α) x, I ≤ J → x ∉ I → x ∈ J → (1:α) ∈ J :=
and_congr I.ne_top_iff_one $ forall_congr $ λ J,
by rw [lt_iff_le_not_le]; exact
 ⟨λ H x h hx₁ hx₂, J.eq_top_iff_one.1 $
    H ⟨h, not_subset.2 ⟨_, hx₂, hx₁⟩⟩,
  λ H ⟨h₁, h₂⟩, let ⟨x, xJ, xI⟩ := not_subset.1 h₂ in
   J.eq_top_iff_one.2 $ H x h₁ xI xJ⟩

theorem is_maximal.eq_of_le {I J : ideal α}
  (hI : I.is_maximal) (hJ : J ≠ ⊤) (IJ : I ≤ J) : I = J :=
eq_iff_le_not_lt.2 ⟨IJ, λ h, hJ (hI.2 _ h)⟩

theorem is_maximal.exists_inv {I : ideal α}
  (hI : I.is_maximal) {x} (hx : x ∉ I) : ∃ y, y * x - 1 ∈ I :=
begin
  cases is_maximal_iff.1 hI with H₁ H₂,
  rcases mem_span_insert'.1 (H₂ (span (insert x I)) x
    (set.subset.trans (subset_insert _ _) subset_span)
    hx (subset_span (mem_insert _ _))) with ⟨y, hy⟩,
  rw [span_eq, ← neg_mem_iff, add_comm, neg_add', neg_mul_eq_neg_mul] at hy,
  exact ⟨-y, hy⟩
end

theorem is_maximal.is_prime {I : ideal α} (H : I.is_maximal) : I.is_prime :=
⟨H.1, λ x y hxy, or_iff_not_imp_left.2 $ λ hx, begin
  cases H.exists_inv hx with z hz,
  have := I.mul_mem_left hz,
  rw [mul_sub, mul_one, mul_comm, mul_assoc] at this,
  exact I.neg_mem_iff.1 ((I.add_mem_iff_right $ I.mul_mem_left hxy).1 this)
end⟩

@[priority 100] -- see Note [lower instance priority]
instance is_maximal.is_prime' (I : ideal α) : ∀ [H : I.is_maximal], I.is_prime :=
is_maximal.is_prime

/-- Krull's theorem: if `I` is an ideal that is not the whole ring, then it is included in some
    maximal ideal. -/
theorem exists_le_maximal (I : ideal α) (hI : I ≠ ⊤) :
  ∃ M : ideal α, M.is_maximal ∧ I ≤ M :=
begin
  rcases zorn.zorn_partial_order₀ { J : ideal α | J ≠ ⊤ } _ I hI with ⟨M, M0, IM, h⟩,
  { refine ⟨M, ⟨M0, λ J hJ, by_contradiction $ λ J0, _⟩, IM⟩,
    cases h J J0 (le_of_lt hJ), exact lt_irrefl _ hJ },
  { intros S SC cC I IS,
    refine ⟨Sup S, λ H, _, λ _, le_Sup⟩,
    obtain ⟨J, JS, J0⟩ : ∃ J ∈ S, (1 : α) ∈ J,
      from (submodule.mem_Sup_of_directed ⟨I, IS⟩ cC.directed_on).1 ((eq_top_iff_one _).1 H),
    exact SC JS ((eq_top_iff_one _).2 J0) }
end

/-- Krull's theorem: a nontrivial ring has a maximal ideal. -/
theorem exists_maximal [nontrivial α] : ∃ M : ideal α, M.is_maximal :=
let ⟨I, ⟨hI, _⟩⟩ := exists_le_maximal (⊥ : ideal α) submodule.bot_ne_top in ⟨I, hI⟩

/-- If P is not properly contained in any maximal ideal then it is not properly contained
  in any proper ideal -/
lemma maximal_of_no_maximal {R : Type u} [comm_ring R] {P : ideal R}
(hmax : ∀ m : ideal R, P < m → ¬is_maximal m) (J : ideal R) (hPJ : P < J) : J = ⊤ :=
begin
  by_contradiction hnonmax,
  rcases exists_le_maximal J hnonmax with ⟨M, hM1, hM2⟩,
  exact hmax M (lt_of_lt_of_le hPJ hM2) hM1,
end

theorem mem_span_pair {x y z : α} :
  z ∈ span ({x, y} : set α) ↔ ∃ a b, a * x + b * y = z :=
by simp [mem_span_insert, mem_span_singleton', @eq_comm _ _ z]

lemma span_singleton_lt_span_singleton [integral_domain β] {x y : β} :
  span ({x} : set β) < span ({y} : set β) ↔ y ≠ 0 ∧ ∃ d : β, ¬ is_unit d ∧ x = y * d :=
by rw [lt_iff_le_not_le, span_singleton_le_span_singleton, span_singleton_le_span_singleton,
  dvd_and_not_dvd_iff]

lemma factors_decreasing [integral_domain β] (b₁ b₂ : β) (h₁ : b₁ ≠ 0) (h₂ : ¬ is_unit b₂) :
  span ({b₁ * b₂} : set β) < span {b₁} :=
lt_of_le_not_le (ideal.span_le.2 $ singleton_subset_iff.2 $
  ideal.mem_span_singleton.2 ⟨b₂, rfl⟩) $ λ h,
h₂ $ is_unit_of_dvd_one _ $ (mul_dvd_mul_iff_left h₁).1 $
by rwa [mul_one, ← ideal.span_singleton_le_span_singleton]

/-- The quotient `R/I` of a ring `R` by an ideal `I`. -/
def quotient (I : ideal α) := I.quotient

namespace quotient
variables {I} {x y : α}

instance (I : ideal α) : has_one I.quotient := ⟨submodule.quotient.mk 1⟩

instance (I : ideal α) : has_mul I.quotient :=
⟨λ a b, quotient.lift_on₂' a b (λ a b, submodule.quotient.mk (a * b)) $
 λ a₁ a₂ b₁ b₂ h₁ h₂, quot.sound $ begin
  refine calc a₁ * a₂ - b₁ * b₂ = a₂ * (a₁ - b₁) + (a₂ - b₂) * b₁ : _
  ... ∈ I : I.add_mem (I.mul_mem_left h₁) (I.mul_mem_right h₂),
  rw [mul_sub, sub_mul, sub_add_sub_cancel, mul_comm, mul_comm b₁]
 end⟩

instance (I : ideal α) : comm_ring I.quotient :=
{ mul := (*),
  one := 1,
  mul_assoc := λ a b c, quotient.induction_on₃' a b c $
    λ a b c, congr_arg submodule.quotient.mk (mul_assoc a b c),
  mul_comm := λ a b, quotient.induction_on₂' a b $
    λ a b, congr_arg submodule.quotient.mk (mul_comm a b),
  one_mul := λ a, quotient.induction_on' a $
    λ a, congr_arg submodule.quotient.mk (one_mul a),
  mul_one := λ a, quotient.induction_on' a $
    λ a, congr_arg submodule.quotient.mk (mul_one a),
  left_distrib := λ a b c, quotient.induction_on₃' a b c $
    λ a b c, congr_arg submodule.quotient.mk (left_distrib a b c),
  right_distrib := λ a b c, quotient.induction_on₃' a b c $
    λ a b c, congr_arg submodule.quotient.mk (right_distrib a b c),
  ..submodule.quotient.add_comm_group I }

/-- The ring homomorphism from a ring `R` to a quotient ring `R/I`. -/
def mk (I : ideal α) : α →+* I.quotient :=
⟨λ a, submodule.quotient.mk a, rfl, λ _ _, rfl, rfl, λ _ _, rfl⟩

instance : inhabited (quotient I) := ⟨mk I 37⟩

protected theorem eq : mk I x = mk I y ↔ x - y ∈ I := submodule.quotient.eq I

@[simp] theorem mk_eq_mk (x : α) : (submodule.quotient.mk x : quotient I) = mk I x := rfl

lemma eq_zero_iff_mem {I : ideal α} : mk I a = 0 ↔ a ∈ I :=
by conv {to_rhs, rw ← sub_zero a }; exact quotient.eq'

theorem zero_eq_one_iff {I : ideal α} : (0 : I.quotient) = 1 ↔ I = ⊤ :=
eq_comm.trans $ eq_zero_iff_mem.trans (eq_top_iff_one _).symm

theorem zero_ne_one_iff {I : ideal α} : (0 : I.quotient) ≠ 1 ↔ I ≠ ⊤ :=
not_congr zero_eq_one_iff

protected theorem nontrivial {I : ideal α} (hI : I ≠ ⊤) : nontrivial I.quotient :=
⟨⟨0, 1, zero_ne_one_iff.2 hI⟩⟩

lemma mk_surjective : function.surjective (mk I) :=
λ y, quotient.induction_on' y (λ x, exists.intro x rfl)

instance (I : ideal α) [hI : I.is_prime] : integral_domain I.quotient :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b,
    quotient.induction_on₂' a b $ λ a b hab,
      (hI.mem_or_mem (eq_zero_iff_mem.1 hab)).elim
        (or.inl ∘ eq_zero_iff_mem.2)
        (or.inr ∘ eq_zero_iff_mem.2),
  .. quotient.comm_ring I,
  .. quotient.nontrivial hI.1 }

lemma is_integral_domain_iff_prime (I : ideal α) : is_integral_domain I.quotient ↔ I.is_prime :=
⟨ λ ⟨h1, h2, h3⟩, ⟨zero_ne_one_iff.1 $ @zero_ne_one _ _ ⟨h1⟩, λ x y h,
    by { simp only [←eq_zero_iff_mem, (mk I).map_mul] at ⊢ h, exact h3 _ _ h}⟩,
  λ h, by exactI integral_domain.to_is_integral_domain I.quotient⟩

lemma exists_inv {I : ideal α} [hI : I.is_maximal] :
 ∀ {a : I.quotient}, a ≠ 0 → ∃ b : I.quotient, a * b = 1 :=
begin
  rintro ⟨a⟩ h,
  cases hI.exists_inv (mt eq_zero_iff_mem.2 h) with b hb,
  rw [mul_comm] at hb,
  exact ⟨mk _ b, quot.sound hb⟩
end

/-- quotient by maximal ideal is a field. def rather than instance, since users will have
computable inverses in some applications -/
protected noncomputable def field (I : ideal α) [hI : I.is_maximal] : field I.quotient :=
{ inv := λ a, if ha : a = 0 then 0 else classical.some (exists_inv ha),
  mul_inv_cancel := λ a (ha : a ≠ 0), show a * dite _ _ _ = _,
    by rw dif_neg ha;
    exact classical.some_spec (exists_inv ha),
  inv_zero := dif_pos rfl,
  ..quotient.integral_domain I }

/-- If the quotient by an ideal is a field, then the ideal is maximal
-/
theorem maximal_of_is_field {R : Type u} [comm_ring R] (I : ideal R)
(hqf : @is_field I.quotient (comm_ring.to_ring (ideal.quotient I))) : I.is_maximal :=
begin
  apply ideal.is_maximal_iff.2,
  split,
  { intro h,
      rcases (hqf.exists_pair_ne) with ⟨⟨x⟩, ⟨y⟩, hxy⟩,
      apply hxy,
      apply ideal.quotient.eq.2,
      rw ←mul_one (x-y),
      apply submodule.smul_mem',
      exact h },
  { intros J x hIJ hxnI hxJ,
      have hxn0 : (ideal.quotient.mk I x) ≠ 0,
      { exact @mt ((ideal.quotient.mk I x) = 0) (x ∈ I) ideal.quotient.eq_zero_iff_mem.1 hxnI },
      have hinvx : ∃ (y : I.quotient), (ideal.quotient.mk I x) * y = 1,
      { exact hqf.mul_inv_cancel' hxn0 },
      rcases hinvx with ⟨⟨y⟩, hy⟩,
      change (ideal.quotient.mk I x) * (ideal.quotient.mk I y) = 1 at hy,
      rw ←((ideal.quotient.mk I).map_mul x y) at hy,
      have hxy1I : x*y-1 ∈ I, exact ideal.quotient.eq.1 hy,
      have hxy1J : x*y-1 ∈ J, exact hIJ hxy1I,
      have hxyJ : x*y ∈ J, exact ideal.mul_mem_right J hxJ,
      have hend : x*y-(x*y-1) ∈ J, exact ideal.sub_mem J hxyJ hxy1J,
      have h1 : 1 = x*y-(x*y-1),
        by calc 1 = 0 + 1         : eq.symm (zero_add 1)
              ... = x*y - x*y + 1 : by rw sub_self
              ... = x*y-(x*y-1)   : by rw sub_add,
      rw h1,
      exact hend, }
end

/-- The quotient of a ring by an ideal is a field iff the ideal is maximal.
-/
theorem maximal_ideal_iff_is_field_quotient {R : Type u} [comm_ring R] (I : ideal R) :
I.is_maximal ↔ (@is_field I.quotient (comm_ring.to_ring (ideal.quotient I))) :=
begin
  split; intro h,
  { exact @field.to_is_field I.quotient (@ideal.quotient.field _ _ I h) },
  { exact maximal_of_is_field I h }
end

variable [comm_ring β]

/-- Given a ring homomorphism `f : α →+* β` sending all elements of an ideal to zero,
lift it to the quotient by this ideal. -/
def lift (S : ideal α) (f : α →+* β) (H : ∀ (a : α), a ∈ S → f a = 0) :
  quotient S →+* β :=
{ to_fun := λ x, quotient.lift_on' x f $ λ (a b) (h : _ ∈ _),
    eq_of_sub_eq_zero $ by rw [← f.map_sub, H _ h],
  map_one' := f.map_one,
  map_zero' := f.map_zero,
  map_add' := λ a₁ a₂, quotient.induction_on₂' a₁ a₂ f.map_add,
  map_mul' := λ a₁ a₂, quotient.induction_on₂' a₁ a₂ f.map_mul }

@[simp] lemma lift_mk (S : ideal α) (f : α →+* β) (H : ∀ (a : α), a ∈ S → f a = 0) :
  lift S f H (mk S a) = f a := rfl

end quotient

section lattice
variables {R : Type u} [comm_ring R]

lemma mem_sup_left {S T : ideal R} : ∀ {x : R}, x ∈ S → x ∈ S ⊔ T :=
show S ≤ S ⊔ T, from le_sup_left

lemma mem_sup_right {S T : ideal R} : ∀ {x : R}, x ∈ T → x ∈ S ⊔ T :=
show T ≤ S ⊔ T, from le_sup_right

lemma mem_supr_of_mem {ι : Type*} {S : ι → ideal R} (i : ι) :
  ∀ {x : R}, x ∈ S i → x ∈ supr S :=
show S i ≤ supr S, from le_supr _ _

lemma mem_Sup_of_mem {S : set (ideal R)} {s : ideal R}
  (hs : s ∈ S) : ∀ {x : R}, x ∈ s → x ∈ Sup S :=
show s ≤ Sup S, from le_Sup hs

theorem mem_Inf {s : set (ideal R)} {x : R} :
  x ∈ Inf s ↔ ∀ ⦃I⦄, I ∈ s → x ∈ I :=
⟨λ hx I his, hx I ⟨I, infi_pos his⟩, λ H I ⟨J, hij⟩, hij ▸ λ S ⟨hj, hS⟩, hS ▸ H hj⟩

@[simp] lemma mem_inf {I J : ideal R} {x : R} : x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J := iff.rfl

@[simp] lemma mem_infi {ι : Type*} {I : ι → ideal R} {x : R} : x ∈ infi I ↔ ∀ i, x ∈ I i :=
submodule.mem_infi _

end lattice

/-- All ideals in a field are trivial. -/
lemma eq_bot_or_top {K : Type u} [field K] (I : ideal K) :
  I = ⊥ ∨ I = ⊤ :=
begin
  rw or_iff_not_imp_right,
  change _ ≠ _ → _,
  rw ideal.ne_top_iff_one,
  intro h1,
  rw eq_bot_iff,
  intros r hr,
  by_cases H : r = 0, {simpa},
  simpa [H, h1] using submodule.smul_mem I r⁻¹ hr,
end

lemma eq_bot_of_prime {K : Type u} [field K] (I : ideal K) [h : I.is_prime] :
  I = ⊥ :=
or_iff_not_imp_right.mp I.eq_bot_or_top h.1

lemma bot_is_maximal {K : Type u} [field K] : is_maximal (⊥ : ideal K) :=
⟨λ h, absurd ((eq_top_iff_one (⊤ : ideal K)).mp rfl) (by rw ← h; simp),
λ I hI, or_iff_not_imp_left.mp (eq_bot_or_top I) (ne_of_gt hI)⟩

section pi
variables (ι : Type v)

/-- `I^n` as an ideal of `R^n`. -/
def pi : ideal (ι → α) :=
{ carrier := { x | ∀ i, x i ∈ I },
  zero_mem' := λ i, submodule.zero_mem _,
  add_mem' := λ a b ha hb i, submodule.add_mem _ (ha i) (hb i),
  smul_mem' := λ a b hb i, ideal.mul_mem_left _ (hb i) }

lemma mem_pi (x : ι → α) : x ∈ I.pi ι ↔ ∀ i, x i ∈ I := iff.rfl

/-- `R^n/I^n` is a `R/I`-module. -/
instance module_pi : module (I.quotient) (I.pi ι).quotient :=
begin
  refine { smul := λ c m, quotient.lift_on₂' c m (λ r m, submodule.quotient.mk $ r • m) _, .. },
  { intros c₁ m₁ c₂ m₂ hc hm,
    change c₁ - c₂ ∈ I at hc,
    change m₁ - m₂ ∈ (I.pi ι) at hm,
    apply ideal.quotient.eq.2,
    have : c₁ • (m₂ - m₁) ∈ I.pi ι,
    { rw ideal.mem_pi,
      intro i,
      simp only [smul_eq_mul, pi.smul_apply, pi.sub_apply],
      apply ideal.mul_mem_left,
      rw ←ideal.neg_mem_iff,
      simpa only [neg_sub] using hm i },
    rw [←ideal.add_mem_iff_left (I.pi ι) this, sub_eq_add_neg, add_comm, ←add_assoc, ←smul_add,
      sub_add_cancel, ←sub_eq_add_neg, ←sub_smul, ideal.mem_pi],
    exact λ i, ideal.mul_mem_right _ hc },
  all_goals { rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ <|> rintro ⟨a⟩,
    simp only [(•), submodule.quotient.quot_mk_eq_mk, ideal.quotient.mk_eq_mk],
    change ideal.quotient.mk _ _ = ideal.quotient.mk _ _,
    congr' with i, simp [mul_assoc, mul_add, add_mul] }
end

/-- `R^n/I^n` is isomorphic to `(R/I)^n` as an `R/I`-module. -/
noncomputable def pi_quot_equiv : (I.pi ι).quotient ≃ₗ[I.quotient] (ι → I.quotient) :=
{ to_fun := λ x, quotient.lift_on' x (λ f i, ideal.quotient.mk I (f i)) $
    λ a b hab, funext (λ i, ideal.quotient.eq.2 (hab i)),
  map_add' := by { rintros ⟨_⟩ ⟨_⟩, refl },
  map_smul' := by { rintros ⟨_⟩ ⟨_⟩, refl },
  inv_fun := λ x, ideal.quotient.mk (I.pi ι) $ λ i, quotient.out' (x i),
  left_inv :=
  begin
    rintro ⟨x⟩,
    exact ideal.quotient.eq.2 (λ i, ideal.quotient.eq.1 (quotient.out_eq' _))
  end,
  right_inv :=
  begin
    intro x,
    ext i,
    obtain ⟨r, hr⟩ := @quot.exists_rep _ _ (x i),
    simp_rw ←hr,
    convert quotient.out_eq' _
  end }

/-- If `f : R^n → R^m` is an `R`-linear map and `I ⊆ R` is an ideal, then the image of `I^n` is
    contained in `I^m`. -/
lemma map_pi {ι} [fintype ι] {ι' : Type w} (x : ι → α) (hi : ∀ i, x i ∈ I)
  (f : (ι → α) →ₗ[α] (ι' → α)) (i : ι') : f x i ∈ I :=
begin
  rw pi_eq_sum_univ x,
  simp only [finset.sum_apply, smul_eq_mul, linear_map.map_sum, pi.smul_apply, linear_map.map_smul],
  exact submodule.sum_mem _ (λ j hj, ideal.mul_mem_right _ (hi j))
end

end pi

end ideal

/-- The set of non-invertible elements of a monoid. -/
def nonunits (α : Type u) [monoid α] : set α := { a | ¬is_unit a }

@[simp] theorem mem_nonunits_iff [comm_monoid α] : a ∈ nonunits α ↔ ¬ is_unit a := iff.rfl

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

theorem coe_subset_nonunits [comm_ring α] {I : ideal α} (h : I ≠ ⊤) :
  (I : set α) ⊆ nonunits α :=
λ x hx hu, h $ I.eq_top_of_is_unit_mem hx hu

lemma exists_max_ideal_of_mem_nonunits [comm_ring α] (h : a ∈ nonunits α) :
  ∃ I : ideal α, I.is_maximal ∧ a ∈ I :=
begin
  have : ideal.span ({a} : set α) ≠ ⊤,
  { intro H, rw ideal.span_singleton_eq_top at H, contradiction },
  rcases ideal.exists_le_maximal _ this with ⟨I, Imax, H⟩,
  use [I, Imax], apply H, apply ideal.subset_span, exact set.mem_singleton a
end

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A commutative ring is local if it has a unique maximal ideal. Note that
  `local_ring` is a predicate. -/
class local_ring (α : Type u) [comm_ring α] extends nontrivial α : Prop :=
(is_local : ∀ (a : α), (is_unit a) ∨ (is_unit (1 - a)))
end prio

namespace local_ring

variables [comm_ring α] [local_ring α]

lemma is_unit_or_is_unit_one_sub_self (a : α) :
  (is_unit a) ∨ (is_unit (1 - a)) :=
is_local a

lemma is_unit_of_mem_nonunits_one_sub_self (a : α) (h : (1 - a) ∈ nonunits α) :
  is_unit a :=
or_iff_not_imp_right.1 (is_local a) h

lemma is_unit_one_sub_self_of_mem_nonunits (a : α) (h : a ∈ nonunits α) :
  is_unit (1 - a) :=
or_iff_not_imp_left.1 (is_local a) h

lemma nonunits_add {x y} (hx : x ∈ nonunits α) (hy : y ∈ nonunits α) :
  x + y ∈ nonunits α :=
begin
  rintros ⟨u, hu⟩,
  apply hy,
  suffices : is_unit ((↑u⁻¹ : α) * y),
  { rcases this with ⟨s, hs⟩,
    use u * s,
    convert congr_arg (λ z, (u : α) * z) hs,
    rw ← mul_assoc, simp },
  rw show (↑u⁻¹ * y) = (1 - ↑u⁻¹ * x),
  { rw eq_sub_iff_add_eq,
    replace hu := congr_arg (λ z, (↑u⁻¹ : α) * z) hu.symm,
    simpa [mul_add, add_comm] using hu },
  apply is_unit_one_sub_self_of_mem_nonunits,
  exact mul_mem_nonunits_right hx
end

variable (α)

/-- The ideal of elements that are not units. -/
def maximal_ideal : ideal α :=
{ carrier := nonunits α,
  zero_mem' := zero_mem_nonunits.2 $ zero_ne_one,
  add_mem' := λ x y hx hy, nonunits_add hx hy,
  smul_mem' := λ a x, mul_mem_nonunits_right }

instance maximal_ideal.is_maximal : (maximal_ideal α).is_maximal :=
begin
  rw ideal.is_maximal_iff,
  split,
  { intro h, apply h, exact is_unit_one },
  { intros I x hI hx H,
    erw not_not at hx,
    rcases hx with ⟨u,rfl⟩,
    simpa using I.smul_mem ↑u⁻¹ H }
end

lemma maximal_ideal_unique :
  ∃! I : ideal α, I.is_maximal :=
⟨maximal_ideal α, maximal_ideal.is_maximal α,
  λ I hI, hI.eq_of_le (maximal_ideal.is_maximal α).1 $
  λ x hx, hI.1 ∘ I.eq_top_of_is_unit_mem hx⟩

variable {α}

lemma eq_maximal_ideal {I : ideal α} (hI : I.is_maximal) : I = maximal_ideal α :=
unique_of_exists_unique (maximal_ideal_unique α) hI $ maximal_ideal.is_maximal α

lemma le_maximal_ideal {J : ideal α} (hJ : J ≠ ⊤) : J ≤ maximal_ideal α :=
begin
  rcases ideal.exists_le_maximal J hJ with ⟨M, hM1, hM2⟩,
  rwa ←eq_maximal_ideal hM1
end

@[simp] lemma mem_maximal_ideal (x) :
  x ∈ maximal_ideal α ↔ x ∈ nonunits α := iff.rfl

end local_ring

lemma local_of_nonunits_ideal [comm_ring α] (hnze : (0:α) ≠ 1)
  (h : ∀ x y ∈ nonunits α, x + y ∈ nonunits α) : local_ring α :=
{ exists_pair_ne := ⟨0, 1, hnze⟩,
  is_local := λ x, or_iff_not_imp_left.mpr $ λ hx,
  begin
    by_contra H,
    apply h _ _ hx H,
    simp [-sub_eq_add_neg, add_sub_cancel'_right]
  end }

lemma local_of_unique_max_ideal [comm_ring α] (h : ∃! I : ideal α, I.is_maximal) :
  local_ring α :=
local_of_nonunits_ideal
(let ⟨I, Imax, _⟩ := h in (λ (H : 0 = 1), Imax.1 $ I.eq_top_iff_one.2 $ H ▸ I.zero_mem))
$ λ x y hx hy H,
let ⟨I, Imax, Iuniq⟩ := h in
let ⟨Ix, Ixmax, Hx⟩ := exists_max_ideal_of_mem_nonunits hx in
let ⟨Iy, Iymax, Hy⟩ := exists_max_ideal_of_mem_nonunits hy in
have xmemI : x ∈ I, from ((Iuniq Ix Ixmax) ▸ Hx),
have ymemI : y ∈ I, from ((Iuniq Iy Iymax) ▸ Hy),
Imax.1 $ I.eq_top_of_is_unit_mem (I.add_mem xmemI ymemI) H

lemma local_of_unique_nonzero_prime (R : Type u) [comm_ring R]
  (h : ∃! P : ideal R, P ≠ ⊥ ∧ ideal.is_prime P) : local_ring R :=
local_of_unique_max_ideal begin
  rcases h with ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩,
  refine ⟨P, ⟨hPnot_top, _⟩, λ M hM, hPunique _ ⟨_, ideal.is_maximal.is_prime hM⟩⟩,
  { refine ideal.maximal_of_no_maximal (λ M hPM hM, ne_of_lt hPM _),
    exact (hPunique _ ⟨ne_bot_of_gt hPM, ideal.is_maximal.is_prime hM⟩).symm },
  { rintro rfl,
    exact hPnot_top (hM.2 P (bot_lt_iff_ne_bot.2 hPnonzero)) },
end

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A local ring homomorphism is a homomorphism between local rings
  such that the image of the maximal ideal of the source is contained within
  the maximal ideal of the target. -/
class is_local_ring_hom [semiring α] [semiring β] (f : α →+* β) : Prop :=
(map_nonunit : ∀ a, is_unit (f a) → is_unit a)
end prio

@[simp] lemma is_unit_of_map_unit [semiring α] [semiring β] (f : α →+* β) [is_local_ring_hom f]
  (a) (h : is_unit (f a)) : is_unit a :=
is_local_ring_hom.map_nonunit a h

theorem of_irreducible_map [semiring α] [semiring β] (f : α →+* β) [h : is_local_ring_hom f] {x : α}
  (hfx : irreducible (f x)) : irreducible x :=
⟨λ h, hfx.1 $ is_unit.map f.to_monoid_hom h, λ p q hx, let ⟨H⟩ := h in
or.imp (H p) (H q) $ hfx.2 _ _ $ f.map_mul p q ▸ congr_arg f hx⟩

section
open local_ring
variables [comm_ring α] [local_ring α] [comm_ring β] [local_ring β]
variables (f : α →+* β) [is_local_ring_hom f]

lemma map_nonunit (a) (h : a ∈ maximal_ideal α) : f a ∈ maximal_ideal β :=
λ H, h $ is_unit_of_map_unit f a H

end

namespace local_ring
variables [comm_ring α] [local_ring α] [comm_ring β] [local_ring β]

variable (α)
/-- The residue field of a local ring is the quotient of the ring by its maximal ideal. -/
def residue_field := (maximal_ideal α).quotient

noncomputable instance residue_field.field : field (residue_field α) :=
ideal.quotient.field (maximal_ideal α)

noncomputable instance : inhabited (residue_field α) := ⟨37⟩

/-- The quotient map from a local ring to its residue field. -/
def residue : α →+* (residue_field α) :=
ideal.quotient.mk _

namespace residue_field

variables {α β}
/-- The map on residue fields induced by a local homomorphism between local rings -/
noncomputable def map (f : α →+* β) [is_local_ring_hom f] :
  residue_field α →+* residue_field β :=
ideal.quotient.lift (maximal_ideal α) ((ideal.quotient.mk _).comp f) $
λ a ha,
begin
  erw ideal.quotient.eq_zero_iff_mem,
  exact map_nonunit f a ha
end

end residue_field

end local_ring

namespace field
variables [field α]

@[priority 100] -- see Note [lower instance priority]
instance : local_ring α :=
{ is_local := λ a,
  if h : a = 0
  then or.inr (by rw [h, sub_zero]; exact is_unit_one)
  else or.inl $ is_unit_of_mul_eq_one a a⁻¹ $ div_self h }

end field
