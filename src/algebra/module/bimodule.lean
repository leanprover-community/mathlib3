/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import ring_theory.tensor_product

/-!
# Bimodules

One frequently encounters situations in which several sets of scalars act on a single space, subject
to compatibility condition(s). A distinguished instance of this is the theory of bimodules: one has
two rings `R`, `S` acting on an additive group `M`, with `R` acting covariantly ("on the left")
and `S` acting contravariantly ("on the right"). The compatibility condition is just:
`(r • m) • s = r • (m • s)` for all `r : R`, `s : S`, `m : M`.

This situation can be set up in Mathlib as:
```lean
variables (R S M : Type*) [ring R] [ring S]
variables [add_comm_group M] [module R M] [module Sᵐᵒᵖ M] [smul_comm_class R Sᵐᵒᵖ M]
```
The key fact is:
```lean
example : module (R ⊗[ℕ] Sᵐᵒᵖ) M := tensor_product.algebra.module
```
Note that the corresponding result holds for the canonically isomorphic ring `R ⊗[ℤ] Sᵐᵒᵖ` but it is
preferable to use the `R ⊗[ℕ] Sᵐᵒᵖ` instance since it works without additive inverses.

Bimodules are thus just a special case of `module`s and most of their properties follow from the
theory of `module`s`. In particular a two-sided submodule of a bimodule is simply a term of type
`submodule (R ⊗[ℕ] Sᵐᵒᵖ) M`.

This file is a place to collect results which are specific to bimodules.

## Main definitions

 * `subbimodule.mk`
 * `subbimodule.smul_mem`
 * `subbimodule.smul_mem'`
 * `subbimodule.to_submodule`
 * `subbimodule.to_submodule'`

## Implementation details

For many definitions and lemmas it is preferable to set things up without opposites, i.e., as:
`[module S M] [smul_comm_class R S M]` rather than `[module Sᵐᵒᵖ M] [smul_comm_class R Sᵐᵒᵖ M]`.
The corresponding results for opposites then follow automatically and do not require taking
advantage of the fact that `(Sᵐᵒᵖ)ᵐᵒᵖ` is defeq to `S`.

## TODO

Develop the theory of two-sided ideals, which have type `submodule (R ⊗[ℕ] Rᵐᵒᵖ) R`.

-/

open_locale tensor_product

local attribute [instance] tensor_product.algebra.module

namespace subbimodule

section algebra

variables {R A B M : Type*}
variables [comm_semiring R] [add_comm_monoid M] [module R M]
variables [semiring A] [semiring B] [module A M] [module B M]
variables [algebra R A] [algebra R B]
variables [is_scalar_tower R A M] [is_scalar_tower R B M]
variables [smul_comm_class A B M]

/-- A constructor for a subbimodule which demands closure under the two sets of scalars
individually, rather than jointly via their tensor product.

Note that `R` plays no role but it is convenient to make this generalisation to support the cases
`R = ℕ` and `R = ℤ` which both show up naturally. See also `base_change`. -/
@[simps] def mk (p : add_submonoid M)
  (hA : ∀ (a : A) {m : M}, m ∈ p → a • m ∈ p)
  (hB : ∀ (b : B) {m : M}, m ∈ p → b • m ∈ p) : submodule (A ⊗[R] B) M :=
{ carrier := p,
  smul_mem' := λ ab m, tensor_product.induction_on ab
   (λ hm, by simpa only [zero_smul] using p.zero_mem)
   (λ a b hm, by simpa only [tensor_product.algebra.smul_def] using hA a (hB b hm))
   (λ z w hz hw hm, by simpa only [add_smul] using p.add_mem (hz hm) (hw hm)),
  .. p }

lemma smul_mem (p : submodule (A ⊗[R] B) M) (a : A) {m : M} (hm : m ∈ p) : a • m ∈ p :=
begin
  suffices : a • m = a ⊗ₜ[R] (1 : B) • m, { exact this.symm ▸ p.smul_mem _ hm, },
  simp [tensor_product.algebra.smul_def],
end

lemma smul_mem' (p : submodule (A ⊗[R] B) M) (b : B) {m : M} (hm : m ∈ p) : b • m ∈ p :=
begin
  suffices : b • m = (1 : A) ⊗ₜ[R] b • m, { exact this.symm ▸ p.smul_mem _ hm, },
  simp [tensor_product.algebra.smul_def],
end

/-- If `A` and `B` are also `algebra`s over yet another set of scalars `S` then we may "base change"
from `R` to `S`. -/
@[simps] def base_change (S : Type*) [comm_semiring S] [module S M] [algebra S A] [algebra S B]
  [is_scalar_tower S A M] [is_scalar_tower S B M] (p : submodule (A ⊗[R] B) M) :
  submodule (A ⊗[S] B) M :=
mk p.to_add_submonoid (smul_mem p) (smul_mem' p)

/-- Forgetting the `B` action, a `submodule` over `A ⊗[R] B` is just a `submodule` over `A`. -/
@[simps] def to_submodule (p : submodule (A ⊗[R] B) M) : submodule A M :=
{ carrier := p,
  smul_mem' := smul_mem p,
  .. p }

/-- Forgetting the `A` action, a `submodule` over `A ⊗[R] B` is just a `submodule` over `B`. -/
@[simps] def to_submodule' (p : submodule (A ⊗[R] B) M) : submodule B M :=
{ carrier := p,
  smul_mem' := smul_mem' p,
  .. p }

end algebra

section ring

variables (R S M : Type*) [ring R] [ring S]
variables [add_comm_group M] [module R M] [module S M] [smul_comm_class R S M]

/-- A `submodule` over `R ⊗[ℕ] S` is naturally also a `submodule` over the canonically-isomorphic
ring `R ⊗[ℤ] S`. -/
@[simps] def to_subbimodule_int (p : submodule (R ⊗[ℕ] S) M) : submodule (R ⊗[ℤ] S) M :=
base_change ℤ p

/-- A `submodule` over `R ⊗[ℤ] S` is naturally also a `submodule` over the canonically-isomorphic
ring `R ⊗[ℕ] S`. -/
@[simps] def to_subbimodule_nat (p : submodule (R ⊗[ℤ] S) M) : submodule (R ⊗[ℕ] S) M :=
base_change ℕ p

end ring

end subbimodule

/-- The type of two-sided ideals in a semiring `R`, realized as subbimodules. -/
abbreviation ideal₂ (R : Type*) [semiring R] := submodule (R ⊗[ℕ] Rᵐᵒᵖ) R

namespace ideal₂

variables {R : Type*} [semiring R]

protected lemma zero_mem (I : ideal₂ R) : (0 : R) ∈ I := zero_mem I
protected lemma add_mem (I : ideal₂ R) {x y : R} (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I :=
add_mem hx hy
protected lemma mul_mem_left (I : ideal₂ R) (x : R) {y : R} (hy : y ∈ I) : x * y ∈ I :=
subbimodule.smul_mem I x hy
protected lemma mul_mem_right (I : ideal₂ R) {x : R} (y : R) (hx : x ∈ I) : x * y ∈ I :=
subbimodule.smul_mem' I (mul_opposite.op y) hx
protected lemma neg_mem {R : Type*} [ring R] (I : ideal₂ R) {x : R} (hx : x ∈ I) : -x ∈ I :=
by simpa only [neg_mul, one_mul] using I.mul_mem_left (-1) hx
protected lemma pow_mem (I : ideal₂ R) {x : R} (hx : x ∈ I) (n : ℕ) (hn : 0 < n) : x ^ n ∈ I :=
begin
  cases n,
  { exact false.elim (hn.ne rfl) },
  { rw pow_succ' x n,
    exact I.mul_mem_left (x ^ n) hx },
end

instance {R : Type*} [ring R] : add_subgroup_class (ideal₂ R) R :=
{ neg_mem := ideal₂.neg_mem }

/-- A constructor for two-sided ideals analogous to `subbimodule.mk`. -/
@[simps] def mk (I : add_submonoid R)
  (h₁ : ∀ (a : R) {m : R}, m ∈ I → a * m ∈ I)
  (h₂ : ∀ (b : R) {m : R}, m ∈ I → m * b ∈ I) : ideal₂ R :=
subbimodule.mk I h₁ (λ b m hm, h₂ (mul_opposite.unop b) hm)

/-- Forget the right-ideal structure of a two-sided ideal. -/
@[simps]
def to_ideal (I : ideal₂ R) : ideal R :=
{ carrier := I,
  add_mem' := λ a b, I.add_mem,
  zero_mem' := I.zero_mem,
  smul_mem' := I.mul_mem_left }

-- we can make this into an order iso?
/-- The equivalence between left ideals and two-sided ideals in a commutative semiring. -/
@[simps]
def _root_.equiv.ideal_ideal₂ {R : Type*} [comm_semiring R] : ideal R ≃ ideal₂ R :=
{ to_fun := λ I, ideal₂.mk I.to_add_submonoid I.mul_mem_left (λ b m hm, I.mul_mem_right b hm),
  inv_fun := to_ideal,
  left_inv := λ I, by { ext, refl },
  right_inv := λ I, by { ext, refl } }

.

@[ext]
lemma ext {I J : ideal₂ R} (h : ∀ (x : R), x ∈ I ↔ x ∈ J) : I = J := submodule.ext h

protected lemma sum_mem (I : ideal₂ R) {ι : Type*} {t : finset ι} {f : ι → R} :
  (∀ (c : ι), c ∈ t → f c ∈ I) → t.sum (λ (i : ι), f i) ∈ I :=
sum_mem

lemma eq_top_of_mul_left_eq_one (I : ideal₂ R) (x y : R) (hx : x ∈ I) (h : y * x = 1) : I = ⊤ :=
submodule.eq_top_iff'.mpr
  (λ z, by simpa only [h, mul_one] using I.mul_mem_left z (I.mul_mem_left y hx))

lemma eq_top_of_mul_right_eq_one (I : ideal₂ R) (x y : R) (hy : y ∈ I) (h : y * x = 1) : I = ⊤ :=
submodule.eq_top_iff'.mpr
  (λ z, by simpa only [h, one_mul] using I.mul_mem_right z (I.mul_mem_right x hy))

lemma eq_top_of_units_mem (I : ideal₂ R) (x : Rˣ) (hx : (x : R) ∈ I) : I = ⊤ :=
I.eq_top_of_mul_left_eq_one x ↑x⁻¹ hx x.inv_mul

lemma eq_top_of_is_unit_mem (I : ideal₂ R) (x : R) (hx : is_unit x) (h : x ∈ I) : I = ⊤ :=
match hx with ⟨u, hu⟩ := I.eq_top_of_units_mem u (hu.symm ▸ h) end

lemma eq_top_iff_one (I : ideal₂ R) : I = ⊤ ↔ (1 : R) ∈ I :=
⟨λ h, h.symm ▸ submodule.mem_top, I.eq_top_of_units_mem 1⟩

lemma ne_top_iff_one (I : ideal₂ R) : I ≠ ⊤ ↔ (1 : R) ∉ I :=
not_iff_not.mpr I.eq_top_iff_one

lemma units_smul_mem_iff_mem (I : ideal₂ R) {x : R} (y : Rˣ) : y • x ∈ I ↔ x ∈ I :=
⟨λ h, by simpa only [←smul_eq_mul, ←units.smul_def, inv_smul_smul] using I.mul_mem_left ↑y⁻¹ h,
 I.mul_mem_left y⟩

lemma is_unit_mul_mem_left_iff_mem (I : ideal₂ R) {x y : R} (hy : is_unit y) : y * x ∈ I ↔ x ∈ I :=
match hy with ⟨u, hu⟩ := by simpa only [hu, units.smul_def] using I.units_smul_mem_iff_mem u end

lemma is_unit_mul_mem_right_iff_mem (I : ideal₂ R) {x y : R} (hy : is_unit y) : x * y ∈ I ↔ x ∈ I :=
begin
  refine ⟨λ h, _, I.mul_mem_right y⟩,
  obtain ⟨u, rfl⟩ := hy,
  simpa only [mul_one, mul_assoc, units.mul_inv] using I.mul_mem_right ↑u⁻¹ h
end

/-- The two-sided ideal generated by a subset of a semiring. -/
def span (s : set R) : ideal₂ R := submodule.span (R ⊗[ℕ] Rᵐᵒᵖ) s

@[simp]
lemma submodule_span_eq {s : set R} : submodule.span (R ⊗[ℕ] Rᵐᵒᵖ) s = span s := rfl

@[simp]
lemma span_empty : span (∅ : set R) = ⊥ := submodule.span_empty

@[simp]
lemma span_univ : span (set.univ : set R) = ⊤ := submodule.span_univ

lemma span_union (s t : set R) : span (s ∪ t) = span s ⊔ span t := submodule.span_union s t

lemma span_Union {ι : Sort*} (s : ι → set R) : span (⋃ i, s i) = ⨆ i, span (s i) :=
submodule.span_Union s

lemma mem_span {s : set R} (x : R) : x ∈ span s ↔ ∀ (I : ideal₂ R), s ⊆ ↑I → x ∈ I :=
submodule.mem_span

lemma subset_span {s : set R} : s ⊆ span s := submodule.subset_span

lemma span_le {s : set R} {I : ideal₂ R} : span s ≤ I ↔ s ⊆ I := submodule.span_le

lemma span_mono {s t : set R} : s ⊆ t → span s ≤ span t := submodule.span_mono

@[simp]
lemma span_eq (I : ideal₂ R) : span (I : set R) = I := submodule.span_eq I

@[simp]
lemma span_singleton_one : span ({1} : set R) = ⊤ :=
(eq_top_iff_one _).mpr (subset_span $ set.mem_singleton 1)

.
lemma mem_span_insert {R : Type*} [ring R] {s : set R} {x y : R} :
  x ∈ span (insert y s) ↔
  ∃ (z ∈ span s) (t : multiset (R × R)), x = (t.map (λ a : R × R, a.1 * y * a.2)).sum + z :=
begin
  rw [←submodule_span_eq, submodule.mem_span_insert],
  split,
  { rintro ⟨a, z, hz, rfl⟩,
    refine a.induction_on _ (λ a b, _) (λ a b, _),
    { exact ⟨z, hz, ∅, by simp⟩ },
    { refine ⟨z, hz, {(a, mul_opposite.unop b)}, _⟩,
      simpa only [mul_assoc, multiset.map_singleton, multiset.sum_singleton] },
    { rintro ⟨z₁, hz₁, t₁, h₁⟩ ⟨z₂, hz₂, t₂, h₂⟩,
      rw [add_smul, add_assoc],
      rw ←eq_sub_iff_add_eq at h₁,
      rw [h₁, h₂],
      refine ⟨z₁ + z₂ - z, _, t₁ + t₂, _⟩,
      exact sub_mem (add_mem hz₁ hz₂) hz,
      rw [multiset.map_add, multiset.sum_add],
      abel,
      }, },
  { rintros ⟨z, hz, t, rfl⟩,
    refine t.induction_on _ _,
    refine ⟨0, z, hz, by simp⟩,
    rintros a t ⟨b, z', hz', h⟩,
    refine ⟨a.1 ⊗ₜ (mul_opposite.op a.2) + b, z', hz', _⟩,
    rw [multiset.map_cons, multiset.sum_cons, add_smul, add_assoc, h, mul_assoc, add_assoc],
    refl }
end

example [decidable_eq R] (y : R) (t : multiset (R × R)) :
  (t.map (λ a : R × R, a.1 * y * a.2)).sum = t.to_finset.sum (λ a : R × R, t.count a • a.1 * y * a.2) :=
begin
  rw finset.sum_multiset_map_count,
  congr,
  funext,
  simp only [nsmul_eq_mul, mul_assoc],
end

lemma mem_span_singleton_self (x : R) : x ∈ span ({x} : set R) :=
subset_span (set.mem_singleton x)

lemma mem_span_singleton {R : Type*} [ring R] {x y : R} :
  x ∈ span ({y} : set R) ↔ ∃ (s : multiset (R × R)), x = (s.map (λ z : R × R, z.1 * y * z.2)).sum :=
begin
  have := @mem_span_insert R _ ∅ x y,
  rw set.is_lawful_singleton.insert_emptyc_eq at this,
  simp [this],
end

lemma span_singleton_le_iff_mem (I : ideal₂ R) {x : R} : span {x} ≤ I ↔ x ∈ I :=
span_le.trans set.singleton_subset_iff

lemma span_singleton_mul_left_is_unit {a : R} (h2 : is_unit a) (x : R) :
  span ({a * x} : set R) = span ({x} : set R) :=
begin
  refine le_antisymm _ _;
  refine (span_singleton_le_iff_mem _).mpr _,
  { exact ideal₂.mul_mem_left _ a (mem_span_singleton_self x) },
  { simpa only [←mul_assoc, is_unit.coe_inv_mul, one_mul] using
      ideal₂.mul_mem_left _ ↑h2.unit⁻¹ (mem_span_singleton_self (a * x)) }
end

lemma span_singleton_mul_right_is_unit {a : R} (h2 : is_unit a) (x : R) :
  span ({x * a} : set R) = span ({x} : set R) :=
begin
  refine le_antisymm _ _;
  refine (span_singleton_le_iff_mem _).mpr _,
  { exact ideal₂.mul_mem_right _ a (mem_span_singleton_self x) },
  { simpa only [mul_assoc, is_unit.mul_coe_inv, mul_one] using
      ideal₂.mul_mem_right _ ↑h2.unit⁻¹ (mem_span_singleton_self (x * a)) }
end

lemma span_insert (x : R) (s : set R) : span (insert x s) = span {x} ⊔ span s :=
span_union _ _

lemma span_eq_bot {s : set R} : span s = ⊥ ↔ ∀ (x : R), x ∈ s → x = 0 :=
⟨λ h x hx, span_le.mp h.le hx,
 λ h, le_bot_iff.mp (span_le.mpr $ λ x hx, set.mem_singleton_iff.mpr $ h x hx)⟩

@[simp]
lemma span_singleton_eq_bot {x : R} : span ({x} : set R) = ⊥ ↔ x = 0 :=
by simp [span_eq_bot]

/- provable, but harder than for `ideal`s.
theorem span_singleton_ne_top {x : R} (hx : ¬is_unit x) : span ({x} : set R) ≠ ⊤ :=
sorry
-/
section pointwise
open_locale pointwise

@[simp]
lemma span_zero : span (0 : set R) = ⊥ := span_singleton_eq_bot.mpr rfl

@[simp]
lemma span_one : span (1 : set R) = ⊤ := span_singleton_one

end pointwise

lemma mem_span_finite_of_mem_span {S : set R} {x : R} (hx : x ∈ span S) :
  ∃ (T : finset R), ↑T ⊆ S ∧ x ∈ span (T : set R) :=
submodule.mem_span_finite_of_mem_span hx

lemma span_eq_top_iff_finite (s : set R) :
  span s = ⊤ ↔ ∃ s' : finset R, ↑s' ⊆ s ∧ span (s' : set R) = ⊤ :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨t, ht, h_one⟩ := mem_span_finite_of_mem_span (h.symm ▸ submodule.mem_top : 1 ∈ span s),
    exact ⟨t, ht, (eq_top_iff_one _).mpr h_one⟩ },
  { rintro ⟨t, ht, h_top⟩,
    exact eq_top_iff.mpr (h_top ▸ span_mono ht), }
end

section lattice

lemma mem_sup_left {S T : ideal₂ R} : ∀ {x : R}, x ∈ S → x ∈ S ⊔ T :=
show S ≤ S ⊔ T, from le_sup_left

lemma mem_sup_right {S T : ideal₂ R} : ∀ {x : R}, x ∈ T → x ∈ S ⊔ T :=
show T ≤ S ⊔ T, from le_sup_right

lemma mem_supr_of_mem {ι : Sort*} {S : ι → ideal₂ R} (i : ι) :
  ∀ {x : R}, x ∈ S i → x ∈ supr S :=
show S i ≤ supr S, from le_supr _ _

lemma mem_Sup_of_mem {S : set (ideal₂ R)} {s : ideal₂ R}
  (hs : s ∈ S) : ∀ {x : R}, x ∈ s → x ∈ Sup S :=
show s ≤ Sup S, from le_Sup hs

theorem mem_Inf {s : set (ideal₂ R)} {x : R} :
  x ∈ Inf s ↔ ∀ ⦃I⦄, I ∈ s → x ∈ I :=
⟨λ hx I his, hx I ⟨I, infi_pos his⟩, λ H I ⟨J, hij⟩, hij ▸ λ S ⟨hj, hS⟩, hS ▸ H hj⟩

@[simp] lemma mem_inf {I J : ideal₂ R} {x : R} : x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J := iff.rfl

@[simp] lemma mem_infi {ι : Sort*} {I : ι → ideal₂ R} {x : R} : x ∈ infi I ↔ ∀ i, x ∈ I i :=
submodule.mem_infi _

@[simp] lemma mem_bot {x : R} : x ∈ (⊥ : ideal₂ R) ↔ x = 0 :=
submodule.mem_bot _

end lattice

end ideal₂
