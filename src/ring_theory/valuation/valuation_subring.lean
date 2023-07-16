/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Junyan Xu, Jack McKoen
-/
import ring_theory.valuation.valuation_ring
import ring_theory.localization.as_subring
import ring_theory.subring.pointwise
import algebraic_geometry.prime_spectrum.basic

/-!

# Valuation subrings of a field

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Projects

The order structure on `valuation_subring K`.

-/

open_locale classical
noncomputable theory

variables (K : Type*) [field K]

/-- A valuation subring of a field `K` is a subring `A` such that for every `x : K`,
either `x ∈ A` or `x⁻¹ ∈ A`. -/
structure valuation_subring extends subring K :=
(mem_or_inv_mem' : ∀ x : K, x ∈ carrier ∨ x⁻¹ ∈ carrier)

namespace valuation_subring

variables {K} (A : valuation_subring K)

instance : set_like (valuation_subring K) K :=
{ coe := λ A, A.to_subring,
  coe_injective' := by { rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ _, congr' } }

@[simp] lemma mem_carrier (x : K) : x ∈ A.carrier ↔ x ∈ A := iff.refl _
@[simp] lemma mem_to_subring (x : K) : x ∈ A.to_subring ↔ x ∈ A := iff.refl _

@[ext] lemma ext (A B : valuation_subring K)
  (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B := set_like.ext h

lemma zero_mem : (0 : K) ∈ A := A.to_subring.zero_mem
lemma one_mem : (1 : K) ∈ A := A.to_subring.one_mem
lemma add_mem (x y : K) : x ∈ A → y ∈ A → x + y ∈ A := A.to_subring.add_mem
lemma mul_mem (x y : K) : x ∈ A → y ∈ A → x * y ∈ A := A.to_subring.mul_mem
lemma neg_mem (x : K) : x ∈ A → (-x) ∈ A := A.to_subring.neg_mem

lemma mem_or_inv_mem (x : K) : x ∈ A ∨ x⁻¹ ∈ A := A.mem_or_inv_mem' _

instance : subring_class (valuation_subring K) K :=
{ zero_mem := zero_mem,
  add_mem := add_mem,
  one_mem := one_mem,
  mul_mem := mul_mem,
  neg_mem := neg_mem }

lemma to_subring_injective : function.injective (to_subring : valuation_subring K → subring K) :=
λ x y h, by { cases x, cases y, congr' }

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
{ cond := λ a b,
  begin
    by_cases (b : K) = 0, { use 0, left, ext, simp [h] },
    by_cases (a : K) = 0, { use 0, right, ext, simp [h] },
    cases A.mem_or_inv_mem (a/b) with hh hh,
    { use ⟨a/b, hh⟩, right, ext, field_simp, ring },
    { rw (show (a/b : K)⁻¹ = b/a, by field_simp) at hh,
      use ⟨b/a, hh⟩, left, ext, field_simp, ring },
  end }

instance : algebra A K :=
show algebra A.to_subring K, by apply_instance

@[simp]
lemma algebra_map_apply (a : A) : algebra_map A K a = a := rfl

instance : is_fraction_ring A K :=
{ map_units := λ ⟨y, hy⟩,
    (units.mk0 (y : K) (λ c, non_zero_divisors.ne_zero hy $ subtype.ext c)).is_unit,
  surj := λ z, begin
    by_cases z = 0, { use (0, 1), simp [h] },
    cases A.mem_or_inv_mem z with hh hh,
    { use (⟨z, hh⟩, 1), simp },
    { refine ⟨⟨1, ⟨⟨_, hh⟩, _⟩⟩, mul_inv_cancel h⟩,
      exact mem_non_zero_divisors_iff_ne_zero.2 (λ c, h (inv_eq_zero.mp (congr_arg coe c))) },
  end,
  eq_iff_exists := λ a b, ⟨ λ h, ⟨1, by { ext, simpa using h }⟩, λ ⟨c, h⟩,
    congr_arg coe ((mul_eq_mul_left_iff.1 h).resolve_right (non_zero_divisors.ne_zero c.2)) ⟩ }

/-- The value group of the valuation associated to `A`. Note: it is actually a group with zero. -/
@[derive linear_ordered_comm_group_with_zero]
def value_group := valuation_ring.value_group A K

/-- Any valuation subring of `K` induces a natural valuation on `K`. -/
def valuation : valuation K A.value_group := valuation_ring.valuation A K

instance inhabited_value_group : inhabited A.value_group := ⟨A.valuation 0⟩

lemma valuation_le_one (a : A) : A.valuation a ≤ 1 :=
(valuation_ring.mem_integer_iff A K _).2 ⟨a, rfl⟩

lemma mem_of_valuation_le_one (x : K) (h : A.valuation x ≤ 1) : x ∈ A :=
let ⟨a, ha⟩ := (valuation_ring.mem_integer_iff A K x).1 h in ha ▸ a.2

lemma valuation_le_one_iff (x : K) : A.valuation x ≤ 1 ↔ x ∈ A :=
⟨mem_of_valuation_le_one _ _, λ ha, A.valuation_le_one ⟨x, ha⟩⟩

lemma valuation_eq_iff (x y : K) : A.valuation x = A.valuation y ↔
  ∃ a : Aˣ, (a : K) * y = x := quotient.eq'

lemma valuation_le_iff (x y : K) : A.valuation x ≤ A.valuation y ↔
  ∃ a : A, (a : K) * y = x := iff.rfl

lemma valuation_surjective : function.surjective A.valuation := surjective_quot_mk _

lemma valuation_unit (a : Aˣ) : A.valuation a = 1 :=
by { rw [← A.valuation.map_one, valuation_eq_iff], use a, simp }

lemma valuation_eq_one_iff (a : A) : is_unit a ↔ A.valuation a = 1 :=
⟨ λ h, A.valuation_unit h.unit,
  λ h, begin
    have ha : (a : K) ≠ 0,
    { intro c, rw [c, A.valuation.map_zero] at h, exact zero_ne_one h },
    have ha' : (a : K)⁻¹ ∈ A,
    { rw [← valuation_le_one_iff, map_inv₀, h, inv_one] },
    apply is_unit_of_mul_eq_one a ⟨a⁻¹, ha'⟩, ext, field_simp,
  end ⟩

lemma valuation_lt_one_or_eq_one (a : A) : A.valuation a < 1 ∨ A.valuation a = 1 :=
lt_or_eq_of_le (A.valuation_le_one a)

lemma valuation_lt_one_iff (a : A) : a ∈ local_ring.maximal_ideal A ↔ A.valuation a < 1 :=
begin
  rw local_ring.mem_maximal_ideal,
  dsimp [nonunits], rw valuation_eq_one_iff,
  exact (A.valuation_le_one a).lt_iff_ne.symm,
end

/-- A subring `R` of `K` such that for all `x : K` either `x ∈ R` or `x⁻¹ ∈ R` is
  a valuation subring of `K`. -/
def of_subring (R : subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) : valuation_subring K :=
{ mem_or_inv_mem' := hR, ..R }

@[simp]
lemma mem_of_subring (R : subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) (x : K) :
  x ∈ of_subring R hR ↔ x ∈ R := iff.refl _

/-- An overring of a valuation ring is a valuation ring. -/
def of_le (R : valuation_subring K) (S : subring K) (h : R.to_subring ≤ S) :
  valuation_subring K :=
{ mem_or_inv_mem' := λ x, (R.mem_or_inv_mem x).imp (@h x) (@h _), ..S}

section order

instance : semilattice_sup (valuation_subring K) :=
{ sup := λ R S, of_le R (R.to_subring ⊔ S.to_subring) $ le_sup_left,
  le_sup_left := λ R S x hx, (le_sup_left : R.to_subring ≤ R.to_subring ⊔ S.to_subring) hx,
  le_sup_right := λ R S x hx, (le_sup_right : S.to_subring ≤ R.to_subring ⊔ S.to_subring) hx,
  sup_le := λ R S T hR hT x hx, (sup_le hR hT : R.to_subring ⊔ S.to_subring ≤ T.to_subring) hx,
  ..(infer_instance : partial_order (valuation_subring K)) }

/-- The ring homomorphism induced by the partial order. -/
def inclusion (R S : valuation_subring K) (h : R ≤ S) : R →+* S :=
subring.inclusion h

/-- The canonical ring homomorphism from a valuation ring to its field of fractions. -/
def subtype (R : valuation_subring K) : R →+* K :=
subring.subtype R.to_subring

/-- The canonical map on value groups induced by a coarsening of valuation rings. -/
def map_of_le (R S : valuation_subring K) (h : R ≤ S) :
  R.value_group →*₀ S.value_group :=
{ to_fun := quotient.map' id $ λ x y ⟨u, hu⟩, ⟨units.map (R.inclusion S h).to_monoid_hom u, hu⟩,
  map_zero' := rfl,
  map_one' := rfl,
  map_mul' := by { rintro ⟨⟩ ⟨⟩, refl } }

@[mono]
lemma monotone_map_of_le (R S : valuation_subring K) (h : R ≤ S) :
  monotone (R.map_of_le S h) :=
by { rintros ⟨⟩ ⟨⟩ ⟨a, ha⟩, exact ⟨R.inclusion S h a, ha⟩ }

@[simp]
lemma map_of_le_comp_valuation (R S : valuation_subring K) (h : R ≤ S) :
  R.map_of_le S h ∘ R.valuation = S.valuation := by { ext, refl }

@[simp]
lemma map_of_le_valuation_apply (R S : valuation_subring K) (h : R ≤ S) (x : K) :
  R.map_of_le S h (R.valuation x) = S.valuation x := rfl

/-- The ideal corresponding to a coarsening of a valuation ring. -/
def ideal_of_le (R S : valuation_subring K) (h : R ≤ S) : ideal R :=
(local_ring.maximal_ideal S).comap (R.inclusion S h)

instance prime_ideal_of_le (R S : valuation_subring K) (h : R ≤ S) :
  (ideal_of_le R S h).is_prime := (local_ring.maximal_ideal S).comap_is_prime _

/-- The coarsening of a valuation ring associated to a prime ideal. -/
def of_prime (A : valuation_subring K) (P : ideal A) [P.is_prime] :
  valuation_subring K :=
of_le A (localization.subalgebra.of_field K _ P.prime_compl_le_non_zero_divisors).to_subring $
  λ a ha, subalgebra.algebra_map_mem _ (⟨a, ha⟩ : A)

instance of_prime_algebra (A : valuation_subring K) (P : ideal A) [P.is_prime] :
  algebra A (A.of_prime P) := subalgebra.algebra _

instance of_prime_scalar_tower (A : valuation_subring K) (P : ideal A) [P.is_prime] :
  is_scalar_tower A (A.of_prime P) K := is_scalar_tower.subalgebra' A K K _

instance of_prime_localization (A : valuation_subring K) (P : ideal A) [P.is_prime] :
  is_localization.at_prime (A.of_prime P) P :=
by apply localization.subalgebra.is_localization_of_field K P.prime_compl
  P.prime_compl_le_non_zero_divisors

lemma le_of_prime (A : valuation_subring K) (P : ideal A) [P.is_prime] :
  A ≤ of_prime A P :=
λ a ha, subalgebra.algebra_map_mem _ (⟨a, ha⟩ : A)

lemma of_prime_valuation_eq_one_iff_mem_prime_compl
  (A : valuation_subring K)
  (P : ideal A) [P.is_prime] (x : A) :
  (of_prime A P).valuation x = 1 ↔ x ∈ P.prime_compl :=
begin
  rw [← is_localization.at_prime.is_unit_to_map_iff (A.of_prime P) P x, valuation_eq_one_iff], refl,
end

@[simp]
lemma ideal_of_le_of_prime (A : valuation_subring K) (P : ideal A) [P.is_prime] :
  ideal_of_le A (of_prime A P) (le_of_prime A P) = P :=
by { ext, apply is_localization.at_prime.to_map_mem_maximal_iff }

@[simp]
lemma of_prime_ideal_of_le (R S : valuation_subring K) (h : R ≤ S) :
  of_prime R (ideal_of_le R S h) = S :=
begin
  ext x, split,
  { rintro ⟨a, r, hr, rfl⟩, apply mul_mem, { exact h a.2 },
    { rw [← valuation_le_one_iff, map_inv₀, ← inv_one, inv_le_inv₀],
      { exact not_lt.1 ((not_iff_not.2 $ valuation_lt_one_iff S _).1 hr) },
      { intro hh, erw [valuation.zero_iff, subring.coe_eq_zero_iff] at hh,
        apply hr, rw hh, apply ideal.zero_mem (R.ideal_of_le S h) },
      { exact one_ne_zero } } },
  { intro hx, by_cases hr : x ∈ R, { exact R.le_of_prime _ hr },
    have : x ≠ 0 := λ h, hr (by { rw h, exact R.zero_mem }),
    replace hr := (R.mem_or_inv_mem x).resolve_left hr,
    { use [1, x⁻¹, hr], split,
      { change (⟨x⁻¹, h hr⟩ : S) ∉ nonunits S,
        erw [mem_nonunits_iff, not_not],
        apply is_unit_of_mul_eq_one _ (⟨x, hx⟩ : S),
        ext, field_simp },
      { field_simp } } },
end

lemma of_prime_le_of_le (P Q : ideal A) [P.is_prime] [Q.is_prime]
  (h : P ≤ Q) : of_prime A Q ≤ of_prime A P :=
λ x ⟨a, s, hs, he⟩, ⟨a, s, λ c, hs (h c), he⟩

lemma ideal_of_le_le_of_le (R S : valuation_subring K)
  (hR : A ≤ R) (hS : A ≤ S) (h : R ≤ S) :
  ideal_of_le A S hS ≤ ideal_of_le A R hR :=
λ x hx, (valuation_lt_one_iff R _).2 begin
  by_contra c, push_neg at c, replace c := monotone_map_of_le R S h c,
  rw [(map_of_le _ _ _).map_one, map_of_le_valuation_apply] at c,
  apply not_le_of_lt ((valuation_lt_one_iff S _).1 hx) c,
end

/-- The equivalence between coarsenings of a valuation ring and its prime ideals.-/
@[simps]
def prime_spectrum_equiv :
  prime_spectrum A ≃ { S | A ≤ S } :=
{ to_fun := λ P, ⟨of_prime A P.as_ideal, le_of_prime _ _⟩,
  inv_fun := λ S, ⟨ideal_of_le _ S S.2, infer_instance⟩,
  left_inv := λ P, by { ext1, simp },
  right_inv := λ S, by { ext1, simp } }

/-- An ordered variant of `prime_spectrum_equiv`. -/
@[simps]
def prime_spectrum_order_equiv : (prime_spectrum A)ᵒᵈ ≃o {S | A ≤ S} :=
{ map_rel_iff' := λ P Q,
    ⟨ λ h, begin
        have := ideal_of_le_le_of_le A _ _ _ _ h,
        iterate 2 { erw ideal_of_le_of_prime at this },
        exact this,
      end,
      λ h, by { apply of_prime_le_of_le, exact h } ⟩,
  ..(prime_spectrum_equiv A) }

instance linear_order_overring : linear_order { S | A ≤ S } :=
{ le_total :=
  let i : is_total (prime_spectrum A) (≤) := ⟨λ ⟨x, _⟩ ⟨y, _⟩, has_le.le.is_total.total x y⟩ in
    by exactI (prime_spectrum_order_equiv A).symm.to_rel_embedding.is_total.total,
  decidable_le := infer_instance,
  ..(infer_instance : partial_order _) }

end order

end valuation_subring

namespace valuation

variables {K} {Γ Γ₁ Γ₂ : Type*}
  [linear_ordered_comm_group_with_zero Γ]
  [linear_ordered_comm_group_with_zero Γ₁]
  [linear_ordered_comm_group_with_zero Γ₂]
  (v : valuation K Γ)
  (v₁ : valuation K Γ₁)
  (v₂ : valuation K Γ₂)

/-- The valuation subring associated to a valuation. -/
def valuation_subring : valuation_subring K :=
{ mem_or_inv_mem' := begin
    intros x,
    cases le_or_lt (v x) 1,
    { left, exact h },
    { right, change v x⁻¹ ≤ 1,
      rw [map_inv₀ v, ← inv_one, inv_le_inv₀],
      { exact le_of_lt h },
      { intro c, simpa [c] using h },
      { exact one_ne_zero } }
  end,
  .. v.integer }

@[simp]
lemma mem_valuation_subring_iff (x : K) : x ∈ v.valuation_subring ↔ v x ≤ 1 := iff.refl _

lemma is_equiv_iff_valuation_subring : v₁.is_equiv v₂ ↔
  v₁.valuation_subring = v₂.valuation_subring :=
begin
  split,
  { intros h, ext x, specialize h x 1, simpa using h },
  { intros h, apply is_equiv_of_val_le_one,
    intros x,
    have : x ∈ v₁.valuation_subring ↔ x ∈ v₂.valuation_subring, by rw h,
    simpa using this }
end

lemma is_equiv_valuation_valuation_subring :
  v.is_equiv v.valuation_subring.valuation :=
begin
  rw [is_equiv_iff_val_le_one],
  intro x,
  rw valuation_subring.valuation_le_one_iff,
  refl,
end

end valuation

namespace valuation_subring

variables {K} (A : valuation_subring K)

@[simp]
lemma valuation_subring_valuation : A.valuation.valuation_subring = A :=
by { ext, rw ← A.valuation_le_one_iff, refl }

section unit_group

/-- The unit group of a valuation subring, as a subgroup of `Kˣ`. -/
def unit_group : subgroup Kˣ :=
(A.valuation.to_monoid_with_zero_hom.to_monoid_hom.comp (units.coe_hom K)).ker

@[simp] lemma mem_unit_group_iff (x : Kˣ) : x ∈ A.unit_group ↔ A.valuation x = 1 := iff.rfl

/-- For a valuation subring `A`, `A.unit_group` agrees with the units of `A`. -/
def unit_group_mul_equiv : A.unit_group ≃* Aˣ :=
{ to_fun := λ x,
  { val := ⟨x, mem_of_valuation_le_one A _ x.prop.le⟩,
    inv := ⟨↑(x⁻¹), mem_of_valuation_le_one _ _ (x⁻¹).prop.le⟩,
    val_inv := subtype.ext (units.mul_inv x),
    inv_val := subtype.ext (units.inv_mul x) },
  inv_fun := λ x, ⟨units.map A.subtype.to_monoid_hom x, A.valuation_unit x⟩,
  left_inv := λ a, by { ext, refl },
  right_inv := λ a, by { ext, refl },
  map_mul' := λ a b, by { ext, refl } }

@[simp]
lemma coe_unit_group_mul_equiv_apply (a : A.unit_group) :
  (A.unit_group_mul_equiv a : K) = a := rfl

@[simp]
lemma coe_unit_group_mul_equiv_symm_apply (a : Aˣ) :
  (A.unit_group_mul_equiv.symm a : K) = a := rfl

lemma unit_group_le_unit_group {A B : valuation_subring K} :
  A.unit_group ≤ B.unit_group ↔ A ≤ B :=
begin
  split,
  { intros h x hx,
    rw [← A.valuation_le_one_iff x, le_iff_lt_or_eq] at hx,
    by_cases h_1 : x = 0, { simp only [h_1, zero_mem] },
    by_cases h_2 : 1 + x = 0,
      { simp only [← add_eq_zero_iff_neg_eq.1 h_2, neg_mem _ _ (one_mem _)] },
    cases hx,
    { have := h (show (units.mk0 _ h_2) ∈ A.unit_group, from A.valuation.map_one_add_of_lt hx),
      simpa using B.add_mem _ _
        (show 1 + x ∈ B, from set_like.coe_mem ((B.unit_group_mul_equiv ⟨_, this⟩) : B))
        (B.neg_mem _ B.one_mem) },
    { have := h (show (units.mk0 x h_1) ∈ A.unit_group, from hx),
      refine set_like.coe_mem ((B.unit_group_mul_equiv ⟨_, this⟩) : B) } },
  { rintros h x (hx : A.valuation x = 1),
    apply_fun A.map_of_le B h at hx,
    simpa using hx }
end

lemma unit_group_injective : function.injective (unit_group : valuation_subring K → subgroup _) :=
λ A B h, by { simpa only [le_antisymm_iff, unit_group_le_unit_group] using h}

lemma eq_iff_unit_group {A B : valuation_subring K} :
  A = B ↔ A.unit_group = B.unit_group :=
unit_group_injective.eq_iff.symm

/-- The map on valuation subrings to their unit groups is an order embedding. -/
def unit_group_order_embedding : valuation_subring K ↪o subgroup Kˣ :=
{ to_fun := λ A, A.unit_group,
  inj' := unit_group_injective,
  map_rel_iff' := λ A B, unit_group_le_unit_group }

lemma unit_group_strict_mono : strict_mono (unit_group : valuation_subring K → subgroup _) :=
unit_group_order_embedding.strict_mono

end unit_group

section nonunits

/-- The nonunits of a valuation subring of `K`, as a subsemigroup of `K`-/
def nonunits : subsemigroup K :=
{ carrier := { x | A.valuation x < 1 },
  mul_mem' := λ a b ha hb, (mul_lt_mul₀ ha hb).trans_eq $ mul_one _ }

lemma mem_nonunits_iff {x : K} : x ∈ A.nonunits ↔ A.valuation x < 1 := iff.rfl

lemma nonunits_le_nonunits {A B : valuation_subring K} :
  B.nonunits ≤ A.nonunits ↔ A ≤ B :=
begin
  split,
  { intros h x hx,
    by_cases h_1 : x = 0, { simp only [h_1, zero_mem] },
    rw [← valuation_le_one_iff, ← not_lt, valuation.one_lt_val_iff _ h_1] at hx ⊢,
    by_contra h_2, from hx (h h_2) },
  { intros h x hx,
    by_contra h_1, from not_lt.2 (monotone_map_of_le _ _ h (not_lt.1 h_1)) hx }
end

lemma nonunits_injective :
  function.injective (nonunits : valuation_subring K → subsemigroup _) :=
λ A B h, by { simpa only [le_antisymm_iff, nonunits_le_nonunits] using h.symm }

lemma nonunits_inj {A B : valuation_subring K} : A.nonunits = B.nonunits ↔ A = B :=
nonunits_injective.eq_iff

/-- The map on valuation subrings to their nonunits is a dual order embedding. -/
def nonunits_order_embedding :
  valuation_subring K ↪o (subsemigroup K)ᵒᵈ :=
{ to_fun := λ A, A.nonunits,
  inj' := nonunits_injective,
  map_rel_iff' := λ A B, nonunits_le_nonunits }

variables {A}

 /-- The elements of `A.nonunits` are those of the maximal ideal of `A` after coercion to `K`.

See also `mem_nonunits_iff_exists_mem_maximal_ideal`, which gets rid of the coercion to `K`,
at the expense of a more complicated right hand side.
 -/
theorem coe_mem_nonunits_iff {a : A} : (a : K) ∈ A.nonunits ↔ a ∈ local_ring.maximal_ideal A :=
(valuation_lt_one_iff _ _).symm

lemma nonunits_le : A.nonunits ≤ A.to_subring.to_submonoid.to_subsemigroup :=
λ a ha, (A.valuation_le_one_iff _).mp (A.mem_nonunits_iff.mp ha).le

lemma nonunits_subset : (A.nonunits : set K) ⊆ A := nonunits_le

 /-- The elements of `A.nonunits` are those of the maximal ideal of `A`.

See also `coe_mem_nonunits_iff`, which has a simpler right hand side but requires the element
to be in `A` already.
 -/
theorem mem_nonunits_iff_exists_mem_maximal_ideal {a : K} :
  a ∈ A.nonunits ↔ ∃ ha, (⟨a, ha⟩ : A) ∈ local_ring.maximal_ideal A :=
⟨λ h, ⟨nonunits_subset h, coe_mem_nonunits_iff.mp h⟩,
 λ ⟨ha, h⟩, coe_mem_nonunits_iff.mpr h⟩

 /-- `A.nonunits` agrees with the maximal ideal of `A`, after taking its image in `K`. -/
theorem image_maximal_ideal : (coe : A → K) '' local_ring.maximal_ideal A = A.nonunits :=
begin
  ext a,
  simp only [set.mem_image, set_like.mem_coe, mem_nonunits_iff_exists_mem_maximal_ideal],
  erw subtype.exists,
  simp_rw [subtype.coe_mk, exists_and_distrib_right, exists_eq_right],
end

end nonunits

section principal_unit_group

/-- The principal unit group of a valuation subring, as a subgroup of `Kˣ`. -/
def principal_unit_group : subgroup Kˣ :=
{ carrier := { x | A.valuation (x - 1) < 1 },
  mul_mem' := begin
    intros a b ha hb,
    refine lt_of_le_of_lt _ (max_lt hb ha),
    rw [← one_mul (A.valuation (b - 1)), ← A.valuation.map_one_add_of_lt ha, add_sub_cancel'_right,
      ← valuation.map_mul, mul_sub_one, ← sub_add_sub_cancel],
    exact A.valuation.map_add _ _,
  end,
  one_mem' := by simp,
  inv_mem' := begin
    dsimp,
    intros a ha,
    conv {to_lhs, rw [← mul_one (A.valuation _), ← A.valuation.map_one_add_of_lt ha]},
    rwa [add_sub_cancel'_right, ← valuation.map_mul, sub_mul, units.inv_mul, ← neg_sub, one_mul,
      valuation.map_neg],
  end }

lemma principal_units_le_units : A.principal_unit_group ≤ A.unit_group :=
λ a h, by simpa only [add_sub_cancel'_right] using A.valuation.map_one_add_of_lt h

lemma mem_principal_unit_group_iff (x : Kˣ) :
  x ∈ A.principal_unit_group ↔ A.valuation ((x : K) - 1) < 1 := iff.rfl

lemma principal_unit_group_le_principal_unit_group {A B : valuation_subring K} :
  B.principal_unit_group ≤ A.principal_unit_group ↔ A ≤ B :=
begin
  split,
  { intros h x hx,
    by_cases h_1 : x = 0, { simp only [h_1, zero_mem] },
    by_cases h_2 : x⁻¹ + 1 = 0,
    { rw [add_eq_zero_iff_eq_neg, inv_eq_iff_eq_inv, inv_neg, inv_one] at h_2,
      simpa only [h_2] using B.neg_mem _ B.one_mem },
    { rw [← valuation_le_one_iff, ← not_lt, valuation.one_lt_val_iff _ h_1, ← add_sub_cancel x⁻¹,
        ← units.coe_mk0 h_2, ← mem_principal_unit_group_iff] at hx ⊢,
      simpa only [hx] using @h (units.mk0 (x⁻¹ + 1) h_2) } },
  { intros h x hx,
    by_contra h_1, from not_lt.2 (monotone_map_of_le _ _ h (not_lt.1 h_1)) hx }
end

lemma principal_unit_group_injective :
  function.injective (principal_unit_group : valuation_subring K → subgroup _) :=
λ A B h, by { simpa [le_antisymm_iff, principal_unit_group_le_principal_unit_group] using h.symm }

lemma eq_iff_principal_unit_group {A B : valuation_subring K} :
  A = B ↔ A.principal_unit_group = B.principal_unit_group :=
principal_unit_group_injective.eq_iff.symm

/-- The map on valuation subrings to their principal unit groups is an order embedding. -/
def principal_unit_group_order_embedding :
  valuation_subring K ↪o (subgroup Kˣ)ᵒᵈ :=
{ to_fun := λ A, A.principal_unit_group,
  inj' := principal_unit_group_injective,
  map_rel_iff' := λ A B, principal_unit_group_le_principal_unit_group }

lemma coe_mem_principal_unit_group_iff {x : A.unit_group} :
  (x : Kˣ) ∈ A.principal_unit_group ↔
  A.unit_group_mul_equiv x ∈ (units.map (local_ring.residue A).to_monoid_hom).ker :=
begin
  rw [monoid_hom.mem_ker, units.ext_iff],
  let π := ideal.quotient.mk (local_ring.maximal_ideal A), convert_to _ ↔ π _ = 1,
  rw [← π.map_one, ← sub_eq_zero, ← π.map_sub, ideal.quotient.eq_zero_iff_mem,
    valuation_lt_one_iff],
  simpa,
end

/-- The principal unit group agrees with the kernel of the canonical map from
the units of `A` to the units of the residue field of `A`. -/
def principal_unit_group_equiv :
  A.principal_unit_group ≃* (units.map (local_ring.residue A).to_monoid_hom).ker :=
{ to_fun := λ x, ⟨A.unit_group_mul_equiv ⟨_, A.principal_units_le_units x.2⟩,
    A.coe_mem_principal_unit_group_iff.1 x.2⟩,
  inv_fun := λ x, ⟨A.unit_group_mul_equiv.symm x,
    by { rw A.coe_mem_principal_unit_group_iff, simpa using set_like.coe_mem x }⟩,
  left_inv := λ x, by simp,
  right_inv := λ x, by simp,
  map_mul' := λ x y, by refl, }

@[simp]
lemma principal_unit_group_equiv_apply (a : A.principal_unit_group) :
  (principal_unit_group_equiv A a : K) = a := rfl

@[simp]
lemma principal_unit_group_symm_apply
  (a : (units.map (local_ring.residue A).to_monoid_hom).ker) :
  (A.principal_unit_group_equiv.symm a : K) = a := rfl

/-- The canonical map from the unit group of `A` to the units of the residue field of `A`. -/
def unit_group_to_residue_field_units :
  A.unit_group →* (local_ring.residue_field A)ˣ :=
monoid_hom.comp (units.map $ (ideal.quotient.mk _).to_monoid_hom)
  A.unit_group_mul_equiv.to_monoid_hom

@[simp]
lemma coe_unit_group_to_residue_field_units_apply (x : A.unit_group) :
  (A.unit_group_to_residue_field_units x : (local_ring.residue_field A) ) =
  (ideal.quotient.mk _ (A.unit_group_mul_equiv x : A)) := rfl

lemma ker_unit_group_to_residue_field_units :
  A.unit_group_to_residue_field_units.ker = A.principal_unit_group.comap A.unit_group.subtype :=
by { ext, simpa only [subgroup.mem_comap, subgroup.coe_subtype, coe_mem_principal_unit_group_iff] }

lemma surjective_unit_group_to_residue_field_units :
  function.surjective A.unit_group_to_residue_field_units :=
(local_ring.surjective_units_map_of_local_ring_hom _
ideal.quotient.mk_surjective local_ring.is_local_ring_hom_residue).comp (mul_equiv.surjective _)

/-- The quotient of the unit group of `A` by the principal unit group of `A` agrees with
the units of the residue field of `A`. -/
def units_mod_principal_units_equiv_residue_field_units :
  (A.unit_group ⧸ (A.principal_unit_group.comap A.unit_group.subtype)) ≃*
  (local_ring.residue_field A)ˣ :=
(quotient_group.quotient_mul_equiv_of_eq A.ker_unit_group_to_residue_field_units.symm).trans
  (quotient_group.quotient_ker_equiv_of_surjective _ A.surjective_unit_group_to_residue_field_units)

@[simp]
lemma units_mod_principal_units_equiv_residue_field_units_comp_quotient_group_mk :
  A.units_mod_principal_units_equiv_residue_field_units.to_monoid_hom.comp
  (quotient_group.mk' _) = A.unit_group_to_residue_field_units := rfl

@[simp]
lemma units_mod_principal_units_equiv_residue_field_units_comp_quotient_group_mk_apply
  (x : A.unit_group) :
  A.units_mod_principal_units_equiv_residue_field_units.to_monoid_hom
  (quotient_group.mk x) = A.unit_group_to_residue_field_units x := rfl

end principal_unit_group

/-! ### Pointwise actions

This transfers the action from `subring.pointwise_mul_action`, noting that it only applies when
the action is by a group. Notably this provides an instances when `G` is `K ≃+* K`.

These instances are in the `pointwise` locale.

The lemmas in this section are copied from `ring_theory/subring/pointwise.lean`; try to keep these
in sync.
-/
section pointwise_actions
open_locale pointwise

variables {G : Type*} [group G] [mul_semiring_action G K]

/-- The action on a valuation subring corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
def pointwise_has_smul : has_smul G (valuation_subring K) :=
{ smul := λ g S,
  -- TODO: if we add `valuation_subring.map` at a later date, we should use it here
  { mem_or_inv_mem' := λ x, (mem_or_inv_mem S (g⁻¹ • x)).imp
      (subring.mem_pointwise_smul_iff_inv_smul_mem.mpr)
      (λ h, subring.mem_pointwise_smul_iff_inv_smul_mem.mpr $ by rwa smul_inv''),
    .. g • S.to_subring } }

localized "attribute [instance] valuation_subring.pointwise_has_smul" in pointwise
open_locale pointwise

@[simp] lemma coe_pointwise_smul (g : G) (S : valuation_subring K) : ↑(g • S) = g • (S : set K) :=
rfl

@[simp] lemma pointwise_smul_to_subring (g : G) (S : valuation_subring K) :
  (g • S).to_subring = g • S.to_subring := rfl

/-- The action on a valuation subring corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale.

This is a stronger version of `valuation_subring.pointwise_has_smul`. -/
def pointwise_mul_action : mul_action G (valuation_subring K) :=
to_subring_injective.mul_action to_subring pointwise_smul_to_subring

localized "attribute [instance] valuation_subring.pointwise_mul_action" in pointwise
open_locale pointwise

lemma smul_mem_pointwise_smul (g : G) (x : K) (S : valuation_subring K) : x ∈ S → g • x ∈ g • S :=
(set.smul_mem_smul_set : _ → _ ∈ g • (S : set K))

lemma mem_smul_pointwise_iff_exists (g : G) (x : K) (S : valuation_subring K) :
  x ∈ g • S ↔ ∃ (s : K), s ∈ S ∧ g • s = x :=
(set.mem_smul_set : x ∈ g • (S : set K) ↔ _)

instance pointwise_central_scalar [mul_semiring_action Gᵐᵒᵖ K] [is_central_scalar G K] :
  is_central_scalar G (valuation_subring K) :=
⟨λ g S, to_subring_injective $ by exact op_smul_eq_smul g S.to_subring⟩

@[simp] lemma smul_mem_pointwise_smul_iff {g : G} {S : valuation_subring K} {x : K} :
  g • x ∈ g • S ↔ x ∈ S :=
set.smul_mem_smul_set_iff

lemma mem_pointwise_smul_iff_inv_smul_mem {g : G} {S : valuation_subring K} {x : K} :
  x ∈ g • S ↔ g⁻¹ • x ∈ S :=
set.mem_smul_set_iff_inv_smul_mem

lemma mem_inv_pointwise_smul_iff {g : G} {S : valuation_subring K} {x : K} :
  x ∈ g⁻¹ • S ↔ g • x ∈ S :=
set.mem_inv_smul_set_iff

@[simp] lemma pointwise_smul_le_pointwise_smul_iff {g : G} {S T : valuation_subring K} :
  g • S ≤ g • T ↔ S ≤ T :=
set.set_smul_subset_set_smul_iff

lemma pointwise_smul_subset_iff {g : G} {S T : valuation_subring K} : g • S ≤ T ↔ S ≤ g⁻¹ • T :=
set.set_smul_subset_iff

lemma subset_pointwise_smul_iff {g : G} {S T : valuation_subring K} : S ≤ g • T ↔ g⁻¹ • S ≤ T :=
set.subset_set_smul_iff

end pointwise_actions

section

variables {L J: Type*} [field L] [field J]

/-- The pullback of a valuation subring `A` along a ring homomorphism `K →+* L`. -/
def comap (A : valuation_subring L) (f : K →+* L) :
  valuation_subring K :=
{ mem_or_inv_mem' := λ k, by simp [valuation_subring.mem_or_inv_mem],
  ..(A.to_subring.comap f) }

@[simp]
lemma coe_comap (A : valuation_subring L) (f : K →+* L) : (A.comap f : set K) = f ⁻¹' A := rfl

@[simp]
lemma mem_comap {A : valuation_subring L} {f : K →+* L} {x : K} : x ∈ A.comap f ↔ f x ∈ A := iff.rfl

lemma comap_comap (A : valuation_subring J) (g : L →+* J) (f : K →+* L) :
  (A.comap g).comap f = A.comap (g.comp f) :=
rfl

end

end valuation_subring

namespace valuation

variables {Γ : Type*} [linear_ordered_comm_group_with_zero Γ] (v : valuation K Γ) (x : Kˣ)

@[simp] lemma mem_unit_group_iff : x ∈ v.valuation_subring.unit_group ↔ v x = 1 :=
(valuation.is_equiv_iff_val_eq_one _ _).mp (valuation.is_equiv_valuation_valuation_subring _).symm

end valuation
