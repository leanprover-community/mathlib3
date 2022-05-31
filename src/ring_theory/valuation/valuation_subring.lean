/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Junyan Xu
-/
import ring_theory.valuation.valuation_ring
import ring_theory.localization.as_subring
import algebraic_geometry.prime_spectrum.basic
import algebra.group_with_zero.basic

/-!

# Valuation subrings of a field

# Projects

The order structure on `valuation_subring K`.

-/

open_locale classical
noncomputable theory

variables (K : Type*) [field K]

/-- A valuation subring of a field `K` is a subring `A` such that for every `x : K`,
either `x ∈ A` or `x⁻¹ ∈ K`. -/
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
    { use ⟨a/b,hh⟩, right, ext, field_simp, ring },
    { rw (show (a/b : K)⁻¹ = b/a, by field_simp) at hh,
      use ⟨b/a,hh⟩, left, ext, field_simp, ring },
  end }

instance : algebra A K :=
show algebra A.to_subring K, by apply_instance

@[simp]
lemma algebra_map_apply (a : A) : algebra_map A K a = a := rfl

instance : is_fraction_ring A K :=
{ map_units := λ ⟨y,hy⟩,
    (units.mk0 (y : K) (λ c, non_zero_divisors.ne_zero hy $ subtype.ext c)).is_unit,
  surj := λ z, begin
    by_cases z = 0, { use (0,1), simp [h] },
    cases A.mem_or_inv_mem z with hh hh,
    { use (⟨z,hh⟩,1), simp },
    { refine ⟨⟨1,⟨⟨_,hh⟩,_⟩⟩, mul_inv_cancel h⟩,
      exact mem_non_zero_divisors_iff_ne_zero.2 (λ c, h (inv_eq_zero.mp (congr_arg coe c))) },
  end,
  eq_iff_exists := λ a b, ⟨ λ h, ⟨1, by { ext, simpa using h }⟩, λ ⟨c,h⟩,
    congr_arg coe ((mul_eq_mul_right_iff.1 h).resolve_right (non_zero_divisors.ne_zero c.2)) ⟩ }

/-- The value group of the valuation associated to `A`. -/
@[derive linear_ordered_comm_group_with_zero]
def value_group := valuation_ring.value_group A K

/-- Any valuation subring of `K` induces a natural valuation on `K`. -/
def valuation : valuation K A.value_group := valuation_ring.valuation A K

instance inhabited_value_group : inhabited A.value_group := ⟨A.valuation 0⟩

lemma valuation_le_one (a : A) : A.valuation a ≤ 1 :=
(valuation_ring.mem_integer_iff A K _).2 ⟨a,rfl⟩

lemma mem_of_valuation_le_one (x : K) (h : A.valuation x ≤ 1) : x ∈ A :=
let ⟨a,ha⟩ := (valuation_ring.mem_integer_iff A K x).1 h in ha ▸ a.2

lemma valuation_le_one_iff (x : K) : A.valuation x ≤ 1 ↔ x ∈ A :=
⟨mem_of_valuation_le_one _ _, λ ha, A.valuation_le_one ⟨x,ha⟩⟩

lemma valuation_eq_iff (x y : K) : A.valuation x = A.valuation y ↔
  ∃ a : Aˣ, (a : K) * y = x := quotient.eq'

lemma valuation_le_iff (x y : K) : A.valuation x ≤ A.valuation y ↔
  ∃ a : A, (a : K) * y = x := iff.rfl

lemma valuation_surjective : function.surjective A.valuation := surjective_quot_mk _

@[simp]
lemma valuation_unit (a : Aˣ) : A.valuation a = 1 :=
 by { rw [← A.valuation.map_one, valuation_eq_iff], use a, simp }

lemma valuation_eq_one_iff (a : A) : is_unit a ↔ A.valuation a = 1 :=
⟨ λ h, A.valuation_unit h.unit,
  λ h, begin
    have ha : (a : K) ≠ 0,
    { intro c, rw [c, A.valuation.map_zero] at h, exact zero_ne_one h },
    have ha' : (a : K)⁻¹ ∈ A,
    { rw [← valuation_le_one_iff, A.valuation.map_inv, h, inv_one] },
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
{ to_fun := quotient.map' id $ λ x y ⟨u,hu⟩, ⟨units.map (R.inclusion S h).to_monoid_hom u, hu⟩,
  map_zero' := rfl,
  map_one' := rfl,
  map_mul' := by { rintro ⟨⟩ ⟨⟩, refl } }

@[mono]
lemma monotone_map_of_le (R S : valuation_subring K) (h : R ≤ S) :
  monotone (R.map_of_le S h) :=
by { rintros ⟨⟩ ⟨⟩ ⟨a,ha⟩, exact ⟨R.inclusion S h a, ha⟩ }

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
of_le A (localization.subalgebra.of_field K P.prime_compl $
  le_non_zero_divisors_of_no_zero_divisors $ not_not_intro P.zero_mem).to_subring $
  λ a ha, subalgebra.algebra_map_mem _ (⟨a,ha⟩ : A)

instance of_prime_algebra (A : valuation_subring K) (P : ideal A) [P.is_prime] :
  algebra A (A.of_prime P) := subalgebra.algebra _

instance of_prime_scalar_tower (A : valuation_subring K) (P : ideal A) [P.is_prime] :
  is_scalar_tower A (A.of_prime P) K := is_scalar_tower.subalgebra' A K K _

instance of_prime_localization (A : valuation_subring K) (P : ideal A) [P.is_prime] :
  is_localization.at_prime (A.of_prime P) P :=
by apply localization.subalgebra.is_localization_of_field K

lemma le_of_prime (A : valuation_subring K) (P : ideal A) [P.is_prime] :
  A ≤ of_prime A P :=
λ a ha, subalgebra.algebra_map_mem _ (⟨a,ha⟩ : A)

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
  { rintro ⟨a,r,hr,rfl⟩, apply mul_mem, { exact h a.2 },
    { rw [← valuation_le_one_iff, valuation.map_inv, ← inv_one, inv_le_inv₀],
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
        apply is_unit_of_mul_eq_one _ (⟨x,hx⟩ : S),
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
  left_inv := λ P, by { ext1, simpa },
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
{ le_total := let i : is_total (prime_spectrum A) (≤) := (subtype.rel_embedding _ _).is_total in
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
      rw [v.map_inv, ← inv_one, inv_le_inv₀],
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
{ carrier := { x | A.valuation x = 1 },
  mul_mem' := begin
    intros a b ha hb,
    dsimp at *,
    rw [A.valuation.map_mul, ha, hb, one_mul],
  end,
  one_mem' := A.valuation.map_one,
  inv_mem' := begin
    intros a ha,
    dsimp at *,
    push_cast,
    rw [A.valuation.map_inv, ha, inv_one],
  end }

lemma mem_unit_group_iff (x : Kˣ) : x ∈ A.unit_group ↔ A.valuation x = 1 := iff.refl _

lemma eq_iff_unit_group (A B : valuation_subring K) :
  A = B ↔ A.unit_group = B.unit_group :=
begin
  rw [← A.valuation_subring_valuation, ← B.valuation_subring_valuation,
    ← valuation.is_equiv_iff_valuation_subring,
    A.valuation_subring_valuation, B.valuation_subring_valuation,
    valuation.is_equiv_iff_val_eq_one, set_like.ext_iff],
  split,
  { intros h x, apply h },
  { intros h x,
    by_cases hx : x = 0, { simp only [hx, valuation.map_zero, zero_ne_one] },
    exact h (units.mk0 x hx) }
end

/-- `A.unit_group` agrees with the units of `A`. -/
def unit_group_equiv : A.unit_group ≃* Aˣ :=
{ to_fun := λ x,
  ⟨⟨x, (A.valuation_le_one_iff _).1 (le_of_eq x.2)⟩,⟨x⁻¹,
  begin
    rw ← A.valuation_le_one_iff,
    apply le_of_eq,
    rw [A.valuation.map_inv, inv_eq_one₀],
    exact x.2,
  end⟩,
    by { ext, exact mul_inv_cancel x.1.ne_zero },
    by { ext, exact inv_mul_cancel x.1.ne_zero }⟩,
  inv_fun := λ x, ⟨⟨x, (x : K)⁻¹,
    mul_inv_cancel ((units.map A.subtype.to_monoid_hom x).ne_zero),
    inv_mul_cancel ((units.map A.subtype.to_monoid_hom x).ne_zero)⟩, begin
      rw mem_unit_group_iff, simpa using A.valuation_unit x,
    end⟩,
  left_inv := λ a, by { ext, refl },
  right_inv := λ a, by { ext, refl },
  map_mul' := λ a b, by { ext, refl } }

@[simp]
lemma coe_unit_group_equiv_apply (a : A.unit_group) :
  (A.unit_group_equiv a : K) = a := rfl

@[simp]
lemma coe_unit_group_equiv_symm_apply (a : Aˣ) :
  (A.unit_group_equiv.symm a : K) = a := rfl

def unit_group_ordered_embedding : valuation_subring K ↪o subgroup Kˣ :=
{ to_fun := λ A, A.unit_group,
  inj' := λ A B h, by rwa eq_iff_unit_group,
  map_rel_iff' := begin
    intros A B,
    dsimp,
    split,
    { rintros h x hx,
      by_cases h_1 : x = 0, { simp only [h_1, zero_mem] },
      rw [← A.valuation_le_one_iff x, le_iff_lt_or_eq] at hx,
      cases hx,
      { have hh : ¬1 + x = 0,
        { by_contra h_2,
          rw add_eq_zero_iff_neg_eq at h_2,
          apply_fun A.valuation at h_2,
          rwa [← h_2, valuation.map_neg, valuation.map_one, lt_self_iff_false] at hx },
        have := h (show (units.mk0 (1 + x) hh) ∈ A.unit_group,
          by exact A.valuation.map_one_add_of_lt hx),
        simpa using B.add_mem _ _
          (show 1 + x ∈ B, by exact set_like.coe_mem ((B.unit_group_equiv ⟨_, this⟩) : B))
          (B.neg_mem _ B.one_mem),
      },
      { have := h (show (units.mk0 x h_1) ∈ A.unit_group, by exact hx),
        refine set_like.coe_mem ((B.unit_group_equiv ⟨_, this⟩) : B) }
    },
    { rintros h x (hx : A.valuation x = 1),
      apply_fun A.map_of_le B h at hx,
      simpa using hx }
  end }

def maximal_ideal : subsemigroup K :=
{ carrier := { x | A.valuation x < 1 },
  mul_mem' := λ a b ha hb, by { simpa using mul_lt_mul₀ ha hb } }

lemma mem_maximal_ideal_iff (x : K) : x ∈ A.maximal_ideal ↔ A.valuation x < 1 := iff.refl _

lemma eq_iff_maximal_ideal (A B : valuation_subring K) :
  A = B ↔ A.maximal_ideal = B.maximal_ideal :=
begin
  simp_rw [← A.valuation_subring_valuation, ← B.valuation_subring_valuation,
    ← valuation.is_equiv_iff_valuation_subring,
    A.valuation_subring_valuation, B.valuation_subring_valuation,
    valuation.is_equiv_iff_val_lt_one, set_like.ext_iff, mem_maximal_ideal_iff],
end

/-- `A.maximal_ideal` agrees with the maximal ideal of `A`. -/
def maximal_ideal_equiv : A.maximal_ideal ≃ local_ring.maximal_ideal A :=
{ to_fun := λ a, ⟨⟨a,(A.valuation_le_one_iff _).1 (le_of_lt a.2)⟩,(A.valuation_lt_one_iff _).2 a.2⟩,
  inv_fun := λ a, ⟨a,(A.valuation_lt_one_iff _).1 a.2⟩,
  left_inv := λ a, by { ext, refl },
  right_inv := λ a, by { ext, refl } }

@[simp]
lemma coe_maximal_ideal_equiv_apply (a : A.maximal_ideal) :
  (A.maximal_ideal_equiv a : K) = a := rfl

@[simp]
lemma coe_maximal_ideal_equiv_symm_apply (a : local_ring.maximal_ideal A) :
  (A.maximal_ideal_equiv.symm a : K) = a := rfl

@[simp]
lemma maximal_ideal_equiv_map_mul (a b : A.maximal_ideal) :
  A.maximal_ideal_equiv (a * b) = (A.maximal_ideal_equiv a : A) • A.maximal_ideal_equiv b := rfl

@[simp]
lemma maximal_ideal_equiv_symm_map_smul (a b : local_ring.maximal_ideal A) :
  A.maximal_ideal_equiv.symm ((a : A) • b) =
  A.maximal_ideal_equiv.symm a * A.maximal_ideal_equiv.symm b := rfl

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
  one_mem' := by { simpa using zero_lt_one₀ },
  inv_mem' := begin
    rintros a ha,
    rwa [set.mem_set_of_eq, ← mul_one (A.valuation (_)), ← A.valuation.map_one_add_of_lt ha,
      add_sub_cancel'_right, ← valuation.map_mul, sub_mul, units.inv_mul, one_mul,
      ← neg_sub (a : K), valuation.map_neg, ← add_sub_cancel'_right _ (a : K),
      A.valuation.map_one_add_of_lt ha, add_sub_cancel'],
  end }

lemma mem_principal_unit_group_iff (x : Kˣ) :
  x ∈ A.principal_unit_group ↔ A.valuation ((x : K) - 1) < 1 := iff.refl _

lemma eq_iff_principal_unit_group (A B : valuation_subring K) :
  A = B ↔ A.principal_unit_group = B.principal_unit_group :=
begin
  simp_rw [← A.valuation_subring_valuation, ← B.valuation_subring_valuation,
    ← valuation.is_equiv_iff_valuation_subring,
    A.valuation_subring_valuation, B.valuation_subring_valuation,
    valuation.is_equiv_iff_val_sub_one_lt_one, set_like.ext_iff],
  split,
  { intros h x, apply h },
  { intros h x,
    by_cases hx : x = 0,
    { simp only [hx, zero_sub, valuation.map_neg, valuation.map_one, lt_self_iff_false], },
    { exact h (units.mk0 x hx) } }
end

lemma one_lt_valuation_iff_valuation_inv_lt_one (x : K) :
  1 < A.valuation x ↔ A.valuation x⁻¹ < 1 :=
begin
  sorry,
end

def principal_unit_group_ordered_embedding :
  valuation_subring K ↪o (subgroup Kˣ)ᵒᵈ :=
{ to_fun := λ A, A.principal_unit_group,
  inj' := λ A B h, by rwa eq_iff_principal_unit_group,
  map_rel_iff' := begin
    intros A B,
    dsimp,
    split,
    { rintros h x hx,
      by_cases h_1 : x = 0, { simp only [h_1, zero_mem] },
      by_contra h_2,
      rw [← valuation_le_one_iff, not_le, B.one_lt_valuation_iff_valuation_inv_lt_one x,
        ← add_sub_cancel x⁻¹ 1] at h_2,
      have hh : ¬x⁻¹ + 1 = 0,
      { by_contra,
        rwa [h, zero_sub, valuation.map_neg, valuation.map_one, lt_self_iff_false] at h_2 },
      rw [← units.coe_mk0 hh, ← mem_principal_unit_group_iff] at h_2,
      have := h h_2,
      rw [mem_principal_unit_group_iff, units.coe_mk0 hh, add_sub_cancel, valuation.map_inv,
        ← inv_one, inv_lt_inv₀ (A.valuation.ne_zero_iff.2 h_1) one_ne_zero, ← not_le,
        valuation_le_one_iff] at this,
      exact this hx,
    },
    { rintros h x hx,
      by_contra h_1,
      cases lt_or_eq_of_le (le_of_not_lt ((A.mem_principal_unit_group_iff _).not.1 h_1)),
      { have := not_le_of_lt h_2,
        rw valuation_le_one_iff at this,
        have p : (x : K) ∉ A,
        { by_contra h_3,
          simpa [← sub_eq_add_neg] using A.add_mem _ _ h_3 (A.neg_mem _ A.one_mem) },
        rw [← valuation_le_one_iff, not_le, A.one_lt_valuation_iff_valuation_inv_lt_one x] at p,
        have q := A.valuation.map_one_sub_of_lt p,
        have tdo : 1 - (x : K)⁻¹ ≠ 0,
        { by_contra,
          rw sub_eq_zero at h,
          apply_fun A.valuation at h,
          rw valuation.map_one at h,
          rwa [h, lt_self_iff_false] at p,
        },
        rw [← units.coe_mk0 tdo, ← mem_unit_group_iff] at q,
        rw ← unit_group_ordered_embedding.map_rel_iff' at h,
        have r := h q,
        change units.mk0 (1 - (↑x)⁻¹) tdo ∈ B.unit_group at r,
        rw mem_unit_group_iff at r,
        change B.valuation (1 - x⁻¹) = 1 at r,
        have s := B.valuation.map_one_add_of_lt hx,
        rw add_sub_cancel'_right at s,
        rw [← mul_one (B.valuation (_)), ← r, ← valuation.map_mul, r, mul_sub, mul_one,
          ← units.coe_inv', units.mul_inv] at s,
        rwa [mem_principal_unit_group_iff, s, lt_self_iff_false] at hx,
      },
      { have hh : ¬(x : K) - 1 = 0,
        { by_contra,
          rw [mem_principal_unit_group_iff, h, valuation.map_zero, zero_lt_iff, not_ne_iff] at h_1,
          exact one_ne_zero h_1},
        symmetry' at h_2,
        rw [← units.coe_mk0 hh, ← mem_unit_group_iff] at h_2,
        have : units.mk0 ((x : K) - 1) hh ∈ B.unit_group,
        { rw ← unit_group_ordered_embedding.map_rel_iff' at h,
          exact h h_2 },
        rw mem_unit_group_iff at this,
        rwa [mem_principal_unit_group_iff, ← units.coe_mk0 hh, this, lt_self_iff_false] at hx,
      }
    }
  end }

lemma principal_units_le_units : A.principal_unit_group ≤ A.unit_group :=
λ a h, by {simpa using A.valuation.map_one_add_of_lt h}

def unit_group_mod_to_residue_field_units :
  (A.unit_group ⧸ (A.principal_unit_group.comap A.unit_group.subtype)) →*
  (local_ring.residue_field A)ˣ :=
quotient_group.lift _
(monoid_hom.comp (units.map $ (ideal.quotient.mk _).to_monoid_hom)
  A.unit_group_equiv.to_monoid_hom)
begin
  rintros ⟨a, ha⟩ h,
  simp only [ring_hom.to_monoid_hom_eq_coe, monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom,
    function.comp_app, subgroup.mem_comap, subgroup.coe_subtype, subgroup.coe_mk] at h ⊢,
  apply units.ext,
  dsimp,
  let π := ideal.quotient.mk (local_ring.maximal_ideal ↥A), change π _ = _,
  rwa [← π.map_one, ← sub_eq_zero, ← π.map_sub, ideal.quotient.eq_zero_iff_mem,
    valuation_lt_one_iff],
end

lemma unit_group_mod_to_residue_field_units_apply (x : A.unit_group) :
  (A.unit_group_mod_to_residue_field_units
    (quotient_group.mk x) : local_ring.residue_field A) =
    (ideal.quotient.mk _ (A.unit_group_equiv x : A)) := rfl

--- added by jack
def unit_group_to_residue_field_units :
  A.unit_group →* (local_ring.residue_field A)ˣ :=
(monoid_hom.comp (units.map $ (ideal.quotient.mk (local_ring.maximal_ideal A)).to_monoid_hom)
  A.unit_group_equiv.to_monoid_hom)

lemma ker_unit_group_to_residue_field_units :
  A.unit_group_to_residue_field_units.ker =
    subgroup.comap A.unit_group.subtype A.principal_unit_group :=
begin
  rw set_like.ext_iff,
  rintros ⟨x, hx⟩,
  rw [unit_group_to_residue_field_units, monoid_hom.mem_ker, ring_hom.to_monoid_hom_eq_coe,
    monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom, function.comp_app, subgroup.mem_comap,
    subgroup.coe_subtype, units.ext_iff],
  dsimp,
  let π := ideal.quotient.mk (local_ring.maximal_ideal ↥A), change π _ = _ ↔ _,
  rw [← π.map_one, ← sub_eq_zero, ← π.map_sub, ideal.quotient.eq_zero_iff_mem,
      valuation_lt_one_iff, mem_principal_unit_group_iff],
  refine ⟨λ h, h, λ h, h⟩,
end

lemma mem_residue_field_units_has_unit_rep (x : (local_ring.residue_field A)ˣ) :
  is_unit (quotient.out' (x : local_ring.residue_field A)) :=
begin
  by_contra,
  rw valuation_eq_one_iff at h,
  have := valuation_lt_one_or_eq_one _ (quotient.out' (x : local_ring.residue_field A)),
  rw or_iff_not_imp_right at this,
  simpa only [units.ne_zero, ← valuation_lt_one_iff, ← ideal.quotient.eq_zero_iff_mem,
    ← ideal.quotient.mk_eq_mk, ← submodule.quotient.mk'_eq_mk, quotient.out_eq'] using this h,
end

def range_unit_group_to_residue_field_units :
  A.unit_group_to_residue_field_units.range ≃* (local_ring.residue_field A)ˣ :=
begin
  sorry,
end
--- end of added by jack

def units_residue_field_equiv :
  (A.unit_group ⧸ (A.principal_unit_group.comap A.unit_group.subtype)) ≃*
  (local_ring.residue_field A)ˣ :=
mul_equiv.trans (mul_equiv.trans
  (quotient_group.equiv_quotient_of_eq A.ker_unit_group_to_residue_field_units).symm
  (quotient_group.quotient_ker_equiv_range A.unit_group_to_residue_field_units))
  A.range_unit_group_to_residue_field_units

/-
begin
  split,
  { have a := function.injective.comp
      (quotient_group.range_ker_lift_injective A.unit_group_to_residue_field_units)
      (mul_equiv.injective
      (quotient_group.equiv_quotient_of_eq A.ker_unit_group_to_residue_field_units).symm ),
    have b := mul_equiv.injective A.range_unit_group_to_residue_field_units,
    refine function.injective.comp b a,
  },
  { have a := function.surjective.comp
      (quotient_group.range_ker_lift_surjective A.unit_group_to_residue_field_units)
      (mul_equiv.surjective
      (quotient_group.equiv_quotient_of_eq A.ker_unit_group_to_residue_field_units).symm ),
    have b := mul_equiv.surjective A.range_unit_group_to_residue_field_units,
    refine function.injective.comp b a,
  }
end
-/

/-
def unit_group_mod_to_residue_field_units_two :
  (A.unit_group ⧸ (A.principal_unit_group.comap A.unit_group.subtype)) →*
  (local_ring.residue_field A)ˣ :=
  monoid_hom.comp (A.range_unit_group_to_residue_field_units.to_monoid_hom)
    ( monoid_hom.comp
    (quotient_group.range_ker_lift A.unit_group_to_residue_field_units)
    (quotient_group.equiv_quotient_of_eq A.ker_unit_group_to_residue_field_units).symm )
-/

/-
lemma mem_residue_field_units_has_unit_rep (x : (local_ring.residue_field A)ˣ) :
  is_unit (quotient.out' (x : local_ring.residue_field A)) :=
begin
  by_contra,
  rw valuation_eq_one_iff at h,
  have := valuation_lt_one_or_eq_one _ (quotient.out' (x : local_ring.residue_field A)),
  rw or_iff_not_imp_right at this,
  simpa only [units.ne_zero, ← valuation_lt_one_iff, ← ideal.quotient.eq_zero_iff_mem,
    ← ideal.quotient.mk_eq_mk, ← submodule.quotient.mk'_eq_mk, quotient.out_eq'] using this h,
end
-/

end unit_group

end valuation_subring

#lint
