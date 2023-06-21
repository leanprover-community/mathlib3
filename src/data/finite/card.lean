/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import set_theory.cardinal.finite

/-!

# Cardinality of finite types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The cardinality of a finite type `α` is given by `nat.card α`. This function has
the "junk value" of `0` for infinite types, but to ensure the function has valid
output, one just needs to know that it's possible to produce a `finite` instance
for the type. (Note: we could have defined a `finite.card` that required you to
supply a `finite` instance, but (a) the function would be `noncomputable` anyway
so there is no need to supply the instance and (b) the function would have a more
complicated dependent type that easily leads to "motive not type correct" errors.)

## Implementation notes

Theorems about `nat.card` are sometimes incidentally true for both finite and infinite
types. If removing a finiteness constraint results in no loss in legibility, we remove
it. We generally put such theorems into the `set_theory.cardinal.finite` module.

-/

noncomputable theory
open_locale classical

variables {α β γ : Type*}

/-- There is (noncomputably) an equivalence between a finite type `α` and `fin (nat.card α)`. -/
def finite.equiv_fin (α : Type*) [finite α] : α ≃ fin (nat.card α) :=
begin
  have := (finite.exists_equiv_fin α).some_spec.some,
  rwa nat.card_eq_of_equiv_fin this,
end

/-- Similar to `finite.equiv_fin` but with control over the term used for the cardinality. -/
def finite.equiv_fin_of_card_eq [finite α] {n : ℕ} (h : nat.card α = n) : α ≃ fin n :=
by { subst h, apply finite.equiv_fin }

lemma nat.card_eq (α : Type*) :
  nat.card α = if h : finite α then by exactI @fintype.card α (fintype.of_finite α) else 0 :=
begin
  casesI finite_or_infinite α,
  { letI := fintype.of_finite α,
    simp only [*, nat.card_eq_fintype_card, dif_pos] },
  { simp [*, not_finite_iff_infinite.mpr h] },
end

lemma finite.card_pos_iff [finite α] : 0 < nat.card α ↔ nonempty α :=
begin
  haveI := fintype.of_finite α,
  rw [nat.card_eq_fintype_card, fintype.card_pos_iff],
end

lemma finite.card_pos [finite α] [h : nonempty α] : 0 < nat.card α :=
finite.card_pos_iff.mpr h

namespace finite

lemma cast_card_eq_mk {α : Type*} [finite α] : ↑(nat.card α) = cardinal.mk α :=
cardinal.cast_to_nat_of_lt_aleph_0 (cardinal.lt_aleph_0_of_finite α)

lemma card_eq [finite α] [finite β] : nat.card α = nat.card β ↔ nonempty (α ≃ β) :=
by { haveI := fintype.of_finite α, haveI := fintype.of_finite β, simp [fintype.card_eq] }

lemma card_le_one_iff_subsingleton [finite α] : nat.card α ≤ 1 ↔ subsingleton α :=
by { haveI := fintype.of_finite α, simp [fintype.card_le_one_iff_subsingleton] }

lemma one_lt_card_iff_nontrivial [finite α] : 1 < nat.card α ↔ nontrivial α :=
by { haveI := fintype.of_finite α, simp [fintype.one_lt_card_iff_nontrivial] }

lemma one_lt_card [finite α] [h : nontrivial α] : 1 < nat.card α :=
one_lt_card_iff_nontrivial.mpr h

@[simp] lemma card_option [finite α] : nat.card (option α) = nat.card α + 1 :=
by { haveI := fintype.of_finite α, simp }

lemma card_le_of_injective [finite β] (f : α → β) (hf : function.injective f) :
  nat.card α ≤ nat.card β :=
by { haveI := fintype.of_finite β, haveI := fintype.of_injective f hf,
     simpa using fintype.card_le_of_injective f hf }

lemma card_le_of_embedding [finite β] (f : α ↪ β) : nat.card α ≤ nat.card β :=
card_le_of_injective _ f.injective

lemma card_le_of_surjective [finite α] (f : α → β) (hf : function.surjective f) :
  nat.card β ≤ nat.card α :=
by { haveI := fintype.of_finite α, haveI := fintype.of_surjective f hf,
     simpa using fintype.card_le_of_surjective f hf }

lemma card_eq_zero_iff [finite α] : nat.card α = 0 ↔ is_empty α :=
by { haveI := fintype.of_finite α, simp [fintype.card_eq_zero_iff] }

/-- If `f` is injective, then `nat.card α ≤ nat.card β`. We must also assume
  `nat.card β = 0 → nat.card α = 0` since `nat.card` is defined to be `0` for infinite types. -/
lemma card_le_of_injective' {f : α → β} (hf : function.injective f)
  (h : nat.card β = 0 → nat.card α = 0) : nat.card α ≤ nat.card β :=
(or_not_of_imp h).cases_on (λ h, le_of_eq_of_le h zero_le')
  (λ h, @card_le_of_injective α β (nat.finite_of_card_ne_zero h) f hf)

/-- If `f` is an embedding, then `nat.card α ≤ nat.card β`. We must also assume
  `nat.card β = 0 → nat.card α = 0` since `nat.card` is defined to be `0` for infinite types. -/
lemma card_le_of_embedding' (f : α ↪ β) (h : nat.card β = 0 → nat.card α = 0) :
  nat.card α ≤ nat.card β :=
card_le_of_injective' f.2 h

/-- If `f` is surjective, then `nat.card β ≤ nat.card α`. We must also assume
  `nat.card α = 0 → nat.card β = 0` since `nat.card` is defined to be `0` for infinite types. -/
lemma card_le_of_surjective' {f : α → β} (hf : function.surjective f)
  (h : nat.card α = 0 → nat.card β = 0) : nat.card β ≤ nat.card α :=
(or_not_of_imp h).cases_on (λ h, le_of_eq_of_le h zero_le')
  (λ h, @card_le_of_surjective α β (nat.finite_of_card_ne_zero h) f hf)

/-- NB: `nat.card` is defined to be `0` for infinite types. -/
lemma card_eq_zero_of_surjective {f : α → β} (hf : function.surjective f) (h : nat.card β = 0) :
  nat.card α = 0 :=
begin
  casesI finite_or_infinite β,
  { haveI := card_eq_zero_iff.mp h,
    haveI := function.is_empty f,
    exact nat.card_of_is_empty },
  { haveI := infinite.of_surjective f hf,
    exact nat.card_eq_zero_of_infinite },
end

/-- NB: `nat.card` is defined to be `0` for infinite types. -/
lemma card_eq_zero_of_injective [nonempty α] {f : α → β} (hf : function.injective f)
  (h : nat.card α = 0) : nat.card β = 0 :=
card_eq_zero_of_surjective (function.inv_fun_surjective hf) h

/-- NB: `nat.card` is defined to be `0` for infinite types. -/
lemma card_eq_zero_of_embedding [nonempty α] (f : α ↪ β) (h : nat.card α = 0) : nat.card β = 0 :=
card_eq_zero_of_injective f.2 h

lemma card_sum [finite α] [finite β] : nat.card (α ⊕ β) = nat.card α + nat.card β :=
by { haveI := fintype.of_finite α, haveI := fintype.of_finite β, simp }

lemma card_image_le {s : set α} [finite s] (f : α → β) : nat.card (f '' s) ≤ nat.card s :=
card_le_of_surjective _ set.surjective_onto_image

lemma card_range_le [finite α] (f : α → β) : nat.card (set.range f) ≤ nat.card α :=
card_le_of_surjective _ set.surjective_onto_range

theorem card_subtype_le [finite α] (p : α → Prop) :
  nat.card {x // p x} ≤ nat.card α :=
by { haveI := fintype.of_finite α, simpa using fintype.card_subtype_le p }

theorem card_subtype_lt [finite α] {p : α → Prop} {x : α} (hx : ¬ p x) :
  nat.card {x // p x} < nat.card α :=
by { haveI := fintype.of_finite α, simpa using fintype.card_subtype_lt hx }

end finite

namespace set

lemma card_union_le (s t : set α) : nat.card ↥(s ∪ t) ≤ nat.card s + nat.card t :=
begin
  casesI _root_.finite_or_infinite ↥(s ∪ t) with h h,
  { rw [finite_coe_iff, finite_union, ←finite_coe_iff, ←finite_coe_iff] at h,
    casesI h,
    rw [←cardinal.nat_cast_le, nat.cast_add,
        finite.cast_card_eq_mk, finite.cast_card_eq_mk, finite.cast_card_eq_mk],
    exact cardinal.mk_union_le s t },
  { exact nat.card_eq_zero_of_infinite.trans_le (zero_le _) },
end

end set
