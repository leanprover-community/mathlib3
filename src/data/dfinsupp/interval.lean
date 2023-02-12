/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.locally_finite
import data.finset.pointwise
import data.fintype.big_operators
import data.dfinsupp.order

/-!
# Finite intervals of finitely supported functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the `locally_finite_order` instance for `Π₀ i, α i` when `α` itself is locally
finite and calculates the cardinality of its finite intervals.
-/

open dfinsupp finset
open_locale big_operators pointwise

variables {ι : Type*} {α : ι → Type*}

namespace finset
variables [decidable_eq ι] [Π i, has_zero (α i)] {s : finset ι} {f : Π₀ i, α i}
  {t : Π i, finset (α i)}

/-- Finitely supported product of finsets. -/
def dfinsupp (s : finset ι) (t : Π i, finset (α i)) : finset (Π₀ i, α i) :=
(s.pi t).map ⟨λ f, dfinsupp.mk s $ λ i, f i i.2, begin
  refine (mk_injective _).comp (λ f g h, _),
  ext i hi,
  convert congr_fun h ⟨i, hi⟩,
  end⟩

@[simp] lemma card_dfinsupp (s : finset ι) (t : Π i, finset (α i)) :
  (s.dfinsupp t).card = ∏ i in s, (t i).card :=
(card_map _).trans $ card_pi _ _

variables [Π i, decidable_eq (α i)]

lemma mem_dfinsupp_iff : f ∈ s.dfinsupp t ↔ f.support ⊆ s ∧ ∀ i ∈ s, f i ∈ t i :=
begin
  refine mem_map.trans ⟨_, _⟩,
  { rintro ⟨f, hf, rfl⟩,
    refine ⟨support_mk_subset, λ i hi, _⟩,
    convert mem_pi.1 hf i hi,
    exact mk_of_mem hi },
  { refine λ h, ⟨λ i _, f i, mem_pi.2 h.2, _⟩,
    ext i,
    dsimp,
    exact ite_eq_left_iff.2 (λ hi, (not_mem_support_iff.1 $ λ H, hi $ h.1 H).symm) }
end

/-- When `t` is supported on `s`, `f ∈ s.dfinsupp t` precisely means that `f` is pointwise in `t`.
-/
@[simp] lemma mem_dfinsupp_iff_of_support_subset {t : Π₀ i, finset (α i)} (ht : t.support ⊆ s) :
  f ∈ s.dfinsupp t ↔ ∀ i, f i ∈ t i :=
begin
  refine mem_dfinsupp_iff.trans (forall_and_distrib.symm.trans $ forall_congr $ λ i, ⟨λ h, _,
    λ h, ⟨λ hi, ht $ mem_support_iff.2 $ λ H, mem_support_iff.1 hi _, λ _, h⟩⟩),
  { by_cases hi : i ∈ s,
    { exact h.2 hi },
    { rw [not_mem_support_iff.1 (mt h.1 hi), not_mem_support_iff.1 (not_mem_mono ht hi)],
      exact zero_mem_zero } },
  { rwa [H, mem_zero] at h }
end

end finset

open finset

namespace dfinsupp

section bundled_singleton
variables [Π i, has_zero (α i)] {f : Π₀ i, α i} {i : ι} {a : α i}

/-- Pointwise `finset.singleton` bundled as a `dfinsupp`. -/
def singleton (f : Π₀ i, α i) : Π₀ i, finset (α i) :=
{ to_fun := λ i, {f i},
  support' := f.support'.map $ λ s, ⟨s, λ i, (s.prop i).imp id (congr_arg _) ⟩ }

lemma mem_singleton_apply_iff : a ∈ f.singleton i ↔ a = f i := mem_singleton

end bundled_singleton

section bundled_Icc
variables [Π i, has_zero (α i)] [Π i, partial_order (α i)] [Π i, locally_finite_order (α i)]
  {f g : Π₀ i, α i} {i : ι} {a : α i}

/-- Pointwise `finset.Icc` bundled as a `dfinsupp`. -/
def range_Icc (f g : Π₀ i, α i) : Π₀ i, finset (α i) :=
{ to_fun := λ i, Icc (f i) (g i),
  support' := f.support'.bind $ λ fs, g.support'.map $ λ gs,
    ⟨fs + gs, λ i, or_iff_not_imp_left.2 $ λ h, begin
      have hf : f i = 0 := (fs.prop i).resolve_left
        (multiset.not_mem_mono (multiset.le.subset $ multiset.le_add_right _ _) h),
      have hg : g i = 0 := (gs.prop i).resolve_left
        (multiset.not_mem_mono (multiset.le.subset $ multiset.le_add_left _ _) h),
      rw [hf, hg],
      exact Icc_self _,
    end⟩ }

@[simp] lemma range_Icc_apply (f g : Π₀ i, α i) (i : ι) : f.range_Icc g i = Icc (f i) (g i) := rfl

lemma mem_range_Icc_apply_iff : a ∈ f.range_Icc g i ↔ f i ≤ a ∧ a ≤ g i := mem_Icc

lemma support_range_Icc_subset [decidable_eq ι] [Π i, decidable_eq (α i)] :
  (f.range_Icc g).support ⊆ f.support ∪ g.support :=
begin
  refine λ x hx, _,
  by_contra,
  refine not_mem_support_iff.2 _ hx,
  rw [range_Icc_apply,
    not_mem_support_iff.1 (not_mem_mono (subset_union_left _ _) h),
      not_mem_support_iff.1 (not_mem_mono (subset_union_right _ _) h)],
  exact Icc_self _,
end


end bundled_Icc

section pi
variables [Π i, has_zero (α i)] [decidable_eq ι] [Π i, decidable_eq (α i)]

/-- Given a finitely supported function `f : Π₀ i, finset (α i)`, one can define the finset
`f.pi` of all finitely supported functions whose value at `i` is in `f i` for all `i`. -/
def pi (f : Π₀ i, finset (α i)) : finset (Π₀ i, α i) := f.support.dfinsupp f

@[simp] lemma mem_pi {f : Π₀ i, finset (α i)} {g : Π₀ i, α i} : g ∈ f.pi ↔ ∀ i, g i ∈ f i :=
mem_dfinsupp_iff_of_support_subset $ subset.refl _

@[simp] lemma card_pi (f : Π₀ i, finset (α i)) : f.pi.card = f.prod (λ i, (f i).card) :=
begin
  rw [pi, card_dfinsupp],
  exact finset.prod_congr rfl (λ i _, by simp only [pi.nat_apply, nat.cast_id]),
end

end pi

section locally_finite
variables [decidable_eq ι] [Π i, decidable_eq (α i)]
variables [Π i, partial_order (α i)] [Π i, has_zero (α i)] [Π i, locally_finite_order (α i)]

instance : locally_finite_order (Π₀ i, α i) :=
locally_finite_order.of_Icc (Π₀ i, α i)
  (λ f g, (f.support ∪ g.support).dfinsupp $ f.range_Icc g)
  (λ f g x, begin
    refine (mem_dfinsupp_iff_of_support_subset $ support_range_Icc_subset).trans _,
    simp_rw [mem_range_Icc_apply_iff, forall_and_distrib],
    refl,
  end)

variables (f g : Π₀ i, α i)

lemma Icc_eq : Icc f g = (f.support ∪ g.support).dfinsupp (f.range_Icc g) := rfl

lemma card_Icc : (Icc f g).card = ∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card :=
card_dfinsupp _ _

lemma card_Ico : (Ico f g).card = ∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card - 1 :=
by rw [card_Ico_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioc : (Ioc f g).card = ∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card - 1 :=
by rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioo : (Ioo f g).card = ∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card - 2 :=
by rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

end locally_finite

section canonically_ordered
variables [decidable_eq ι] [Π i, decidable_eq (α i)]
variables [Π i, canonically_ordered_add_monoid (α i)] [Π i, locally_finite_order (α i)]

variables (f : Π₀ i, α i)

lemma card_Iic : (Iic f).card = ∏ i in f.support, (Iic (f i)).card :=
by simp_rw [Iic_eq_Icc, card_Icc, dfinsupp.bot_eq_zero, support_zero, empty_union, zero_apply,
  bot_eq_zero]

lemma card_Iio : (Iio f).card = ∏ i in f.support, (Iic (f i)).card - 1 :=
by rw [card_Iio_eq_card_Iic_sub_one, card_Iic]

end canonically_ordered

end dfinsupp
