/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.big_operators.basic
import data.set.pointwise.basic

/-!
# Results about pointwise operations on sets and big operators.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

namespace set

open_locale big_operators pointwise
open function

variables {ι α β F : Type*}

section monoid
variables [monoid α] [monoid β] [monoid_hom_class F α β]

@[to_additive]
lemma set.image_list_prod (f : F) : ∀ (l : list (set α)),
  (f : α → β) '' l.prod = (l.map (λ s, f '' s)).prod
| [] := set.image_one.trans $ congr_arg singleton (map_one f)
| (a :: as) := by rw [list.map_cons, list.prod_cons, list.prod_cons, set.image_mul,
  set.image_list_prod]

end monoid

section comm_monoid
variables [comm_monoid α] [comm_monoid β] [monoid_hom_class F α β]

@[to_additive]
lemma set.image_multiset_prod (f : F) : ∀ (m : multiset (set α)),
  (f : α → β) '' m.prod = (m.map (λ s, f '' s)).prod :=
quotient.ind $ by simpa only [multiset.quot_mk_to_coe, multiset.coe_prod, multiset.coe_map]
                 using set.image_list_prod f

@[to_additive]
lemma set.image_finset_prod (f : F) (m : finset ι) (s : ι → set α) :
  (f : α → β) '' (∏ i in m, s i) = (∏ i in m, f '' s i) :=
(set.image_multiset_prod f _).trans $ congr_arg multiset.prod $ multiset.map_map _ _ _

/-- The n-ary version of `set.mem_mul`. -/
@[to_additive /-" The n-ary version of `set.mem_add`. "-/]
lemma mem_finset_prod (t : finset ι) (f : ι → set α) (a : α) :
  a ∈ ∏ i in t, f i ↔ ∃ (g : ι → α) (hg : ∀ {i}, i ∈ t → g i ∈ f i), ∏ i in t, g i = a :=
begin
  classical,
  induction t using finset.induction_on with i is hi ih generalizing a,
  { simp_rw [finset.prod_empty, set.mem_one],
    exact ⟨λ h, ⟨λ i, a, λ i, false.elim, h.symm⟩, λ ⟨f, _, hf⟩, hf.symm⟩ },
  rw [finset.prod_insert hi, set.mem_mul],
  simp_rw [finset.prod_insert hi],
  simp_rw ih,
  split,
  { rintro ⟨x, y, hx, ⟨g, hg, rfl⟩, rfl⟩,
    refine ⟨function.update g i x, λ j hj, _, _⟩,
    obtain rfl | hj := finset.mem_insert.mp hj,
    { rw function.update_same, exact hx },
    { rw update_noteq (ne_of_mem_of_not_mem hj hi), exact hg hj, },
    rw [finset.prod_update_of_not_mem hi, function.update_same], },
  { rintro ⟨g, hg, rfl⟩,
    exact ⟨g i, is.prod g, hg (is.mem_insert_self _),
      ⟨g, λ i hi, hg (finset.mem_insert_of_mem hi), rfl⟩, rfl⟩ },
end

/-- A version of `set.mem_finset_prod` with a simpler RHS for products over a fintype. -/
@[to_additive /-" A version of `set.mem_finset_sum` with a simpler RHS for sums over a fintype. "-/]
lemma mem_fintype_prod [fintype ι] (f : ι → set α) (a : α) :
  a ∈ ∏ i, f i ↔ ∃ (g : ι → α) (hg : ∀ i, g i ∈ f i), ∏ i, g i = a :=
by { rw mem_finset_prod, simp }

/-- An n-ary version of `set.mul_mem_mul`. -/
@[to_additive /-" An n-ary version of `set.add_mem_add`. "-/]
lemma list_prod_mem_list_prod (t : list ι) (f : ι → set α)
  (g : ι → α) (hg : ∀ i ∈ t, g i ∈ f i) :
  (t.map g).prod ∈ (t.map f).prod :=
begin
  induction t with h tl ih,
  { simp_rw [list.map_nil, list.prod_nil, set.mem_one] },
  { simp_rw [list.map_cons, list.prod_cons],
    exact mul_mem_mul
      (hg h $ list.mem_cons_self _ _) (ih $ λ i hi, hg i $ list.mem_cons_of_mem _ hi) }
end

/-- An n-ary version of `set.mul_subset_mul`. -/
@[to_additive /-" An n-ary version of `set.add_subset_add`. "-/]
lemma list_prod_subset_list_prod (t : list ι) (f₁ f₂ : ι → set α) (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) :
  (t.map f₁).prod ⊆ (t.map f₂).prod :=
begin
  induction t with h tl ih,
  { refl, },
  { simp_rw [list.map_cons, list.prod_cons],
    exact mul_subset_mul
      (hf h $ list.mem_cons_self _ _) (ih $ λ i hi, hf i $ list.mem_cons_of_mem _ hi) }
end

@[to_additive]
lemma list_prod_singleton {M : Type*} [comm_monoid M] (s : list M) :
  (s.map $ λ i, ({i} : set M)).prod = {s.prod} :=
(map_list_prod (singleton_monoid_hom : M →* set M) _).symm

/-- An n-ary version of `set.mul_mem_mul`. -/
@[to_additive /-" An n-ary version of `set.add_mem_add`. "-/]
lemma multiset_prod_mem_multiset_prod (t : multiset ι) (f : ι → set α)
  (g : ι → α) (hg : ∀ i ∈ t, g i ∈ f i) :
  (t.map g).prod ∈ (t.map f).prod :=
begin
  induction t using quotient.induction_on,
  simp_rw [multiset.quot_mk_to_coe, multiset.coe_map, multiset.coe_prod],
  exact list_prod_mem_list_prod _ _ _ hg,
end

/-- An n-ary version of `set.mul_subset_mul`. -/
@[to_additive /-" An n-ary version of `set.add_subset_add`. "-/]
lemma multiset_prod_subset_multiset_prod (t : multiset ι) (f₁ f₂ : ι → set α)
  (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) :
  (t.map f₁).prod ⊆ (t.map f₂).prod :=
begin
  induction t using quotient.induction_on,
  simp_rw [multiset.quot_mk_to_coe, multiset.coe_map, multiset.coe_prod],
  exact list_prod_subset_list_prod _ _ _ hf,
end

@[to_additive]
lemma multiset_prod_singleton {M : Type*} [comm_monoid M] (s : multiset M) :
  (s.map $ λ i, ({i} : set M)).prod = {s.prod} :=
(map_multiset_prod (singleton_monoid_hom : M →* set M) _).symm

/-- An n-ary version of `set.mul_mem_mul`. -/
@[to_additive /-" An n-ary version of `set.add_mem_add`. "-/]
lemma finset_prod_mem_finset_prod (t : finset ι) (f : ι → set α)
  (g : ι → α) (hg : ∀ i ∈ t, g i ∈ f i) :
  ∏ i in t, g i ∈ ∏ i in t, f i :=
multiset_prod_mem_multiset_prod _ _ _ hg

/-- An n-ary version of `set.mul_subset_mul`. -/
@[to_additive /-" An n-ary version of `set.add_subset_add`. "-/]
lemma finset_prod_subset_finset_prod (t : finset ι) (f₁ f₂ : ι → set α)
  (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) :
  ∏ i in t, f₁ i ⊆ ∏ i in t, f₂ i :=
multiset_prod_subset_multiset_prod _ _ _ hf

@[to_additive]
lemma finset_prod_singleton {M ι : Type*} [comm_monoid M] (s : finset ι) (I : ι → M) :
  ∏ (i : ι) in s, ({I i} : set M) = {∏ (i : ι) in s, I i} :=
(map_prod (singleton_monoid_hom : M →* set M) _ _).symm

/-- The n-ary version of `set.image_mul_prod`. -/
@[to_additive "The n-ary version of `set.add_image_prod`. "]
lemma image_finset_prod_pi (l : finset ι) (S : ι → set α) :
  (λ f : ι → α, ∏ i in l, f i) '' (l : set ι).pi S = (∏ i in l, S i) :=
by { ext, simp_rw [mem_finset_prod, mem_image, mem_pi, exists_prop, finset.mem_coe] }

/-- A special case of `set.image_finset_prod_pi` for `finset.univ`. -/
@[to_additive "A special case of `set.image_finset_sum_pi` for `finset.univ`. "]
lemma image_fintype_prod_pi [fintype ι] (S : ι → set α) :
  (λ f : ι → α, ∏ i, f i) '' univ.pi S = (∏ i, S i) :=
by simpa only [finset.coe_univ] using image_finset_prod_pi finset.univ S

end comm_monoid

/-! TODO: define `decidable_mem_finset_prod` and `decidable_mem_finset_sum`. -/

end set
