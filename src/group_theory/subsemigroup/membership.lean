/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Jireh Loreaux
-/
import group_theory.subsemigroup.operations

/-!
# Subsemigroups: membership criteria

In this file we prove various facts about membership in a subsemigroup:

* `list_prod_mem`, `multiset_prod_mem`, `prod_mem`: if each element of a collection belongs
  to a multiplicative subsemigroup, then so does their product;
* `list_sum_mem`, `multiset_sum_mem`, `sum_mem`: if each element of a collection belongs
  to an additive subsemigroup, then so does their sum;
* `pow_mem`, `nsmul_mem`: if `x ∈ S` where `S` is a multiplicative (resp., additive) subsemigroup
  and `n` is a natural number, then `x^n` (resp., `n • x`) belongs to `S`;
* `mem_supr_of_directed`, `coe_supr_of_directed`, `mem_Sup_of_directed_on`,
  `coe_Sup_of_directed_on`: the supremum of a directed collection of subsemigroup is their union.
* `sup_eq_range`, `mem_sup`: supremum of two subsemigroups `S`, `T` of a commutative semigroup is
  the set of products;
* `closure_singleton_eq`, `mem_closure_singleton`, `mem_closure_pair`: the multiplicative (resp.,
  additive) closure of `{x}` consists of powers (resp., natural multiples) of `x`, and a similar
  result holds for the closure of `{x, y}`.

## Tags
subsemigroup, subsemigroups
-/

variables {M A B : Type*}

/-
Here, we can't have various product lemmas because we don't have a `1 : M`. Perhaps we need to
define a type of nonempty lists, and then products on those?
-/

section non_assoc
variables [has_mul M]

open set

namespace subsemigroup

-- TODO: this section can be generalized to `[mul_mem_class B M] [complete_lattice B]`
-- such that `complete_lattice.le` coincides with `set_like.le`

@[to_additive]
lemma mem_supr_of_directed {ι} {S : ι → subsemigroup M} (hS : directed (≤) S) {x : M} :
  x ∈ (⨆ i, S i) ↔ ∃ i, x ∈ S i :=
begin
  refine ⟨_, λ ⟨i, hi⟩, (set_like.le_def.1 $ le_supr S i) hi⟩,
  suffices : x ∈ closure (⋃ i, (S i : set M)) → ∃ i, x ∈ S i,
    by simpa only [closure_Union, closure_eq (S _)] using this,
  refine (λ hx, closure_induction hx (λ y hy, mem_Union.mp hy) _),
  { rintros x y ⟨i, hi⟩ ⟨j, hj⟩,
    rcases hS i j with ⟨k, hki, hkj⟩,
    exact ⟨k, (S k).mul_mem (hki hi) (hkj hj)⟩ }
end

@[to_additive]
lemma coe_supr_of_directed {ι} {S : ι → subsemigroup M} (hS : directed (≤) S) :
  ((⨆ i, S i : subsemigroup M) : set M) = ⋃ i, ↑(S i) :=
set.ext $ λ x, by simp [mem_supr_of_directed hS]

@[to_additive]
lemma mem_Sup_of_directed_on {S : set (subsemigroup M)} (Sne : S.nonempty)
  (hS : directed_on (≤) S) {x : M} :
  x ∈ Sup S ↔ ∃ s ∈ S, x ∈ s :=
by simp only [Sup_eq_supr', mem_supr_of_directed hS.directed_coe, set_coe.exists, subtype.coe_mk]

@[to_additive]
lemma coe_Sup_of_directed_on {S : set (subsemigroup M)} (Sne : S.nonempty)
  (hS : directed_on (≤) S) :
  (↑(Sup S) : set M) = ⋃ s ∈ S, ↑s :=
set.ext $ λ x, by simp [mem_Sup_of_directed_on Sne hS]

@[to_additive]
lemma mem_sup_left {S T : subsemigroup M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T :=
show S ≤ S ⊔ T, from le_sup_left

@[to_additive]
lemma mem_sup_right {S T : subsemigroup M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T :=
show T ≤ S ⊔ T, from le_sup_right

@[to_additive]
lemma mul_mem_sup {S T : subsemigroup M} {x y : M} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T :=
mul_mem (mem_sup_left hx) (mem_sup_right hy)

@[to_additive]
lemma mem_supr_of_mem {ι : Sort*} {S : ι → subsemigroup M} (i : ι) :
  ∀ {x : M}, x ∈ S i → x ∈ supr S :=
show S i ≤ supr S, from le_supr _ _

@[to_additive]
lemma mem_Sup_of_mem {S : set (subsemigroup M)} {s : subsemigroup M}
  (hs : s ∈ S) : ∀ {x : M}, x ∈ s → x ∈ Sup S :=
show s ≤ Sup S, from le_Sup hs

/-- An induction principle for elements of `⨆ i, S i`.
If `C` holds all elements of `S i` for all `i`, and is preserved under multiplication,
then it holds for all elements of the supremum of `S`. -/
@[elab_as_eliminator, to_additive /-" An induction principle for elements of `⨆ i, S i`.
If `C` holds all elements of `S i` for all `i`, and is preserved under addition,
then it holds for all elements of the supremum of `S`. "-/]
lemma supr_induction {ι : Sort*} (S : ι → subsemigroup M) {C : M → Prop} {x : M} (hx : x ∈ ⨆ i, S i)
  (hp : ∀ i (x ∈ S i), C x)
  (hmul : ∀ x y, C x → C y → C (x * y)) : C x :=
begin
  rw supr_eq_closure at hx,
  refine closure_induction hx (λ x hx, _) hmul,
  obtain ⟨i, hi⟩ := set.mem_Union.mp hx,
  exact hp _ _ hi,
end

/-- A dependent version of `subsemigroup.supr_induction`. -/
@[elab_as_eliminator, to_additive /-"A dependent version of `add_subsemigroup.supr_induction`. "-/]
lemma supr_induction' {ι : Sort*} (S : ι → subsemigroup M) {C : Π x, (x ∈ ⨆ i, S i) → Prop}
  (hp : ∀ i (x ∈ S i), C x (mem_supr_of_mem i ‹_›))
  (hmul : ∀ x y hx hy, C x hx → C y hy → C (x * y) (mul_mem ‹_› ‹_›))
  {x : M} (hx : x ∈ ⨆ i, S i) : C x hx :=
begin
  refine exists.elim _ (λ (hx : x ∈ ⨆ i, S i) (hc : C x hx), hc),
  refine supr_induction S hx (λ i x hx, _) (λ x y, _),
  { exact ⟨_, hp _ _ hx⟩ },
  { rintro ⟨_, Cx⟩ ⟨_, Cy⟩,
    exact ⟨_, hmul _ _ _ _ Cx Cy⟩ },
end

end subsemigroup

end non_assoc
