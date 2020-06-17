/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import group_theory.submonoid.operations
import algebra.big_operators
import algebra.free_monoid

/-!
# Submonoids

## Main definitions

* `submonoid.to_monoid`, `submonoid.to_comm_monoid`: a submonoid inherits a (commutative) monoid
  structure.
* `submonoid.subtype`: embedding of a submonoid into the ambient monoid.
* `submonoid.inclusion`: given two submonoids `S`, `T` such that `S ≤ T`, `S.inclusion T` is the
  inclusion of `S` into `T` as a monoid homomorphism;
* `mul_equiv.submonoid_congr`: converts a proof of `S = T` into a monoid isomorphism between `S`
  and `T`.
* `submonoid.prod`: product of two submonoids `s : submonoid M` and `t : submonoid N` as a submonoid
  of `M × N`;
* `submonoid.prod_equiv`: monoid isomorphism between `s.prod t` and `s × t`;
* `monoid_hom.mrestrict`: restrict a monoid homomorphism to a submonoid;
* `monoid_hom.cod_mrestrict`: restrict the codomain of a monoid homomorphism to a submonoid;
* `monoid_hom.mrange_restrict`: restrict a monoid homomorphism to its range;

## Implementation notes

Submonoid inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a submonoid's underlying set.

## Tags
submonoid, submonoids
-/

open_locale big_operators

variables {M : Type*} [monoid M] {s : set M}
variables {A : Type*} [add_monoid A] {t : set A}

namespace submonoid

variables (S : submonoid M)

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an `add_submonoid` is in the `add_submonoid`."]
lemma list_prod_mem : ∀ {l : list M}, (∀x ∈ l, x ∈ S) → l.prod ∈ S
| []     h := S.one_mem
| (a::l) h :=
  suffices a * l.prod ∈ S, by rwa [list.prod_cons],
  have a ∈ S ∧ (∀ x ∈ l, x ∈ S), from list.forall_mem_cons.1 h,
  S.mul_mem this.1 (list_prod_mem this.2)

/-- Product of a multiset of elements in a submonoid of a `comm_monoid` is in the submonoid. -/
@[to_additive "Sum of a multiset of elements in an `add_submonoid` of an `add_comm_monoid` is
in the `add_submonoid`."]
lemma multiset_prod_mem {M} [comm_monoid M] (S : submonoid M) (m : multiset M) :
  (∀a ∈ m, a ∈ S) → m.prod ∈ S :=
begin
  refine quotient.induction_on m (assume l hl, _),
  rw [multiset.quot_mk_to_coe, multiset.coe_prod],
  exact S.list_prod_mem hl
end

/-- Product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is in the
    submonoid. -/
@[to_additive "Sum of elements in an `add_submonoid` of an `add_comm_monoid` indexed by a `finset`
is in the `add_submonoid`."]
lemma prod_mem {M : Type*} [comm_monoid M] (S : submonoid M)
  {ι : Type*} {t : finset ι} {f : ι → M} (h : ∀c ∈ t, f c ∈ S) :
  ∏ c in t, f c ∈ S :=
S.multiset_prod_mem (t.1.map f) $ λ x hx, let ⟨i, hi, hix⟩ := multiset.mem_map.1 hx in hix ▸ h i hi

lemma pow_mem {x : M} (hx : x ∈ S) : ∀ n:ℕ, x^n ∈ S
| 0 := S.one_mem
| (n+1) := S.mul_mem hx (pow_mem n)

open set

@[to_additive]
lemma mem_supr_of_directed {ι} [hι : nonempty ι] {S : ι → submonoid M} (hS : directed (≤) S)
  {x : M} :
  x ∈ (⨆ i, S i) ↔ ∃ i, x ∈ S i :=
begin
  refine ⟨_, λ ⟨i, hi⟩, (le_def.1 $ le_supr S i) hi⟩,
  suffices : x ∈ closure (⋃ i, (S i : set M)) → ∃ i, x ∈ S i,
    by simpa only [closure_Union, closure_eq (S _)] using this,
  refine (λ hx, closure_induction hx (λ _, mem_Union.1) _ _),
  { exact hι.elim (λ i, ⟨i, (S i).one_mem⟩) },
  { rintros x y ⟨i, hi⟩ ⟨j, hj⟩,
    rcases hS i j with ⟨k, hki, hkj⟩,
    exact ⟨k, (S k).mul_mem (hki hi) (hkj hj)⟩ }
end

@[to_additive]
lemma coe_supr_of_directed {ι} [nonempty ι] {S : ι → submonoid M} (hS : directed (≤) S) :
  ((⨆ i, S i : submonoid M) : set M) = ⋃ i, ↑(S i) :=
set.ext $ λ x, by simp [mem_supr_of_directed hS]

@[to_additive]
lemma mem_Sup_of_directed_on {S : set (submonoid M)} (Sne : S.nonempty)
  (hS : directed_on (≤) S) {x : M} :
  x ∈ Sup S ↔ ∃ s ∈ S, x ∈ s :=
begin
  haveI : nonempty S := Sne.to_subtype,
  rw [Sup_eq_supr, supr_subtype', mem_supr_of_directed, subtype.exists],
  exact (directed_on_iff_directed _).1 hS
end

@[to_additive]
lemma coe_Sup_of_directed_on {S : set (submonoid M)} (Sne : S.nonempty) (hS : directed_on (≤) S) :
  (↑(Sup S) : set M) = ⋃ s ∈ S, ↑s :=
set.ext $ λ x, by simp [mem_Sup_of_directed_on Sne hS]

variables {N : Type*} [monoid N] {P : Type*} [monoid P]

end submonoid

namespace monoid_hom

variables {N : Type*} {P : Type*} [monoid N] [monoid P] (S : submonoid M)

open submonoid

/-- Restriction of a monoid hom to a submonoid of the domain. -/
@[to_additive "Restriction of an add_monoid hom to an `add_submonoid` of the domain."]
def mrestrict {N : Type*} [monoid N] (f : M →* N) (S : submonoid M) : S →* N := f.comp S.subtype

@[simp, to_additive]
lemma mrestrict_apply {N : Type*} [monoid N] (f : M →* N) (x : S) : f.mrestrict S x = f x := rfl

/-- Restriction of a monoid hom to a submonoid of the codomain. -/
@[to_additive "Restriction of an `add_monoid` hom to an `add_submonoid` of the codomain."]
def cod_mrestrict (f : M →* N) (S : submonoid N) (h : ∀ x, f x ∈ S) : M →* S :=
{ to_fun := λ n, ⟨f n, h n⟩,
  map_one' := subtype.eq f.map_one,
  map_mul' := λ x y, subtype.eq (f.map_mul x y) }

/-- Restriction of a monoid hom to its range interpreted as a submonoid. -/
@[to_additive "Restriction of an `add_monoid` hom to its range interpreted as a submonoid."]
def mrange_restrict {N} [monoid N] (f : M →* N) : M →* f.mrange :=
f.cod_mrestrict f.mrange $ λ x, ⟨x, submonoid.mem_top x, rfl⟩

@[simp, to_additive]
lemma coe_mrange_restrict {N} [monoid N] (f : M →* N) (x : M) :
  (f.mrange_restrict x : N) = f x :=
rfl

end monoid_hom

namespace free_monoid

variables {α : Type*}

open submonoid

@[to_additive]
theorem closure_range_of : closure (set.range $ @of α) = ⊤ :=
eq_top_iff.2 $ λ x hx, free_monoid.rec_on x (one_mem _) $ λ x xs hxs,
  mul_mem _ (subset_closure $ set.mem_range_self _) hxs

end free_monoid

namespace submonoid

variables {N : Type*} [monoid N]

open monoid_hom

/-- The monoid hom associated to an inclusion of submonoids. -/
@[to_additive "The `add_monoid` hom associated to an inclusion of submonoids."]
def inclusion {S T : submonoid M} (h : S ≤ T) : S →* T :=
S.subtype.cod_mrestrict _ (λ x, h x.2)

@[simp, to_additive]
lemma range_subtype (s : submonoid M) : s.subtype.mrange = s :=
ext' $ (coe_mrange _).trans $ set.range_coe_subtype s

lemma closure_singleton_eq (x : M) : closure ({x} : set M) = (powers_hom M x).mrange :=
closure_eq_of_le (set.singleton_subset_iff.2 ⟨multiplicative.of_add 1, trivial, pow_one x⟩) $
  λ x ⟨n, _, hn⟩, hn ▸ pow_mem _ (subset_closure $ set.mem_singleton _) _

/-- The submonoid generated by an element of a monoid equals the set of natural number powers of
    the element. -/
lemma mem_closure_singleton {x y : M} : y ∈ closure ({x} : set M) ↔ ∃ n:ℕ, x^n=y :=
by rw [closure_singleton_eq, mem_mrange]; refl

@[to_additive]
lemma closure_eq_mrange (s : set M) : closure s = (free_monoid.lift (coe : s → M)).mrange :=
by rw [mrange, ← free_monoid.closure_range_of, map_mclosure,
  ← set.range_comp, free_monoid.lift_comp_of, set.range_coe_subtype]

@[to_additive]
lemma exists_list_of_mem_closure {s : set M} {x : M} (hx : x ∈ closure s) :
  ∃ (l : list M) (hl : ∀ y ∈ l, y ∈ s), l.prod = x :=
begin
  rw [closure_eq_mrange, mem_mrange] at hx,
  rcases hx with ⟨l, hx⟩,
  exact ⟨list.map coe l, λ y hy, let ⟨z, hz, hy⟩ := list.mem_map.1 hy in hy ▸ z.2, hx⟩
end

end submonoid

namespace submonoid

variables {N : Type*} [comm_monoid N]

open monoid_hom

@[to_additive]
lemma sup_eq_range (s t : submonoid N) : s ⊔ t = (s.subtype.coprod t.subtype).mrange :=
by rw [mrange, ← range_inl_sup_range_inr, map_sup, map_mrange, coprod_comp_inl,
  map_mrange, coprod_comp_inr, range_subtype, range_subtype]

@[to_additive]
lemma mem_sup {s t : submonoid N} {x : N} :
  x ∈ s ⊔ t ↔ ∃ (y ∈ s) (z ∈ t), y * z = x :=
by simp only [sup_eq_range, mem_mrange, coprod_apply, prod.exists, submonoid.exists,
  coe_subtype, subtype.coe_mk]

end submonoid

namespace add_submonoid

open set

lemma smul_mem (S : add_submonoid A) {x : A} (hx : x ∈ S) :
  ∀ n : ℕ, n •ℕ x ∈ S
| 0     := S.zero_mem
| (n+1) := S.add_mem hx (smul_mem n)

lemma closure_singleton_eq (x : A) : closure ({x} : set A) = (multiples_hom A x).mrange :=
closure_eq_of_le (set.singleton_subset_iff.2 ⟨1, trivial, one_nsmul x⟩) $
  λ x ⟨n, _, hn⟩, hn ▸ smul_mem _ (subset_closure $ set.mem_singleton _) _

/-- The `add_submonoid` generated by an element of an `add_monoid` equals the set of
natural number multiples of the element. -/
lemma mem_closure_singleton {x y : A} :
  y ∈ closure ({x} : set A) ↔ ∃ n:ℕ, n •ℕ x = y :=
by rw [closure_singleton_eq, add_monoid_hom.mem_mrange]; refl

end add_submonoid


namespace mul_equiv

variables {S T : submonoid M}

/-- Makes the identity isomorphism from a proof that two submonoids of a multiplicative
    monoid are equal. -/
@[to_additive add_submonoid_congr "Makes the identity additive isomorphism from a proof two
submonoids of an additive monoid are equal."]
def submonoid_congr (h : S = T) : S ≃* T :=
{ map_mul' :=  λ _ _, rfl, ..equiv.set_congr $ submonoid.ext'_iff.1 h }

end mul_equiv
