/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import group_theory.submonoid.basic
import algebra.big_operators
import algebra.free_monoid
import algebra.group.prod
import data.equiv.mul_add

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

/-- A submonoid of a monoid inherits a multiplication. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits an addition."]
instance has_mul : has_mul S := ⟨λ a b, ⟨a.1 * b.1, S.mul_mem a.2 b.2⟩⟩

/-- A submonoid of a monoid inherits a 1. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits a zero."]
instance has_one : has_one S := ⟨⟨_, S.one_mem⟩⟩

@[simp, to_additive] lemma coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y := rfl
@[simp, to_additive] lemma coe_one : ((1 : S) : M) = 1 := rfl
attribute [norm_cast] coe_mul coe_one
attribute [norm_cast] add_submonoid.coe_add add_submonoid.coe_zero

/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive to_add_monoid "An `add_submonoid` of an `add_monoid` inherits an `add_monoid`
structure."]
instance to_monoid {M : Type*} [monoid M] (S : submonoid M) : monoid S :=
by refine { mul := (*), one := 1, .. }; simp [mul_assoc, ← submonoid.coe_eq_coe]

/-- A submonoid of a `comm_monoid` is a `comm_monoid`. -/
@[to_additive to_add_comm_monoid "An `add_submonoid` of an `add_comm_monoid` is
an `add_comm_monoid`."]
instance to_comm_monoid {M} [comm_monoid M] (S : submonoid M) : comm_monoid S :=
{ mul_comm := λ _ _, subtype.eq $ mul_comm _ _, ..S.to_monoid}

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive "The natural monoid hom from an `add_submonoid` of `add_monoid` `M` to `M`."]
def subtype : S →* M := ⟨coe, rfl, λ _ _, rfl⟩

@[simp, to_additive] theorem coe_subtype : ⇑S.subtype = coe := rfl

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

/-- Given `submonoid`s `s`, `t` of monoids `M`, `N` respectively, `s × t` as a submonoid
of `M × N`. -/
@[to_additive prod "Given `add_submonoid`s `s`, `t` of `add_monoid`s `A`, `B` respectively, `s × t`
as an `add_submonoid` of `A × B`."]
def prod (s : submonoid M) (t : submonoid N) : submonoid (M × N) :=
{ carrier := (s : set M).prod t,
  one_mem' := ⟨s.one_mem, t.one_mem⟩,
  mul_mem' := λ p q hp hq, ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩ }

@[to_additive coe_prod]
lemma coe_prod (s : submonoid M) (t : submonoid N) :
 (s.prod t : set (M × N)) = (s : set M).prod (t : set N) :=
rfl

@[to_additive mem_prod]
lemma mem_prod {s : submonoid M} {t : submonoid N} {p : M × N} :
  p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t := iff.rfl

@[to_additive prod_mono]
lemma prod_mono : ((≤) ⇒ (≤) ⇒ (≤)) (@prod M _ N _) (@prod M _ N _) :=
λ s s' hs t t' ht, set.prod_mono hs ht

@[to_additive prod_mono_right]
lemma prod_mono_right (s : submonoid M) : monotone (λ t : submonoid N, s.prod t) :=
prod_mono (le_refl s)

@[to_additive prod_mono_left]
lemma prod_mono_left (t : submonoid N) : monotone (λ s : submonoid M, s.prod t) :=
λ s₁ s₂ hs, prod_mono hs (le_refl t)

@[to_additive prod_top]
lemma prod_top (s : submonoid M) :
  s.prod (⊤ : submonoid N) = s.comap (monoid_hom.fst M N) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_fst]

@[to_additive top_prod]
lemma top_prod (s : submonoid N) :
  (⊤ : submonoid M).prod s = s.comap (monoid_hom.snd M N) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_snd]

@[simp, to_additive top_prod_top]
lemma top_prod_top : (⊤ : submonoid M).prod (⊤ : submonoid N) = ⊤ :=
(top_prod _).trans $ comap_top _

@[to_additive] lemma bot_prod_bot : (⊥ : submonoid M).prod (⊥ : submonoid N) = ⊥ :=
ext' $ by simp [coe_prod, prod.one_eq_mk]

/-- Product of submonoids is isomorphic to their product as monoids. -/
@[to_additive prod_equiv "Product of additive submonoids is isomorphic to their product
as additive monoids"]
def prod_equiv (s : submonoid M) (t : submonoid N) : s.prod t ≃* s × t :=
{ map_mul' := λ x y, rfl, .. equiv.set.prod ↑s ↑t }

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

/-- Restriction of a monoid hom to its range iterpreted as a submonoid. -/
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

@[to_additive]
lemma map_inl (s : submonoid M) : s.map (inl M N) = s.prod ⊥ :=
ext $ λ p, ⟨λ ⟨x, hx, hp⟩, hp ▸ ⟨hx, set.mem_singleton 1⟩,
  λ ⟨hps, hp1⟩, ⟨p.1, hps, prod.ext rfl $ (set.eq_of_mem_singleton hp1).symm⟩⟩

@[to_additive]
lemma map_inr (s : submonoid N) : s.map (inr M N) = prod ⊥ s :=
ext $ λ p, ⟨λ ⟨x, hx, hp⟩, hp ▸ ⟨set.mem_singleton 1, hx⟩,
  λ ⟨hp1, hps⟩, ⟨p.2, hps, prod.ext (set.eq_of_mem_singleton hp1).symm rfl⟩⟩

@[to_additive]
lemma range_inl : (inl M N).mrange = prod ⊤ ⊥ := map_inl ⊤

@[to_additive]
lemma range_inr : (inr M N).mrange = prod ⊥ ⊤ := map_inr ⊤

@[to_additive]
lemma range_inl' : (inl M N).mrange = comap (snd M N) ⊥ := range_inl.trans (top_prod _)

@[to_additive]
lemma range_inr' : (inr M N).mrange = comap (fst M N) ⊥ := range_inr.trans (prod_top _)

@[simp, to_additive]
lemma range_fst : (fst M N).mrange = ⊤ :=
(fst M N).mrange_top_of_surjective $ @prod.fst_surjective _ _ ⟨1⟩

@[simp, to_additive]
lemma range_snd : (snd M N).mrange = ⊤ :=
(snd M N).mrange_top_of_surjective $ @prod.snd_surjective _ _ ⟨1⟩

@[simp, to_additive prod_bot_sup_bot_prod]
lemma prod_bot_sup_bot_prod (s : submonoid M) (t : submonoid N) :
  (s.prod ⊥) ⊔ (prod ⊥ t) = s.prod t :=
le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) $
assume p hp, prod.fst_mul_snd p ▸ mul_mem _
  ((le_sup_left : s.prod ⊥ ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, set.mem_singleton 1⟩)
  ((le_sup_right : prod ⊥ t ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨set.mem_singleton 1, hp.2⟩)

@[simp, to_additive]
lemma range_inl_sup_range_inr : (inl M N).mrange ⊔ (inr M N).mrange = ⊤ :=
by simp only [range_inl, range_inr, prod_bot_sup_bot_prod, top_prod_top]

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

/-- Makes the identity isomorphism from a proof two submonoids of a multiplicative
    monoid are equal. -/
@[to_additive add_submonoid_congr "Makes the identity additive isomorphism from a proof two
submonoids of an additive monoid are equal."]
def submonoid_congr (h : S = T) : S ≃* T :=
{ map_mul' :=  λ _ _, rfl, ..equiv.set_congr $ submonoid.ext'_iff.1 h }

end mul_equiv
