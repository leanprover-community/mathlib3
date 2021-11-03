/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard
-/
import group_theory.submonoid.basic
import algebra.big_operators.basic
import deprecated.group

/-!
# Unbundled submonoids

This file defines unbundled multiplicative and additive submonoids `is_submonoid` and
`is_add_submonoid`. These are not the preferred way to talk about submonoids and should
not be used for any new projects. The preferred way in mathlib are the bundled
versions `submonoid G` and `add_submonoid G`.

## Main definitions

`is_add_submonoid (S : set G)` : the predicate that `S` is the underlying subset of an additive
submonoid of `G`. The bundled variant `add_subgroup G` should be used in preference to this.

`is_submonoid (S : set G)` : the predicate that `S` is the underlying subset of a submonoid
of `G`. The bundled variant `submonoid G` should be used in preference to this.

## Tags

subgroup, subgroups, is_subgroup

## Tags
submonoid, submonoids, is_submonoid
-/

open_locale big_operators

variables {M : Type*} [monoid M] {s : set M}
variables {A : Type*} [add_monoid A] {t : set A}

/-- `s` is an additive submonoid: a set containing 0 and closed under addition.
Note that this structure is deprecated, and the bundled variant `add_submonoid A` should be
preferred. -/
structure is_add_submonoid (s : set A) : Prop :=
(zero_mem : (0:A) ∈ s)
(add_mem {a b} : a ∈ s → b ∈ s → a + b ∈ s)

/-- `s` is a submonoid: a set containing 1 and closed under multiplication.
Note that this structure is deprecated, and the bundled variant `submonoid M` should be
preferred. -/
@[to_additive]
structure is_submonoid (s : set M) : Prop :=
(one_mem : (1:M) ∈ s)
(mul_mem {a b} : a ∈ s → b ∈ s → a * b ∈ s)

lemma additive.is_add_submonoid
  {s : set M} : ∀ (is : is_submonoid s), @is_add_submonoid (additive M) _ s
| ⟨h₁, h₂⟩ := ⟨h₁, @h₂⟩

theorem additive.is_add_submonoid_iff
  {s : set M} : @is_add_submonoid (additive M) _ s ↔ is_submonoid s :=
⟨λ ⟨h₁, h₂⟩, ⟨h₁, @h₂⟩, additive.is_add_submonoid⟩

lemma multiplicative.is_submonoid
  {s : set A} : ∀ (is : is_add_submonoid s), @is_submonoid (multiplicative A) _ s
| ⟨h₁, h₂⟩ := ⟨h₁, @h₂⟩

theorem multiplicative.is_submonoid_iff
  {s : set A} : @is_submonoid (multiplicative A) _ s ↔ is_add_submonoid s :=
⟨λ ⟨h₁, h₂⟩, ⟨h₁, @h₂⟩, multiplicative.is_submonoid⟩

/-- The intersection of two submonoids of a monoid `M` is a submonoid of `M`. -/
@[to_additive "The intersection of two `add_submonoid`s of an `add_monoid` `M` is
an `add_submonoid` of M."]
lemma is_submonoid.inter {s₁ s₂ : set M} (is₁ : is_submonoid s₁) (is₂ : is_submonoid s₂) :
  is_submonoid (s₁ ∩ s₂) :=
{ one_mem := ⟨is₁.one_mem, is₂.one_mem⟩,
  mul_mem := λ x y hx hy,
    ⟨is₁.mul_mem hx.1 hy.1, is₂.mul_mem hx.2 hy.2⟩ }

/-- The intersection of an indexed set of submonoids of a monoid `M` is a submonoid of `M`. -/
@[to_additive "The intersection of an indexed set of `add_submonoid`s of an `add_monoid` `M` is
an `add_submonoid` of `M`."]
lemma is_submonoid.Inter {ι : Sort*} {s : ι → set M} (h : ∀ y : ι, is_submonoid (s y)) :
  is_submonoid (set.Inter s) :=
{ one_mem := set.mem_Inter.2 $ λ y, (h y).one_mem,
  mul_mem := λ x₁ x₂ h₁ h₂, set.mem_Inter.2 $
    λ y, (h y).mul_mem (set.mem_Inter.1 h₁ y) (set.mem_Inter.1 h₂ y) }

/-- The union of an indexed, directed, nonempty set of submonoids of a monoid `M` is a submonoid
    of `M`. -/
@[to_additive "The union of an indexed, directed, nonempty set
of `add_submonoid`s of an `add_monoid` `M` is an `add_submonoid` of `M`. "]
lemma is_submonoid_Union_of_directed {ι : Type*} [hι : nonempty ι]
  {s : ι → set M} (hs : ∀ i, is_submonoid (s i))
  (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
  is_submonoid (⋃i, s i) :=
{ one_mem := let ⟨i⟩ := hι in set.mem_Union.2 ⟨i, (hs i).one_mem⟩,
  mul_mem := λ a b ha hb,
    let ⟨i, hi⟩ := set.mem_Union.1 ha in
    let ⟨j, hj⟩ := set.mem_Union.1 hb in
    let ⟨k, hk⟩ := directed i j in
    set.mem_Union.2 ⟨k, (hs k).mul_mem (hk.1 hi) (hk.2 hj)⟩ }

section powers

/-- The set of natural number powers `1, x, x², ...` of an element `x` of a monoid. -/
@[to_additive multiples
"The set of natural number multiples `0, x, 2x, ...` of an element `x` of an `add_monoid`."]
def powers (x : M) : set M := {y | ∃ n:ℕ, x^n = y}

/-- 1 is in the set of natural number powers of an element of a monoid. -/
@[to_additive "0 is in the set of natural number multiples of an element of an `add_monoid`."]
lemma powers.one_mem {x : M} : (1 : M) ∈ powers x := ⟨0, pow_zero _⟩

/-- An element of a monoid is in the set of that element's natural number powers. -/
@[to_additive
"An element of an `add_monoid` is in the set of that element's natural number multiples."]
lemma powers.self_mem {x : M} : x ∈ powers x := ⟨1, pow_one _⟩

/-- The set of natural number powers of an element of a monoid is closed under multiplication. -/
@[to_additive
"The set of natural number multiples of an element of an `add_monoid` is closed under addition."]
lemma powers.mul_mem {x y z : M} : (y ∈ powers x) → (z ∈ powers x) → (y * z ∈ powers x) :=
λ ⟨n₁, h₁⟩ ⟨n₂, h₂⟩, ⟨n₁ + n₂, by simp only [pow_add, *]⟩

/-- The set of natural number powers of an element of a monoid `M` is a submonoid of `M`. -/
@[to_additive "The set of natural number multiples of an element of
an `add_monoid` `M` is an `add_submonoid` of `M`."]
lemma powers.is_submonoid (x : M) : is_submonoid (powers x) :=
{ one_mem := powers.one_mem,
  mul_mem := λ y z, powers.mul_mem }

/-- A monoid is a submonoid of itself. -/
@[to_additive "An `add_monoid` is an `add_submonoid` of itself."]
lemma univ.is_submonoid : is_submonoid (@set.univ M) := by split; simp

/-- The preimage of a submonoid under a monoid hom is a submonoid of the domain. -/
@[to_additive "The preimage of an `add_submonoid` under an `add_monoid` hom is
an `add_submonoid` of the domain."]
lemma is_submonoid.preimage {N : Type*} [monoid N] {f : M → N} (hf : is_monoid_hom f)
  {s : set N} (hs : is_submonoid s) : is_submonoid (f ⁻¹' s) :=
{ one_mem := show f 1 ∈ s, by rw is_monoid_hom.map_one hf; exact hs.one_mem,
  mul_mem := λ a b (ha : f a ∈ s) (hb : f b ∈ s),
    show f (a * b) ∈ s, by rw is_monoid_hom.map_mul hf; exact hs.mul_mem ha hb }

/-- The image of a submonoid under a monoid hom is a submonoid of the codomain. -/
@[to_additive "The image of an `add_submonoid` under an `add_monoid`
hom is an `add_submonoid` of the codomain."]
lemma is_submonoid.image {γ : Type*} [monoid γ] {f : M → γ} (hf : is_monoid_hom f)
  {s : set M} (hs : is_submonoid s) : is_submonoid (f '' s) :=
{ one_mem := ⟨1, hs.one_mem, hf.map_one⟩,
  mul_mem := λ a b ⟨x, hx⟩ ⟨y, hy⟩, ⟨x * y, hs.mul_mem hx.1 hy.1,
    by rw [hf.map_mul, hx.2, hy.2]⟩ }

/-- The image of a monoid hom is a submonoid of the codomain. -/
@[to_additive "The image of an `add_monoid` hom is an `add_submonoid`
of the codomain."]
lemma range.is_submonoid {γ : Type*} [monoid γ] {f : M → γ} (hf : is_monoid_hom f) :
  is_submonoid (set.range f) :=
by { rw ← set.image_univ, exact univ.is_submonoid.image hf }

/-- Submonoids are closed under natural powers. -/
@[to_additive is_add_submonoid.smul_mem
"An `add_submonoid` is closed under multiplication by naturals."]
lemma is_submonoid.pow_mem {a : M} (hs : is_submonoid s) (h : a ∈ s) : ∀ {n : ℕ}, a ^ n ∈ s
| 0 := by { rw pow_zero, exact hs.one_mem }
| (n + 1) := by { rw pow_succ, exact hs.mul_mem h is_submonoid.pow_mem }

/-- The set of natural number powers of an element of a submonoid is a subset of the submonoid. -/
@[to_additive is_add_submonoid.multiples_subset "The set of natural number multiples of an element
of an `add_submonoid` is a subset of the `add_submonoid`."]
lemma is_submonoid.power_subset {a : M} (hs : is_submonoid s) (h : a ∈ s) : powers a ⊆ s :=
assume x ⟨n, hx⟩, hx ▸ hs.pow_mem h

end powers

namespace is_submonoid

/-- The product of a list of elements of a submonoid is an element of the submonoid. -/
@[to_additive "The sum of a list of elements of an `add_submonoid` is an element of the
`add_submonoid`."]
lemma list_prod_mem (hs : is_submonoid s) : ∀{l : list M}, (∀x∈l, x ∈ s) → l.prod ∈ s
| []     h := hs.one_mem
| (a::l) h :=
  suffices a * l.prod ∈ s, by simpa,
  have a ∈ s ∧ (∀x∈l, x ∈ s), by simpa using h,
  hs.mul_mem this.1 (list_prod_mem this.2)

/-- The product of a multiset of elements of a submonoid of a `comm_monoid` is an element of
the submonoid. -/
@[to_additive "The sum of a multiset of elements of an `add_submonoid` of an `add_comm_monoid`
is an element of the `add_submonoid`. "]
lemma multiset_prod_mem {M} [comm_monoid M] {s : set M} (hs : is_submonoid s) (m : multiset M) :
  (∀a∈m, a ∈ s) → m.prod ∈ s :=
begin
  refine quotient.induction_on m (assume l hl, _),
  rw [multiset.quot_mk_to_coe, multiset.coe_prod],
  exact list_prod_mem hs hl
end

/-- The product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is an element
of the submonoid. -/
@[to_additive "The sum of elements of an `add_submonoid` of an `add_comm_monoid` indexed by
a `finset` is an element of the `add_submonoid`."]
lemma finset_prod_mem {M A} [comm_monoid M] {s : set M} (hs : is_submonoid s) (f : A → M) :
  ∀(t : finset A), (∀b∈t, f b ∈ s) → ∏ b in t, f b ∈ s
| ⟨m, hm⟩ _ := multiset_prod_mem hs _ (by simpa)

end is_submonoid

namespace add_monoid

/-- The inductively defined membership predicate for the submonoid generated by a subset of a
    monoid. -/
inductive in_closure (s : set A) : A → Prop
| basic {a : A} : a ∈ s → in_closure a
| zero : in_closure 0
| add {a b : A} : in_closure a → in_closure b → in_closure (a + b)

end add_monoid

namespace monoid

/-- The inductively defined membership predicate for the `submonoid` generated by a subset of an
    monoid. -/
@[to_additive]
inductive in_closure (s : set M) : M → Prop
| basic {a : M} : a ∈ s → in_closure a
| one : in_closure 1
| mul {a b : M} : in_closure a → in_closure b → in_closure (a * b)

/-- The inductively defined submonoid generated by a subset of a monoid. -/
@[to_additive "The inductively defined `add_submonoid` genrated by a subset of an `add_monoid`."]
def closure (s : set M) : set M := {a | in_closure s a }

@[to_additive]
lemma closure.is_submonoid (s : set M) : is_submonoid (closure s) :=
{ one_mem := in_closure.one, mul_mem := assume a b, in_closure.mul }

/-- A subset of a monoid is contained in the submonoid it generates. -/
@[to_additive "A subset of an `add_monoid` is contained in the `add_submonoid` it generates."]
theorem subset_closure {s : set M} : s ⊆ closure s :=
assume a, in_closure.basic

/-- The submonoid generated by a set is contained in any submonoid that contains the set. -/
@[to_additive "The `add_submonoid` generated by a set is contained in any `add_submonoid` that
contains the set."]
theorem closure_subset {s t : set M} (ht : is_submonoid t) (h : s ⊆ t) : closure s ⊆ t :=
assume a ha, by induction ha; simp [h _, *, is_submonoid.one_mem, is_submonoid.mul_mem]

/-- Given subsets `t` and `s` of a monoid `M`, if `s ⊆ t`, the submonoid of `M` generated by `s` is
    contained in the submonoid generated by `t`. -/
@[to_additive "Given subsets `t` and `s` of an `add_monoid M`, if `s ⊆ t`, the `add_submonoid`
of `M` generated by `s` is contained in the `add_submonoid` generated by `t`."]
theorem closure_mono {s t : set M} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_subset (closure.is_submonoid t) $ set.subset.trans h subset_closure

/-- The submonoid generated by an element of a monoid equals the set of natural number powers of
    the element. -/
@[to_additive "The `add_submonoid` generated by an element of an `add_monoid` equals the set of
natural number multiples of the element."]
theorem closure_singleton {x : M} : closure ({x} : set M) = powers x :=
set.eq_of_subset_of_subset (closure_subset (powers.is_submonoid x) $ set.singleton_subset_iff.2 $
  powers.self_mem) $ is_submonoid.power_subset (closure.is_submonoid _) $
  set.singleton_subset_iff.1 $ subset_closure

/-- The image under a monoid hom of the submonoid generated by a set equals the submonoid generated
    by the image of the set under the monoid hom. -/
@[to_additive "The image under an `add_monoid` hom of the `add_submonoid` generated by a set equals
the `add_submonoid` generated by the image of the set under the `add_monoid` hom."]
lemma image_closure {A : Type*} [monoid A] {f : M → A} (hf : is_monoid_hom f) (s : set M) :
  f '' closure s = closure (f '' s) :=
le_antisymm
  begin
    rintros _ ⟨x, hx, rfl⟩,
    apply in_closure.rec_on hx; intros,
    { solve_by_elim [subset_closure, set.mem_image_of_mem] },
    { rw [hf.map_one], apply is_submonoid.one_mem (closure.is_submonoid (f '' s))},
    { rw [hf.map_mul], solve_by_elim [(closure.is_submonoid _).mul_mem] }
  end
  (closure_subset (is_submonoid.image hf (closure.is_submonoid _)) $
    set.image_subset _ subset_closure)

/-- Given an element `a` of the submonoid of a monoid `M` generated by a set `s`, there exists
a list of elements of `s` whose product is `a`. -/
@[to_additive "Given an element `a` of the `add_submonoid` of an `add_monoid M` generated by
a set `s`, there exists a list of elements of `s` whose sum is `a`."]
theorem exists_list_of_mem_closure {s : set M} {a : M} (h : a ∈ closure s) :
  (∃l:list M, (∀x∈l, x ∈ s) ∧ l.prod = a) :=
begin
  induction h,
  case in_closure.basic : a ha { existsi ([a]), simp [ha] },
  case in_closure.one { existsi ([]), simp },
  case in_closure.mul : a b _ _ ha hb
  { rcases ha with ⟨la, ha, eqa⟩,
    rcases hb with ⟨lb, hb, eqb⟩,
    existsi (la ++ lb),
    simp [eqa.symm, eqb.symm, or_imp_distrib],
    exact assume a, ⟨ha a, hb a⟩ }
end

/-- Given sets `s, t` of a commutative monoid `M`, `x ∈ M` is in the submonoid of `M` generated by
    `s ∪ t` iff there exists an element of the submonoid generated by `s` and an element of the
    submonoid generated by `t` whose product is `x`. -/
@[to_additive "Given sets `s, t` of a commutative `add_monoid M`, `x ∈ M` is in the `add_submonoid`
of `M` generated by `s ∪ t` iff there exists an element of the `add_submonoid` generated by `s`
and an element of the `add_submonoid` generated by `t` whose sum is `x`."]
theorem mem_closure_union_iff {M : Type*} [comm_monoid M] {s t : set M} {x : M} :
  x ∈ closure (s ∪ t) ↔ ∃ y ∈ closure s, ∃ z ∈ closure t, y * z = x :=
⟨λ hx, let ⟨L, HL1, HL2⟩ := exists_list_of_mem_closure hx in HL2 ▸
  list.rec_on L (λ _, ⟨1, (closure.is_submonoid _).one_mem, 1,
    (closure.is_submonoid _).one_mem, mul_one _⟩)
    (λ hd tl ih HL1, let ⟨y, hy, z, hz, hyzx⟩ := ih (list.forall_mem_of_forall_mem_cons HL1) in
      or.cases_on (HL1 hd $ list.mem_cons_self _ _)
        (λ hs, ⟨hd * y, (closure.is_submonoid _).mul_mem (subset_closure hs) hy, z, hz,
          by rw [mul_assoc, list.prod_cons, ← hyzx]; refl⟩)
        (λ ht, ⟨y, hy, z * hd, (closure.is_submonoid _).mul_mem hz (subset_closure ht),
          by rw [← mul_assoc, list.prod_cons, ← hyzx, mul_comm hd]; refl⟩)) HL1,
λ ⟨y, hy, z, hz, hyzx⟩, hyzx ▸ (closure.is_submonoid _).mul_mem
  (closure_mono (set.subset_union_left _ _) hy)
  (closure_mono (set.subset_union_right _ _) hz)⟩

end monoid

/-- Create a bundled submonoid from a set `s` and `[is_submonoid s]`. -/
@[to_additive "Create a bundled additive submonoid from a set `s` and `[is_add_submonoid s]`."]
def submonoid.of {s : set M} (h : is_submonoid s) : submonoid M := ⟨s, h.1, h.2⟩

@[to_additive]
lemma submonoid.is_submonoid (S : submonoid M) : is_submonoid (S : set M) := ⟨S.2, S.3⟩
