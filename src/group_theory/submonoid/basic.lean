/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import algebra.group.basic
import data.set.lattice
import data.equiv.basic

/-!
# Submonoids

This file defines bundled multiplicative and additive submonoids.

## Main definitions

* `submonoid M`: a bundled submonoid of a monoid `M`; the underlying set is given in the `carrier`
  field of the structure, and should be accessed through coercion as in `(S : set M)`.
* `add_submonoid M` : a bundled submonoid of an additive monoid `M`.
* `submonoid.to_add_submonoid`, `submonoid.of_add_submonoid`, `add_submonoid.to_submonoid`,
  `add_submonoid.of_submonoid`: convert between multiplicative and additive submonoids of `M`,
  `multiplicative M`, and `additive M`.
* `submonoid.add_submonoid_equiv`: equivalence between `submonoid M`
  and `add_submonoid (additive M)`.

For each of the following definitions in the `submonoid` namespace, there is a corresponding
definition in the `add_submonoid` namespace.

* `submonoid.copy` : copy of a submonoid with `carrier` replaced by a set that is equal but possibly
  not definitionally equal to the carrier of the original `submonoid`.
* `submonoid.closure` :  monoid closure of a set, i.e., the least submonoid that includes the set.
* `submonoid.gi` : `closure : set M → submonoid M` and coercion `coe : submonoid M → set M`
  form a `galois_insertion`;
* `submonoid.comap`: preimage of a submonoid under a monoid homomorphism as a submonoid of the
  domain;
* `submonoid.map`: image of a submonoid under a monoid homomorphism as a submonoid of the codomain;
* `monoid_hom.mrange`: range of a monoid homomorphism as a submonoid of the codomain;
* `monoid_hom.eq_mlocus`: the submonoid of elements `x : M` such that `f x = g x`;
* `monoid_hom.of_mdense`:  if a map `f : M → N` between two monoids satisfies `f 1 = 1` and
  `f (x * y) = f x * f y` for `y` from some dense set `s`, then `f` is a monoid homomorphism.
  E.g., if `f : ℕ → M` satisfies `f 0 = 0` and `f (x + 1) = f x + f 1`, then `f` is an additive
  monoid homomorphism.

## Implementation notes

Submonoid inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a submonoid's underlying set.

## Tags
submonoid, submonoids
-/

variables {M : Type*} [monoid M] {s : set M}
variables {A : Type*} [add_monoid A] {t : set A}

/-- A submonoid of a monoid `M` is a subset containing 1 and closed under multiplication. -/
structure submonoid (M : Type*) [monoid M] :=
(carrier : set M)
(one_mem' : (1 : M) ∈ carrier)
(mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier)

/-- An additive submonoid of an additive monoid `M` is a subset containing 0 and
  closed under addition. -/
structure add_submonoid (M : Type*) [add_monoid M] :=
(carrier : set M)
(zero_mem' : (0 : M) ∈ carrier)
(add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier)

attribute [to_additive add_submonoid] submonoid

/-- Map from submonoids of monoid `M` to `add_submonoid`s of `additive M`. -/
def submonoid.to_add_submonoid {M : Type*} [monoid M] (S : submonoid M) :
  add_submonoid (additive M) :=
{ carrier := S.carrier,
  zero_mem' := S.one_mem',
  add_mem' := S.mul_mem' }

/-- Map from `add_submonoid`s of `additive M` to submonoids of `M`. -/
def submonoid.of_add_submonoid {M : Type*} [monoid M] (S : add_submonoid (additive M)) :
  submonoid M :=
{ carrier := S.carrier,
  one_mem' := S.zero_mem',
  mul_mem' := S.add_mem' }

/-- Map from `add_submonoid`s of `add_monoid M` to submonoids of `multiplicative M`. -/
def add_submonoid.to_submonoid {M : Type*} [add_monoid M] (S : add_submonoid M) :
  submonoid (multiplicative M) :=
{ carrier := S.carrier,
  one_mem' := S.zero_mem',
  mul_mem' := S.add_mem' }

/-- Map from submonoids of `multiplicative M` to `add_submonoid`s of `add_monoid M`. -/
def add_submonoid.of_submonoid {M : Type*} [add_monoid M] (S : submonoid (multiplicative M)) :
  add_submonoid M :=
{ carrier := S.carrier,
  zero_mem' := S.one_mem',
  add_mem' := S.mul_mem' }

/-- Submonoids of monoid `M` are isomorphic to additive submonoids of `additive M`. -/
def submonoid.add_submonoid_equiv (M : Type*) [monoid M] :
  submonoid M ≃ add_submonoid (additive M) :=
{ to_fun := submonoid.to_add_submonoid,
  inv_fun := submonoid.of_add_submonoid,
  left_inv := λ x, by cases x; refl,
  right_inv := λ x, by cases x; refl }

namespace submonoid

@[to_additive]
instance : has_coe (submonoid M) (set M) := ⟨submonoid.carrier⟩

@[to_additive]
instance : has_coe_to_sort (submonoid M) := ⟨Type*, λ S, S.carrier⟩

@[to_additive]
instance : has_mem M (submonoid M) := ⟨λ m S, m ∈ (S:set M)⟩

@[simp, to_additive]
lemma mem_carrier {s : submonoid M} {x : M} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

@[simp, norm_cast, to_additive]
lemma mem_coe {S : submonoid M} {m : M} : m ∈ (S : set M) ↔ m ∈ S := iff.rfl

@[simp, norm_cast, to_additive]
lemma coe_coe (s : submonoid M) : ↥(s : set M) = s := rfl

attribute [norm_cast] add_submonoid.mem_coe add_submonoid.coe_coe

@[to_additive]
protected lemma «exists» {s : submonoid M} {p : s → Prop} :
  (∃ x : s, p x) ↔ ∃ x ∈ s, p ⟨x, ‹x ∈ s›⟩ :=
set_coe.exists

@[to_additive]
protected lemma «forall» {s : submonoid M} {p : s → Prop} :
  (∀ x : s, p x) ↔ ∀ x ∈ s, p ⟨x, ‹x ∈ s›⟩ :=
set_coe.forall

/-- Two submonoids are equal if the underlying subsets are equal. -/
@[to_additive "Two `add_submonoid`s are equal if the underlying subsets are equal."]
theorem ext' ⦃S T : submonoid M⦄ (h : (S : set M) = T) : S = T :=
by cases S; cases T; congr'

/-- Two submonoids are equal if and only if the underlying subsets are equal. -/
@[to_additive "Two `add_submonoid`s are equal if and only if the underlying subsets are equal."]
protected theorem ext'_iff {S T : submonoid M}  : S = T ↔ (S : set M) = T :=
⟨λ h, h ▸ rfl, λ h, ext' h⟩

/-- Two submonoids are equal if they have the same elements. -/
@[ext, to_additive "Two `add_submonoid`s are equal if they have the same elements."]
theorem ext {S T : submonoid M}
  (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := ext' $ set.ext h

attribute [ext] add_submonoid.ext

/-- Copy a submonoid replacing `carrier` with a set that is equal to it. -/
@[to_additive "Copy an additive submonoid replacing `carrier` with a set that is equal to it."]
def copy (S : submonoid M) (s : set M) (hs : s = S) : submonoid M :=
{ carrier := s,
  one_mem' := hs.symm ▸ S.one_mem',
  mul_mem' := hs.symm ▸ S.mul_mem' }

variable {S : submonoid M}

@[simp, to_additive] lemma coe_copy {s : set M} (hs : s = S) :
  (S.copy s hs : set M) = s := rfl

@[to_additive] lemma copy_eq {s : set M} (hs : s = S) : S.copy s hs = S := ext' hs

variable (S)

/-- A submonoid contains the monoid's 1. -/
@[to_additive "An `add_submonoid` contains the monoid's 0."]
theorem one_mem : (1 : M) ∈ S := S.one_mem'

/-- A submonoid is closed under multiplication. -/
@[to_additive "An `add_submonoid` is closed under addition."]
theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S := submonoid.mul_mem' S

@[simp, to_additive] lemma coe_eq_coe (x y : S) : (x : M) = y ↔ x = y := set_coe.ext_iff
attribute [norm_cast] coe_eq_coe add_submonoid.coe_eq_coe

@[to_additive]
instance : has_le (submonoid M) := ⟨λ S T, ∀ ⦃x⦄, x ∈ S → x ∈ T⟩

@[to_additive]
lemma le_def {S T : submonoid M} : S ≤ T ↔ ∀ ⦃x : M⦄, x ∈ S → x ∈ T := iff.rfl

@[simp, norm_cast, to_additive]
lemma coe_subset_coe {S T : submonoid M} : (S : set M) ⊆ T ↔ S ≤ T := iff.rfl

@[to_additive]
instance : partial_order (submonoid M) :=
{ le := λ S T, ∀ ⦃x⦄, x ∈ S → x ∈ T,
  .. partial_order.lift (coe : submonoid M → set M) ext' infer_instance }

@[simp, norm_cast, to_additive]
lemma coe_ssubset_coe {S T : submonoid M} : (S : set M) ⊂ T ↔ S < T := iff.rfl

attribute [norm_cast]  add_submonoid.coe_subset_coe add_submonoid.coe_ssubset_coe

/-- The submonoid `M` of the monoid `M`. -/
@[to_additive "The additive submonoid `M` of the `add_monoid M`."]
instance : has_top (submonoid M) :=
⟨{ carrier := set.univ,
   one_mem' := set.mem_univ 1,
   mul_mem' := λ _ _ _ _, set.mem_univ _ }⟩

/-- The trivial submonoid `{1}` of an monoid `M`. -/
@[to_additive "The trivial `add_submonoid` `{0}` of an `add_monoid` `M`."]
instance : has_bot (submonoid M) :=
⟨{ carrier := {1},
   one_mem' := set.mem_singleton 1,
   mul_mem' := λ a b ha hb, by { simp only [set.mem_singleton_iff] at *, rw [ha, hb, mul_one] }}⟩

@[to_additive]
instance : inhabited (submonoid M) := ⟨⊥⟩

@[simp, to_additive] lemma mem_bot {x : M} : x ∈ (⊥ : submonoid M) ↔ x = 1 := set.mem_singleton_iff

@[simp, to_additive] lemma mem_top (x : M) : x ∈ (⊤ : submonoid M) := set.mem_univ x

@[simp, to_additive] lemma coe_top : ((⊤ : submonoid M) : set M) = set.univ := rfl

@[simp, to_additive] lemma coe_bot : ((⊥ : submonoid M) : set M) = {1} := rfl

/-- The inf of two submonoids is their intersection. -/
@[to_additive "The inf of two `add_submonoid`s is their intersection."]
instance : has_inf (submonoid M) :=
⟨λ S₁ S₂,
  { carrier := S₁ ∩ S₂,
    one_mem' := ⟨S₁.one_mem, S₂.one_mem⟩,
    mul_mem' := λ _ _ ⟨hx, hx'⟩ ⟨hy, hy'⟩,
      ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[simp, to_additive]
lemma coe_inf (p p' : submonoid M) : ((p ⊓ p' : submonoid M) : set M) = p ∩ p' := rfl

@[simp, to_additive]
lemma mem_inf {p p' : submonoid M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

@[to_additive]
instance : has_Inf (submonoid M) :=
⟨λ s, {
  carrier := ⋂ t ∈ s, ↑t,
  one_mem' := set.mem_bInter $ λ i h, i.one_mem,
  mul_mem' := λ x y hx hy, set.mem_bInter $ λ i h,
    i.mul_mem (by apply set.mem_bInter_iff.1 hx i h) (by apply set.mem_bInter_iff.1 hy i h) }⟩

@[simp, to_additive]
lemma coe_Inf (S : set (submonoid M)) : ((Inf S : submonoid M) : set M) = ⋂ s ∈ S, ↑s := rfl

@[to_additive]
lemma mem_Inf {S : set (submonoid M)} {x : M} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p := set.mem_bInter_iff

@[to_additive]
lemma mem_infi {ι : Sort*} {S : ι → submonoid M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i :=
by simp only [infi, mem_Inf, set.forall_range_iff]

@[simp, to_additive]
lemma coe_infi {ι : Sort*} {S : ι → submonoid M} : (↑(⨅ i, S i) : set M) = ⋂ i, S i :=
by simp only [infi, coe_Inf, set.bInter_range]

attribute [norm_cast] coe_Inf coe_infi

/-- Submonoids of a monoid form a complete lattice. -/
@[to_additive "The `add_submonoid`s of an `add_monoid` form a complete lattice."]
instance : complete_lattice (submonoid M) :=
{ le           := (≤),
  lt           := (<),
  bot          := (⊥),
  bot_le       := λ S x hx, (mem_bot.1 hx).symm ▸ S.one_mem,
  top          := (⊤),
  le_top       := λ S x hx, mem_top x,
  inf          := (⊓),
  Inf          := has_Inf.Inf,
  le_inf       := λ a b c ha hb x hx, ⟨ha hx, hb hx⟩,
  inf_le_left  := λ a b x, and.left,
  inf_le_right := λ a b x, and.right,
  .. complete_lattice_of_Inf (submonoid M) $ λ s,
    is_glb.of_image (λ S T, show (S : set M) ≤ T ↔ S ≤ T, from coe_subset_coe) is_glb_binfi }

/-- The `submonoid` generated by a set. -/
@[to_additive "The `add_submonoid` generated by a set"]
def closure (s : set M) : submonoid M := Inf {S | s ⊆ S}

@[to_additive]
lemma mem_closure {x : M} : x ∈ closure s ↔ ∀ S : submonoid M, s ⊆ S → x ∈ S :=
mem_Inf

/-- The submonoid generated by a set includes the set. -/
@[simp, to_additive "The `add_submonoid` generated by a set includes the set."]
lemma subset_closure : s ⊆ closure s := λ x hx, mem_closure.2 $ λ S hS, hS hx

variable {S}
open set

/-- A submonoid `S` includes `closure s` if and only if it includes `s`. -/
@[simp, to_additive "An additive submonoid `S` includes `closure s` if and only if it includes `s`"]
lemma closure_le : closure s ≤ S ↔ s ⊆ S :=
⟨subset.trans subset_closure, λ h, Inf_le h⟩

/-- Submonoid closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[to_additive "Additive submonoid closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`"]
lemma closure_mono ⦃s t : set M⦄ (h : s ⊆ t) : closure s ≤ closure t :=
closure_le.2 $ subset.trans h subset_closure

@[to_additive]
lemma closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure s) : closure s = S :=
le_antisymm (closure_le.2 h₁) h₂

variable (S)

/-- An induction principle for closure membership. If `p` holds for `1` and all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
@[to_additive "An induction principle for additive closure membership. If `p` holds for `0` and all
elements of `s`, and is preserved under addition, then `p` holds for all elements
of the additive closure of `s`."]
lemma closure_induction {p : M → Prop} {x} (h : x ∈ closure s)
  (Hs : ∀ x ∈ s, p x) (H1 : p 1)
  (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
(@closure_le _ _ _ ⟨p, H1, Hmul⟩).2 Hs h

attribute [elab_as_eliminator] submonoid.closure_induction add_submonoid.closure_induction

@[to_additive]
lemma dense_induction {p : M → Prop} (x : M) {s : set M} (hs : closure s = ⊤)
  (Hs : ∀ x ∈ s, p x) (H1 : p 1)
  (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
have ∀ x ∈ closure s, p x, from λ x hx, closure_induction hx Hs H1 Hmul,
by simpa [hs] using this x

attribute [elab_as_eliminator] dense_induction add_submonoid.dense_induction

variable (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
@[to_additive "`closure` forms a Galois insertion with the coercion to set."]
protected def gi : galois_insertion (@closure M _) coe :=
{ choice := λ s _, closure s,
  gc := λ s t, closure_le,
  le_l_u := λ s, subset_closure,
  choice_eq := λ s h, rfl }

variable {M}

/-- Closure of a submonoid `S` equals `S`. -/
@[simp, to_additive "Additive closure of an additive submonoid `S` equals `S`"]
lemma closure_eq : closure (S : set M) = S := (submonoid.gi M).l_u_eq S

@[simp, to_additive] lemma closure_empty : closure (∅ : set M) = ⊥ :=
(submonoid.gi M).gc.l_bot

@[simp, to_additive] lemma closure_univ : closure (univ : set M) = ⊤ :=
@coe_top M _ ▸ closure_eq ⊤

@[to_additive]
lemma closure_union (s t : set M) : closure (s ∪ t) = closure s ⊔ closure t :=
(submonoid.gi M).gc.l_sup

@[to_additive]
lemma closure_Union {ι} (s : ι → set M) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
(submonoid.gi M).gc.l_supr

variables {N : Type*} [monoid N] {P : Type*} [monoid P]

/-- The preimage of a submonoid along a monoid homomorphism is a submonoid. -/
@[to_additive "The preimage of an `add_submonoid` along an `add_monoid` homomorphism is an
`add_submonoid`."]
def comap (f : M →* N) (S : submonoid N) : submonoid M :=
{ carrier := (f ⁻¹' S),
  one_mem' := show f 1 ∈ S, by rw f.map_one; exact S.one_mem,
  mul_mem' := λ a b ha hb,
    show f (a * b) ∈ S, by rw f.map_mul; exact S.mul_mem ha hb }

@[simp, to_additive]
lemma coe_comap (S : submonoid N) (f : M →* N) : (S.comap f : set M) = f ⁻¹' S := rfl

@[simp, to_additive]
lemma mem_comap {S : submonoid N} {f : M →* N} {x : M} : x ∈ S.comap f ↔ f x ∈ S := iff.rfl

@[to_additive]
lemma comap_comap (S : submonoid P) (g : N →* P) (f : M →* N) :
  (S.comap g).comap f = S.comap (g.comp f) :=
rfl

/-- The image of a submonoid along a monoid homomorphism is a submonoid. -/
@[to_additive "The image of an `add_submonoid` along an `add_monoid` homomorphism is
an `add_submonoid`."]
def map (f : M →* N) (S : submonoid M) : submonoid N :=
{ carrier := (f '' S),
  one_mem' := ⟨1, S.one_mem, f.map_one⟩,
  mul_mem' := begin rintros _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩, exact ⟨x * y, S.mul_mem hx hy,
    by rw f.map_mul; refl⟩ end }

@[simp, to_additive]
lemma coe_map (f : M →* N) (S : submonoid M) :
  (S.map f : set N) = f '' S := rfl

@[simp, to_additive]
lemma mem_map {f : M →* N} {S : submonoid M} {y : N} :
  y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
mem_image_iff_bex

@[to_additive]
lemma map_map (g : N →* P) (f : M →* N) : (S.map f).map g = S.map (g.comp f) :=
ext' $ image_image _ _ _

@[to_additive]
lemma map_le_iff_le_comap {f : M →* N} {S : submonoid M} {T : submonoid N} :
  S.map f ≤ T ↔ S ≤ T.comap f :=
image_subset_iff

@[to_additive]
lemma gc_map_comap (f : M →* N) : galois_connection (map f) (comap f) :=
λ S T, map_le_iff_le_comap

@[to_additive]
lemma map_sup (S T : submonoid M) (f : M →* N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
(gc_map_comap f).l_sup

@[to_additive]
lemma map_supr {ι : Sort*} (f : M →* N) (s : ι → submonoid M) :
  (supr s).map f = ⨆ i, (s i).map f :=
(gc_map_comap f).l_supr

@[to_additive]
lemma comap_inf (S T : submonoid N) (f : M →* N) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
(gc_map_comap f).u_inf

@[to_additive]
lemma comap_infi {ι : Sort*} (f : M →* N) (s : ι → submonoid N) :
  (infi s).comap f = ⨅ i, (s i).comap f :=
(gc_map_comap f).u_infi

@[simp, to_additive] lemma map_bot (f : M →* N) : (⊥ : submonoid M).map f = ⊥ :=
(gc_map_comap f).l_bot

@[simp, to_additive] lemma comap_top (f : M →* N) : (⊤ : submonoid N).comap f = ⊤ :=
(gc_map_comap f).u_top

@[simp, to_additive] lemma map_id (S : submonoid M) : S.map (monoid_hom.id M) = S :=
ext (λ x, ⟨λ ⟨_, h, rfl⟩, h, λ h, ⟨_, h, rfl⟩⟩)

end submonoid

namespace monoid_hom

variables {N : Type*} {P : Type*} [monoid N] [monoid P] (S : submonoid M)

open submonoid

/-- The range of a monoid homomorphism is a submonoid. -/
@[to_additive "The range of an `add_monoid_hom` is an `add_submonoid`."]
def mrange (f : M →* N) : submonoid N := (⊤ : submonoid M).map f

@[simp, to_additive] lemma coe_mrange (f : M →* N) :
  (f.mrange : set N) = set.range f :=
set.image_univ

@[simp, to_additive] lemma mem_mrange {f : M →* N} {y : N} :
  y ∈ f.mrange ↔ ∃ x, f x = y :=
by simp [mrange]

@[to_additive]
lemma map_mrange (g : N →* P) (f : M →* N) : f.mrange.map g = (g.comp f).mrange :=
(⊤ : submonoid M).map_map g f

@[to_additive]
lemma mrange_top_iff_surjective {N} [monoid N] {f : M →* N} :
  f.mrange = (⊤ : submonoid N) ↔ function.surjective f :=
submonoid.ext'_iff.trans $ iff.trans (by rw [coe_mrange, coe_top]) set.range_iff_surjective

/-- The range of a surjective monoid hom is the whole of the codomain. -/
@[to_additive "The range of a surjective `add_monoid` hom is the whole of the codomain."]
lemma mrange_top_of_surjective {N} [monoid N] (f : M →* N) (hf : function.surjective f) :
  f.mrange = (⊤ : submonoid N) :=
mrange_top_iff_surjective.2 hf

/-- The submonoid of elements `x : M` such that `f x = g x` -/
@[to_additive "The additive submonoid of elements `x : M` such that `f x = g x`"]
def eq_mlocus (f g : M →* N) : submonoid M :=
{ carrier := {x | f x = g x},
  one_mem' := by rw [set.mem_set_of_eq, f.map_one, g.map_one],
  mul_mem' := λ x y (hx : _ = _) (hy : _ = _), by simp [*] }

/-- If two monoid homomorphisms are equal on a set, then they are equal on its submonoid closure. -/
@[to_additive]
lemma eq_on_mclosure {f g : M →* N} {s : set M} (h : set.eq_on f g s) :
  set.eq_on f g (closure s) :=
show closure s ≤ f.eq_mlocus g, from closure_le.2 h

@[to_additive]
lemma eq_of_eq_on_mtop {f g : M →* N} (h : set.eq_on f g (⊤ : submonoid M)) :
  f = g :=
ext $ λ x, h trivial

@[to_additive]
lemma eq_of_eq_on_mdense {s : set M} (hs : closure s = ⊤) {f g : M →* N} (h : s.eq_on f g) :
  f = g :=
eq_of_eq_on_mtop $ hs ▸ eq_on_mclosure h

@[to_additive]
lemma mclosure_preimage_le (f : M →* N) (s : set N) :
  closure (f ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, mem_coe.2 $ mem_comap.2 $ subset_closure hx

/-- The image under a monoid hom of the submonoid generated by a set equals the submonoid generated
    by the image of the set. -/
@[to_additive "The image under an `add_monoid` hom of the `add_submonoid` generated by a set equals
the `add_submonoid` generated by the image of the set."]
lemma map_mclosure (f : M →* N) (s : set M) :
  (closure s).map f = closure (f '' s) :=
le_antisymm
  (map_le_iff_le_comap.2 $ le_trans (closure_mono $ set.subset_preimage_image _ _)
    (mclosure_preimage_le _ _))
  (closure_le.2 $ set.image_subset _ subset_closure)

/-- Let `s` be a subset of a monoid `M` such that the closure of `s` is the whole monoid.
Then `monoid_hom.of_mdense` defines a monoid homomorphism from `M` asking for a proof
of `f (x * y) = f x * f y` only for `y ∈ s`. -/
@[to_additive]
def of_mdense (f : M → N) (hs : closure s = ⊤) (h1 : f 1 = 1)
  (hmul : ∀ x (y ∈ s), f (x * y) = f x * f y) :
  M →* N :=
{ to_fun := f,
  map_one' := h1,
  map_mul' := λ x y, dense_induction y hs (λ y hy x, hmul x y hy) (by simp [h1])
    (λ y₁ y₂ h₁ h₂ x, by simp only [← mul_assoc, h₁, h₂]) x }

/-- Let `s` be a subset of an additive monoid `M` such that the closure of `s` is the whole monoid.
Then `add_monoid_hom.of_mdense` defines an additive monoid homomorphism from `M` asking for a proof
of `f (x + y) = f x + f y` only for `y ∈ s`. -/
add_decl_doc add_monoid_hom.of_mdense

@[simp, to_additive] lemma coe_of_mdense (f : M → N) (hs : closure s = ⊤) (h1 hmul) :
  ⇑(of_mdense f hs h1 hmul) = f := rfl

attribute [norm_cast] coe_of_mdense add_monoid_hom.coe_of_mdense

end monoid_hom
