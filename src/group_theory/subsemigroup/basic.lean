/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky
-/
import algebra.hom.group  -- Only needed for notation
import data.set.lattice
import data.set_like.basic

/-!
# Subsemigroups: definition and `complete_lattice` structure

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines bundled multiplicative and additive subsemigroups. We also define
a `complete_lattice` structure on `subsemigroup`s,
and define the closure of a set as the minimal subsemigroup that includes this set.

## Main definitions

* `subsemigroup M`: the type of bundled subsemigroup of a magma `M`; the underlying set is given in
  the `carrier` field of the structure, and should be accessed through coercion as in `(S : set M)`.
* `add_subsemigroup M` : the type of bundled subsemigroups of an additive magma `M`.

For each of the following definitions in the `subsemigroup` namespace, there is a corresponding
definition in the `add_subsemigroup` namespace.

* `subsemigroup.copy` : copy of a subsemigroup with `carrier` replaced by a set that is equal but
  possibly not definitionally equal to the carrier of the original `subsemigroup`.
* `subsemigroup.closure` :  semigroup closure of a set, i.e.,
  the least subsemigroup that includes the set.
* `subsemigroup.gi` : `closure : set M → subsemigroup M` and coercion `coe : subsemigroup M → set M`
  form a `galois_insertion`;

## Implementation notes

Subsemigroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subsemigroup's underlying set.

Note that `subsemigroup M` does not actually require `semigroup M`,
instead requiring only the weaker `has_mul M`.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers.

## Tags
subsemigroup, subsemigroups
-/

variables {M : Type*} {N : Type*}
variables {A : Type*}

section non_assoc
variables [has_mul M] {s : set M}
variables [has_add A] {t : set A}

/-- `mul_mem_class S M` says `S` is a type of subsets `s ≤ M` that are closed under `(*)` -/
class mul_mem_class (S M : Type*) [has_mul M] [set_like S M] : Prop :=
(mul_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a * b ∈ s)

export mul_mem_class (mul_mem)

/-- `add_mem_class S M` says `S` is a type of subsets `s ≤ M` that are closed under `(+)` -/
class add_mem_class (S M : Type*) [has_add M] [set_like S M] : Prop :=
(add_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a + b ∈ s)

export add_mem_class (add_mem)

attribute [to_additive] mul_mem_class

/-- A subsemigroup of a magma `M` is a subset closed under multiplication. -/
structure subsemigroup (M : Type*) [has_mul M] :=
(carrier : set M)
(mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier)

/-- An additive subsemigroup of an additive magma `M` is a subset closed under addition. -/
structure add_subsemigroup (M : Type*) [has_add M] :=
(carrier : set M)
(add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier)

attribute [to_additive add_subsemigroup] subsemigroup

namespace subsemigroup

@[to_additive]
instance : set_like (subsemigroup M) M :=
⟨subsemigroup.carrier, λ p q h, by cases p; cases q; congr'⟩

@[to_additive]
instance : mul_mem_class (subsemigroup M) M :=
{ mul_mem := subsemigroup.mul_mem' }

/-- See Note [custom simps projection] -/
@[to_additive " See Note [custom simps projection]"]
def simps.coe (S : subsemigroup M) : set M := S

initialize_simps_projections subsemigroup (carrier → coe)
initialize_simps_projections add_subsemigroup (carrier → coe)

@[simp, to_additive]
lemma mem_carrier {s : subsemigroup M} {x : M} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

@[simp, to_additive]
lemma mem_mk {s : set M} {x : M} (h_mul) : x ∈ mk s h_mul ↔ x ∈ s := iff.rfl

@[simp, to_additive]
lemma coe_set_mk {s : set M} (h_mul) : (mk s h_mul : set M) = s := rfl

@[simp, to_additive]
lemma mk_le_mk {s t : set M} (h_mul) (h_mul') :
  mk s h_mul ≤ mk t h_mul' ↔ s ⊆ t := iff.rfl

/-- Two subsemigroups are equal if they have the same elements. -/
@[ext, to_additive "Two `add_subsemigroup`s are equal if they have the same elements."]
theorem ext {S T : subsemigroup M}
  (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

/-- Copy a subsemigroup replacing `carrier` with a set that is equal to it. -/
@[to_additive "Copy an additive subsemigroup replacing `carrier` with a set that is equal to
it."]
protected def copy (S : subsemigroup M) (s : set M) (hs : s = S) : subsemigroup M :=
{ carrier := s,
  mul_mem' := λ _ _, hs.symm ▸ S.mul_mem' }

variable {S : subsemigroup M}

@[simp, to_additive] lemma coe_copy {s : set M} (hs : s = S) :
  (S.copy s hs : set M) = s := rfl

@[to_additive] lemma copy_eq {s : set M} (hs : s = S) : S.copy s hs = S :=
set_like.coe_injective hs

variable (S)

/-- A subsemigroup is closed under multiplication. -/
@[to_additive "An `add_subsemigroup` is closed under addition."]
protected theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S := subsemigroup.mul_mem' S

/-- The subsemigroup `M` of the magma `M`. -/
@[to_additive "The additive subsemigroup `M` of the magma `M`."]
instance : has_top (subsemigroup M) :=
⟨{ carrier := set.univ,
   mul_mem' := λ _ _ _ _, set.mem_univ _ }⟩

/-- The trivial subsemigroup `∅` of a magma `M`. -/
@[to_additive "The trivial `add_subsemigroup` `∅` of an additive magma `M`."]
instance : has_bot (subsemigroup M) :=
⟨{ carrier := ∅,
   mul_mem' := λ a b, by simp }⟩

@[to_additive]
instance : inhabited (subsemigroup M) := ⟨⊥⟩

@[to_additive] lemma not_mem_bot {x : M} : x ∉ (⊥ : subsemigroup M) := set.not_mem_empty x

@[simp, to_additive] lemma mem_top (x : M) : x ∈ (⊤ : subsemigroup M) := set.mem_univ x

@[simp, to_additive] lemma coe_top : ((⊤ : subsemigroup M) : set M) = set.univ := rfl

@[simp, to_additive] lemma coe_bot : ((⊥ : subsemigroup M) : set M) = ∅ := rfl

/-- The inf of two subsemigroups is their intersection. -/
@[to_additive "The inf of two `add_subsemigroup`s is their intersection."]
instance : has_inf (subsemigroup M) :=
⟨λ S₁ S₂,
  { carrier := S₁ ∩ S₂,
    mul_mem' := λ _ _ ⟨hx, hx'⟩ ⟨hy, hy'⟩,
      ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[simp, to_additive]
lemma coe_inf (p p' : subsemigroup M) : ((p ⊓ p' : subsemigroup M) : set M) = p ∩ p' := rfl

@[simp, to_additive]
lemma mem_inf {p p' : subsemigroup M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

@[to_additive]
instance : has_Inf (subsemigroup M) :=
⟨λ s,
{ carrier := ⋂ t ∈ s, ↑t,
  mul_mem' := λ x y hx hy, set.mem_bInter $ λ i h,
    i.mul_mem (by apply set.mem_Inter₂.1 hx i h) (by apply set.mem_Inter₂.1 hy i h) }⟩

@[simp, norm_cast, to_additive]
lemma coe_Inf (S : set (subsemigroup M)) : ((Inf S : subsemigroup M) : set M) = ⋂ s ∈ S, ↑s := rfl

@[to_additive]
lemma mem_Inf {S : set (subsemigroup M)} {x : M} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p := set.mem_Inter₂

@[to_additive]
lemma mem_infi {ι : Sort*} {S : ι → subsemigroup M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i :=
by simp only [infi, mem_Inf, set.forall_range_iff]

@[simp, norm_cast, to_additive]
lemma coe_infi {ι : Sort*} {S : ι → subsemigroup M} : (↑(⨅ i, S i) : set M) = ⋂ i, S i :=
by simp only [infi, coe_Inf, set.bInter_range]

/-- subsemigroups of a monoid form a complete lattice. -/
@[to_additive "The `add_subsemigroup`s of an `add_monoid` form a complete lattice."]
instance : complete_lattice (subsemigroup M) :=
{ le           := (≤),
  lt           := (<),
  bot          := (⊥),
  bot_le       := λ S x hx, (not_mem_bot hx).elim,
  top          := (⊤),
  le_top       := λ S x hx, mem_top x,
  inf          := (⊓),
  Inf          := has_Inf.Inf,
  le_inf       := λ a b c ha hb x hx, ⟨ha hx, hb hx⟩,
  inf_le_left  := λ a b x, and.left,
  inf_le_right := λ a b x, and.right,
  .. complete_lattice_of_Inf (subsemigroup M) $ λ s,
    is_glb.of_image (λ S T,
      show (S : set M) ≤ T ↔ S ≤ T, from set_like.coe_subset_coe) is_glb_binfi }

@[simp, to_additive]
lemma subsingleton_of_subsingleton [subsingleton (subsemigroup M)] : subsingleton M :=
begin
  constructor; intros x y,
  have : ∀ a : M, a ∈ (⊥ : subsemigroup M),
  { simp [subsingleton.elim (⊥ : subsemigroup M) ⊤] },
  exact absurd (this x) not_mem_bot
end

@[to_additive]
instance [hn : nonempty M] : nontrivial (subsemigroup M) :=
⟨⟨⊥, ⊤, λ h, by { obtain ⟨x⟩ := id hn, refine absurd (_ : x ∈ ⊥) not_mem_bot, simp [h] }⟩⟩

/-- The `subsemigroup` generated by a set. -/
@[to_additive "The `add_subsemigroup` generated by a set"]
def closure (s : set M) : subsemigroup M := Inf {S | s ⊆ S}

@[to_additive]
lemma mem_closure {x : M} : x ∈ closure s ↔ ∀ S : subsemigroup M, s ⊆ S → x ∈ S :=
mem_Inf

/-- The subsemigroup generated by a set includes the set. -/
@[simp, to_additive "The `add_subsemigroup` generated by a set includes the set."]
lemma subset_closure : s ⊆ closure s := λ x hx, mem_closure.2 $ λ S hS, hS hx

@[to_additive]
lemma not_mem_of_not_mem_closure {P : M} (hP : P ∉ closure s) : P ∉ s := λ h, hP (subset_closure h)

variable {S}
open set

/-- A subsemigroup `S` includes `closure s` if and only if it includes `s`. -/
@[simp, to_additive "An additive subsemigroup `S` includes `closure s`
if and only if it includes `s`"]
lemma closure_le : closure s ≤ S ↔ s ⊆ S :=
⟨subset.trans subset_closure, λ h, Inf_le h⟩

/-- subsemigroup closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[to_additive "Additive subsemigroup closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`"]
lemma closure_mono ⦃s t : set M⦄ (h : s ⊆ t) : closure s ≤ closure t :=
closure_le.2 $ subset.trans h subset_closure

@[to_additive]
lemma closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure s) : closure s = S :=
le_antisymm (closure_le.2 h₁) h₂

variable (S)

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_eliminator, to_additive "An induction principle for additive closure membership. If `p`
holds for all elements of `s`, and is preserved under addition, then `p` holds for all
elements of the additive closure of `s`."]
lemma closure_induction {p : M → Prop} {x} (h : x ∈ closure s)
  (Hs : ∀ x ∈ s, p x)
  (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
(@closure_le _ _ _ ⟨p, Hmul⟩).2 Hs h

/-- A dependent version of `subsemigroup.closure_induction`.  -/
@[elab_as_eliminator, to_additive "A dependent version of `add_subsemigroup.closure_induction`. "]
lemma closure_induction' (s : set M) {p : Π x, x ∈ closure s → Prop}
  (Hs : ∀ x (h : x ∈ s), p x (subset_closure h))
  (Hmul : ∀ x hx y hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
  {x} (hx : x ∈ closure s) :
  p x hx :=
begin
  refine exists.elim _ (λ (hx : x ∈ closure s) (hc : p x hx), hc),
  exact closure_induction hx
    (λ x hx, ⟨_, Hs x hx⟩) (λ x y ⟨hx', hx⟩ ⟨hy', hy⟩, ⟨_, Hmul _ _ _ _ hx hy⟩),
end

/-- An induction principle for closure membership for predicates with two arguments.  -/
@[elab_as_eliminator, to_additive "An induction principle for additive closure membership for
predicates with two arguments."]
lemma closure_induction₂ {p : M → M → Prop} {x} {y : M} (hx : x ∈ closure s) (hy : y ∈ closure s)
  (Hs : ∀ (x ∈ s) (y ∈ s), p x y)
  (Hmul_left : ∀ x y z, p x z → p y z → p (x * y) z)
  (Hmul_right : ∀ x y z, p z x → p z y → p z (x * y)) : p x y :=
closure_induction hx
  (λ x xs, closure_induction hy (Hs x xs) (λ z y h₁ h₂, Hmul_right z _ _ h₁ h₂))
  (λ x z h₁ h₂, Hmul_left _ _ _ h₁ h₂)

/-- If `s` is a dense set in a magma `M`, `subsemigroup.closure s = ⊤`, then in order to prove that
some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`,
and verify that `p x` and `p y` imply `p (x * y)`. -/
@[elab_as_eliminator, to_additive "If `s` is a dense set in an additive monoid `M`,
`add_subsemigroup.closure s = ⊤`, then in order to prove that some predicate `p` holds
for all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify that `p x` and `p y` imply
`p (x + y)`."]
lemma dense_induction {p : M → Prop} (x : M) {s : set M} (hs : closure s = ⊤)
  (Hs : ∀ x ∈ s, p x)
  (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
have ∀ x ∈ closure s, p x, from λ x hx, closure_induction hx Hs Hmul,
by simpa [hs] using this x

variable (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
@[to_additive "`closure` forms a Galois insertion with the coercion to set."]
protected def gi : galois_insertion (@closure M _) coe :=
{ choice := λ s _, closure s,
  gc := λ s t, closure_le,
  le_l_u := λ s, subset_closure,
  choice_eq := λ s h, rfl }

variable {M}

/-- Closure of a subsemigroup `S` equals `S`. -/
@[simp, to_additive "Additive closure of an additive subsemigroup `S` equals `S`"]
lemma closure_eq : closure (S : set M) = S := (subsemigroup.gi M).l_u_eq S

@[simp, to_additive] lemma closure_empty : closure (∅ : set M) = ⊥ :=
(subsemigroup.gi M).gc.l_bot

@[simp, to_additive] lemma closure_univ : closure (univ : set M) = ⊤ :=
@coe_top M _ ▸ closure_eq ⊤

@[to_additive]
lemma closure_union (s t : set M) : closure (s ∪ t) = closure s ⊔ closure t :=
(subsemigroup.gi M).gc.l_sup

@[to_additive]
lemma closure_Union {ι} (s : ι → set M) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
(subsemigroup.gi M).gc.l_supr

@[simp, to_additive]
lemma closure_singleton_le_iff_mem (m : M) (p : subsemigroup M) :
  closure {m} ≤ p ↔ m ∈ p :=
by rw [closure_le, singleton_subset_iff, set_like.mem_coe]

@[to_additive]
lemma mem_supr {ι : Sort*} (p : ι → subsemigroup M) {m : M} :
  (m ∈ ⨆ i, p i) ↔ (∀ N, (∀ i, p i ≤ N) → m ∈ N) :=
begin
  rw [← closure_singleton_le_iff_mem, le_supr_iff],
  simp only [closure_singleton_le_iff_mem],
end

@[to_additive]
lemma supr_eq_closure {ι : Sort*} (p : ι → subsemigroup M) :
  (⨆ i, p i) = subsemigroup.closure (⋃ i, (p i : set M)) :=
by simp_rw [subsemigroup.closure_Union, subsemigroup.closure_eq]

end subsemigroup

namespace mul_hom

variables [has_mul N]

open subsemigroup

/-- The subsemigroup of elements `x : M` such that `f x = g x` -/
@[to_additive "The additive subsemigroup of elements `x : M` such that `f x = g x`"]
def eq_mlocus (f g : M →ₙ* N) : subsemigroup M :=
{ carrier := {x | f x = g x},
  mul_mem' := λ x y (hx : _ = _) (hy : _ = _), by simp [*] }

/-- If two mul homomorphisms are equal on a set, then they are equal on its subsemigroup closure. -/
@[to_additive "If two add homomorphisms are equal on a set,
then they are equal on its additive subsemigroup closure."]
lemma eq_on_mclosure {f g : M →ₙ* N} {s : set M} (h : set.eq_on f g s) :
  set.eq_on f g (closure s) :=
show closure s ≤ f.eq_mlocus g, from closure_le.2 h

@[to_additive]
lemma eq_of_eq_on_mtop {f g : M →ₙ* N} (h : set.eq_on f g (⊤ : subsemigroup M)) :
  f = g :=
ext $ λ x, h trivial

@[to_additive]
lemma eq_of_eq_on_mdense {s : set M} (hs : closure s = ⊤) {f g : M →ₙ* N} (h : s.eq_on f g) :
  f = g :=
eq_of_eq_on_mtop $ hs ▸ eq_on_mclosure h


end mul_hom

end non_assoc

section assoc

namespace mul_hom

open subsemigroup

/-- Let `s` be a subset of a semigroup `M` such that the closure of `s` is the whole semigroup.
Then `mul_hom.of_mdense` defines a mul homomorphism from `M` asking for a proof
of `f (x * y) = f x * f y` only for `y ∈ s`. -/
@[to_additive]
def of_mdense {M N} [semigroup M] [semigroup N] {s : set M} (f : M → N) (hs : closure s = ⊤)
  (hmul : ∀ x (y ∈ s), f (x * y) = f x * f y) :
  M →ₙ* N :=
{ to_fun := f,
  map_mul' := λ x y, dense_induction y hs (λ y hy x, hmul x y hy)
    (λ y₁ y₂ h₁ h₂ x, by simp only [← mul_assoc, h₁, h₂]) x }

/-- Let `s` be a subset of an additive semigroup `M` such that the closure of `s` is the whole
semigroup.  Then `add_hom.of_mdense` defines an additive homomorphism from `M` asking for a proof
of `f (x + y) = f x + f y` only for `y ∈ s`. -/
add_decl_doc add_hom.of_mdense

@[simp, norm_cast, to_additive] lemma coe_of_mdense [semigroup M] [semigroup N] {s : set M}
  (f : M → N) (hs : closure s = ⊤) (hmul) :
  (of_mdense f hs hmul : M → N) = f := rfl

end mul_hom

end assoc
