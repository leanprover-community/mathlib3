/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
import data.finset.basic
import data.set.functor
import data.finite.basic

/-!
# Finite sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines predicates for finite and infinite sets and provides
`fintype` instances for many set constructions. It also proves basic facts
about finite sets and gives ways to manipulate `set.finite` expressions.

## Main definitions

* `set.finite : set α → Prop`
* `set.infinite : set α → Prop`
* `set.to_finite` to prove `set.finite` for a `set` from a `finite` instance.
* `set.finite.to_finset` to noncomputably produce a `finset` from a `set.finite` proof.
  (See `set.to_finset` for a computable version.)

## Implementation

A finite set is defined to be a set whose coercion to a type has a `fintype` instance.
Since `set.finite` is `Prop`-valued, this is the mere fact that the `fintype` instance
exists.

There are two components to finiteness constructions. The first is `fintype` instances for each
construction. This gives a way to actually compute a `finset` that represents the set, and these
may be accessed using `set.to_finset`. This gets the `finset` in the correct form, since otherwise
`finset.univ : finset s` is a `finset` for the subtype for `s`. The second component is
"constructors" for `set.finite` that give proofs that `fintype` instances exist classically given
other `set.finite` proofs. Unlike the `fintype` instances, these *do not* use any decidability
instances since they do not compute anything.

## Tags

finite sets
-/

open set function

universes u v w x
variables {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace set

/-- A set is finite if there is a `finset` with the same elements.
This is represented as there being a `fintype` instance for the set
coerced to a type.

Note: this is a custom inductive type rather than `nonempty (fintype s)`
so that it won't be frozen as a local instance. -/
@[protected] inductive finite (s : set α) : Prop
| intro : fintype s → finite

-- The `protected` attribute does not take effect within the same namespace block.
end set

namespace set

lemma finite_def {s : set α} : s.finite ↔ nonempty (fintype s) := ⟨λ ⟨h⟩, ⟨h⟩, λ ⟨h⟩, ⟨h⟩⟩

alias finite_def ↔ finite.nonempty_fintype _

lemma finite_coe_iff {s : set α} : finite s ↔ s.finite :=
by rw [finite_iff_nonempty_fintype, finite_def]

/-- Constructor for `set.finite` using a `finite` instance. -/
theorem to_finite (s : set α) [finite s] : s.finite :=
finite_coe_iff.mp ‹_›

/-- Construct a `finite` instance for a `set` from a `finset` with the same elements. -/
protected lemma finite.of_finset {p : set α} (s : finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : p.finite :=
⟨fintype.of_finset s H⟩

/-- Projection of `set.finite` to its `finite` instance.
This is intended to be used with dot notation.
See also `set.finite.fintype` and `set.finite.nonempty_fintype`. -/
protected lemma finite.to_subtype {s : set α} (h : s.finite) : finite s :=
finite_coe_iff.mpr h

/-- A finite set coerced to a type is a `fintype`.
This is the `fintype` projection for a `set.finite`.

Note that because `finite` isn't a typeclass, this definition will not fire if it
is made into an instance -/
protected noncomputable def finite.fintype {s : set α} (h : s.finite) : fintype s :=
h.nonempty_fintype.some

/-- Using choice, get the `finset` that represents this `set.` -/
protected noncomputable def finite.to_finset {s : set α} (h : s.finite) : finset α :=
@set.to_finset _ _ h.fintype

theorem finite.exists_finset {s : set α} (h : s.finite) :
  ∃ s' : finset α, ∀ a : α, a ∈ s' ↔ a ∈ s :=
by { casesI h, exact ⟨s.to_finset, λ _, mem_to_finset⟩ }

theorem finite.exists_finset_coe {s : set α} (h : s.finite) :
  ∃ s' : finset α, ↑s' = s :=
by { casesI h, exact ⟨s.to_finset, s.coe_to_finset⟩ }

/-- Finite sets can be lifted to finsets. -/
instance : can_lift (set α) (finset α) coe set.finite :=
{ prf := λ s hs, hs.exists_finset_coe }

/-- A set is infinite if it is not finite.

This is protected so that it does not conflict with global `infinite`. -/
protected def infinite (s : set α) : Prop := ¬ s.finite

@[simp] lemma not_infinite {s : set α} : ¬ s.infinite ↔ s.finite := not_not

/-- See also `finite_or_infinite`, `fintype_or_infinite`. -/
protected lemma finite_or_infinite (s : set α) : s.finite ∨ s.infinite := em _

/-! ### Basic properties of `set.finite.to_finset` -/

namespace finite
variables {s t : set α} {a : α} {hs : s.finite} {ht : t.finite}

@[simp] protected lemma mem_to_finset (h : s.finite) : a ∈ h.to_finset ↔ a ∈ s :=
@mem_to_finset _ _ h.fintype _

@[simp] protected lemma coe_to_finset (h : s.finite) : (h.to_finset : set α) = s :=
@coe_to_finset _ _ h.fintype

@[simp] protected lemma to_finset_nonempty (h : s.finite) : h.to_finset.nonempty ↔ s.nonempty :=
by rw [← finset.coe_nonempty, finite.coe_to_finset]

/-- Note that this is an equality of types not holding definitionally. Use wisely. -/
lemma coe_sort_to_finset (h : s.finite) : ↥h.to_finset = ↥s :=
by rw [← finset.coe_sort_coe _, h.coe_to_finset]

@[simp] protected lemma to_finset_inj : hs.to_finset = ht.to_finset ↔ s = t :=
@to_finset_inj _ _ _ hs.fintype ht.fintype

@[simp] lemma to_finset_subset {t : finset α} : hs.to_finset ⊆ t ↔ s ⊆ t :=
by rw [←finset.coe_subset, finite.coe_to_finset]

@[simp] lemma to_finset_ssubset {t : finset α} : hs.to_finset ⊂ t ↔ s ⊂ t :=
by rw [←finset.coe_ssubset, finite.coe_to_finset]

@[simp] lemma subset_to_finset {s : finset α} : s ⊆ ht.to_finset ↔ ↑s ⊆ t :=
by rw [←finset.coe_subset, finite.coe_to_finset]

@[simp] lemma ssubset_to_finset {s : finset α} : s ⊂ ht.to_finset ↔ ↑s ⊂ t :=
by rw [←finset.coe_ssubset, finite.coe_to_finset]

@[mono] protected lemma to_finset_subset_to_finset : hs.to_finset ⊆ ht.to_finset ↔ s ⊆ t :=
by simp only [← finset.coe_subset, finite.coe_to_finset]

@[mono] protected lemma to_finset_ssubset_to_finset : hs.to_finset ⊂ ht.to_finset ↔ s ⊂ t :=
by simp only [← finset.coe_ssubset, finite.coe_to_finset]

alias finite.to_finset_subset_to_finset ↔ _ to_finset_mono
alias finite.to_finset_ssubset_to_finset ↔ _ to_finset_strict_mono

attribute [protected] to_finset_mono to_finset_strict_mono

@[simp] protected lemma to_finset_set_of [fintype α] (p : α → Prop) [decidable_pred p]
  (h : {x | p x}.finite) :
  h.to_finset = finset.univ.filter p :=
by { ext, simp }

@[simp] lemma disjoint_to_finset {hs : s.finite} {ht : t.finite} :
  disjoint hs.to_finset ht.to_finset ↔ disjoint s t :=
@disjoint_to_finset _ _ _ hs.fintype ht.fintype

protected lemma to_finset_inter [decidable_eq α] (hs : s.finite) (ht : t.finite)
  (h : (s ∩ t).finite) : h.to_finset = hs.to_finset ∩ ht.to_finset :=
by { ext, simp }

protected lemma to_finset_union [decidable_eq α] (hs : s.finite) (ht : t.finite)
  (h : (s ∪ t).finite) : h.to_finset = hs.to_finset ∪ ht.to_finset :=
by { ext, simp }

protected lemma to_finset_diff [decidable_eq α] (hs : s.finite) (ht : t.finite)
  (h : (s \ t).finite) : h.to_finset = hs.to_finset \ ht.to_finset :=
by { ext, simp }

protected lemma to_finset_symm_diff [decidable_eq α] (hs : s.finite) (ht : t.finite)
  (h : (s ∆ t).finite) : h.to_finset = hs.to_finset ∆ ht.to_finset :=
by { ext, simp [mem_symm_diff, finset.mem_symm_diff] }

protected lemma to_finset_compl [decidable_eq α] [fintype α] (hs : s.finite) (h : sᶜ.finite) :
  h.to_finset = hs.to_finsetᶜ :=
by { ext, simp }

@[simp] protected lemma to_finset_empty (h : (∅ : set α).finite) : h.to_finset = ∅ :=
by { ext, simp }

-- Note: Not `simp` because `set.finite.to_finset_set_of` already proves it
@[simp] protected lemma to_finset_univ [fintype α] (h : (set.univ : set α).finite) :
  h.to_finset = finset.univ :=
by { ext, simp }

@[simp] protected lemma to_finset_eq_empty {h : s.finite} : h.to_finset = ∅ ↔ s = ∅ :=
@to_finset_eq_empty _ _ h.fintype

@[simp] protected lemma to_finset_eq_univ [fintype α] {h : s.finite} :
  h.to_finset = finset.univ ↔ s = univ :=
@to_finset_eq_univ _ _ _ h.fintype

protected lemma to_finset_image [decidable_eq β] (f : α → β) (hs : s.finite) (h : (f '' s).finite) :
  h.to_finset = hs.to_finset.image f :=
by { ext, simp }

@[simp] protected lemma to_finset_range [decidable_eq α] [fintype β] (f : β → α)
  (h : (range f).finite) :
  h.to_finset = finset.univ.image f :=
by { ext, simp }

end finite

/-! ### Fintype instances

Every instance here should have a corresponding `set.finite` constructor in the next section.
 -/

section fintype_instances

instance fintype_univ [fintype α] : fintype (@univ α) :=
fintype.of_equiv α (equiv.set.univ α).symm

/-- If `(set.univ : set α)` is finite then `α` is a finite type. -/
noncomputable def fintype_of_finite_univ (H : (univ : set α).finite) : fintype α :=
@fintype.of_equiv _ (univ : set α) H.fintype (equiv.set.univ _)

instance fintype_union [decidable_eq α] (s t : set α) [fintype s] [fintype t] :
  fintype (s ∪ t : set α) := fintype.of_finset (s.to_finset ∪ t.to_finset) $ by simp

instance fintype_sep (s : set α) (p : α → Prop) [fintype s] [decidable_pred p] :
  fintype ({a ∈ s | p a} : set α) := fintype.of_finset (s.to_finset.filter p) $ by simp

instance fintype_inter (s t : set α) [decidable_eq α] [fintype s] [fintype t] :
  fintype (s ∩ t : set α) := fintype.of_finset (s.to_finset ∩ t.to_finset) $ by simp

/-- A `fintype` instance for set intersection where the left set has a `fintype` instance. -/
instance fintype_inter_of_left (s t : set α) [fintype s] [decidable_pred (∈ t)] :
  fintype (s ∩ t : set α) := fintype.of_finset (s.to_finset.filter (∈ t)) $ by simp

/-- A `fintype` instance for set intersection where the right set has a `fintype` instance. -/
instance fintype_inter_of_right (s t : set α) [fintype t] [decidable_pred (∈ s)] :
  fintype (s ∩ t : set α) := fintype.of_finset (t.to_finset.filter (∈ s)) $ by simp [and_comm]

/-- A `fintype` structure on a set defines a `fintype` structure on its subset. -/
def fintype_subset (s : set α) {t : set α} [fintype s] [decidable_pred (∈ t)] (h : t ⊆ s) :
  fintype t :=
by { rw ← inter_eq_self_of_subset_right h, apply set.fintype_inter_of_left }

instance fintype_diff [decidable_eq α] (s t : set α) [fintype s] [fintype t] :
  fintype (s \ t : set α) := fintype.of_finset (s.to_finset \ t.to_finset) $ by simp

instance fintype_diff_left (s t : set α) [fintype s] [decidable_pred (∈ t)] :
  fintype (s \ t : set α) := set.fintype_sep s (∈ tᶜ)

instance fintype_Union [decidable_eq α] [fintype (plift ι)]
  (f : ι → set α) [∀ i, fintype (f i)] : fintype (⋃ i, f i) :=
fintype.of_finset (finset.univ.bUnion (λ i : plift ι, (f i.down).to_finset)) $ by simp

instance fintype_sUnion [decidable_eq α] {s : set (set α)}
  [fintype s] [H : ∀ (t : s), fintype (t : set α)] : fintype (⋃₀ s) :=
by { rw sUnion_eq_Union, exact @set.fintype_Union _ _ _ _ _ H }

/-- A union of sets with `fintype` structure over a set with `fintype` structure has a `fintype`
structure. -/
def fintype_bUnion [decidable_eq α] {ι : Type*} (s : set ι) [fintype s]
  (t : ι → set α) (H : ∀ i ∈ s, fintype (t i)) : fintype (⋃(x ∈ s), t x) :=
fintype.of_finset
(s.to_finset.attach.bUnion
  (λ x, by { haveI := H x (by simpa using x.property), exact (t x).to_finset })) $ by simp

instance fintype_bUnion' [decidable_eq α] {ι : Type*} (s : set ι) [fintype s]
  (t : ι → set α) [∀ i, fintype (t i)] : fintype (⋃(x ∈ s), t x) :=
fintype.of_finset (s.to_finset.bUnion (λ x, (t x).to_finset)) $ by simp

/-- If `s : set α` is a set with `fintype` instance and `f : α → set β` is a function such that
each `f a`, `a ∈ s`, has a `fintype` structure, then `s >>= f` has a `fintype` structure. -/
def fintype_bind {α β} [decidable_eq β] (s : set α) [fintype s]
  (f : α → set β) (H : ∀ a ∈ s, fintype (f a)) : fintype (s >>= f) :=
set.fintype_bUnion s f H

instance fintype_bind' {α β} [decidable_eq β] (s : set α) [fintype s]
  (f : α → set β) [H : ∀ a, fintype (f a)] : fintype (s >>= f) :=
set.fintype_bUnion' s f

instance fintype_empty : fintype (∅ : set α) := fintype.of_finset ∅ $ by simp

instance fintype_singleton (a : α) : fintype ({a} : set α) := fintype.of_finset {a} $ by simp

instance fintype_pure : ∀ a : α, fintype (pure a : set α) :=
set.fintype_singleton

/-- A `fintype` instance for inserting an element into a `set` using the
corresponding `insert` function on `finset`. This requires `decidable_eq α`.
There is also `set.fintype_insert'` when `a ∈ s` is decidable. -/
instance fintype_insert (a : α) (s : set α) [decidable_eq α] [fintype s] :
  fintype (insert a s : set α) :=
fintype.of_finset (insert a s.to_finset) $ by simp

/-- A `fintype` structure on `insert a s` when inserting a new element. -/
def fintype_insert_of_not_mem {a : α} (s : set α) [fintype s] (h : a ∉ s) :
  fintype (insert a s : set α) :=
fintype.of_finset ⟨a ::ₘ s.to_finset.1, s.to_finset.nodup.cons (by simp [h]) ⟩ $ by simp

/-- A `fintype` structure on `insert a s` when inserting a pre-existing element. -/
def fintype_insert_of_mem {a : α} (s : set α) [fintype s] (h : a ∈ s) :
  fintype (insert a s : set α) :=
fintype.of_finset s.to_finset $ by simp [h]

/-- The `set.fintype_insert` instance requires decidable equality, but when `a ∈ s`
is decidable for this particular `a` we can still get a `fintype` instance by using
`set.fintype_insert_of_not_mem` or `set.fintype_insert_of_mem`.

This instance pre-dates `set.fintype_insert`, and it is less efficient.
When `decidable_mem_of_fintype` is made a local instance, then this instance would
override `set.fintype_insert` if not for the fact that its priority has been
adjusted. See Note [lower instance priority]. -/
@[priority 100]
instance fintype_insert' (a : α) (s : set α) [decidable $ a ∈ s] [fintype s] :
  fintype (insert a s : set α) :=
if h : a ∈ s then fintype_insert_of_mem s h else fintype_insert_of_not_mem s h

instance fintype_image [decidable_eq β] (s : set α) (f : α → β) [fintype s] : fintype (f '' s) :=
fintype.of_finset (s.to_finset.image f) $ by simp

/-- If a function `f` has a partial inverse and sends a set `s` to a set with `[fintype]` instance,
then `s` has a `fintype` structure as well. -/
def fintype_of_fintype_image (s : set α)
  {f : α → β} {g} (I : is_partial_inv f g) [fintype (f '' s)] : fintype s :=
fintype.of_finset ⟨_, (f '' s).to_finset.2.filter_map g $ injective_of_partial_inv_right I⟩ $ λ a,
begin
  suffices : (∃ b x, f x = b ∧ g b = some a ∧ x ∈ s) ↔ a ∈ s,
  by simpa [exists_and_distrib_left.symm, and.comm, and.left_comm, and.assoc],
  rw exists_swap,
  suffices : (∃ x, x ∈ s ∧ g (f x) = some a) ↔ a ∈ s, {simpa [and.comm, and.left_comm, and.assoc]},
  simp [I _, (injective_of_partial_inv I).eq_iff]
end

instance fintype_range [decidable_eq α] (f : ι → α) [fintype (plift ι)] :
  fintype (range f) :=
fintype.of_finset (finset.univ.image $ f ∘ plift.down) $ by simp [equiv.plift.exists_congr_left]

instance fintype_map {α β} [decidable_eq β] :
  ∀ (s : set α) (f : α → β) [fintype s], fintype (f <$> s) := set.fintype_image

instance fintype_lt_nat (n : ℕ) : fintype {i | i < n} :=
fintype.of_finset (finset.range n) $ by simp

instance fintype_le_nat (n : ℕ) : fintype {i | i ≤ n} :=
by simpa [nat.lt_succ_iff] using set.fintype_lt_nat (n+1)

/-- This is not an instance so that it does not conflict with the one
in src/order/locally_finite. -/
def nat.fintype_Iio (n : ℕ) : fintype (Iio n) :=
set.fintype_lt_nat n

instance fintype_prod (s : set α) (t : set β) [fintype s] [fintype t] :
  fintype (s ×ˢ t : set (α × β)) :=
fintype.of_finset (s.to_finset ×ˢ t.to_finset) $ by simp

instance fintype_off_diag [decidable_eq α] (s : set α) [fintype s] : fintype s.off_diag :=
fintype.of_finset s.to_finset.off_diag $ by simp

/-- `image2 f s t` is `fintype` if `s` and `t` are. -/
instance fintype_image2 [decidable_eq γ] (f : α → β → γ) (s : set α) (t : set β)
  [hs : fintype s] [ht : fintype t] : fintype (image2 f s t : set γ) :=
by { rw ← image_prod, apply set.fintype_image }

instance fintype_seq [decidable_eq β] (f : set (α → β)) (s : set α) [fintype f] [fintype s] :
  fintype (f.seq s) :=
by { rw seq_def, apply set.fintype_bUnion' }

instance fintype_seq' {α β : Type u} [decidable_eq β]
  (f : set (α → β)) (s : set α) [fintype f] [fintype s] : fintype (f <*> s) :=
set.fintype_seq f s

instance fintype_mem_finset (s : finset α) : fintype {a | a ∈ s} :=
finset.fintype_coe_sort s

end fintype_instances

end set

/-! ### Finset -/

namespace finset

/-- Gives a `set.finite` for the `finset` coerced to a `set`.
This is a wrapper around `set.to_finite`. -/
@[simp] lemma finite_to_set (s : finset α) : (s : set α).finite := set.to_finite _

@[simp] lemma finite_to_set_to_finset (s : finset α) : s.finite_to_set.to_finset = s :=
by { ext, rw [set.finite.mem_to_finset, mem_coe] }

end finset

namespace multiset

@[simp] lemma finite_to_set (s : multiset α) : {x | x ∈ s}.finite :=
by { classical, simpa only [← multiset.mem_to_finset] using s.to_finset.finite_to_set }

@[simp] lemma finite_to_set_to_finset [decidable_eq α] (s : multiset α) :
  s.finite_to_set.to_finset = s.to_finset :=
by { ext x, simp }

end multiset

@[simp] lemma list.finite_to_set (l : list α) : {x | x ∈ l}.finite :=
(show multiset α, from ⟦l⟧).finite_to_set

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `fintype` instances
in `data.set.finite`. While every `fintype` instance gives a `finite` instance, those
instances that depend on `fintype` or `decidable` instances need an additional `finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`subtype.finite` for subsets of a finite type.
-/

namespace finite.set

open_locale classical

example {s : set α} [finite α] : finite s := infer_instance
example : finite (∅ : set α) := infer_instance
example (a : α) : finite ({a} : set α) := infer_instance

instance finite_union (s t : set α) [finite s] [finite t] :
  finite (s ∪ t : set α) :=
by { casesI nonempty_fintype s, casesI nonempty_fintype t, apply_instance }

instance finite_sep (s : set α) (p : α → Prop) [finite s] :
  finite ({a ∈ s | p a} : set α) :=
by { casesI nonempty_fintype s, apply_instance }

protected lemma subset (s : set α) {t : set α} [finite s] (h : t ⊆ s) : finite t :=
by { rw ←sep_eq_of_subset h, apply_instance }

instance finite_inter_of_right (s t : set α) [finite t] :
  finite (s ∩ t : set α) := finite.set.subset t (inter_subset_right s t)

instance finite_inter_of_left (s t : set α) [finite s] :
  finite (s ∩ t : set α) := finite.set.subset s (inter_subset_left s t)

instance finite_diff (s t : set α) [finite s] :
  finite (s \ t : set α) := finite.set.subset s (diff_subset s t)

instance finite_range (f : ι → α) [finite ι] : finite (range f) :=
by { haveI := fintype.of_finite (plift ι), apply_instance }

instance finite_Union [finite ι] (f : ι → set α) [∀ i, finite (f i)] : finite (⋃ i, f i) :=
begin
  rw [Union_eq_range_psigma],
  apply set.finite_range
end

instance finite_sUnion {s : set (set α)} [finite s] [H : ∀ (t : s), finite (t : set α)] :
  finite (⋃₀ s) :=
by { rw sUnion_eq_Union, exact @finite.set.finite_Union _ _ _ _ H }

lemma finite_bUnion {ι : Type*} (s : set ι) [finite s] (t : ι → set α) (H : ∀ i ∈ s, finite (t i)) :
  finite (⋃(x ∈ s), t x) :=
begin
  rw [bUnion_eq_Union],
  haveI : ∀ (i : s), finite (t i) := λ i, H i i.property,
  apply_instance,
end

instance finite_bUnion' {ι : Type*} (s : set ι) [finite s] (t : ι → set α) [∀ i, finite (t i)] :
  finite (⋃(x ∈ s), t x) :=
finite_bUnion s t (λ i h, infer_instance)

/--
Example: `finite (⋃ (i < n), f i)` where `f : ℕ → set α` and `[∀ i, finite (f i)]`
(when given instances from `data.nat.interval`).
-/
instance finite_bUnion'' {ι : Type*} (p : ι → Prop) [h : finite {x | p x}]
  (t : ι → set α) [∀ i, finite (t i)] :
  finite (⋃ x (h : p x), t x) :=
@finite.set.finite_bUnion' _ _ (set_of p) h t _

instance finite_Inter {ι : Sort*} [nonempty ι] (t : ι → set α) [∀ i, finite (t i)] :
  finite (⋂ i, t i) :=
finite.set.subset (t $ classical.arbitrary ι) (Inter_subset _ _)

instance finite_insert (a : α) (s : set α) [finite s] : finite (insert a s : set α) :=
finite.set.finite_union {a} s

instance finite_image (s : set α) (f : α → β) [finite s] : finite (f '' s) :=
by { casesI nonempty_fintype s, apply_instance }

instance finite_replacement [finite α] (f : α → β) : finite {(f x) | (x : α)} :=
finite.set.finite_range f

instance finite_prod (s : set α) (t : set β) [finite s] [finite t] :
  finite (s ×ˢ t : set (α × β)) :=
finite.of_equiv _ (equiv.set.prod s t).symm

instance finite_image2 (f : α → β → γ) (s : set α) (t : set β) [finite s] [finite t] :
  finite (image2 f s t : set γ) :=
by { rw ← image_prod, apply_instance }

instance finite_seq (f : set (α → β)) (s : set α) [finite f] [finite s] : finite (f.seq s) :=
by { rw seq_def, apply_instance }

end finite.set

namespace set

/-! ### Constructors for `set.finite`

Every constructor here should have a corresponding `fintype` instance in the previous section
(or in the `fintype` module).

The implementation of these constructors ideally should be no more than `set.to_finite`,
after possibly setting up some `fintype` and classical `decidable` instances.
-/
section set_finite_constructors

@[nontriviality] lemma finite.of_subsingleton [subsingleton α] (s : set α) : s.finite := s.to_finite

theorem finite_univ [finite α] : (@univ α).finite := set.to_finite _

theorem finite_univ_iff : (@univ α).finite ↔ finite α :=
finite_coe_iff.symm.trans (equiv.set.univ α).finite_iff

alias finite_univ_iff ↔ _root_.finite.of_finite_univ _

theorem finite.union {s t : set α} (hs : s.finite) (ht : t.finite) : (s ∪ t).finite :=
by { casesI hs, casesI ht, apply to_finite }

theorem finite.finite_of_compl {s : set α} (hs : s.finite) (hsc : sᶜ.finite) : finite α :=
by { rw [← finite_univ_iff, ← union_compl_self s], exact hs.union hsc }

lemma finite.sup {s t : set α} : s.finite → t.finite → (s ⊔ t).finite := finite.union

theorem finite.sep {s : set α} (hs : s.finite) (p : α → Prop) : {a ∈ s | p a}.finite :=
by { casesI hs, apply to_finite }

theorem finite.inter_of_left {s : set α} (hs : s.finite) (t : set α) : (s ∩ t).finite :=
by { casesI hs, apply to_finite }

theorem finite.inter_of_right {s : set α} (hs : s.finite) (t : set α) : (t ∩ s).finite :=
by { casesI hs, apply to_finite }

theorem finite.inf_of_left {s : set α} (h : s.finite) (t : set α) : (s ⊓ t).finite :=
h.inter_of_left t

theorem finite.inf_of_right {s : set α} (h : s.finite) (t : set α) : (t ⊓ s).finite :=
h.inter_of_right t

theorem finite.subset {s : set α} (hs : s.finite) {t : set α} (ht : t ⊆ s) : t.finite :=
by { casesI hs, haveI := finite.set.subset _ ht, apply to_finite }

theorem finite.diff {s : set α} (hs : s.finite) (t : set α) : (s \ t).finite :=
by { casesI hs, apply to_finite }

theorem finite.of_diff {s t : set α} (hd : (s \ t).finite) (ht : t.finite) : s.finite :=
(hd.union ht).subset $ subset_diff_union _ _

theorem finite_Union [finite ι] {f : ι → set α} (H : ∀ i, (f i).finite) :
  (⋃ i, f i).finite :=
by { haveI := λ i, (H i).fintype, apply to_finite }

theorem finite.sUnion {s : set (set α)} (hs : s.finite) (H : ∀ t ∈ s, set.finite t) :
  (⋃₀ s).finite :=
by { casesI hs, haveI := λ (i : s), (H i i.2).to_subtype, apply to_finite }

theorem finite.bUnion {ι} {s : set ι} (hs : s.finite)
  {t : ι → set α} (ht : ∀ i ∈ s, (t i).finite) : (⋃(i ∈ s), t i).finite :=
by { classical, casesI hs,
     haveI := fintype_bUnion s t (λ i hi, (ht i hi).fintype), apply to_finite }

/-- Dependent version of `finite.bUnion`. -/
theorem finite.bUnion' {ι} {s : set ι} (hs : s.finite)
  {t : Π (i ∈ s), set α} (ht : ∀ i ∈ s, (t i ‹_›).finite) : (⋃(i ∈ s), t i ‹_›).finite :=
by { casesI hs, rw [bUnion_eq_Union], apply finite_Union (λ (i : s), ht i.1 i.2), }

theorem finite.sInter {α : Type*} {s : set (set α)} {t : set α} (ht : t ∈ s)
  (hf : t.finite) : (⋂₀ s).finite :=
hf.subset (sInter_subset_of_mem ht)

theorem finite.bind {α β} {s : set α} {f : α → set β} (h : s.finite) (hf : ∀ a ∈ s, (f a).finite) :
  (s >>= f).finite :=
h.bUnion hf

@[simp] theorem finite_empty : (∅ : set α).finite := to_finite _

@[simp] theorem finite_singleton (a : α) : ({a} : set α).finite := to_finite _

theorem finite_pure (a : α) : (pure a : set α).finite := to_finite _

@[simp] theorem finite.insert (a : α) {s : set α} (hs : s.finite) : (insert a s).finite :=
by { casesI hs, apply to_finite }

theorem finite.image {s : set α} (f : α → β) (hs : s.finite) : (f '' s).finite :=
by { casesI hs, apply to_finite }

theorem finite_range (f : ι → α) [finite ι] : (range f).finite :=
to_finite _

lemma finite.dependent_image {s : set α} (hs : s.finite) (F : Π i ∈ s, β) :
  {y : β | ∃ x (hx : x ∈ s), y = F x hx}.finite :=
by { casesI hs, simpa [range, eq_comm] using finite_range (λ x : s, F x x.2) }

theorem finite.map {α β} {s : set α} : ∀ (f : α → β), s.finite → (f <$> s).finite :=
finite.image

theorem finite.of_finite_image {s : set α} {f : α → β} (h : (f '' s).finite) (hi : set.inj_on f s) :
  s.finite :=
by { casesI h, exact ⟨fintype.of_injective (λ a, (⟨f a.1, mem_image_of_mem f a.2⟩ : f '' s))
                       (λ a b eq, subtype.eq $ hi a.2 b.2 $ subtype.ext_iff_val.1 eq)⟩ }

lemma finite_of_finite_preimage {f : α → β} {s : set β} (h : (f ⁻¹' s).finite)
  (hs : s ⊆ range f) : s.finite :=
by { rw [← image_preimage_eq_of_subset hs], exact finite.image f h }

theorem finite.of_preimage {f : α → β} {s : set β} (h : (f ⁻¹' s).finite) (hf : surjective f) :
  s.finite :=
hf.image_preimage s ▸ h.image _

theorem finite.preimage {s : set β} {f : α → β}
  (I : set.inj_on f (f⁻¹' s)) (h : s.finite) : (f ⁻¹' s).finite :=
(h.subset (image_preimage_subset f s)).of_finite_image I

theorem finite.preimage_embedding {s : set β} (f : α ↪ β) (h : s.finite) : (f ⁻¹' s).finite :=
h.preimage (λ _ _ _ _ h', f.injective h')

lemma finite_lt_nat (n : ℕ) : set.finite {i | i < n} := to_finite _

lemma finite_le_nat (n : ℕ) : set.finite {i | i ≤ n} := to_finite _

lemma finite.prod {s : set α} {t : set β} (hs : s.finite) (ht : t.finite) :
  (s ×ˢ t : set (α × β)).finite :=
by { casesI hs, casesI ht, apply to_finite }

lemma finite.off_diag {s : set α} (hs : s.finite) : s.off_diag.finite :=
by { classical, casesI hs, apply set.to_finite }

lemma finite.image2 (f : α → β → γ) {s : set α} {t : set β} (hs : s.finite) (ht : t.finite) :
  (image2 f s t).finite :=
by { casesI hs, casesI ht, apply to_finite }

theorem finite.seq {f : set (α → β)} {s : set α} (hf : f.finite) (hs : s.finite) :
  (f.seq s).finite :=
by { classical, casesI hf, casesI hs, apply to_finite }

theorem finite.seq' {α β : Type u} {f : set (α → β)} {s : set α} (hf : f.finite) (hs : s.finite) :
  (f <*> s).finite :=
hf.seq hs

theorem finite_mem_finset (s : finset α) : {a | a ∈ s}.finite := to_finite _

lemma subsingleton.finite {s : set α} (h : s.subsingleton) : s.finite :=
h.induction_on finite_empty finite_singleton

lemma finite_preimage_inl_and_inr {s : set (α ⊕ β)} :
  (sum.inl ⁻¹' s).finite ∧ (sum.inr ⁻¹' s).finite ↔ s.finite :=
⟨λ h, image_preimage_inl_union_image_preimage_inr s ▸ (h.1.image _).union (h.2.image _),
  λ h, ⟨h.preimage (sum.inl_injective.inj_on _), h.preimage (sum.inr_injective.inj_on _)⟩⟩

theorem exists_finite_iff_finset {p : set α → Prop} :
  (∃ s : set α, s.finite ∧ p s) ↔ ∃ s : finset α, p ↑s :=
⟨λ ⟨s, hs, hps⟩, ⟨hs.to_finset, hs.coe_to_finset.symm ▸ hps⟩,
  λ ⟨s, hs⟩, ⟨s, s.finite_to_set, hs⟩⟩

/-- There are finitely many subsets of a given finite set -/
lemma finite.finite_subsets {α : Type u} {a : set α} (h : a.finite) : {b | b ⊆ a}.finite :=
⟨fintype.of_finset ((finset.powerset h.to_finset).map finset.coe_emb.1) $ λ s,
  by simpa [← @exists_finite_iff_finset α (λ t, t ⊆ a ∧ t = s), finite.subset_to_finset,
    ← and.assoc] using h.subset⟩

/-- Finite product of finite sets is finite -/
lemma finite.pi {δ : Type*} [finite δ] {κ : δ → Type*} {t : Π d, set (κ d)}
  (ht : ∀ d, (t d).finite) :
  (pi univ t).finite :=
begin
  casesI nonempty_fintype δ,
  lift t to Π d, finset (κ d) using ht,
  classical,
  rw ← fintype.coe_pi_finset,
  apply finset.finite_to_set
end

/-- A finite union of finsets is finite. -/
lemma union_finset_finite_of_range_finite (f : α → finset β) (h : (range f).finite) :
  (⋃ a, (f a : set β)).finite :=
by { rw ← bUnion_range, exact h.bUnion (λ y hy, y.finite_to_set) }

lemma finite_range_ite {p : α → Prop} [decidable_pred p] {f g : α → β} (hf : (range f).finite)
  (hg : (range g).finite) : (range (λ x, if p x then f x else g x)).finite :=
(hf.union hg).subset range_ite_subset

lemma finite_range_const {c : β} : (range (λ x : α, c)).finite :=
(finite_singleton c).subset range_const_subset

end set_finite_constructors

/-! ### Properties -/

instance finite.inhabited : inhabited {s : set α // s.finite} := ⟨⟨∅, finite_empty⟩⟩

@[simp] lemma finite_union {s t : set α} : (s ∪ t).finite ↔ s.finite ∧ t.finite :=
⟨λ h, ⟨h.subset (subset_union_left _ _), h.subset (subset_union_right _ _)⟩,
 λ ⟨hs, ht⟩, hs.union ht⟩

theorem finite_image_iff {s : set α} {f : α → β} (hi : inj_on f s) :
  (f '' s).finite ↔ s.finite :=
⟨λ h, h.of_finite_image hi, finite.image _⟩

lemma univ_finite_iff_nonempty_fintype :
  (univ : set α).finite ↔ nonempty (fintype α) :=
⟨λ h, ⟨fintype_of_finite_univ h⟩, λ ⟨_i⟩, by exactI finite_univ⟩

@[simp] lemma finite.to_finset_singleton {a : α} (ha : ({a} : set α).finite := finite_singleton _) :
  ha.to_finset = {a} :=
finset.ext $ by simp

@[simp] lemma finite.to_finset_insert [decidable_eq α] {s : set α} {a : α}
  (hs : (insert a s).finite) :
  hs.to_finset = insert a (hs.subset $ subset_insert _ _).to_finset :=
finset.ext $ by simp

lemma finite.to_finset_insert' [decidable_eq α] {a : α} {s : set α} (hs : s.finite) :
  (hs.insert a).to_finset = insert a hs.to_finset :=
finite.to_finset_insert _

lemma finite.to_finset_prod {s : set α} {t : set β} (hs : s.finite) (ht : t.finite) :
hs.to_finset ×ˢ ht.to_finset = (hs.prod ht).to_finset := finset.ext $ by simp

lemma finite.to_finset_off_diag {s : set α} [decidable_eq α] (hs : s.finite) :
hs.off_diag.to_finset = hs.to_finset.off_diag := finset.ext $ by simp

lemma finite.fin_embedding {s : set α} (h : s.finite) : ∃ (n : ℕ) (f : fin n ↪ α), range f = s :=
⟨_, (fintype.equiv_fin (h.to_finset : set α)).symm.as_embedding, by simp⟩

lemma finite.fin_param {s : set α} (h : s.finite) :
  ∃ (n : ℕ) (f : fin n → α), injective f ∧ range f = s :=
let ⟨n, f, hf⟩ := h.fin_embedding in ⟨n, f, f.injective, hf⟩

lemma finite_option {s : set (option α)} : s.finite ↔ {x : α | some x ∈ s}.finite :=
⟨λ h, h.preimage_embedding embedding.some,
  λ h, ((h.image some).insert none).subset $
    λ x, option.cases_on x (λ _, or.inl rfl) (λ x hx, or.inr $ mem_image_of_mem _ hx)⟩

lemma finite_image_fst_and_snd_iff {s : set (α × β)} :
  (prod.fst '' s).finite ∧ (prod.snd '' s).finite ↔ s.finite :=
⟨λ h, (h.1.prod h.2).subset $ λ x h, ⟨mem_image_of_mem _ h, mem_image_of_mem _ h⟩,
  λ h, ⟨h.image _, h.image _⟩⟩

lemma forall_finite_image_eval_iff {δ : Type*} [finite δ] {κ : δ → Type*} {s : set (Π d, κ d)} :
  (∀ d, (eval d '' s).finite) ↔ s.finite :=
⟨λ h, (finite.pi h).subset $ subset_pi_eval_image _ _, λ h d, h.image _⟩

lemma finite_subset_Union {s : set α} (hs : s.finite)
  {ι} {t : ι → set α} (h : s ⊆ ⋃ i, t i) : ∃ I : set ι, I.finite ∧ s ⊆ ⋃ i ∈ I, t i :=
begin
  casesI hs,
  choose f hf using show ∀ x : s, ∃ i, x.1 ∈ t i, {simpa [subset_def] using h},
  refine ⟨range f, finite_range f, λ x hx, _⟩,
  rw [bUnion_range, mem_Union],
  exact ⟨⟨x, hx⟩, hf _⟩
end

lemma eq_finite_Union_of_finite_subset_Union  {ι} {s : ι → set α} {t : set α} (tfin : t.finite)
  (h : t ⊆ ⋃ i, s i) :
  ∃ I : set ι, I.finite ∧ ∃ σ : {i | i ∈ I} → set α,
     (∀ i, (σ i).finite) ∧ (∀ i, σ i ⊆ s i) ∧ t = ⋃ i, σ i :=
let ⟨I, Ifin, hI⟩ := finite_subset_Union tfin h in
⟨I, Ifin, λ x, s x ∩ t,
    λ i, tfin.subset (inter_subset_right _ _),
    λ i, inter_subset_left _ _,
    begin
      ext x,
      rw mem_Union,
      split,
      { intro x_in,
        rcases mem_Union.mp (hI x_in) with ⟨i, _, ⟨hi, rfl⟩, H⟩,
        use [i, hi, H, x_in] },
      { rintros ⟨i, hi, H⟩,
        exact H }
    end⟩

@[elab_as_eliminator]
theorem finite.induction_on {C : set α → Prop} {s : set α} (h : s.finite)
  (H0 : C ∅) (H1 : ∀ {a s}, a ∉ s → set.finite s → C s → C (insert a s)) : C s :=
begin
  lift s to finset α using h,
  induction s using finset.cons_induction_on with a s ha hs,
  { rwa [finset.coe_empty] },
  { rw [finset.coe_cons],
    exact @H1 a s ha (set.to_finite _) hs }
end

/-- Analogous to `finset.induction_on'`. -/
@[elab_as_eliminator]
theorem finite.induction_on' {C : set α → Prop} {S : set α} (h : S.finite)
  (H0 : C ∅) (H1 : ∀ {a s}, a ∈ S → s ⊆ S → a ∉ s → C s → C (insert a s)) : C S :=
begin
  refine @set.finite.induction_on α (λ s, s ⊆ S → C s) S h (λ _, H0) _ subset.rfl,
  intros a s has hsf hCs haS,
  rw insert_subset at haS,
  exact H1 haS.1 haS.2 has (hCs haS.2)
end

@[elab_as_eliminator]
theorem finite.dinduction_on {C : ∀ (s : set α), s.finite → Prop} {s : set α} (h : s.finite)
  (H0 : C ∅ finite_empty)
  (H1 : ∀ {a s}, a ∉ s → ∀ h : set.finite s, C s h → C (insert a s) (h.insert a)) :
  C s h :=
have ∀ h : s.finite, C s h,
  from finite.induction_on h (λ h, H0) (λ a s has hs ih h, H1 has hs (ih _)),
this h

section
local attribute [instance] nat.fintype_Iio

/--
If `P` is some relation between terms of `γ` and sets in `γ`,
such that every finite set `t : set γ` has some `c : γ` related to it,
then there is a recursively defined sequence `u` in `γ`
so `u n` is related to the image of `{0, 1, ..., n-1}` under `u`.

(We use this later to show sequentially compact sets
are totally bounded.)
-/
lemma seq_of_forall_finite_exists  {γ : Type*}
  {P : γ → set γ → Prop} (h : ∀ t : set γ, t.finite → ∃ c, P c t) :
  ∃ u : ℕ → γ, ∀ n, P (u n) (u '' Iio n) :=
⟨λ n, @nat.strong_rec_on' (λ _, γ) n $ λ n ih, classical.some $ h
    (range $ λ m : Iio n, ih m.1 m.2)
    (finite_range _),
λ n, begin
  classical,
  refine nat.strong_rec_on' n (λ n ih, _),
  rw nat.strong_rec_on_beta', convert classical.some_spec (h _ _),
  ext x, split,
  { rintros ⟨m, hmn, rfl⟩, exact ⟨⟨m, hmn⟩, rfl⟩ },
  { rintros ⟨⟨m, hmn⟩, rfl⟩, exact ⟨m, hmn, rfl⟩ }
end⟩

end

/-! ### Cardinality -/

theorem empty_card : fintype.card (∅ : set α) = 0 := rfl

@[simp] theorem empty_card' {h : fintype.{u} (∅ : set α)} :
  @fintype.card (∅ : set α) h = 0 :=
eq.trans (by congr) empty_card

theorem card_fintype_insert_of_not_mem {a : α} (s : set α) [fintype s] (h : a ∉ s) :
  @fintype.card _ (fintype_insert_of_not_mem s h) = fintype.card s + 1 :=
by rw [fintype_insert_of_not_mem, fintype.card_of_finset];
   simp [finset.card, to_finset]; refl

@[simp] theorem card_insert {a : α} (s : set α)
  [fintype s] (h : a ∉ s) {d : fintype.{u} (insert a s : set α)} :
  @fintype.card _ d = fintype.card s + 1 :=
by rw ← card_fintype_insert_of_not_mem s h; congr

lemma card_image_of_inj_on {s : set α} [fintype s]
  {f : α → β} [fintype (f '' s)] (H : ∀x∈s, ∀y∈s, f x = f y → x = y) :
  fintype.card (f '' s) = fintype.card s :=
by haveI := classical.prop_decidable; exact
calc fintype.card (f '' s) = (s.to_finset.image f).card : fintype.card_of_finset' _ (by simp)
... = s.to_finset.card : finset.card_image_of_inj_on
    (λ x hx y hy hxy, H x (mem_to_finset.1 hx) y (mem_to_finset.1 hy) hxy)
... = fintype.card s : (fintype.card_of_finset' _ (λ a, mem_to_finset)).symm

lemma card_image_of_injective (s : set α) [fintype s]
  {f : α → β} [fintype (f '' s)] (H : function.injective f) :
  fintype.card (f '' s) = fintype.card s :=
card_image_of_inj_on $ λ _ _ _ _ h, H h

@[simp] theorem card_singleton (a : α) :
  fintype.card ({a} : set α) = 1 :=
fintype.card_of_subsingleton _

lemma card_lt_card {s t : set α} [fintype s] [fintype t] (h : s ⊂ t) :
  fintype.card s < fintype.card t :=
fintype.card_lt_of_injective_not_surjective (set.inclusion h.1) (set.inclusion_injective h.1) $
  λ hst, (ssubset_iff_subset_ne.1 h).2 (eq_of_inclusion_surjective hst)

lemma card_le_of_subset {s t : set α} [fintype s] [fintype t] (hsub : s ⊆ t) :
  fintype.card s ≤ fintype.card t :=
fintype.card_le_of_injective (set.inclusion hsub) (set.inclusion_injective hsub)

lemma eq_of_subset_of_card_le {s t : set α} [fintype s] [fintype t]
   (hsub : s ⊆ t) (hcard : fintype.card t ≤ fintype.card s) : s = t :=
(eq_or_ssubset_of_subset hsub).elim id
  (λ h, absurd hcard $ not_le_of_lt $ card_lt_card h)

lemma card_range_of_injective [fintype α] {f : α → β} (hf : injective f)
  [fintype (range f)] : fintype.card (range f) = fintype.card α :=
eq.symm $ fintype.card_congr $ equiv.of_injective f hf

lemma finite.card_to_finset {s : set α} [fintype s] (h : s.finite) :
  h.to_finset.card = fintype.card s :=
begin
  rw [← finset.card_attach, finset.attach_eq_univ, ← fintype.card],
  refine fintype.card_congr (equiv.set_congr _),
  ext x,
  show x ∈ h.to_finset ↔ x ∈ s,
  simp,
end

lemma card_ne_eq [fintype α] (a : α) [fintype {x : α | x ≠ a}] :
  fintype.card {x : α | x ≠ a} = fintype.card α - 1 :=
begin
  haveI := classical.dec_eq α,
  rw [←to_finset_card, to_finset_set_of, finset.filter_ne',
    finset.card_erase_of_mem (finset.mem_univ _), finset.card_univ],
end


/-! ### Infinite sets -/

theorem infinite_univ_iff : (@univ α).infinite ↔ infinite α :=
by rw [set.infinite, finite_univ_iff, not_finite_iff_infinite]

theorem infinite_univ [h : infinite α] : (@univ α).infinite :=
infinite_univ_iff.2 h

theorem infinite_coe_iff {s : set α} : infinite s ↔ s.infinite :=
not_finite_iff_infinite.symm.trans finite_coe_iff.not

alias infinite_coe_iff ↔ _ infinite.to_subtype

/-- Embedding of `ℕ` into an infinite set. -/
noncomputable def infinite.nat_embedding (s : set α) (h : s.infinite) : ℕ ↪ s :=
by { haveI := h.to_subtype, exact infinite.nat_embedding s }

lemma infinite.exists_subset_card_eq {s : set α} (hs : s.infinite) (n : ℕ) :
  ∃ t : finset α, ↑t ⊆ s ∧ t.card = n :=
⟨((finset.range n).map (hs.nat_embedding _)).map (embedding.subtype _), by simp⟩

lemma infinite.nonempty {s : set α} (h : s.infinite) : s.nonempty :=
let a := infinite.nat_embedding s h 37 in ⟨a.1, a.2⟩

lemma infinite_of_finite_compl [infinite α] {s : set α} (hs : sᶜ.finite) : s.infinite :=
λ h, set.infinite_univ (by simpa using hs.union h)

lemma finite.infinite_compl [infinite α] {s : set α} (hs : s.finite) : sᶜ.infinite :=
λ h, set.infinite_univ (by simpa using hs.union h)

protected theorem infinite.mono {s t : set α} (h : s ⊆ t) : s.infinite → t.infinite :=
mt (λ ht, ht.subset h)

lemma infinite.diff {s t : set α} (hs : s.infinite) (ht : t.finite) : (s \ t).infinite :=
λ h, hs $ h.of_diff ht

@[simp] lemma infinite_union {s t : set α} : (s ∪ t).infinite ↔ s.infinite ∨ t.infinite :=
by simp only [set.infinite, finite_union, not_and_distrib]

theorem infinite_of_infinite_image (f : α → β) {s : set α} (hs : (f '' s).infinite) :
  s.infinite :=
mt (finite.image f) hs

theorem infinite_image_iff {s : set α} {f : α → β} (hi : inj_on f s) :
  (f '' s).infinite ↔ s.infinite :=
not_congr $ finite_image_iff hi

theorem infinite_of_inj_on_maps_to {s : set α} {t : set β} {f : α → β}
  (hi : inj_on f s) (hm : maps_to f s t) (hs : s.infinite) : t.infinite :=
((infinite_image_iff hi).2 hs).mono (maps_to'.mp hm)

theorem infinite.exists_ne_map_eq_of_maps_to {s : set α} {t : set β} {f : α → β}
  (hs : s.infinite) (hf : maps_to f s t) (ht : t.finite) :
  ∃ (x ∈ s) (y ∈ s), x ≠ y ∧ f x = f y :=
begin
  contrapose! ht,
  exact infinite_of_inj_on_maps_to (λ x hx y hy, not_imp_not.1 (ht x hx y hy)) hf hs
end

theorem infinite_range_of_injective [infinite α] {f : α → β} (hi : injective f) :
  (range f).infinite :=
by { rw [←image_univ, infinite_image_iff (inj_on_of_injective hi _)], exact infinite_univ }

theorem infinite_of_injective_forall_mem [infinite α] {s : set β} {f : α → β}
  (hi : injective f) (hf : ∀ x : α, f x ∈ s) : s.infinite :=
by { rw ←range_subset_iff at hf, exact (infinite_range_of_injective hi).mono hf }

lemma infinite.exists_nat_lt {s : set ℕ} (hs : s.infinite) (n : ℕ) : ∃ m ∈ s, n < m :=
let ⟨m, hm⟩ := (hs.diff $ set.finite_le_nat n).nonempty in ⟨m, by simpa using hm⟩

lemma infinite.exists_not_mem_finset {s : set α} (hs : s.infinite) (f : finset α) :
  ∃ a ∈ s, a ∉ f :=
let ⟨a, has, haf⟩ := (hs.diff (to_finite f)).nonempty
in ⟨a, has, λ h, haf $ finset.mem_coe.1 h⟩

lemma not_inj_on_infinite_finite_image {f : α → β} {s : set α}
  (h_inf : s.infinite) (h_fin : (f '' s).finite) :
  ¬ inj_on f s :=
begin
  haveI : finite (f '' s) := finite_coe_iff.mpr h_fin,
  haveI : infinite s := infinite_coe_iff.mpr h_inf,
  have := not_injective_infinite_finite
    ((f '' s).cod_restrict (s.restrict f) $ λ x, ⟨x, x.property, rfl⟩),
  contrapose! this,
  rwa [injective_cod_restrict, ← inj_on_iff_injective],
end

/-! ### Order properties -/

lemma finite_is_top (α : Type*) [partial_order α] : {x : α | is_top x}.finite :=
(subsingleton_is_top α).finite

lemma finite_is_bot (α : Type*) [partial_order α] : {x : α | is_bot x}.finite :=
(subsingleton_is_bot α).finite

theorem infinite.exists_lt_map_eq_of_maps_to [linear_order α] {s : set α} {t : set β} {f : α → β}
  (hs : s.infinite) (hf : maps_to f s t) (ht : t.finite) :
  ∃ (x ∈ s) (y ∈ s), x < y ∧ f x = f y :=
let ⟨x, hx, y, hy, hxy, hf⟩ := hs.exists_ne_map_eq_of_maps_to hf ht
in hxy.lt_or_lt.elim (λ hxy, ⟨x, hx, y, hy, hxy, hf⟩) (λ hyx, ⟨y, hy, x, hx, hyx, hf.symm⟩)

lemma finite.exists_lt_map_eq_of_forall_mem [linear_order α] [infinite α] {t : set β}
  {f : α → β} (hf : ∀ a, f a ∈ t) (ht : t.finite) :
  ∃ a b, a < b ∧ f a = f b :=
begin
  rw ←maps_univ_to at hf,
  obtain ⟨a, -, b, -, h⟩ := (@infinite_univ α _).exists_lt_map_eq_of_maps_to hf ht,
  exact ⟨a, b, h⟩,
end

lemma exists_min_image [linear_order β] (s : set α) (f : α → β) (h1 : s.finite) :
  s.nonempty → ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b
| ⟨x, hx⟩ := by simpa only [exists_prop, finite.mem_to_finset]
  using h1.to_finset.exists_min_image f ⟨x, h1.mem_to_finset.2 hx⟩

lemma exists_max_image [linear_order β] (s : set α) (f : α → β) (h1 : s.finite) :
  s.nonempty → ∃ a ∈ s, ∀ b ∈ s, f b ≤ f a
| ⟨x, hx⟩ := by simpa only [exists_prop, finite.mem_to_finset]
  using h1.to_finset.exists_max_image f ⟨x, h1.mem_to_finset.2 hx⟩

theorem exists_lower_bound_image [hα : nonempty α] [linear_order β] (s : set α) (f : α → β)
  (h : s.finite) : ∃ (a : α), ∀ b ∈ s, f a ≤ f b :=
begin
  by_cases hs : set.nonempty s,
  { exact let ⟨x₀, H, hx₀⟩ := set.exists_min_image s f h hs in ⟨x₀, λ x hx, hx₀ x hx⟩ },
  { exact nonempty.elim hα (λ a, ⟨a, λ x hx, absurd (set.nonempty_of_mem hx) hs⟩) }
end

theorem exists_upper_bound_image [hα : nonempty α] [linear_order β] (s : set α) (f : α → β)
  (h : s.finite) : ∃ (a : α), ∀ b ∈ s, f b ≤ f a :=
begin
  by_cases hs : set.nonempty s,
  { exact let ⟨x₀, H, hx₀⟩ := set.exists_max_image s f h hs in ⟨x₀, λ x hx, hx₀ x hx⟩ },
  { exact nonempty.elim hα (λ a, ⟨a, λ x hx, absurd (set.nonempty_of_mem hx) hs⟩) }
end

lemma finite.supr_binfi_of_monotone {ι ι' α : Type*} [preorder ι'] [nonempty ι']
  [is_directed ι' (≤)] [order.frame α] {s : set ι} (hs : s.finite) {f : ι → ι' → α}
  (hf : ∀ i ∈ s, monotone (f i)) :
  (⨆ j, ⨅ i ∈ s, f i j) = ⨅ i ∈ s, ⨆ j, f i j :=
begin
  revert hf,
  refine hs.induction_on _ _,
  { intro hf, simp [supr_const] },
  { intros a s has hs ihs hf,
    rw [ball_insert_iff] at hf,
    simp only [infi_insert, ← ihs hf.2],
    exact supr_inf_of_monotone hf.1 (λ j₁ j₂ hj, infi₂_mono $ λ i hi, hf.2 i hi hj) }
end

lemma finite.supr_binfi_of_antitone {ι ι' α : Type*} [preorder ι'] [nonempty ι']
  [is_directed ι' (swap (≤))] [order.frame α] {s : set ι} (hs : s.finite) {f : ι → ι' → α}
  (hf : ∀ i ∈ s, antitone (f i)) :
  (⨆ j, ⨅ i ∈ s, f i j) = ⨅ i ∈ s, ⨆ j, f i j :=
@finite.supr_binfi_of_monotone ι ι'ᵒᵈ α _ _ _ _ _ hs _ (λ i hi, (hf i hi).dual_left)

lemma finite.infi_bsupr_of_monotone {ι ι' α : Type*} [preorder ι'] [nonempty ι']
  [is_directed ι' (swap (≤))] [order.coframe α] {s : set ι} (hs : s.finite) {f : ι → ι' → α}
  (hf : ∀ i ∈ s, monotone (f i)) :
  (⨅ j, ⨆ i ∈ s, f i j) = ⨆ i ∈ s, ⨅ j, f i j :=
hs.supr_binfi_of_antitone (λ i hi, (hf i hi).dual_right)

lemma finite.infi_bsupr_of_antitone {ι ι' α : Type*} [preorder ι'] [nonempty ι']
  [is_directed ι' (≤)] [order.coframe α] {s : set ι} (hs : s.finite) {f : ι → ι' → α}
  (hf : ∀ i ∈ s, antitone (f i)) :
  (⨅ j, ⨆ i ∈ s, f i j) = ⨆ i ∈ s, ⨅ j, f i j :=
hs.supr_binfi_of_monotone (λ i hi, (hf i hi).dual_right)

lemma _root_.supr_infi_of_monotone {ι ι' α : Type*} [finite ι] [preorder ι'] [nonempty ι']
  [is_directed ι' (≤)] [order.frame α] {f : ι → ι' → α} (hf : ∀ i, monotone (f i)) :
  (⨆ j, ⨅ i, f i j) = ⨅ i, ⨆ j, f i j :=
by simpa only [infi_univ] using finite_univ.supr_binfi_of_monotone (λ i hi, hf i)

lemma _root_.supr_infi_of_antitone {ι ι' α : Type*} [finite ι] [preorder ι'] [nonempty ι']
  [is_directed ι' (swap (≤))] [order.frame α] {f : ι → ι' → α} (hf : ∀ i, antitone (f i)) :
  (⨆ j, ⨅ i, f i j) = ⨅ i, ⨆ j, f i j :=
@supr_infi_of_monotone ι ι'ᵒᵈ α _ _ _ _ _ _ (λ i, (hf i).dual_left)

lemma _root_.infi_supr_of_monotone {ι ι' α : Type*} [finite ι] [preorder ι'] [nonempty ι']
  [is_directed ι' (swap (≤))] [order.coframe α] {f : ι → ι' → α} (hf : ∀ i, monotone (f i)) :
  (⨅ j, ⨆ i, f i j) = ⨆ i, ⨅ j, f i j :=
supr_infi_of_antitone (λ i, (hf i).dual_right)

lemma _root_.infi_supr_of_antitone {ι ι' α : Type*} [finite ι] [preorder ι'] [nonempty ι']
  [is_directed ι' (≤)] [order.coframe α] {f : ι → ι' → α} (hf : ∀ i, antitone (f i)) :
  (⨅ j, ⨆ i, f i j) = ⨆ i, ⨅ j, f i j :=
supr_infi_of_monotone (λ i, (hf i).dual_right)

/-- An increasing union distributes over finite intersection. -/
lemma Union_Inter_of_monotone {ι ι' α : Type*} [finite ι] [preorder ι'] [is_directed ι' (≤)]
  [nonempty ι'] {s : ι → ι' → set α} (hs : ∀ i, monotone (s i)) :
  (⋃ j : ι', ⋂ i : ι, s i j) = ⋂ i : ι, ⋃ j : ι', s i j :=
supr_infi_of_monotone hs

/-- A decreasing union distributes over finite intersection. -/
lemma Union_Inter_of_antitone {ι ι' α : Type*} [finite ι] [preorder ι'] [is_directed ι' (swap (≤))]
  [nonempty ι'] {s : ι → ι' → set α} (hs : ∀ i, antitone (s i)) :
  (⋃ j : ι', ⋂ i : ι, s i j) = ⋂ i : ι, ⋃ j : ι', s i j :=
supr_infi_of_antitone hs

/-- An increasing intersection distributes over finite union. -/
lemma Inter_Union_of_monotone {ι ι' α : Type*} [finite ι] [preorder ι'] [is_directed ι' (swap (≤))]
  [nonempty ι'] {s : ι → ι' → set α} (hs : ∀ i, monotone (s i)) :
  (⋂ j : ι', ⋃ i : ι, s i j) = ⋃ i : ι, ⋂ j : ι', s i j :=
infi_supr_of_monotone hs

/-- A decreasing intersection distributes over finite union. -/
lemma Inter_Union_of_antitone {ι ι' α : Type*} [finite ι] [preorder ι'] [is_directed ι' (≤)]
  [nonempty ι'] {s : ι → ι' → set α} (hs : ∀ i, antitone (s i)) :
  (⋂ j : ι', ⋃ i : ι, s i j) = ⋃ i : ι, ⋂ j : ι', s i j :=
infi_supr_of_antitone hs

lemma Union_pi_of_monotone {ι ι' : Type*} [linear_order ι'] [nonempty ι'] {α : ι → Type*}
  {I : set ι} {s : Π i, ι' → set (α i)} (hI : I.finite) (hs : ∀ i ∈ I, monotone (s i)) :
  (⋃ j : ι', I.pi (λ i, s i j)) = I.pi (λ i, ⋃ j, s i j) :=
begin
  simp only [pi_def, bInter_eq_Inter, preimage_Union],
  haveI := hI.fintype,
  exact Union_Inter_of_monotone (λ i j₁ j₂ h, preimage_mono $ hs i i.2 h)
end

lemma Union_univ_pi_of_monotone {ι ι' : Type*} [linear_order ι'] [nonempty ι'] [finite ι]
  {α : ι → Type*} {s : Π i, ι' → set (α i)} (hs : ∀ i, monotone (s i)) :
  (⋃ j : ι', pi univ (λ i, s i j)) = pi univ (λ i, ⋃ j, s i j) :=
Union_pi_of_monotone finite_univ (λ i _, hs i)

lemma finite_range_find_greatest {P : α → ℕ → Prop} [∀ x, decidable_pred (P x)] {b : ℕ} :
  (range (λ x, nat.find_greatest (P x) b)).finite :=
(finite_le_nat b).subset $ range_subset_iff.2 $ λ x, nat.find_greatest_le _

lemma finite.exists_maximal_wrt [partial_order β] (f : α → β) (s : set α) (h : set.finite s) :
  s.nonempty → ∃ a ∈ s, ∀ a' ∈ s, f a ≤ f a' → f a = f a' :=
begin
  refine h.induction_on _ _,
  { exact λ h, absurd h not_nonempty_empty },
  intros a s his _ ih _,
  cases s.eq_empty_or_nonempty with h h,
  { use a, simp [h] },
  rcases ih h with ⟨b, hb, ih⟩,
  by_cases f b ≤ f a,
  { refine ⟨a, set.mem_insert _ _, λ c hc hac, le_antisymm hac _⟩,
    rcases set.mem_insert_iff.1 hc with rfl | hcs,
    { refl },
    { rwa [← ih c hcs (le_trans h hac)] } },
  { refine ⟨b, set.mem_insert_of_mem _ hb, λ c hc hbc, _⟩,
    rcases set.mem_insert_iff.1 hc with rfl | hcs,
    { exact (h hbc).elim },
    { exact ih c hcs hbc } }
end

section

variables [semilattice_sup α] [nonempty α] {s : set α}

/--A finite set is bounded above.-/
protected lemma finite.bdd_above (hs : s.finite) : bdd_above s :=
finite.induction_on hs bdd_above_empty $ λ a s _ _ h, h.insert a

/--A finite union of sets which are all bounded above is still bounded above.-/
lemma finite.bdd_above_bUnion {I : set β} {S : β → set α} (H : I.finite) :
  (bdd_above (⋃i∈I, S i)) ↔ (∀i ∈ I, bdd_above (S i)) :=
finite.induction_on H
  (by simp only [bUnion_empty, bdd_above_empty, ball_empty_iff])
  (λ a s ha _ hs, by simp only [bUnion_insert, ball_insert_iff, bdd_above_union, hs])

lemma infinite_of_not_bdd_above : ¬ bdd_above s → s.infinite := mt finite.bdd_above

end

section

variables [semilattice_inf α] [nonempty α] {s : set α}

/--A finite set is bounded below.-/
protected lemma finite.bdd_below (hs : s.finite) : bdd_below s := @finite.bdd_above αᵒᵈ _ _ _ hs

/--A finite union of sets which are all bounded below is still bounded below.-/
lemma finite.bdd_below_bUnion {I : set β} {S : β → set α} (H : I.finite) :
  bdd_below (⋃ i ∈ I, S i) ↔ ∀ i ∈ I, bdd_below (S i) :=
@finite.bdd_above_bUnion αᵒᵈ _ _ _ _ _ H

lemma infinite_of_not_bdd_below : ¬ bdd_below s → s.infinite :=
begin
  contrapose!,
  rw not_infinite,
  apply finite.bdd_below,
end

end

end set

namespace finset

/-- A finset is bounded above. -/
protected lemma bdd_above [semilattice_sup α] [nonempty α] (s : finset α) :
  bdd_above (↑s : set α) :=
s.finite_to_set.bdd_above

/-- A finset is bounded below. -/
protected lemma bdd_below [semilattice_inf α] [nonempty α] (s : finset α) :
  bdd_below (↑s : set α) :=
s.finite_to_set.bdd_below

end finset

variables [linear_order α]

/-- If a linear order does not contain any triple of elements `x < y < z`, then this type
is finite. -/
lemma finite.of_forall_not_lt_lt (h : ∀ ⦃x y z : α⦄, x < y → y < z → false) :
  finite α :=
begin
  nontriviality α,
  rcases exists_pair_ne α with ⟨x, y, hne⟩,
  refine @finite.of_fintype α ⟨{x, y}, λ z , _⟩,
  simpa [hne] using eq_or_eq_or_eq_of_forall_not_lt_lt h z x y
end

/-- If a set `s` does not contain any triple of elements `x < y < z`, then `s` is finite. -/
lemma set.finite_of_forall_not_lt_lt {s : set α} (h : ∀ (x y z ∈ s), x < y → y < z → false) :
  set.finite s :=
@set.to_finite _ s $ finite.of_forall_not_lt_lt $ by simpa only [set_coe.forall'] using h

lemma set.finite_diff_Union_Ioo (s : set α) : (s \ ⋃ (x ∈ s) (y ∈ s), Ioo x y).finite :=
set.finite_of_forall_not_lt_lt $ λ x hx y hy z hz hxy hyz, hy.2 $ mem_Union₂_of_mem hx.1 $
  mem_Union₂_of_mem hz.1 ⟨hxy, hyz⟩

lemma set.finite_diff_Union_Ioo' (s : set α) : (s \ ⋃ x : s × s, Ioo x.1 x.2).finite :=
by simpa only [Union, supr_prod, supr_subtype] using s.finite_diff_Union_Ioo
