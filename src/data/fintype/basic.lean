/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.finset.image

/-!
# Finite types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a typeclass to state that a type is finite.

## Main declarations

* `fintype α`:  Typeclass saying that a type is finite. It takes as fields a `finset` and a proof
  that all terms of type `α` are in it.
* `finset.univ`: The finset of all elements of a fintype.

See `data.fintype.card` for the cardinality of a fintype,
the equivalence with `fin (fintype.card α)`, and pigeonhole principles.

## Instances

Instances for `fintype` for
* `{x // p x}` are in this file as `fintype.subtype`
* `option α` are in `data.fintype.option`
* `α × β` are in `data.fintype.prod`
* `α ⊕ β` are in `data.fintype.sum`
* `Σ (a : α), β a` are in `data.fintype.sigma`

These files also contain appropriate `infinite` instances for these types.

`infinite` instances for `ℕ`, `ℤ`, `multiset α`, and `list α` are in `data.fintype.lattice`.

Types which have a surjection from/an injection to a `fintype` are themselves fintypes.
See `fintype.of_injective` and `fintype.of_surjective`.
-/

open function
open_locale nat

universes u v

variables {α β γ : Type*}

/-- `fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
class fintype (α : Type*) :=
(elems [] : finset α)
(complete : ∀ x : α, x ∈ elems)

namespace finset
variables [fintype α] {s t : finset α}

/-- `univ` is the universal finite set of type `finset α` implied from
  the assumption `fintype α`. -/
def univ : finset α := fintype.elems α

@[simp] theorem mem_univ (x : α) : x ∈ (univ : finset α) :=
fintype.complete x

@[simp] theorem mem_univ_val : ∀ x, x ∈ (univ : finset α).1 := mem_univ

lemma eq_univ_iff_forall : s = univ ↔ ∀ x, x ∈ s := by simp [ext_iff]
lemma eq_univ_of_forall  : (∀ x, x ∈ s) → s = univ := eq_univ_iff_forall.2

@[simp, norm_cast] lemma coe_univ : ↑(univ : finset α) = (set.univ : set α) := by ext; simp
@[simp, norm_cast] lemma coe_eq_univ : (s : set α) = set.univ ↔ s = univ :=
by rw [←coe_univ, coe_inj]

lemma nonempty.eq_univ [subsingleton α] : s.nonempty → s = univ :=
by { rintro ⟨x, hx⟩, refine eq_univ_of_forall (λ y, by rwa subsingleton.elim y x) }

lemma univ_nonempty_iff : (univ : finset α).nonempty ↔ nonempty α :=
by rw [← coe_nonempty, coe_univ, set.nonempty_iff_univ_nonempty]

lemma univ_nonempty [nonempty α] : (univ : finset α).nonempty :=
univ_nonempty_iff.2 ‹_›

lemma univ_eq_empty_iff : (univ : finset α) = ∅ ↔ is_empty α :=
by rw [← not_nonempty_iff, ← univ_nonempty_iff, not_nonempty_iff_eq_empty]

@[simp] lemma univ_eq_empty [is_empty α] : (univ : finset α) = ∅ := univ_eq_empty_iff.2 ‹_›

@[simp] lemma univ_unique [unique α] : (univ : finset α) = {default} :=
finset.ext $ λ x, iff_of_true (mem_univ _) $ mem_singleton.2 $ subsingleton.elim x default

@[simp] theorem subset_univ (s : finset α) : s ⊆ univ := λ a _, mem_univ a

instance : bounded_order (finset α) :=
{ top := univ,
  le_top := subset_univ,
  .. finset.order_bot }

@[simp] lemma top_eq_univ : (⊤ : finset α) = univ := rfl

lemma ssubset_univ_iff {s : finset α} : s ⊂ univ ↔ s ≠ univ := @lt_top_iff_ne_top _ _ _ s

lemma codisjoint_left : codisjoint s t ↔ ∀ ⦃a⦄, a ∉ s → a ∈ t :=
by { classical, simp [codisjoint_iff, eq_univ_iff_forall, or_iff_not_imp_left] }

lemma codisjoint_right : codisjoint s t ↔ ∀ ⦃a⦄, a ∉ t → a ∈ s :=
codisjoint.comm.trans codisjoint_left

section boolean_algebra
variables [decidable_eq α] {a : α}

instance : boolean_algebra (finset α) := generalized_boolean_algebra.to_boolean_algebra

lemma sdiff_eq_inter_compl (s t : finset α) : s \ t = s ∩ tᶜ := sdiff_eq

lemma compl_eq_univ_sdiff (s : finset α) : sᶜ = univ \ s := rfl

@[simp] lemma mem_compl : a ∈ sᶜ ↔ a ∉ s := by simp [compl_eq_univ_sdiff]

lemma not_mem_compl : a ∉ sᶜ ↔ a ∈ s := by rw [mem_compl, not_not]

@[simp, norm_cast] lemma coe_compl (s : finset α) : ↑(sᶜ) = (↑s : set α)ᶜ :=
set.ext $ λ x, mem_compl

@[simp] lemma compl_empty : (∅ : finset α)ᶜ = univ := compl_bot

@[simp] lemma compl_univ : (univ : finset α)ᶜ = ∅ := compl_top

@[simp] lemma compl_eq_empty_iff (s : finset α) : sᶜ = ∅ ↔ s = univ := compl_eq_bot

@[simp] lemma compl_eq_univ_iff (s : finset α) : sᶜ = univ ↔ s = ∅ := compl_eq_top

@[simp] lemma union_compl (s : finset α) : s ∪ sᶜ = univ := sup_compl_eq_top

@[simp] lemma inter_compl (s : finset α) : s ∩ sᶜ = ∅ := inf_compl_eq_bot

@[simp] lemma compl_union (s t : finset α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := compl_sup

@[simp] lemma compl_inter (s t : finset α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := compl_inf

@[simp] lemma compl_erase : (s.erase a)ᶜ = insert a sᶜ :=
by { ext, simp only [or_iff_not_imp_left, mem_insert, not_and, mem_compl, mem_erase] }

@[simp] lemma compl_insert : (insert a s)ᶜ = sᶜ.erase a :=
by { ext, simp only [not_or_distrib, mem_insert, iff_self, mem_compl, mem_erase] }

@[simp] lemma insert_compl_self (x : α) : insert x ({x}ᶜ : finset α) = univ :=
by rw [←compl_erase, erase_singleton, compl_empty]

@[simp] lemma compl_filter (p : α → Prop) [decidable_pred p] [Π x, decidable (¬p x)] :
  (univ.filter p)ᶜ = univ.filter (λ x, ¬p x) :=
(filter_not _ _).symm

lemma compl_ne_univ_iff_nonempty (s : finset α) : sᶜ ≠ univ ↔ s.nonempty :=
by simp [eq_univ_iff_forall, finset.nonempty]

lemma compl_singleton (a : α) : ({a} : finset α)ᶜ = univ.erase a :=
by rw [compl_eq_univ_sdiff, sdiff_singleton_eq_erase]

lemma insert_inj_on' (s : finset α) : set.inj_on (λ a, insert a s) (sᶜ : finset α) :=
by { rw coe_compl, exact s.insert_inj_on }

lemma image_univ_of_surjective [fintype β] {f : β → α} (hf : surjective f) : univ.image f = univ :=
eq_univ_of_forall $ hf.forall.2 $ λ _, mem_image_of_mem _ $ mem_univ _

end boolean_algebra

lemma map_univ_of_surjective [fintype β] {f : β ↪ α} (hf : surjective f) : univ.map f = univ :=
eq_univ_of_forall $ hf.forall.2 $ λ _, mem_map_of_mem _ $ mem_univ _

@[simp] lemma map_univ_equiv [fintype β] (f : β ≃ α) : univ.map f.to_embedding = univ :=
map_univ_of_surjective f.surjective

@[simp] lemma univ_inter [decidable_eq α] (s : finset α) :
  univ ∩ s = s := ext $ λ a, by simp

@[simp] lemma inter_univ [decidable_eq α] (s : finset α) :
  s ∩ univ = s :=
by rw [inter_comm, univ_inter]

@[simp] lemma piecewise_univ [Π i : α, decidable (i ∈ (univ : finset α))]
  {δ : α → Sort*} (f g : Π i, δ i) : univ.piecewise f g = f :=
by { ext i, simp [piecewise] }

lemma piecewise_compl [decidable_eq α] (s : finset α) [Π i : α, decidable (i ∈ s)]
  [Π i : α, decidable (i ∈ sᶜ)] {δ : α → Sort*} (f g : Π i, δ i) :
  sᶜ.piecewise f g = s.piecewise g f :=
by { ext i, simp [piecewise] }

@[simp] lemma piecewise_erase_univ {δ : α → Sort*} [decidable_eq α] (a : α) (f g : Π a, δ a) :
  (finset.univ.erase a).piecewise f g = function.update f a (g a) :=
by rw [←compl_singleton, piecewise_compl, piecewise_singleton]

lemma univ_map_equiv_to_embedding {α β : Type*} [fintype α] [fintype β] (e : α ≃ β) :
  univ.map e.to_embedding = univ :=
eq_univ_iff_forall.mpr (λ b, mem_map.mpr ⟨e.symm b, mem_univ _, by simp⟩)

@[simp] lemma univ_filter_exists (f : α → β) [fintype β]
  [decidable_pred (λ y, ∃ x, f x = y)] [decidable_eq β] :
  finset.univ.filter (λ y, ∃ x, f x = y) = finset.univ.image f :=
by { ext, simp }

/-- Note this is a special case of `(finset.image_preimage f univ _).symm`. -/
lemma univ_filter_mem_range (f : α → β) [fintype β]
  [decidable_pred (λ y, y ∈ set.range f)] [decidable_eq β] :
  finset.univ.filter (λ y, y ∈ set.range f) = finset.univ.image f :=
univ_filter_exists f

lemma coe_filter_univ (p : α → Prop) [decidable_pred p] : (univ.filter p : set α) = {x | p x} :=
by rw [coe_filter, coe_univ, set.sep_univ]

end finset

open finset function

namespace fintype

instance decidable_pi_fintype {α} {β : α → Type*} [∀ a, decidable_eq (β a)] [fintype α] :
  decidable_eq (Π a, β a) :=
λ f g, decidable_of_iff (∀ a ∈ fintype.elems α, f a = g a)
  (by simp [function.funext_iff, fintype.complete])

instance decidable_forall_fintype {p : α → Prop} [decidable_pred p] [fintype α] :
  decidable (∀ a, p a) :=
decidable_of_iff (∀ a ∈ @univ α _, p a) (by simp)

instance decidable_exists_fintype {p : α → Prop} [decidable_pred p] [fintype α] :
  decidable (∃ a, p a) :=
decidable_of_iff (∃ a ∈ @univ α _, p a) (by simp)

instance decidable_mem_range_fintype [fintype α] [decidable_eq β] (f : α → β) :
  decidable_pred (∈ set.range f) :=
λ x, fintype.decidable_exists_fintype

section bundled_homs

instance decidable_eq_equiv_fintype [decidable_eq β] [fintype α] :
  decidable_eq (α ≃ β) :=
λ a b, decidable_of_iff (a.1 = b.1) equiv.coe_fn_injective.eq_iff

instance decidable_eq_embedding_fintype [decidable_eq β] [fintype α] :
  decidable_eq (α ↪ β) :=
λ a b, decidable_of_iff ((a : α → β) = b) function.embedding.coe_injective.eq_iff

@[to_additive]
instance decidable_eq_one_hom_fintype [decidable_eq β] [fintype α] [has_one α] [has_one β]:
  decidable_eq (one_hom α β) :=
λ a b, decidable_of_iff ((a : α → β) = b) (injective.eq_iff one_hom.coe_inj)

@[to_additive]
instance decidable_eq_mul_hom_fintype [decidable_eq β] [fintype α] [has_mul α] [has_mul β]:
  decidable_eq (α →ₙ* β) :=
λ a b, decidable_of_iff ((a : α → β) = b) (injective.eq_iff mul_hom.coe_inj)

@[to_additive]
instance decidable_eq_monoid_hom_fintype [decidable_eq β] [fintype α]
  [mul_one_class α] [mul_one_class β]:
  decidable_eq (α →* β) :=
λ a b, decidable_of_iff ((a : α → β) = b) (injective.eq_iff monoid_hom.coe_inj)

instance decidable_eq_monoid_with_zero_hom_fintype [decidable_eq β] [fintype α]
  [mul_zero_one_class α] [mul_zero_one_class β] :
  decidable_eq (α →*₀ β) :=
λ a b, decidable_of_iff ((a : α → β) = b) (injective.eq_iff monoid_with_zero_hom.coe_inj)

instance decidable_eq_ring_hom_fintype [decidable_eq β] [fintype α]
  [semiring α] [semiring β]:
  decidable_eq (α →+* β) :=
λ a b, decidable_of_iff ((a : α → β) = b) (injective.eq_iff ring_hom.coe_inj)

end bundled_homs

instance decidable_injective_fintype [decidable_eq α] [decidable_eq β] [fintype α] :
  decidable_pred (injective : (α → β) → Prop) := λ x, by unfold injective; apply_instance

instance decidable_surjective_fintype [decidable_eq β] [fintype α] [fintype β] :
  decidable_pred (surjective : (α → β) → Prop) := λ x, by unfold surjective; apply_instance

instance decidable_bijective_fintype [decidable_eq α] [decidable_eq β] [fintype α] [fintype β] :
  decidable_pred (bijective : (α → β) → Prop) := λ x, by unfold bijective; apply_instance

instance decidable_right_inverse_fintype [decidable_eq α] [fintype α] (f : α → β) (g : β → α) :
  decidable (function.right_inverse f g) :=
show decidable (∀ x, g (f x) = x), by apply_instance

instance decidable_left_inverse_fintype [decidable_eq β] [fintype β] (f : α → β) (g : β → α) :
  decidable (function.left_inverse f g) :=
show decidable (∀ x, f (g x) = x), by apply_instance

/-- Construct a proof of `fintype α` from a universal multiset -/
def of_multiset [decidable_eq α] (s : multiset α) (H : ∀ x : α, x ∈ s) :
  fintype α :=
⟨s.to_finset, by simpa using H⟩

/-- Construct a proof of `fintype α` from a universal list -/
def of_list [decidable_eq α] (l : list α) (H : ∀ x : α, x ∈ l) :
  fintype α :=
⟨l.to_finset, by simpa using H⟩

instance (α : Type*) : subsingleton (fintype α) :=
⟨λ ⟨s₁, h₁⟩ ⟨s₂, h₂⟩, by congr; simp [finset.ext_iff, h₁, h₂]⟩

/-- Given a predicate that can be represented by a finset, the subtype
associated to the predicate is a fintype. -/
protected def subtype {p : α → Prop} (s : finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
  fintype {x // p x} :=
⟨⟨s.1.pmap subtype.mk (λ x, (H x).1),
  s.nodup.pmap $ λ a _ b _, congr_arg subtype.val⟩,
λ ⟨x, px⟩, multiset.mem_pmap.2 ⟨x, (H x).2 px, rfl⟩⟩

/-- Construct a fintype from a finset with the same elements. -/
def of_finset {p : set α} (s : finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : fintype p :=
fintype.subtype s H

/-- If `f : α → β` is a bijection and `α` is a fintype, then `β` is also a fintype. -/
def of_bijective [fintype α] (f : α → β) (H : function.bijective f) : fintype β :=
⟨univ.map ⟨f, H.1⟩,
λ b, let ⟨a, e⟩ := H.2 b in e ▸ mem_map_of_mem _ (mem_univ _)⟩

/-- If `f : α → β` is a surjection and `α` is a fintype, then `β` is also a fintype. -/
def of_surjective [decidable_eq β] [fintype α] (f : α → β) (H : function.surjective f) :
  fintype β :=
⟨univ.image f, λ b, let ⟨a, e⟩ := H b in e ▸ mem_image_of_mem _ (mem_univ _)⟩

end fintype

namespace finset
variables [fintype α] [decidable_eq α] {s t : finset α}

instance decidable_codisjoint : decidable (codisjoint s t) :=
decidable_of_iff _ codisjoint_left.symm

instance decidable_is_compl : decidable (is_compl s t) := decidable_of_iff' _ is_compl_iff

end finset

section inv

namespace function

variables [fintype α] [decidable_eq β]

namespace injective

variables {f : α → β} (hf : function.injective f)

/--
The inverse of an `hf : injective` function `f : α → β`, of the type `↥(set.range f) → α`.
This is the computable version of `function.inv_fun` that requires `fintype α` and `decidable_eq β`,
or the function version of applying `(equiv.of_injective f hf).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = fintype.card α`.
-/
def inv_of_mem_range : set.range f → α :=
λ b, finset.choose (λ a, f a = b) finset.univ ((exists_unique_congr (by simp)).mp
  (hf.exists_unique_of_mem_range b.property))

lemma left_inv_of_inv_of_mem_range (b : set.range f) :
  f (hf.inv_of_mem_range b) = b :=
(finset.choose_spec (λ a, f a = b) _ _).right

@[simp] lemma right_inv_of_inv_of_mem_range (a : α) :
  hf.inv_of_mem_range (⟨f a, set.mem_range_self a⟩) = a :=
hf (finset.choose_spec (λ a', f a' = f a) _ _).right

lemma inv_fun_restrict [nonempty α] :
  (set.range f).restrict (inv_fun f) = hf.inv_of_mem_range :=
begin
  ext ⟨b, h⟩,
  apply hf,
  simp [hf.left_inv_of_inv_of_mem_range, @inv_fun_eq _ _ _ f b (set.mem_range.mp h)]
end

lemma inv_of_mem_range_surjective : function.surjective hf.inv_of_mem_range :=
λ a, ⟨⟨f a, set.mem_range_self a⟩, by simp⟩

end injective

namespace embedding
variables (f : α ↪ β) (b : set.range f)

/--
The inverse of an embedding `f : α ↪ β`, of the type `↥(set.range f) → α`.
This is the computable version of `function.inv_fun` that requires `fintype α` and `decidable_eq β`,
or the function version of applying `(equiv.of_injective f f.injective).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = fintype.card α`.
-/
def inv_of_mem_range : α :=
f.injective.inv_of_mem_range b

@[simp] lemma left_inv_of_inv_of_mem_range :
  f (f.inv_of_mem_range b) = b :=
f.injective.left_inv_of_inv_of_mem_range b

@[simp] lemma right_inv_of_inv_of_mem_range (a : α) :
  f.inv_of_mem_range ⟨f a, set.mem_range_self a⟩ = a :=
f.injective.right_inv_of_inv_of_mem_range a

lemma inv_fun_restrict [nonempty α] :
  (set.range f).restrict (inv_fun f) = f.inv_of_mem_range :=
begin
  ext ⟨b, h⟩,
  apply f.injective,
  simp [f.left_inv_of_inv_of_mem_range, @inv_fun_eq _ _ _ f b (set.mem_range.mp h)]
end

lemma inv_of_mem_range_surjective : function.surjective f.inv_of_mem_range :=
λ a, ⟨⟨f a, set.mem_range_self a⟩, by simp⟩

end embedding

end function

end inv

namespace fintype

/-- Given an injective function to a fintype, the domain is also a
fintype. This is noncomputable because injectivity alone cannot be
used to construct preimages. -/
noncomputable def of_injective [fintype β] (f : α → β) (H : function.injective f) : fintype α :=
by letI := classical.dec; exact
if hα : nonempty α then by letI := classical.inhabited_of_nonempty hα;
  exact of_surjective (inv_fun f) (inv_fun_surjective H)
else ⟨∅, λ x, (hα ⟨x⟩).elim⟩

/-- If `f : α ≃ β` and `α` is a fintype, then `β` is also a fintype. -/
def of_equiv (α : Type*) [fintype α] (f : α ≃ β) : fintype β := of_bijective _ f.bijective

/-- Any subsingleton type with a witness is a fintype (with one term). -/
def of_subsingleton (a : α) [subsingleton α] : fintype α :=
⟨{a}, λ b, finset.mem_singleton.2 (subsingleton.elim _ _)⟩

@[simp] theorem univ_of_subsingleton (a : α) [subsingleton α] :
  @univ _ (of_subsingleton a) = {a} := rfl

@[priority 100] -- see Note [lower instance priority]
instance of_is_empty [is_empty α] : fintype α := ⟨∅, is_empty_elim⟩

/-- Note: this lemma is specifically about `fintype.of_is_empty`. For a statement about
arbitrary `fintype` instances, use `finset.univ_eq_empty`. -/
-- no-lint since while `finset.univ_eq_empty` can prove this, it isn't applicable for `dsimp`.
@[simp, nolint simp_nf] theorem univ_of_is_empty [is_empty α] : @univ α _ = ∅ := rfl

end fintype

namespace set
variables {s t : set α}

/-- Construct a finset enumerating a set `s`, given a `fintype` instance.  -/
def to_finset (s : set α) [fintype s] : finset α :=
(@finset.univ s _).map $ function.embedding.subtype _

@[congr]
lemma to_finset_congr {s t : set α} [fintype s] [fintype t] (h : s = t) :
  to_finset s = to_finset t :=
by cc

@[simp] theorem mem_to_finset {s : set α} [fintype s] {a : α} : a ∈ s.to_finset ↔ a ∈ s :=
by simp [to_finset]

/-- Many `fintype` instances for sets are defined using an extensionally equal `finset`.
Rewriting `s.to_finset` with `set.to_finset_of_finset` replaces the term with such a `finset`. -/
theorem to_finset_of_finset {p : set α} (s : finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) :
  @set.to_finset _ p (fintype.of_finset s H) = s :=
finset.ext (λ x, by rw [mem_to_finset, H])

/-- Membership of a set with a `fintype` instance is decidable.

Using this as an instance leads to potential loops with `subtype.fintype` under certain decidability
assumptions, so it should only be declared a local instance. -/
def decidable_mem_of_fintype [decidable_eq α] (s : set α) [fintype s] (a) : decidable (a ∈ s) :=
decidable_of_iff _ mem_to_finset

@[simp] theorem coe_to_finset (s : set α) [fintype s] : (↑s.to_finset : set α) = s :=
set.ext $ λ _, mem_to_finset

@[simp] lemma to_finset_nonempty {s : set α} [fintype s] : s.to_finset.nonempty ↔ s.nonempty :=
by rw [←finset.coe_nonempty, coe_to_finset]

@[simp] theorem to_finset_inj {s t : set α} [fintype s] [fintype t] :
  s.to_finset = t.to_finset ↔ s = t :=
⟨λ h, by rw [←s.coe_to_finset, h, t.coe_to_finset], λ h, by simp [h]; congr⟩

@[mono]
lemma to_finset_subset_to_finset [fintype s] [fintype t] : s.to_finset ⊆ t.to_finset ↔ s ⊆ t :=
by simp [finset.subset_iff, set.subset_def]

@[simp] lemma to_finset_ssubset [fintype s] {t : finset α} : s.to_finset ⊂ t ↔ s ⊂ t :=
by rw [←finset.coe_ssubset, coe_to_finset]

@[simp] lemma subset_to_finset {s : finset α} [fintype t] : s ⊆ t.to_finset ↔ ↑s ⊆ t :=
by rw [←finset.coe_subset, coe_to_finset]

@[simp] lemma ssubset_to_finset {s : finset α} [fintype t] : s ⊂ t.to_finset ↔ ↑s ⊂ t :=
by rw [←finset.coe_ssubset, coe_to_finset]

@[mono]
lemma to_finset_ssubset_to_finset [fintype s] [fintype t] : s.to_finset ⊂ t.to_finset ↔ s ⊂ t :=
by simp only [finset.ssubset_def, to_finset_subset_to_finset, ssubset_def]

@[simp] lemma to_finset_subset [fintype s] {t : finset α} : s.to_finset ⊆ t ↔ s ⊆ t :=
by rw [←finset.coe_subset, coe_to_finset]

alias to_finset_subset_to_finset ↔ _ to_finset_mono
alias to_finset_ssubset_to_finset ↔ _ to_finset_strict_mono

@[simp] lemma disjoint_to_finset [fintype s] [fintype t] :
  disjoint s.to_finset t.to_finset ↔ disjoint s t :=
by simp only [←disjoint_coe, coe_to_finset]

section decidable_eq
variables [decidable_eq α] (s t) [fintype s] [fintype t]

@[simp] lemma to_finset_inter [fintype ↥(s ∩ t)] : (s ∩ t).to_finset = s.to_finset ∩ t.to_finset :=
by { ext, simp }

@[simp] lemma to_finset_union [fintype ↥(s ∪ t)] : (s ∪ t).to_finset = s.to_finset ∪ t.to_finset :=
by { ext, simp }

@[simp] lemma to_finset_diff [fintype ↥(s \ t)] : (s \ t).to_finset = s.to_finset \ t.to_finset :=
by { ext, simp }

@[simp] lemma to_finset_symm_diff [fintype ↥(s ∆ t)] :
  (s ∆ t).to_finset = s.to_finset ∆ t.to_finset :=
by { ext, simp [mem_symm_diff, finset.mem_symm_diff] }

@[simp] lemma to_finset_compl [fintype α] [fintype ↥sᶜ] : sᶜ.to_finset = s.to_finsetᶜ :=
by { ext, simp }

end decidable_eq

/- TODO The `↥` circumvents an elaboration bug. See comment on `set.to_finset_univ`. -/
@[simp] lemma to_finset_empty [fintype ↥(∅ : set α)] : (∅ : set α).to_finset = ∅ := by { ext, simp }

/- TODO Without the coercion arrow (`↥`) there is an elaboration bug in the following two;
it essentially infers `fintype.{v} (set.univ.{u} : set α)` with `v` and `u` distinct.
Reported in leanprover-community/lean#672 -/
@[simp] lemma to_finset_univ [fintype α] [fintype ↥(set.univ : set α)] :
  (set.univ : set α).to_finset = finset.univ :=
by { ext, simp }

@[simp] lemma to_finset_eq_empty [fintype s] : s.to_finset = ∅ ↔ s = ∅ :=
by rw [←to_finset_empty, to_finset_inj]

@[simp] lemma to_finset_eq_univ [fintype α] [fintype s] : s.to_finset = finset.univ ↔ s = univ :=
by rw [← coe_inj, coe_to_finset, coe_univ]

@[simp] lemma to_finset_set_of [fintype α] (p : α → Prop) [decidable_pred p] [fintype {x | p x}] :
  {x | p x}.to_finset = finset.univ.filter p :=
by { ext, simp }

@[simp] lemma to_finset_ssubset_univ [fintype α] {s : set α} [fintype s] :
  s.to_finset ⊂ finset.univ ↔ s ⊂ univ :=
by rw [← coe_ssubset, coe_to_finset, coe_univ]

@[simp]
lemma to_finset_image [decidable_eq β] (f : α → β) (s : set α) [fintype s] [fintype (f '' s)] :
  (f '' s).to_finset = s.to_finset.image f :=
finset.coe_injective $ by simp

@[simp] lemma to_finset_range [decidable_eq α] [fintype β] (f : β → α) [fintype (set.range f)] :
  (set.range f).to_finset = finset.univ.image f :=
by { ext, simp }

/- TODO The `↥` circumvents an elaboration bug. See comment on `set.to_finset_univ`. -/
lemma to_finset_singleton (a : α) [fintype ↥({a} : set α)] : ({a} : set α).to_finset = {a} :=
by { ext, simp }

/- TODO The `↥` circumvents an elaboration bug. See comment on `set.to_finset_univ`. -/
@[simp] lemma to_finset_insert [decidable_eq α] {a : α} {s : set α}
  [fintype ↥(insert a s : set α)] [fintype s] :
  (insert a s).to_finset = insert a s.to_finset :=
by { ext, simp }

lemma filter_mem_univ_eq_to_finset [fintype α] (s : set α) [fintype s] [decidable_pred (∈ s)] :
  finset.univ.filter (∈ s) = s.to_finset :=
by { ext, simp only [mem_filter, finset.mem_univ, true_and, mem_to_finset] }

end set

@[simp] lemma finset.to_finset_coe (s : finset α) [fintype ↥(s : set α)] :
  (s : set α).to_finset = s :=
ext $ λ _, set.mem_to_finset

instance (n : ℕ) : fintype (fin n) :=
⟨⟨list.fin_range n, list.nodup_fin_range n⟩, list.mem_fin_range⟩

lemma fin.univ_def (n : ℕ) : (univ : finset (fin n)) = ⟨list.fin_range n, list.nodup_fin_range n⟩ :=
rfl

@[simp] lemma fin.image_succ_above_univ {n : ℕ} (i : fin (n + 1)) :
  univ.image i.succ_above = {i}ᶜ :=
by { ext m, simp }

@[simp] lemma fin.image_succ_univ (n : ℕ) : (univ : finset (fin n)).image fin.succ = {0}ᶜ :=
by rw [← fin.succ_above_zero, fin.image_succ_above_univ]

@[simp] lemma fin.image_cast_succ (n : ℕ) :
  (univ : finset (fin n)).image fin.cast_succ = {fin.last n}ᶜ :=
by rw [← fin.succ_above_last, fin.image_succ_above_univ]

/- The following three lemmas use `finset.cons` instead of `insert` and `finset.map` instead of
`finset.image` to reduce proof obligations downstream. -/

/-- Embed `fin n` into `fin (n + 1)` by prepending zero to the `univ` -/
lemma fin.univ_succ (n : ℕ) :
  (univ : finset (fin (n + 1))) =
    cons 0 (univ.map ⟨fin.succ, fin.succ_injective _⟩) (by simp [map_eq_image]) :=
by simp [map_eq_image]

/-- Embed `fin n` into `fin (n + 1)` by appending a new `fin.last n` to the `univ` -/
lemma fin.univ_cast_succ (n : ℕ) :
  (univ : finset (fin (n + 1))) =
    cons (fin.last n) (univ.map fin.cast_succ.to_embedding) (by simp [map_eq_image]) :=
by simp [map_eq_image]

/-- Embed `fin n` into `fin (n + 1)` by inserting
around a specified pivot `p : fin (n + 1)` into the `univ` -/
lemma fin.univ_succ_above (n : ℕ) (p : fin (n + 1)) :
  (univ : finset (fin (n + 1))) = cons p (univ.map $ (fin.succ_above p).to_embedding) (by simp) :=
by simp [map_eq_image]

@[instance, priority 10] def unique.fintype {α : Type*} [unique α] : fintype α :=
fintype.of_subsingleton default

/-- Short-circuit instance to decrease search for `unique.fintype`,
since that relies on a subsingleton elimination for `unique`. -/
instance fintype.subtype_eq (y : α) : fintype {x // x = y} :=
fintype.subtype {y} (by simp)

/-- Short-circuit instance to decrease search for `unique.fintype`,
since that relies on a subsingleton elimination for `unique`. -/
instance fintype.subtype_eq' (y : α) : fintype {x // y = x} :=
fintype.subtype {y} (by simp [eq_comm])

@[simp] theorem fintype.univ_empty : @univ empty _ = ∅ := rfl

@[simp] theorem fintype.univ_pempty : @univ pempty _ = ∅ := rfl

instance : fintype unit := fintype.of_subsingleton ()

theorem fintype.univ_unit : @univ unit _ = {()} := rfl

instance : fintype punit := fintype.of_subsingleton punit.star

@[simp] theorem fintype.univ_punit : @univ punit _ = {punit.star} := rfl

instance : fintype bool := ⟨⟨{tt, ff}, by simp⟩, λ x, by cases x; simp⟩

@[simp] theorem fintype.univ_bool : @univ bool _ = {tt, ff} := rfl

instance additive.fintype : Π [fintype α], fintype (additive α) := id

instance multiplicative.fintype : Π [fintype α], fintype (multiplicative α) := id

/-- Given that `α × β` is a fintype, `α` is also a fintype. -/
def fintype.prod_left {α β} [decidable_eq α] [fintype (α × β)] [nonempty β] : fintype α :=
⟨(fintype.elems (α × β)).image prod.fst,
  λ a, let ⟨b⟩ := ‹nonempty β› in by simp; exact ⟨b, fintype.complete _⟩⟩

/-- Given that `α × β` is a fintype, `β` is also a fintype. -/
def fintype.prod_right {α β} [decidable_eq β] [fintype (α × β)] [nonempty α] : fintype β :=
⟨(fintype.elems (α × β)).image prod.snd,
  λ b, let ⟨a⟩ := ‹nonempty α› in by simp; exact ⟨a, fintype.complete _⟩⟩

instance (α : Type*) [fintype α] : fintype (ulift α) :=
fintype.of_equiv _ equiv.ulift.symm

instance (α : Type*) [fintype α] : fintype (plift α) :=
fintype.of_equiv _ equiv.plift.symm

instance (α : Type*) [fintype α] : fintype αᵒᵈ := ‹fintype α›
instance (α : Type*) [finite α] : finite αᵒᵈ := ‹finite α›

instance (α : Type*) [fintype α] : fintype (lex α) := ‹fintype α›

section finset

/-! ### `fintype (s : finset α)` -/

instance finset.fintype_coe_sort {α : Type u} (s : finset α) : fintype s :=
⟨s.attach, s.mem_attach⟩

@[simp] lemma finset.univ_eq_attach {α : Type u} (s : finset α) :
  (univ : finset s) = s.attach :=
rfl

end finset

lemma fintype.coe_image_univ [fintype α] [decidable_eq β] {f : α → β} :
  ↑(finset.image f finset.univ) = set.range f :=
by { ext x, simp }

instance list.subtype.fintype [decidable_eq α] (l : list α) : fintype {x // x ∈ l} :=
fintype.of_list l.attach l.mem_attach

instance multiset.subtype.fintype [decidable_eq α] (s : multiset α) : fintype {x // x ∈ s} :=
fintype.of_multiset s.attach s.mem_attach

instance finset.subtype.fintype (s : finset α) : fintype {x // x ∈ s} :=
⟨s.attach, s.mem_attach⟩

instance finset_coe.fintype (s : finset α) : fintype (↑s : set α) :=
finset.subtype.fintype s

lemma finset.attach_eq_univ {s : finset α} : s.attach = finset.univ := rfl

instance plift.fintype_Prop (p : Prop) [decidable p] : fintype (plift p) :=
⟨if h : p then {⟨h⟩} else ∅, λ ⟨h⟩, by simp [h]⟩

instance Prop.fintype : fintype Prop :=
⟨⟨{true, false}, by simp [true_ne_false]⟩, classical.cases (by simp) (by simp)⟩

@[simp] lemma fintype.univ_Prop : (finset.univ : finset Prop) = {true, false} :=
finset.eq_of_veq $ by simp; refl

instance subtype.fintype (p : α → Prop) [decidable_pred p] [fintype α] : fintype {x // p x} :=
fintype.subtype (univ.filter p) (by simp)

/-- A set on a fintype, when coerced to a type, is a fintype. -/
def set_fintype [fintype α] (s : set α) [decidable_pred (∈ s)] : fintype s :=
subtype.fintype (λ x, x ∈ s)

section
variables (α)

/-- The `αˣ` type is equivalent to a subtype of `α × α`. -/
@[simps]
def _root_.units_equiv_prod_subtype [monoid α] :
  αˣ ≃ {p : α × α // p.1 * p.2 = 1 ∧ p.2 * p.1 = 1} :=
{ to_fun := λ u, ⟨(u, ↑u⁻¹), u.val_inv, u.inv_val⟩,
  inv_fun := λ p, units.mk (p : α × α).1 (p : α × α).2 p.prop.1 p.prop.2,
  left_inv := λ u, units.ext rfl,
  right_inv := λ p, subtype.ext $ prod.ext rfl rfl}

/-- In a `group_with_zero` `α`, the unit group `αˣ` is equivalent to the subtype of nonzero
elements. -/
@[simps]
def _root_.units_equiv_ne_zero [group_with_zero α] : αˣ ≃ {a : α // a ≠ 0} :=
⟨λ a, ⟨a, a.ne_zero⟩, λ a, units.mk0 _ a.prop, λ _, units.ext rfl, λ _, subtype.ext rfl⟩

end

namespace fintype

/-- Given `fintype α`, `finset_equiv_set` is the equiv between `finset α` and `set α`. (All
sets on a finite type are finite.) -/
noncomputable def finset_equiv_set [fintype α] : finset α ≃ set α :=
{ to_fun := coe,
  inv_fun := by { classical, exact λ s, s.to_finset },
  left_inv := λ s, by convert finset.to_finset_coe s,
  right_inv := λ s, by { classical, exact s.coe_to_finset } }

@[simp] lemma finset_equiv_set_apply [fintype α] (s : finset α) : finset_equiv_set s = s := rfl

@[simp] lemma finset_equiv_set_symm_apply [fintype α] (s : set α) [fintype s] :
  finset_equiv_set.symm s = s.to_finset :=
by convert rfl

end fintype

instance quotient.fintype [fintype α] (s : setoid α)
  [decidable_rel ((≈) : α → α → Prop)] : fintype (quotient s) :=
fintype.of_surjective quotient.mk (λ x, quotient.induction_on x (λ x, ⟨x, rfl⟩))

instance psigma.fintype_prop_left {α : Prop} {β : α → Type*} [decidable α] [∀ a, fintype (β a)] :
  fintype (Σ' a, β a) :=
if h : α then fintype.of_equiv (β h) ⟨λ x, ⟨h, x⟩, psigma.snd, λ _, rfl, λ ⟨_, _⟩, rfl⟩
else ⟨∅, λ x, h x.1⟩

instance psigma.fintype_prop_right {α : Type*} {β : α → Prop} [∀ a, decidable (β a)] [fintype α] :
  fintype (Σ' a, β a) :=
fintype.of_equiv {a // β a} ⟨λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, rfl, λ ⟨x, y⟩, rfl⟩

instance psigma.fintype_prop_prop {α : Prop} {β : α → Prop} [decidable α] [∀ a, decidable (β a)] :
  fintype (Σ' a, β a) :=
if h : ∃ a, β a then ⟨{⟨h.fst, h.snd⟩}, λ ⟨_, _⟩, by simp⟩ else ⟨∅, λ ⟨x, y⟩, h ⟨x, y⟩⟩

instance pfun_fintype (p : Prop) [decidable p] (α : p → Type*)
  [Π hp, fintype (α hp)] : fintype (Π hp : p, α hp) :=
if hp : p then fintype.of_equiv (α hp) ⟨λ a _, a, λ f, f hp, λ _, rfl, λ _, rfl⟩
          else ⟨singleton (λ h, (hp h).elim), by simp [hp, function.funext_iff]⟩

lemma mem_image_univ_iff_mem_range
  {α β : Type*} [fintype α] [decidable_eq β] {f : α → β} {b : β} :
  b ∈ univ.image f ↔ b ∈ set.range f :=
by simp

namespace fintype

section choose
open fintype equiv

variables [fintype α] (p : α → Prop) [decidable_pred p]

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def choose_x (hp : ∃! a : α, p a) : {a // p a} :=
⟨finset.choose p univ (by simp; exact hp), finset.choose_property _ _ _⟩

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of `α`. -/
def choose (hp : ∃! a, p a) : α := choose_x p hp

lemma choose_spec (hp : ∃! a, p a) : p (choose p hp) :=
(choose_x p hp).property

@[simp] lemma choose_subtype_eq {α : Type*} (p : α → Prop) [fintype {a : α // p a}]
  [decidable_eq α] (x : {a : α // p a})
  (h : ∃! (a : {a // p a}), (a : α) = x := ⟨x, rfl, λ y hy, by simpa [subtype.ext_iff] using hy⟩) :
  fintype.choose (λ (y : {a : α // p a}), (y : α) = x) h = x :=
by rw [subtype.ext_iff, fintype.choose_spec (λ (y : {a : α // p a}), (y : α) = x) _]

end choose

section bijection_inverse
open function

variables [fintype α] [decidable_eq β] {f : α → β}

/--
`bij_inv f` is the unique inverse to a bijection `f`. This acts
  as a computable alternative to `function.inv_fun`. -/
def bij_inv (f_bij : bijective f) (b : β) : α :=
fintype.choose (λ a, f a = b)
begin
  rcases f_bij.right b with ⟨a', fa_eq_b⟩,
  rw ← fa_eq_b,
  exact ⟨a', ⟨rfl, (λ a h, f_bij.left h)⟩⟩
end

lemma left_inverse_bij_inv (f_bij : bijective f) : left_inverse (bij_inv f_bij) f :=
λ a, f_bij.left (choose_spec (λ a', f a' = f a) _)

lemma right_inverse_bij_inv (f_bij : bijective f) : right_inverse (bij_inv f_bij) f :=
λ b, choose_spec (λ a', f a' = b) _

lemma bijective_bij_inv (f_bij : bijective f) : bijective (bij_inv f_bij) :=
⟨(right_inverse_bij_inv _).injective, (left_inverse_bij_inv _).surjective⟩

end bijection_inverse
end fintype

section trunc

/--
For `s : multiset α`, we can lift the existential statement that `∃ x, x ∈ s` to a `trunc α`.
-/
def trunc_of_multiset_exists_mem {α} (s : multiset α) : (∃ x, x ∈ s) → trunc α :=
quotient.rec_on_subsingleton s $ λ l h,
  match l, h with
    | [],       _ := false.elim (by tauto)
    | (a :: _), _ := trunc.mk a
  end

/--
A `nonempty` `fintype` constructively contains an element.
-/
def trunc_of_nonempty_fintype (α) [nonempty α] [fintype α] : trunc α :=
trunc_of_multiset_exists_mem finset.univ.val (by simp)

/--
By iterating over the elements of a fintype, we can lift an existential statement `∃ a, P a`
to `trunc (Σ' a, P a)`, containing data.
-/
def trunc_sigma_of_exists {α} [fintype α] {P : α → Prop} [decidable_pred P] (h : ∃ a, P a) :
  trunc (Σ' a, P a) :=
@trunc_of_nonempty_fintype (Σ' a, P a) (exists.elim h $ λ a ha, ⟨⟨a, ha⟩⟩) _

end trunc

namespace multiset

variables [fintype α] [decidable_eq α]

@[simp] lemma count_univ (a : α) :
  count a finset.univ.val = 1 :=
count_eq_one_of_mem finset.univ.nodup (finset.mem_univ _)

end multiset

/-- Auxiliary definition to show `exists_seq_of_forall_finset_exists`. -/
noncomputable def seq_of_forall_finset_exists_aux
  {α : Type*} [decidable_eq α] (P : α → Prop) (r : α → α → Prop)
  (h : ∀ (s : finset α), ∃ y, (∀ x ∈ s, P x) → (P y ∧ (∀ x ∈ s, r x y))) : ℕ → α
| n := classical.some (h (finset.image (λ (i : fin n), seq_of_forall_finset_exists_aux i)
        (finset.univ : finset (fin n))))
using_well_founded {dec_tac := `[exact i.2]}

/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m < n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
lemma exists_seq_of_forall_finset_exists {α : Type*} (P : α → Prop) (r : α → α → Prop)
  (h : ∀ (s : finset α), (∀ x ∈ s, P x) → ∃ y, P y ∧ (∀ x ∈ s, r x y)) :
  ∃ (f : ℕ → α), (∀ n, P (f n)) ∧ (∀ m n, m < n → r (f m) (f n)) :=
begin
  classical,
  haveI : nonempty α,
  { rcases h ∅ (by simp) with ⟨y, hy⟩,
    exact ⟨y⟩ },
  choose! F hF using h,
  have h' : ∀ (s : finset α), ∃ y, (∀ x ∈ s, P x) → (P y ∧ (∀ x ∈ s, r x y)) := λ s, ⟨F s, hF s⟩,
  set f := seq_of_forall_finset_exists_aux P r h' with hf,
  have A : ∀ (n : ℕ), P (f n),
  { assume n,
    induction n using nat.strong_induction_on with n IH,
    have IH' : ∀ (x : fin n), P (f x) := λ n, IH n.1 n.2,
    rw [hf, seq_of_forall_finset_exists_aux],
    exact (classical.some_spec (h' (finset.image (λ (i : fin n), f i)
      (finset.univ : finset (fin n)))) (by simp [IH'])).1 },
  refine ⟨f, A, λ m n hmn, _⟩,
  nth_rewrite 1 hf,
  rw seq_of_forall_finset_exists_aux,
  apply (classical.some_spec (h' (finset.image (λ (i : fin n), f i)
    (finset.univ : finset (fin n)))) (by simp [A])).2,
  exact finset.mem_image.2 ⟨⟨m, hmn⟩, finset.mem_univ _, rfl⟩,
end

/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
symmetric relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m ≠ n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
lemma exists_seq_of_forall_finset_exists' {α : Type*} (P : α → Prop) (r : α → α → Prop)
  [is_symm α r]
  (h : ∀ (s : finset α), (∀ x ∈ s, P x) → ∃ y, P y ∧ (∀ x ∈ s, r x y)) :
  ∃ (f : ℕ → α), (∀ n, P (f n)) ∧ (∀ m n, m ≠ n → r (f m) (f n)) :=
begin
  rcases exists_seq_of_forall_finset_exists P r h with ⟨f, hf, hf'⟩,
  refine ⟨f, hf, λ m n hmn, _⟩,
  rcases lt_trichotomy m n with h|rfl|h,
  { exact hf' m n h },
  { exact (hmn rfl).elim },
  { apply symm,
    exact hf' n m h }
end
