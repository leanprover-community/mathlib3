/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import data.finite.basic
import data.set.finite

/-!
# Finite instances for `set`

This module provides ways to go between `set.finite` and `finite` and also provides a number
of `finite` instances for basic set constructions such as unions, intersections, and so on.

## Main definitions

* `set.finite_of_finite` creates a `set.finite` proof from a `finite` instance
* `set.finite.finite` creates a `finite` instance from a `set.finite` proof
* `finite.set.subset` for finiteness of subsets of a finite set

## Tags

finiteness, finite sets

-/

open set
open_locale classical

universes u v w x
variables {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

/-- Constructor for `set.finite` using a `finite` instance. -/
theorem set.finite_of_finite (s : set α) [finite s] : s.finite := ⟨fintype.of_finite s⟩

/-- Projection of `set.finite` to its `finite` instance.
This is intended to be used with dot notation.
See also `set.finite.fintype`. -/
@[nolint dup_namespace]
protected lemma set.finite.finite {s : set α} (h : s.finite) : finite s :=
finite.of_fintype h.fintype

lemma set.finite_iff_finite {s : set α} : s.finite ↔ finite s :=
⟨λ h, h.finite, λ h, by exactI set.finite_of_finite s⟩

/-- Construct a `finite` instance for a `set` from a `finset` with the same elements. -/
protected lemma finite.of_finset {p : set α} (s : finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : finite p :=
finite.of_fintype (fintype.of_finset s H)

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `fintype` instances
in `data.set.finite`. While every `fintype` instance gives a `finite` instance, those
instances that depend on `fintype` or `decidable` instances need an additional `finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`subtype.finite` for subsets of a finite type.
-/

namespace finite.set

instance finite_union (s t : set α) [finite s] [finite t] :
  finite (s ∪ t : set α) :=
by { haveI := fintype.of_finite s, haveI := fintype.of_finite t, apply_instance }

instance finite_sep (s : set α) (p : α → Prop) [finite s] :
  finite ({a ∈ s | p a} : set α) :=
by { haveI := fintype.of_finite s, apply_instance }

protected lemma subset (s : set α) {t : set α} [finite s] (h : t ⊆ s) : finite t :=
by { rw eq_sep_of_subset h, apply_instance }

instance finite_inter_of_right (s t : set α) [finite t] :
  finite (s ∩ t : set α) := finite.set.subset t (inter_subset_right s t)

instance finite_inter_of_left (s t : set α) [finite s] :
  finite (s ∩ t : set α) := finite.set.subset s (inter_subset_left s t)

instance finite_diff (s t : set α) [finite s] :
  finite (s \ t : set α) := finite.set.subset s (diff_subset s t)

instance finite_Union [finite ι] (f : ι → set α) [∀ i, finite (f i)] : finite (⋃ i, f i) :=
begin
  convert_to finite (⋃ (i : plift ι), f i.down),
  { congr, ext, simp },
  haveI := fintype.of_finite (plift ι),
  haveI := λ i, fintype.of_finite (f i),
  apply_instance,
end

instance finite_sUnion {s : set (set α)} [finite s] [H : ∀ (t : s), finite (t : set α)] :
  finite (⋃₀ s) :=
by { rw sUnion_eq_Union, exact @finite.set.finite_Union _ _ _ _ H }

lemma finite_bUnion {ι : Type*} (s : set ι) [finite s] (t : ι → set α) (H : ∀ i ∈ s, finite (t i)) :
  finite (⋃(x ∈ s), t x) :=
begin
  convert_to finite (⋃ (x : s), t x),
  { congr' 1, ext, simp },
  haveI : ∀ (i : s), finite (t i) := λ i, H i i.property,
  apply_instance,
end

instance finite_bUnion' {ι : Type*} (s : set ι) [finite s] (t : ι → set α) [∀ i, finite (t i)] :
  finite (⋃(x ∈ s), t x) :=
finite_bUnion s t (λ i h, infer_instance)

instance finite_Inter {ι : Sort*} [nonempty ι] (t : ι → set α) [∀ i, finite (t i)] :
  finite (⋂ i, t i) :=
finite.set.subset (t $ classical.arbitrary ι) (Inter_subset _ _)

instance finite_insert (a : α) (s : set α) [finite s] : finite (insert a s : set α) :=
((set.finite_of_finite s).insert a).finite

instance finite_image (s : set α) (f : α → β) [finite s] : finite (f '' s) :=
((set.finite_of_finite s).image f).finite

instance finite_range (f : ι → α) [finite ι] : finite (range f) :=
by { haveI := fintype.of_finite (plift ι), apply_instance }

instance finite_prod (s : set α) (t : set β) [finite s] [finite t] :
  finite (s ×ˢ t : set (α × β)) :=
by { haveI := fintype.of_finite s, haveI := fintype.of_finite t, apply_instance }

instance finite_image2 (f : α → β → γ) (s : set α) (t : set β) [finite s] [finite t] :
  finite (image2 f s t : set γ) :=
by { rw ← image_prod, apply_instance }

instance finite_seq (f : set (α → β)) (s : set α) [finite f] [finite s] : finite (f.seq s) :=
by { rw seq_def, apply_instance }

end finite.set

/-! ### Non-instances -/

/-- If `(set.univ : set α)` is finite then `α` is a finite type. -/
lemma set.finite.finite_of_finite_univ (H : (univ : set α).finite) : finite α :=
@finite.of_equiv _ _ H.finite (equiv.set.univ α)

lemma finite.set.finite_of_finite_univ [finite ↥(univ : set α)] : finite α :=
(set.finite_of_finite _).finite_of_finite_univ

lemma finite.set.finite_of_finite_image (s : set α)
  {f : α → β} {g} (I : function.is_partial_inv f g) [finite (f '' s)] : finite s :=
begin
  haveI := fintype.of_finite (f '' s),
  exact finite.of_fintype (set.fintype_of_fintype_image s I),
end
