/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import order.complete_boolean_algebra
import order.directed
import order.galois_connection

/-!
# The set lattice

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides usual set notation for unions and intersections, a `complete_lattice` instance
for `set α`, and some more set constructions.

## Main declarations

* `set.Union`: Union of an indexed family of sets.
* `set.Inter`: Intersection of an indexed family of sets.
* `set.sInter`: **s**et **Inter**. Intersection of sets belonging to a set of sets.
* `set.sUnion`: **s**et **Union**. Union of sets belonging to a set of sets. This is actually
  defined in core Lean.
* `set.sInter_eq_bInter`, `set.sUnion_eq_bInter`: Shows that `⋂₀ s = ⋂ x ∈ s, x` and
  `⋃₀ s = ⋃ x ∈ s, x`.
* `set.complete_boolean_algebra`: `set α` is a `complete_boolean_algebra` with `≤ = ⊆`, `< = ⊂`,
  `⊓ = ∩`, `⊔ = ∪`, `⨅ = ⋂`, `⨆ = ⋃` and `\` as the set difference. See `set.boolean_algebra`.
* `set.kern_image`: For a function `f : α → β`, `s.kern_image f` is the set of `y` such that
  `f ⁻¹ y ⊆ s`.
* `set.seq`: Union of the image of a set under a **seq**uence of functions. `seq s t` is the union
  of `f '' t` over all `f ∈ s`, where `t : set α` and `s : set (α → β)`.
* `set.Union_eq_sigma_of_disjoint`: Equivalence between `⋃ i, t i` and `Σ i, t i`, where `t` is an
  indexed family of disjoint sets.

## Naming convention

In lemma names,
* `⋃ i, s i` is called `Union`
* `⋂ i, s i` is called `Inter`
* `⋃ i j, s i j` is called `Union₂`. This is a `Union` inside a `Union`.
* `⋂ i j, s i j` is called `Inter₂`. This is an `Inter` inside an `Inter`.
* `⋃ i ∈ s, t i` is called `bUnion` for "bounded `Union`". This is the special case of `Union₂`
  where `j : i ∈ s`.
* `⋂ i ∈ s, t i` is called `bInter` for "bounded `Inter`". This is the special case of `Inter₂`
  where `j : i ∈ s`.

## Notation

* `⋃`: `set.Union`
* `⋂`: `set.Inter`
* `⋃₀`: `set.sUnion`
* `⋂₀`: `set.sInter`
-/

open function tactic set

universes u
variables {α β γ : Type*} {ι ι' ι₂ : Sort*} {κ κ₁ κ₂ : ι → Sort*} {κ' : ι' → Sort*}

namespace set

/-! ### Complete lattice and complete Boolean algebra instances -/

instance : has_Inf (set α) := ⟨λ s, {a | ∀ t ∈ s, a ∈ t}⟩
instance : has_Sup (set α) := ⟨λ s, {a | ∃ t ∈ s, a ∈ t}⟩

/-- Intersection of a set of sets. -/
def sInter (S : set (set α)) : set α := Inf S

/-- Union of a set of sets. -/
def sUnion (S : set (set α)) : set α := Sup S

prefix `⋂₀ `:110 := sInter
prefix `⋃₀ `:110 := sUnion

@[simp] theorem mem_sInter {x : α} {S : set (set α)} : x ∈ ⋂₀ S ↔ ∀ t ∈ S, x ∈ t := iff.rfl
@[simp] theorem mem_sUnion {x : α} {S : set (set α)} : x ∈ ⋃₀ S ↔ ∃ t ∈ S, x ∈ t := iff.rfl

/-- Indexed union of a family of sets -/
def Union (s : ι → set β) : set β := supr s

/-- Indexed intersection of a family of sets -/
def Inter (s : ι → set β) : set β := infi s

notation `⋃` binders `, ` r:(scoped f, Union f) := r
notation `⋂` binders `, ` r:(scoped f, Inter f) := r

@[simp] lemma Sup_eq_sUnion (S : set (set α)) : Sup S = ⋃₀ S := rfl
@[simp] lemma Inf_eq_sInter (S : set (set α)) : Inf S = ⋂₀ S := rfl
@[simp] lemma supr_eq_Union (s : ι → set α) : supr s = Union s := rfl
@[simp] lemma infi_eq_Inter (s : ι → set α) : infi s = Inter s := rfl

@[simp] lemma mem_Union {x : α} {s : ι → set α} : x ∈ (⋃ i, s i) ↔ ∃ i, x ∈ s i :=
⟨λ ⟨t, ⟨⟨a, (t_eq : s a = t)⟩, (h : x ∈ t)⟩⟩, ⟨a, t_eq.symm ▸ h⟩,
  λ ⟨a, h⟩, ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩⟩

@[simp] lemma mem_Inter {x : α} {s : ι → set α} : x ∈ (⋂ i, s i) ↔ ∀ i, x ∈ s i :=
⟨λ (h : ∀ a ∈ {a : set α | ∃ i, s i = a}, x ∈ a) a, h (s a) ⟨a, rfl⟩,
  λ h t ⟨a, (eq : s a = t)⟩, eq ▸ h a⟩

lemma mem_Union₂ {x : γ} {s : Π i, κ i → set γ} : x ∈ (⋃ i j, s i j) ↔ ∃ i j, x ∈ s i j :=
by simp_rw mem_Union

lemma mem_Inter₂ {x : γ} {s : Π i, κ i → set γ} : x ∈ (⋂ i j, s i j) ↔ ∀ i j, x ∈ s i j :=
by simp_rw mem_Inter

lemma mem_Union_of_mem {s : ι → set α} {a : α} (i : ι) (ha : a ∈ s i) : a ∈ ⋃ i, s i :=
mem_Union.2 ⟨i, ha⟩

lemma mem_Union₂_of_mem {s : Π i, κ i → set α} {a : α} {i : ι} (j : κ i) (ha : a ∈ s i j) :
  a ∈ ⋃ i j, s i j :=
mem_Union₂.2 ⟨i, j, ha⟩

lemma mem_Inter_of_mem {s : ι → set α} {a : α} (h : ∀ i, a ∈ s i) : a ∈ ⋂ i, s i := mem_Inter.2 h

lemma mem_Inter₂_of_mem {s : Π i, κ i → set α} {a : α} (h : ∀ i j, a ∈ s i j) : a ∈ ⋂ i j, s i j :=
mem_Inter₂.2 h

instance : complete_boolean_algebra (set α) :=
{ Sup    := Sup,
  Inf    := Inf,
  le_Sup := λ s t t_in a a_in, ⟨t, ⟨t_in, a_in⟩⟩,
  Sup_le := λ s t h a ⟨t', ⟨t'_in, a_in⟩⟩, h t' t'_in a_in,
  le_Inf := λ s t h a a_in t' t'_in, h t' t'_in a_in,
  Inf_le := λ s t t_in a h, h _ t_in,
  infi_sup_le_sup_Inf := λ s S x, iff.mp $ by simp [forall_or_distrib_left],
  inf_Sup_le_supr_inf := λ s S x, iff.mp $ by simp [exists_and_distrib_left],
  .. set.boolean_algebra }

section galois_connection
variables {f : α → β}

protected lemma image_preimage : galois_connection (image f) (preimage f) :=
λ a b, image_subset_iff

/-- `kern_image f s` is the set of `y` such that `f ⁻¹ y ⊆ s`. -/
def kern_image (f : α → β) (s : set α) : set β := {y | ∀ ⦃x⦄, f x = y → x ∈ s}

protected lemma preimage_kern_image : galois_connection (preimage f) (kern_image f) :=
λ a b,
⟨ λ h x hx y hy, have f y ∈ a, from hy.symm ▸ hx, h this,
  λ h x (hx : f x ∈ a), h hx rfl⟩

end galois_connection

/-! ### Union and intersection over an indexed family of sets -/

instance : order_top (set α) :=
{ top := univ,
  le_top := by simp }

@[congr] theorem Union_congr_Prop {p q : Prop} {f₁ : p → set α} {f₂ : q → set α}
  (pq : p ↔ q) (f : ∀x, f₁ (pq.mpr x) = f₂ x) : Union f₁ = Union f₂ :=
supr_congr_Prop pq f

@[congr] theorem Inter_congr_Prop {p q : Prop} {f₁ : p → set α} {f₂ : q → set α}
  (pq : p ↔ q) (f : ∀x, f₁ (pq.mpr x) = f₂ x) : Inter f₁ = Inter f₂ :=
infi_congr_Prop pq f

lemma Union_plift_up (f : plift ι → set α) : (⋃ i, f (plift.up i)) = ⋃ i, f i := supr_plift_up _
lemma Union_plift_down (f : ι → set α) : (⋃ i, f (plift.down i)) = ⋃ i, f i := supr_plift_down _
lemma Inter_plift_up (f : plift ι → set α) : (⋂ i, f (plift.up i)) = ⋂ i, f i := infi_plift_up _
lemma Inter_plift_down (f : ι → set α) : (⋂ i, f (plift.down i)) = ⋂ i, f i := infi_plift_down _

lemma Union_eq_if {p : Prop} [decidable p] (s : set α) :
  (⋃ h : p, s) = if p then s else ∅ :=
supr_eq_if _

lemma Union_eq_dif {p : Prop} [decidable p] (s : p → set α) :
  (⋃ (h : p), s h) = if h : p then s h else ∅ :=
supr_eq_dif _

lemma Inter_eq_if {p : Prop} [decidable p] (s : set α) :
  (⋂ h : p, s) = if p then s else univ :=
infi_eq_if _

lemma Infi_eq_dif {p : Prop} [decidable p] (s : p → set α) :
  (⋂ (h : p), s h) = if h : p then s h else univ :=
infi_eq_dif _

lemma exists_set_mem_of_union_eq_top {ι : Type*} (t : set ι) (s : ι → set β)
  (w : (⋃ i ∈ t, s i) = ⊤) (x : β) :
  ∃ (i ∈ t), x ∈ s i :=
begin
  have p : x ∈ ⊤ := set.mem_univ x,
  simpa only [←w, set.mem_Union] using p,
end

lemma nonempty_of_union_eq_top_of_nonempty
  {ι : Type*} (t : set ι) (s : ι → set α) (H : nonempty α) (w : (⋃ i ∈ t, s i) = ⊤) :
  t.nonempty :=
begin
  obtain ⟨x, m, -⟩ := exists_set_mem_of_union_eq_top t s w H.some,
  exact ⟨x, m⟩,
end

theorem set_of_exists (p : ι → β → Prop) : {x | ∃ i, p i x} = ⋃ i, {x | p i x} :=
ext $ λ i, mem_Union.symm

theorem set_of_forall (p : ι → β → Prop) : {x | ∀ i, p i x} = ⋂ i, {x | p i x} :=
ext $ λ i, mem_Inter.symm

lemma Union_subset {s : ι → set α} {t : set α} (h : ∀ i, s i ⊆ t) : (⋃ i, s i) ⊆ t :=
@supr_le (set α) _ _ _ _ h

lemma Union₂_subset {s : Π i, κ i → set α} {t : set α} (h : ∀ i j, s i j ⊆ t) :
  (⋃ i j, s i j) ⊆ t :=
Union_subset $ λ x, Union_subset (h x)

theorem subset_Inter {t : set β} {s : ι → set β} (h : ∀ i, t ⊆ s i) : t ⊆ ⋂ i, s i :=
@le_infi (set β) _ _ _ _ h

lemma subset_Inter₂ {s : set α} {t : Π i, κ i → set α} (h : ∀ i j, s ⊆ t i j) : s ⊆ ⋂ i j, t i j :=
subset_Inter $ λ x, subset_Inter $ h x

@[simp] lemma Union_subset_iff {s : ι → set α} {t : set α} : (⋃ i, s i) ⊆ t ↔ ∀ i, s i ⊆ t :=
⟨λ h i, subset.trans (le_supr s _) h, Union_subset⟩

lemma Union₂_subset_iff {s : Π i, κ i → set α} {t : set α} :
  (⋃ i j, s i j) ⊆ t ↔ ∀ i j, s i j ⊆ t :=
by simp_rw Union_subset_iff

@[simp] lemma subset_Inter_iff {s : set α} {t : ι → set α} : s ⊆ (⋂ i, t i) ↔ ∀ i, s ⊆ t i :=
@le_infi_iff (set α) _ _ _ _

@[simp] lemma subset_Inter₂_iff {s : set α} {t : Π i, κ i → set α} :
  s ⊆ (⋂ i j, t i j) ↔ ∀ i j, s ⊆ t i j :=
by simp_rw subset_Inter_iff

lemma subset_Union : ∀ (s : ι → set β) (i : ι), s i ⊆ ⋃ i, s i := le_supr
lemma Inter_subset : ∀ (s : ι → set β) (i : ι), (⋂ i, s i) ⊆ s i := infi_le

lemma subset_Union₂ {s : Π i, κ i → set α} (i : ι) (j : κ i) : s i j ⊆ ⋃ i j, s i j :=
@le_supr₂ (set α) _ _ _ _ i j

lemma Inter₂_subset {s : Π i, κ i → set α} (i : ι) (j : κ i) : (⋂ i j, s i j) ⊆ s i j :=
@infi₂_le (set α) _ _ _ _ i j

/-- This rather trivial consequence of `subset_Union`is convenient with `apply`, and has `i`
explicit for this purpose. -/
lemma subset_Union_of_subset {s : set α} {t : ι → set α} (i : ι) (h : s ⊆ t i) : s ⊆ ⋃ i, t i :=
@le_supr_of_le (set α) _ _ _ _ i h

/-- This rather trivial consequence of `Inter_subset`is convenient with `apply`, and has `i`
explicit for this purpose. -/
lemma Inter_subset_of_subset {s : ι → set α} {t : set α} (i : ι) (h : s i ⊆ t) : (⋂ i, s i) ⊆ t :=
@infi_le_of_le (set α) _ _ _ _ i h

/-- This rather trivial consequence of `subset_Union₂` is convenient with `apply`, and has `i` and
`j` explicit for this purpose. -/
lemma subset_Union₂_of_subset {s : set α} {t : Π i, κ i → set α} (i : ι) (j : κ i) (h : s ⊆ t i j) :
  s ⊆ ⋃ i j, t i j :=
@le_supr₂_of_le (set α) _ _ _ _ _ i j h

/-- This rather trivial consequence of `Inter₂_subset` is convenient with `apply`, and has `i` and
`j` explicit for this purpose. -/
lemma Inter₂_subset_of_subset {s : Π i, κ i → set α} {t : set α} (i : ι) (j : κ i) (h : s i j ⊆ t) :
  (⋂ i j, s i j) ⊆ t :=
@infi₂_le_of_le (set α) _ _ _ _ _ i j h

lemma Union_mono {s t : ι → set α} (h : ∀ i, s i ⊆ t i) : (⋃ i, s i) ⊆ ⋃ i, t i :=
@supr_mono (set α) _ _ s t h

lemma Union₂_mono {s t : Π i, κ i → set α} (h : ∀ i j, s i j ⊆ t i j) :
  (⋃ i j, s i j) ⊆ ⋃ i j, t i j :=
@supr₂_mono (set α) _ _ _ s t h

lemma Inter_mono {s t : ι → set α} (h : ∀ i, s i ⊆ t i) : (⋂ i, s i) ⊆ ⋂ i, t i :=
@infi_mono (set α) _ _ s t h

lemma Inter₂_mono {s t : Π i, κ i → set α} (h : ∀ i j, s i j ⊆ t i j) :
  (⋂ i j, s i j) ⊆ ⋂ i j, t i j :=
@infi₂_mono (set α) _ _ _ s t h

lemma Union_mono' {s : ι → set α} {t : ι₂ → set α} (h : ∀ i, ∃ j, s i ⊆ t j) :
  (⋃ i, s i) ⊆ ⋃ i, t i :=
@supr_mono' (set α) _ _ _ s t h

lemma Union₂_mono' {s : Π i, κ i → set α} {t : Π i', κ' i' → set α}
  (h : ∀ i j, ∃ i' j', s i j ⊆ t i' j') :
  (⋃ i j, s i j) ⊆ ⋃ i' j', t i' j' :=
@supr₂_mono' (set α) _ _ _ _ _ s t h

lemma Inter_mono' {s : ι → set α} {t : ι' → set α} (h : ∀ j, ∃ i, s i ⊆ t j) :
  (⋂ i, s i) ⊆ (⋂ j, t j) :=
set.subset_Inter $ λ j, let ⟨i, hi⟩ := h j in Inter_subset_of_subset i hi

lemma Inter₂_mono' {s : Π i, κ i → set α} {t : Π i', κ' i' → set α}
  (h : ∀ i' j', ∃ i j, s i j ⊆ t i' j') :
  (⋂ i j, s i j) ⊆ ⋂ i' j', t i' j' :=
subset_Inter₂_iff.2 $ λ i' j', let ⟨i, j, hst⟩ := h i' j' in (Inter₂_subset _ _).trans hst

lemma Union₂_subset_Union (κ : ι → Sort*) (s : ι → set α) : (⋃ i (j : κ i), s i) ⊆ ⋃ i, s i :=
Union_mono $ λ i, Union_subset $ λ h, subset.rfl

lemma Inter_subset_Inter₂ (κ : ι → Sort*) (s : ι → set α) : (⋂ i, s i) ⊆ ⋂ i (j : κ i), s i :=
Inter_mono $ λ i, subset_Inter $ λ h, subset.rfl

lemma Union_set_of (P : ι → α → Prop) : (⋃ i, {x : α | P i x}) = {x : α | ∃ i, P i x} :=
by { ext, exact mem_Union }

lemma Inter_set_of (P : ι → α → Prop) : (⋂ i, {x : α | P i x}) = {x : α | ∀ i, P i x} :=
by { ext, exact mem_Inter }

lemma Union_congr_of_surjective {f : ι → set α} {g : ι₂ → set α} (h : ι → ι₂)
  (h1 : surjective h) (h2 : ∀ x, g (h x) = f x) : (⋃ x, f x) = ⋃ y, g y :=
h1.supr_congr h h2

lemma Inter_congr_of_surjective {f : ι → set α} {g : ι₂ → set α} (h : ι → ι₂)
  (h1 : surjective h) (h2 : ∀ x, g (h x) = f x) : (⋂ x, f x) = ⋂ y, g y :=
h1.infi_congr h h2

lemma Union_congr {s t : ι → set α} (h : ∀ i, s i = t i) : (⋃ i, s i) = ⋃ i, t i := supr_congr h
lemma Inter_congr {s t : ι → set α} (h : ∀ i, s i = t i) : (⋂ i, s i) = ⋂ i, t i := infi_congr h

lemma Union₂_congr {s t : Π i, κ i → set α} (h : ∀ i j, s i j = t i j) :
  (⋃ i j, s i j) = ⋃ i j, t i j :=
Union_congr $ λ i, Union_congr $ h i

lemma Inter₂_congr {s t : Π i, κ i → set α} (h : ∀ i j, s i j = t i j) :
  (⋂ i j, s i j) = ⋂ i j, t i j :=
Inter_congr $ λ i, Inter_congr $ h i

section nonempty
variables [nonempty ι] {f : ι → set α} {s : set α}

lemma Union_const (s : set β) : (⋃ i : ι, s) = s := supr_const
lemma Inter_const (s : set β) : (⋂ i : ι, s) = s := infi_const

lemma Union_eq_const (hf : ∀ i, f i = s) : (⋃ i, f i) = s := (Union_congr hf).trans $ Union_const _
lemma Inter_eq_const (hf : ∀ i, f i = s) : (⋂ i, f i) = s := (Inter_congr hf).trans $ Inter_const _

end nonempty

@[simp] theorem compl_Union (s : ι → set β) : (⋃ i, s i)ᶜ = (⋂ i, (s i)ᶜ) :=
compl_supr

lemma compl_Union₂ (s : Π i, κ i → set α) : (⋃ i j, s i j)ᶜ = ⋂ i j, (s i j)ᶜ :=
by simp_rw compl_Union

@[simp] theorem compl_Inter (s : ι → set β) : (⋂ i, s i)ᶜ = (⋃ i, (s i)ᶜ) :=
compl_infi

lemma compl_Inter₂ (s : Π i, κ i → set α) : (⋂ i j, s i j)ᶜ = ⋃ i j, (s i j)ᶜ :=
by simp_rw compl_Inter

-- classical -- complete_boolean_algebra
theorem Union_eq_compl_Inter_compl (s : ι → set β) : (⋃ i, s i) = (⋂ i, (s i)ᶜ)ᶜ :=
by simp only [compl_Inter, compl_compl]

-- classical -- complete_boolean_algebra
theorem Inter_eq_compl_Union_compl (s : ι → set β) : (⋂ i, s i) = (⋃ i, (s i)ᶜ)ᶜ :=
by simp only [compl_Union, compl_compl]

theorem inter_Union (s : set β) (t : ι → set β) :
  s ∩ (⋃ i, t i) = ⋃ i, s ∩ t i :=
inf_supr_eq _ _

theorem Union_inter (s : set β) (t : ι → set β) :
  (⋃ i, t i) ∩ s = ⋃ i, t i ∩ s :=
supr_inf_eq _ _

theorem Union_union_distrib (s : ι → set β) (t : ι → set β) :
  (⋃ i, s i ∪ t i) = (⋃ i, s i) ∪ (⋃ i, t i) :=
supr_sup_eq

theorem Inter_inter_distrib (s : ι → set β) (t : ι → set β) :
  (⋂ i, s i ∩ t i) = (⋂ i, s i) ∩ (⋂ i, t i) :=
infi_inf_eq

theorem union_Union [nonempty ι] (s : set β) (t : ι → set β) :
  s ∪ (⋃ i, t i) = ⋃ i, s ∪ t i :=
sup_supr

theorem Union_union [nonempty ι] (s : set β) (t : ι → set β) :
  (⋃ i, t i) ∪ s = ⋃ i, t i ∪ s :=
supr_sup

theorem inter_Inter [nonempty ι] (s : set β) (t : ι → set β) :
  s ∩ (⋂ i, t i) = ⋂ i, s ∩ t i :=
inf_infi

theorem Inter_inter [nonempty ι] (s : set β) (t : ι → set β) :
  (⋂ i, t i) ∩ s = ⋂ i, t i ∩ s :=
infi_inf

-- classical
theorem union_Inter (s : set β) (t : ι → set β) :
  s ∪ (⋂ i, t i) = ⋂ i, s ∪ t i :=
sup_infi_eq _ _

theorem Inter_union (s : ι → set β) (t : set β) :
  (⋂ i, s i) ∪ t = ⋂ i, s i ∪ t :=
infi_sup_eq _ _

theorem Union_diff (s : set β) (t : ι → set β) :
  (⋃ i, t i) \ s = ⋃ i, t i \ s :=
Union_inter _ _

theorem diff_Union [nonempty ι] (s : set β) (t : ι → set β) :
  s \ (⋃ i, t i) = ⋂ i, s \ t i :=
by rw [diff_eq, compl_Union, inter_Inter]; refl

theorem diff_Inter (s : set β) (t : ι → set β) :
  s \ (⋂ i, t i) = ⋃ i, s \ t i :=
by rw [diff_eq, compl_Inter, inter_Union]; refl

lemma directed_on_Union {r} {f : ι → set α} (hd : directed (⊆) f)
  (h : ∀ x, directed_on r (f x)) : directed_on r (⋃ x, f x) :=
by simp only [directed_on, exists_prop, mem_Union, exists_imp_distrib]; exact
λ a₁ b₁ fb₁ a₂ b₂ fb₂,
let ⟨z, zb₁, zb₂⟩ := hd b₁ b₂,
    ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂) in
⟨x, ⟨z, xf⟩, xa₁, xa₂⟩

lemma Union_inter_subset {ι α} {s t : ι → set α} : (⋃ i, s i ∩ t i) ⊆ (⋃ i, s i) ∩ (⋃ i, t i) :=
le_supr_inf_supr s t

lemma Union_inter_of_monotone {ι α} [preorder ι] [is_directed ι (≤)] {s t : ι → set α}
  (hs : monotone s) (ht : monotone t) : (⋃ i, s i ∩ t i) = (⋃ i, s i) ∩ (⋃ i, t i) :=
supr_inf_of_monotone hs ht

lemma Union_inter_of_antitone {ι α} [preorder ι] [is_directed ι (swap (≤))] {s t : ι → set α}
  (hs : antitone s) (ht : antitone t) : (⋃ i, s i ∩ t i) = (⋃ i, s i) ∩ (⋃ i, t i) :=
supr_inf_of_antitone hs ht

lemma Inter_union_of_monotone {ι α} [preorder ι] [is_directed ι (swap (≤))] {s t : ι → set α}
  (hs : monotone s) (ht : monotone t) : (⋂ i, s i ∪ t i) = (⋂ i, s i) ∪ (⋂ i, t i) :=
infi_sup_of_monotone hs ht

lemma Inter_union_of_antitone {ι α} [preorder ι] [is_directed ι (≤)] {s t : ι → set α}
  (hs : antitone s) (ht : antitone t) : (⋂ i, s i ∪ t i) = (⋂ i, s i) ∪ (⋂ i, t i) :=
infi_sup_of_antitone hs ht

/-- An equality version of this lemma is `Union_Inter_of_monotone` in `data.set.finite`. -/
lemma Union_Inter_subset {s : ι → ι' → set α} : (⋃ j, ⋂ i, s i j) ⊆ ⋂ i, ⋃ j, s i j :=
supr_infi_le_infi_supr (flip s)

lemma Union_option {ι} (s : option ι → set α) : (⋃ o, s o) = s none ∪ ⋃ i, s (some i) :=
supr_option s

lemma Inter_option {ι} (s : option ι → set α) : (⋂ o, s o) = s none ∩ ⋂ i, s (some i) :=
infi_option s

section

variables (p : ι → Prop) [decidable_pred p]

lemma Union_dite (f : Π i, p i → set α) (g : Π i, ¬p i → set α) :
  (⋃ i, if h : p i then f i h else g i h) = (⋃ i (h : p i), f i h) ∪ (⋃ i (h : ¬ p i), g i h) :=
supr_dite _ _ _

lemma Union_ite (f g : ι → set α) :
  (⋃ i, if p i then f i else g i) = (⋃ i (h : p i), f i) ∪ (⋃ i (h : ¬ p i), g i) :=
Union_dite _ _ _

lemma Inter_dite (f : Π i, p i → set α) (g : Π i, ¬p i → set α) :
  (⋂ i, if h : p i then f i h else g i h) = (⋂ i (h : p i), f i h) ∩ (⋂ i (h : ¬ p i), g i h) :=
infi_dite _ _ _

lemma Inter_ite (f g : ι → set α) :
  (⋂ i, if p i then f i else g i) = (⋂ i (h : p i), f i) ∩ (⋂ i (h : ¬ p i), g i) :=
Inter_dite _ _ _

end

lemma image_projection_prod {ι : Type*} {α : ι → Type*} {v : Π (i : ι), set (α i)}
  (hv : (pi univ v).nonempty) (i : ι) :
  (λ (x : Π (i : ι), α i), x i) '' (⋂ k, (λ (x : Π (j : ι), α j), x k) ⁻¹' v k) = v i:=
begin
  classical,
  apply subset.antisymm,
  { simp [Inter_subset] },
  { intros y y_in,
    simp only [mem_image, mem_Inter, mem_preimage],
    rcases hv with ⟨z, hz⟩,
    refine ⟨function.update z i y, _, update_same i y z⟩,
    rw @forall_update_iff ι α _ z i y (λ i t, t ∈ v i),
    exact ⟨y_in, λ j hj, by simpa using hz j⟩ },
end

/-! ### Unions and intersections indexed by `Prop` -/

theorem Inter_false {s : false → set α} : Inter s = univ := infi_false
theorem Union_false {s : false → set α} : Union s = ∅ := supr_false

@[simp] theorem Inter_true {s : true → set α} : Inter s = s trivial := infi_true

@[simp] theorem Union_true {s : true → set α} : Union s = s trivial := supr_true

@[simp] theorem Inter_exists {p : ι → Prop} {f : Exists p → set α} :
  (⋂ x, f x) = (⋂ i (h : p i), f ⟨i, h⟩) :=
infi_exists

@[simp] theorem Union_exists {p : ι → Prop} {f : Exists p → set α} :
  (⋃ x, f x) = (⋃ i (h : p i), f ⟨i, h⟩) :=
supr_exists

@[simp] lemma Union_empty : (⋃ i : ι, ∅ : set α) = ∅ := supr_bot

@[simp] lemma Inter_univ : (⋂ i : ι, univ : set α) = univ := infi_top

section

variables {s : ι → set α}

@[simp] lemma Union_eq_empty : (⋃ i, s i) = ∅ ↔ ∀ i, s i = ∅ := supr_eq_bot

@[simp] lemma Inter_eq_univ : (⋂ i, s i) = univ ↔ ∀ i, s i = univ := infi_eq_top

@[simp] lemma nonempty_Union : (⋃ i, s i).nonempty ↔ ∃ i, (s i).nonempty :=
by simp [nonempty_iff_ne_empty]

@[simp] lemma nonempty_bUnion {t : set α} {s : α → set β} :
  (⋃ i ∈ t, s i).nonempty ↔ ∃ i ∈ t, (s i).nonempty :=
by simp [nonempty_iff_ne_empty]

lemma Union_nonempty_index (s : set α) (t : s.nonempty → set β) :
  (⋃ h, t h) = ⋃ x ∈ s, t ⟨x, ‹_›⟩ :=
supr_exists

end

@[simp] theorem Inter_Inter_eq_left {b : β} {s : Π x : β, x = b → set α} :
  (⋂ x (h : x = b), s x h) = s b rfl :=
infi_infi_eq_left

@[simp] theorem Inter_Inter_eq_right {b : β} {s : Π x : β, b = x → set α} :
  (⋂ x (h : b = x), s x h) = s b rfl :=
infi_infi_eq_right

@[simp] theorem Union_Union_eq_left {b : β} {s : Π x : β, x = b → set α} :
  (⋃ x (h : x = b), s x h) = s b rfl :=
supr_supr_eq_left

@[simp] theorem Union_Union_eq_right {b : β} {s : Π x : β, b = x → set α} :
  (⋃ x (h : b = x), s x h) = s b rfl :=
supr_supr_eq_right

theorem Inter_or {p q : Prop} (s : p ∨ q → set α) :
  (⋂ h, s h) = (⋂ h : p, s (or.inl h)) ∩ (⋂ h : q, s (or.inr h)) :=
infi_or

theorem Union_or {p q : Prop} (s : p ∨ q → set α) :
  (⋃ h, s h) = (⋃ i, s (or.inl i)) ∪ (⋃ j, s (or.inr j)) :=
supr_or

theorem Union_and {p q : Prop} (s : p ∧ q → set α) :
  (⋃ h, s h) = ⋃ hp hq, s ⟨hp, hq⟩ :=
supr_and

theorem Inter_and {p q : Prop} (s : p ∧ q → set α) :
  (⋂ h, s h) = ⋂ hp hq, s ⟨hp, hq⟩ :=
infi_and

lemma Union_comm (s : ι → ι' → set α) : (⋃ i i', s i i') = ⋃ i' i, s i i' := supr_comm
lemma Inter_comm (s : ι → ι' → set α) : (⋂ i i', s i i') = ⋂ i' i, s i i' := infi_comm

lemma Union₂_comm (s : Π i₁, κ₁ i₁ → Π i₂, κ₂ i₂ → set α) :
  (⋃ i₁ j₁ i₂ j₂, s i₁ j₁ i₂ j₂) = ⋃ i₂ j₂ i₁ j₁, s i₁ j₁ i₂ j₂ :=
supr₂_comm _

lemma Inter₂_comm (s : Π i₁, κ₁ i₁ → Π i₂, κ₂ i₂ → set α) :
  (⋂ i₁ j₁ i₂ j₂, s i₁ j₁ i₂ j₂) = ⋂ i₂ j₂ i₁ j₁, s i₁ j₁ i₂ j₂ :=
infi₂_comm _

@[simp] theorem bUnion_and (p : ι → Prop) (q : ι → ι' → Prop) (s : Π x y, p x ∧ q x y → set α) :
  (⋃ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h) =
    ⋃ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ :=
by simp only [Union_and, @Union_comm _ ι']

@[simp] theorem bUnion_and' (p : ι' → Prop) (q : ι → ι' → Prop) (s : Π x y, p y ∧ q x y → set α) :
  (⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h) =
    ⋃ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ :=
by simp only [Union_and, @Union_comm _ ι]

@[simp] theorem bInter_and (p : ι → Prop) (q : ι → ι' → Prop) (s : Π x y, p x ∧ q x y → set α) :
  (⋂ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h) =
    ⋂ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ :=
by simp only [Inter_and, @Inter_comm _ ι']

@[simp] theorem bInter_and' (p : ι' → Prop) (q : ι → ι' → Prop) (s : Π x y, p y ∧ q x y → set α) :
  (⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h) =
    ⋂ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ :=
by simp only [Inter_and, @Inter_comm _ ι]

@[simp] theorem Union_Union_eq_or_left {b : β} {p : β → Prop} {s : Π x : β, (x = b ∨ p x) → set α} :
  (⋃ x h, s x h) = s b (or.inl rfl) ∪ ⋃ x (h : p x), s x (or.inr h) :=
by simp only [Union_or, Union_union_distrib, Union_Union_eq_left]

@[simp] theorem Inter_Inter_eq_or_left {b : β} {p : β → Prop} {s : Π x : β, (x = b ∨ p x) → set α} :
  (⋂ x h, s x h) = s b (or.inl rfl) ∩ ⋂ x (h : p x), s x (or.inr h) :=
by simp only [Inter_or, Inter_inter_distrib, Inter_Inter_eq_left]

/-! ### Bounded unions and intersections -/

/-- A specialization of `mem_Union₂`. -/
theorem mem_bUnion {s : set α} {t : α → set β} {x : α} {y : β} (xs : x ∈ s) (ytx : y ∈ t x) :
  y ∈ ⋃ x ∈ s, t x :=
mem_Union₂_of_mem xs ytx

/-- A specialization of `mem_Inter₂`. -/
theorem mem_bInter {s : set α} {t : α → set β} {y : β} (h : ∀ x ∈ s, y ∈ t x) :
  y ∈ ⋂ x ∈ s, t x :=
mem_Inter₂_of_mem h

/-- A specialization of `subset_Union₂`. -/
theorem subset_bUnion_of_mem {s : set α} {u : α → set β} {x : α} (xs : x ∈ s) :
  u x ⊆ (⋃ x ∈ s, u x) :=
subset_Union₂ x xs

/-- A specialization of `Inter₂_subset`. -/
theorem bInter_subset_of_mem {s : set α} {t : α → set β} {x : α} (xs : x ∈ s) :
  (⋂ x ∈ s, t x) ⊆ t x :=
Inter₂_subset x xs

theorem bUnion_subset_bUnion_left {s s' : set α} {t : α → set β}
  (h : s ⊆ s') : (⋃ x ∈ s, t x) ⊆ (⋃ x ∈ s', t x) :=
Union₂_subset $ λ x hx, subset_bUnion_of_mem $ h hx

theorem bInter_subset_bInter_left {s s' : set α} {t : α → set β}
  (h : s' ⊆ s) : (⋂ x ∈ s, t x) ⊆ (⋂ x ∈ s', t x) :=
subset_Inter₂ $ λ x hx, bInter_subset_of_mem $ h hx

lemma bUnion_mono {s s' : set α} {t t' : α → set β} (hs : s' ⊆ s) (h : ∀ x ∈ s, t x ⊆ t' x) :
  (⋃ x ∈ s', t x) ⊆ ⋃ x ∈ s, t' x :=
(bUnion_subset_bUnion_left hs).trans $ Union₂_mono h

lemma bInter_mono {s s' : set α} {t t' : α → set β} (hs : s ⊆ s') (h : ∀ x ∈ s, t x ⊆ t' x) :
  (⋂ x ∈ s', t x) ⊆ (⋂ x ∈ s, t' x) :=
(bInter_subset_bInter_left hs).trans $ Inter₂_mono h

theorem bUnion_eq_Union (s : set α) (t : Π x ∈ s, set β) :
  (⋃ x ∈ s, t x ‹_›) = (⋃ x : s, t x x.2) :=
supr_subtype'

theorem bInter_eq_Inter (s : set α) (t : Π x ∈ s, set β) :
  (⋂ x ∈ s, t x ‹_›) = (⋂ x : s, t x x.2) :=
infi_subtype'

theorem Union_subtype (p : α → Prop) (s : {x // p x} → set β) :
  (⋃ x : {x // p x}, s x) = ⋃ x (hx : p x), s ⟨x, hx⟩ :=
supr_subtype

theorem Inter_subtype (p : α → Prop) (s : {x // p x} → set β) :
  (⋂ x : {x // p x}, s x) = ⋂ x (hx : p x), s ⟨x, hx⟩ :=
infi_subtype

theorem bInter_empty (u : α → set β) : (⋂ x ∈ (∅ : set α), u x) = univ :=
infi_emptyset

theorem bInter_univ (u : α → set β) : (⋂ x ∈ @univ α, u x) = ⋂ x, u x :=
infi_univ

@[simp] lemma bUnion_self (s : set α) : (⋃ x ∈ s, s) = s :=
subset.antisymm (Union₂_subset $ λ x hx, subset.refl s) (λ x hx, mem_bUnion hx hx)

@[simp] lemma Union_nonempty_self (s : set α) : (⋃ h : s.nonempty, s) = s :=
by rw [Union_nonempty_index, bUnion_self]

-- TODO(Jeremy): here is an artifact of the encoding of bounded intersection:
-- without dsimp, the next theorem fails to type check, because there is a lambda
-- in a type that needs to be contracted. Using simp [eq_of_mem_singleton xa] also works.

theorem bInter_singleton (a : α) (s : α → set β) : (⋂ x ∈ ({a} : set α), s x) = s a :=
infi_singleton

theorem bInter_union (s t : set α) (u : α → set β) :
  (⋂ x ∈ s ∪ t, u x) = (⋂ x ∈ s, u x) ∩ (⋂ x ∈ t, u x) :=
infi_union

theorem bInter_insert (a : α) (s : set α) (t : α → set β) :
  (⋂ x ∈ insert a s, t x) = t a ∩ (⋂ x ∈ s, t x) :=
by simp

-- TODO(Jeremy): another example of where an annotation is needed

theorem bInter_pair (a b : α) (s : α → set β) :
  (⋂ x ∈ ({a, b} : set α), s x) = s a ∩ s b :=
by rw [bInter_insert, bInter_singleton]

lemma bInter_inter {ι α : Type*} {s : set ι} (hs : s.nonempty) (f : ι → set α) (t : set α) :
  (⋂ i ∈ s, f i ∩ t) = (⋂ i ∈ s, f i) ∩ t :=
begin
  haveI : nonempty s := hs.to_subtype,
  simp [bInter_eq_Inter, ← Inter_inter]
end

lemma inter_bInter {ι α : Type*} {s : set ι} (hs : s.nonempty) (f : ι → set α) (t : set α) :
  (⋂ i ∈ s, t ∩ f i) = t ∩ ⋂ i ∈ s, f i :=
begin
  rw [inter_comm, ← bInter_inter hs],
  simp [inter_comm]
end

theorem bUnion_empty (s : α → set β) : (⋃ x ∈ (∅ : set α), s x) = ∅ :=
supr_emptyset

theorem bUnion_univ (s : α → set β) : (⋃ x ∈ @univ α, s x) = ⋃ x, s x :=
supr_univ

theorem bUnion_singleton (a : α) (s : α → set β) : (⋃ x ∈ ({a} : set α), s x) = s a :=
supr_singleton

@[simp] theorem bUnion_of_singleton (s : set α) : (⋃ x ∈ s, {x}) = s :=
ext $ by simp

theorem bUnion_union (s t : set α) (u : α → set β) :
  (⋃ x ∈ s ∪ t, u x) = (⋃ x ∈ s, u x) ∪ (⋃ x ∈ t, u x) :=
supr_union

@[simp] lemma Union_coe_set {α β : Type*} (s : set α) (f : s → set β) :
  (⋃ i, f i) = ⋃ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
Union_subtype _ _

@[simp] lemma Inter_coe_set {α β : Type*} (s : set α) (f : s → set β) :
  (⋂ i, f i) = ⋂ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
Inter_subtype _ _

theorem bUnion_insert (a : α) (s : set α) (t : α → set β) :
  (⋃ x ∈ insert a s, t x) = t a ∪ (⋃ x ∈ s, t x) :=
by simp

theorem bUnion_pair (a b : α) (s : α → set β) :
  (⋃ x ∈ ({a, b} : set α), s x) = s a ∪ s b :=
by simp

lemma inter_Union₂ (s : set α) (t : Π i, κ i → set α) : s ∩ (⋃ i j, t i j) = ⋃ i j, s ∩ t i j :=
by simp only [inter_Union]

lemma Union₂_inter (s : Π i, κ i → set α) (t : set α) : (⋃ i j, s i j) ∩ t = ⋃ i j, s i j ∩ t :=
by simp_rw Union_inter

lemma union_Inter₂ (s : set α) (t : Π i, κ i → set α) : s ∪ (⋂ i j, t i j) = ⋂ i j, s ∪ t i j :=
by simp_rw union_Inter

lemma Inter₂_union (s : Π i, κ i → set α) (t : set α) : (⋂ i j, s i j) ∪ t = ⋂ i j, s i j ∪ t :=
by simp_rw Inter_union

theorem mem_sUnion_of_mem {x : α} {t : set α} {S : set (set α)} (hx : x ∈ t) (ht : t ∈ S) :
  x ∈ ⋃₀ S :=
⟨t, ht, hx⟩

-- is this theorem really necessary?
theorem not_mem_of_not_mem_sUnion {x : α} {t : set α} {S : set (set α)}
  (hx : x ∉ ⋃₀ S) (ht : t ∈ S) : x ∉ t :=
λ h, hx ⟨t, ht, h⟩

theorem sInter_subset_of_mem {S : set (set α)} {t : set α} (tS : t ∈ S) : ⋂₀ S ⊆ t :=
Inf_le tS

theorem subset_sUnion_of_mem {S : set (set α)} {t : set α} (tS : t ∈ S) : t ⊆ ⋃₀ S :=
le_Sup tS

lemma subset_sUnion_of_subset {s : set α} (t : set (set α)) (u : set α) (h₁ : s ⊆ u)
  (h₂ : u ∈ t) : s ⊆ ⋃₀ t :=
subset.trans h₁ (subset_sUnion_of_mem h₂)

theorem sUnion_subset {S : set (set α)} {t : set α} (h : ∀ t' ∈ S, t' ⊆ t) : (⋃₀ S) ⊆ t :=
Sup_le h

@[simp] theorem sUnion_subset_iff {s : set (set α)} {t : set α} : ⋃₀ s ⊆ t ↔ ∀ t' ∈ s, t' ⊆ t :=
@Sup_le_iff (set α) _ _ _

theorem subset_sInter {S : set (set α)} {t : set α} (h : ∀ t' ∈ S, t ⊆ t') : t ⊆ (⋂₀ S) :=
le_Inf h

@[simp] theorem subset_sInter_iff {S : set (set α)} {t : set α} : t ⊆ (⋂₀ S) ↔ ∀ t' ∈ S, t ⊆ t' :=
@le_Inf_iff (set α) _ _ _

theorem sUnion_subset_sUnion {S T : set (set α)} (h : S ⊆ T) : ⋃₀ S ⊆ ⋃₀ T :=
sUnion_subset $ λ s hs, subset_sUnion_of_mem (h hs)

theorem sInter_subset_sInter {S T : set (set α)} (h : S ⊆ T) : ⋂₀ T ⊆ ⋂₀ S :=
subset_sInter $ λ s hs, sInter_subset_of_mem (h hs)

@[simp] theorem sUnion_empty : ⋃₀ ∅ = (∅ : set α) := Sup_empty

@[simp] theorem sInter_empty : ⋂₀ ∅ = (univ : set α) := Inf_empty

@[simp] theorem sUnion_singleton (s : set α) : ⋃₀ {s} = s := Sup_singleton

@[simp] theorem sInter_singleton (s : set α) : ⋂₀ {s} = s := Inf_singleton

@[simp] theorem sUnion_eq_empty {S : set (set α)} : (⋃₀ S) = ∅ ↔ ∀ s ∈ S, s = ∅ := Sup_eq_bot

@[simp] theorem sInter_eq_univ {S : set (set α)} : (⋂₀ S) = univ ↔ ∀ s ∈ S, s = univ := Inf_eq_top

@[simp] theorem nonempty_sUnion {S : set (set α)} : (⋃₀ S).nonempty ↔ ∃ s ∈ S, set.nonempty s :=
by simp [nonempty_iff_ne_empty]

lemma nonempty.of_sUnion {s : set (set α)} (h : (⋃₀ s).nonempty) : s.nonempty :=
let ⟨s, hs, _⟩ := nonempty_sUnion.1 h in ⟨s, hs⟩

lemma nonempty.of_sUnion_eq_univ [nonempty α] {s : set (set α)} (h : ⋃₀ s = univ) : s.nonempty :=
nonempty.of_sUnion $ h.symm ▸ univ_nonempty

theorem sUnion_union (S T : set (set α)) : ⋃₀ (S ∪ T) = ⋃₀ S ∪ ⋃₀ T := Sup_union

theorem sInter_union (S T : set (set α)) : ⋂₀ (S ∪ T) = ⋂₀ S ∩ ⋂₀ T := Inf_union

@[simp] theorem sUnion_insert (s : set α) (T : set (set α)) : ⋃₀ (insert s T) = s ∪ ⋃₀ T :=
Sup_insert

@[simp] theorem sInter_insert (s : set α) (T : set (set α)) : ⋂₀ (insert s T) = s ∩ ⋂₀ T :=
Inf_insert

@[simp] lemma sUnion_diff_singleton_empty (s : set (set α)) : ⋃₀ (s \ {∅}) = ⋃₀ s :=
Sup_diff_singleton_bot s

@[simp] lemma sInter_diff_singleton_univ (s : set (set α)) : ⋂₀ (s \ {univ}) = ⋂₀ s :=
Inf_diff_singleton_top s

theorem sUnion_pair (s t : set α) : ⋃₀ {s, t} = s ∪ t :=
Sup_pair

theorem sInter_pair (s t : set α) : ⋂₀ {s, t} = s ∩ t :=
Inf_pair

@[simp] theorem sUnion_image (f : α → set β) (s : set α) : ⋃₀ (f '' s) = ⋃ x ∈ s, f x := Sup_image

@[simp] theorem sInter_image (f : α → set β) (s : set α) : ⋂₀ (f '' s) = ⋂ x ∈ s, f x := Inf_image

@[simp] theorem sUnion_range (f : ι → set β) : ⋃₀ (range f) = ⋃ x, f x := rfl

@[simp] theorem sInter_range (f : ι → set β) : ⋂₀ (range f) = ⋂ x, f x := rfl

lemma Union_eq_univ_iff {f : ι → set α} : (⋃ i, f i) = univ ↔ ∀ x, ∃ i, x ∈ f i :=
by simp only [eq_univ_iff_forall, mem_Union]

lemma Union₂_eq_univ_iff {s : Π i, κ i → set α} : (⋃ i j, s i j) = univ ↔ ∀ a, ∃ i j, a ∈ s i j :=
by simp only [Union_eq_univ_iff, mem_Union]

lemma sUnion_eq_univ_iff {c : set (set α)} :
  ⋃₀ c = univ ↔ ∀ a, ∃ b ∈ c, a ∈ b :=
by simp only [eq_univ_iff_forall, mem_sUnion]

-- classical
lemma Inter_eq_empty_iff {f : ι → set α} : (⋂ i, f i) = ∅ ↔ ∀ x, ∃ i, x ∉ f i :=
by simp [set.eq_empty_iff_forall_not_mem]

-- classical
lemma Inter₂_eq_empty_iff {s : Π i, κ i → set α} : (⋂ i j, s i j) = ∅ ↔ ∀ a, ∃ i j, a ∉ s i j :=
by simp only [eq_empty_iff_forall_not_mem, mem_Inter, not_forall]

-- classical
lemma sInter_eq_empty_iff {c : set (set α)} :
  ⋂₀ c = ∅ ↔ ∀ a, ∃ b ∈ c, a ∉ b :=
by simp [set.eq_empty_iff_forall_not_mem]

-- classical
@[simp] theorem nonempty_Inter {f : ι → set α} : (⋂ i, f i).nonempty ↔ ∃ x, ∀ i, x ∈ f i :=
by simp [nonempty_iff_ne_empty, Inter_eq_empty_iff]

-- classical
@[simp] lemma nonempty_Inter₂ {s : Π i, κ i → set α} :
  (⋂ i j, s i j).nonempty ↔ ∃ a, ∀ i j, a ∈ s i j :=
by simp [nonempty_iff_ne_empty, Inter_eq_empty_iff]

-- classical
@[simp] theorem nonempty_sInter {c : set (set α)}:
  (⋂₀ c).nonempty ↔ ∃ a, ∀ b ∈ c, a ∈ b :=
by simp [nonempty_iff_ne_empty, sInter_eq_empty_iff]

-- classical
theorem compl_sUnion (S : set (set α)) :
  (⋃₀ S)ᶜ = ⋂₀ (compl '' S) :=
ext $ λ x, by simp

-- classical
theorem sUnion_eq_compl_sInter_compl (S : set (set α)) :
  ⋃₀ S = (⋂₀ (compl '' S))ᶜ :=
by rw [←compl_compl (⋃₀ S), compl_sUnion]

-- classical
theorem compl_sInter (S : set (set α)) :
  (⋂₀ S)ᶜ = ⋃₀ (compl '' S) :=
by rw [sUnion_eq_compl_sInter_compl, compl_compl_image]

-- classical
theorem sInter_eq_compl_sUnion_compl (S : set (set α)) :
   ⋂₀ S = (⋃₀ (compl '' S))ᶜ :=
by rw [←compl_compl (⋂₀ S), compl_sInter]

theorem inter_empty_of_inter_sUnion_empty {s t : set α} {S : set (set α)} (hs : t ∈ S)
    (h : s ∩ ⋃₀ S = ∅) :
  s ∩ t = ∅ :=
eq_empty_of_subset_empty $ by rw ← h; exact
inter_subset_inter_right _ (subset_sUnion_of_mem hs)

theorem range_sigma_eq_Union_range {γ : α → Type*} (f : sigma γ → β) :
  range f = ⋃ a, range (λ b, f ⟨a, b⟩) :=
set.ext $ by simp

theorem Union_eq_range_sigma (s : α → set β) : (⋃ i, s i) = range (λ a : Σ i, s i, a.2) :=
by simp [set.ext_iff]

theorem Union_eq_range_psigma (s : ι → set β) : (⋃ i, s i) = range (λ a : Σ' i, s i, a.2) :=
by simp [set.ext_iff]

theorem Union_image_preimage_sigma_mk_eq_self {ι : Type*} {σ : ι → Type*} (s : set (sigma σ)) :
  (⋃ i, sigma.mk i '' (sigma.mk i ⁻¹' s)) = s :=
begin
  ext x,
  simp only [mem_Union, mem_image, mem_preimage],
  split,
  { rintro ⟨i, a, h, rfl⟩, exact h },
  { intro h, cases x with i a, exact ⟨i, a, h, rfl⟩ }
end

lemma sigma.univ (X : α → Type*) : (set.univ : set (Σ a, X a)) = ⋃ a, range (sigma.mk a) :=
set.ext $ λ x, iff_of_true trivial ⟨range (sigma.mk x.1), set.mem_range_self _, x.2, sigma.eta x⟩

lemma sUnion_mono {s t : set (set α)} (h : s ⊆ t) : (⋃₀ s) ⊆ (⋃₀ t) :=
sUnion_subset $ λ t' ht', subset_sUnion_of_mem $ h ht'

lemma Union_subset_Union_const {s : set α} (h : ι → ι₂) : (⋃ i : ι, s) ⊆ (⋃ j : ι₂, s) :=
@supr_const_mono (set α) ι ι₂ _ s h

@[simp] lemma Union_singleton_eq_range {α β : Type*} (f : α → β) :
  (⋃ (x : α), {f x}) = range f :=
by { ext x, simp [@eq_comm _ x] }

lemma Union_of_singleton (α : Type*) : (⋃ x, {x} : set α) = univ :=
by simp

lemma Union_of_singleton_coe (s : set α) :
  (⋃ (i : s), {i} : set α) = s :=
by simp

lemma sUnion_eq_bUnion {s : set (set α)} : (⋃₀ s) = (⋃ (i : set α) (h : i ∈ s), i) :=
by rw [← sUnion_image, image_id']

lemma sInter_eq_bInter {s : set (set α)} : (⋂₀ s) = (⋂ (i : set α) (h : i ∈ s), i) :=
by rw [← sInter_image, image_id']

lemma sUnion_eq_Union {s : set (set α)} : (⋃₀ s) = (⋃ (i : s), i) :=
by simp only [←sUnion_range, subtype.range_coe]

lemma sInter_eq_Inter {s : set (set α)} : (⋂₀ s) = (⋂ (i : s), i) :=
by simp only [←sInter_range, subtype.range_coe]

@[simp] lemma Union_of_empty [is_empty ι] (s : ι → set α) : (⋃ i, s i) = ∅ := supr_of_empty _
@[simp] lemma Inter_of_empty [is_empty ι] (s : ι → set α) : (⋂ i, s i) = univ := infi_of_empty _

lemma union_eq_Union {s₁ s₂ : set α} : s₁ ∪ s₂ = ⋃ b : bool, cond b s₁ s₂ :=
sup_eq_supr s₁ s₂

lemma inter_eq_Inter {s₁ s₂ : set α} : s₁ ∩ s₂ = ⋂ b : bool, cond b s₁ s₂ :=
inf_eq_infi s₁ s₂

lemma sInter_union_sInter {S T : set (set α)} :
  (⋂₀ S) ∪ (⋂₀ T) = (⋂ p ∈ S ×ˢ T, (p : (set α) × (set α)).1 ∪ p.2) :=
Inf_sup_Inf

lemma sUnion_inter_sUnion {s t : set (set α)} :
  (⋃₀ s) ∩ (⋃₀ t) = (⋃ p ∈ s ×ˢ t, (p : (set α) × (set α )).1 ∩ p.2) :=
Sup_inf_Sup

lemma bUnion_Union (s : ι → set α) (t : α → set β) :
  (⋃ x ∈ ⋃ i, s i, t x) = ⋃ i (x ∈ s i), t x :=
by simp [@Union_comm _ ι]

lemma bInter_Union (s : ι → set α) (t : α → set β) :
  (⋂ x ∈ ⋃ i, s i, t x) = ⋂ i (x ∈ s i), t x :=
by simp [@Inter_comm _ ι]

lemma sUnion_Union (s : ι → set (set α)) : ⋃₀ (⋃ i, s i) = ⋃ i, ⋃₀ (s i) :=
by simp only [sUnion_eq_bUnion, bUnion_Union]

theorem sInter_Union (s : ι → set (set α)) : ⋂₀ (⋃ i, s i) = ⋂ i, ⋂₀ s i :=
by simp only [sInter_eq_bInter, bInter_Union]

lemma Union_range_eq_sUnion {α β : Type*} (C : set (set α))
  {f : ∀ (s : C), β → s} (hf : ∀ (s : C), surjective (f s)) :
  (⋃ (y : β), range (λ (s : C), (f s y).val)) = ⋃₀ C :=
begin
  ext x, split,
  { rintro ⟨s, ⟨y, rfl⟩, ⟨s, hs⟩, rfl⟩, refine ⟨_, hs, _⟩, exact (f ⟨s, hs⟩ y).2 },
  { rintro ⟨s, hs, hx⟩, cases hf ⟨s, hs⟩ ⟨x, hx⟩ with y hy, refine ⟨_, ⟨y, rfl⟩, ⟨s, hs⟩, _⟩,
    exact congr_arg subtype.val hy }
end

lemma Union_range_eq_Union (C : ι → set α) {f : ∀ (x : ι), β → C x}
  (hf : ∀ (x : ι), surjective (f x)) :
  (⋃ (y : β), range (λ (x : ι), (f x y).val)) = ⋃ x, C x :=
begin
  ext x, rw [mem_Union, mem_Union], split,
  { rintro ⟨y, i, rfl⟩, exact ⟨i, (f i y).2⟩ },
  { rintro ⟨i, hx⟩, cases hf i ⟨x, hx⟩ with y hy,
    exact ⟨y, i, congr_arg subtype.val hy⟩ }
end

lemma union_distrib_Inter_left (s : ι → set α) (t : set α) : t ∪ (⋂ i, s i) = (⋂ i, t ∪ s i) :=
sup_infi_eq _ _

lemma union_distrib_Inter₂_left (s : set α) (t : Π i, κ i → set α) :
  s ∪ (⋂ i j, t i j) = ⋂ i j, s ∪ t i j :=
by simp_rw union_distrib_Inter_left

lemma union_distrib_Inter_right (s : ι → set α) (t : set α) : (⋂ i, s i) ∪ t = (⋂ i, s i ∪ t) :=
infi_sup_eq _ _

lemma union_distrib_Inter₂_right (s : Π i, κ i → set α) (t : set α) :
  (⋂ i j, s i j) ∪ t = ⋂ i j, s i j ∪ t :=
by simp_rw union_distrib_Inter_right


section function

/-! ### `maps_to` -/

lemma maps_to_sUnion {S : set (set α)} {t : set β} {f : α → β} (H : ∀ s ∈ S, maps_to f s t) :
  maps_to f (⋃₀ S) t :=
λ x ⟨s, hs, hx⟩, H s hs hx

lemma maps_to_Union {s : ι → set α} {t : set β} {f : α → β} (H : ∀ i, maps_to f (s i) t) :
  maps_to f (⋃ i, s i) t :=
maps_to_sUnion $ forall_range_iff.2 H

lemma maps_to_Union₂ {s : Π i, κ i → set α} {t : set β} {f : α → β}
  (H : ∀ i j, maps_to f (s i j) t) :
  maps_to f (⋃ i j, s i j) t :=
maps_to_Union $ λ i, maps_to_Union (H i)

lemma maps_to_Union_Union {s : ι → set α} {t : ι → set β} {f : α → β}
  (H : ∀ i, maps_to f (s i) (t i)) :
  maps_to f (⋃ i, s i) (⋃ i, t i) :=
maps_to_Union $ λ i, (H i).mono (subset.refl _) (subset_Union t i)

lemma maps_to_Union₂_Union₂ {s : Π i, κ i → set α} {t : Π i, κ i → set β} {f : α → β}
  (H : ∀ i j, maps_to f (s i j) (t i j)) :
  maps_to f (⋃ i j, s i j) (⋃ i j, t i j) :=
maps_to_Union_Union $ λ i, maps_to_Union_Union (H i)

lemma maps_to_sInter {s : set α} {T : set (set β)} {f : α → β} (H : ∀ t ∈ T, maps_to f s t) :
  maps_to f s (⋂₀ T) :=
λ x hx t ht, H t ht hx

lemma maps_to_Inter {s : set α} {t : ι → set β} {f : α → β} (H : ∀ i, maps_to f s (t i)) :
  maps_to f s (⋂ i, t i) :=
λ x hx, mem_Inter.2 $ λ i, H i hx

lemma maps_to_Inter₂ {s : set α} {t : Π i, κ i → set β} {f : α → β}
  (H : ∀ i j, maps_to f s (t i j)) :
  maps_to f s (⋂ i j, t i j) :=
maps_to_Inter $ λ i, maps_to_Inter (H i)

lemma maps_to_Inter_Inter {s : ι → set α} {t : ι → set β} {f : α → β}
  (H : ∀ i, maps_to f (s i) (t i)) :
  maps_to f (⋂ i, s i) (⋂ i, t i) :=
maps_to_Inter $ λ i, (H i).mono (Inter_subset s i) (subset.refl _)

lemma maps_to_Inter₂_Inter₂ {s : Π i, κ i → set α} {t : Π i, κ i → set β} {f : α → β}
  (H : ∀ i j, maps_to f (s i j) (t i j)) :
  maps_to f (⋂ i j, s i j) (⋂ i j, t i j) :=
maps_to_Inter_Inter $ λ i, maps_to_Inter_Inter (H i)

lemma image_Inter_subset (s : ι → set α) (f : α → β) :
  f '' (⋂ i, s i) ⊆ ⋂ i, f '' (s i) :=
(maps_to_Inter_Inter $ λ i, maps_to_image f (s i)).image_subset

lemma image_Inter₂_subset (s : Π i, κ i → set α) (f : α → β) :
  f '' (⋂ i j, s i j) ⊆ ⋂ i j, f '' s i j :=
(maps_to_Inter₂_Inter₂ $ λ i hi, maps_to_image f (s i hi)).image_subset

lemma image_sInter_subset (S : set (set α)) (f : α → β) :
  f '' (⋂₀ S) ⊆ ⋂ s ∈ S, f '' s :=
by { rw sInter_eq_bInter, apply image_Inter₂_subset }

/-! ### `restrict_preimage` -/
section

open function

variables (s : set β) {f : α → β} {U : ι → set β} (hU : Union U = univ)

include hU

lemma injective_iff_injective_of_Union_eq_univ :
  injective f ↔ ∀ i, injective ((U i).restrict_preimage f) :=
begin
  refine ⟨λ H i, (U i).restrict_preimage_injective H, λ H x y e, _⟩,
  obtain ⟨i, hi⟩ := set.mem_Union.mp (show f x ∈ set.Union U, by { rw hU, triv }),
  injection @H i ⟨x, hi⟩ ⟨y, show f y ∈ U i, from e ▸ hi⟩ (subtype.ext e)
end

lemma surjective_iff_surjective_of_Union_eq_univ :
  surjective f ↔ ∀ i, surjective ((U i).restrict_preimage f) :=
begin
  refine ⟨λ H i, (U i).restrict_preimage_surjective H, λ H x, _⟩,
  obtain ⟨i, hi⟩ := set.mem_Union.mp (show x ∈ set.Union U, by { rw hU, triv }),
  exact ⟨_, congr_arg subtype.val (H i ⟨x, hi⟩).some_spec⟩
end

lemma bijective_iff_bijective_of_Union_eq_univ :
  bijective f ↔ ∀ i, bijective ((U i).restrict_preimage f) :=
by simp_rw [bijective, forall_and_distrib, injective_iff_injective_of_Union_eq_univ hU,
  surjective_iff_surjective_of_Union_eq_univ hU]
end

/-! ### `inj_on` -/

lemma inj_on.image_Inter_eq [nonempty ι] {s : ι → set α} {f : α → β} (h : inj_on f (⋃ i, s i)) :
  f '' (⋂ i, s i) = ⋂ i, f '' (s i) :=
begin
  inhabit ι,
  refine subset.antisymm (image_Inter_subset s f) (λ y hy, _),
  simp only [mem_Inter, mem_image_iff_bex] at hy,
  choose x hx hy using hy,
  refine ⟨x default, mem_Inter.2 $ λ i, _, hy _⟩,
  suffices : x default = x i,
  { rw this, apply hx },
  replace hx : ∀ i, x i ∈ ⋃ j, s j := λ i, (subset_Union _ _) (hx i),
  apply h (hx _) (hx _),
  simp only [hy]
end

lemma inj_on.image_bInter_eq {p : ι → Prop} {s : Π i (hi : p i), set α} (hp : ∃ i, p i) {f : α → β}
  (h : inj_on f (⋃ i hi, s i hi)) :
  f '' (⋂ i hi, s i hi) = ⋂ i hi, f '' (s i hi) :=
begin
  simp only [Inter, infi_subtype'],
  haveI : nonempty {i // p i} := nonempty_subtype.2 hp,
  apply inj_on.image_Inter_eq,
  simpa only [Union, supr_subtype'] using h
end

lemma image_Inter {f : α → β} (hf : bijective f) (s : ι → set α) :
  f '' (⋂ i, s i) = ⋂ i, f '' s i :=
begin
  casesI is_empty_or_nonempty ι,
  { simp_rw [Inter_of_empty, image_univ_of_surjective hf.surjective] },
  { exact (hf.injective.inj_on _).image_Inter_eq }
end

lemma image_Inter₂ {f : α → β} (hf : bijective f) (s : Π i, κ i → set α) :
  f '' (⋂ i j, s i j) = ⋂ i j, f '' s i j :=
by simp_rw image_Inter hf

lemma inj_on_Union_of_directed {s : ι → set α} (hs : directed (⊆) s)
  {f : α → β} (hf : ∀ i, inj_on f (s i)) :
  inj_on f (⋃ i, s i) :=
begin
  intros x hx y hy hxy,
  rcases mem_Union.1 hx with ⟨i, hx⟩,
  rcases mem_Union.1 hy with ⟨j, hy⟩,
  rcases hs i j with ⟨k, hi, hj⟩,
  exact hf k (hi hx) (hj hy) hxy
end

/-! ### `surj_on` -/

lemma surj_on_sUnion {s : set α} {T : set (set β)} {f : α → β} (H : ∀ t ∈ T, surj_on f s t) :
  surj_on f s (⋃₀ T) :=
λ x ⟨t, ht, hx⟩, H t ht hx

lemma surj_on_Union {s : set α} {t : ι → set β} {f : α → β} (H : ∀ i, surj_on f s (t i)) :
  surj_on f s (⋃ i, t i) :=
surj_on_sUnion $ forall_range_iff.2 H

lemma surj_on_Union_Union {s : ι → set α} {t : ι → set β} {f : α → β}
  (H : ∀ i, surj_on f (s i) (t i)) :
  surj_on f (⋃ i, s i) (⋃ i, t i) :=
surj_on_Union $ λ i, (H i).mono (subset_Union _ _) (subset.refl _)

lemma surj_on_Union₂ {s : set α} {t : Π i, κ i → set β} {f : α → β}
  (H : ∀ i j, surj_on f s (t i j)) :
  surj_on f s (⋃ i j, t i j) :=
surj_on_Union $ λ i, surj_on_Union (H i)

lemma surj_on_Union₂_Union₂ {s : Π i, κ i → set α} {t : Π i, κ i → set β} {f : α → β}
  (H : ∀ i j, surj_on f (s i j) (t i j)) :
  surj_on f (⋃ i j, s i j) (⋃ i j, t i j) :=
surj_on_Union_Union $ λ i, surj_on_Union_Union (H i)

lemma surj_on_Inter [hi : nonempty ι] {s : ι → set α} {t : set β} {f : α → β}
  (H : ∀ i, surj_on f (s i) t) (Hinj : inj_on f (⋃ i, s i)) :
  surj_on f (⋂ i, s i) t :=
begin
  intros y hy,
  rw [Hinj.image_Inter_eq, mem_Inter],
  exact λ i, H i hy
end

lemma surj_on_Inter_Inter [hi : nonempty ι] {s : ι → set α} {t : ι → set β} {f : α → β}
  (H : ∀ i, surj_on f (s i) (t i)) (Hinj : inj_on f (⋃ i, s i)) :
  surj_on f (⋂ i, s i) (⋂ i, t i) :=
surj_on_Inter (λ i, (H i).mono (subset.refl _) (Inter_subset _ _)) Hinj

/-! ### `bij_on` -/

lemma bij_on_Union {s : ι → set α} {t : ι → set β} {f : α → β} (H : ∀ i, bij_on f (s i) (t i))
  (Hinj : inj_on f (⋃ i, s i)) :
  bij_on f (⋃ i, s i) (⋃ i, t i) :=
⟨maps_to_Union_Union $ λ i, (H i).maps_to, Hinj, surj_on_Union_Union $ λ i, (H i).surj_on⟩

lemma bij_on_Inter [hi :nonempty ι] {s : ι → set α} {t : ι → set β} {f : α → β}
  (H : ∀ i, bij_on f (s i) (t i)) (Hinj : inj_on f (⋃ i, s i)) :
  bij_on f (⋂ i, s i) (⋂ i, t i) :=
⟨maps_to_Inter_Inter $ λ i, (H i).maps_to, hi.elim $ λ i, (H i).inj_on.mono (Inter_subset _ _),
  surj_on_Inter_Inter (λ i, (H i).surj_on) Hinj⟩

lemma bij_on_Union_of_directed {s : ι → set α} (hs : directed (⊆) s) {t : ι → set β} {f : α → β}
  (H : ∀ i, bij_on f (s i) (t i)) :
  bij_on f (⋃ i, s i) (⋃ i, t i) :=
bij_on_Union H $ inj_on_Union_of_directed hs (λ i, (H i).inj_on)

lemma bij_on_Inter_of_directed [nonempty ι] {s : ι → set α} (hs : directed (⊆) s) {t : ι → set β}
  {f : α → β} (H : ∀ i, bij_on f (s i) (t i)) :
  bij_on f (⋂ i, s i) (⋂ i, t i) :=
bij_on_Inter H $ inj_on_Union_of_directed hs (λ i, (H i).inj_on)

end function

/-! ### `image`, `preimage` -/

section image

lemma image_Union {f : α → β} {s : ι → set α} : f '' (⋃ i, s i) = (⋃ i, f '' s i) :=
begin
  ext1 x,
  simp [image, ← exists_and_distrib_right, @exists_swap α]
end

lemma image_Union₂ (f : α → β) (s : Π i, κ i → set α) : f '' (⋃ i j, s i j) = ⋃ i j, f '' s i j :=
by simp_rw image_Union

lemma univ_subtype {p : α → Prop} : (univ : set (subtype p)) = (⋃ x (h : p x), {⟨x, h⟩}) :=
set.ext $ λ ⟨x, h⟩, by simp [h]

lemma range_eq_Union {ι} (f : ι → α) : range f = (⋃ i, {f i}) :=
set.ext $ λ a, by simp [@eq_comm α a]

lemma image_eq_Union (f : α → β) (s : set α) : f '' s = (⋃ i ∈ s, {f i}) :=
set.ext $ λ b, by simp [@eq_comm β b]

lemma bUnion_range {f : ι → α} {g : α → set β} : (⋃ x ∈ range f, g x) = (⋃ y, g (f y)) :=
supr_range

@[simp] lemma Union_Union_eq' {f : ι → α} {g : α → set β} :
  (⋃ x y (h : f y = x), g x) = ⋃ y, g (f y) :=
by simpa using bUnion_range

lemma bInter_range {f : ι → α} {g : α → set β} : (⋂ x ∈ range f, g x) = (⋂ y, g (f y)) :=
infi_range

@[simp] lemma Inter_Inter_eq' {f : ι → α} {g : α → set β} :
  (⋂ x y (h : f y = x), g x) = ⋂ y, g (f y) :=
by simpa using bInter_range

variables {s : set γ} {f : γ → α} {g : α → set β}

lemma bUnion_image : (⋃ x ∈ f '' s, g x) = (⋃ y ∈ s, g (f y)) :=
supr_image

lemma bInter_image : (⋂ x ∈ f '' s, g x) = (⋂ y ∈ s, g (f y)) :=
infi_image

end image

section preimage

theorem monotone_preimage {f : α → β} : monotone (preimage f) := λ a b h, preimage_mono h

@[simp] lemma preimage_Union {f : α → β} {s : ι → set β} : f ⁻¹' (⋃ i, s i) = (⋃ i, f ⁻¹' s i) :=
set.ext $ by simp [preimage]

lemma preimage_Union₂ {f : α → β} {s : Π i, κ i → set β} :
  f ⁻¹' (⋃ i j, s i j) = ⋃ i j, f ⁻¹' s i j :=
by simp_rw preimage_Union

@[simp] theorem preimage_sUnion {f : α → β} {s : set (set β)} :
  f ⁻¹' (⋃₀ s) = (⋃ t ∈ s, f ⁻¹' t) :=
by rw [sUnion_eq_bUnion, preimage_Union₂]

lemma preimage_Inter {f : α → β} {s : ι → set β} : f ⁻¹' (⋂ i, s i) = (⋂ i, f ⁻¹' s i) :=
by ext; simp

lemma preimage_Inter₂ {f : α → β} {s : Π i, κ i → set β} :
  f ⁻¹' (⋂ i j, s i j) = ⋂ i j, f ⁻¹' s i j :=
by simp_rw preimage_Inter

@[simp] lemma preimage_sInter {f : α → β} {s : set (set β)} : f ⁻¹' (⋂₀ s) = ⋂ t ∈ s, f ⁻¹' t :=
by rw [sInter_eq_bInter, preimage_Inter₂]

@[simp] lemma bUnion_preimage_singleton (f : α → β) (s : set β) : (⋃ y ∈ s, f ⁻¹' {y}) = f ⁻¹' s :=
by rw [← preimage_Union₂, bUnion_of_singleton]

lemma bUnion_range_preimage_singleton (f : α → β) : (⋃ y ∈ range f, f ⁻¹' {y}) = univ :=
by rw [bUnion_preimage_singleton, preimage_range]

end preimage

section prod

lemma prod_Union {s : set α} {t : ι → set β} : s ×ˢ (⋃ i, t i) = ⋃ i, s ×ˢ (t i) := by { ext, simp }

lemma prod_Union₂ {s : set α} {t : Π i, κ i → set β} : s ×ˢ (⋃ i j, t i j) = ⋃ i j, s ×ˢ t i j :=
by simp_rw [prod_Union]

lemma prod_sUnion {s : set α} {C : set (set β)} : s ×ˢ (⋃₀ C) = ⋃₀ ((λ t, s ×ˢ t) '' C) :=
by simp_rw [sUnion_eq_bUnion, bUnion_image, prod_Union₂]

lemma Union_prod_const {s : ι → set α} {t : set β} : (⋃ i, s i) ×ˢ t = ⋃ i, s i ×ˢ t :=
by { ext, simp }

lemma Union₂_prod_const {s : Π i, κ i → set α} {t : set β} :
  (⋃ i j, s i j) ×ˢ t = ⋃ i j, s i j ×ˢ t :=
by simp_rw [Union_prod_const]

lemma sUnion_prod_const {C : set (set α)} {t : set β} :
  (⋃₀ C) ×ˢ t = ⋃₀ ((λ s : set α, s ×ˢ t) '' C) :=
by simp only [sUnion_eq_bUnion, Union₂_prod_const, bUnion_image]

lemma Union_prod {ι ι' α β} (s : ι → set α) (t : ι' → set β) :
  (⋃ (x : ι × ι'), s x.1 ×ˢ t x.2) = (⋃ (i : ι), s i) ×ˢ (⋃ (i : ι'), t i) :=
by { ext, simp }

lemma Union_prod_of_monotone [semilattice_sup α] {s : α → set β} {t : α → set γ}
  (hs : monotone s) (ht : monotone t) : (⋃ x, s x ×ˢ t x) = (⋃ x, s x) ×ˢ (⋃ x, t x) :=
begin
  ext ⟨z, w⟩, simp only [mem_prod, mem_Union, exists_imp_distrib, and_imp, iff_def], split,
  { intros x hz hw, exact ⟨⟨x, hz⟩, x, hw⟩ },
  { intros x hz x' hw, exact ⟨x ⊔ x', hs le_sup_left hz, ht le_sup_right hw⟩ }
end

lemma sInter_prod_sInter_subset (S : set (set α)) (T : set (set β)) :
  ⋂₀ S ×ˢ ⋂₀ T ⊆ ⋂ r ∈ S ×ˢ T, r.1 ×ˢ r.2 :=
subset_Inter₂ (λ x hx y hy, ⟨hy.1 x.1 hx.1, hy.2 x.2 hx.2⟩)

lemma sInter_prod_sInter {S : set (set α)} {T : set (set β)} (hS : S.nonempty) (hT : T.nonempty) :
  ⋂₀ S ×ˢ ⋂₀ T = ⋂ r ∈ S ×ˢ T, r.1 ×ˢ r.2 :=
begin
  obtain ⟨s₁, h₁⟩ := hS,
  obtain ⟨s₂, h₂⟩ := hT,
  refine set.subset.antisymm (sInter_prod_sInter_subset S T) (λ x hx, _),
  rw mem_Inter₂ at hx,
  exact ⟨λ s₀ h₀, (hx (s₀, s₂) ⟨h₀, h₂⟩).1, λ s₀ h₀, (hx (s₁, s₀) ⟨h₁, h₀⟩).2⟩,
end

lemma sInter_prod {S : set (set α)} (hS : S.nonempty) (t : set β) :
  ⋂₀ S ×ˢ t = ⋂ s ∈ S, s ×ˢ t :=
begin
  rw [←sInter_singleton t, sInter_prod_sInter hS (singleton_nonempty t), sInter_singleton],
  simp_rw [prod_singleton, mem_image, Inter_exists, bInter_and', Inter_Inter_eq_right],
end

lemma prod_sInter {T : set (set β)} (hT : T.nonempty) (s : set α) :
  s ×ˢ ⋂₀ T = ⋂ t ∈ T, s ×ˢ t :=
begin
  rw [←sInter_singleton s, sInter_prod_sInter (singleton_nonempty s) hT, sInter_singleton],
  simp_rw [singleton_prod, mem_image, Inter_exists, bInter_and', Inter_Inter_eq_right],
end
end prod

section image2

variables (f : α → β → γ) {s : set α} {t : set β}

lemma Union_image_left : (⋃ a ∈ s, f a '' t) = image2 f s t :=
by { ext y, split; simp only [mem_Union]; rintro ⟨a, ha, x, hx, ax⟩; exact ⟨a, x, ha, hx, ax⟩ }

lemma Union_image_right : (⋃ b ∈ t, (λ a, f a b) '' s) = image2 f s t :=
by { ext y, split; simp only [mem_Union]; rintro ⟨a, b, c, d, e⟩, exact ⟨c, a, d, b, e⟩,
     exact ⟨b, d, a, c, e⟩ }

lemma image2_Union_left (s : ι → set α) (t : set β) :
  image2 f (⋃ i, s i) t = ⋃ i, image2 f (s i) t :=
by simp only [← image_prod, Union_prod_const, image_Union]

lemma image2_Union_right (s : set α) (t : ι → set β) :
  image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i) :=
by simp only [← image_prod, prod_Union, image_Union]

lemma image2_Union₂_left (s : Π i, κ i → set α) (t : set β) :
  image2 f (⋃ i j, s i j) t = ⋃ i j, image2 f (s i j) t :=
by simp_rw image2_Union_left

lemma image2_Union₂_right (s : set α) (t : Π i, κ i → set β) :
  image2 f s (⋃ i j, t i j) = ⋃ i j, image2 f s (t i j) :=
by simp_rw image2_Union_right

lemma image2_Inter_subset_left (s : ι → set α) (t : set β) :
  image2 f (⋂ i, s i) t ⊆ ⋂ i, image2 f (s i) t :=
by { simp_rw [image2_subset_iff, mem_Inter], exact λ x hx y hy i, mem_image2_of_mem (hx _) hy }

lemma image2_Inter_subset_right (s : set α) (t : ι → set β) :
  image2 f s (⋂ i, t i) ⊆ ⋂ i, image2 f s (t i) :=
by { simp_rw [image2_subset_iff, mem_Inter], exact λ x hx y hy i, mem_image2_of_mem hx (hy _) }

lemma image2_Inter₂_subset_left (s : Π i, κ i → set α) (t : set β) :
  image2 f (⋂ i j, s i j) t ⊆ ⋂ i j, image2 f (s i j) t :=
by { simp_rw [image2_subset_iff, mem_Inter], exact λ x hx y hy i j, mem_image2_of_mem (hx _ _) hy }

lemma image2_Inter₂_subset_right (s : set α) (t : Π i, κ i → set β) :
  image2 f s (⋂ i j, t i j) ⊆ ⋂ i j, image2 f s (t i j) :=
by { simp_rw [image2_subset_iff, mem_Inter], exact λ x hx y hy i j, mem_image2_of_mem hx (hy _ _) }

/-- The `set.image2` version of `set.image_eq_Union` -/
lemma image2_eq_Union (s : set α) (t : set β) : image2 f s t = ⋃ (i ∈ s) (j ∈ t), {f i j} :=
by simp_rw [←image_eq_Union, Union_image_left]

lemma prod_eq_bUnion_left : s ×ˢ t = ⋃ a ∈ s, (λ b, (a, b)) '' t :=
by rw [Union_image_left, image2_mk_eq_prod]

lemma prod_eq_bUnion_right : s ×ˢ t = ⋃ b ∈ t, (λ a, (a, b)) '' s :=
by rw [Union_image_right, image2_mk_eq_prod]

end image2

section seq

/-- Given a set `s` of functions `α → β` and `t : set α`, `seq s t` is the union of `f '' t` over
all `f ∈ s`. -/
def seq (s : set (α → β)) (t : set α) : set β := {b | ∃ f ∈ s, ∃ a ∈ t, (f : α → β) a = b}

lemma seq_def {s : set (α → β)} {t : set α} : seq s t = ⋃ f ∈ s, f '' t :=
set.ext $ by simp [seq]

@[simp] lemma mem_seq_iff {s : set (α → β)} {t : set α} {b : β} :
  b ∈ seq s t ↔ ∃ (f ∈ s) (a ∈ t), (f : α → β) a = b :=
iff.rfl

lemma seq_subset {s : set (α → β)} {t : set α} {u : set β} :
  seq s t ⊆ u ↔ (∀ f ∈ s, ∀ a ∈ t, (f : α → β) a ∈ u) :=
iff.intro
  (λ h f hf a ha, h ⟨f, hf, a, ha, rfl⟩)
  (λ h b ⟨f, hf, a, ha, eq⟩, eq ▸ h f hf a ha)

lemma seq_mono {s₀ s₁ : set (α → β)} {t₀ t₁ : set α} (hs : s₀ ⊆ s₁) (ht : t₀ ⊆ t₁) :
  seq s₀ t₀ ⊆ seq s₁ t₁ :=
λ b ⟨f, hf, a, ha, eq⟩, ⟨f, hs hf, a, ht ha, eq⟩

lemma singleton_seq {f : α → β} {t : set α} : set.seq {f} t = f '' t :=
set.ext $ by simp

lemma seq_singleton {s : set (α → β)} {a : α} : set.seq s {a} = (λ f : α → β, f a) '' s :=
set.ext $ by simp

lemma seq_seq {s : set (β → γ)} {t : set (α → β)} {u : set α} :
  seq s (seq t u) = seq (seq ((∘) '' s) t) u :=
begin
  refine set.ext (λ c, iff.intro _ _),
  { rintro ⟨f, hfs, b, ⟨g, hg, a, hau, rfl⟩, rfl⟩,
    exact ⟨f ∘ g, ⟨(∘) f, mem_image_of_mem _ hfs, g, hg, rfl⟩, a, hau, rfl⟩ },
  { rintro ⟨fg, ⟨fc, ⟨f, hfs, rfl⟩, g, hgt, rfl⟩, a, ha, rfl⟩,
    exact ⟨f, hfs, g a, ⟨g, hgt, a, ha, rfl⟩, rfl⟩ }
end

lemma image_seq {f : β → γ} {s : set (α → β)} {t : set α} :
  f '' seq s t = seq ((∘) f '' s) t :=
by rw [← singleton_seq, ← singleton_seq, seq_seq, image_singleton]

lemma prod_eq_seq {s : set α} {t : set β} : s ×ˢ t = (prod.mk '' s).seq t :=
begin
  ext ⟨a, b⟩,
  split,
  { rintro ⟨ha, hb⟩, exact ⟨prod.mk a, ⟨a, ha, rfl⟩, b, hb, rfl⟩ },
  { rintro ⟨f, ⟨x, hx, rfl⟩, y, hy, eq⟩, rw ← eq, exact ⟨hx, hy⟩ }
end

lemma prod_image_seq_comm (s : set α) (t : set β) :
  (prod.mk '' s).seq t = seq ((λ b a, (a, b)) '' t) s :=
by rw [← prod_eq_seq, ← image_swap_prod, prod_eq_seq, image_seq, ← image_comp, prod.swap]

lemma image2_eq_seq (f : α → β → γ) (s : set α) (t : set β) : image2 f s t = seq (f '' s) t :=
by { ext, simp }

end seq

section pi

variables {π : α → Type*}

lemma pi_def (i : set α) (s : Π a, set (π a)) :
  pi i s = (⋂ a ∈ i, eval a ⁻¹' s a) :=
by { ext, simp }

lemma univ_pi_eq_Inter (t : Π i, set (π i)) : pi univ t = ⋂ i, eval i ⁻¹' t i :=
by simp only [pi_def, Inter_true, mem_univ]

lemma pi_diff_pi_subset (i : set α) (s t : Π a, set (π a)) :
  pi i s \ pi i t ⊆ ⋃ a ∈ i, (eval a ⁻¹' (s a \ t a)) :=
begin
  refine diff_subset_comm.2 (λ x hx a ha, _),
  simp only [mem_diff, mem_pi, mem_Union, not_exists, mem_preimage, not_and, not_not, eval_apply]
    at hx,
  exact hx.2 _ ha (hx.1 _ ha)
end

lemma Union_univ_pi (t : Π i, ι → set (π i)) :
  (⋃ (x : α → ι), pi univ (λ i, t i (x i))) = pi univ (λ i, ⋃ (j : ι), t i j) :=
by { ext, simp [classical.skolem] }

end pi

end set

namespace function
namespace surjective

lemma Union_comp {f : ι → ι₂} (hf : surjective f) (g : ι₂ → set α) :
  (⋃ x, g (f x)) = ⋃ y, g y :=
hf.supr_comp g

lemma Inter_comp {f : ι → ι₂} (hf : surjective f) (g : ι₂ → set α) :
  (⋂ x, g (f x)) = ⋂ y, g y :=
hf.infi_comp g

end surjective
end function

/-!
### Disjoint sets

We define some lemmas in the `disjoint` namespace to be able to use projection notation.
-/

section disjoint

variables {s t u : set α} {f : α → β}

namespace set

@[simp] theorem disjoint_Union_left {ι : Sort*} {s : ι → set α} :
  disjoint (⋃ i, s i) t ↔ ∀ i, disjoint (s i) t :=
supr_disjoint_iff

@[simp] theorem disjoint_Union_right {ι : Sort*} {s : ι → set α} :
  disjoint t (⋃ i, s i) ↔ ∀ i, disjoint t (s i) :=
disjoint_supr_iff

@[simp] lemma disjoint_Union₂_left {s : Π i, κ i → set α} {t : set α} :
  disjoint (⋃ i j, s i j) t ↔ ∀ i j, disjoint (s i j) t :=
supr₂_disjoint_iff

@[simp] lemma disjoint_Union₂_right {s : set α} {t : Π i, κ i → set α} :
  disjoint s (⋃ i j, t i j) ↔ ∀ i j, disjoint s (t i j) :=
disjoint_supr₂_iff

@[simp] lemma disjoint_sUnion_left {S : set (set α)} {t : set α} :
  disjoint (⋃₀ S) t ↔ ∀ s ∈ S, disjoint s t :=
Sup_disjoint_iff

@[simp] lemma disjoint_sUnion_right {s : set α} {S : set (set α)} :
  disjoint s (⋃₀ S) ↔ ∀ t ∈ S, disjoint s t :=
disjoint_Sup_iff

end set

end disjoint

/-! ### Intervals -/

namespace set
variables [complete_lattice α]

lemma Ici_supr (f : ι → α) : Ici (⨆ i, f i) = ⋂ i, Ici (f i) :=
ext $ λ _, by simp only [mem_Ici, supr_le_iff, mem_Inter]

lemma Iic_infi (f : ι → α) : Iic (⨅ i, f i) = ⋂ i, Iic (f i) :=
ext $ λ _, by simp only [mem_Iic, le_infi_iff, mem_Inter]

lemma Ici_supr₂ (f : Π i, κ i → α) : Ici (⨆ i j, f i j) = ⋂ i j, Ici (f i j) := by simp_rw Ici_supr
lemma Iic_infi₂ (f : Π i, κ i → α) : Iic (⨅ i j, f i j) = ⋂ i j, Iic (f i j) := by simp_rw Iic_infi

lemma Ici_Sup (s : set α) : Ici (Sup s) = ⋂ a ∈ s, Ici a := by rw [Sup_eq_supr, Ici_supr₂]
lemma Iic_Inf (s : set α) : Iic (Inf s) = ⋂ a ∈ s, Iic a := by rw [Inf_eq_infi, Iic_infi₂]

end set

namespace set
variables (t : α → set β)

lemma bUnion_diff_bUnion_subset (s₁ s₂ : set α) :
  (⋃ x ∈ s₁, t x) \ (⋃ x ∈ s₂, t x) ⊆ (⋃ x ∈ s₁ \ s₂, t x) :=
begin
  simp only [diff_subset_iff, ← bUnion_union],
  apply bUnion_subset_bUnion_left,
  rw union_diff_self,
  apply subset_union_right
end

/-- If `t` is an indexed family of sets, then there is a natural map from `Σ i, t i` to `⋃ i, t i`
sending `⟨i, x⟩` to `x`. -/
def sigma_to_Union (x : Σ i, t i) : (⋃ i, t i) := ⟨x.2, mem_Union.2 ⟨x.1, x.2.2⟩⟩

lemma sigma_to_Union_surjective : surjective (sigma_to_Union t)
| ⟨b, hb⟩ := have ∃ a, b ∈ t a, by simpa using hb, let ⟨a, hb⟩ := this in ⟨⟨a, b, hb⟩, rfl⟩

lemma sigma_to_Union_injective (h : ∀ i j, i ≠ j → disjoint (t i) (t j)) :
  injective (sigma_to_Union t)
| ⟨a₁, b₁, h₁⟩ ⟨a₂, b₂, h₂⟩ eq :=
  have b_eq : b₁ = b₂, from congr_arg subtype.val eq,
  have a_eq : a₁ = a₂, from classical.by_contradiction $ λ ne,
    have b₁ ∈ t a₁ ∩ t a₂, from ⟨h₁, b_eq.symm ▸ h₂⟩,
    (h _ _ ne).le_bot this,
  sigma.eq a_eq $ subtype.eq $ by subst b_eq; subst a_eq

lemma sigma_to_Union_bijective (h : ∀ i j, i ≠ j → disjoint (t i) (t j)) :
  bijective (sigma_to_Union t) :=
⟨sigma_to_Union_injective t h, sigma_to_Union_surjective t⟩

/-- Equivalence between a disjoint union and a dependent sum. -/
noncomputable def Union_eq_sigma_of_disjoint {t : α → set β}
  (h : ∀ i j, i ≠ j → disjoint (t i) (t j)) : (⋃ i, t i) ≃ (Σ i, t i) :=
(equiv.of_bijective _ $ sigma_to_Union_bijective t h).symm

lemma Union_ge_eq_Union_nat_add (u : ℕ → set α) (n : ℕ) : (⋃ i ≥ n, u i) = ⋃ i, u (i + n) :=
supr_ge_eq_supr_nat_add u n

lemma Inter_ge_eq_Inter_nat_add (u : ℕ → set α) (n : ℕ) : (⋂ i ≥ n, u i) = ⋂ i, u (i + n) :=
infi_ge_eq_infi_nat_add u n

lemma _root_.monotone.Union_nat_add {f : ℕ → set α} (hf : monotone f) (k : ℕ) :
  (⋃ n, f (n + k)) = ⋃ n, f n :=
hf.supr_nat_add k

lemma _root_.antitone.Inter_nat_add {f : ℕ → set α} (hf : antitone f) (k : ℕ) :
  (⋂ n, f (n + k)) = ⋂ n, f n :=
hf.infi_nat_add k

@[simp] lemma Union_Inter_ge_nat_add (f : ℕ → set α) (k : ℕ) :
  (⋃ n, ⋂ i ≥ n, f (i + k)) = ⋃ n, ⋂ i ≥ n, f i :=
supr_infi_ge_nat_add f k

lemma union_Union_nat_succ (u : ℕ → set α) : u 0 ∪ (⋃ i, u (i + 1)) = ⋃ i, u i :=
sup_supr_nat_succ u

lemma inter_Inter_nat_succ (u : ℕ → set α) : u 0 ∩ (⋂ i, u (i + 1)) = ⋂ i, u i :=
inf_infi_nat_succ u

end set

open set

variables [complete_lattice β]

lemma supr_Union (s : ι → set α) (f : α → β) : (⨆ a ∈ (⋃ i, s i), f a) = ⨆ i (a ∈ s i), f a :=
by { rw supr_comm, simp_rw [mem_Union, supr_exists] }

lemma infi_Union (s : ι → set α) (f : α → β) : (⨅ a ∈ (⋃ i, s i), f a) = ⨅ i (a ∈ s i), f a :=
@supr_Union α βᵒᵈ _ _ s f

lemma Sup_sUnion (s : set (set β)) : Sup (⋃₀ s) = ⨆ t ∈ s, Sup t :=
by simp only [sUnion_eq_bUnion, Sup_eq_supr, supr_Union]

lemma Inf_sUnion (s : set (set β)) : Inf (⋃₀ s) = ⨅ t ∈ s, Inf t := @Sup_sUnion βᵒᵈ _ _
