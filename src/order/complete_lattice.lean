/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.bool.set
import data.nat.basic
import order.bounds

/-!
# Theory of complete lattices

## Main definitions

* `Sup` and `Inf` are the supremum and the infimum of a set;
* `supr (f : ι → α)` and `infi (f : ι → α)` are indexed supremum and infimum of a function,
  defined as `Sup` and `Inf` of the range of this function;
* `class complete_lattice`: a bounded lattice such that `Sup s` is always the least upper boundary
  of `s` and `Inf s` is always the greatest lower boundary of `s`;
* `class complete_linear_order`: a linear ordered complete lattice.

## Naming conventions

In lemma names,
* `Sup` is called `Sup`
* `Inf` is called `Inf`
* `⨆ i, s i` is called `supr`
* `⨅ i, s i` is called `infi`
* `⨆ i j, s i j` is called `supr₂`. This is a `supr` inside a `supr`.
* `⨅ i j, s i j` is called `infi₂`. This is an `infi` inside an `infi`.
* `⨆ i ∈ s, t i` is called `bsupr` for "bounded `supr`". This is the special case of `supr₂`
  where `j : i ∈ s`.
* `⨅ i ∈ s, t i` is called `binfi` for "bounded `infi`". This is the special case of `infi₂`
  where `j : i ∈ s`.

## Notation

* `⨆ i, f i` : `supr f`, the supremum of the range of `f`;
* `⨅ i, f i` : `infi f`, the infimum of the range of `f`.
-/

set_option old_structure_cmd true
open set function

variables {α β β₂ : Type*} {ι ι' : Sort*} {κ : ι → Sort*} {κ' : ι' → Sort*}

/-- class for the `Sup` operator -/
class has_Sup (α : Type*) := (Sup : set α → α)
/-- class for the `Inf` operator -/
class has_Inf (α : Type*) := (Inf : set α → α)

export has_Sup (Sup) has_Inf (Inf)

/-- Supremum of a set -/
add_decl_doc has_Sup.Sup
/-- Infimum of a set -/
add_decl_doc has_Inf.Inf

/-- Indexed supremum -/
def supr [has_Sup α] {ι} (s : ι → α) : α := Sup (range s)
/-- Indexed infimum -/
def infi [has_Inf α] {ι} (s : ι → α) : α := Inf (range s)

@[priority 50] instance has_Inf_to_nonempty (α) [has_Inf α] : nonempty α := ⟨Inf ∅⟩
@[priority 50] instance has_Sup_to_nonempty (α) [has_Sup α] : nonempty α := ⟨Sup ∅⟩

notation `⨆` binders `, ` r:(scoped f, supr f) := r
notation `⨅` binders `, ` r:(scoped f, infi f) := r

instance (α) [has_Inf α] : has_Sup αᵒᵈ := ⟨(Inf : set α → α)⟩
instance (α) [has_Sup α] : has_Inf αᵒᵈ := ⟨(Sup : set α → α)⟩

/--
Note that we rarely use `complete_semilattice_Sup`
(in fact, any such object is always a `complete_lattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
@[ancestor partial_order has_Sup]
class complete_semilattice_Sup (α : Type*) extends partial_order α, has_Sup α :=
(le_Sup : ∀ s, ∀ a ∈ s, a ≤ Sup s)
(Sup_le : ∀ s a, (∀ b ∈ s, b ≤ a) → Sup s ≤ a)

section
variables [complete_semilattice_Sup α] {s t : set α} {a b : α}

@[ematch] theorem le_Sup : a ∈ s → a ≤ Sup s := complete_semilattice_Sup.le_Sup s a

theorem Sup_le : (∀ b ∈ s, b ≤ a) → Sup s ≤ a := complete_semilattice_Sup.Sup_le s a

lemma is_lub_Sup (s : set α) : is_lub s (Sup s) := ⟨λ x, le_Sup, λ x, Sup_le⟩

lemma is_lub.Sup_eq (h : is_lub s a) : Sup s = a := (is_lub_Sup s).unique h

theorem le_Sup_of_le (hb : b ∈ s) (h : a ≤ b) : a ≤ Sup s :=
le_trans h (le_Sup hb)

theorem Sup_le_Sup (h : s ⊆ t) : Sup s ≤ Sup t :=
(is_lub_Sup s).mono (is_lub_Sup t) h

@[simp] theorem Sup_le_iff : Sup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
is_lub_le_iff (is_lub_Sup s)

lemma le_Sup_iff : a ≤ Sup s ↔ ∀ b ∈ upper_bounds s, a ≤ b :=
⟨λ h b hb, le_trans h (Sup_le hb), λ hb, hb _ (λ x, le_Sup)⟩

lemma le_supr_iff {s : ι → α} : a ≤ supr s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b :=
by simp [supr, le_Sup_iff, upper_bounds]

theorem Sup_le_Sup_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) : Sup s ≤ Sup t :=
le_Sup_iff.2 $ λ b hb, Sup_le $ λ a ha, let ⟨c, hct, hac⟩ := h a ha in hac.trans (hb hct)

-- We will generalize this to conditionally complete lattices in `cSup_singleton`.
theorem Sup_singleton {a : α} : Sup {a} = a :=
is_lub_singleton.Sup_eq

end

/--
Note that we rarely use `complete_semilattice_Inf`
(in fact, any such object is always a `complete_lattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
@[ancestor partial_order has_Inf]
class complete_semilattice_Inf (α : Type*) extends partial_order α, has_Inf α :=
(Inf_le : ∀ s, ∀ a ∈ s, Inf s ≤ a)
(le_Inf : ∀ s a, (∀ b ∈ s, a ≤ b) → a ≤ Inf s)


section
variables [complete_semilattice_Inf α] {s t : set α} {a b : α}

@[ematch] theorem Inf_le : a ∈ s → Inf s ≤ a := complete_semilattice_Inf.Inf_le s a

theorem le_Inf : (∀ b ∈ s, a ≤ b) → a ≤ Inf s := complete_semilattice_Inf.le_Inf s a

lemma is_glb_Inf (s : set α) : is_glb s (Inf s) := ⟨λ a, Inf_le, λ a, le_Inf⟩

lemma is_glb.Inf_eq (h : is_glb s a) : Inf s = a := (is_glb_Inf s).unique h

theorem Inf_le_of_le (hb : b ∈ s) (h : b ≤ a) : Inf s ≤ a :=
le_trans (Inf_le hb) h

theorem Inf_le_Inf (h : s ⊆ t) : Inf t ≤ Inf s :=
(is_glb_Inf s).mono (is_glb_Inf t) h

@[simp] theorem le_Inf_iff : a ≤ Inf s ↔ ∀ b ∈ s, a ≤ b :=
le_is_glb_iff (is_glb_Inf s)

lemma Inf_le_iff : Inf s ≤ a ↔ ∀ b ∈ lower_bounds s, b ≤ a :=
⟨λ h b hb, le_trans (le_Inf hb) h, λ hb, hb _ (λ x, Inf_le)⟩

lemma infi_le_iff {s : ι → α} : infi s ≤ a ↔ ∀ b, (∀ i, b ≤ s i) → b ≤ a :=
by simp [infi, Inf_le_iff, lower_bounds]

theorem Inf_le_Inf_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, y ≤ x) : Inf t ≤ Inf s :=
le_of_forall_le begin
  simp only [le_Inf_iff],
  introv h₀ h₁,
  rcases h _ h₁ with ⟨y, hy, hy'⟩,
  solve_by_elim [le_trans _ hy']
end

-- We will generalize this to conditionally complete lattices in `cInf_singleton`.
theorem Inf_singleton {a : α} : Inf {a} = a :=
is_glb_singleton.Inf_eq

end

/-- A complete lattice is a bounded lattice which has suprema and infima for every subset. -/
@[protect_proj, ancestor lattice complete_semilattice_Sup complete_semilattice_Inf has_top has_bot]
class complete_lattice (α : Type*) extends
  lattice α, complete_semilattice_Sup α, complete_semilattice_Inf α, has_top α, has_bot α :=
(le_top : ∀ x : α, x ≤ ⊤)
(bot_le : ∀ x : α, ⊥ ≤ x)

@[priority 100]  -- see Note [lower instance priority]
instance complete_lattice.to_bounded_order [h : complete_lattice α] : bounded_order α :=
{ ..h }

/-- Create a `complete_lattice` from a `partial_order` and `Inf` function
that returns the greatest lower bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `complete_lattice`
instance as
```
instance : complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Sup, bot, top
  ..complete_lattice_of_Inf my_T _ }
```
-/
def complete_lattice_of_Inf (α : Type*) [H1 : partial_order α]
  [H2 : has_Inf α] (is_glb_Inf : ∀ s : set α, is_glb s (Inf s)) :
  complete_lattice α :=
{ bot := Inf univ,
  bot_le := λ x, (is_glb_Inf univ).1 trivial,
  top := Inf ∅,
  le_top := λ a, (is_glb_Inf ∅).2 $ by simp,
  sup := λ a b, Inf {x | a ≤ x ∧ b ≤ x},
  inf := λ a b, Inf {a, b},
  le_inf := λ a b c hab hac, by { apply (is_glb_Inf _).2, simp [*] },
  inf_le_right := λ a b, (is_glb_Inf _).1 $ mem_insert_of_mem _ $ mem_singleton _,
  inf_le_left := λ a b, (is_glb_Inf _).1 $ mem_insert _ _,
  sup_le := λ a b c hac hbc, (is_glb_Inf _).1 $ by simp [*],
  le_sup_left := λ a b, (is_glb_Inf _).2 $ λ x, and.left,
  le_sup_right := λ a b, (is_glb_Inf _).2 $ λ x, and.right,
  le_Inf := λ s a ha, (is_glb_Inf s).2 ha,
  Inf_le := λ s a ha, (is_glb_Inf s).1 ha,
  Sup := λ s, Inf (upper_bounds s),
  le_Sup := λ s a ha, (is_glb_Inf (upper_bounds s)).2 $ λ b hb, hb ha,
  Sup_le := λ s a ha, (is_glb_Inf (upper_bounds s)).1 ha,
  .. H1, .. H2 }

/--
Any `complete_semilattice_Inf` is in fact a `complete_lattice`.

Note that this construction has bad definitional properties:
see the doc-string on `complete_lattice_of_Inf`.
-/
def complete_lattice_of_complete_semilattice_Inf (α : Type*) [complete_semilattice_Inf α] :
  complete_lattice α :=
complete_lattice_of_Inf α (λ s, is_glb_Inf s)

/-- Create a `complete_lattice` from a `partial_order` and `Sup` function
that returns the least upper bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `complete_lattice`
instance as
```
instance : complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Inf, bot, top
  ..complete_lattice_of_Sup my_T _ }
```
-/
def complete_lattice_of_Sup (α : Type*) [H1 : partial_order α]
  [H2 : has_Sup α] (is_lub_Sup : ∀ s : set α, is_lub s (Sup s)) :
  complete_lattice α :=
{ top := Sup univ,
  le_top := λ x, (is_lub_Sup univ).1 trivial,
  bot := Sup ∅,
  bot_le := λ x, (is_lub_Sup ∅).2 $ by simp,
  sup := λ a b, Sup {a, b},
  sup_le := λ a b c hac hbc, (is_lub_Sup _).2 (by simp [*]),
  le_sup_left := λ a b, (is_lub_Sup _).1 $ mem_insert _ _,
  le_sup_right := λ a b, (is_lub_Sup _).1 $ mem_insert_of_mem _ $ mem_singleton _,
  inf := λ a b, Sup {x | x ≤ a ∧ x ≤ b},
  le_inf := λ a b c hab hac, (is_lub_Sup _).1 $ by simp [*],
  inf_le_left := λ a b, (is_lub_Sup _).2 (λ x, and.left),
  inf_le_right := λ a b, (is_lub_Sup _).2 (λ x, and.right),
  Inf := λ s, Sup (lower_bounds s),
  Sup_le := λ s a ha, (is_lub_Sup s).2 ha,
  le_Sup := λ s a ha, (is_lub_Sup s).1 ha,
  Inf_le := λ s a ha, (is_lub_Sup (lower_bounds s)).2 (λ b hb, hb ha),
  le_Inf := λ s a ha, (is_lub_Sup (lower_bounds s)).1 ha,
  .. H1, .. H2 }

/--
Any `complete_semilattice_Sup` is in fact a `complete_lattice`.

Note that this construction has bad definitional properties:
see the doc-string on `complete_lattice_of_Sup`.
-/
def complete_lattice_of_complete_semilattice_Sup (α : Type*) [complete_semilattice_Sup α] :
  complete_lattice α :=
complete_lattice_of_Sup α (λ s, is_lub_Sup s)

/-- A complete linear order is a linear order whose lattice structure is complete. -/
class complete_linear_order (α : Type*) extends complete_lattice α,
  linear_order α renaming max → sup min → inf

namespace order_dual
variable (α)

instance [complete_lattice α] : complete_lattice αᵒᵈ :=
{ le_Sup := @complete_lattice.Inf_le α _,
  Sup_le := @complete_lattice.le_Inf α _,
  Inf_le := @complete_lattice.le_Sup α _,
  le_Inf := @complete_lattice.Sup_le α _,
  .. order_dual.lattice α, ..order_dual.has_Sup α, ..order_dual.has_Inf α,
  .. order_dual.bounded_order α }

instance [complete_linear_order α] : complete_linear_order αᵒᵈ :=
{ .. order_dual.complete_lattice α, .. order_dual.linear_order α }

end order_dual

section
variables [complete_lattice α] {s t : set α} {a b : α}

theorem Inf_le_Sup (hs : s.nonempty) : Inf s ≤ Sup s :=
is_glb_le_is_lub (is_glb_Inf s) (is_lub_Sup s) hs

theorem Sup_union {s t : set α} : Sup (s ∪ t) = Sup s ⊔ Sup t :=
((is_lub_Sup s).union (is_lub_Sup t)).Sup_eq

theorem Sup_inter_le {s t : set α} : Sup (s ∩ t) ≤ Sup s ⊓ Sup t :=
Sup_le $ λ b hb, le_inf (le_Sup hb.1) (le_Sup hb.2)
/-
  Sup_le (λ a ⟨a_s, a_t⟩, le_inf (le_Sup a_s) (le_Sup a_t))
-/

theorem Inf_union {s t : set α} : Inf (s ∪ t) = Inf s ⊓ Inf t :=
((is_glb_Inf s).union (is_glb_Inf t)).Inf_eq

theorem le_Inf_inter {s t : set α} : Inf s ⊔ Inf t ≤ Inf (s ∩ t) := @Sup_inter_le αᵒᵈ _ _ _

@[simp] theorem Sup_empty : Sup ∅ = (⊥ : α) :=
(@is_lub_empty α _ _).Sup_eq

@[simp] theorem Inf_empty : Inf ∅ = (⊤ : α) :=
(@is_glb_empty α _ _).Inf_eq

@[simp] theorem Sup_univ : Sup univ = (⊤ : α) :=
(@is_lub_univ α _ _).Sup_eq

@[simp] theorem Inf_univ : Inf univ = (⊥ : α) :=
(@is_glb_univ α _ _).Inf_eq

-- TODO(Jeremy): get this automatically
@[simp] theorem Sup_insert {a : α} {s : set α} : Sup (insert a s) = a ⊔ Sup s :=
((is_lub_Sup s).insert a).Sup_eq

@[simp] theorem Inf_insert {a : α} {s : set α} : Inf (insert a s) = a ⊓ Inf s :=
((is_glb_Inf s).insert a).Inf_eq

theorem Sup_le_Sup_of_subset_insert_bot (h : s ⊆ insert ⊥ t) : Sup s ≤ Sup t :=
le_trans (Sup_le_Sup h) (le_of_eq (trans Sup_insert bot_sup_eq))

theorem Inf_le_Inf_of_subset_insert_top (h : s ⊆ insert ⊤ t) : Inf t ≤ Inf s :=
le_trans (le_of_eq (trans top_inf_eq.symm Inf_insert.symm)) (Inf_le_Inf h)

theorem Sup_pair {a b : α} : Sup {a, b} = a ⊔ b :=
(@is_lub_pair α _ a b).Sup_eq

theorem Inf_pair {a b : α} : Inf {a, b} = a ⊓ b :=
(@is_glb_pair α _ a b).Inf_eq

@[simp] theorem Inf_eq_top : Inf s = ⊤ ↔ (∀ a ∈ s, a = ⊤) :=
iff.intro
  (λ h a ha, top_unique $ h ▸ Inf_le ha)
  (λ h, top_unique $ le_Inf $ λ a ha, top_le_iff.2 $ h a ha)

lemma eq_singleton_top_of_Inf_eq_top_of_nonempty {s : set α}
  (h_inf : Inf s = ⊤) (hne : s.nonempty) : s = {⊤} :=
by { rw set.eq_singleton_iff_nonempty_unique_mem, rw Inf_eq_top at h_inf, exact ⟨hne, h_inf⟩, }

@[simp] lemma Sup_eq_bot : Sup s = ⊥ ↔ ∀ a ∈ s, a = ⊥ := @Inf_eq_top αᵒᵈ _ _

lemma eq_singleton_bot_of_Sup_eq_bot_of_nonempty {s : set α}
  (h_sup : Sup s = ⊥) (hne : s.nonempty) : s = {⊥} :=
by { rw set.eq_singleton_iff_nonempty_unique_mem, rw Sup_eq_bot at h_sup, exact ⟨hne, h_sup⟩, }

/--Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w < b`.
See `cSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem Sup_eq_of_forall_le_of_forall_lt_exists_gt (_ : ∀a∈s, a ≤ b)
  (H : ∀w, w < b → (∃a∈s, w < a)) : Sup s = b :=
have h : (Sup s < b) ∨ (Sup s = b) := lt_or_eq_of_le (Sup_le ‹∀a∈s, a ≤ b›),
have ¬(Sup s < b) := λ hb,
  let ⟨a, ha, ha'⟩ := H (Sup s) hb in  /- a ∈ s, Sup s < a-/
  have Sup s < Sup s := lt_of_lt_of_le ha' (le_Sup ha),
  show false, from lt_irrefl _ this,
show Sup s = b, from or.resolve_left h this

/--Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w > b`.
See `cInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem Inf_eq_of_forall_ge_of_forall_gt_exists_lt : (∀ a ∈ s, b ≤ a) →
  (∀ w, b < w → (∃ a ∈ s, a < w)) → Inf s = b :=
@Sup_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ ‹_›

end

section complete_linear_order
variables [complete_linear_order α] {s t : set α} {a b : α}

lemma Inf_lt_iff : Inf s < b ↔ ∃ a ∈ s, a < b := is_glb_lt_iff $ is_glb_Inf s
lemma lt_Sup_iff : b < Sup s ↔ ∃ a ∈ s, b < a := lt_is_lub_iff $ is_lub_Sup s

lemma Sup_eq_top : Sup s = ⊤ ↔ (∀ b < ⊤, ∃ a ∈ s, b < a) :=
iff.intro
  (λ (h : Sup s = ⊤) b hb, by rwa [←h, lt_Sup_iff] at hb)
  (λ h, top_unique $ le_of_not_gt $ λ h',
    let ⟨a, ha, h⟩ := h _ h' in
    lt_irrefl a $ lt_of_le_of_lt (le_Sup ha) h)

lemma Inf_eq_bot : Inf s = ⊥ ↔ ∀ b > ⊥, ∃ a ∈ s, a < b := @Sup_eq_top αᵒᵈ _ _

lemma lt_supr_iff {f : ι → α} : a < supr f ↔ ∃ i, a < f i := lt_Sup_iff.trans exists_range_iff
lemma infi_lt_iff {f : ι → α} : infi f < a ↔ ∃ i, f i < a := Inf_lt_iff.trans exists_range_iff

end complete_linear_order

/-
### supr & infi
-/

section has_Sup
variables [has_Sup α] {f g : ι → α}

lemma Sup_range : Sup (range f) = supr f := rfl
lemma Sup_eq_supr' (s : set α) : Sup s = ⨆ a : s, a := by rw [supr, subtype.range_coe]

lemma supr_congr (h : ∀ i, f i = g i) : (⨆ i, f i) = ⨆ i, g i := congr_arg _ $ funext h

lemma function.surjective.supr_comp {f : ι → ι'} (hf : surjective f) (g : ι' → α) :
  (⨆ x, g (f x)) = ⨆ y, g y :=
by simp only [supr, hf.range_comp]

protected lemma function.surjective.supr_congr {g : ι' → α} (h : ι → ι') (h1 : surjective h)
  (h2 : ∀ x, g (h x) = f x) : (⨆ x, f x) = ⨆ y, g y :=
by { convert h1.supr_comp g, exact (funext h2).symm }

@[congr] lemma supr_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
  (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : supr f₁ = supr f₂ :=
begin
  obtain rfl := propext pq,
  congr' with x,
  apply f
end

lemma supr_range' (g : β → α) (f : ι → β) : (⨆ b : range f, g b) = ⨆ i, g (f i) :=
by rw [supr, supr, ← image_eq_range, ← range_comp]

lemma Sup_image' {s : set β} {f : β → α} : Sup (f '' s) = ⨆ a : s, f a :=
by rw [supr, image_eq_range]

end has_Sup

section has_Inf
variables [has_Inf α] {f g : ι → α}

lemma Inf_range : Inf (range f) = infi f := rfl
lemma Inf_eq_infi' (s : set α) : Inf s = ⨅ a : s, a := @Sup_eq_supr' αᵒᵈ _ _

lemma infi_congr (h : ∀ i, f i = g i) : (⨅ i, f i) = ⨅ i, g i := congr_arg _ $ funext h

lemma function.surjective.infi_comp {f : ι → ι'} (hf : surjective f) (g : ι' → α) :
  (⨅ x, g (f x)) = ⨅ y, g y :=
@function.surjective.supr_comp αᵒᵈ _ _  _ f hf g

lemma function.surjective.infi_congr {g : ι' → α} (h : ι → ι') (h1 : surjective h)
  (h2 : ∀ x, g (h x) = f x) : (⨅ x, f x) = ⨅ y, g y :=
@function.surjective.supr_congr αᵒᵈ _ _ _ _ _ h h1 h2

@[congr]lemma infi_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α}
  (pq : p ↔ q) (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : infi f₁ = infi f₂ :=
@supr_congr_Prop αᵒᵈ _ p q f₁ f₂ pq f

lemma infi_range' (g : β → α) (f : ι → β) : (⨅ b : range f, g b) = ⨅ i, g (f i) :=
@supr_range' αᵒᵈ _ _ _ _ _

lemma Inf_image' {s : set β} {f : β → α} : Inf (f '' s) = ⨅ a : s, f a := @Sup_image' αᵒᵈ _ _ _ _

end has_Inf

section
variables [complete_lattice α] {f g s t : ι → α} {a b : α}

-- TODO: this declaration gives error when starting smt state
--@[ematch]
lemma le_supr (f : ι → α) (i : ι) : f i ≤ supr f := le_Sup ⟨i, rfl⟩
lemma infi_le (f : ι → α) (i : ι) : infi f ≤ f i := Inf_le ⟨i, rfl⟩

@[ematch] lemma le_supr' (f : ι → α) (i : ι) : (: f i ≤ supr f :) := le_Sup ⟨i, rfl⟩
@[ematch] lemma infi_le' (f : ι → α) (i : ι) : (: infi f ≤ f i :) := Inf_le ⟨i, rfl⟩

/- TODO: this version would be more powerful, but, alas, the pattern matcher
   doesn't accept it.
@[ematch] lemma le_supr' (f : ι → α) (i : ι) : (: f i :) ≤ (: supr f :) :=
le_Sup ⟨i, rfl⟩
-/

lemma is_lub_supr : is_lub (range f) (⨆ j, f j) := is_lub_Sup _
lemma is_glb_infi : is_glb (range f) (⨅ j, f j) := is_glb_Inf _

lemma is_lub.supr_eq (h : is_lub (range f) a) : (⨆ j, f j) = a := h.Sup_eq
lemma is_glb.infi_eq (h : is_glb (range f) a) : (⨅ j, f j) = a := h.Inf_eq

lemma le_supr_of_le (i : ι) (h : a ≤ f i) : a ≤ supr f := h.trans $ le_supr _ i
lemma infi_le_of_le (i : ι) (h : f i ≤ a) : infi f ≤ a := (infi_le _ i).trans h

lemma le_supr₂ {f : Π i, κ i → α} (i : ι) (j : κ i) : f i j ≤ ⨆ i j, f i j :=
le_supr_of_le i $ le_supr (f i) j

lemma infi₂_le {f : Π i, κ i → α} (i : ι) (j : κ i) : (⨅ i j, f i j) ≤ f i j :=
infi_le_of_le i $ infi_le (f i) j

lemma le_supr₂_of_le {f : Π i, κ i → α} (i : ι) (j : κ i) (h : a ≤ f i j) : a ≤ ⨆ i j, f i j :=
h.trans $ le_supr₂ i j

lemma infi₂_le_of_le {f : Π i, κ i → α} (i : ι) (j : κ i) (h : f i j ≤ a) : (⨅ i j, f i j) ≤ a :=
(infi₂_le i j).trans h

lemma supr_le (h : ∀ i, f i ≤ a) : supr f ≤ a := Sup_le $ λ b ⟨i, eq⟩, eq ▸ h i
lemma le_infi (h : ∀ i, a ≤ f i) : a ≤ infi f := le_Inf $ λ b ⟨i, eq⟩, eq ▸ h i

lemma supr₂_le {f : Π i, κ i → α} (h : ∀ i j, f i j ≤ a) : (⨆ i j, f i j) ≤ a :=
supr_le $ λ i, supr_le $ h i

lemma le_infi₂ {f : Π i, κ i → α} (h : ∀ i j, a ≤ f i j) : a ≤ ⨅ i j, f i j :=
le_infi $ λ i, le_infi $ h i

lemma supr₂_le_supr (κ : ι → Sort*) (f : ι → α) : (⨆ i (j : κ i), f i) ≤ ⨆ i, f i :=
supr₂_le $ λ i j, le_supr f i

lemma infi_le_infi₂ (κ : ι → Sort*) (f : ι → α) : (⨅ i, f i) ≤ ⨅ i (j : κ i), f i :=
le_infi₂ $ λ i j, infi_le f i

lemma supr_mono (h : ∀ i, f i ≤ g i) : supr f ≤ supr g := supr_le $ λ i, le_supr_of_le i $ h i
lemma infi_mono (h : ∀ i, f i ≤ g i) : infi f ≤ infi g := le_infi $ λ i, infi_le_of_le i $ h i

lemma supr₂_mono {f g : Π i, κ i → α} (h : ∀ i j, f i j ≤ g i j) : (⨆ i j, f i j) ≤ ⨆ i j, g i j :=
supr_mono $ λ i, supr_mono $ h i

lemma infi₂_mono {f g : Π i, κ i → α} (h : ∀ i j, f i j ≤ g i j) : (⨅ i j, f i j) ≤ ⨅ i j, g i j :=
infi_mono $ λ i, infi_mono $ h i

lemma supr_mono' {g : ι' → α} (h : ∀ i, ∃ i', f i ≤ g i') : supr f ≤ supr g :=
supr_le $ λ i, exists.elim (h i) le_supr_of_le

lemma infi_mono' {g : ι' → α} (h : ∀ i', ∃ i, f i ≤ g i') : infi f ≤ infi g :=
le_infi $ λ i', exists.elim (h i') infi_le_of_le

lemma supr₂_mono' {f : Π i, κ i → α} {g : Π i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i j ≤ g i' j') :
  (⨆ i j, f i j) ≤ ⨆ i j, g i j :=
supr₂_le $ λ i j, let ⟨i', j', h⟩ := h i j in le_supr₂_of_le i' j' h

lemma infi₂_mono' {f : Π i, κ i → α} {g : Π i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i' j' ≤ g i j) :
  (⨅ i j, f i j) ≤ ⨅ i j, g i j :=
le_infi₂ $ λ i j, let ⟨i', j', h⟩ := h i j in infi₂_le_of_le i' j' h

lemma supr_const_mono (h : ι → ι') : (⨆ i : ι, a) ≤ ⨆ j : ι', a := supr_le $ le_supr _ ∘ h
lemma infi_const_mono (h : ι' → ι) : (⨅ i : ι, a) ≤ ⨅ j : ι', a := le_infi $ infi_le _ ∘ h

lemma bsupr_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
  (⨆ i (h : p i), f i) ≤ ⨆ i (h : q i), f i :=
supr_mono $ λ i, supr_const_mono (hpq i)

lemma binfi_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
  (⨅ i (h : q i), f i) ≤ ⨅ i (h : p i), f i :=
infi_mono $ λ i, infi_const_mono (hpq i)

@[simp] lemma supr_le_iff : supr f ≤ a ↔ ∀ i, f i ≤ a :=
(is_lub_le_iff is_lub_supr).trans forall_range_iff

@[simp] lemma le_infi_iff : a ≤ infi f ↔ ∀ i, a ≤ f i :=
(le_is_glb_iff is_glb_infi).trans forall_range_iff

@[simp] lemma supr₂_le_iff {f : Π i, κ i → α} : (⨆ i j, f i j) ≤ a ↔ ∀ i j, f i j ≤ a :=
by simp_rw supr_le_iff

@[simp] lemma le_infi₂_iff {f : Π i, κ i → α} : a ≤ (⨅ i j, f i j) ↔ ∀ i j, a ≤ f i j :=
by simp_rw le_infi_iff

lemma supr_lt_iff : supr f < a ↔ ∃ b, b < a ∧ ∀ i, f i ≤ b :=
⟨λ h, ⟨supr f, h, le_supr f⟩, λ ⟨b, h, hb⟩, (supr_le hb).trans_lt h⟩

lemma lt_infi_iff : a < infi f ↔ ∃ b, a < b ∧ ∀ i, b ≤ f i :=
⟨λ h, ⟨infi f, h, infi_le f⟩, λ ⟨b, h, hb⟩, h.trans_le $ le_infi hb⟩

lemma Sup_eq_supr {s : set α} : Sup s = ⨆ a ∈ s, a :=
le_antisymm (Sup_le le_supr₂) (supr₂_le $ λ b, le_Sup)

lemma Inf_eq_infi {s : set α} : Inf s = ⨅ a ∈ s, a := @Sup_eq_supr αᵒᵈ _ _

lemma monotone.le_map_supr [complete_lattice β] {f : α → β} (hf : monotone f) :
  (⨆ i, f (s i)) ≤ f (supr s) :=
supr_le $ λ i, hf $ le_supr _ _

lemma monotone.le_map_supr₂ [complete_lattice β] {f : α → β} (hf : monotone f) (s : Π i, κ i → α) :
  (⨆ i j, f (s i j)) ≤ f (⨆ i j, s i j) :=
supr₂_le $ λ i j, hf $ le_supr₂ _ _

lemma monotone.le_map_Sup [complete_lattice β] {s : set α} {f : α → β} (hf : monotone f) :
  (⨆ a ∈ s, f a) ≤ f (Sup s) :=
by rw [Sup_eq_supr]; exact hf.le_map_supr₂ _

lemma antitone.le_map_infi [complete_lattice β] {f : α → β} (hf : antitone f) :
  (⨆ i, f (s i)) ≤ f (infi s) :=
hf.dual_left.le_map_supr

lemma antitone.le_map_infi₂ [complete_lattice β] {f : α → β} (hf : antitone f) (s : Π i, κ i → α) :
  (⨆ i j, f (s i j)) ≤ f (⨅ i j, s i j) :=
hf.dual_left.le_map_supr₂ _

lemma antitone.le_map_Inf [complete_lattice β] {s : set α} {f : α → β} (hf : antitone f) :
  (⨆ a ∈ s, f a) ≤ f (Inf s) :=
hf.dual_left.le_map_Sup

lemma order_iso.map_supr [complete_lattice β] (f : α ≃o β) (x : ι → α) :
  f (⨆ i, x i) = ⨆ i, f (x i) :=
eq_of_forall_ge_iff $ f.surjective.forall.2 $ λ x,
  by simp only [f.le_iff_le, supr_le_iff]

lemma order_iso.map_Sup [complete_lattice β] (f : α ≃o β) (s : set α) :
  f (Sup s) = ⨆ a ∈ s, f a :=
by simp only [Sup_eq_supr, order_iso.map_supr]

lemma supr_comp_le {ι' : Sort*} (f : ι' → α) (g : ι → ι') : (⨆ x, f (g x)) ≤ ⨆ y, f y :=
supr_mono' $ λ x, ⟨_, le_rfl⟩

lemma monotone.supr_comp_eq [preorder β] {f : β → α} (hf : monotone f)
  {s : ι → β} (hs : ∀ x, ∃ i, x ≤ s i) : (⨆ x, f (s x)) = ⨆ y, f y :=
le_antisymm (supr_comp_le _ _) (supr_mono' $ λ x, (hs x).imp $ λ i hi, hf hi)

lemma monotone.map_infi_le [complete_lattice β] {f : α → β} (hf : monotone f) :
  f (infi s) ≤ (⨅ i, f (s i)) :=
le_infi $ λ i, hf $ infi_le _ _

lemma monotone.map_infi₂_le [complete_lattice β] {f : α → β} (hf : monotone f) (s : Π i, κ i → α) :
  f (⨅ i j, s i j) ≤ ⨅ i j, f (s i j) :=
hf.dual.le_map_supr₂ _

lemma monotone.map_Inf_le [complete_lattice β] {s : set α} {f : α → β} (hf : monotone f) :
  f (Inf s) ≤ ⨅ a ∈ s, f a :=
by rw [Inf_eq_infi]; exact hf.map_infi₂_le _

lemma antitone.map_supr_le [complete_lattice β] {f : α → β} (hf : antitone f) :
  f (supr s) ≤ ⨅ i, f (s i) :=
hf.dual_left.map_infi_le

lemma antitone.map_supr₂_le [complete_lattice β] {f : α → β} (hf : antitone f) (s : Π i, κ i → α) :
  f (⨆ i j, s i j) ≤ ⨅ i j, f (s i j) :=
hf.dual_left.map_infi₂_le _

lemma antitone.map_Sup_le [complete_lattice β] {s : set α} {f : α → β} (hf : antitone f) :
  f (Sup s) ≤ ⨅ a ∈ s, f a :=
hf.dual_left.map_Inf_le

lemma order_iso.map_infi [complete_lattice β] (f : α ≃o β) (x : ι → α) :
  f (⨅ i, x i) = ⨅ i, f (x i) :=
order_iso.map_supr f.dual _

lemma order_iso.map_Inf [complete_lattice β] (f : α ≃o β) (s : set α) :
  f (Inf s) = ⨅ a ∈ s, f a :=
order_iso.map_Sup f.dual _

lemma le_infi_comp {ι' : Sort*} (f : ι' → α) (g : ι → ι') : (⨅ y, f y) ≤ ⨅ x, f (g x) :=
infi_mono' $ λ x, ⟨_, le_rfl⟩

lemma monotone.infi_comp_eq [preorder β] {f : β → α} (hf : monotone f)
  {s : ι → β} (hs : ∀ x, ∃ i, s i ≤ x) : (⨅ x, f (s x)) = ⨅ y, f y :=
le_antisymm (infi_mono' $ λ x, (hs x).imp $ λ i hi, hf hi) (le_infi_comp _ _)

lemma supr_const_le {x : α} : (⨆ (h : ι), x) ≤ x :=
supr_le (λ _, le_rfl)

lemma le_infi_const {x : α} : x ≤ (⨅ (h : ι), x) :=
le_infi (λ _, le_rfl)

-- We will generalize this to conditionally complete lattices in `cinfi_const`.
theorem infi_const [nonempty ι] {a : α} : (⨅ b : ι, a) = a :=
by rw [infi, range_const, Inf_singleton]

-- We will generalize this to conditionally complete lattices in `csupr_const`.
theorem supr_const [nonempty ι] {a : α} : (⨆ b : ι, a) = a := @infi_const αᵒᵈ _ _ _ _

@[simp] lemma infi_top : (⨅ i:ι, ⊤ : α) = ⊤ := top_unique $ le_infi $ λ i, le_rfl
@[simp] lemma supr_bot : (⨆ i:ι, ⊥ : α) = ⊥ := @infi_top αᵒᵈ _ _

@[simp] lemma supr_eq_bot : supr s = ⊥ ↔ ∀ i, s i = ⊥ := Sup_eq_bot.trans forall_range_iff
@[simp] lemma infi_eq_top : infi s = ⊤ ↔ ∀ i, s i = ⊤ := Inf_eq_top.trans forall_range_iff

@[simp] lemma supr₂_eq_bot {f : Π i, κ i → α} : (⨆ i j, f i j) = ⊥ ↔ ∀ i j, f i j = ⊥ :=
by simp_rw supr_eq_bot

@[simp] lemma infi₂_eq_top {f : Π i, κ i → α} : (⨅ i j, f i j) = ⊤ ↔ ∀ i j, f i j = ⊤ :=
by simp_rw infi_eq_top

@[simp] lemma supr_pos {p : Prop} {f : p → α} (hp : p) : (⨆ h : p, f h) = f hp :=
le_antisymm (supr_le $ λ h, le_rfl) (le_supr _ _)

@[simp] lemma infi_pos {p : Prop} {f : p → α} (hp : p) : (⨅ h : p, f h) = f hp :=
le_antisymm (infi_le _ _) (le_infi $ λ h, le_rfl)

@[simp] lemma supr_neg {p : Prop} {f : p → α} (hp : ¬ p) : (⨆ h : p, f h) = ⊥ :=
le_antisymm (supr_le $ λ h, (hp h).elim) bot_le

@[simp] lemma infi_neg {p : Prop} {f : p → α} (hp : ¬ p) : (⨅ h : p, f h) = ⊤ :=
le_antisymm le_top $ le_infi $ λ h, (hp h).elim

/--Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `csupr_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem supr_eq_of_forall_le_of_forall_lt_exists_gt {f : ι → α} (h₁ : ∀ i, f i ≤ b)
  (h₂ : ∀ w, w < b → (∃ i, w < f i)) : (⨆ (i : ι), f i) = b :=
Sup_eq_of_forall_le_of_forall_lt_exists_gt (forall_range_iff.mpr h₁)
  (λ w hw, exists_range_iff.mpr $ h₂ w hw)

/--Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `cinfi_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem infi_eq_of_forall_ge_of_forall_gt_exists_lt {f : ι → α} (h₁ : ∀ i, b ≤ f i)
(h₂ : ∀ w, b < w → (∃ i, f i < w)) : (⨅ (i : ι), f i) = b :=
@supr_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _ ‹_› ‹_› ‹_›

lemma supr_eq_dif {p : Prop} [decidable p] (a : p → α) :
  (⨆ h : p, a h) = if h : p then a h else ⊥ :=
by by_cases p; simp [h]

lemma supr_eq_if {p : Prop} [decidable p] (a : α) :
  (⨆ h : p, a) = if p then a else ⊥ :=
supr_eq_dif (λ _, a)

lemma infi_eq_dif {p : Prop} [decidable p] (a : p → α) :
  (⨅ h : p, a h) = if h : p then a h else ⊤ :=
@supr_eq_dif αᵒᵈ _ _ _ _

lemma infi_eq_if {p : Prop} [decidable p] (a : α) :
  (⨅ h : p, a) = if p then a else ⊤ :=
infi_eq_dif (λ _, a)

-- TODO: should this be @[simp]?
lemma supr_comm {f : ι → ι' → α} : (⨆ i j, f i j) = ⨆ j i, f i j :=
le_antisymm
  (supr_le $ λ i, supr_mono $ λ j, le_supr _ i)
  (supr_le $ λ j, supr_mono $ λ i, le_supr _ _)

-- TODO: should this be @[simp]?
lemma infi_comm {f : ι → ι' → α} : (⨅ i j, f i j) = ⨅ j i, f i j := @supr_comm αᵒᵈ _ _ _ _

/- TODO: this is strange. In the proof below, we get exactly the desired
   among the equalities, but close does not get it.
begin
  apply @le_antisymm,
    simp, intros,
    begin [smt]
      ematch, ematch, ematch, trace_state, have := le_refl (f i_1 i),
      trace_state, close
    end
end
-/

@[simp] theorem infi_infi_eq_left {b : β} {f : Π x : β, x = b → α} :
  (⨅ x, ⨅ h : x = b, f x h) = f b rfl :=
le_antisymm
  (infi₂_le _ rfl)
  (le_infi $ λ b', le_infi $ λ eq, match b', eq with ._, rfl := le_rfl end)

@[simp] theorem infi_infi_eq_right {b : β} {f : Π x : β, b = x → α} :
  (⨅ x, ⨅ h : b = x, f x h) = f b rfl :=
le_antisymm
  (infi₂_le _ rfl)
  (le_infi₂ $ λ b' eq, match b', eq with ._, rfl := le_rfl end)

@[simp] theorem supr_supr_eq_left {b : β} {f : Π x : β, x = b → α} :
  (⨆ x, ⨆ h : x = b, f x h) = f b rfl :=
@infi_infi_eq_left αᵒᵈ _ _ _ _

@[simp] theorem supr_supr_eq_right {b : β} {f : Π x : β, b = x → α} :
  (⨆ x, ⨆ h : b = x, f x h) = f b rfl :=
@infi_infi_eq_right αᵒᵈ _ _ _ _

attribute [ematch] le_refl

theorem infi_subtype {p : ι → Prop} {f : subtype p → α} : (⨅ x, f x) = (⨅ i (h : p i), f ⟨i, h⟩) :=
le_antisymm (le_infi₂ $ λ i h, infi_le _ _) (le_infi $ λ ⟨i, h⟩, infi₂_le _ _)

lemma infi_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
  (⨅ i (h : p i), f i h) = (⨅ x : subtype p, f x x.property) :=
(@infi_subtype _ _ _ p (λ x, f x.val x.property)).symm

lemma infi_subtype'' {ι} (s : set ι) (f : ι → α) :
  (⨅ i : s, f i) = ⨅ (t : ι) (H : t ∈ s), f t :=
infi_subtype

theorem infi_inf_eq {f g : ι → α} : (⨅ x, f x ⊓ g x) = (⨅ x, f x) ⊓ (⨅ x, g x) :=
le_antisymm
  (le_inf (infi_mono $ λ i, inf_le_left) $ infi_mono $ λ i, inf_le_right)
  (le_infi $ λ i, inf_le_inf (infi_le _ _) $ infi_le _ _)

/- TODO: here is another example where more flexible pattern matching
   might help.

begin
  apply @le_antisymm,
  safe, pose h := f a ⊓ g a, begin [smt] ematch, ematch  end
end
-/

lemma infi_inf [h : nonempty ι] {f : ι → α} {a : α} : (⨅ x, f x) ⊓ a = (⨅ x, f x ⊓ a) :=
by rw [infi_inf_eq, infi_const]

lemma inf_infi [nonempty ι] {f : ι → α} {a : α} : a ⊓ (⨅ x, f x) = (⨅ x, a ⊓ f x) :=
by rw [inf_comm, infi_inf]; simp [inf_comm]

lemma binfi_inf {p : ι → Prop} {f : Π i (hi : p i), α} {a : α} (h : ∃ i, p i) :
  (⨅ i (h : p i), f i h) ⊓ a = ⨅ i (h : p i), f i h ⊓ a :=
by haveI : nonempty {i // p i} := (let ⟨i, hi⟩ := h in ⟨⟨i, hi⟩⟩);
  rw [infi_subtype', infi_subtype', infi_inf]

lemma inf_binfi {p : ι → Prop} {f : Π i (hi : p i), α} {a : α} (h : ∃ i, p i) :
  a ⊓ (⨅ i (h : p i), f i h) = ⨅ i (h : p i), a ⊓ f i h :=
by simpa only [inf_comm] using binfi_inf h

theorem supr_sup_eq {f g : ι → α} : (⨆ x, f x ⊔ g x) = (⨆ x, f x) ⊔ (⨆ x, g x) :=
@infi_inf_eq αᵒᵈ ι _ _ _

lemma supr_sup [h : nonempty ι] {f : ι → α} {a : α} : (⨆ x, f x) ⊔ a = (⨆ x, f x ⊔ a) :=
@infi_inf αᵒᵈ _ _ _ _ _

lemma sup_supr [nonempty ι] {f : ι → α} {a : α} : a ⊔ (⨆ x, f x) = (⨆ x, a ⊔ f x) :=
@inf_infi αᵒᵈ _ _ _ _ _

/-! ### `supr` and `infi` under `Prop` -/

@[simp] theorem infi_false {s : false → α} : infi s = ⊤ :=
le_antisymm le_top (le_infi $ λ i, false.elim i)

@[simp] theorem supr_false {s : false → α} : supr s = ⊥ :=
le_antisymm (supr_le $ λ i, false.elim i) bot_le

lemma supr_true {s : true → α} : supr s = s trivial := supr_pos trivial
lemma infi_true {s : true → α} : infi s = s trivial := infi_pos trivial

@[simp] lemma infi_exists {p : ι → Prop} {f : Exists p → α} : (⨅ x, f x) = ⨅ i h, f ⟨i, h⟩ :=
le_antisymm (le_infi₂ $ λ i h, infi_le _ _) (le_infi $ λ ⟨i, h⟩, infi₂_le _ _)

@[simp] lemma supr_exists {p : ι → Prop} {f : Exists p → α} : (⨆ x, f x) = ⨆ i h, f ⟨i, h⟩ :=
@infi_exists αᵒᵈ _ _ _ _

lemma infi_and {p q : Prop} {s : p ∧ q → α} : infi s = ⨅ h₁ h₂, s ⟨h₁, h₂⟩ :=
le_antisymm (le_infi₂ $ λ i j, infi_le _ _) (le_infi $ λ ⟨i, h⟩, infi₂_le _ _)

/-- The symmetric case of `infi_and`, useful for rewriting into a infimum over a conjunction -/
lemma infi_and' {p q : Prop} {s : p → q → α} :
  (⨅ (h₁ : p) (h₂ : q), s h₁ h₂) = ⨅ (h : p ∧ q), s h.1 h.2 :=
by { symmetry, exact infi_and }

lemma supr_and {p q : Prop} {s : p ∧ q → α} : supr s = ⨆ h₁ h₂, s ⟨h₁, h₂⟩ := @infi_and αᵒᵈ _ _ _ _

/-- The symmetric case of `supr_and`, useful for rewriting into a supremum over a conjunction -/
lemma supr_and' {p q : Prop} {s : p → q → α} :
  (⨆ (h₁ : p) (h₂ : q), s h₁ h₂) = ⨆ (h : p ∧ q), s h.1 h.2 :=
by { symmetry, exact supr_and }

theorem infi_or {p q : Prop} {s : p ∨ q → α} :
  infi s = (⨅ h : p, s (or.inl h)) ⊓ (⨅ h : q, s (or.inr h)) :=
le_antisymm
  (le_inf (le_infi_comp _ _) $ le_infi_comp _ _)
  (le_infi $ λ i, match i with
  | or.inl i := inf_le_of_left_le $ infi_le _ _
  | or.inr j := inf_le_of_right_le $ infi_le _ _
  end)

theorem supr_or {p q : Prop} {s : p ∨ q → α} :
  (⨆ x, s x) = (⨆ i, s (or.inl i)) ⊔ (⨆ j, s (or.inr j)) :=
@infi_or αᵒᵈ _ _ _ _

section

variables (p : ι → Prop) [decidable_pred p]

lemma supr_dite (f : Π i, p i → α) (g : Π i, ¬p i → α) :
  (⨆ i, if h : p i then f i h else g i h) = (⨆ i (h : p i), f i h) ⊔ (⨆ i (h : ¬ p i), g i h) :=
begin
  rw ←supr_sup_eq,
  congr' 1 with i,
  split_ifs with h;
  simp [h],
end

lemma supr_ite (f g : ι → α) :
  (⨆ i, if p i then f i else g i) = (⨆ i (h : p i), f i) ⊔ (⨆ i (h : ¬ p i), g i) :=
supr_dite _ _ _

lemma infi_dite (f : Π i, p i → α) (g : Π i, ¬p i → α) :
  (⨅ i, if h : p i then f i h else g i h) = (⨅ i (h : p i), f i h) ⊓ (⨅ i (h : ¬ p i), g i h) :=
supr_dite p (show Π i, p i → αᵒᵈ, from f) g

lemma infi_ite (f g : ι → α) :
  (⨅ i, if p i then f i else g i) = (⨅ i (h : p i), f i) ⊓ (⨅ i (h : ¬ p i), g i) :=
infi_dite _ _ _

end

lemma infi_range {g : β → α} {f : ι → β} : (⨅ b ∈ range f, g b) = ⨅ i, g (f i) :=
by rw [← infi_subtype'', infi_range']

lemma supr_range {g : β → α} {f : ι → β} : (⨆ b ∈ range f, g b) = ⨆ i, g (f i) :=
@infi_range αᵒᵈ _ _ _ _ _

theorem Inf_image {s : set β} {f : β → α} : Inf (f '' s) = ⨅ a ∈ s, f a :=
by rw [← infi_subtype'', Inf_image']

theorem Sup_image {s : set β} {f : β → α} : Sup (f '' s) = ⨆ a ∈ s, f a := @Inf_image αᵒᵈ _ _ _ _

/-
### supr and infi under set constructions
-/

theorem infi_emptyset {f : β → α} : (⨅ x ∈ (∅ : set β), f x) = ⊤ :=
by simp

theorem supr_emptyset {f : β → α} : (⨆ x ∈ (∅ : set β), f x) = ⊥ :=
by simp

theorem infi_univ {f : β → α} : (⨅ x ∈ (univ : set β), f x) = (⨅ x, f x) :=
by simp

theorem supr_univ {f : β → α} : (⨆ x ∈ (univ : set β), f x) = (⨆ x, f x) :=
by simp

theorem infi_union {f : β → α} {s t : set β} : (⨅ x ∈ s ∪ t, f x) = (⨅x∈s, f x) ⊓ (⨅x∈t, f x) :=
by simp only [← infi_inf_eq, infi_or]

lemma infi_split (f : β → α) (p : β → Prop) :
  (⨅ i, f i) = (⨅ i (h : p i), f i) ⊓ (⨅ i (h : ¬ p i), f i) :=
by simpa [classical.em] using @infi_union _ _ _ f {i | p i} {i | ¬ p i}

lemma infi_split_single (f : β → α) (i₀ : β) :
  (⨅ i, f i) = f i₀ ⊓ (⨅ i (h : i ≠ i₀), f i) :=
by convert infi_split _ _; simp

theorem infi_le_infi_of_subset {f : β → α} {s t : set β} (h : s ⊆ t) :
  (⨅ x ∈ t, f x) ≤ (⨅ x ∈ s, f x) :=
by rw [(union_eq_self_of_subset_left h).symm, infi_union]; exact inf_le_left

theorem supr_union {f : β → α} {s t : set β} :
  (⨆ x ∈ s ∪ t, f x) = (⨆ x ∈ s, f x) ⊔ (⨆ x ∈ t, f x) :=
@infi_union αᵒᵈ _ _ _ _ _

lemma supr_split (f : β → α) (p : β → Prop) :
  (⨆ i, f i) = (⨆ i (h : p i), f i) ⊔ (⨆ i (h : ¬ p i), f i) :=
@infi_split αᵒᵈ _ _ _ _

lemma supr_split_single (f : β → α) (i₀ : β) :
  (⨆ i, f i) = f i₀ ⊔ (⨆ i (h : i ≠ i₀), f i) :=
@infi_split_single αᵒᵈ _ _ _ _

theorem supr_le_supr_of_subset {f : β → α} {s t : set β} (h : s ⊆ t) :
  (⨆ x ∈ s, f x) ≤ (⨆ x ∈ t, f x) :=
@infi_le_infi_of_subset αᵒᵈ _ _ _ _ _ h

theorem infi_insert {f : β → α} {s : set β} {b : β} :
  (⨅ x ∈ insert b s, f x) = f b ⊓ (⨅ x ∈ s, f x) :=
eq.trans infi_union $ congr_arg (λ x, x ⊓ (⨅ x ∈ s, f x)) infi_infi_eq_left

theorem supr_insert {f : β → α} {s : set β} {b : β} :
  (⨆ x ∈ insert b s, f x) = f b ⊔ (⨆ x ∈ s, f x) :=
eq.trans supr_union $ congr_arg (λ x, x ⊔ (⨆ x ∈ s, f x)) supr_supr_eq_left

theorem infi_singleton {f : β → α} {b : β} : (⨅ x ∈ (singleton b : set β), f x) = f b :=
by simp

theorem infi_pair {f : β → α} {a b : β} : (⨅ x ∈ ({a, b} : set β), f x) = f a ⊓ f b :=
by rw [infi_insert, infi_singleton]

theorem supr_singleton {f : β → α} {b : β} : (⨆ x ∈ (singleton b : set β), f x) = f b :=
@infi_singleton αᵒᵈ _ _ _ _

theorem supr_pair {f : β → α} {a b : β} : (⨆ x ∈ ({a, b} : set β), f x) = f a ⊔ f b :=
by rw [supr_insert, supr_singleton]

lemma infi_image {γ} {f : β → γ} {g : γ → α} {t : set β} :
  (⨅ c ∈ f '' t, g c) = (⨅ b ∈ t, g (f b)) :=
by rw [← Inf_image, ← Inf_image, ← image_comp]

lemma supr_image {γ} {f : β → γ} {g : γ → α} {t : set β} :
  (⨆ c ∈ f '' t, g c) = (⨆ b ∈ t, g (f b)) :=
@infi_image αᵒᵈ _ _ _ _ _ _

theorem supr_extend_bot {e : ι → β} (he : injective e) (f : ι → α) :
  (⨆ j, extend e f ⊥ j) = ⨆ i, f i :=
begin
  rw supr_split _ (λ j, ∃ i, e i = j),
  simp [extend_apply he, extend_apply', @supr_comm _ β ι] { contextual := tt }
end

/-!
### `supr` and `infi` under `Type`
-/

theorem supr_of_empty' {α ι} [has_Sup α] [is_empty ι] (f : ι → α) :
  supr f = Sup (∅ : set α) :=
congr_arg Sup (range_eq_empty f)

theorem supr_of_empty [is_empty ι] (f : ι → α) : supr f = ⊥ :=
(supr_of_empty' f).trans Sup_empty

theorem infi_of_empty' {α ι} [has_Inf α] [is_empty ι] (f : ι → α) :
  infi f = Inf (∅ : set α) :=
congr_arg Inf (range_eq_empty f)

theorem infi_of_empty [is_empty ι] (f : ι → α) : infi f = ⊤ := @supr_of_empty αᵒᵈ _ _ _ f

lemma supr_bool_eq {f : bool → α} : (⨆b:bool, f b) = f tt ⊔ f ff :=
by rw [supr, bool.range_eq, Sup_pair, sup_comm]

lemma infi_bool_eq {f : bool → α} : (⨅b:bool, f b) = f tt ⊓ f ff := @supr_bool_eq αᵒᵈ _ _

lemma sup_eq_supr (x y : α) : x ⊔ y = ⨆ b : bool, cond b x y :=
by rw [supr_bool_eq, bool.cond_tt, bool.cond_ff]

lemma inf_eq_infi (x y : α) : x ⊓ y = ⨅ b : bool, cond b x y := @sup_eq_supr αᵒᵈ _ _ _

lemma is_glb_binfi {s : set β} {f : β → α} : is_glb (f '' s) (⨅ x ∈ s, f x) :=
by simpa only [range_comp, subtype.range_coe, infi_subtype'] using @is_glb_infi α s _ (f ∘ coe)

theorem supr_subtype {p : ι → Prop} {f : subtype p → α} : (⨆ x, f x) = (⨆ i (h:p i), f ⟨i, h⟩) :=
@infi_subtype αᵒᵈ _ _ _ _

lemma supr_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
  (⨆ i (h : p i), f i h) = (⨆ x : subtype p, f x x.property) :=
(@supr_subtype _ _ _ p (λ x, f x.val x.property)).symm

lemma supr_subtype'' {ι} (s : set ι) (f : ι → α) :
  (⨆ i : s, f i) = ⨆ (t : ι) (H : t ∈ s), f t :=
supr_subtype

lemma is_lub_bsupr {s : set β} {f : β → α} : is_lub (f '' s) (⨆ x ∈ s, f x) :=
by simpa only [range_comp, subtype.range_coe, supr_subtype'] using @is_lub_supr α s _ (f ∘ coe)

theorem infi_sigma {p : β → Type*} {f : sigma p → α} : (⨅ x, f x) = (⨅ i (h : p i), f ⟨i, h⟩) :=
eq_of_forall_le_iff $ λ c, by simp only [le_infi_iff, sigma.forall]

theorem supr_sigma {p : β → Type*} {f : sigma p → α} : (⨆ x, f x) = (⨆ i (h : p i), f ⟨i, h⟩) :=
@infi_sigma αᵒᵈ _ _ _ _

theorem infi_prod {γ : Type*} {f : β × γ → α} : (⨅ x, f x) = (⨅ i j, f (i, j)) :=
eq_of_forall_le_iff $ λ c, by simp only [le_infi_iff, prod.forall]

theorem supr_prod {γ : Type*} {f : β × γ → α} : (⨆ x, f x) = (⨆ i j, f (i, j)) :=
@infi_prod αᵒᵈ _ _ _ _

theorem infi_sum {γ : Type*} {f : β ⊕ γ → α} :
  (⨅ x, f x) = (⨅ i, f (sum.inl i)) ⊓ (⨅ j, f (sum.inr j)) :=
eq_of_forall_le_iff $ λ c, by simp only [le_inf_iff, le_infi_iff, sum.forall]

theorem supr_sum {γ : Type*} {f : β ⊕ γ → α} :
  (⨆ x, f x) = (⨆ i, f (sum.inl i)) ⊔ (⨆ j, f (sum.inr j)) :=
@infi_sum αᵒᵈ _ _ _ _

theorem supr_option (f : option β → α) :
  (⨆ o, f o) = f none ⊔ ⨆ b, f (option.some b) :=
eq_of_forall_ge_iff $ λ c, by simp only [supr_le_iff, sup_le_iff, option.forall]

theorem infi_option (f : option β → α) :
  (⨅ o, f o) = f none ⊓ ⨅ b, f (option.some b) :=
@supr_option αᵒᵈ _ _ _

/-- A version of `supr_option` useful for rewriting right-to-left. -/
lemma supr_option_elim (a : α) (f : β → α) : (⨆ o : option β, o.elim a f) = a ⊔ ⨆ b, f b :=
by simp [supr_option]

/-- A version of `infi_option` useful for rewriting right-to-left. -/
lemma infi_option_elim (a : α) (f : β → α) : (⨅ o : option β, o.elim a f) = a ⊓ ⨅ b, f b :=
@supr_option_elim αᵒᵈ _ _ _ _

/-- When taking the supremum of `f : ι → α`, the elements of `ι` on which `f` gives `⊥` can be
dropped, without changing the result. -/
lemma supr_ne_bot_subtype (f : ι → α) : (⨆ i : {i // f i ≠ ⊥}, f i) = ⨆ i, f i :=
begin
  by_cases htriv : ∀ i, f i = ⊥,
  { simp only [htriv, supr_bot] },
  refine le_antisymm (supr_comp_le f _) (supr_mono' _),
  intros i,
  by_cases hi : f i = ⊥,
  { rw hi,
    obtain ⟨i₀, hi₀⟩ := not_forall.mp htriv,
    exact ⟨⟨i₀, hi₀⟩, bot_le⟩ },
  { exact ⟨⟨i, hi⟩, rfl.le⟩ },
end

/-- When taking the infimum of `f : ι → α`, the elements of `ι` on which `f` gives `⊤` can be
dropped, without changing the result. -/
lemma infi_ne_top_subtype (f : ι → α) : (⨅ i : {i // f i ≠ ⊤}, f i) = ⨅ i, f i :=
@supr_ne_bot_subtype αᵒᵈ ι _ f

/-!
### `supr` and `infi` under `ℕ`
-/

lemma supr_ge_eq_supr_nat_add {u : ℕ → α} (n : ℕ) : (⨆ i ≥ n, u i) = ⨆ i, u (i + n) :=
begin
  apply le_antisymm;
  simp only [supr_le_iff],
  { exact λ i hi, le_Sup ⟨i - n, by { dsimp only, rw tsub_add_cancel_of_le hi }⟩ },
  { exact λ i, le_Sup ⟨i + n, supr_pos (nat.le_add_left _ _)⟩ }
end

lemma infi_ge_eq_infi_nat_add {u : ℕ → α} (n : ℕ) : (⨅ i ≥ n, u i) = ⨅ i, u (i + n) :=
@supr_ge_eq_supr_nat_add αᵒᵈ _ _ _

lemma monotone.supr_nat_add {f : ℕ → α} (hf : monotone f) (k : ℕ) :
  (⨆ n, f (n + k)) = ⨆ n, f n :=
le_antisymm (supr_le $ λ i, le_supr _ (i + k)) $ supr_mono $ λ i, hf $ nat.le_add_right i k

@[simp] lemma supr_infi_ge_nat_add (f : ℕ → α) (k : ℕ) :
  (⨆ n, ⨅ i ≥ n, f (i + k)) = ⨆ n, ⨅ i ≥ n, f i :=
begin
  have hf : monotone (λ n, ⨅ i ≥ n, f i) := λ n m h, binfi_mono (λ i, h.trans),
  rw ←monotone.supr_nat_add hf k,
  { simp_rw [infi_ge_eq_infi_nat_add, ←nat.add_assoc], },
end

lemma sup_supr_nat_succ (u : ℕ → α) : u 0 ⊔ (⨆ i, u (i + 1)) = ⨆ i, u i :=
begin
  refine eq_of_forall_ge_iff (λ c, _),
  simp only [sup_le_iff, supr_le_iff],
  refine ⟨λ h, _, λ h, ⟨h _, λ i, h _⟩⟩,
  rintro (_|i),
  exacts [h.1, h.2 i]
end

lemma inf_infi_nat_succ (u : ℕ → α) : u 0 ⊓ (⨅ i, u (i + 1)) = ⨅ i, u i :=
@sup_supr_nat_succ αᵒᵈ _ u

end

section complete_linear_order
variables [complete_linear_order α]

lemma supr_eq_top (f : ι → α) : supr f = ⊤ ↔ (∀ b <⊤, ∃ i, b < f i) :=
by simp only [← Sup_range, Sup_eq_top, set.exists_range_iff]

lemma infi_eq_bot (f : ι → α) : infi f = ⊥ ↔ (∀ b > ⊥, ∃ i, f i < b) :=
by simp only [← Inf_range, Inf_eq_bot, set.exists_range_iff]

end complete_linear_order

/-!
### Instances
-/

instance Prop.complete_lattice : complete_lattice Prop :=
{ Sup    := λ s, ∃ a ∈ s, a,
  le_Sup := λ s a h p, ⟨a, h, p⟩,
  Sup_le := λ s a h ⟨b, h', p⟩, h b h' p,
  Inf    := λ s, ∀ a, a ∈ s → a,
  Inf_le := λ s a h p, p a h,
  le_Inf := λ s a h p b hb, h b hb p,
  .. Prop.bounded_order,
  .. Prop.distrib_lattice }

noncomputable instance Prop.complete_linear_order : complete_linear_order Prop :=
{ ..Prop.complete_lattice, ..Prop.linear_order }

@[simp] lemma Sup_Prop_eq {s : set Prop} : Sup s = ∃ p ∈ s, p := rfl
@[simp] lemma Inf_Prop_eq {s : set Prop} : Inf s = ∀ p ∈ s, p := rfl

@[simp] lemma infi_Prop_eq {p : ι → Prop} : (⨅ i, p i) = ∀ i, p i :=
le_antisymm (λ h i, h _ ⟨i, rfl⟩ ) (λ h p ⟨i, eq⟩, eq ▸ h i)

@[simp] lemma supr_Prop_eq {p : ι → Prop} : (⨆ i, p i) = ∃ i, p i :=
le_antisymm (λ ⟨q, ⟨i, (eq : p i = q)⟩, hq⟩, ⟨i, eq.symm ▸ hq⟩) (λ ⟨i, hi⟩, ⟨p i, ⟨i, rfl⟩, hi⟩)

instance pi.has_Sup {α : Type*} {β : α → Type*} [Π i, has_Sup (β i)] : has_Sup (Π i, β i) :=
⟨λ s i, ⨆ f : s, (f : Π i, β i) i⟩

instance pi.has_Inf {α : Type*} {β : α → Type*} [Π i, has_Inf (β i)] : has_Inf (Π i, β i) :=
⟨λ s i, ⨅ f : s, (f : Π i, β i) i⟩

instance pi.complete_lattice {α : Type*} {β : α → Type*} [∀ i, complete_lattice (β i)] :
  complete_lattice (Π i, β i) :=
{ Sup := Sup,
  Inf := Inf,
  le_Sup := λ s f hf i, le_supr (λ f : s, (f : Π i, β i) i) ⟨f, hf⟩,
  Inf_le := λ s f hf i, infi_le (λ f : s, (f : Π i, β i) i) ⟨f, hf⟩,
  Sup_le := λ s f hf i, supr_le $ λ g, hf g g.2 i,
  le_Inf := λ s f hf i, le_infi $ λ g, hf g g.2 i,
  .. pi.bounded_order,
  .. pi.lattice }

lemma Inf_apply {α : Type*} {β : α → Type*} [Π i, has_Inf (β i)]
  {s : set (Π a, β a)} {a : α} : (Inf s) a = (⨅ f : s, (f : Π a, β a) a) :=
rfl

@[simp] lemma infi_apply {α : Type*} {β : α → Type*} {ι : Sort*} [Π i, has_Inf (β i)]
  {f : ι → Π a, β a} {a : α} : (⨅ i, f i) a = ⨅ i, f i a :=
by rw [infi, Inf_apply, infi, infi, ← image_eq_range (λ f : Π i, β i, f a) (range f), ← range_comp]

lemma Sup_apply {α : Type*} {β : α → Type*} [Π i, has_Sup (β i)] {s : set (Πa, β a)} {a : α} :
  (Sup s) a = (⨆ f : s, (f : Π a, β a) a) :=
rfl

lemma unary_relation_Sup_iff {α : Type*} (s : set (α → Prop)) {a : α} :
  Sup s a ↔ ∃ (r : α → Prop), r ∈ s ∧ r a :=
by { change (∃ _, _) ↔ _, simp [-eq_iff_iff] }

lemma binary_relation_Sup_iff {α β : Type*} (s : set (α → β → Prop)) {a : α} {b : β} :
  Sup s a b ↔ ∃ (r : α → β → Prop), r ∈ s ∧ r a b :=
by { change (∃ _, _) ↔ _, simp [-eq_iff_iff] }

@[simp] lemma supr_apply {α : Type*} {β : α → Type*} {ι : Sort*} [Π i, has_Sup (β i)]
  {f : ι → Π a, β a} {a : α} : (⨆ i, f i) a = (⨆ i, f i a) :=
@infi_apply α (λ i, (β i)ᵒᵈ) _ _ f a

section complete_lattice
variables [preorder α] [complete_lattice β]

theorem monotone_Sup_of_monotone {s : set (α → β)} (m_s : ∀ f ∈ s, monotone f) : monotone (Sup s) :=
λ x y h, supr_mono $ λ f, m_s f f.2 h

theorem monotone_Inf_of_monotone {s : set (α → β)} (m_s : ∀ f ∈ s, monotone f) : monotone (Inf s) :=
λ x y h, infi_mono $ λ f, m_s f f.2 h

end complete_lattice

namespace prod
variables (α β)

instance [has_Inf α] [has_Inf β] : has_Inf (α × β) :=
⟨λs, (Inf (prod.fst '' s), Inf (prod.snd '' s))⟩

instance [has_Sup α] [has_Sup β] : has_Sup (α × β) :=
⟨λs, (Sup (prod.fst '' s), Sup (prod.snd '' s))⟩

instance [complete_lattice α] [complete_lattice β] : complete_lattice (α × β) :=
{ le_Sup := λ s p hab, ⟨le_Sup $ mem_image_of_mem _ hab, le_Sup $ mem_image_of_mem _ hab⟩,
  Sup_le := λ s p h,
    ⟨ Sup_le $ ball_image_of_ball $ λ p hp, (h p hp).1,
      Sup_le $ ball_image_of_ball $ λ p hp, (h p hp).2⟩,
  Inf_le := λ s p hab, ⟨Inf_le $ mem_image_of_mem _ hab, Inf_le $ mem_image_of_mem _ hab⟩,
  le_Inf := λ s p h,
    ⟨ le_Inf $ ball_image_of_ball $ λ p hp, (h p hp).1,
      le_Inf $ ball_image_of_ball $ λ p hp, (h p hp).2⟩,
  .. prod.lattice α β,
  .. prod.bounded_order α β,
  .. prod.has_Sup α β,
  .. prod.has_Inf α β }

end prod

section complete_lattice
variables [complete_lattice α] {a : α} {s : set α}

/-- This is a weaker version of `sup_Inf_eq` -/
lemma sup_Inf_le_infi_sup : a ⊔ Inf s ≤ ⨅ b ∈ s, a ⊔ b :=
le_infi₂ $ λ i h, sup_le_sup_left (Inf_le h) _

/-- This is a weaker version of `Inf_sup_eq` -/
lemma Inf_sup_le_infi_sup : Inf s ⊔ a ≤ ⨅ b ∈ s, b ⊔ a :=
le_infi₂ $ λ i h, sup_le_sup_right (Inf_le h) _

/-- This is a weaker version of `inf_Sup_eq` -/
lemma supr_inf_le_inf_Sup : (⨆ b ∈ s, a ⊓ b) ≤ a ⊓ Sup s :=
supr₂_le $ λ i h, inf_le_inf_left _ (le_Sup h)

/-- This is a weaker version of `Sup_inf_eq` -/
lemma supr_inf_le_Sup_inf : (⨆ b ∈ s, b ⊓ a) ≤ Sup s ⊓ a :=
supr₂_le $ λ i h, inf_le_inf_right _ (le_Sup h)

lemma disjoint_Sup_left {a : set α} {b : α} (d : disjoint (Sup a) b) {i} (hi : i ∈ a) :
  disjoint i b :=
(supr₂_le_iff.1 (supr_inf_le_Sup_inf.trans d) i hi : _)

lemma disjoint_Sup_right {a : set α} {b : α} (d : disjoint b (Sup a)) {i} (hi : i ∈ a) :
  disjoint b i :=
(supr₂_le_iff.mp (supr_inf_le_inf_Sup.trans d) i hi : _)

end complete_lattice

/-- Pullback a `complete_lattice` along an injection. -/
@[reducible] -- See note [reducible non-instances]
protected def function.injective.complete_lattice [has_sup α] [has_inf α] [has_Sup α]
  [has_Inf α] [has_top α] [has_bot α] [complete_lattice β]
  (f : α → β) (hf : function.injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
  (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_Sup : ∀ s, f (Sup s) = ⨆ a ∈ s, f a)
  (map_Inf : ∀ s, f (Inf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
  complete_lattice α :=
{ Sup := Sup,
  le_Sup := λ s a h, (le_supr₂ a h).trans (map_Sup _).ge,
  Sup_le := λ s a h, (map_Sup _).trans_le $ supr₂_le h,
  Inf := Inf,
  Inf_le := λ s a h, (map_Inf _).trans_le $ infi₂_le a h,
  le_Inf := λ s a h, (le_infi₂ h).trans (map_Inf _).ge,
  -- we cannot use bounded_order.lift here as the `has_le` instance doesn't exist yet
  top := ⊤,
  le_top := λ a, (@le_top β _ _ _).trans map_top.ge,
  bot := ⊥,
  bot_le := λ a, map_bot.le.trans bot_le,
  ..hf.lattice f map_sup map_inf }
