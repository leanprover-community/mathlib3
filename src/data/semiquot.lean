/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.set.lattice

/-! # Semiquotients

A data type for semiquotients, which are classically equivalent to
nonempty sets, but are useful for programming; the idea is that
a semiquotient set `S` represents some (particular but unknown)
element of `S`. This can be used to model nondeterministic functions,
which return something in a range of values (represented by the
predicate `S`) but are not completely determined.
-/

/-- A member of `semiquot α` is classically a nonempty `set α`,
  and in the VM is represented by an element of `α`; the relation
  between these is that the VM element is required to be a member
  of the set `s`. The specific element of `s` that the VM computes
  is hidden by a quotient construction, allowing for the representation
  of nondeterministic functions. -/
structure {u} semiquot (α : Type*) := mk' ::
(s : set α)
(val : trunc ↥s)

namespace semiquot
variables {α : Type*} {β : Type*}

instance : has_mem α (semiquot α) := ⟨λ a q, a ∈ q.s⟩

/-- Construct a `semiquot α` from `h : a ∈ s` where `s : set α`. -/
def mk {a : α} {s : set α} (h : a ∈ s) : semiquot α :=
⟨s, trunc.mk ⟨a, h⟩⟩

theorem ext_s {q₁ q₂ : semiquot α} : q₁ = q₂ ↔ q₁.s = q₂.s :=
⟨congr_arg _,
 λ h, by cases q₁; cases q₂; congr; exact h⟩

theorem ext {q₁ q₂ : semiquot α} : q₁ = q₂ ↔ ∀ a, a ∈ q₁ ↔ a ∈ q₂ :=
ext_s.trans set.ext_iff

theorem exists_mem (q : semiquot α) : ∃ a, a ∈ q :=
let ⟨⟨a, h⟩, h₂⟩ := q.2.exists_rep in ⟨a, h⟩

theorem eq_mk_of_mem {q : semiquot α} {a : α} (h : a ∈ q) :
  q = @mk _ a q.1 h := ext_s.2 rfl

theorem nonempty (q : semiquot α) : q.s.nonempty := q.exists_mem

/-- `pure a` is `a` reinterpreted as an unspecified element of `{a}`. -/
protected def pure (a : α) : semiquot α := mk (set.mem_singleton a)

@[simp] theorem mem_pure' {a b : α} : a ∈ semiquot.pure b ↔ a = b :=
set.mem_singleton_iff

/-- Replace `s` in a `semiquot` with a superset. -/
def blur' (q : semiquot α) {s : set α} (h : q.s ⊆ s) : semiquot α :=
⟨s, trunc.lift (λ a : q.s, trunc.mk ⟨a.1, h a.2⟩)
  (λ _ _, trunc.eq _ _) q.2⟩

/-- Replace `s` in a `q : semiquot α` with a union `s ∪ q.s` -/
def blur (s : set α) (q : semiquot α) : semiquot α :=
blur' q (set.subset_union_right s q.s)

theorem blur_eq_blur' (q : semiquot α) (s : set α) (h : q.s ⊆ s) :
  blur s q = blur' q h :=
by unfold blur; congr; exact set.union_eq_self_of_subset_right h

@[simp] theorem mem_blur' (q : semiquot α) {s : set α} (h : q.s ⊆ s)
  {a : α} : a ∈ blur' q h ↔ a ∈ s := iff.rfl

/-- Convert a `trunc α` to a `semiquot α`. -/
def of_trunc (q : trunc α) : semiquot α :=
⟨set.univ, q.map (λ a, ⟨a, trivial⟩)⟩

/-- Convert a `semiquot α` to a `trunc α`. -/
def to_trunc (q : semiquot α) : trunc α :=
q.2.map subtype.val

/-- If `f` is a constant on `q.s`, then `q.lift_on f` is the value of `f`
at any point of `q`. -/
def lift_on (q : semiquot α) (f : α → β) (h : ∀ a b ∈ q, f a = f b) : β :=
trunc.lift_on q.2 (λ x, f x.1) (λ x y, h _ _ x.2 y.2)

theorem lift_on_of_mem (q : semiquot α)
  (f : α → β) (h : ∀ a b ∈ q, f a = f b)
  (a : α) (aq : a ∈ q) : lift_on q f h = f a :=
by revert h; rw eq_mk_of_mem aq; intro; refl

/-- Apply a function to the unknown value stored in a `semiquot α`. -/
def map (f : α → β) (q : semiquot α) : semiquot β :=
⟨f '' q.1, q.2.map (λ x, ⟨f x.1, set.mem_image_of_mem _ x.2⟩)⟩

@[simp] theorem mem_map (f : α → β) (q : semiquot α) (b : β) :
  b ∈ map f q ↔ ∃ a, a ∈ q ∧ f a = b := set.mem_image _ _ _

/-- Apply a function returning a `semiquot` to a `semiquot`. -/
def bind (q : semiquot α) (f : α → semiquot β) : semiquot β :=
⟨⋃ a ∈ q.1, (f a).1,
 q.2.bind (λ a, (f a.1).2.map (λ b, ⟨b.1, set.mem_bUnion a.2 b.2⟩))⟩

@[simp] theorem mem_bind (q : semiquot α) (f : α → semiquot β) (b : β) :
  b ∈ bind q f ↔ ∃ a ∈ q, b ∈ f a := set.mem_bUnion_iff

instance : monad semiquot :=
{ pure := @semiquot.pure,
  map := @semiquot.map,
  bind := @semiquot.bind }

@[simp] lemma map_def {β} : ((<$>) : (α → β) → semiquot α → semiquot β) = map := rfl
@[simp] lemma bind_def {β} : ((>>=) : semiquot α → (α → semiquot β) → semiquot β) = bind := rfl

@[simp] theorem mem_pure {a b : α} : a ∈ (pure b : semiquot α) ↔ a = b :=
set.mem_singleton_iff

theorem mem_pure_self (a : α) : a ∈ (pure a : semiquot α) :=
set.mem_singleton a

@[simp] theorem pure_inj {a b : α} : (pure a : semiquot α) = pure b ↔ a = b :=
ext_s.trans set.singleton_eq_singleton_iff

instance : is_lawful_monad semiquot :=
{ pure_bind  := λ α β x f, ext.2 $ by simp,
  bind_assoc := λ α β γ s f g, ext.2 $ by simp; exact
    λ c, ⟨λ ⟨b, ⟨a, as, bf⟩, cg⟩, ⟨a, as, b, bf, cg⟩,
          λ ⟨a, as, b, bf, cg⟩, ⟨b, ⟨a, as, bf⟩, cg⟩⟩,
  id_map     := λ α q, ext.2 $ by simp,
  bind_pure_comp_eq_map := λ α β f s, ext.2 $ by simp [eq_comm] }

instance : has_le (semiquot α) := ⟨λ s t, s.s ⊆ t.s⟩

instance : partial_order (semiquot α) :=
{ le := λ s t, ∀ ⦃x⦄, x ∈ s → x ∈ t,
  le_refl := λ s, set.subset.refl _,
  le_trans := λ s t u, set.subset.trans,
  le_antisymm := λ s t h₁ h₂, ext_s.2 (set.subset.antisymm h₁ h₂) }

instance : semilattice_sup (semiquot α) :=
{ sup := λ s, blur s.s,
  le_sup_left := λ s t, set.subset_union_left _ _,
  le_sup_right := λ s t, set.subset_union_right _ _,
  sup_le := λ s t u, set.union_subset,
  ..semiquot.partial_order }

@[simp] theorem pure_le {a : α} {s : semiquot α} : pure a ≤ s ↔ a ∈ s :=
set.singleton_subset_iff

/-- Assert that a `semiquot` contains only one possible value. -/
def is_pure (q : semiquot α) : Prop := ∀ a b ∈ q, a = b

/-- Extract the value from a `is_pure` semiquotient. -/
def get (q : semiquot α) (h : q.is_pure) : α := lift_on q id h

theorem get_mem {q : semiquot α} (p) : get q p ∈ q :=
let ⟨a, h⟩ := exists_mem q in
by unfold get; rw lift_on_of_mem q _ _ a h; exact h

theorem eq_pure {q : semiquot α} (p) : q = pure (get q p) :=
ext.2 $ λ a, by simp; exact
⟨λ h, p _ _ h (get_mem _), λ e, e.symm ▸ get_mem _⟩

@[simp] theorem pure_is_pure (a : α) : is_pure (pure a)
| b c ab ac := by { simp at ab ac, cc }

theorem is_pure_iff {s : semiquot α} : is_pure s ↔ ∃ a, s = pure a :=
⟨λ h, ⟨_, eq_pure h⟩, λ ⟨a, e⟩, e.symm ▸ pure_is_pure _⟩

theorem is_pure.mono {s t : semiquot α}
  (st : s ≤ t) (h : is_pure t) : is_pure s
| a b as bs := h _ _ (st as) (st bs)

theorem is_pure.min {s t : semiquot α} (h : is_pure t) : s ≤ t ↔ s = t :=
⟨λ st, le_antisymm st $ by rw [eq_pure h, eq_pure (h.mono st)]; simp;
   exact h _ _ (get_mem _) (st $ get_mem _),
 le_of_eq⟩

theorem is_pure_of_subsingleton [subsingleton α] (q : semiquot α) : is_pure q
| a b aq bq := subsingleton.elim _ _

/-- `univ : semiquot α` represents an unspecified element of `univ : set α`. -/
def univ [inhabited α] : semiquot α :=
mk $ set.mem_univ (default _)

instance [inhabited α] : inhabited (semiquot α) := ⟨univ⟩

@[simp] theorem mem_univ [inhabited α] : ∀ a, a ∈ @univ α _ :=
@set.mem_univ α

@[congr] theorem univ_unique (I J : inhabited α) : @univ _ I = @univ _ J :=
ext.2 $ by simp

@[simp] theorem is_pure_univ [inhabited α] : @is_pure α univ ↔ subsingleton α :=
⟨λ h, ⟨λ a b, h a b trivial trivial⟩, λ ⟨h⟩ a b _ _, h a b⟩

instance [inhabited α] : order_top (semiquot α) :=
{ top := univ,
  le_top := λ s, set.subset_univ _,
  ..semiquot.partial_order }

instance [inhabited α] : semilattice_sup_top (semiquot α) :=
{ ..semiquot.order_top,
  ..semiquot.semilattice_sup }

end semiquot
