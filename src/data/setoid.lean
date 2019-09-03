/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import data.quot order.complete_lattice
/-!
# Setoids
Some definitions relating to setoids, including the complete lattice of setoids on a type.

## Implementation notes
The primed definitions and lemmas make it easier to talk about different setoids on the same type.

## Tags
setoid, equivalence, iseqv, relation
-/
variables {α : Type*} {β : Type*}

namespace setoid

def r' (r : setoid α) := @setoid.r _ r

@[extensionality] lemma ext' {r s : setoid α} (H : ∀ a b, r.r' a b ↔ s.r' a b) : r = s := ext H

def to_set (r : setoid α) : set (α × α) := {x : α × α | @setoid.r _ r x.1 x.2}

instance : has_le (setoid α) := ⟨λ r s, ∀ x y, r.r' x y → s.r' x y⟩
instance : has_mem (α × α) (setoid α) := ⟨λ x r, x ∈ r.to_set⟩

@[refl] lemma refl' (r : setoid α) (x) : r.r' x x := r.2.1 x
@[symm] lemma symm' (r : setoid α) : ∀ {x y}, r.r' x y → r.r' y x := λ _ _ h, r.2.2.1 h
@[trans] lemma trans' (r : setoid α) : ∀ {x y z}, r.r' x y → r.r' y z → r.r' x z := 
λ  _ _ _ hx hy, r.2.2.2 hx hy

def ker (f : α → β) : setoid α :=
⟨λ x y, f x = f y, ⟨λ x, rfl, λ _ _ h, h.symm, λ _ _ _ h1 h2, h1.trans h2⟩⟩ 

variables (α)

def diag : setoid α :=
⟨(=), ⟨λ _, rfl, λ _ _ h, h.symm, λ _ _ _ h1 h2, h1.trans h2⟩⟩

def top : setoid α := 
⟨λ _ _, true, ⟨λ _, trivial, λ _ _ h, h, λ _ _ _ h1 h2, h1⟩⟩

variables {α}

protected def prod (r : setoid α) (s : setoid β) : setoid (α × β) :=
⟨λ x y, r.r' x.1 y.1 ∧ s.r' x.2 y.2,
  ⟨λ x, ⟨r.refl' x.1, s.refl' x.2⟩, λ _ _ h, ⟨r.symm' h.1, s.symm' h.2⟩, 
   λ _ _ _ h1 h2, ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩⟩

def pi {ι : Type*} {f : ι → Type*} (C : Π i, setoid (f i)) : setoid (Π i, f i) :=
{ r := λ x y, ∀ i, (C i).r' (x i) (y i),
  iseqv := ⟨λ x i, (C i).refl' (x i), λ _ _ h i, (C i).symm' (h i),
            λ _ _ _ h1 h2 i, (C i).trans' (h1 i) (h2 i)⟩}

open lattice

instance : partial_order (setoid α) :=
{ le := (≤),
  lt := λ r s, r ≤ s ∧ ¬s ≤ r,
  le_refl := λ r x y h, h,
  le_trans := λ _ _ _ hr hs x y h, hs x y $ hr x y h,
  lt_iff_le_not_le := λ _ _, iff.rfl,
  le_antisymm := λ r s h1 h2, setoid.ext' $ λ x y, ⟨h1 x y, h2 x y⟩ }

instance : has_bot (setoid α) := ⟨diag α⟩

instance : order_bot (setoid α) :=
{ bot := has_bot.bot (setoid α),
  bot_le := λ r x y h, h ▸ r.2.1 x, ..setoid.partial_order }

instance : has_top (setoid α) := ⟨setoid.top α⟩

instance : order_top (setoid α) :=
{ top := has_top.top (setoid α),
  le_top := λ r x y h, trivial,
  ..setoid.partial_order }

instance : has_inf (setoid α) :=
⟨λ r s, ⟨λ x y, r.r' x y ∧ s.r' x y, ⟨λ x, ⟨r.refl' x, s.refl' x⟩, 
 λ x y h, ⟨r.symm' h.1, s.symm' h.2⟩, 
 λ _ _ _ h1 h2, ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩⟩⟩

instance : has_Inf (setoid α) :=
⟨λ S, ⟨λ x y, (∀ r ∈ S, r' r x y), 
⟨λ x r hr, r.refl' x, λ x y h r hr, r.symm' $ h r hr, 
 λ _ _ _ h1 h2 r hr, r.trans' (h1 r hr) $ h2 r hr⟩⟩⟩

lemma Inf_le (S : set (setoid α)) (r∈S) : Inf S ≤ r :=
λ _ _ h, h r H

lemma le_Inf (S : set (setoid α)) (r) : (∀ s∈S, r ≤ s) → r ≤ Inf S :=
λ H _ _ h s hs, H s hs _ _ h

instance : has_sup (setoid α) := ⟨λ r s, Inf { x | r ≤ x ∧ s ≤ x}⟩

instance : complete_lattice (setoid α) :=
{ sup := has_sup.sup,
  le_sup_left := λ r s, le_Inf _ r $ λ _ hx, hx.1,
  le_sup_right := λ r s, le_Inf _ s $ λ _ hx, hx.2,
  sup_le := λ r s t h1 h2, Inf_le _ t ⟨h1, h2⟩,
  inf := has_inf.inf,
  inf_le_left := λ _ _ _ _ h, h.1,
  inf_le_right := λ _ _ _ _ h, h.2,
  le_inf := λ _ _ _ h1 h2 _ _ h, ⟨h1 _ _ h, h2 _ _ h⟩,
  Sup := λ tt, Inf {t | ∀ t'∈tt, t' ≤ t},
  Inf := has_Inf.Inf,
  le_Sup := λ _ _ hs, le_Inf _ _ $ λ r hr, hr _ hs,
  Sup_le := λ _ _ hs, Inf_le _ _ hs,
  Inf_le := Inf_le,
  le_Inf := le_Inf,
  ..setoid.partial_order,
  ..setoid.lattice.order_top, ..setoid.lattice.order_bot}

inductive in_closure (r : α → α → Prop) : α → α → Prop
| of_r : ∀ x y, r x y → in_closure x y
| refl : ∀ x, in_closure x x
| symm : ∀ {x y}, in_closure x y → in_closure y x
| trans : ∀ {x y z}, in_closure x y → in_closure y z → in_closure x z 

def closure (r : α → α → Prop) : setoid α :=
⟨in_closure r, ⟨λ x, in_closure.refl r x, λ _ _, in_closure.symm, λ _ _ _, in_closure.trans⟩⟩ 

theorem closure_eq (r : α → α → Prop) : closure r = Inf {s : setoid α | ∀ x y, r x y → s.r' x y} :=
setoid.ext' $ λ _ _, 
  ⟨λ H, in_closure.rec (λ _ _ h _ hs, hs _ _ h) (setoid.refl' _) 
    (λ _ _ _ h, setoid.symm' _ h) (λ _ _ _ _ _ h1 h2, setoid.trans' _ h1 h2) H, 
  Inf_le _ _ (λ _ _, in_closure.of_r _ _) _ _⟩

lemma sup_eq_closure (r s : setoid α) : r ⊔ s = closure (λ x y, r.r' x y ∨ s.r' x y) :=
by rw closure_eq; apply congr_arg Inf; ext; exact 
  ⟨λ h _ _ H, or.elim H (λ hl, h.1 _ _ hl) $ λ hr, h.2 _ _ hr, 
   λ H, ⟨λ _ _ h, H _ _ $ or.inl h, λ _ _ h, H _ _ $ or.inr h⟩⟩

lemma Sup_eq_closure (S : set (setoid α)) : 
  Sup S = closure (λ x y, ∃ r : setoid α, r∈S ∧ r.r' x y) :=
by rw closure_eq; apply congr_arg Inf; ext;
   exact ⟨λ h _ _ ⟨r, hr⟩, h r hr.1 _ _ hr.2, λ h r hS _ _ hr, h _ _ ⟨r, hS, hr⟩⟩

theorem closure_le {r : α → α → Prop} {s : setoid α} (h : ∀ x y, r x y → s.r' x y) : 
  closure r ≤ s :=
by rw closure_eq; exact Inf_le _ _ h

theorem closure_mono {r s : α → α → Prop} (h : ∀ x y, r x y → s x y) : closure r ≤ closure s :=
closure_le $ λ x y hr, in_closure.of_r _ _ $ h x y hr

end setoid
