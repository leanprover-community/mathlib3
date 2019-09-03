/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import data.quot order.complete_lattice data.equiv.basic order.order_iso order.galois_connection
/-!
# Equivalence relations
Some definitions and results; in particular, the complete lattice of 
equivalence relations an a type, results about the inductively defined equivalence closure
of a binary relation, and the analogues of some isomorphism theorems for quotients of arbitrary 
types.

## Implementation notes
The definitions and lemmas ending in ' are to make it easier to talk about different equivalence 
relations on the same type without adding a coercion instance from setoid α to (α → α → Prop).

## Tags
setoid, equivalence, iseqv, relation, equivalence relation
-/
variables {α : Type*} {β : Type*}

open lattice 

namespace setoid

/-- A version of setoid.r that takes the equivalence relation as an explicit argument. -/
def r' (r : setoid α) := @setoid.r _ r

@[extensionality] lemma ext' {r s : setoid α} (H : ∀ a b, r.r' a b ↔ s.r' a b) : r = s := ext H
lemma ext_iff {r s : setoid α} : r = s ↔ ∀ a b, r.r' a b ↔ s.r' a b :=
⟨λ h a b, h ▸ iff.rfl, ext'⟩

/-- Defining the relation '≤' for equivalence relations. -/
instance : has_le (setoid α) := ⟨λ r s, ∀ x y, r.r' x y → s.r' x y⟩
instance : has_mem (α × α) (setoid α) := ⟨λ x r, r.r' x.1 x.2⟩

@[refl] lemma refl' (r : setoid α) (x) : r.r' x x := r.2.1 x
@[symm] lemma symm' (r : setoid α) : ∀ {x y}, r.r' x y → r.r' y x := λ _ _ h, r.2.2.1 h
@[trans] lemma trans' (r : setoid α) : ∀ {x y z}, r.r' x y → r.r' y z → r.r' x z := 
λ  _ _ _ hx hy, r.2.2.2 hx hy

/-- The kernel of a function is an equivalence relation. -/
def ker (f : α → β) : setoid α :=
⟨λ x y, f x = f y, ⟨λ x, rfl, λ _ _ h, h.symm, λ _ _ _ h1 h2, h1.trans h2⟩⟩ 

/-- The kernel of the quotient map induced by an equivalence relation r equals r. -/
@[simp] lemma ker_mk_eq (r : setoid α) : ker (@quotient.mk _ r) = r :=
ext' $ λ x y, quotient.eq

open lattice

/-- The infimum of two equivalence relations. -/
instance : has_inf (setoid α) :=
⟨λ r s, ⟨λ x y, r.r' x y ∧ s.r' x y, ⟨λ x, ⟨r.refl' x, s.refl' x⟩, 
 λ x y h, ⟨r.symm' h.1, s.symm' h.2⟩, 
 λ _ _ _ h1 h2, ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩⟩⟩

/-- The infimum of a set of equivalence relations. -/
instance : has_Inf (setoid α) :=
⟨λ S, ⟨λ x y, (∀ r ∈ S, r' r x y), 
⟨λ x r hr, r.refl' x, λ x y h r hr, r.symm' $ h r hr, 
 λ _ _ _ h1 h2 r hr, r.trans' (h1 r hr) $ h2 r hr⟩⟩⟩

/-- The infimum of a set of equivalence relations is contained in any element of the set. -/
lemma Inf_le (S : set (setoid α)) (r∈S) : Inf S ≤ r :=
λ _ _ h, h r H

/-- If an equivalence relation r is contained in every element of a set of equivalence relations,
    r is contained in the infimum of the set. -/
lemma le_Inf (S : set (setoid α)) (r) : (∀ s∈S, r ≤ s) → r ≤ Inf S :=
λ H _ _ h s hs, H s hs _ _ h

/-- The supremum of two equivalence relations, defined as the infimum of the set of
    equivalence relations containing both. -/
instance : has_sup (setoid α) := ⟨λ r s, Inf { x | r ≤ x ∧ s ≤ x}⟩

/-- The complete lattice of equivalence relations on a type, with bottom element '='
    and top element the trivial equivalence relation. -/
instance : complete_lattice (setoid α) :=
{ sup := has_sup.sup,
  le := (≤),
  lt := λ r s, r ≤ s ∧ ¬s ≤ r,
  le_refl := λ r x y h, h,
  le_trans := λ _ _ _ hr hs x y h, hs x y $ hr x y h,
  lt_iff_le_not_le := λ _ _, iff.rfl,
  le_antisymm := λ r s h1 h2, setoid.ext' $ λ x y, ⟨h1 x y, h2 x y⟩,
  le_sup_left := λ r s, le_Inf _ r $ λ _ hx, hx.1,
  le_sup_right := λ r s, le_Inf _ s $ λ _ hx, hx.2,
  sup_le := λ r s t h1 h2, Inf_le _ t ⟨h1, h2⟩,
  inf := has_inf.inf,
  inf_le_left := λ _ _ _ _ h, h.1,
  inf_le_right := λ _ _ _ _ h, h.2,
  le_inf := λ _ _ _ h1 h2 _ _ h, ⟨h1 _ _ h, h2 _ _ h⟩,
  top := ⟨λ _ _, true, ⟨λ _, trivial, λ _ _ h, h, λ _ _ _ h1 h2, h1⟩⟩,
  le_top := λ _ _ _ _, trivial,
  bot := ⟨(=), ⟨λ _, rfl, λ _ _ h, h.symm, λ _ _ _ h1 h2, h1.trans h2⟩⟩,
  bot_le := λ r x y h, h ▸ r.2.1 x,
  Sup := λ tt, Inf {t | ∀ t'∈tt, t' ≤ t},
  Inf := has_Inf.Inf,
  le_Sup := λ _ _ hs, le_Inf _ _ $ λ r hr, hr _ hs,
  Sup_le := λ _ _ hs, Inf_le _ _ hs,
  Inf_le := Inf_le,
  le_Inf := le_Inf }

/-- The inductively defined equivalence closure of an arbitrary binary relation r is the infimum 
    of the set of all equivalence relations containing r. -/
theorem eqv_gen_eq (r : α → α → Prop) : 
  eqv_gen.setoid r = Inf {s : setoid α | ∀ x y, r x y → s.r' x y} :=
setoid.ext' $ λ _ _, 
  ⟨λ H, eqv_gen.rec (λ _ _ h _ hs, hs _ _ h) (refl' _) 
    (λ _ _ _ h, symm' _ h) (λ _ _ _ _ _ h1 h2, trans' _ h1 h2) H, 
  Inf_le _ _ (λ _ _, eqv_gen.rel _ _) _ _⟩

/-- The supremum of two equivalence relations r and s is the equivalence closure of the binary
    relation 'x is related to y by r or s'. -/
lemma sup_eq_eqv_gen (r s : setoid α) : r ⊔ s = eqv_gen.setoid (λ x y, r.r' x y ∨ s.r' x y) :=
by rw eqv_gen_eq; apply congr_arg Inf; ext; exact 
  ⟨λ h _ _ H, or.elim H (λ hl, h.1 _ _ hl) $ λ hr, h.2 _ _ hr, 
   λ H, ⟨λ _ _ h, H _ _ $ or.inl h, λ _ _ h, H _ _ $ or.inr h⟩⟩

/-- The supremum of a set S of equivalence relations is the equivalence closure of the binary
    relation 'there exists r ∈ S relating x and y'. -/
lemma Sup_eq_eqv_gen (S : set (setoid α)) : 
  Sup S = eqv_gen.setoid (λ x y, ∃ r : setoid α, r∈S ∧ r.r' x y) :=
by rw eqv_gen_eq; apply congr_arg Inf; ext;
   exact ⟨λ h _ _ ⟨r, hr⟩, h r hr.1 _ _ hr.2, λ h r hS _ _ hr, h _ _ ⟨r, hS, hr⟩⟩

/-- The equivalence closure of an equivalence relation r is r. -/
@[simp] lemma eqv_gen_of_setoid (r : setoid α) : eqv_gen.setoid r.r = r :=
le_antisymm (by rw eqv_gen_eq; exact Inf_le _ r (λ x y h, h)) eqv_gen.rel

/-- Equivalence closure is idempotent. -/
@[simp] lemma eqv_gen_idem (r : α → α → Prop) : 
  eqv_gen.setoid (eqv_gen.setoid r).r' = eqv_gen.setoid r :=
eqv_gen_of_setoid _ 

/-- The equivalence closure of a binary relation r is contained in any equivalence
    relation containing r. -/
theorem eqv_gen_le {r : α → α → Prop} {s : setoid α} (h : ∀ x y, r x y → s.r' x y) : 
  eqv_gen.setoid r ≤ s :=
by rw eqv_gen_eq; exact Inf_le _ _ h

/-- Equivalence closure of binary relations is monotonic. -/
theorem eqv_gen_mono {r s : α → α → Prop} (h : ∀ x y, r x y → s x y) : 
  eqv_gen.setoid r ≤ eqv_gen.setoid s :=
eqv_gen_le $ λ x y hr, eqv_gen.rel _ _ $ h x y hr

open function

/-- A function from α to β is injective iff its kernel is the bottom element of the complete lattice
    of equivalence relations on α. -/
theorem injective_iff_ker_bot (f : α → β) :
  injective f ↔ ker f = ⊥ := 
⟨λ hf, setoid.ext' $ λ x y, ⟨λ h, hf h, λ h, h ▸ rfl⟩, 
 λ hk x y h, show r' ⊥ x y, from hk ▸ (show (ker f).r' x y, from h)⟩

/-- The elements related to x ∈ α by the kernel of f are those in the preimage of f(x) under f. -/
lemma ker_apply_eq_preimage (f : α → β) (x) : (ker f).r' x = f ⁻¹' {f x} :=
set.ext $ λ x,
  ⟨λ h, set.mem_preimage.2 (set.mem_singleton_iff.2 h.symm),
   λ h, (set.mem_singleton_iff.1 (set.mem_preimage.1 h)).symm⟩

/-- The uniqueness part of the universal property for quotients of an arbitrary type. -/
theorem lift_unique {r : setoid α} {f : α → β} (H : r ≤ ker f) (g : quotient r → β)
  (Hg : f = g ∘ quotient.mk) : quotient.lift f H = g :=
by ext; rcases x; erw [quotient.lift_beta f H, Hg]; refl

/-- Given a map f from α to β, the natural map from the quotient of α by the kernel of f is 
    injective. -/
lemma injective_ker_lift (f : α → β) : injective (@quotient.lift _ _ (ker f) f (λ _ _ h, h)) :=
λ x y, by apply quotient.induction_on₂' x y; intros a b; show (ker f).r' a b → _; from quotient.sound'

/-- Given a map f from α to β, the kernel of f is the unique equivalence relation on α whose
    induced map from the quotient of α to β is injective. -/
lemma ker_eq_lift_injective {r : setoid α} (f : α → β) (H : ∀ x y, r.r' x y → f x = f y) 
  (h : injective (quotient.lift f H)) : ker f = r :=
le_antisymm 
 (λ x y hk, quotient.exact $ h $ show quotient.lift f H ⟦x⟧ = quotient.lift f H ⟦y⟧, from hk)
 (λ _ _ h, H _ _ h)

variables (r : setoid α) (f : α → β)

/-- The quotient of α by the kernel of a function f bijects with f's image. -/
noncomputable def quotient_ker_equiv_range : 
  quotient (ker f) ≃ set.range f :=
@equiv.of_bijective _ (set.range f) (@quotient.lift _ (set.range f) (ker f) 
    (λ x, ⟨f x, set.mem_range_self x⟩) $ λ a b h, subtype.eq' h)
    ⟨λ x y h, injective_ker_lift f $ by rcases x; rcases y; injections, 
     λ ⟨w, z, hz⟩, ⟨@quotient.mk _ (ker f) z, by rw quotient.lift_beta; exact subtype.ext.2 hz⟩⟩

/-- The quotient of α by the kernel of a surjective function f bijects with f's codomain. -/
noncomputable def quotient_ker_equiv_of_surjective (hf : surjective f) :
  quotient (ker f) ≃ β :=
@equiv.of_bijective _ _ (@quotient.lift _ _ (ker f) f (λ _ _ h, h)) 
  ⟨injective_ker_lift f, λ y, exists.elim (hf y) $ λ w hw, ⟨quotient.mk' w, hw⟩⟩

/-- The analogue of the third isomorphism theorem for quotients of arbitrary types. -/
noncomputable def quotient_quotient_equiv_quotient (s : setoid α) (h : r ≤ s) :
  quotient (ker (quot.map_right h)) ≃ quotient s :=
quotient_ker_equiv_of_surjective _ $ λ x, by rcases x; exact ⟨quotient.mk' x, rfl⟩

/-- Given an equivalence relation r on α, the natural map from equivalence relations containing
    r to equivalence relations on the quotient of α by r. -/
def to_con (s : {s // r ≤ s}) : setoid (quotient r) :=
{ r := λ x y, quotient.lift_on₂' x y s.1.r' $ λ _ _ _ _ ha hb, iff_iff_eq.1
         ⟨λ h', s.1.trans' (s.1.symm' $ s.2 _ _ ha) $ s.1.trans' h' $ s.2 _ _ hb,
          λ h', s.1.trans' (s.2 _ _ ha) $ s.1.trans' h' $ s.1.symm' $ s.2 _ _ hb⟩,
  iseqv := ⟨λ x, quotient.induction_on' x $ λ y, s.1.refl' y,
              λ x y, quotient.induction_on₂' x y $ λ _ _ h', s.1.symm' h',
              λ x y z, quotient.induction_on₃' x y z $ λ _ _ _ h1 h2, s.1.trans' h1 h2⟩}

/-- Given an equivalence relation r on α, the natural map from equivalence relations on the
    quotient of α by r to equivalence relations on α. -/
def of_con (s : setoid (quotient r)) : setoid α :=
⟨λ x y, s.r' ⟦x⟧ ⟦y⟧, ⟨λ _, s.refl' _, λ _ _ h, s.symm' h, λ _ _ _ h1 h2, s.trans' h1 h2⟩⟩

/-- Given an equivalence relation r on α, the order-preserving bijection between the set of 
    equivalence relations containing r and the equivalence relations on the quotient of α by r. -/
def correspondence : ((≤) : {s // r ≤ s} → {s // r ≤ s} → Prop) ≃o
((≤) : setoid (quotient r) → setoid (quotient r) → Prop) :=
{ to_fun := λ s, r.to_con s,
  inv_fun := λ s, subtype.mk (r.of_con s) $ 
    λ x y h, show s.r' ⟦x⟧ ⟦y⟧, from quotient.sound h ▸ s.refl' ⟦x⟧,
  left_inv := λ s, subtype.ext.2 $ show r.of_con (r.to_con s) = s.1, by ext; refl,
  right_inv := λ s, by ext; rcases a; rcases b; refl,
  ord := λ a b, ⟨λ hle x y, quotient.induction_on₂ x y $ λ w z h, hle w z h,
                 λ H p q h, H ⟦p⟧ ⟦q⟧ h⟩ }

/-- There is a Galois insertion of equivalence relations on α into binary relations on α, with
    equivalence closure the lower adjoint. -/
def gi : @galois_insertion (α → α → Prop) (setoid α) _ _ eqv_gen.setoid r' :=
{ choice := λ r h, eqv_gen.setoid r,
  gc := λ r s, ⟨λ H _ _ h, H _ _ $ eqv_gen.rel _ _ h, λ H, (eqv_gen_eq r).symm ▸ Inf_le _ s H⟩,
  le_l_u := λ x, (eqv_gen_of_setoid x).symm ▸ le_refl x,
  choice_eq := λ _ _, rfl}

end setoid
