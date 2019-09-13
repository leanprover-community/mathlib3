/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Bryan Gin-ge Chen
-/

import data.quot data.set.lattice data.fintype order.order_iso order.galois_connection

/-!
# Equivalence relations
The first section of the file defines the complete lattice of equivalence relations 
on a type, results about the inductively defined equivalence closure of a binary relation, 
and the analogues of some isomorphism theorems for quotients of arbitrary types.

The second section comprises properties of equivalence relations viewed as partitions and 
a function "bell" that computes the number of possible partitions of a finite set, along 
with some preliminary results about "bell".

## Implementation notes
The function "rel" and lemmas ending in ' make it easier to talk about different 
equivalence relations on the same type without adding a coercion instance from 
setoid α to (α → α → Prop).

The complete lattice instance for setoids could be defined by lifting the Galois
insertion of equivalence relations on α into binary relations on α, but the resulting
functions are less easy to use. 

Partitions are not defined as a separate structure here; it is encouraged that users
reason about them using the existing "setoid" and its infrastructure.

Eventually there should be a proof here that Bell numbers are the number of possible
partitions of a finite set.

## Tags
setoid, equivalence, iseqv, relation, equivalence relation, partition, equivalence 
class, Bell number, Bell triangle
-/
variables {α : Type*} {β : Type*}

open lattice 

namespace order_iso

variables [preorder α] [preorder β] (oi : @order_iso α β (≤) (≤))

-- order.order_iso doesn't import order.galois_connection, and vice versa.

/-- Makes a Galois connection from an order-preserving bijection. -/
theorem to_galois_connection : galois_connection oi oi.symm :=
λ b g, by rw [ord' oi, apply_symm_apply]

/-- Makes a Galois insertion from an order-preserving bijection. -/
protected def to_galois_insertion : @galois_insertion α β _ _ (oi) (oi.symm) :=
{ choice := λ b h, oi b,
  gc := to_galois_connection oi,
  le_l_u := λ g, le_of_eq (oi.right_inv g).symm,
  choice_eq := λ b h, rfl }

end order_iso

namespace setoid

/-- A version of setoid.r that takes the equivalence relation as an explicit argument. -/
def rel (r : setoid α) := @setoid.r _ r

@[extensionality] lemma ext' {r s : setoid α} 
  (H : ∀ a b, r.rel a b ↔ s.rel a b) : r = s := ext H

lemma ext_iff {r s : setoid α} : r = s ↔ ∀ a b, r.rel a b ↔ s.rel a b :=
⟨λ h a b, h ▸ iff.rfl, ext'⟩

/-- Defining the relation '≤' for equivalence relations. -/
instance : has_le (setoid α) := ⟨λ r s, ∀ x y, r.rel x y → s.rel x y⟩

instance : has_mem (α × α) (setoid α) := ⟨λ x r, r.rel x.1 x.2⟩

@[refl] lemma refl' (r : setoid α) (x) : r.rel x x := r.2.1 x
@[symm] lemma symm' (r : setoid α) : ∀ {x y}, r.rel x y → r.rel y x := λ _ _ h, r.2.2.1 h
@[trans] lemma trans' (r : setoid α) : ∀ {x y z}, r.rel x y → r.rel y z → r.rel x z := 
λ  _ _ _ hx hy, r.2.2.2 hx hy

/-- The kernel of a function is an equivalence relation. -/
def ker (f : α → β) : setoid α :=
⟨λ x y, f x = f y, ⟨λ x, rfl, λ _ _ h, h.symm, λ _ _ _ h1 h2, h1.trans h2⟩⟩ 

/-- The kernel of the quotient map induced by an equivalence relation r equals r. -/
@[simp] lemma ker_mk_eq (r : setoid α) : ker (@quotient.mk _ r) = r :=
ext' $ λ x y, quotient.eq

/-- The infimum of two equivalence relations. -/
instance : has_inf (setoid α) :=
⟨λ r s, ⟨λ x y, r.rel x y ∧ s.rel x y, ⟨λ x, ⟨r.refl' x, s.refl' x⟩, 
 λ x y h, ⟨r.symm' h.1, s.symm' h.2⟩, 
 λ _ _ _ h1 h2, ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩⟩⟩

/-- The infimum of a set of equivalence relations. -/
instance : has_Inf (setoid α) :=
⟨λ S, ⟨λ x y, (∀ r ∈ S, rel r x y), 
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
instance complete_lattice : complete_lattice (setoid α) :=
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
  eqv_gen.setoid r = Inf {s : setoid α | ∀ x y, r x y → s.rel x y} :=
setoid.ext' $ λ _ _, 
  ⟨λ H, eqv_gen.rec (λ _ _ h _ hs, hs _ _ h) (refl' _) 
    (λ _ _ _ h, symm' _ h) (λ _ _ _ _ _ h1 h2, trans' _ h1 h2) H, 
  Inf_le _ _ (λ _ _, eqv_gen.rel _ _) _ _⟩

/-- The supremum of two equivalence relations r and s is the equivalence closure of the binary
    relation 'x is related to y by r or s'. -/
lemma sup_eq_eqv_gen (r s : setoid α) : 
  r ⊔ s = eqv_gen.setoid (λ x y, r.rel x y ∨ s.rel x y) :=
by rw eqv_gen_eq; apply congr_arg Inf; ext; exact 
  ⟨λ h _ _ H, or.elim H (λ hl, h.1 _ _ hl) $ λ hr, h.2 _ _ hr, 
   λ H, ⟨λ _ _ h, H _ _ $ or.inl h, λ _ _ h, H _ _ $ or.inr h⟩⟩

/-- The supremum of a set S of equivalence relations is the equivalence closure of the binary
    relation 'there exists r ∈ S relating x and y'. -/
lemma Sup_eq_eqv_gen (S : set (setoid α)) : 
  Sup S = eqv_gen.setoid (λ x y, ∃ r : setoid α, r∈S ∧ r.rel x y) :=
by rw eqv_gen_eq; apply congr_arg Inf; ext;
   exact ⟨λ h _ _ ⟨r, hr⟩, h r hr.1 _ _ hr.2, λ h r hS _ _ hr, h _ _ ⟨r, hS, hr⟩⟩

/-- The equivalence closure of an equivalence relation r is r. -/
@[simp] lemma eqv_gen_of_setoid (r : setoid α) : eqv_gen.setoid r.r = r :=
le_antisymm (by rw eqv_gen_eq; exact Inf_le _ r (λ x y h, h)) eqv_gen.rel

/-- Equivalence closure is idempotent. -/
@[simp] lemma eqv_gen_idem (r : α → α → Prop) : 
  eqv_gen.setoid (eqv_gen.setoid r).rel = eqv_gen.setoid r :=
eqv_gen_of_setoid _ 

/-- The equivalence closure of a binary relation r is contained in any equivalence
    relation containing r. -/
theorem eqv_gen_le {r : α → α → Prop} {s : setoid α} (h : ∀ x y, r x y → s.rel x y) : 
  eqv_gen.setoid r ≤ s :=
by rw eqv_gen_eq; exact Inf_le _ _ h

/-- Equivalence closure of binary relations is monotonic. -/
theorem eqv_gen_mono {r s : α → α → Prop} (h : ∀ x y, r x y → s x y) : 
  eqv_gen.setoid r ≤ eqv_gen.setoid s :=
eqv_gen_le $ λ x y hr, eqv_gen.rel _ _ $ h x y hr

theorem le_def {r s : setoid α} : r ≤ s ↔ ∀ {x y}, r.rel x y → s.rel x y := iff.rfl

/-- The infimum of 2 equivalence relations r and s is the same relation as the infimum 
    of the underlying binary operations. -/
lemma inf_def {r s : setoid α} : (r ⊓ s).rel = r.rel ⊓ s.rel := rfl 

/-- The supremum of 2 equivalence relations r and s is equivalence closure of the 
    supremum of the underlying binary operations. -/
lemma sup_def {r s : setoid α} : r ⊔ s = eqv_gen.setoid (r.rel ⊔ s.rel) :=
by rw sup_eq_eqv_gen; refl

theorem inf_iff_and {r s : setoid α} {x y} : 
  (r ⊓ s).rel x y ↔ r.rel x y ∧ s.rel x y := iff.rfl

/-- The underlying binary operation of the infimum of a set of equivalence relations
    is the infimum of the set's image under the map to the underlying
    binary operation. -/
theorem Inf_def {s : set (setoid α)} : (Inf s).rel = Inf (rel '' s) :=
begin
  ext x y,
  erw [Inf_image, infi_apply, infi_apply, infi_Prop_eq],
  split,
    intros h r,
    rw [infi_apply, infi_apply, infi_Prop_eq],
    exact λ hr, h r hr,
  intros h r hr,
  specialize h r,
  rw [infi_apply, infi_apply, infi_Prop_eq] at h, 
  exact h hr,
end 

/-- The underlying binary operation of the supremum of a set of equivalence relations
    is the equivalence closure of the supremum of the set's image under the map to 
    the underlying binary operation. -/
lemma Sup_def {s : set (setoid α)} : Sup s = eqv_gen.setoid (Sup (rel '' s)) := 
begin
  rw Sup_eq_eqv_gen, 
  congr,
  ext x y,
  erw [Sup_image, supr_apply, supr_apply, supr_Prop_eq], 
  split,
    rintro ⟨r, h, hr⟩, 
    use r,
    rw [supr_apply, supr_apply, supr_Prop_eq], 
    exact ⟨h, hr⟩,
  rintro ⟨r, h⟩, 
  obtain ⟨h, hr⟩ := by rw [supr_apply, supr_apply, supr_Prop_eq] at h; exact h,
  exact ⟨r, h, hr⟩,
end 

open function

/-- A function from α to β is injective iff its kernel is the bottom element of the complete lattice
    of equivalence relations on α. -/
theorem injective_iff_ker_bot (f : α → β) :
  injective f ↔ ker f = ⊥ := 
⟨λ hf, setoid.ext' $ λ x y, ⟨λ h, hf h, λ h, h ▸ rfl⟩, 
 λ hk x y h, show rel ⊥ x y, from hk ▸ (show (ker f).rel x y, from h)⟩

/-- The elements related to x ∈ α by the kernel of f are those in the preimage of f(x) under f. -/
lemma ker_apply_eq_preimage (f : α → β) (x) : (ker f).rel x = f ⁻¹' {f x} :=
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
λ x y, by apply quotient.induction_on₂' x y; intros a b; 
  show (ker f).rel a b → _; from quotient.sound'

/-- Given a map f from α to β, the kernel of f is the unique equivalence relation on α whose
    induced map from the quotient of α to β is injective. -/
lemma ker_eq_lift_injective {r : setoid α} (f : α → β) (H : ∀ x y, r.rel x y → f x = f y) 
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
def to_setoid (s : {s // r ≤ s}) : setoid (quotient r) :=
{ r := λ x y, quotient.lift_on₂' x y s.1.rel $ λ _ _ _ _ ha hb, iff_iff_eq.1
         ⟨λ h', s.1.trans' (s.1.symm' $ s.2 _ _ ha) $ s.1.trans' h' $ s.2 _ _ hb,
          λ h', s.1.trans' (s.2 _ _ ha) $ s.1.trans' h' $ s.1.symm' $ s.2 _ _ hb⟩,
  iseqv := ⟨λ x, quotient.induction_on' x $ λ y, s.1.refl' y,
              λ x y, quotient.induction_on₂' x y $ λ _ _ h', s.1.symm' h',
              λ x y z, quotient.induction_on₃' x y z $ λ _ _ _ h1 h2, s.1.trans' h1 h2⟩}

/-- Given an equivalence relation r on α, the natural map from equivalence relations on the
    quotient of α by r to equivalence relations on α. -/
def of_setoid (s : setoid (quotient r)) : setoid α :=
⟨λ x y, s.rel ⟦x⟧ ⟦y⟧, ⟨λ _, s.refl' _, λ _ _ h, s.symm' h, λ _ _ _ h1 h2, s.trans' h1 h2⟩⟩

/-- Given an equivalence relation r on α, the order-preserving bijection between the set of 
    equivalence relations containing r and the equivalence relations on the quotient of α by r. -/
def correspondence : ((≤) : {s // r ≤ s} → {s // r ≤ s} → Prop) ≃o
((≤) : setoid (quotient r) → setoid (quotient r) → Prop) :=
{ to_fun := λ s, r.to_setoid s,
  inv_fun := λ s, subtype.mk (r.of_setoid s) $ 
    λ x y h, show s.rel ⟦x⟧ ⟦y⟧, from quotient.sound h ▸ s.refl' ⟦x⟧,
  left_inv := λ s, subtype.ext.2 $ show r.of_setoid (r.to_setoid s) = s.1, by ext; refl,
  right_inv := λ s, by ext; rcases a; rcases b; refl,
  ord := λ a b, ⟨λ hle x y, quotient.induction_on₂ x y $ λ w z h, hle w z h,
                 λ H p q h, H ⟦p⟧ ⟦q⟧ h⟩ }

/-- There is a Galois insertion of equivalence relations on α into binary relations 
    on α, with equivalence closure the lower adjoint. -/
def gi : @galois_insertion (α → α → Prop) (setoid α) _ _ eqv_gen.setoid rel :=
{ choice := λ r h, eqv_gen.setoid r,
  gc := λ r s, ⟨λ H _ _ h, H _ _ $ eqv_gen.rel _ _ h, λ H, (eqv_gen_eq r).symm ▸ Inf_le _ s H⟩,
  le_l_u := λ x, (eqv_gen_of_setoid x).symm ▸ le_refl x,
  choice_eq := λ _ _, rfl}

/-- Two equivalence relations are equal iff their underlying binary operations are equal. -/
theorem eq_iff_r_eq {r₁ r₂ : setoid α} : r₁ = r₂ ↔ r₁.rel = r₂.rel :=
⟨λ h, h ▸ rfl, λ h, setoid.ext' $ λ x y, h ▸ iff.rfl⟩

/-- If x ∈ α is in 2 elements of a set of sets partitioning α, those 2 sets are equal. -/
lemma eq_of_mem_eqv_class {c : set (set α)} 
  (H : ∀ a, ∃ b ∈ c, a ∈ b ∧ ∀ b' ∈ c, a ∈ b' → b = b')
  {x b b'} (hc : b ∈ c) (hb : x ∈ b) (hc' : b' ∈ c) (hb' : x ∈ b') : 
  b = b' := 
let ⟨_, _, _, h⟩ := H x in (h b hc hb).symm.trans $ h b' hc' hb'
 
/-- Makes an equivalence relation from a set of sets partitioning α. -/
def mk_classes (c : set (set α)) 
  (H : ∀ a, ∃ b ∈ c, a ∈ b ∧ ∀ b' ∈ c, a ∈ b' → b = b') : 
  setoid α := 
⟨λ x y, ∀ b ∈ c, (x ∈ b → y ∈ b), ⟨λ _ _ _ hx, hx, 
 λ x _ h _ hb hy, let ⟨z, hc, hx, hz⟩ := H x in 
    eq_of_mem_eqv_class H hc (h z hc hx) hb hy ▸ hx,
 λ x y z h1 h2 b hc hb, let ⟨v, hvc, hy, hv⟩ := H y in let ⟨w, hwc, hz, hw⟩ := H z in 
    (eq_of_mem_eqv_class H hwc hz hvc $ h2 v hvc hy).trans 
      (eq_of_mem_eqv_class H hvc hy hc $ h1 b hc hb) ▸ hz⟩⟩

/-- Makes the equivalence classes of an equivalence relation. -/
def classes (r : setoid α) : set (set α) := 
{ s | ∃ y ∈ s, s = {x | r.rel x y}}

lemma mem_classes (r : setoid α) (y) : {x | r.rel x y} ∈ r.classes := ⟨y, r.refl' y, rfl⟩ 

/-- Two equivalence relations are equal iff all their equivalence classes are equal. -/
lemma eq_iff_classes_eq' {r₁ r₂ : setoid α} :
  r₁ = r₂ ↔ ∀ x, {y | r₁.rel x y} = {y | r₂.rel x y} :=
⟨λ h x, h ▸ rfl, λ h, ext' $ λ x, (set.ext_iff _ _).1 $ h x⟩

/-- Two equivalence relations are equal iff their equivalence classes are equal. -/
lemma eq_iff_classes_eq {r₁ r₂ : setoid α} :
  r₁ = r₂ ↔ r₁.classes = r₂.classes :=
⟨λ h, h ▸ rfl, λ h, ext' $ λ a b, 
  ⟨λ h1, let ⟨w, hm, hw⟩ := show _ ∈ r₂.classes, by rw ←h; exact r₁.mem_classes a in 
      r₂.trans' (show a ∈ {x | r₂.rel x w}, from hw ▸ r₁.refl' a) $
        r₂.symm' (show b ∈ {x | r₂.rel x w}, by rw ←hw; exact r₁.symm' h1), 
   λ h1, let ⟨w, hm, hw⟩ := show _ ∈ r₁.classes, by rw h; exact r₂.mem_classes a in
      r₁.trans' (show a ∈ {x | r₁.rel x w}, from hw ▸ r₂.refl' a) $
        r₁.symm' (show b ∈ {x | r₁.rel x w}, by rw ←hw; exact r₂.symm' h1)⟩⟩

/-- The empty set is not an equivalence class. -/
lemma empty_not_mem_classes {r : setoid α} : ∅ ∉ r.classes :=
λ ⟨y, h, hy⟩, set.not_mem_empty y h

/-- Equivalence classes partition the type. -/
lemma classes_eqv_classes {r : setoid α} : 
  ∀ a, ∃ b ∈ r.classes, a ∈ b ∧ ∀ b' ∈ r.classes, a ∈ b' → b = b' :=
λ a, ⟨{x | r.rel x a}, r.mem_classes a, 
  ⟨r.refl' a, λ s ⟨y, hy, h⟩ ha, by rw h at *; ext; 
    exact ⟨λ hx, r.trans' hx ha, λ hx, r.trans' hx $ r.symm' ha⟩⟩⟩

/-- If x ∈ α is in 2 equivalence classes, the equivalence classes are equal. -/
lemma eq_of_mem_classes {r : setoid α} {x b} (hc : b ∈ r.classes) 
  (hb : x ∈ b) {b'} (hc' : b' ∈ r.classes) (hb' : x ∈ b') : b = b' :=
eq_of_mem_eqv_class classes_eqv_classes hc hb hc' hb'

/-- The elements of a set of set partitioning α are the equivalence classes of the 
    equivalence relation defined by the set of sets. -/
lemma eq_eqv_class_of_mem {c : set (set α)} 
  (H : ∀ a, ∃ b ∈ c, a ∈ b ∧ ∀ b' ∈ c, a ∈ b' → b = b')
  {s y} (hs : s ∈ c) (hy : y ∈ s) : s = {x | rel (mk_classes c H) x y} :=
set.ext $ λ x, 
  ⟨λ hs', symm' (mk_classes c H) $ λ b' hb' h', eq_of_mem_eqv_class H hs hy hb' h' ▸ hs',
   λ hx, let ⟨b', hc', hb', h'⟩ := H x in 
     (eq_of_mem_eqv_class H hs hy hc' $ hx b' hc' hb').symm ▸ hb'⟩

/-- The equivalence classes of the equivalence relation defined by a set of sets 
    partitioning α are elements of the set of sets. -/
lemma eqv_class_mem {c : set (set α)} 
  (H : ∀ a, ∃ b ∈ c, a ∈ b ∧ ∀ b' ∈ c, a ∈ b' → b = b') {y} : 
  {x | rel (mk_classes c H) x y} ∈ c :=
let ⟨b, hc, hy, hb⟩ := H y in eq_eqv_class_of_mem H hc hy ▸ hc

/-- The union of a set of sets covering α is the entirety of α. -/
lemma eqv_classes_union {c : set (set α)} (H : ∀ a, ∃ b ∈ c, a ∈ b) : 
  set.sUnion c = @set.univ α :=
set.univ_subset_iff.1 $ λ x hx, let ⟨b, hm, hb⟩ := H x in set.mem_sUnion_of_mem hb hm

/-- Distinct elements of a set of sets partitioning α are disjoint. -/
lemma eqv_classes_disjoint {c : set (set α)} 
  (H : ∀ a, ∃ b ∈ c, a ∈ b ∧ ∀ b' ∈ c, a ∈ b' → b = b') 
  (b₁ b₂) (h₁ : b₁ ∈ c) (h₂ : b₂ ∈ c) (h : b₁ ≠ b₂) : disjoint b₁ b₂ :=
set.disjoint_left.2 $ λ x hx1 hx2, let ⟨b, hc, hx, hb⟩ := H x in
  h $ eq_of_mem_eqv_class H h₁ hx1 h₂ hx2
 
/-- A set of disjoint sets covering α partition α. -/
lemma eqv_classes_of_disjoint_union {c : set (set α)} (hu : set.sUnion c = @set.univ α) 
  (H : ∀ b b' ∈ c, b ≠ b' → disjoint b b') : 
  ∀ a, ∃ b ∈ c, a ∈ b ∧ ∀ b' ∈ c, a ∈ b' → b = b' :=
λ a, let ⟨b, hc, ha⟩ := set.mem_sUnion.1 $ show a ∈ _, by rw hu; exact set.mem_univ a in
  ⟨b, hc, ha, λ b' hc' ha', let hp := classical.prop_decidable in 
  (@not_not _ $ hp _).1 $ λ hn, set.not_mem_empty a $ H b b' hc hc' hn ⟨ha, ha'⟩⟩

/-- If x ∈ α is in 2 elements of a set of disjoint sets covering α, those elements 
    are equal. -/
lemma eq_of_mem_disjoint {c : set (set α)} (hu : set.sUnion c = @set.univ α) 
  (H : ∀ b b' ∈ c, b ≠ b' → disjoint b b') {x b} (hb : b ∈ c) (hx : x ∈ b)
  {b'} (hb' : b' ∈ c) (hx' : x ∈ b') : b = b' :=
eq_of_mem_eqv_class (eqv_classes_of_disjoint_union hu H) hb hx hb' hx'

/-- Makes an equivalence relation from a set of disjoints sets covering α. -/
def setoid_of_disjoint_union {c : set (set α)} (hu : set.sUnion c = @set.univ α) 
  (H : ∀ b b' ∈ c, b ≠ b' → disjoint b b') : setoid α :=
setoid.mk_classes c $ eqv_classes_of_disjoint_union hu H

/-- The equivalence relation made from the equivalence classes of an equivalence 
    relation r equals r. -/
theorem mk_classes_classes (r : setoid α) : 
  mk_classes r.classes classes_eqv_classes = r := 
ext' $ λ x y, ⟨λ h, r.symm' (h {z | r.rel z x} (r.mem_classes x) $ r.refl' x),
  λ h b hb hx, eq_of_mem_classes (r.mem_classes x) (r.refl' x) hb hx ▸ r.symm' h⟩

section partition

def partitions (α) (c : set (set α)) := 
∅ ∉ c ∧ ∀ a, ∃ b ∈ c, a ∈ b ∧ ∀ b' ∈ c, a ∈ b' → b = b'

/-- A partition of α does not contain the empty set. -/
lemma ne_empty_of_mem_partition {c : subtype (partitions α)} {s} (h : s ∈ c.1) : 
  s ≠ ∅ :=
λ hs0, c.2.1 $ hs0 ▸ h 

/-- All elements of a partition of α are the equivalence class of some y ∈ α. -/
lemma exists_of_mem_partition {c : subtype (partitions α)} {s} (hs : s ∈ c.1) : 
  ∃ y, s = { x | rel (mk_classes c.1 c.2.2) x y } :=
let ⟨y, hy⟩ := set.exists_mem_of_ne_empty $ ne_empty_of_mem_partition hs in 
  ⟨y, eq_eqv_class_of_mem c.2.2 hs hy⟩

/-- The equivalence classes of the equivalence relation defined by a partition of α are
    the original partition. -/
theorem classes_mk_classes (c : subtype (partitions α)) : 
  (mk_classes c.1 c.2.2).classes = c.1 := 
set.ext $ λ s,
  ⟨λ ⟨y, hm, hs⟩, by rcases c.2.2 y with ⟨b, hc, hb, hy⟩; convert hc; rw hs; ext; 
      exact ⟨λ hx, symm' (mk_classes c.1 c.2.2) hx b hc hb, λ hx b' hc' hx', 
              eq_of_mem_eqv_class c.2.2 hc hx hc' hx' ▸ hb⟩, 
   λ h, let ⟨y, hy⟩ := set.exists_mem_of_ne_empty $ ne_empty_of_mem_partition h in 
     ⟨y, hy, eq_eqv_class_of_mem c.2.2 h hy⟩⟩

/-- Defining ≤ on partitions as the ≤ defined on their induced equivalence relations. -/
instance partition.le : has_le (subtype (partitions α)) :=
⟨λ x y, mk_classes x.1 x.2.2 ≤ mk_classes y.1 y.2.2⟩

/-- Defining a partial order on partitions as the partial order on their induced
    equivalence relations. -/
instance partition.partial_order : partial_order (subtype (partitions α)) :=
{ le := (≤),
  lt := λ x y, x ≤ y ∧ ¬y ≤ x,
  le_refl := λ x, @le_refl (setoid α) _ _,
  le_trans := λ _ _ _ h1 h2, @le_trans (setoid α) _ _ _ _ h1 h2,
  lt_iff_le_not_le := λ x y, iff.rfl,
  le_antisymm := λ x y hx hy, let h := @le_antisymm (setoid α) _ _ _ hx hy in by 
    rw [subtype.ext, ←classes_mk_classes x, ←classes_mk_classes y, h] }

variables (α)

/-- The order-preserving bijection between equivalence relations and partitions of sets. -/
def partition.order_iso : 
  ((≤) : setoid α → setoid α → Prop) ≃o (@setoid.partitions.partial_order α).le := 
{ to_fun := λ r, ⟨r.classes, empty_not_mem_classes, classes_eqv_classes⟩,
  inv_fun := λ x, mk_classes x.1 x.2.2,
  left_inv := λ r, mk_classes_classes r,
  right_inv := λ x, by rw [subtype.ext, ←classes_mk_classes x],
  ord := λ x y, by conv {to_lhs, rw [←mk_classes_classes x, ←mk_classes_classes y]}; refl}

variables {α}

/-- A complete lattice instance for partitions; there is more infrastructure for the 
    equivalent complete lattice on equivalence relations. -/
instance partition.complete_lattice : 
  _root_.lattice.complete_lattice (subtype (partitions α)) :=
galois_insertion.lift_complete_lattice $ @order_iso.to_galois_insertion
_ (subtype (partitions α)) _ (partial_order.to_preorder _) $ partition.order_iso α
 
theorem partition.le_def (c d : subtype (partitions α)) : 
  c ≤ d ↔ mk_classes c.1 c.2.2 ≤ mk_classes d.1 d.2.2 := 
iff.rfl

open list

/-- Appends the last element of a list to the beginning. -/
def bell_init : list ℕ → list ℕ
| [] := []
| (a :: l) := (last (a :: l) $ cons_ne_nil a l) :: (a :: l) 

/-- Folds (+) over a list from the left, returning the list of partial results. -/
def bell_aux : list ℕ → list ℕ
| [] := []
| (a :: l) := (scanl (+) 0 (a :: l)).tail 

/-- The nth row of the Bell triangle. -/
def bell_row : ℕ → list ℕ
| 0 := [1] 
| (n + 1) := bell_aux (bell_init (bell_row n))

/-- The nth Bell number. -/
def bell (n : ℕ) : ℕ := (bell_row n).head 

/-- Appending the last element of a list to its beginning increases its length by one. -/
lemma init_length {a : ℕ} {l : list ℕ} : 
  length (bell_init (a::l)) = length (a::l) + 1 :=
length_cons _ _ 

/-- Folding a function over a list from the left, appending the function's value on
    an input to the beginning, increases its length by 1. -/
lemma length_scanl {β : Type*} {f : α → β → α} : 
  ∀ a l, length (scanl f a l) = l.length + 1
| a [] := rfl
| a (x :: l) := by erw [length_cons, length_cons, length_scanl] 

/-- Applying "bell_aux" does not change a list's length. -/
lemma aux_length {a : ℕ} {l : list ℕ} : 
  length (bell_aux (a :: l)) = length (a :: l) := 
by erw length_scanl; norm_num

/-- The length of the nth row of the Bell triangle is n + 1. -/
lemma row_length (n : ℕ) : length (bell_row n) = n + 1 :=
begin
  induction n with n hn,
    refl, 
  rcases exists_of_length_succ (bell_row n) hn with ⟨h, t, H⟩,
  rcases exists_of_length_succ (bell_init (bell_row n)) 
    (by rw H; exact init_length) with ⟨h', t', H'⟩,
  rw [bell_row, H', aux_length, ←H', H, init_length, ←H, hn],
end 

/-- Restatement of appending the last element of the nth row of the Bell triangle to
    the row's beginning. -/
lemma init_row : ∀ n, bell_init (bell_row n) = 
  nth_le (bell_row n) n ((row_length n).symm ▸ nat.lt_succ_self n) :: bell_row n :=
begin
  intro n,
  rcases exists_of_length_succ (bell_row n) 
    (row_length _) with ⟨h, t, hl⟩,
  conv {congr, rw hl},
  rw [bell_init, last_eq_nth_le], 
  congr' 2, 
      rw ←hl, 
    rw [←hl, row_length], 
    refl, 
  rw ←hl,
end

/-- The (n + 1)th Bell number is the last element of the nth row of the Bell triangle. -/
lemma bell_succ (n : ℕ) :
  bell (n + 1) = nth_le (bell_row n) n (by rw row_length; norm_num) :=
begin
  rw [bell, (show nth_le _ _ _ = (bell_init (bell_row n)).head, by 
        rw init_row n; refl), bell_row], 
  rcases exists_of_length_succ (bell_row n) (row_length n) with ⟨h, t, H⟩,
  rcases exists_of_length_succ (bell_init (bell_row n)) 
    (by rw H; exact init_length) with ⟨h', t', H'⟩,
  rw [H', bell_aux, ←H', H, bell_init, scanl, tail, zero_add], 
  refl,
end

/-- There are finitely many equivalence relations on a finite type. -/
noncomputable instance [h : fintype α] : fintype (setoid α) :=
@fintype.of_equiv _ _
(@subtype.fintype _ (@set.fintype _ (@set.fintype _  h $ classical.dec_eq _) $ 
  classical.dec_eq _) _ $ classical.dec_pred _) $ 
  (partition.order_iso α).to_equiv.symm

end partition

end setoid