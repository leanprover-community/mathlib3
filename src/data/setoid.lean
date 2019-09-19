/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Bryan Gin-ge Chen
-/

import data.quot data.set.lattice data.fintype order.galois_connection

/-!
# Equivalence relations

The first section of the file defines the complete lattice of equivalence relations
on a type, results about the inductively defined equivalence closure of a binary relation,
and the analogues of some isomorphism theorems for quotients of arbitrary types.

The second section comprises properties of equivalence relations viewed as partitions.

## Implementation notes

The function `rel` and lemmas ending in ' make it easier to talk about different
equivalence relations on the same type.

The complete lattice instance for equivalence relations could have been defined by lifting
the Galois insertion of equivalence relations on α into binary relations on α, and then using
`complete_lattice.copy` to define a complete lattice instance with more appropriate
definitional equalities (a similar example is `filter.lattice.complete_lattice` in
`order/filter/basic.lean`). This does not save space, however, and is less clear.

Partitions are not defined as a separate structure here; users are encouraged to
reason about them using the existing `setoid` and its infrastructure.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation, partition, equivalence
class
-/
variables {α : Type*} {β : Type*}

open lattice

/-- A version of `setoid.r` that takes the equivalence relation as an explicit argument. -/
def setoid.rel (r : setoid α) : α → α → Prop := @setoid.r _ r

/-- A version of `quotient.eq'` compatible with `setoid.rel`, to make rewriting possible. -/
lemma quotient.eq_rel {r : setoid α} {x y} : ⟦x⟧ = ⟦y⟧ ↔ r.rel x y := quotient.eq'

namespace setoid

@[extensionality] lemma ext' {r s : setoid α} (H : ∀ a b, r.rel a b ↔ s.rel a b) :
  r = s := ext H

lemma ext_iff {r s : setoid α} : r = s ↔ ∀ a b, r.rel a b ↔ s.rel a b :=
⟨λ h a b, h ▸ iff.rfl, ext'⟩

/-- Two equivalence relations are equal iff their underlying binary operations are equal. -/
theorem eq_iff_rel_eq {r₁ r₂ : setoid α} : r₁ = r₂ ↔ r₁.rel = r₂.rel :=
⟨λ h, h ▸ rfl, λ h, setoid.ext' $ λ x y, h ▸ iff.rfl⟩

/-- Defining `≤` for equivalence relations. -/
instance : has_le (setoid α) := ⟨λ r s, ∀ x y, r.rel x y → s.rel x y⟩

theorem le_def {r s : setoid α} : r ≤ s ↔ ∀ {x y}, r.rel x y → s.rel x y := iff.rfl

@[refl] lemma refl' (r : setoid α) (x) : r.rel x x := r.2.1 x
@[symm] lemma symm' (r : setoid α) : ∀ {x y}, r.rel x y → r.rel y x := λ _ _ h, r.2.2.1 h
@[trans] lemma trans' (r : setoid α) : ∀ {x y z}, r.rel x y → r.rel y z → r.rel x z :=
λ _ _ _ hx, r.2.2.2 hx

/-- The kernel of a function is an equivalence relation. -/
def ker (f : α → β) : setoid α :=
⟨λ x y, f x = f y, ⟨λ _, rfl, λ _ _ h, h.symm, λ _ _ _ h, h.trans⟩⟩

/-- The kernel of the quotient map induced by an equivalence relation r equals r. -/
@[simp] lemma ker_mk_eq (r : setoid α) : ker (@quotient.mk _ r) = r :=
ext' $ λ x y, quotient.eq

/-- The infimum of two equivalence relations. -/
instance : has_inf (setoid α) :=
⟨λ r s, ⟨λ x y, r.rel x y ∧ s.rel x y, ⟨λ x, ⟨r.refl' x, s.refl' x⟩,
 λ _ _ h, ⟨r.symm' h.1, s.symm' h.2⟩,
 λ _ _ _ h1 h2, ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩⟩⟩

/-- The infimum of 2 equivalence relations r and s is the same relation as the infimum
    of the underlying binary operations. -/
lemma inf_def {r s : setoid α} : (r ⊓ s).rel = r.rel ⊓ s.rel := rfl

theorem inf_iff_and {r s : setoid α} {x y} :
  (r ⊓ s).rel x y ↔ r.rel x y ∧ s.rel x y := iff.rfl

/-- The infimum of a set of equivalence relations. -/
instance : has_Inf (setoid α) :=
⟨λ S, ⟨λ x y, ∀ r ∈ S, rel r x y,
⟨λ x r hr, r.refl' x, λ _ _ h r hr, r.symm' $ h r hr,
 λ _ _ _ h1 h2 r hr, r.trans' (h1 r hr) $ h2 r hr⟩⟩⟩

/-- The underlying binary operation of the infimum of a set of equivalence relations
    is the infimum of the set's image under the map to the underlying binary operation. -/
theorem Inf_def {s : set (setoid α)} : (Inf s).rel = Inf (rel '' s) :=
by { ext, simp only [Inf_image, infi_apply, infi_Prop_eq], refl }

/-- The infimum of a set of equivalence relations is contained in any element of the set. -/
lemma Inf_le (S : set (setoid α)) (r ∈ S) : Inf S ≤ r :=
λ _ _ h, h r H

/-- If an equivalence relation r is contained in every element of a set of equivalence relations,
    r is contained in the infimum of the set. -/
lemma le_Inf (S : set (setoid α)) (r) : (∀ s ∈ S, r ≤ s) → r ≤ Inf S :=
λ H _ _ h s hs, H s hs _ _ h

/-- The inductively defined equivalence closure of a binary relation r is the infimum
    of the set of all equivalence relations containing r. -/
theorem eqv_gen_eq (r : α → α → Prop) :
  eqv_gen.setoid r = Inf {s : setoid α | ∀ x y, r x y → s.rel x y} :=
setoid.ext' $ λ _ _,
  ⟨λ H, eqv_gen.rec (λ _ _ h _ hs, hs _ _ h) (refl' _)
    (λ _ _ _, symm' _) (λ _ _ _ _ _, trans' _) H,
  Inf_le _ _ (λ _ _, eqv_gen.rel _ _) _ _⟩

/-- The supremum of two equivalence relations, defined as the infimum of the set of
    equivalence relations containing both. -/
instance : has_sup (setoid α) := ⟨λ r s, Inf {x | r ≤ x ∧ s ≤ x}⟩

/-- The supremum of two equivalence relations r and s is the equivalence closure of the binary
    relation `x is related to y by r or s`. -/
lemma sup_eq_eqv_gen (r s : setoid α) :
  r ⊔ s = eqv_gen.setoid (λ x y, r.rel x y ∨ s.rel x y) :=
begin
  rw eqv_gen_eq,
  apply congr_arg Inf,
  ext,
  exact ⟨λ h _ _ H, or.elim H (h.1 _ _) (h.2 _ _),
         λ H, ⟨λ _ _ h, H _ _ $ or.inl h, λ _ _ h, H _ _ $ or.inr h⟩⟩
end

/-- The supremum of 2 equivalence relations r and s is the equivalence closure of the
    supremum of the underlying binary operations. -/
lemma sup_def {r s : setoid α} : r ⊔ s = eqv_gen.setoid (r.rel ⊔ s.rel) :=
by rw sup_eq_eqv_gen; refl

/-- The complete lattice of equivalence relations on a type, with bottom element `=`
    and top element the trivial equivalence relation. -/
instance complete_lattice : complete_lattice (setoid α) :=
{ sup := has_sup.sup,
  le := (≤),
  lt := λ r s, r ≤ s ∧ ¬s ≤ r,
  le_refl := λ _ _ _, id,
  le_trans := λ _ _ _ hr hs _ _ h, hs _ _ $ hr _ _ h,
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

/-- The supremum of a set S of equivalence relations is the equivalence closure of the binary
    relation `there exists r ∈ S relating x and y`. -/
lemma Sup_eq_eqv_gen (S : set (setoid α)) :
  Sup S = eqv_gen.setoid (λ x y, ∃ r : setoid α, r ∈ S ∧ r.rel x y) :=
begin
  rw eqv_gen_eq,
  apply congr_arg Inf,
  ext,
  exact ⟨λ h _ _ ⟨r, hr⟩, h r hr.1 _ _ hr.2,
         λ h r hS _ _ hr, h _ _ ⟨r, hS, hr⟩⟩
end

/-- The supremum of a set of equivalence relations is the equivalence closure of the
    supremum of the set's image under the map to the underlying binary operation. -/
lemma Sup_def {s : set (setoid α)} : Sup s = eqv_gen.setoid (Sup (rel '' s)) :=
begin
  rw Sup_eq_eqv_gen,
  congr,
  ext x y,
  erw [Sup_image, supr_apply, supr_apply, supr_Prop_eq],
  simp only [Sup_image, supr_Prop_eq, supr_apply, supr_Prop_eq, exists_prop]
end

/-- The equivalence closure of an equivalence relation r is r. -/
@[simp] lemma eqv_gen_of_setoid (r : setoid α) : eqv_gen.setoid r.r = r :=
le_antisymm (by rw eqv_gen_eq; exact Inf_le _ r (λ _ _, id)) eqv_gen.rel

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
eqv_gen_le $ λ _ _ hr, eqv_gen.rel _ _ $ h _ _ hr

/-- There is a Galois insertion of equivalence relations on α into binary relations
    on α, with equivalence closure the lower adjoint. -/
def gi : @galois_insertion (α → α → Prop) (setoid α) _ _ eqv_gen.setoid rel :=
{ choice := λ r h, eqv_gen.setoid r,
  gc := λ r s, ⟨λ H _ _ h, H _ _ $ eqv_gen.rel _ _ h, λ H, eqv_gen_of_setoid s ▸ eqv_gen_mono H⟩,
  le_l_u := λ x, (eqv_gen_of_setoid x).symm ▸ le_refl x,
  choice_eq := λ _ _, rfl }

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
begin
  ext,
  rcases x,
  erw [quotient.lift_beta f H, Hg],
  refl
end

/-- Given a map f from α to β, the natural map from the quotient of α by the kernel of f is
    injective. -/
lemma injective_ker_lift (f : α → β) : injective (@quotient.lift _ _ (ker f) f (λ _ _ h, h)) :=
λ x y, quotient.induction_on₂' x y $ λ a b h, quotient.sound' h

/-- Given a map f from α to β, the kernel of f is the unique equivalence relation on α whose
    induced map from the quotient of α to β is injective. -/
lemma ker_eq_lift_of_injective {r : setoid α} (f : α → β) (H : ∀ x y, r.rel x y → f x = f y)
  (h : injective (quotient.lift f H)) : ker f = r :=
le_antisymm
  (λ x y hk, quotient.exact $ h $ show quotient.lift f H ⟦x⟧ = quotient.lift f H ⟦y⟧, from hk)
  H

variables (r : setoid α) (f : α → β)

/-- The first isomorphism theorem for sets: the quotient of α by the kernel of a function f
    bijects with f's image. -/
noncomputable def quotient_ker_equiv_range :
  quotient (ker f) ≃ set.range f :=
@equiv.of_bijective _ (set.range f) (@quotient.lift _ (set.range f) (ker f)
  (λ x, ⟨f x, set.mem_range_self x⟩) $ λ _ _ h, subtype.eq' h)
  ⟨λ x y h, injective_ker_lift f $ by rcases x; rcases y; injections,
   λ ⟨w, z, hz⟩, ⟨@quotient.mk _ (ker f) z, by rw quotient.lift_beta; exact subtype.ext.2 hz⟩⟩

/-- The quotient of α by the kernel of a surjective function f bijects with f's codomain. -/
noncomputable def quotient_ker_equiv_of_surjective (hf : surjective f) :
  quotient (ker f) ≃ β :=
@equiv.of_bijective _ _ (@quotient.lift _ _ (ker f) f (λ _ _, id))
  ⟨injective_ker_lift f, λ y, exists.elim (hf y) $ λ w hw, ⟨quotient.mk' w, hw⟩⟩

/-- The third isomorphism theorem for sets. -/
noncomputable def quotient_quotient_equiv_quotient (s : setoid α) (h : r ≤ s) :
  quotient (ker (quot.map_right h)) ≃ quotient s :=
quotient_ker_equiv_of_surjective _ $ λ x, by rcases x; exact ⟨quotient.mk' x, rfl⟩

/-- Given an equivalence relation r on α and a surjective map f from α to the quotient of α by r,
    the natural map from equivalence relations containing r to equivalence relations on the
    quotient of α by r. -/
def to_quotient {f : α → quotient r} (hf : surjective f) (s : {s // r ≤ s}) :
  setoid (quotient r) :=
{ r := λ x y, s.1.rel (classical.some $ hf x) (classical.some $ hf y),
  iseqv := ⟨λ x, s.1.refl' _, λ _ _ h, s.1.symm' h, λ _ _ _ h1, s.1.trans' h1⟩ }

/-- Given an equivalence relation r on α and a map f to the quotient of α by r, an
    equivalence relation s on the quotient induces an equivalence relation on f's domain defined
    by x ≈ y ↔ f(x) is related to f(y) by s. -/
def of_quotient (f : β → quotient r) (s : setoid (quotient r)) : setoid β :=
⟨λ x y, s.rel (f x) (f y),
 ⟨λ _, s.refl' _, λ _ _ h, s.symm' h, λ _ _ _ h1 h2, s.trans' h1 h2⟩⟩

section
  open classical quotient
  /-- Given an equivalence relation r on α, the order-preserving bijection between the set of
      equivalence relations containing r and the equivalence relations on the quotient of α by r. -/
  def correspondence : ((≤) : {s // r ≤ s} → {s // r ≤ s} → Prop) ≃o
    ((≤) : setoid (quotient r) → setoid (quotient r) → Prop) :=
  { to_fun := λ s, r.to_quotient exists_rep s,
    inv_fun := λ s, subtype.mk (r.of_quotient quotient.mk' s) $
      λ x y h, show s.rel ⟦x⟧ ⟦y⟧, from sound h ▸ s.refl' ⟦x⟧,
    left_inv := λ s, subtype.ext.2 $ ext' $ λ x y,
        ⟨λ h, s.1.trans' (s.1.trans' (s.2 x (some $ exists_rep ⟦x⟧) $
                eq_rel.1 (some_spec $ exists_rep ⟦x⟧).symm) h) $
                  s.2 (some $ exists_rep ⟦y⟧) y $ eq_rel.1 $ some_spec $ exists_rep ⟦y⟧,
         λ h, s.1.trans' (s.1.trans' (s.2 (some $ exists_rep ⟦x⟧) x $
                eq_rel.1 (some_spec $ exists_rep ⟦x⟧)) h) $
                  s.2 y (some $ exists_rep ⟦y⟧) $ eq_rel.1 (some_spec $ exists_rep ⟦y⟧).symm⟩,
    right_inv := λ s, ext' $ λ x y, show s.rel ⟦(some _)⟧ ⟦(some _)⟧ ↔ s.rel x y, by
      rw [some_spec (exists_rep _), some_spec (exists_rep _)],
    ord := λ a b, ⟨λ h x y ha, h (some $ exists_rep x) (some $ exists_rep y) ha,
      λ h x y ha, b.1.trans' (b.1.trans' (b.2 x (some $ exists_rep ⟦x⟧) $
          eq_rel.1 (some_spec $ exists_rep ⟦x⟧).symm) $
            h ⟦x⟧ ⟦y⟧ (a.1.trans' (a.1.trans' (a.2 (some $ exists_rep ⟦x⟧) x $
              eq_rel.1 $ some_spec $ exists_rep ⟦x⟧) ha) $
                a.2 y (some $ exists_rep ⟦y⟧) $ eq_rel.1 (some_spec $ exists_rep ⟦y⟧).symm)) $
                  b.2 (some $ exists_rep ⟦y⟧) y $ eq_rel.1 $ some_spec $ exists_rep ⟦y⟧⟩ }
end

-- Partitions

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
⟨λ x y, ∀ b ∈ c, x ∈ b → y ∈ b, ⟨λ _ _ _ hx, hx,
 λ x _ h _ hb hy, let ⟨z, hc, hx, hz⟩ := H x in
    eq_of_mem_eqv_class H hc (h z hc hx) hb hy ▸ hx,
 λ x y z h1 h2 b hc hb, let ⟨v, hvc, hy, hv⟩ := H y in let ⟨w, hwc, hz, hw⟩ := H z in
    (eq_of_mem_eqv_class H hwc hz hvc $ h2 v hvc hy).trans
      (eq_of_mem_eqv_class H hvc hy hc $ h1 b hc hb) ▸ hz⟩⟩

/-- Makes the equivalence classes of an equivalence relation. -/
def classes (r : setoid α) : set (set α) :=
{s | ∃ y, s = {x | r.rel x y}}

lemma mem_classes (r : setoid α) (y) : {x | r.rel x y} ∈ r.classes := ⟨y, rfl⟩

/-- Two equivalence relations are equal iff all their equivalence classes are equal. -/
lemma eq_iff_classes_eq {r₁ r₂ : setoid α} :
  r₁ = r₂ ↔ ∀ x, {y | r₁.rel x y} = {y | r₂.rel x y} :=
⟨λ h x, h ▸ rfl, λ h, ext' $ λ x, (set.ext_iff _ _).1 $ h x⟩

/-- Two equivalence relations are equal iff their equivalence classes are equal. -/
lemma classes_inj {r₁ r₂ : setoid α} :
  r₁ = r₂ ↔ r₁.classes = r₂.classes :=
⟨λ h, h ▸ rfl, λ h, ext' $ λ a b,
  ⟨λ h1, let ⟨w, hw⟩ := show _ ∈ r₂.classes, by rw ←h; exact r₁.mem_classes a in
      r₂.trans' (show a ∈ {x | r₂.rel x w}, from hw ▸ r₁.refl' a) $
        r₂.symm' (show b ∈ {x | r₂.rel x w}, by rw ←hw; exact r₁.symm' h1),
   λ h1, let ⟨w, hw⟩ := show _ ∈ r₁.classes, by rw h; exact r₂.mem_classes a in
      r₁.trans' (show a ∈ {x | r₁.rel x w}, from hw ▸ r₂.refl' a) $
        r₁.symm' (show b ∈ {x | r₁.rel x w}, by rw ←hw; exact r₂.symm' h1)⟩⟩

/-- The empty set is not an equivalence class. -/
lemma empty_not_mem_classes {r : setoid α} : ∅ ∉ r.classes :=
λ ⟨y, hy⟩, set.not_mem_empty y $ hy.symm ▸ r.refl' y

/-- Equivalence classes partition the type. -/
lemma classes_eqv_classes {r : setoid α} :
  ∀ a, ∃ b ∈ r.classes, a ∈ b ∧ ∀ b' ∈ r.classes, a ∈ b' → b = b' :=
λ a, ⟨{x | r.rel x a}, r.mem_classes a,
  ⟨r.refl' a, λ s ⟨y, h⟩ ha, by rw h at *; ext;
    exact ⟨λ hx, r.trans' hx ha, λ hx, r.trans' hx $ r.symm' ha⟩⟩⟩

/-- If x ∈ α is in 2 equivalence classes, the equivalence classes are equal. -/
lemma eq_of_mem_classes {r : setoid α} {x b} (hc : b ∈ r.classes)
  (hb : x ∈ b) {b'} (hc' : b' ∈ r.classes) (hb' : x ∈ b') : b = b' :=
eq_of_mem_eqv_class classes_eqv_classes hc hb hc' hb'

/-- The elements of a set of sets partitioning α are the equivalence classes of the
    equivalence relation defined by the set of sets. -/
lemma eq_eqv_class_of_mem {c : set (set α)}
  (H : ∀ a, ∃ b ∈ c, a ∈ b ∧ ∀ b' ∈ c, a ∈ b' → b = b')
  {s y} (hs : s ∈ c) (hy : y ∈ s) : s = {x | (mk_classes c H).rel x y} :=
set.ext $ λ x,
  ⟨λ hs', symm' (mk_classes c H) $ λ b' hb' h', eq_of_mem_eqv_class H hs hy hb' h' ▸ hs',
   λ hx, let ⟨b', hc', hb', h'⟩ := H x in
     (eq_of_mem_eqv_class H hs hy hc' $ hx b' hc' hb').symm ▸ hb'⟩

/-- The equivalence classes of the equivalence relation defined by a set of sets
    partitioning α are elements of the set of sets. -/
lemma eqv_class_mem {c : set (set α)}
  (H : ∀ a, ∃ b ∈ c, a ∈ b ∧ ∀ b' ∈ c, a ∈ b' → b = b') {y} :
  {x | (mk_classes c H).rel x y} ∈ c :=
let ⟨b, hc, hy, hb⟩ := H y in eq_eqv_class_of_mem H hc hy ▸ hc

/-- Distinct elements of a set of sets partitioning α are disjoint. -/
lemma eqv_classes_disjoint {c : set (set α)}
  (H : ∀ a, ∃ b ∈ c, a ∈ b ∧ ∀ b' ∈ c, a ∈ b' → b = b') :
  set.pairwise_disjoint c :=
λ b₁ h₁ b₂ h₂ h, set.disjoint_left.2 $
  λ x hx1 hx2, let ⟨b, hc, hx, hb⟩ := H x in h $ eq_of_mem_eqv_class H h₁ hx1 h₂ hx2

/-- A set of disjoint sets covering α partition α (classical). -/
lemma eqv_classes_of_disjoint_union {c : set (set α)}
  (hu : set.sUnion c = @set.univ α) (H : set.pairwise_disjoint c) (a) :
  ∃ b ∈ c, a ∈ b ∧ ∀ b' ∈ c, a ∈ b' → b = b' :=
let ⟨b, hc, ha⟩ := set.mem_sUnion.1 $ show a ∈ _, by rw hu; exact set.mem_univ a in
  ⟨b, hc, ha, λ b' hc' ha', set.pairwise_disjoint_elim H hc hc' a ha ha'⟩

/-- Makes an equivalence relation from a set of disjoints sets covering α. -/
def setoid_of_disjoint_union {c : set (set α)} (hu : set.sUnion c = @set.univ α)
  (H : set.pairwise_disjoint c) : setoid α :=
setoid.mk_classes c $ eqv_classes_of_disjoint_union hu H

/-- The equivalence relation made from the equivalence classes of an equivalence
    relation r equals r. -/
theorem mk_classes_classes (r : setoid α) :
  mk_classes r.classes classes_eqv_classes = r :=
ext' $ λ x y, ⟨λ h, r.symm' (h {z | r.rel z x} (r.mem_classes x) $ r.refl' x),
  λ h b hb hx, eq_of_mem_classes (r.mem_classes x) (r.refl' x) hb hx ▸ r.symm' h⟩

section partition

def is_partition (c : set (set α)) :=
∅ ∉ c ∧ ∀ a, ∃ b ∈ c, a ∈ b ∧ ∀ b' ∈ c, a ∈ b' → b = b'

/-- A partition of α does not contain the empty set. -/
lemma ne_empty_of_mem_partition {c : set (set α)} (hc : is_partition c) {s} (h : s ∈ c) :
  s ≠ ∅ :=
λ hs0, hc.1 $ hs0 ▸ h

/-- All elements of a partition of α are the equivalence class of some y ∈ α. -/
lemma exists_of_mem_partition {c : set (set α)} (hc : is_partition c) {s} (hs : s ∈ c) :
  ∃ y, s = {x | (mk_classes c hc.2).rel x y} :=
let ⟨y, hy⟩ := set.exists_mem_of_ne_empty $ ne_empty_of_mem_partition hc hs in
  ⟨y, eq_eqv_class_of_mem hc.2 hs hy⟩

/-- The equivalence classes of the equivalence relation defined by a partition of α equal
    the original partition. -/
theorem classes_mk_classes (c : set (set α)) (hc : is_partition c) :
  (mk_classes c hc.2).classes = c :=
set.ext $ λ s,
  ⟨λ ⟨y, hs⟩, by rcases hc.2 y with ⟨b, hm, hb, hy⟩;
    rwa (show s = b, from hs.symm ▸ set.ext
      (λ x, ⟨λ hx, symm' (mk_classes c hc.2) hx b hm hb,
             λ hx b' hc' hx', eq_of_mem_eqv_class hc.2 hm hx hc' hx' ▸ hb⟩)),
   λ h, let ⟨y, hy⟩ := set.exists_mem_of_ne_empty $ ne_empty_of_mem_partition hc h in
     ⟨y, eq_eqv_class_of_mem hc.2 h hy⟩⟩

/-- Defining `≤` on partitions as the `≤` defined on their induced equivalence relations. -/
instance partition.le : has_le (subtype (@is_partition α)) :=
⟨λ x y, mk_classes x.1 x.2.2 ≤ mk_classes y.1 y.2.2⟩

/-- Defining a partial order on partitions as the partial order on their induced
    equivalence relations. -/
instance partition.partial_order : partial_order (subtype (@is_partition α)) :=
{ le := (≤),
  lt := λ x y, x ≤ y ∧ ¬y ≤ x,
  le_refl := λ _, @le_refl (setoid α) _ _,
  le_trans := λ _ _ _, @le_trans (setoid α) _ _ _ _,
  lt_iff_le_not_le := λ _ _, iff.rfl,
  le_antisymm := λ x y hx hy, let h := @le_antisymm (setoid α) _ _ _ hx hy in by
    rw [subtype.ext, ←classes_mk_classes x.1 x.2, ←classes_mk_classes y.1 y.2, h] }

variables (α)

/-- The order-preserving bijection between equivalence relations and partitions of sets. -/
def partition.order_iso :
  ((≤) : setoid α → setoid α → Prop) ≃o (@setoid.partition.partial_order α).le :=
{ to_fun := λ r, ⟨r.classes, empty_not_mem_classes, classes_eqv_classes⟩,
  inv_fun := λ x, mk_classes x.1 x.2.2,
  left_inv := mk_classes_classes,
  right_inv := λ x, by rw [subtype.ext, ←classes_mk_classes x.1 x.2],
  ord := λ x y, by conv {to_lhs, rw [←mk_classes_classes x, ←mk_classes_classes y]}; refl }

variables {α}

/-- A complete lattice instance for partitions; there is more infrastructure for the
    equivalent complete lattice on equivalence relations. -/
instance partition.complete_lattice :
  _root_.lattice.complete_lattice (subtype (@is_partition α)) :=
galois_insertion.lift_complete_lattice $ @order_iso.to_galois_insertion
_ (subtype (@is_partition α)) _ (partial_order.to_preorder _) $ partition.order_iso α

end partition

end setoid
