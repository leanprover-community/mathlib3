/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import data.quot order.complete_lattice data.equiv.basic order.order_iso order.galois_connection
/-!
# Setoids
Some definitions relating to setoids, including the complete lattice of setoids on a type.

## Implementation notes
The primed definitions and lemmas make it easier to talk about different setoids on the same type.

## Tags
setoid, equivalence, iseqv, relation
-/
variables {α : Type*} {β : Type*}

open lattice 

namespace setoid

def r' (r : setoid α) := @setoid.r _ r

@[extensionality] lemma ext' {r s : setoid α} (H : ∀ a b, r.r' a b ↔ s.r' a b) : r = s := ext H

instance : has_le (setoid α) := ⟨λ r s, ∀ x y, r.r' x y → s.r' x y⟩
instance : has_mem (α × α) (setoid α) := ⟨λ x r, r.r' x.1 x.2⟩

@[refl] lemma refl' (r : setoid α) (x) : r.r' x x := r.2.1 x
@[symm] lemma symm' (r : setoid α) : ∀ {x y}, r.r' x y → r.r' y x := λ _ _ h, r.2.2.1 h
@[trans] lemma trans' (r : setoid α) : ∀ {x y z}, r.r' x y → r.r' y z → r.r' x z := 
λ  _ _ _ hx hy, r.2.2.2 hx hy

def ker (f : α → β) : setoid α :=
⟨λ x y, f x = f y, ⟨λ x, rfl, λ _ _ h, h.symm, λ _ _ _ h1 h2, h1.trans h2⟩⟩ 

lemma ker_mk_eq (r : setoid α) : ker (@quotient.mk _ r) = r :=
ext' $ λ x y, quotient.eq

variables (α)

def bot : setoid α :=
⟨(=), ⟨λ _, rfl, λ _ _ h, h.symm, λ _ _ _ h1 h2, h1.trans h2⟩⟩

def top : setoid α := 
⟨λ _ _, true, ⟨λ _, trivial, λ _ _ h, h, λ _ _ _ h1 h2, h1⟩⟩

variables {α}

protected def prod (r : setoid α) (s : setoid β) : setoid (α × β) :=
⟨λ x y, r.r' x.1 y.1 ∧ s.r' x.2 y.2,
  ⟨λ x, ⟨r.refl' x.1, s.refl' x.2⟩, λ _ _ h, ⟨r.symm' h.1, s.symm' h.2⟩, 
   λ _ _ _ h1 h2, ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩⟩

open lattice

instance : partial_order (setoid α) :=
{ le := (≤),
  lt := λ r s, r ≤ s ∧ ¬s ≤ r,
  le_refl := λ r x y h, h,
  le_trans := λ _ _ _ hr hs x y h, hs x y $ hr x y h,
  lt_iff_le_not_le := λ _ _, iff.rfl,
  le_antisymm := λ r s h1 h2, setoid.ext' $ λ x y, ⟨h1 x y, h2 x y⟩ }

instance : has_bot (setoid α) := ⟨bot α⟩

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

theorem eqv_gen_eq (r : α → α → Prop) : 
  eqv_gen.setoid r = Inf {s : setoid α | ∀ x y, r x y → s.r' x y} :=
setoid.ext' $ λ _ _, 
  ⟨λ H, eqv_gen.rec (λ _ _ h _ hs, hs _ _ h) (refl' _) 
    (λ _ _ _ h, symm' _ h) (λ _ _ _ _ _ h1 h2, trans' _ h1 h2) H, 
  Inf_le _ _ (λ _ _, eqv_gen.rel _ _) _ _⟩

lemma sup_eq_eqv_gen (r s : setoid α) : r ⊔ s = eqv_gen.setoid (λ x y, r.r' x y ∨ s.r' x y) :=
by rw eqv_gen_eq; apply congr_arg Inf; ext; exact 
  ⟨λ h _ _ H, or.elim H (λ hl, h.1 _ _ hl) $ λ hr, h.2 _ _ hr, 
   λ H, ⟨λ _ _ h, H _ _ $ or.inl h, λ _ _ h, H _ _ $ or.inr h⟩⟩

lemma Sup_eq_eqv_gen (S : set (setoid α)) : 
  Sup S = eqv_gen.setoid (λ x y, ∃ r : setoid α, r∈S ∧ r.r' x y) :=
by rw eqv_gen_eq; apply congr_arg Inf; ext;
   exact ⟨λ h _ _ ⟨r, hr⟩, h r hr.1 _ _ hr.2, λ h r hS _ _ hr, h _ _ ⟨r, hS, hr⟩⟩

theorem eqv_gen_of_setoid (r : setoid α) : eqv_gen.setoid r.r = r :=
le_antisymm (by rw eqv_gen_eq; exact Inf_le _ r (λ x y h, h)) eqv_gen.rel

theorem eqv_gen_le {r : α → α → Prop} {s : setoid α} (h : ∀ x y, r x y → s.r' x y) : 
  eqv_gen.setoid r ≤ s :=
by rw eqv_gen_eq; exact Inf_le _ _ h

theorem eqv_gen_mono {r s : α → α → Prop} (h : ∀ x y, r x y → s x y) : 
  eqv_gen.setoid r ≤ eqv_gen.setoid s :=
eqv_gen_le $ λ x y hr, eqv_gen.rel _ _ $ h x y hr

open function

theorem injective_iff_ker_bot (f : α → β) :
  injective f ↔ ker f = ⊥ := 
⟨λ hf, setoid.ext' $ λ x y, ⟨λ h, hf h, λ h, h ▸ rfl⟩, 
 λ hk x y h, show r' ⊥ x y, from hk ▸ (show (ker f).r' x y, from h)⟩

lemma ker_apply_eq_preimage (f : α → β) (m) : (ker f).r' m = f ⁻¹' {f m} :=
set.ext $ λ x,
  ⟨λ h, set.mem_preimage.2 (set.mem_singleton_iff.2 h.symm),
   λ h, (set.mem_singleton_iff.1 (set.mem_preimage.1 h)).symm⟩

theorem lift_unique {r : setoid α} {f : α → β} (H : r ≤ ker f) (g : quotient r → β)
  (Hg : f = g ∘ quotient.mk) : quotient.lift f H = g :=
by ext; rcases x; erw [quotient.lift_beta f H, Hg]; refl

lemma injective_ker_lift (f : α → β) : injective (@quotient.lift _ _ (ker f) f (λ _ _ h, h)) :=
λ x y, by apply quotient.induction_on₂' x y; intros a b; show (ker f).r' a b → _; from quotient.sound'

variables (r : setoid α)

lemma ker_eq_of_equiv (h : quotient r ≃ β) (f : α → β) (H : ∀ x y, r.r' x y → f x = f y) 
  (hh : quotient.lift f H = h) : ker f = r :=
le_antisymm 
 (λ x y hk, quotient.exact $ h.injective $ hh ▸ 
    show quotient.lift f H ⟦x⟧ = quotient.lift f H ⟦y⟧, from hk) 
 $ λ _ _ h, H _ _ h

noncomputable def quotient_ker_equiv_range (f : α → β) : 
  quotient (ker f) ≃ set.range f :=
  @equiv.of_bijective _ (set.range f) (@quotient.lift _ (set.range f) (ker f) 
              (λ x, ⟨f x, set.mem_range_self x⟩) $ λ a b h, subtype.eq' h)
        ⟨λ x y h, injective_ker_lift f $ by rcases x; rcases y; injections, 
         λ ⟨w, z, hz⟩, ⟨@quotient.mk _ (ker f) z, by rw quotient.lift_beta; exact subtype.ext.2 hz⟩⟩

noncomputable def quotient_ker_equiv_of_surjective (f : α → β) (hf : surjective f) :
  quotient (ker f) ≃ β :=
@equiv.of_bijective _ _ (@quotient.lift _ _ (ker f) f (λ _ _ h, h)) 
  ⟨injective_ker_lift f, λ y, exists.elim (hf y) $ λ w hw, ⟨quotient.mk' w, hw⟩⟩

noncomputable def quotient_quotient_equiv_quotient (r s : setoid α) (h : r ≤ s) :
  quotient (ker (quot.map_right h)) ≃ quotient s :=
quotient_ker_equiv_of_surjective _ $ λ x, by rcases x; exact ⟨quotient.mk' x, rfl⟩

def to_con (r : setoid α) (s : {s // r ≤ s}) : setoid (quotient r) :=
{ r := λ x y, quotient.lift_on₂' x y s.1.r' $ λ _ _ _ _ ha hb, iff_iff_eq.1
         ⟨λ h', s.1.trans' (s.1.symm' $ s.2 _ _ ha) $ s.1.trans' h' $ s.2 _ _ hb,
          λ h', s.1.trans' (s.2 _ _ ha) $ s.1.trans' h' $ s.1.symm' $ s.2 _ _ hb⟩,
  iseqv := ⟨λ x, quotient.induction_on' x $ λ y, s.1.refl' y,
              λ x y, quotient.induction_on₂' x y $ λ _ _ h', s.1.symm' h',
              λ x y z, quotient.induction_on₃' x y z $ λ _ _ _ h1 h2, s.1.trans' h1 h2⟩}

def of_con (s : setoid (quotient r)) : setoid α :=
⟨λ x y, s.r' ⟦x⟧ ⟦y⟧, ⟨λ _, s.refl' _, λ _ _ h, s.symm' h, λ _ _ _ h1 h2, s.trans' h1 h2⟩⟩

def correspondence (r : setoid α) : ((≤) : {s // r ≤ s} → {s // r ≤ s} → Prop) ≃o
((≤) : setoid (quotient r) → setoid (quotient r) → Prop) :=
{ to_fun := λ s, r.to_con s,
  inv_fun := λ s, subtype.mk (r.of_con s) $ 
    λ x y h, show s.r' ⟦x⟧ ⟦y⟧, from quotient.sound h ▸ s.refl' ⟦x⟧,
  left_inv := λ s, subtype.ext.2 $ show r.of_con (r.to_con s) = s.1, by ext; refl,
  right_inv := λ s, by ext; rcases a; rcases b; refl,
  ord := λ a b, ⟨λ hle x y, quotient.induction_on₂ x y $ λ w z h, hle w z h,
                 λ H p q h, H ⟦p⟧ ⟦q⟧ h⟩ }

def gi : @galois_insertion (α → α → Prop) (setoid α) _ _ eqv_gen.setoid r' :=
{ choice := λ r h, eqv_gen.setoid r,
  gc := λ r s, ⟨λ H _ _ h, H _ _ $ eqv_gen.rel _ _ h, λ H, (eqv_gen_eq r).symm ▸ Inf_le _ s H⟩,
  le_l_u := λ x, (eqv_gen_of_setoid x).symm ▸ le_refl x,
  choice_eq := λ _ _, rfl}

end setoid
