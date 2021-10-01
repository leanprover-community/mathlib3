/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import order.preorder_hom
import dynamics.fixed_points.basic

/-!
# Fixed point construction on complete lattices

This file sets up the basic theory of fixed points of a monotone function in a complete lattice

## Main definitions

* `lfp`: The least fixed point of a monotone function.
* `gfp`: The greatest fixed point of a monotone function.
* `prev_fixed`: The least fixed point of a monotone function greater than a given element.
* `next_fixed`: The greatest fixed point of a monotone function smaller than a given element.
* `fixed_points.complete_lattice`: The Knaster-Tarski theorem: fixed points form themselves a
  complete lattice.

## Tags

fixed point, complete lattice, monotone function
-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open function (fixed_points is_fixed_pt)

namespace preorder_hom

section basic

variables [complete_lattice α] (f : α →ₘ α)

/-- Least fixed point of a monotone function -/
def lfp : (α →ₘ α) →ₘ α :=
{ to_fun := λ f, Inf {a | f a ≤ a},
  monotone' := λ f g hle, Inf_le_Inf $ λ a ha, (hle a).trans ha }

/-- Greatest fixed point of a monotone function -/
def gfp : (α →ₘ α) →ₘ α :=
{ to_fun := λ f, Sup {a | a ≤ f a},
  monotone' := λ f g hle, Sup_le_Sup $ λ a ha, le_trans ha (hle a) }

lemma lfp_le {a : α} (h : f a ≤ a) : lfp f ≤ a := Inf_le h

lemma lfp_le_fixed {a : α} (h : f a = a) : lfp f ≤ a := f.lfp_le h.le

lemma le_lfp {a : α} (h : ∀ b, f b ≤ b → a ≤ b) : a ≤ lfp f := le_Inf h

lemma map_le_lfp {a : α} (ha : a ≤ f.lfp) : f a ≤ f.lfp :=
f.le_lfp $ λ b hb, (f.mono $ le_Inf_iff.1 ha _ hb).trans hb

@[simp] lemma map_lfp : f (lfp f) = lfp f :=
have h : f (lfp f) ≤ lfp f, from f.map_le_lfp le_rfl,
h.antisymm $ f.lfp_le $ f.mono h

lemma is_fixed_pt_lfp : is_fixed_pt f f.lfp := f.map_lfp

lemma lfp_le_map {a : α} (ha : lfp f ≤ a) : lfp f ≤ f a :=
calc lfp f = f (lfp f) : f.map_lfp.symm
       ... ≤ f a       : f.mono ha

lemma is_least_lfp_le : is_least {a | f a ≤ a} (lfp f) :=
⟨f.map_lfp.le, λ a, f.lfp_le⟩

lemma is_least_lfp : is_least (fixed_points f) (lfp f) :=
⟨f.is_fixed_pt_lfp, λ a, f.lfp_le_fixed⟩

lemma lfp_induction {p : α → Prop} (step : ∀ a, p a → a ≤ lfp f → p (f a))
  (hSup : ∀ s, (∀ a ∈ s, p a) → p (Sup s)) :
  p (lfp f) :=
begin
  set s := {a | a ≤ lfp f ∧ p a},
  specialize hSup s (λ a, and.right),
  suffices : Sup s = lfp f, from this ▸ hSup,
  have h : Sup s ≤ lfp f := Sup_le (λ b, and.left),
  have hmem : f (Sup s) ∈ s, from ⟨f.map_le_lfp h, step _ hSup h⟩,
  exact h.antisymm (f.lfp_le $ le_Sup hmem)
end

lemma le_gfp {a : α} (h : a ≤ f a) : a ≤ gfp f :=
le_Sup h

lemma gfp_le {a : α} (h : ∀ b, b ≤ f b → b ≤ a) : gfp f ≤ a :=
Sup_le h

lemma is_fixed_pt_gfp : is_fixed_pt f (gfp f) := f.dual.is_fixed_pt_lfp

@[simp] lemma map_gfp : f (gfp f) = gfp f := f.dual.map_lfp

lemma map_le_gfp {a : α} (ha : a ≤ gfp f) : f a ≤ gfp f := f.dual.lfp_le_map ha

lemma gfp_le_map {a : α} (ha : gfp f ≤ a) : gfp f ≤ f a := f.dual.map_le_lfp ha

lemma is_greatest_gfp_le : is_greatest {a | a ≤ f a} (gfp f) :=
f.dual.is_least_lfp_le

lemma is_greatest_gfp : is_greatest (fixed_points f) (gfp f) :=
f.dual.is_least_lfp

lemma gfp_induction {p : α → Prop} (step : ∀ a, p a → gfp f ≤ a → p (f a))
  (hInf : ∀ s, (∀ a ∈ s, p a) → p (Inf s)) :
  p (gfp f) :=
f.dual.lfp_induction step hInf

end basic

section eqn

variables [complete_lattice α] [complete_lattice β] (f : β →ₘ α) (g : α →ₘ β)

-- Rolling rule
lemma map_lfp_comp : f (lfp (g.comp f)) = lfp (f.comp g) :=
le_antisymm ((f.comp g).map_lfp ▸ f.mono (lfp_le_fixed _ $ congr_arg g (f.comp g).map_lfp)) $
  lfp_le _ (congr_arg f (g.comp f).map_lfp).le

lemma map_gfp_comp : f ((g.comp f).gfp) = (f.comp g).gfp :=
f.dual.map_lfp_comp g.dual

-- Diagonal rule
lemma lfp_lfp (h : α →ₘ α →ₘ α) :
  lfp (lfp.comp h) = lfp (λ x, h x x) :=
begin
  let a := lfp (lfp ∘ h),
  refine (lfp_le _).antisymm (lfp_le (eq.le _)),
  { exact lfp_le (lfp_fixed_point (λ a b hab, m hab hab)).le },
  have ha : (lfp ∘ h) a = a := lfp_fixed_point
    ((monotone_lfp : monotone (_ : _ → α)).comp (λ b c hbc x, m hbc le_rfl)),
  calc h a a = h a (lfp (h a)) : congr_arg (h a) ha.symm
       ... = (lfp ∘ h) a       : lfp_fixed_point $ λ b c hbc, m le_rfl hbc
       ... = a                 : ha,
end

lemma gfp_gfp {h : α → α → α} (m : ∀ ⦃a b c d⦄, a ≤ b → c ≤ d → h a c ≤ h b d) :
  gfp (gfp ∘ h) = gfp (λ x, h x x) :=
begin
  let a := gfp (gfp ∘ h),
  refine (le_gfp (eq.ge _)).antisymm (le_gfp (le_gfp (gfp_fixed_point (λ a b hab, m hab hab)).ge)),
  have ha : (gfp ∘ h) a = a := gfp_fixed_point
    ((monotone_gfp : monotone (_ : _ → α)).comp (λ b c hbc x, m hbc le_rfl)),
  calc h a a = h a (gfp (h a)) : congr_arg (h a) ha.symm
         ... = (gfp ∘ h) a     : gfp_fixed_point $ λ b c hbc, m le_rfl hbc
         ... = a               : ha,
end

end fixedpoint_eqn

/- The complete lattice of fixed points of a function f -/
namespace fixed_points
variables [complete_lattice α] (f : α → α) (hf : monotone f)

def prev (x : α) : α := gfp (λ z, x ⊓ f z)
def next (x : α) : α := lfp (λ z, x ⊔ f z)

variable {f}

lemma prev_le {x : α} : prev f x ≤ x := gfp_le $ λ z hz, hz.trans inf_le_left

lemma prev_eq (hf : monotone f) {a : α} (h : f a ≤ a) : f (prev f a) = prev f a :=
calc f (prev f a) = a ⊓ f (prev f a) : (inf_of_le_right $ (hf prev_le).trans h).symm
              ... = prev f a         : gfp_fixed_point $ λ x y h, inf_le_inf_left _ (hf h)

def prev_fixed (hf : monotone f) (a : α) (h : f a ≤ a) : fixed_points f :=
⟨prev f a, prev_eq hf h⟩

lemma le_next {x : α} : x ≤ next f x := le_lfp $ λ z hz, le_sup_left.trans hz

lemma next_eq (hf : monotone f) {a : α} (h : a ≤ f a) : f (next f a) = next f a :=
calc f (next f a) = a ⊔ f (next f a) : (sup_of_le_right $ h.trans (hf le_next)).symm
              ... = next f a         : lfp_fixed_point $ λ x y h, sup_le_sup_left (hf h) _

def next_fixed (hf : monotone f) (a : α) (h : a ≤ f a) : fixed_points f :=
⟨next f a, next_eq hf h⟩

variable f

lemma sup_le_f_of_fixed_points (x y : fixed_points f) : x.1 ⊔ y.1 ≤ f (x.1 ⊔ y.1) :=
sup_le (x.2.ge.trans (hf le_sup_left)) (y.2.ge.trans (hf le_sup_right))

lemma f_le_inf_of_fixed_points (x y : fixed_points f) : f (x.1 ⊓ y.1) ≤ x.1 ⊓ y.1 :=
le_inf ((hf inf_le_left).trans x.2.le) ((hf inf_le_right).trans y.2.le)

lemma Sup_le_f_of_fixed_points (A : set α) (hA : A ⊆ fixed_points f) : Sup A ≤ f (Sup A) :=
Sup_le $ λ x hx, (hA hx) ▸ (hf $ le_Sup hx)

lemma f_le_Inf_of_fixed_points (A : set α) (hA : A ⊆ fixed_points f) : f (Inf A) ≤ Inf A :=
le_Inf $ λ x hx, (hA hx) ▸ (hf $ Inf_le hx)

/-- **Knaster-Tarski Theorem**: The fixed points of `f` form a complete lattice.
This cannot be an instance, since it depends on the monotonicity of `f`. -/
protected def complete_lattice : complete_lattice (fixed_points f) :=
{ le           := (≤),
  le_refl      := le_refl,
  le_trans     := λ x y z, le_trans,
  le_antisymm  := λ x y, le_antisymm,

  sup          := λ x y, next_fixed hf (x.1 ⊔ y.1) (sup_le_f_of_fixed_points f hf x y),
  le_sup_left  := λ x y, (le_sup_left.trans le_next : x.1 ≤ _),
  le_sup_right := λ x y, (le_sup_right.trans le_next : y.1 ≤ _),
  sup_le       := λ x y z hxz hyz, lfp_le $ sup_le (sup_le hxz hyz) (z.2.symm ▸ le_refl z.1),

  inf          := λ x y, prev_fixed hf (x.1 ⊓ y.1) (f_le_inf_of_fixed_points f hf x y),
  inf_le_left  := λ x y, (prev_le.trans inf_le_left : _ ≤ x.1),
  inf_le_right := λ x y, (prev_le.trans inf_le_right : _ ≤ y.1),
  le_inf       := λ x y z hxy hxz, le_gfp $ le_inf (le_inf hxy hxz) (x.2.symm ▸ le_refl x),

  top          := prev_fixed hf ⊤ le_top,
  le_top       := λ ⟨x, hx⟩, le_gfp $ le_inf le_top (hx.symm ▸ le_rfl),

  bot          := next_fixed hf ⊥ bot_le,
  bot_le       := λ ⟨x, hx⟩, lfp_le $ sup_le bot_le (hx.symm ▸ le_rfl),

  Sup          := λ A, next_fixed hf (Sup $ subtype.val '' A)
    (Sup_le_f_of_fixed_points f hf (subtype.val '' A) (λ z ⟨x, hx⟩, hx.2 ▸ x.2)),
  le_Sup       := λ A x hx, (le_Sup $ show x.1 ∈ subtype.val '' A, from ⟨x, hx, rfl⟩).trans le_next,
  Sup_le       := λ A x hx, lfp_le $ sup_le (Sup_le $ λ z ⟨y, hyA, hyz⟩, hyz ▸ hx y hyA)
    (x.2.symm ▸ le_rfl),

  Inf          := λ A, prev_fixed hf (Inf $ subtype.val '' A)
    (f_le_Inf_of_fixed_points f hf (subtype.val '' A) (λ z ⟨x, hx⟩, hx.2 ▸ x.2)),
  le_Inf       := λ A x hx, le_gfp $ le_inf (le_Inf $ λ z ⟨y, hyA, hyz⟩, hyz ▸ hx y hyA)
    (x.2.symm ▸ le_rfl),
  Inf_le       := λ A x hx, prev_le.trans (Inf_le $ show x.1 ∈ subtype.val '' A, from ⟨x, hx, rfl⟩)}

end fixed_points
