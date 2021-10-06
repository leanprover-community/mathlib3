/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Yury Kudryashov
-/
import order.preorder_hom
import dynamics.fixed_points.basic

/-!
# Fixed point construction on complete lattices

This file sets up the basic theory of fixed points of a monotone function in a complete lattice.

## Main definitions

* `preorder_hom.lfp`: The least fixed point of a bundled monotone function.
* `preorder_hom.gfp`: The greatest fixed point of a bundled monotone function.
* `preorder_hom.prev_fixed`: The greatest fixed point of a bundled monotone function smaller than or
  equal to a given element.
* `preorder_hom.next_fixed`: The least fixed point of a bundled monotone function greater than or
  equal to a given element.
* `fixed_points.complete_lattice`: The Knaster-Tarski theorem: fixed points of a monotone
  self-map of a complete lattice form themselves a complete lattice.

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
  lfp (lfp.comp h) = lfp h.on_diag :=
begin
  let a := lfp (lfp.comp h),
  refine (lfp_le _ _).antisymm (lfp_le _ (eq.le _)),
  { exact lfp_le _ h.on_diag.map_lfp.le },
  have ha : (lfp ∘ h) a = a := (lfp.comp h).map_lfp,
  calc h a a = h a (lfp (h a)) : congr_arg (h a) ha.symm
         ... = lfp (h a)       : (h a).map_lfp
         ... = a               : ha
end

lemma gfp_gfp (h : α →ₘ α →ₘ α) :
  gfp (gfp.comp h) = gfp h.on_diag :=
@lfp_lfp (order_dual α) _ $ (preorder_hom.dual_iso (order_dual α)
  (order_dual α)).symm.to_order_embedding.to_preorder_hom.comp h.dual

end eqn

section prev_next
variables [complete_lattice α] (f : α →ₘ α)

lemma gfp_const_inf_le (x : α) : gfp (const α x ⊓ f) ≤ x :=
gfp_le _ $ λ b hb, hb.trans inf_le_left

/-- Previous fixed point of a monotone map. If `f` is a monotone self-map of a complete lattice and
`x` is a point such that `f x ≤ x`, then `f.prev_fixed x hx` is the greatest fixed point of `f`
that is less than or equal to `x`. -/
def prev_fixed (x : α) (hx : f x ≤ x) : fixed_points f :=
⟨gfp (const α x ⊓ f),
  calc f (gfp (const α x ⊓ f)) = x ⊓ f (gfp (const α x ⊓ f)) :
    eq.symm $ inf_of_le_right $ (f.mono $ f.gfp_const_inf_le x).trans hx
  ... = gfp (const α x ⊓ f) : (const α x ⊓ f).map_gfp ⟩

/-- Next fixed point of a monotone map. If `f` is a monotone self-map of a complete lattice and
`x` is a point such that `x ≤ f x`, then `f.next_fixed x hx` is the least fixed point of `f`
that is greater than or equal to `x`. -/
def next_fixed (x : α) (hx : x ≤ f x) : fixed_points f :=
{ val := (const α x ⊔ f).lfp,
  .. f.dual.prev_fixed x hx }

lemma prev_fixed_le {x : α} (hx : f x ≤ x) : ↑(f.prev_fixed x hx) ≤ x :=
f.gfp_const_inf_le x

lemma le_next_fixed {x : α} (hx : x ≤ f x) : x ≤ f.next_fixed x hx :=
f.dual.prev_fixed_le hx

lemma next_fixed_le {x : α} (hx : x ≤ f x) {y : fixed_points f} (h : x ≤ y) :
  f.next_fixed x hx ≤ y :=
subtype.coe_le_coe.1 $ lfp_le _ $ sup_le h y.2.le

@[simp] lemma next_fixed_le_iff {x : α} (hx : x ≤ f x) {y : fixed_points f} :
  f.next_fixed x hx ≤ y ↔ x ≤ y :=
⟨λ h, (f.le_next_fixed hx).trans h, f.next_fixed_le hx⟩

@[simp] lemma le_prev_fixed_iff {x : α} (hx : f x ≤ x) {y : fixed_points f} :
  y ≤ f.prev_fixed x hx ↔ ↑y ≤ x :=
f.dual.next_fixed_le_iff hx

lemma le_prev_fixed {x : α} (hx : f x ≤ x) {y : fixed_points f} (h : ↑y ≤ x) :
  y ≤ f.prev_fixed x hx :=
(f.le_prev_fixed_iff hx).2 h

lemma le_map_sup_fixed_points (x y : fixed_points f) : (x ⊔ y : α) ≤ f (x ⊔ y) :=
calc (x ⊔ y : α) = f x ⊔ f y : congr_arg2 (⊔) x.2.symm y.2.symm
             ... ≤ f (x ⊔ y) : f.mono.le_map_sup x y

lemma map_inf_fixed_points_le (x y : fixed_points f) : f (x ⊓ y) ≤ x ⊓ y :=
f.dual.le_map_sup_fixed_points x y

lemma le_map_Sup_subset_fixed_points (A : set α) (hA : A ⊆ fixed_points f) : Sup A ≤ f (Sup A) :=
Sup_le $ λ x hx, hA hx ▸ (f.mono $ le_Sup hx)

lemma map_Inf_subset_fixed_points_le (A : set α) (hA : A ⊆ fixed_points f) : f (Inf A) ≤ Inf A :=
le_Inf $ λ x hx, (hA hx) ▸ (f.mono $ Inf_le hx)

end prev_next

end preorder_hom

namespace fixed_points

open preorder_hom

variables [complete_lattice α] (f : α →ₘ α)

instance : semilattice_sup (fixed_points f) :=
{ sup := λ x y, f.next_fixed (x ⊔ y) (f.le_map_sup_fixed_points x y),
  le_sup_left := λ x y, subtype.coe_le_coe.1 $ le_sup_left.trans (f.le_next_fixed _),
  le_sup_right := λ x y, subtype.coe_le_coe.1 $ le_sup_right.trans (f.le_next_fixed _),
  sup_le := λ x y z hxz hyz, f.next_fixed_le _ $ sup_le hxz hyz,
  .. subtype.partial_order _ }

instance : semilattice_inf (fixed_points f) :=
{ inf := λ x y, f.prev_fixed (x ⊓ y) (f.map_inf_fixed_points_le x y),
  .. subtype.partial_order _, .. (order_dual.semilattice_inf (fixed_points f.dual))  }

instance : complete_semilattice_Sup (fixed_points f) :=
{ Sup := λ s, f.next_fixed (Sup (coe '' s))
    (f.le_map_Sup_subset_fixed_points (coe '' s) (λ z ⟨x, hx⟩, hx.2 ▸ x.2)),
  le_Sup := λ s x hx, subtype.coe_le_coe.1 $ le_trans (le_Sup $ set.mem_image_of_mem _ hx)
    (f.le_next_fixed _),
  Sup_le := λ s x hx, f.next_fixed_le _ $ Sup_le $ set.ball_image_iff.2 hx,
  .. subtype.partial_order _ }

instance : complete_semilattice_Inf (fixed_points f) :=
{ Inf := λ s, f.prev_fixed (Inf (coe '' s))
    (f.map_Inf_subset_fixed_points_le (coe '' s) (λ z ⟨x, hx⟩, hx.2 ▸ x.2)),
  le_Inf := λ s x hx, f.le_prev_fixed _ $ le_Inf $ set.ball_image_iff.2 hx,
  Inf_le := λ s x hx, subtype.coe_le_coe.1 $ le_trans (f.prev_fixed_le _)
    (Inf_le $ set.mem_image_of_mem _ hx),
  .. subtype.partial_order _ }

/-- **Knaster-Tarski Theorem**: The fixed points of `f` form a complete lattice. -/
instance : complete_lattice (fixed_points f) :=
{ top := ⟨f.gfp, f.is_fixed_pt_gfp⟩,
  bot := ⟨f.lfp, f.is_fixed_pt_lfp⟩,
  le_top := λ x, f.le_gfp x.2.ge,
  bot_le := λ x, f.lfp_le x.2.le,
  .. subtype.partial_order _,
  .. fixed_points.semilattice_sup f,
  .. fixed_points.semilattice_inf f,
  .. fixed_points.complete_semilattice_Sup f,
  .. fixed_points.complete_semilattice_Inf f }

end fixed_points
