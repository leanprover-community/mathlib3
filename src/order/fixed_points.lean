/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import order.complete_lattice
import dynamics.fixed_points

/-!
# Fixed point construction on complete lattices
-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open function (fixed_points)

section fixedpoint
variables [complete_lattice α] {f : α → α}

/-- Least fixed point of a monotone function -/
def lfp (f : α → α) : α := Inf {a | f a ≤ a}
/-- Greatest fixed point of a monotone function -/
def gfp (f : α → α) : α := Sup {a | a ≤ f a}

theorem lfp_le {a : α} (h : f a ≤ a) : lfp f ≤ a :=
Inf_le h

theorem le_lfp {a : α} (h : ∀b, f b ≤ b → a ≤ b) : a ≤ lfp f :=
le_Inf h

theorem lfp_eq (m : monotone f) : lfp f = f (lfp f) :=
have f (lfp f) ≤ lfp f,
  from le_lfp $ assume b, assume h : f b ≤ b, le_trans (m (lfp_le h)) h,
le_antisymm (lfp_le (m this)) this

theorem lfp_induct {p : α → Prop} (m : monotone f)
  (step : ∀a, p a → a ≤ lfp f → p (f a)) (sup : ∀s, (∀a∈s, p a) → p (Sup s)) :
p (lfp f) :=
let s := {a | a ≤ lfp f ∧ p a} in
have p_s : p (Sup s),
  from sup s (assume a ⟨_, h⟩, h),
have Sup s ≤ lfp f,
  from le_lfp $ assume a, assume h : f a ≤ a, Sup_le $ assume b ⟨b_le, _⟩, le_trans b_le (lfp_le h),
have Sup s = lfp f,
  from le_antisymm this $ lfp_le $ le_Sup
    ⟨le_trans (m this) $ ge_of_eq $ lfp_eq m, step _ p_s this⟩,
this ▸ p_s

theorem monotone_lfp : monotone (@lfp α _) :=
assume f g, assume : f ≤ g, le_lfp $ assume a, assume : g a ≤ a, lfp_le $ le_trans (‹f ≤ g› a) this

theorem le_gfp {a : α} (h : a ≤ f a) : a ≤ gfp f :=
le_Sup h

theorem gfp_le {a : α} (h : ∀b, b ≤ f b → b ≤ a) : gfp f ≤ a :=
Sup_le h

theorem gfp_eq (m : monotone f) : gfp f = f (gfp f) :=
have gfp f ≤ f (gfp f),
  from gfp_le $ assume b, assume h : b ≤ f b, le_trans h (m (le_gfp h)),
le_antisymm this (le_gfp (m this))

theorem gfp_induct {p : α → Prop} (m : monotone f)
  (step : ∀a, p a → gfp f ≤ a → p (f a)) (inf : ∀s, (∀a∈s, p a) → p (Inf s)) :
p (gfp f) :=
let s := {a | gfp f ≤ a ∧ p a} in
have p_s : p (Inf s),
  from inf s (assume a ⟨_, h⟩, h),
have gfp f ≤ Inf s,
  from gfp_le $ assume a, assume h : a ≤ f a, le_Inf $ assume b ⟨le_b, _⟩, le_trans (le_gfp h) le_b,
have Inf s = gfp f,
  from le_antisymm (le_gfp $ Inf_le
    ⟨le_trans (le_of_eq $ gfp_eq m) (m this), step _ p_s this⟩) this,
this ▸ p_s

theorem monotone_gfp : monotone (@gfp α _) :=
assume f g, assume : f ≤ g, gfp_le $ assume a, assume : a ≤ f a, le_gfp $ le_trans this (‹f ≤ g› a)

end fixedpoint

section fixedpoint_eqn
variables [complete_lattice α] [complete_lattice β] {f : β → α} {g : α → β}

-- Rolling rule
theorem lfp_comp (m_f : monotone f) (m_g : monotone g) : lfp (f ∘ g) = f (lfp (g ∘ f)) :=
le_antisymm
  (lfp_le $ m_f $ ge_of_eq $ lfp_eq $ m_g.comp m_f)
  (le_lfp $ assume a fg_le,
    le_trans (m_f $ lfp_le $ show (g ∘ f) (g a) ≤ g a, from m_g fg_le) fg_le)

theorem gfp_comp (m_f : monotone f) (m_g : monotone g) : gfp (f ∘ g) = f (gfp (g ∘ f)) :=
le_antisymm
  (gfp_le $ assume a fg_le,
    le_trans fg_le $ m_f $ le_gfp $ show g a ≤ (g ∘ f) (g a), from m_g fg_le)
  (le_gfp $ m_f $ le_of_eq $ gfp_eq $ m_g.comp m_f)

-- Diagonal rule
theorem lfp_lfp {h : α → α → α} (m : ∀⦃a b c d⦄, a ≤ b → c ≤ d → h a c ≤ h b d) :
  lfp (lfp ∘ h) = lfp (λx, h x x) :=
let f := lfp (lfp ∘ h) in
have f_eq : f = lfp (h f),
  from lfp_eq $ monotone.comp monotone_lfp (assume a b h x, m h (le_refl _)) ,
le_antisymm
  (lfp_le $ lfp_le $ ge_of_eq $ lfp_eq $ assume a b h, m h h)
  (lfp_le $ ge_of_eq $
    calc f = lfp (h f)       : f_eq
       ... = h f (lfp (h f)) : lfp_eq $ assume a b h, m (le_refl _) h
       ... = h f f           : congr_arg (h f) f_eq.symm)

theorem gfp_gfp {h : α → α → α} (m : ∀⦃a b c d⦄, a ≤ b → c ≤ d → h a c ≤ h b d) :
  gfp (gfp ∘ h) = gfp (λx, h x x) :=
let f := gfp (gfp ∘ h) in
have f_eq : f = gfp (h f),
  from gfp_eq $ monotone.comp monotone_gfp (assume a b h x, m h (le_refl _)),
le_antisymm
  (le_gfp $ le_of_eq $
    calc f = gfp (h f)       : f_eq
       ... = h f (gfp (h f)) : gfp_eq $ assume a b h, m (le_refl _) h
       ... = h f f           : congr_arg (h f) f_eq.symm)
  (le_gfp $ le_gfp $ le_of_eq $ gfp_eq $ assume a b h, m h h)

end fixedpoint_eqn

/- The complete lattice of fixed points of a function f -/
namespace fixed_points
variables [complete_lattice α] (f : α → α) (hf : monotone f)

def prev (x : α) : α := gfp (λ z, x ⊓ f z)
def next (x : α) : α := lfp (λ z, x ⊔ f z)

variable {f}

theorem prev_le {x : α} : prev f x ≤ x := gfp_le $ λ z hz, le_trans hz inf_le_left

lemma prev_eq (hf : monotone f) {a : α} (h : f a ≤ a) : prev f a = f (prev f a) :=
calc prev f a = a ⊓ f (prev f a) :
    gfp_eq $ show monotone (λz, a ⊓ f z), from assume x y h, inf_le_inf_left _ (hf h)
  ... = f (prev f a) :
    inf_of_le_right $ le_trans (hf prev_le) h

def prev_fixed (hf : monotone f) (a : α) (h : f a ≤ a) : fixed_points f :=
⟨prev f a, (prev_eq hf h).symm⟩

theorem next_le {x : α} : x ≤ next f x := le_lfp $ λ z hz, le_trans le_sup_left hz

lemma next_eq (hf : monotone f) {a : α} (h : a ≤ f a) : next f a = f (next f a) :=
calc next f a = a ⊔ f (next f a) :
    lfp_eq $ show monotone (λz, a ⊔ f z), from assume x y h, sup_le_sup_left (hf h) _
 ... = f (next f a) :
    sup_of_le_right $ le_trans h (hf next_le)

def next_fixed (hf : monotone f) (a : α) (h : a ≤ f a) : fixed_points f :=
⟨next f a, (next_eq hf h).symm⟩

variable f

theorem sup_le_f_of_fixed_points (x y : fixed_points f) : x.1 ⊔ y.1 ≤ f (x.1 ⊔ y.1) :=
sup_le
  (x.2 ▸ (hf $ show x.1 ≤ f x.1 ⊔ y.1, from x.2.symm ▸ le_sup_left))
  (y.2 ▸ (hf $ show y.1 ≤ x.1 ⊔ f y.1, from y.2.symm ▸ le_sup_right))

theorem f_le_inf_of_fixed_points (x y : fixed_points f) : f (x.1 ⊓ y.1) ≤ x.1 ⊓ y.1 :=
le_inf
  (x.2 ▸ (hf $ show f (x.1) ⊓ y.1 ≤ x.1, from x.2.symm ▸ inf_le_left))
  (y.2 ▸ (hf $ show x.1 ⊓ f (y.1) ≤ y.1, from y.2.symm ▸ inf_le_right))

theorem Sup_le_f_of_fixed_points (A : set α) (HA : A ⊆ fixed_points f) : Sup A ≤ f (Sup A) :=
Sup_le $ λ x hxA, (HA hxA) ▸ (hf $ le_Sup hxA)

theorem f_le_Inf_of_fixed_points (A : set α) (HA : A ⊆ fixed_points f) : f (Inf A) ≤ Inf A :=
le_Inf $ λ x hxA, (HA hxA) ▸ (hf $ Inf_le hxA)

/-- The fixed points of `f` form a complete lattice.
This cannot be an instance, since it depends on the monotonicity of `f`. -/
protected def complete_lattice : complete_lattice (fixed_points f) :=
{ le           := λx y, x.1 ≤ y.1,
  le_refl      := λ x, le_refl x,
  le_trans     := λ x y z, le_trans,
  le_antisymm  := λ x y hx hy, subtype.eq $ le_antisymm hx hy,

  sup          := λ x y, next_fixed hf (x.1 ⊔ y.1) (sup_le_f_of_fixed_points f hf x y),
  le_sup_left  := λ x y, show x.1 ≤ _, from le_trans le_sup_left next_le,
  le_sup_right := λ x y, show y.1 ≤ _, from le_trans le_sup_right next_le,
  sup_le       := λ x y z hxz hyz, lfp_le $ sup_le (sup_le hxz hyz) (z.2.symm ▸ le_refl z.1),

  inf          := λ x y, prev_fixed hf (x.1 ⊓ y.1) (f_le_inf_of_fixed_points f hf x y),
  inf_le_left  := λ x y, show _ ≤ x.1, from le_trans prev_le inf_le_left,
  inf_le_right := λ x y, show _ ≤ y.1, from le_trans prev_le inf_le_right,
  le_inf       := λ x y z hxy hxz, le_gfp $ le_inf (le_inf hxy hxz) (x.2.symm ▸ le_refl x),

  top          := prev_fixed hf ⊤ le_top,
  le_top       := λ ⟨x, H⟩, le_gfp $ le_inf le_top (H.symm ▸ le_refl x),

  bot          := next_fixed hf ⊥ bot_le,
  bot_le       := λ ⟨x, H⟩, lfp_le $ sup_le bot_le (H.symm ▸ le_refl x),

  Sup          := λ A, next_fixed hf (Sup $ subtype.val '' A)
    (Sup_le_f_of_fixed_points f hf (subtype.val '' A) (λ z ⟨x, hx⟩, hx.2 ▸ x.2)),
  le_Sup       := λ A x hxA, show x.1 ≤ _, from le_trans
    (le_Sup $ show x.1 ∈ subtype.val '' A, from ⟨x, hxA, rfl⟩)
    next_le,
  Sup_le       := λ A x Hx, lfp_le $ sup_le (Sup_le $ λ z ⟨y, hyA, hyz⟩, hyz ▸ Hx y hyA) (x.2.symm ▸ le_refl x),

  Inf          := λ A, prev_fixed hf (Inf $ subtype.val '' A)
    (f_le_Inf_of_fixed_points f hf (subtype.val '' A) (λ z ⟨x, hx⟩, hx.2 ▸ x.2)),
  le_Inf       := λ A x Hx, le_gfp $ le_inf (le_Inf $ λ z ⟨y, hyA, hyz⟩, hyz ▸ Hx y hyA) (x.2.symm ▸ le_refl x.1),
  Inf_le       := λ A x hxA, show _ ≤ x.1, from le_trans
    prev_le
    (Inf_le $ show x.1 ∈ subtype.val '' A, from ⟨x, hxA, rfl⟩) }

end fixed_points
