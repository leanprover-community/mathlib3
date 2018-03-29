import order.complete_lattice order.order_iso order.fixed_points

open lattice

universe u

variables {α : Type u} [complete_lattice α]
variables (f : α → α) (M : monotone f)

def fixed_points : set α := { x | f x = x }

namespace fixed_points

def previous (x : α) : α :=
gfp (λ z, x ⊓ f z)

variable {f}

theorem previous.le {x : α} : previous f x ≤ x :=
gfp_le $ λ z hz, le_trans hz inf_le_left

theorem previous.le_apply {x : α} : previous f x ≤ f (previous f x) :=
gfp_le $ λ z hz, le_trans (le_trans hz inf_le_right) $ M $ le_gfp hz

theorem previous.fixed {x : α} (H : f x ≤ x) : f (previous f x) = previous f x :=
le_antisymm
  (le_gfp $ le_inf (le_trans (M previous.le) H) (M $ previous.le_apply M))
  (previous.le_apply M)

variable f

def next (x : α) : α :=
lfp (λ z, x ⊔ f z)

variable {f}

theorem next.le {x : α} : x ≤ next f x :=
le_lfp $ λ z hz, le_trans le_sup_left hz

theorem next.apply_le {x : α} : f (next f x) ≤ next f x :=
le_lfp $ λ z hz, le_trans (le_trans (M $ show next f x ≤ z, from lfp_le hz) le_sup_right) hz

theorem next.fixed {x : α} (H : x ≤ f x) : f (next f x) = next f x :=
le_antisymm
  (next.apply_le M)
  (lfp_le $ sup_le (le_trans H (M next.le)) (M $ next.apply_le M))

variable f

theorem sup_le_f_of_fixed_points (x y : fixed_points f) : x.1 ⊔ y.1 ≤ f (x.1 ⊔ y.1) :=
sup_le
  (x.2 ▸ (M $ show x.1 ≤ f x.1 ⊔ y.1, from x.2.symm ▸ le_sup_left))
  (y.2 ▸ (M $ show y.1 ≤ x.1 ⊔ f y.1, from y.2.symm ▸ le_sup_right))

theorem f_le_inf_of_fixed_points (x y : fixed_points f) : f (x.1 ⊓ y.1) ≤ x.1 ⊓ y.1 :=
le_inf
  (x.2 ▸ (M $ show f (x.1) ⊓ y.1 ≤ x.1, from x.2.symm ▸ inf_le_left))
  (y.2 ▸ (M $ show x.1 ⊓ f (y.1) ≤ y.1, from y.2.symm ▸ inf_le_right))

theorem Sup_le_f_of_fixed_points (A : set α) (HA : A ⊆ fixed_points f) : Sup A ≤ f (Sup A) :=
Sup_le $ λ x hxA, (HA hxA) ▸ (M $ le_Sup hxA)

theorem f_le_Inf_of_fixed_points (A : set α) (HA : A ⊆ fixed_points f) : f (Inf A) ≤ Inf A :=
le_Inf $ λ x hxA, (HA hxA) ▸ (M $ Inf_le hxA)

instance : complete_lattice (fixed_points f) :=
{ le           := subrel (≤) _,
  le_refl      := λ x, le_refl x,
  le_trans     := λ x y z, le_trans,
  le_antisymm  := λ x y hx hy, subtype.eq $ le_antisymm hx hy,

  sup          := λ x y, ⟨next f (x.1 ⊔ y.1), next.fixed M (sup_le_f_of_fixed_points f M x y)⟩,
  le_sup_left  := λ x y, show x.1 ≤ _, from le_trans le_sup_left next.le,
  le_sup_right := λ x y, show y.1 ≤ _, from le_trans le_sup_right next.le,
  sup_le       := λ x y z hxz hyz, lfp_le $ sup_le (sup_le hxz hyz) (z.2.symm ▸ le_refl z.1),

  inf          := λ x y, ⟨previous f (x.1 ⊓ y.1), previous.fixed M (f_le_inf_of_fixed_points f M x y)⟩,
  inf_le_left  := λ x y, show _ ≤ x.1, from le_trans previous.le inf_le_left,
  inf_le_right := λ x y, show _ ≤ y.1, from le_trans previous.le inf_le_right,
  le_inf       := λ x y z hxy hxz, le_gfp $ le_inf (le_inf hxy hxz) (x.2.symm ▸ le_refl x),

  top          := ⟨previous f ⊤, previous.fixed M le_top⟩,
  le_top       := λ ⟨x, H⟩, le_gfp $ le_inf le_top (H.symm ▸ le_refl x),

  bot          := ⟨next f ⊥, next.fixed M bot_le⟩,
  bot_le       := λ ⟨x, H⟩, lfp_le $ sup_le bot_le (H.symm ▸ le_refl x),

  Sup          := λ A, ⟨next f (Sup $ subtype.val '' A), next.fixed M (Sup_le_f_of_fixed_points f M (subtype.val '' A) (λ z ⟨x, hx⟩, hx.2 ▸ x.2))⟩,
  le_Sup       := λ A x hxA, show x.1 ≤ _, from le_trans
                    (le_Sup $ show x.1 ∈ subtype.val '' A, from ⟨x, hxA, rfl⟩)
                    next.le,
  Sup_le       := λ A x Hx, lfp_le $ sup_le (Sup_le $ λ z ⟨y, hyA, hyz⟩, hyz ▸ Hx y hyA) (x.2.symm ▸ le_refl x),

  Inf          := λ A, ⟨previous f (Inf $ subtype.val '' A), previous.fixed M (f_le_Inf_of_fixed_points f M (subtype.val '' A) (λ z ⟨x, hx⟩, hx.2 ▸ x.2))⟩,
  le_Inf       := λ A x Hx, le_gfp $ le_inf (le_Inf $ λ z ⟨y, hyA, hyz⟩, hyz ▸ Hx y hyA) (x.2.symm ▸ le_refl x.1),
  Inf_le       := λ A x hxA, show _ ≤ x.1, from le_trans
                    previous.le
                    (Inf_le $ show x.1 ∈ subtype.val '' A, from ⟨x, hxA, rfl⟩) }

end fixed_points
