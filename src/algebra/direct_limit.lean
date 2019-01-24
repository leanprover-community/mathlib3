import linear_algebra.direct_sum_module

universes u v w
#check directed
#check @directed.finset_le
#check submodule.Union_coe_of_directed
#check dfinsupp
open lattice

class directed_order (α : Type u) extends partial_order α :=
(directed : ∀ i j : α, ∃ k, i ≤ k ∧ j ≤ k)

variables {ι : out_param (Type u)} [inhabited ι]
variables [directed_order ι] [decidable_eq ι]
variables {G : ι → Type v}

class directed_system (f : Π i j, i ≤ j → G i → G j) : Prop :=
(Hid : ∀ i x, f i i (le_refl i) x = x)
(Hcomp : ∀ i j k hij hjk x, f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x)

section module
variables [Π i, decidable_eq (G i)] {R : Type w} [comm_ring R]
variables [Π i, add_comm_group (G i)] [Π i, module R (G i)]

def direct_limit.submodule (f : Π i j, i ≤ j → G i →ₗ G j) :
  submodule R (direct_sum R ι G) :=
submodule.span $ ⋃ i j (H : i ≤ j) x,
{ @direct_sum.of _ _ ι _ G _ _ i x - direct_sum.of G j (f i j H x) }

end module

/-theorem le_sup_left {α : Type u} [directed_order α] {x y : α} : x ≤ x ⊔ y :=
directed_order.le_sup_left x y

theorem le_sup_right {α : Type u} [directed_order α] {x y : α} : y ≤ x ⊔ y :=
directed_order.le_sup_right x y

variables {ι : out_param (Type u)} [inhabited ι] [directed_order ι]
variables {G : ι → Type v}

def direct_limit.setoid (f : Π i j, i ≤ j → G i → G j)
  [directed_system f] : setoid (sigma G) :=
⟨λ i j, ∃ k (hik : i.1 ≤ k) (hjk : j.1 ≤ k), f i.1 k hik i.2 = f j.1 k hjk j.2,
 λ i, ⟨i.1, le_refl i.1, le_refl i.1, rfl⟩,
 λ i j ⟨k, hik, hjk, H⟩, ⟨k, hjk, hik, H.symm⟩,
 λ i j k ⟨ij, hiij, hjij, hij⟩ ⟨jk, hjjk, hkjk, hjk⟩,
   ⟨ij ⊔ jk, le_trans hiij le_sup_left, le_trans hkjk le_sup_right,
    calc  f i.1 (ij ⊔ jk) _ i.2
        = f ij (ij ⊔ jk) _ (f i.1 ij _ i.2) : eq.symm $ directed_system.Hcomp f _ _ _ _ _ _
    ... = f ij (ij ⊔ jk) _ (f j.1 ij _ j.2) : congr_arg _ hij
    ... = f j.1 (ij ⊔ jk) _ j.2 : directed_system.Hcomp f _ _ _ _ _ _
    ... = f jk (ij ⊔ jk) _ (f j.1 jk _ j.2) : eq.symm $ directed_system.Hcomp f _ _ _ _ _ _
    ... = f jk (ij ⊔ jk) _ (f k.1 jk _ k.2) : congr_arg _ hjk
    ... = f k.1 (ij ⊔ jk) _ k.2 : directed_system.Hcomp f _ _ _ _ _ _⟩⟩

local attribute [instance] direct_limit.setoid

def direct_limit (f : Π i j, i ≤ j → G i → G j)
  [directed_system f] : Type (max u v) :=
quotient (direct_limit.setoid f)

namespace direct_limit

variables (f : Π i j, i ≤ j → G i → G j) [directed_system f]

def of (i x) : direct_limit f :=
⟦⟨i, x⟩⟧

theorem of_f {i j hij x} : (of f j (f i j hij x)) = of f i x :=
quotient.sound ⟨j, le_refl j, hij, directed_system.Hcomp f _ _ _ _ _ _⟩

variables {P : Type*} (g : Π i, G i → P)
variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

def rec (x : direct_limit f) : P :=
quotient.lift_on x (λ i, g i.1 i.2) $
λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨t, hpt, hqt, hpqt⟩,
calc  g p xp
    = g t (f p t hpt xp) : eq.symm $ Hg p t hpt xp
... = g t (f q t hqt xq) : congr_arg _ hpqt
... = g q xq : Hg q t hqt xq

lemma rec_of {i} (x) : rec f g Hg (of f i x) = g i x := rfl

theorem rec_unique (F : direct_limit f → P)
  (HF : ∀ i x, F (of f i x) = g i x) (x) :
  F x = rec f g Hg x :=
quotient.induction_on x $ λ ⟨i, x⟩, HF i x

end direct_limit

namespace directed_system

variables [∀ i, add_comm_group (G i)] (f : Π i j, i ≤ j → G i → G j)
variables [∀ i j h, is_add_group_hom (f i j h)] [directed_system f]

theorem map_add {i j k m xi xj hik hjk hkm} :
  f k m hkm (f i k hik xi + f j k hjk xj) = f i m (le_trans hik hkm) xi + f j m (le_trans hjk hkm) xj :=
(is_add_group_hom.add _ _ _).trans $
congr_arg₂ (+) (directed_system.Hcomp f _ _ _ _ _ _) (directed_system.Hcomp f _ _ _ _ _ _)

theorem add {i j hij x y} : f i j hij (x + y) = f i j hij x + f i j hij y :=
is_add_group_hom.add _ _ _

theorem zero {i j hij} : f i j hij 0 = 0 :=
is_add_group_hom.zero _

theorem neg {i j hij x} : f i j hij (-x) = -f i j hij x :=
is_add_group_hom.neg _ _

end directed_system

namespace directed_system

variables [∀ i, ring (G i)] (f : Π i j, i ≤ j → G i → G j)
variables [∀ i j h, is_ring_hom (f i j h)] [directed_system f]

theorem map_mul {i j k m xi xj hik hjk hkm} :
  f k m hkm (f i k hik xi * f j k hjk xj) = f i m (le_trans hik hkm) xi * f j m (le_trans hjk hkm) xj :=
(is_ring_hom.map_mul _).trans $
congr_arg₂ (*) (directed_system.Hcomp f _ _ _ _ _ _) (directed_system.Hcomp f _ _ _ _ _ _)

theorem mul {i j hij x y} : f i j hij (x * y) = f i j hij x * f i j hij y :=
is_ring_hom.map_mul _

theorem one {i j hij} : f i j hij 1 = 1 :=
is_ring_hom.map_one _

end directed_system

namespace direct_limit

variables [∀ i, add_comm_group (G i)] (f : Π i j, i ≤ j → G i → G j)
variables [∀ i j h, is_add_group_hom (f i j h)] [directed_system f]

local attribute [instance] direct_limit.setoid

instance add_comm_group' : add_comm_group (quotient (direct_limit.setoid f)) :=
{ add := λ i j, quotient.lift_on₂ i j
    (λ xi xj, ⟦⟨xi.1 ⊔ xj.1, f xi.1 (xi.1 ⊔ xj.1) le_sup_left xi.2 +
      f xj.1 (xi.1 ⊔ xj.1) le_sup_right xj.2⟩⟧ : sigma G → sigma G → quotient (direct_limit.setoid f))
    (λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩ ⟨s, xs⟩ ⟨t, hpt, hrt, hprt⟩ ⟨u, hqu, hsu, hqsu⟩, quotient.sound $
      ⟨(p ⊔ q) ⊔ (r ⊔ s) ⊔ (t ⊔ u),
       le_trans le_sup_left le_sup_left,
       le_trans le_sup_right le_sup_left,
       calc   f (p ⊔ q) (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) (le_trans le_sup_left le_sup_left)
                (f p (p ⊔ q) le_sup_left xp + f q (p ⊔ q) le_sup_right xq)
          =   f p (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) (le_trans hpt (le_trans le_sup_left le_sup_right)) xp
            + f q (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) (le_trans hqu (le_trans le_sup_right le_sup_right)) xq :
        directed_system.map_add f
      ... =   f t (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ (f p t hpt xp)
            + f u (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ (f q u hqu xq) :
        congr_arg₂ (+) (directed_system.Hcomp f _ _ _ _ _ _).symm (directed_system.Hcomp f _ _ _ _ _ _).symm
      ... =   f t (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ (f r t hrt xr)
            + f u (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ (f s u hsu xs) :
        congr_arg₂ (+) (congr_arg _ hprt) (congr_arg _ hqsu)
      ... =   f r (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ xr
            + f s (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ xs :
        congr_arg₂ (+) (directed_system.Hcomp f _ _ _ _ _ _) (directed_system.Hcomp f _ _ _ _ _ _)
      ... =   f (r ⊔ s) (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) (le_trans le_sup_right le_sup_left)
                (f r (r ⊔ s) le_sup_left xr + f s (r ⊔ s) le_sup_right xs) :
        eq.symm $ directed_system.map_add f⟩),
  add_assoc := λ i j k, quotient.induction_on₃ i j k $ λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩, quotient.sound
    ⟨((p ⊔ q) ⊔ r) ⊔ (p ⊔ (q ⊔ r)), le_sup_left, le_sup_right,
     by dsimp; simp [directed_system.map_add f, directed_system.add f, directed_system.Hcomp f, -add_comm]⟩,
  zero := ⟦⟨default _, 0⟩⟧,
  zero_add := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound
    ⟨default _ ⊔ p, le_refl _, le_sup_right,
     by dsimp; simp [directed_system.map_add f, directed_system.zero f, directed_system.Hcomp f]⟩,
  add_zero := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound
    ⟨p ⊔ default ι, le_refl _, le_sup_left,
     by dsimp; simp [directed_system.map_add f, directed_system.zero f, directed_system.Hcomp f]⟩,
  neg := λ i, quotient.lift_on i (λ p, ⟦⟨p.1, -p.2⟩⟧ : sigma G → quotient (direct_limit.setoid f)) $
    λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨t, hpt, hqt, hpqt⟩, quotient.sound $
    ⟨t, hpt, hqt, by dsimp at hpqt ⊢; simp [directed_system.neg f, hpqt]⟩,
  add_left_neg := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound $
    ⟨(p ⊔ p) ⊔ default ι, le_sup_left, le_sup_right,
     by dsimp; simp [directed_system.map_add f, directed_system.neg f, directed_system.zero f]⟩,
  add_comm := λ i j, quotient.induction_on₂ i j $ λ ⟨p, xp⟩ ⟨q, xq⟩, quotient.sound
    ⟨(p ⊔ q) ⊔ (q ⊔ p), le_sup_left, le_sup_right,
     by dsimp; simp [directed_system.map_add f]⟩ }

instance : add_comm_group (direct_limit f) :=
direct_limit.add_comm_group' f

instance of.is_add_group_hom {i} : is_add_group_hom (direct_limit.of f i) :=
is_add_group_hom.mk _ $ λ x y, quotient.sound
⟨i ⊔ i, le_sup_left, le_refl _,
 by dsimp; simp [directed_system.map_add f]; simp [directed_system.add f]⟩

theorem of.zero_exact {i x} (H : of f i x = 0) :
  ∃ p hp1, f i p hp1 x = (0 : G p) :=
let ⟨p, hp1, hp2, hp3⟩ := quotient.exact H in
⟨p, hp1, hp3.trans $ is_add_group_hom.zero _⟩

variables {P : Type*} [add_comm_group P]
variables (g : Π i, G i → P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
variables [∀ i, is_add_group_hom (g i)]

def rec.is_add_group_hom : is_add_group_hom (rec f g Hg) :=
is_add_group_hom.mk _ $ λ i j, quotient.induction_on₂ i j $ λ ⟨p, xp⟩ ⟨q, xq⟩,
calc  _ = _ : is_add_group_hom.add _ _ _
    ... = _ : congr_arg₂ (+) (Hg _ _ _ _) (Hg _ _ _ _)

end direct_limit

namespace direct_limit

variables [∀ i, ring (G i)] (f : Π i j, i ≤ j → G i → G j)
variables [∀ i j h, is_ring_hom (f i j h)] [directed_system f]

local attribute [instance] direct_limit.setoid

instance ring' : ring (quotient (direct_limit.setoid f)) :=
{ mul := λ i j, quotient.lift_on₂ i j
    (λ xi xj, ⟦⟨xi.1 ⊔ xj.1, f xi.1 (xi.1 ⊔ xj.1) le_sup_left xi.2 *
      f xj.1 (xi.1 ⊔ xj.1) le_sup_right xj.2⟩⟧ : sigma G → sigma G → quotient (direct_limit.setoid f))
    (λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩ ⟨s, xs⟩ ⟨t, hpt, hrt, hprt⟩ ⟨u, hqu, hsu, hqsu⟩, quotient.sound $
      ⟨(p ⊔ q) ⊔ (r ⊔ s) ⊔ (t ⊔ u),
       le_trans le_sup_left le_sup_left,
       le_trans le_sup_right le_sup_left,
       calc   f (p ⊔ q) (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) (le_trans le_sup_left le_sup_left)
                (f p (p ⊔ q) le_sup_left xp * f q (p ⊔ q) le_sup_right xq)
          =   f p (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) (le_trans hpt (le_trans le_sup_left le_sup_right)) xp
            * f q (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) (le_trans hqu (le_trans le_sup_right le_sup_right)) xq :
        directed_system.map_mul f
      ... =   f t (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ (f p t hpt xp)
            * f u (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ (f q u hqu xq) :
        congr_arg₂ (*) (directed_system.Hcomp f _ _ _ _ _ _).symm (directed_system.Hcomp f _ _ _ _ _ _).symm
      ... =   f t (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ (f r t hrt xr)
            * f u (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ (f s u hsu xs) :
        congr_arg₂ (*) (congr_arg _ hprt) (congr_arg _ hqsu)
      ... =   f r (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ xr
            * f s (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) _ xs :
        congr_arg₂ (*) (directed_system.Hcomp f _ _ _ _ _ _) (directed_system.Hcomp f _ _ _ _ _ _)
      ... =   f (r ⊔ s) (p ⊔ q ⊔ (r ⊔ s) ⊔ (t ⊔ u)) (le_trans le_sup_right le_sup_left)
                (f r (r ⊔ s) le_sup_left xr * f s (r ⊔ s) le_sup_right xs) :
        eq.symm $ directed_system.map_mul f⟩),
  mul_assoc := λ i j k, quotient.induction_on₃ i j k $ λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩, quotient.sound
    ⟨((p ⊔ q) ⊔ r) ⊔ (p ⊔ (q ⊔ r)), le_sup_left, le_sup_right,
     by dsimp; simp [directed_system.map_mul f, directed_system.mul f, directed_system.Hcomp f, mul_assoc]⟩,
  one := ⟦⟨default _, 1⟩⟧,
  one_mul := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound
    ⟨default _ ⊔ p, le_refl _, le_sup_right,
     by dsimp; simp [directed_system.map_mul f, directed_system.one f, directed_system.Hcomp f]⟩,
  mul_one := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound
    ⟨p ⊔ default ι, le_refl _, le_sup_left,
     by dsimp; simp [directed_system.map_mul f, directed_system.one f, directed_system.Hcomp f]⟩,
  left_distrib := λ i j k, quotient.induction_on₃ i j k $ λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩, quotient.sound
    ⟨p ⊔ (q ⊔ r) ⊔ (p ⊔ q ⊔ (p ⊔ r)), le_sup_left, le_sup_right,
     by dsimp; simp [directed_system.add f, directed_system.mul f, directed_system.Hcomp f, mul_add]⟩,
  right_distrib := λ i j k, quotient.induction_on₃ i j k $ λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩, quotient.sound
    ⟨p ⊔ q ⊔ r ⊔ (p ⊔ r ⊔ (q ⊔ r)), le_sup_left, le_sup_right,
     by dsimp; simp [directed_system.add f, directed_system.mul f, directed_system.Hcomp f, add_mul]⟩,
  .. direct_limit.add_comm_group' f }

instance: ring (direct_limit f) :=
direct_limit.ring' f

instance of.is_ring_hom {i} : is_ring_hom (direct_limit.of f i) :=
{ map_add := is_add_group_hom.add _,
  map_mul := λ x y, quotient.sound ⟨i ⊔ i, le_sup_left, le_refl _,
    by dsimp; simp [directed_system.mul f, directed_system.Hcomp f]⟩,
  map_one := quotient.sound ⟨i ⊔ default _, le_sup_left, le_sup_right,
    by dsimp; simp [directed_system.one f]⟩ }

theorem of.one_exact {i x} (H : of f i x = 1) :
  ∃ p hp1, f i p hp1 x = (1 : G p) :=
let ⟨p, hp1, hp2, hp3⟩ := quotient.exact H in
⟨p, hp1, hp3.trans $ is_ring_hom.map_one _⟩

variables {P : Type*} [ring P]
variables (g : Π i, G i → P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
variables [∀ i, is_ring_hom (g i)]

local attribute [instance] rec.is_add_group_hom

def rec.is_ring_hom : is_ring_hom (rec f g Hg) :=
{ map_add := is_add_group_hom.add _,
  map_mul := λ i j, quotient.induction_on₂ i j $ λ ⟨p, xp⟩ ⟨q, xq⟩,
    calc  _ = _ : is_ring_hom.map_mul _
        ... = _ : congr_arg₂ (*) (Hg _ _ _ _) (Hg _ _ _ _),
  map_one := show g (default _) 1 = 1, from is_ring_hom.map_one _ }

end direct_limit

namespace direct_limit

variables [∀ i, comm_ring (G i)] (f : Π i j, i ≤ j → G i → G j)
variables [∀ i j h, is_ring_hom (f i j h)] [directed_system f]

local attribute [instance] direct_limit.setoid

instance comm_ring' : comm_ring (quotient (direct_limit.setoid f)) :=
{
  mul_comm := λ i j, quotient.induction_on₂ i j $ λ ⟨p, xp⟩ ⟨q, xq⟩, quotient.sound
    ⟨(p ⊔ q) ⊔ (q ⊔ p), le_sup_left, le_sup_right,
     by dsimp; simp [directed_system.map_mul f, directed_system.mul f, directed_system.Hcomp f, mul_comm]⟩
  .. direct_limit.ring' f }

instance: comm_ring (direct_limit f) :=
direct_limit.comm_ring' f

end direct_limit
-/