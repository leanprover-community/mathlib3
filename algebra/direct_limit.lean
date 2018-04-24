import algebra.ring order.lattice

universes u v

theorem congr_arg₂ {α β γ : Type*} (f : α → β → γ) {x₁ x₂ : α} {y₁ y₂ : β}
  (Hx : x₁ = x₂) (Hy : y₁ = y₂) : f x₁ y₁ = f x₂ y₂ :=
eq.drec (eq.drec rfl Hy) Hx

open lattice

def is_add_group_hom {α : Type*} {β : Type*} [add_group α] [add_group β] (f : α → β) : Prop :=
@is_group_hom (multiplicative α) (multiplicative β) _ _ f

attribute [class] is_add_group_hom

namespace is_add_group_hom

variables {α : Type*} {β : Type*} [add_group α] [add_group β] (f : α → β) [hf : is_add_group_hom f]

theorem add (x y) : f (x + y) = f x + f y :=
@is_group_hom.mul (multiplicative α) (multiplicative β) _ _ f hf x y

theorem zero : f 0 = 0 :=
@is_group_hom.one (multiplicative α) (multiplicative β) _ _ f hf

theorem neg (x) : f (-x) = -f x :=
@is_group_hom.inv (multiplicative α) (multiplicative β) _ _ f hf x

end is_add_group_hom

instance is_ring_hom.to_is_add_group_hom {α : Type*} {β : Type*} [ring α] [ring β]
  (f : α → β) [is_ring_hom f] : is_add_group_hom f :=
⟨λ _ _, is_ring_hom.map_add f⟩

variables {ι : out_param (Type u)} [inhabited ι] [semilattice_sup ι] {G : ι → Type v}

section add_comm_group

class directed_system (f : Π i j, i ≤ j → G i → G j) : Prop :=
(Hid : ∀ i x, f i i (le_refl i) x = x)
(Hcomp : ∀ i j k hij hjk x, f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x)

variables [∀ i, add_comm_group (G i)] (f : Π i j, i ≤ j → G i → G j)
variables [∀ i j h, is_add_group_hom (f i j h)] [directed_system f]

instance direct_limit.setoid : setoid (sigma G) :=
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

def direct_limit : Type (max u v) :=
quotient (direct_limit.setoid f)

instance direct_limit.add_comm_group' : add_comm_group (quotient (direct_limit.setoid f)) :=
{ add := λ i j, quotient.lift_on₂ i j
    (λ xi xj, ⟦⟨xi.1 ⊔ xj.1, f xi.1 (xi.1 ⊔ xj.1) le_sup_left xi.2 +
      f xj.1 (xi.1 ⊔ xj.1) le_sup_right xj.2⟩⟧ : sigma G → sigma G → quotient (direct_limit.setoid f))
    (λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩ ⟨s, xs⟩ ⟨t, hpt, hrt, hprt⟩ ⟨u, hqu, hsu, hqsu⟩, quotient.sound $
      ⟨t ⊔ u,
       sup_le (le_trans hpt le_sup_left) (le_trans hqu le_sup_right),
       sup_le (le_trans hrt le_sup_left) (le_trans hsu le_sup_right),
       calc   f (p ⊔ q) (t ⊔ u) _
                (f p (p ⊔ q) le_sup_left xp + f q (p ⊔ q) le_sup_right xq)
          =   f (p ⊔ q) (t ⊔ u) _ (f p (p ⊔ q) le_sup_left xp)
            + f (p ⊔ q) (t ⊔ u) _ (f q (p ⊔ q) le_sup_right xq) :
        is_add_group_hom.add _ _ _
      ... =   f p (t ⊔ u) _ xp + f q (t ⊔ u) _ xq :
        congr_arg₂ (+) (directed_system.Hcomp f _ _ _ _ _ _) (directed_system.Hcomp f _ _ _ _ _ _)
      ... =   f p (t ⊔ u) (le_trans hpt le_sup_left) xp + f q (t ⊔ u) (le_trans hqu le_sup_right) xq : rfl
      ... =   f t (t ⊔ u) le_sup_left (f p t hpt xp) + f u (t ⊔ u) le_sup_right (f q u hqu xq) :
        congr_arg₂ (+) (directed_system.Hcomp f _ _ _ _ _ _).symm (directed_system.Hcomp f _ _ _ _ _ _).symm
      ... =   f t (t ⊔ u) le_sup_left (f r t hrt xr) + f u (t ⊔ u) le_sup_right (f s u hsu xs) :
        congr_arg₂ (+) (congr_arg _ hprt) (congr_arg _ hqsu)
      ... =   _ : congr_arg₂ (+) (directed_system.Hcomp f _ _ _ _ _ _) (directed_system.Hcomp f _ _ _ _ _ _)
      ... =   f r (t ⊔ u) (le_trans le_sup_left (sup_le (le_trans hrt le_sup_left) (le_trans hsu le_sup_right))) xr
            + f s (t ⊔ u) (le_trans le_sup_right (sup_le (le_trans hrt le_sup_left) (le_trans hsu le_sup_right))) xs : rfl
      ... =   _ : congr_arg₂ (+) (directed_system.Hcomp f _ _ _ _ _ _).symm (directed_system.Hcomp f _ _ _ _ _ _).symm
      ... =   f (r ⊔ s) (t ⊔ u) _ (f r (r ⊔ s) le_sup_left xr + f s (r ⊔ s) le_sup_right xs) :
        (is_add_group_hom.add _ _ _).symm ⟩),
  add_assoc := λ i j k, quotient.induction_on₃ i j k $ λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩, quotient.sound
    ⟨p ⊔ q ⊔ r, le_refl _, le_of_eq sup_assoc.symm, begin
      dsimp,
      rw is_add_group_hom.add (f (p ⊔ q) (p ⊔ q ⊔ r) le_sup_left),
      rw is_add_group_hom.add (f (q ⊔ r) (p ⊔ (q ⊔ r)) le_sup_right),
      rw is_add_group_hom.add (f (p ⊔ q ⊔ r) (p ⊔ q ⊔ r) (le_refl (p ⊔ q ⊔ r))),
      rw is_add_group_hom.add (f (p ⊔ q ⊔ r) (p ⊔ q ⊔ r) (le_refl (p ⊔ q ⊔ r))),
      rw is_add_group_hom.add (f (p ⊔ (q ⊔ r)) (p ⊔ q ⊔ r) (le_of_eq (eq.symm sup_assoc))),
      rw is_add_group_hom.add (f (p ⊔ (q ⊔ r)) (p ⊔ q ⊔ r) (le_of_eq (eq.symm sup_assoc))),
      repeat { rw directed_system.Hcomp f },
      apply add_assoc
    end⟩,
  zero := ⟦⟨default _, 0⟩⟧,
  zero_add := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound
    ⟨default _ ⊔ p, le_refl _, le_sup_right, begin
      dsimp,
      rw is_add_group_hom.add (f (default ι ⊔ p) (default ι ⊔ p) (le_refl (default ι ⊔ p))),
      repeat { rw directed_system.Hcomp f },
      rw is_add_group_hom.zero (f (default ι) (default ι ⊔ p) (le_trans le_sup_left (le_refl (default ι ⊔ p)))),
      apply zero_add
    end⟩,
  add_zero := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound
    ⟨p ⊔ default ι, le_refl _, le_sup_left, begin
      dsimp,
      rw is_add_group_hom.add (f (p ⊔ default ι) (p ⊔ default ι) (le_refl (p ⊔ default ι))),
      repeat { rw directed_system.Hcomp f },
      rw is_add_group_hom.zero (f (default ι) (p ⊔ default ι) (le_trans le_sup_right (le_refl (p ⊔ default ι)))),
      apply add_zero
    end⟩,
  neg := λ i, quotient.lift_on i (λ p, ⟦⟨p.1, -p.2⟩⟧ : sigma G → quotient (direct_limit.setoid f)) $
    λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨t, hpt, hqt, hpqt⟩, quotient.sound $
    ⟨t, hpt, hqt, by dsimp at hpqt ⊢; rw [is_add_group_hom.neg (f p t hpt), is_add_group_hom.neg (f q t hqt), hpqt]⟩,
  add_left_neg := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound $
    ⟨(p ⊔ p) ⊔ default ι, le_sup_left, le_sup_right, begin
      dsimp,
      rw is_add_group_hom.add (f (p ⊔ p) (p ⊔ p ⊔ default ι) le_sup_left),
      repeat { rw directed_system.Hcomp f },
      rw is_add_group_hom.neg (f p (p ⊔ p ⊔ default ι) (le_trans le_sup_left le_sup_left)),
      rw is_add_group_hom.zero (f (default ι) (p ⊔ p ⊔ default ι) le_sup_right),
      apply add_left_neg
    end⟩,
  add_comm := λ i j, quotient.induction_on₂ i j $ λ ⟨p, xp⟩ ⟨q, xq⟩, quotient.sound
    ⟨p ⊔ q, le_refl _, le_of_eq sup_comm, begin
      dsimp,
      rw is_add_group_hom.add (f (p ⊔ q) (p ⊔ q) (le_refl (p ⊔ q))),
      rw is_add_group_hom.add (f (q ⊔ p) (p ⊔ q) (le_of_eq sup_comm)),
      repeat { rw directed_system.Hcomp f },
      apply add_comm
    end⟩ }

instance direct_limit.add_comm_group : add_comm_group (direct_limit f) :=
direct_limit.add_comm_group' f

def direct_limit.of (i) (x : G i) : direct_limit f :=
⟦⟨i, x⟩⟧

instance direct_limit.of.is_add_group_hom {i} : is_add_group_hom (direct_limit.of f i) :=
⟨λ x y, quotient.sound ⟨i, le_refl _, sup_le (le_refl _) (le_refl _),
 begin
   dsimp,
   rw is_add_group_hom.add (f (i ⊔ i) i _),
   repeat { rw directed_system.Hcomp f },
   repeat { rw directed_system.Hid f },
   refl,
   apply_instance
  end⟩⟩

theorem direct_limit.of.zero_exact {i x} (H : direct_limit.of f i x = 0) :
  ∃ p hp1, f i p hp1 x = (0 : G p) :=
let ⟨p, hp1, hp2, hp3⟩ := quotient.exact H in
⟨p, hp1, hp3.trans $ is_add_group_hom.zero _⟩

end add_comm_group

section ring

variables [∀ i, ring (G i)] (f : Π i j, i ≤ j → G i → G j)
variables [∀ i j h, is_ring_hom (f i j h)] [directed_system f]

instance direct_limit.ring' : ring (quotient (direct_limit.setoid f)) :=
{ mul := λ i j, quotient.lift_on₂ i j
    (λ xi xj, ⟦⟨xi.1 ⊔ xj.1, f xi.1 (xi.1 ⊔ xj.1) le_sup_left xi.2 *
      f xj.1 (xi.1 ⊔ xj.1) le_sup_right xj.2⟩⟧ : sigma G → sigma G → quotient (direct_limit.setoid f))
    (λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩ ⟨s, xs⟩ ⟨t, hpt, hrt, hprt⟩ ⟨u, hqu, hsu, hqsu⟩, quotient.sound $
      ⟨t ⊔ u,
       sup_le (le_trans hpt le_sup_left) (le_trans hqu le_sup_right),
       sup_le (le_trans hrt le_sup_left) (le_trans hsu le_sup_right),
       calc   f (p ⊔ q) (t ⊔ u) _
                (f p (p ⊔ q) le_sup_left xp * f q (p ⊔ q) le_sup_right xq)
          =   f (p ⊔ q) (t ⊔ u) _ (f p (p ⊔ q) le_sup_left xp)
            * f (p ⊔ q) (t ⊔ u) _ (f q (p ⊔ q) le_sup_right xq) :
        is_ring_hom.map_mul _
      ... =   f p (t ⊔ u) _ xp * f q (t ⊔ u) _ xq :
        congr_arg₂ (*) (directed_system.Hcomp f _ _ _ _ _ _) (directed_system.Hcomp f _ _ _ _ _ _)
      ... =   f p (t ⊔ u) (le_trans hpt le_sup_left) xp * f q (t ⊔ u) (le_trans hqu le_sup_right) xq : rfl
      ... =   f t (t ⊔ u) le_sup_left (f p t hpt xp) * f u (t ⊔ u) le_sup_right (f q u hqu xq) :
        congr_arg₂ (*) (directed_system.Hcomp f _ _ _ _ _ _).symm (directed_system.Hcomp f _ _ _ _ _ _).symm
      ... =   f t (t ⊔ u) le_sup_left (f r t hrt xr) * f u (t ⊔ u) le_sup_right (f s u hsu xs) :
        congr_arg₂ (*) (congr_arg _ hprt) (congr_arg _ hqsu)
      ... =   _ : congr_arg₂ (*) (directed_system.Hcomp f _ _ _ _ _ _) (directed_system.Hcomp f _ _ _ _ _ _)
      ... =   f r (t ⊔ u) (le_trans le_sup_left (sup_le (le_trans hrt le_sup_left) (le_trans hsu le_sup_right))) xr
            * f s (t ⊔ u) (le_trans le_sup_right (sup_le (le_trans hrt le_sup_left) (le_trans hsu le_sup_right))) xs : rfl
      ... =   _ : congr_arg₂ (*) (directed_system.Hcomp f _ _ _ _ _ _).symm (directed_system.Hcomp f _ _ _ _ _ _).symm
      ... =   f (r ⊔ s) (t ⊔ u) _ (f r (r ⊔ s) le_sup_left xr * f s (r ⊔ s) le_sup_right xs) :
        (is_ring_hom.map_mul _).symm ⟩),
  mul_assoc := λ i j k, quotient.induction_on₃ i j k $ λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩, quotient.sound
    ⟨p ⊔ q ⊔ r, le_refl _, le_of_eq sup_assoc.symm, begin
      dsimp,
      rw is_ring_hom.map_mul (f (p ⊔ q) (p ⊔ q ⊔ r) le_sup_left),
      rw is_ring_hom.map_mul (f (q ⊔ r) (p ⊔ (q ⊔ r)) le_sup_right),
      rw is_ring_hom.map_mul (f (p ⊔ q ⊔ r) (p ⊔ q ⊔ r) (le_refl (p ⊔ q ⊔ r))),
      rw is_ring_hom.map_mul (f (p ⊔ q ⊔ r) (p ⊔ q ⊔ r) (le_refl (p ⊔ q ⊔ r))),
      rw is_ring_hom.map_mul (f (p ⊔ (q ⊔ r)) (p ⊔ q ⊔ r) (le_of_eq (eq.symm sup_assoc))),
      rw is_ring_hom.map_mul (f (p ⊔ (q ⊔ r)) (p ⊔ q ⊔ r) (le_of_eq (eq.symm sup_assoc))),
      repeat { rw directed_system.Hcomp f },
      apply mul_assoc
    end⟩,
  one := ⟦⟨default _, 1⟩⟧,
  one_mul := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound
    ⟨default _ ⊔ p, le_refl _, le_sup_right, begin
      dsimp,
      rw is_ring_hom.map_mul (f (default ι ⊔ p) (default ι ⊔ p) (le_refl (default ι ⊔ p))),
      repeat { rw directed_system.Hcomp f },
      rw is_ring_hom.map_one (f (default ι) (default ι ⊔ p) (le_trans le_sup_left (le_refl (default ι ⊔ p)))),
      apply one_mul
    end⟩,
  mul_one := λ i, quotient.induction_on i $ λ ⟨p, xp⟩, quotient.sound
    ⟨p ⊔ default ι, le_refl _, le_sup_left, begin
      dsimp,
      rw is_ring_hom.map_mul (f (p ⊔ default ι) (p ⊔ default ι) (le_refl (p ⊔ default ι))),
      repeat { rw directed_system.Hcomp f },
      rw is_ring_hom.map_one (f (default ι) (p ⊔ default ι) (le_trans le_sup_right (le_refl (p ⊔ default ι)))),
      apply mul_one
    end⟩,
  left_distrib := λ i j k, quotient.induction_on₃ i j k $ λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩, quotient.sound
    ⟨p ⊔ (q ⊔ r) ⊔ (p ⊔ q ⊔ (p ⊔ r)), le_sup_left, le_sup_right, begin
      dsimp,
      rw is_ring_hom.map_mul (f (p ⊔ (q ⊔ r)) (p ⊔ (q ⊔ r) ⊔ (p ⊔ q ⊔ (p ⊔ r))) le_sup_left),
      rw is_ring_hom.map_add (f (q ⊔ r) (p ⊔ (q ⊔ r)) le_sup_right),
      rw is_ring_hom.map_add (f (p ⊔ (q ⊔ r)) (p ⊔ (q ⊔ r) ⊔ (p ⊔ q ⊔ (p ⊔ r))) le_sup_left),
      rw is_ring_hom.map_mul (f (p ⊔ q) (p ⊔ q ⊔ (p ⊔ r)) _),
      rw is_ring_hom.map_mul (f (p ⊔ r) (p ⊔ q ⊔ (p ⊔ r)) _),
      rw is_ring_hom.map_add (f (p ⊔ q ⊔ (p ⊔ r)) (p ⊔ (q ⊔ r) ⊔ (p ⊔ q ⊔ (p ⊔ r))) le_sup_right),
      rw is_ring_hom.map_mul (f (p ⊔ q ⊔ (p ⊔ r)) (p ⊔ (q ⊔ r) ⊔ (p ⊔ q ⊔ (p ⊔ r))) le_sup_right),
      rw is_ring_hom.map_mul (f (p ⊔ q ⊔ (p ⊔ r)) (p ⊔ (q ⊔ r) ⊔ (p ⊔ q ⊔ (p ⊔ r))) le_sup_right),
      rw left_distrib,
      repeat { rw directed_system.Hcomp f },
      repeat { apply_instance }
    end⟩,
  right_distrib := λ i j k, quotient.induction_on₃ i j k $ λ ⟨p, xp⟩ ⟨q, xq⟩ ⟨r, xr⟩, quotient.sound
    ⟨p ⊔ q ⊔ r ⊔ (p ⊔ r ⊔ (q ⊔ r)), le_sup_left, le_sup_right, begin
      dsimp,
      rw is_ring_hom.map_mul (f (p ⊔ q ⊔ r) (p ⊔ q ⊔ r ⊔ (p ⊔ r ⊔ (q ⊔ r))) le_sup_left),
      rw is_ring_hom.map_add (f (p ⊔ q) (p ⊔ q ⊔ r) le_sup_left),
      rw is_ring_hom.map_add (f (p ⊔ q ⊔ r) (p ⊔ q ⊔ r ⊔ (p ⊔ r ⊔ (q ⊔ r))) le_sup_left),
      rw is_ring_hom.map_mul (f (p ⊔ r) (p ⊔ r ⊔ (q ⊔ r)) _),
      rw is_ring_hom.map_mul (f (q ⊔ r) (p ⊔ r ⊔ (q ⊔ r)) _),
      rw is_ring_hom.map_add (f (p ⊔ r ⊔ (q ⊔ r)) (p ⊔ q ⊔ r ⊔ (p ⊔ r ⊔ (q ⊔ r))) le_sup_right),
      rw is_ring_hom.map_mul (f (p ⊔ r ⊔ (q ⊔ r)) (p ⊔ q ⊔ r ⊔ (p ⊔ r ⊔ (q ⊔ r))) le_sup_right),
      rw is_ring_hom.map_mul (f (p ⊔ r ⊔ (q ⊔ r)) (p ⊔ q ⊔ r ⊔ (p ⊔ r ⊔ (q ⊔ r))) le_sup_right),
      rw right_distrib,
      repeat { rw directed_system.Hcomp f },
      repeat { apply_instance }
    end⟩,
  .. direct_limit.add_comm_group' f }

instance direct_limit.ring : ring (direct_limit f) :=
direct_limit.ring' f

instance direct_limit.of.is_ring_hom {i} : is_ring_hom (direct_limit.of f i) :=
{ map_add := is_add_group_hom.add _,
  map_mul := λ x y, quotient.sound ⟨i, le_refl _, sup_le (le_refl _) (le_refl _),
    begin
      dsimp,
      rw is_ring_hom.map_mul (f (i ⊔ i) i _),
      repeat { rw directed_system.Hcomp f },
      repeat { rw directed_system.Hid f },
      apply_instance
     end⟩,
  map_one := quotient.sound ⟨i ⊔ default _, le_sup_left, le_sup_right,
    begin
      dsimp,
      rw is_ring_hom.map_one (f i (i ⊔ default ι) le_sup_left),
      rw is_ring_hom.map_one (f (default ι) (i ⊔ default ι) le_sup_right)
    end⟩ }

end ring
