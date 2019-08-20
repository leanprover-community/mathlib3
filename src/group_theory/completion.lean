import ring_theory.localization2

variables (X : Type*) [comm_monoid X]
          {Y : Type*} [comm_monoid Y] {Z : Type*} [comm_monoid Z]

local notation `top` := (⊤ : submonoid X)

@[reducible] def completion := (submonoid.r (⊤ : submonoid X)).quotient

namespace completion

instance top_coe : has_coe X top := ⟨λ x, ⟨x, set.mem_univ x⟩⟩

def of : X →* completion X := localization.monoid_hom.of top
def r : X × X → X × X → Prop := λ x y, (⊤ : submonoid X).r (x.1, x.2) (y.1, y.2)

@[elab_as_eliminator, reducible]
def lift₁ {β : Type*} (f : X × X → β) (H : ∀ (a b : X × X), r X a b → f a = f b) :
  completion X → β :=
localization.lift₁ top (λ x, f (x.1, (x.2 : X))) $ λ x y, H (x.1, x.2) (y.1, y.2)

variables {X}
def mk (x y : X) : completion X := localization.mk x y
@[simp] lemma top_coe_mul {x y : X} : (((x*y) : X) : top) = (x : top) * (y : top) := rfl
@[simp] lemma top_coe_apply (x : X) : ((x : top) : X) = x := rfl
lemma top_coe_inj {x y : X} (h : (x : top) = y) : x = y :=
by rw [←top_coe_apply x, ←top_coe_apply y, h]

@[simp] lemma mk_mul_mk (x y s t : X) :
  mk x s * mk y t = mk (x * y) (s * t) := rfl

@[elab_as_eliminator]
theorem ind {p : completion X → Prop} (H : ∀ (y : X × X), p (mk y.1 y.2))
  (x : completion X) : p x :=
by {apply localization.ind, intro y, convert H (y.1, (y.2 : X)), cases y, cases y_snd, refl}

@[elab_as_eliminator]
theorem induction_on {p : completion X → Prop} (x : completion X)
  (H : ∀ (y : X × X), p (mk y.1 y.2)) : p x := ind H x

instance : has_inv (completion X) :=
⟨lift₁ X (λ x, (mk x.2 x.1)) $
λ a b ⟨w, hw⟩, con.eq.2 $ ⟨w, by {dsimp at hw ⊢, rw [mul_comm a.2, mul_comm b.2, hw]}⟩⟩

def inv : completion X →* completion X :=
⟨λ x, x⁻¹, rfl, λ x y, by rcases x; rcases y; refl⟩

@[simp] lemma inv_apply (x :  X × X) :
(mk x.1 x.2)⁻¹ = mk x.2 x.1 := rfl

@[simp] lemma mk_self {x : X} : mk x x = 1 :=
by apply localization.mk_self

protected lemma mul_left_inv (x : completion X) : x⁻¹ * x = 1 :=
begin
  apply induction_on x,
  intro y, simp [mul_comm],
end

instance : comm_group (completion X) :=
{  inv := has_inv.inv,
   mul_left_inv := completion.mul_left_inv,
   ..localization.comm_monoid}

noncomputable def completion_of_group_equiv {G : Type*} [comm_group G] : G ≃* completion G :=
let H : ∀ g : G, is_unit (monoid_hom.id G g) := λ g, ⟨(lift g : units G), by refl⟩ in
{ to_fun := localization.monoid_hom.of (⊤ : submonoid G),
  inv_fun := localization.monoid_hom.lift (monoid_hom.id G) $ λ (g : (⊤ : submonoid G)), H (g : G),
  left_inv := λ x, localization.monoid_hom.lift_of _ x,
  right_inv := λ x, begin
      apply localization.induction_on x,
      intro z,
      have : (lift (z.2 : G) : units G) = classical.some (H (z.2 : G)), by
       { ext, show monoid_hom.id G z.2 = _, apply classical.some_spec (H (z.2 : G))},
      apply localization.r_of_eq,
      rw [localization.monoid_hom.lift, localization.monoid_hom.lift'_mk, ←this],
      show 1 * z.1 = (z.2 : G) * (z.1 * (z.2 : G)⁻¹),
      simp [mul_comm z.1]
    end,
   map_mul' := monoid_hom.map_mul _}

end completion

namespace completion_functor

def obj := completion X

instance : comm_group (completion_functor.obj X) :=
by unfold completion_functor.obj; apply_instance

variables {X}

def map (f : X →* Y) : completion X →* completion Y :=
localization.monoid_hom.map f $ λ y, submonoid.mem_top (f y)

theorem map_id : map (monoid_hom.id X) = monoid_hom.id (completion X) :=
localization.monoid_hom.map_id

theorem map_comp (f : X →* Y) (g : Y →* Z) : map (g.comp f) = (map g).comp (map f) :=
(localization.monoid_hom.map_comp_map g (λ (x : top), submonoid.mem_top (f x))
(λ (y : (⊤ : submonoid Y)), submonoid.mem_top (g y))).symm

end completion_functor

namespace completion

variables (G : Type*) [comm_group G] {H : Type*} [comm_group H]

namespace adjunction

variables (X G)

noncomputable def hom_equiv : (completion_functor.obj X →* G) ≃ (X →* G) :=
{ to_fun := λ f, f.comp (localization.monoid_hom.of top),
  inv_fun := λ f, localization.monoid_hom.lift f $ λ (x : top), ⟨(lift (f (x : X)) : units G), rfl⟩,
  left_inv := λ f, localization.monoid_hom.lift_apply_of f,
  right_inv := λ f, @localization.monoid_hom.lift_comp_of X _ top G _ f
    (λ (x : top), ⟨(lift (f (x : X)) : units G), rfl⟩)}

variables {X G}

theorem naturality_left_symm (f : X →* Y) (g : Y →* G) :
 (hom_equiv X G).symm (g.comp f) = ((hom_equiv Y G).symm g).comp (completion_functor.map f) :=
begin
  symmetry,
  rw equiv.eq_symm_apply,
  show ((localization.monoid_hom.lift g _).comp
    (localization.monoid_hom.map f _)).comp (localization.monoid_hom.of top) = g.comp f,
  rw [monoid_hom.comp_assoc, localization.monoid_hom.map_comp_of, ←monoid_hom.comp_assoc,
      localization.monoid_hom.lift_comp_of],
end

end adjunction

open localization fraction_ring
variables (R : Type*) [integral_domain R] [decidable_eq R]

lemma units.mk0_mul {α : Type*} [discrete_field α] (a b : α) (ha : a ≠ 0) (hb : b ≠ 0) :
  units.mk0 (a*b) (mul_ne_zero ha hb) = units.mk0 a ha * units.mk0 b hb :=
by ext; refl

def non_zero_divisors_map : (non_zero_divisors R) →* units (fraction_ring R) :=
{ to_fun := λ x, units.mk0 (fraction_ring.of R x.1)
    (λ h, absurd (eq_zero_of x.1 h) (mem_non_zero_divisors_iff_ne_zero.1 x.2)),
  map_one' := by ext; refl,
  map_mul' := λ x y, by ext; convert (fraction_ring.of R).map_mul _ _}

@[simp] lemma non_zero_divisors_map_apply (x : non_zero_divisors R) :
  non_zero_divisors_map R x = units.mk0 (fraction_ring.of R (x : R))
  (λ h, absurd (eq_zero_of x.1 h) (mem_non_zero_divisors_iff_ne_zero.1 x.2)) := rfl

noncomputable def fraction_ring_units_equiv :
  completion (non_zero_divisors R) ≃* units (fraction_ring R) :=
let H : ∀ w : non_zero_divisors R, is_unit (non_zero_divisors_map R w) :=
(λ x, ⟨lift (non_zero_divisors_map R x), rfl⟩) in
mul_equiv.equiv_of_char_pred (non_zero_divisors_map R)
(λ w, H (w : non_zero_divisors R)) $ by
{ split,
    intro y,
    cases exists_rep (y : fraction_ring R) with w hw,
    have h0 : w.1 ≠ 0,
    by { assume h, suffices : (y : fraction_ring R) = 0, by simpa,
         rw ←hw, apply r_of_eq, rw h, simp},
    use mk (⟨w.1, mem_non_zero_divisors_iff_ne_zero.2 h0⟩) w.2,
    ext,
    rw [←hw, ←units.mk0_val (λ (h : localization.mk w.1 w.2 = 0),
      let ⟨t, ht⟩ := localization.eq.1 h in
      absurd (eq_zero_of_ne_zero_of_mul_eq_zero h0 (by simpa using ht))
             (mem_non_zero_divisors_iff_ne_zero.1 t.2))],
    congr,
    erw monoid_hom.lift_mk,
    have : (lift (non_zero_divisors_map R w.2 : units _) : units (units _)) = classical.some (H w.2),
      by {apply units.ext, show non_zero_divisors_map R w.2 = _, apply classical.some_spec (H w.2)},
    dsimp,
    erw [←this, non_zero_divisors_map_apply, units.coe_inv, _root_.lift, mul_inv_eq_iff_eq_mul,
         ←units.mk0_mul, units.units.mk0_inj, mul_comm, of_mul_mk, mul_comm ↑w.2,
         mk_mul_cancel_right],
    refl,
  ext x y,
  split,
    intro h,
    use 1,
    simp [subtype.ext.2 (of.injective ((units.units.mk0_inj _ _).1 ((con.ker_rel _).1 h)))],
  rintro ⟨t, ht⟩,
  rw [con.ker_rel, non_zero_divisors_map_apply, non_zero_divisors_map_apply, units.units.mk0_inj,
      ←units.mul_left_inj (units.mk0 (fraction_ring.of R (t : non_zero_divisors R) : _)
      (λ h, absurd (eq_zero_of _ h) $ mem_non_zero_divisors_iff_ne_zero.1 t.1.2)), units.mk0_val,
      ←(fraction_ring.of R).map_mul, ←(fraction_ring.of R).map_mul, ←submonoid.coe_mul,
      ←submonoid.coe_mul],
  exact congr_arg (fraction_ring.of R) (congr_arg (subtype.val) (by simpa using ht))}

end completion
