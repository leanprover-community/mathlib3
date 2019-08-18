import ring_theory.localization2

variables {α : Type*} [monoid α] (X : Type*) [comm_monoid X]
          {Y : Type*} [comm_monoid Y] {Z : Type*} [comm_monoid Z]

local notation `top` := (⊤ : submonoid X)

@[reducible] def completion := (submonoid.r (⊤ : submonoid X)).quotient

namespace completion

instance top_coe : has_coe X top := ⟨λ x, ⟨x, set.mem_univ x⟩⟩
instance : has_coe (X × top) (completion X) := infer_instance
instance of_coe : has_coe X (completion X) := infer_instance

variables {X}

@[simp] lemma top_coe_apply (x : X) : ((x : top) : X) = x := rfl
lemma top_coe_inj {x y : X} (h : (x : top) = y) : x = y :=
by rw [←top_coe_apply x, ←top_coe_apply y, h]

instance : has_inv (completion X) :=
⟨localization.lift top (λ x, (((x.2 : X), (x.1: top)) : completion X)) $
λ a b ⟨w, hw⟩, con.eq.2 $ ⟨w, by {dsimp, rw [mul_comm _ b.1, mul_comm _ a.1, hw]}⟩⟩

def inv : completion X →* completion X :=
⟨λ x, x⁻¹, rfl, λ x y, by induction x; induction y; refl⟩

@[simp] lemma inv_apply (x :  X × top) :
(((x.2 : X), (x.1 : top)) : completion X) = x⁻¹ := rfl

@[simp] lemma coe_mul {x y : X} : (x : top) * (y : top) = ((x * y : X) : top) := rfl

@[simp] lemma coe_self {x : X} : ((x, (x : top)) : completion X) = 1 :=
by apply localization.mk_self

protected lemma mul_left_inv (x : completion X) : x⁻¹ * x = 1 :=
begin
  apply con.induction_on' x,
  rintro ⟨y1, y2⟩,
  rw [←inv_apply, ←localization.mk_apply, ←localization.mk_apply,
      localization.mk_mul_mk, mul_comm],
  apply coe_self,
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
      apply con.induction_on' x,
      intro z,
      have : (lift (z.2 : G) : units G) = classical.some (H (z.2 : G)), by
       { ext, show monoid_hom.id G z.2 = _, apply classical.some_spec (H (z.2 : G))},
      rw localization.monoid_hom.of_apply,
      apply localization.r_of_eq,
      rw [←@prod.mk.eta _ _ z, ←localization.mk_apply, localization.monoid_hom.lift,
          localization.monoid_hom.lift'_mk, ←this],
      show 1 * z.1 = (z.2 : G) * (z.1 * (z.2 : G)⁻¹),
      simp [mul_comm z.1]
    end,
   map_mul' := monoid_hom.map_mul _}

end completion

/- Redoing the adjunction without the category theory library. I don't really know how to do
   forgetful functors without the category theory library. I could map G to @set.univ G but
   that's 'too forgetful' and it's not really materially saying anything. -/
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
  left_inv := λ f, localization.monoid_hom.lift_apply_coe f,
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
  rw [←monoid_hom.comp_assoc, localization.monoid_hom.map_comp_of,
      monoid_hom.comp_assoc, localization.monoid_hom.lift_comp_of],
end

end adjunction

open localization localization.fraction_ring
variables (R : Type*) [integral_domain R] [decidable_eq R]

def non_zero_divisors_map : (non_zero_divisors R) →* units (fraction_ring R) :=
{ to_fun := λ x, units.mk0 (localization.of x.1 : fraction_ring R)
    (λ h, absurd (eq_zero_of x.1 h) (mem_non_zero_divisors_iff_ne_zero.1 x.2)),
  map_one' := by {ext, refl},
  map_mul' := λ x y, by {ext, show ↑(x.val * y.val) = ↑(x.val) * ↑(y.val),
    apply localization.coe_mul}}

noncomputable def fraction_ring_units_equiv :
  completion (non_zero_divisors R) ≃* units (fraction_ring R) :=
let H : ∀ w : non_zero_divisors R, is_unit (non_zero_divisors_map R w) :=
(λ x, ⟨lift (non_zero_divisors_map R x), rfl⟩) in
localization.mul_equiv.equiv_of_char_pred (non_zero_divisors_map R)
(λ w, H (w : non_zero_divisors R)) $ by
{ split,
    intro y,
    cases con.exists_rep (y : fraction_ring R) with w hw,
    have h0 : w.1 ≠ 0,
    by { assume h, suffices : (y : fraction_ring R) = 0, by simpa,
         rw [←hw, ←localization.coe_zero],
         apply r_of_eq, rw h, simp},
    use (((⟨w.1, mem_non_zero_divisors_iff_ne_zero.2 h0⟩, w.2) :
          (non_zero_divisors R × (⊤ : submonoid (non_zero_divisors R)))) :
            completion (non_zero_divisors R)),
    ext, rw ←hw,
    suffices : ↑((non_zero_divisors_map R) ⟨w.fst, _⟩ * ↑(classical.some _)⁻¹) = ↑w, by exact this,
    have : (lift (non_zero_divisors_map R w.2 : units (fraction_ring R)) :
            units (units (fraction_ring R))) = classical.some (H w.2), by
       { apply units.ext, show non_zero_divisors_map R w.2 = _, apply classical.some_spec (H w.2)},
    dsimp, rw [←this],
    show ((units.mk0 (of (⟨w.1, mem_non_zero_divisors_iff_ne_zero.2 h0⟩ : non_zero_divisors R).1 :
            fraction_ring R) (λ hn, absurd (eq_zero_of _ hn) h0)) : fraction_ring R) *
          ((units.mk0 (of (w.2 : non_zero_divisors R) : fraction_ring R)
          (λ hn, absurd (eq_zero_of _ hn) (mem_non_zero_divisors_iff_ne_zero.1
            (w.2 : non_zero_divisors R).2)))⁻¹ : fraction_ring R) = _,
    simp [(mk_eq_div R).symm, mk_eq, units.inv_eq_inv, to_units_coe],
  ext x y,
  split,
    intro h,
    use 1,
    simp [subtype.ext.2 (of.injective ((units.units.mk0_inj _ _).1 ((con.ker_rel _).1 h)))],
  rintro ⟨t, ht⟩,
  rw con.ker_rel,
  show units.mk0 (of (x : R)) _ = units.mk0 (of (y : R)) _,
  congr' 1,
  rw [←units.mul_left_inj
      ((units.mk0 (localization.of ((t : non_zero_divisors R) : R) : fraction_ring R))
      (λ h, absurd (eq_zero_of _ h) (mem_non_zero_divisors_iff_ne_zero.1 t.1.2))), units.mk0_val,
      ←of_mul, ←of_mul, ←submonoid.coe_mul, ←submonoid.coe_mul],
  congr' 2, simpa using ht}

end completion
