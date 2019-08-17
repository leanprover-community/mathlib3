import group_theory.quotient_monoid

variables {α : Type*} [monoid α] (X : Type*) [comm_monoid X]
          {Y : Type*} [comm_monoid Y] {Z : Type*} [comm_monoid Z]

local notation `top` := (⊤ : submonoid X)

@[reducible] def completion := (submonoid.r (⊤ : submonoid X)).quotient

namespace completion

instance top_coe : has_coe X top := ⟨λ x, ⟨x, set.mem_univ x⟩⟩
instance : has_coe (X × top) (completion X) := infer_instance

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

lemma mul_left_inv (x : completion X) : x⁻¹ * x = 1 :=
begin
  apply con.induction_on' x,
  rintro ⟨y1, y2⟩,
  rw [←inv_apply, ←localization.mk_apply, ←localization.mk_apply,
      localization.mk_mul_mk, mul_comm],
  apply coe_self,
end

instance : comm_group (completion X) :=
{  mul := (*),
   one := 1,
   one_mul := one_mul,
   mul_one := mul_one,
   mul_assoc := mul_assoc,
   inv := has_inv.inv,
   mul_left_inv := mul_left_inv,
   mul_comm := mul_comm}


lemma comm_group.coe_inj {G : Type*} [comm_group G] {x y : G}
(H : (x : completion G) = (y : completion G)) : x = y :=
by {cases con.eq.1 H with w hw, simp * at *}

lemma comm_group.coe_surj {G : Type*} [comm_group G] {y : completion G} :
  ∃ x : G, (x : completion G) = y :=
begin
  apply con.induction_on' y,
  intro z,
  use z.1*(↑z.2)⁻¹,
  simp,
  use 1,
end

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
#exit
section
open localization localization.fraction_ring classical
variables (R : Type u) [integral_domain R] [decidable_eq R]

def non_zero_divisors' : submonoid R :=
⟨non_zero_divisors R, λ z hz, by rwa monoid.mul_one at hz,
 λ x₁ x₂ hx₁ hx₂ z hz,
 have z * x₁ * x₂ = 0, by rwa monoid.mul_assoc,
 hx₁ z $ hx₂ (z * x₁) this⟩

lemma ne_zero_of_non_zero_divisors' {x : non_zero_divisors' R} : (x : R) ≠ 0 :=
λ hm, absurd (x.2 1 (by rw [hm.symm, monoid.one_mul]; finish)).symm zero_ne_one

local notation `fracR` := fractions (⊤ : submonoid (non_zero_divisors' R))
variables {R}
lemma of_inv_eq {x : non_zero_divisors' R} : (of (x : R) :  fraction_ring R)⁻¹ = mk 1 x :=
by tidy

lemma ne_zero_of {x : non_zero_divisors' R} : (of x : fraction_ring R) ≠ 0 :=
λ h, absurd (of.injective (by rwa ←of_zero at h)) (ne_zero_of_non_zero_divisors' R)

variables (R)

@[reducible] def fraction_ring_map : non_zero_divisors' R →* units (fraction_ring R) :=
⟨λ r, to_units r, by tidy, λ x y, by tidy⟩

variables {R}

lemma map_eq : ⇑(fraction_ring_map R) = λ r, to_units r := rfl

lemma fraction_ring_mk_apply
  (x : R × non_zero_divisors R) : localization.mk x.1 x.2 = ⟦x⟧ :=
by tidy

@[reducible] def aux_nonzero (a : R × non_zero_divisors' R) (Ha : a.1 ∈ non_zero_divisors' R) :
  non_zero_divisors' R × (⊤ : submonoid (non_zero_divisors' R)) :=
prod.mk (⟨a.1, Ha⟩ : non_zero_divisors' R) (⟨a.2, mem_top a.2⟩ : (⊤ : submonoid (non_zero_divisors' R)))

lemma ne_zero_aux (a : R × non_zero_divisors R) (Ha : a.1 ≠ 0) : (localization.mk a.1 a.2) ≠ 0 :=
λ h, absurd
(by rw [mk_eq, units.inv_eq_inv, to_units_coe, mul_eq_zero, inv_eq_zero, ←coe_zero] at h;
    exact or.elim h (λ hl, of.injective (show of a.1 = of 0, from hl))
      (λ hr, absurd (of.injective (show localization.of ↑a.2 = _, from hr))
                    (ne_zero_of_non_zero_divisors' R))) Ha

lemma surjective_aux (a : R × non_zero_divisors R) (Ha : a.1 ≠ 0) :
  units.mk0 (localization.mk a.1 a.2) (ne_zero_aux a Ha) =
  (to_units (aux_nonzero a (mem_non_zero_divisors_iff_ne_zero.2 Ha)).1)*(to_units a.2)⁻¹ :=
by tidy

lemma eq_aux (x : fracR) :
aux (⊤ : submonoid (non_zero_divisors' R)) (fraction_ring_map R) (λ x, ⟨(fraction_ring_map R x)⁻¹, mul_left_inv _⟩) x =
(fraction_ring_map R x.2)⁻¹ * (fraction_ring_map R x.1) :=
begin
sorry,
end

#exit
-/

end completion

/-
lemma surjective_fraction_hom : ∀ x≠(0 : fraction_ring R), ∃ y : fracR, units.mk0 x H =
  fractions_hom ⊤ (fraction_ring_map R) (λ x, ⟨(fraction_ring_map R x)⁻¹, mul_left_inv _⟩) y :=
begin
intro x,
apply quotient.induction_on x,
intros,
have ha0 : a.1 ≠ 0, from λ h, absurd (eq.refl 0)
  (by rw [←fraction_ring_mk_apply, mk_eq, h, coe_zero, zero_mul, ne.def] at H; finish),
use fractions.mk (⊤ : submonoid (non_zero_divisors' R)) (aux_nonzero a (mem_coe.2 (mem_non_zero_divisors_iff_ne_zero.2 ha0))),
conv {to_lhs, congr, rw ←fraction_ring_mk_apply a},-- skip, whnf, rw aux_nonzero, simp only [map_eq]},
rw surjective_aux a ha0, rw coe_apply,
simp [map_eq], rw aux_nonzero,
conv {to_rhs, congr, whnf, congr, rw eq_of_left_inv (fraction_ring_map R (x.2 : _ )) (classical.some_spec _ _) (mul_left_inv _), simp, },
rw aux_nonzero,simp,
--suffices Hu : units.mk0 ⟦a⟧ H = (fraction_ring_map (aux_nonzero a this).1) * (fraction_ring_map (aux_nonzero a this).2)⁻¹, by
 --{simp * at *},
end

lemma universal_pred_of_fraction_ring :
  universal_pred ⊤ (fraction_ring_map R) (λ x, ⟨(fraction_ring_map R x)⁻¹, mul_left_inv _⟩) :=
sorry

def fractions_group_equiv : (units (fraction_ring R)) ≃* fractions (non_zero_divisors' R) :=
sorry

end


-/-/
