import algebraic_geometry.prime_spectrum
import topology.sheaves.sheaf
import algebra.category.CommRing
import ring_theory.localization

open category_theory
open category_theory.limits
open Top

noncomputable theory

section move_this

def dvd_preorder (R : Type*) := R

namespace dvd_preorder

variables (R : Type*) [comm_semiring R]

instance : preorder (dvd_preorder R) :=
{ le := @has_dvd.dvd R _,
  le_refl := dvd_refl,
  le_trans := λ x y z, dvd_trans }

end dvd_preorder

namespace localization_map
variables {R : Type*} [comm_ring R] {M : submonoid R} {S : Type*} [comm_ring S]
variables {A : Type*} [comm_semiring A]

@[ext, priority 1024]
lemma ext' (l : localization_map M S) (f g : S →+* A) (h : ∀ r : R, f (l.to_map r) = g (l.to_map r)) : f = g :=
begin
  ext s,
  obtain ⟨⟨r, m⟩, hrm⟩ := l.surj s,
  obtain ⟨lm, hlm⟩ := l.map_units m,
  calc f s = f (s * l.to_map m * ↑lm⁻¹) : by simp only [←hlm, units.mul_inv_cancel_right]
  ... = g (s * l.to_map m * ↑lm⁻¹) : _
  ... = g s :  by simp only [←hlm, units.mul_inv_cancel_right],
  simp only [hrm, ring_hom.map_mul, h],
  congr' 1,
  calc f ↑lm⁻¹ = units.map f.to_monoid_hom (lm⁻¹) : rfl
           ... = units.map g.to_monoid_hom (lm⁻¹) : _
           ... = g ↑lm⁻¹ : rfl,
  simp only [monoid_hom.map_inv],
  congr' 2,
  ext,
  show f lm = g lm,
  rw [hlm, h],
end

end localization_map

end move_this

namespace algebraic_geometry

namespace prime_spectrum

variables (R : Type*) [comm_ring R]

noncomputable def localization_functor :
  (dvd_preorder R) ⥤ CommRing :=
{ obj := λ f, CommRing.of $ localization (submonoid.of $ @powers R _ f),
  map := λ f g hfg, @localization_map.lift _ _ _ _ _ _ _
          (localization.of (submonoid.of $ @powers R _ f))
          (localization.of (submonoid.of $ @powers R _ g)).to_ring_hom
          begin
            rintros ⟨r, n, rfl⟩,
            refine is_unit_of_dvd_unit (ring_hom.map_dvd _ $ pow_dvd_pow_of_dvd hfg.down.down n) _,
            apply localization_map.map_units _ ⟨_, _⟩,
            exact ⟨n, rfl⟩,
          end,
  map_id' :=
  begin
    intros f, -- we need an ext lemma
    apply localization_map.ext' (localization.of (submonoid.of $ @powers R _ f)),
    intros r,
    simp only [coe_id, localization_map.lift_id],
  end,
  map_comp' :=
  begin
    intros f _ _ h₁ h₂,
    apply localization_map.ext' (localization.of (submonoid.of $ @powers R _ f)),
    intro r,
    simp only [localization_map.lift_eq, coe_comp],
  end }

-- def structure_presheaf_obj_diagram (U : (topological_space.opens ↥(of (prime_spectrum R)))ᵒᵖ) :
--   (dvd_preorder R)ᵒᵖ ⥤ CommRing :=
-- { obj := λ f, CommRing.of $ localization (submonoid.of $ @powers R _ f.unop),
         -- meh, need to restrict to those `f` for which `D(f) ⊆ U`
--   map := λ f g hfg, @localization_map.lift _ _ _ _ _ _ _
--          (localization.of (submonoid.of $ @powers R _ f.unop))
--          (localization.of (submonoid.of $ @powers R _ g.unop)).to_ring_hom
--          begin
--           rintros ⟨r, n, rfl⟩,
--          end,
--   map_id' := _,
--   map_comp' := _ }

def invertibility_locus (f : R) : set (prime_spectrum R) :=
(prime_spectrum.zero_locus {f})ᶜ

def structure_presheaf_obj (U : (topological_space.opens ↥(of (prime_spectrum R)))ᵒᵖ) :
  CommRing :=
limit (full_subcategory_inclusion
  {f : dvd_preorder R | ∀ P ∈ invertibility_locus R f, P ∈ U.unop}
  ⋙ localization_functor R)

def structure_presheaf : presheaf CommRing (Top.of (prime_spectrum R)) :=
{ obj := λ U, structure_presheaf_obj _ U,
  map := λ U V i,
  begin
    let c : cone
    (full_subcategory_inclusion
      {f : dvd_preorder R | ∀ P ∈ invertibility_locus R f, P ∈ V.unop}
      ⋙ localization_functor R) :=
    { X := structure_presheaf_obj _ U,
      π := _ },
    refine limit.lift _ c,
    refine { app := λ f, limit.π _ ⟨f, (λ (P : ↥(of (prime_spectrum R))) (hP : P ∈ invertibility_locus R ↑f), i.unop.down.down (f.property P hP))⟩ ≫ 𝟙 _, naturality' := _ },
    intros f g hfg,
    -- dsimp, simp,
    sorry
  end,
  map_id' :=
  begin
    intros U,
    ext1,
    dsimp,
  end,
  map_comp' := _ }

end prime_spectrum

end algebraic_geometry
