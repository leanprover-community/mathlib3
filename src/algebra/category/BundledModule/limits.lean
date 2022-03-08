import algebra.category.BundledModule.basic
import algebra.category.CommRing.limits
import algebra.category.Group.limits
import category_theory.category.basic

noncomputable theory

open category_theory

namespace BundledModule

universes u
variables {ι : Type u} [small_category ι] (𝓕 : ι ⥤ BundledModule.{u})

local notation `𝓞` := 𝓕 ⋙ forget_to_Ring
local notation `𝓜` := 𝓕 ⋙ forget_to_Ab
local notation `isoAb` := limits.limit.iso_limit_cone ⟨_, AddCommGroup.limit_cone_is_limit 𝓜⟩
local notation `isoRing` := limits.limit.iso_limit_cone ⟨_, Ring.limit_cone_is_limit 𝓞⟩

instance : ∀ (i : ι), module (𝓞 .obj i) (𝓜 .obj i) := λ i,
begin
  have eq1 : 𝓞 .obj i = (𝓕.obj i).1 := rfl,
  have eq2 : 𝓜 .obj i = ⟨(𝓕.obj i).2⟩ := rfl,
  rw [eq1, eq2],
  apply_instance,
end

instance : ∀ (i : ι), has_scalar ((𝓞 ⋙ forget Ring).obj i) ((𝓜 ⋙ forget Ab).obj i) := λ i,
begin
  have eq1 : (𝓞 ⋙ forget Ring).obj i = (𝓕.obj i).1 := rfl,
  have eq2 : (𝓜 ⋙ forget Ab).obj i = (𝓕.obj i).2 := rfl,
  rw [eq1, eq2],
  apply_instance,
end

def r_bu.functor (r : limits.limit 𝓞) : 𝓜 ⟶ 𝓜 :=
{ app := λ i, { to_fun := λ m, limits.limit.π 𝓞 i r • m,
    map_zero' := by simp,
    map_add' := by simp },
  naturality' := λ i j fij, begin
    ext m,
    simp only [comp_apply, functor.comp_map, add_monoid_hom.coe_mk],
    change _ • (𝓕.map fij).2 _ = (𝓕.map fij).2 _,
    rw [linear_map.map_smul],
    congr,
    conv_rhs { rw [show r = isoRing .inv (isoRing .hom r), by simp] },
    change _ = (𝓕.map fij).fst ((isoRing .inv ≫ _) _),
    rw [limits.limit.iso_limit_cone_inv_π],
    have eq1 : (𝓕.map fij).fst ((isoRing .hom r).1 i) = ((isoRing .hom r).1 j) := (isoRing .hom r).2 fij,
    convert eq1,
    rw eq1,
    conv_lhs { rw [show r = isoRing .inv (isoRing .hom r), by simp] },
    change (isoRing .inv ≫ _) _ = _,
    rw [limits.limit.iso_limit_cone_inv_π],
    refl,
  end }

/--`r•` map-/
def r_bu (r : limits.limit 𝓞) : (limits.limit 𝓜 : Ab) ⟶ (limits.limit 𝓜 : Ab) :=
limits.lim_map $ r_bu.functor 𝓕 r

-- lemma r_bu_section (r : limits.limit 𝓞) (m : (AddCommGroup.limit_cone 𝓜).X) :
--   r_bu 𝓕 r (isoAb .inv m) = limits.limit.lift 𝓜 (AddCommGroup.limit_cone 𝓜)
--     ⟨λ i, limits.limit.π 𝓞 i r • (m.1 i : 𝓜 .obj i), _⟩ := sorry
lemma r_bu_π (r : limits.limit 𝓞) (m : limits.limit 𝓜) (i : ι) :
  limits.limit.π 𝓜 i (r_bu 𝓕 r m) = limits.limit.π 𝓞 i r • limits.limit.π 𝓜 i m :=
begin
  change (limits.lim_map (@r_bu.functor ι _ 𝓕 r) ≫ _) _ = _,
  simp only [r_bu.functor, limits.lim_map_π, comp_apply, add_monoid_hom.coe_mk],
end

lemma r_bu_one : r_bu 𝓕 1 = 𝟙 _ :=
begin
  ext,
  simp only [r_bu, r_bu.functor, limits.lim_map_π, comp_apply, add_monoid_hom.coe_mk, one_smul,
    map_one, category.id_comp],
end

lemma r_bu_zero : r_bu 𝓕 0 = 0 :=
begin
  ext,
  simp only [comp_apply, limits.zero_comp, AddCommGroup.zero_apply, r_bu],
  change (limits.lim_map (@r_bu.functor ι _ 𝓕 0) ≫ _) _ = 0,
  simp only [r_bu.functor, limits.lim_map_π, comp_apply, add_monoid_hom.coe_mk, zero_smul, map_zero],
end

lemma r_bu_mul (r1 r2 : limits.limit 𝓞) :
  r_bu 𝓕 (r1 * r2) = r_bu 𝓕 r2 ≫ r_bu 𝓕 r1 :=
begin
  ext,
  simp only [r_bu, r_bu.functor, limits.lim_map_π, comp_apply, add_monoid_hom.coe_mk,
    limits.lim_map_π_assoc, map_mul, category.assoc],
  convert mul_smul _ _ _,
end

lemma r_bu_add (r1 r2 : limits.limit 𝓞) :
  r_bu 𝓕 (r1 + r2) = r_bu 𝓕 r1 + r_bu 𝓕 r2 :=
begin
  ext,
  simp only [comp_apply, preadditive.add_comp, add_monoid_hom.add_apply, r_bu],
  change (limits.lim_map (@r_bu.functor ι _ 𝓕 (r1 + r2)) ≫ _) _ =
    (limits.lim_map (@r_bu.functor ι _ 𝓕 r1) ≫ _) _ +
    (limits.lim_map (@r_bu.functor ι _ 𝓕 r2) ≫ _) _,
  simp only [limits.lim_map_π, comp_apply, r_bu.functor, map_add],
  convert add_smul _ _ _,
end

instance has_scalar : has_scalar (limits.limit 𝓞 : Ring) (limits.limit 𝓜 : Ab) :=
{ smul := λ r, r_bu 𝓕 r }

-- instance has_scalar : has_scalar (limits.limit 𝓞 : Ring) (limits.limit 𝓜 : Ab) :=
-- { smul := λ r m, begin
--   refine isoAb .inv ⟨λ i, (isoRing .hom r).1 i • (isoAb .hom m).1 i, λ i j fij, _⟩,

--   { simp only [forget_map_eq_coe, functor.comp_map, subtype.val_eq_coe],
--     change (𝓕.map fij).2 _ = _,
--     rw [linear_map.map_smul, restriction_of_scalar.smul_def'],
--     have eq1 := (isoRing .hom r).2 fij,
--     have eq2 := (isoAb .hom m).2 fij,
--     simp only [forget_map_eq_coe, functor.comp_map, subtype.val_eq_coe] at eq1 eq2,
--     rw [←eq1, ←eq2],
--     refl, },
-- end }

lemma limit_ext_iff (x y : limits.limit 𝓜) : x = y ↔ isoAb .hom x = isoAb .hom y :=
⟨λ eq1, by rw eq1, λ eq1, begin
  have eq2 := congr_arg (isoAb .inv) eq1,
  convert eq2;
  simp,
end⟩

instance mul_action : mul_action (limits.limit 𝓞 : Ring) (limits.limit 𝓜 : Ab) :=
{ one_smul := λ x, begin
    unfold has_scalar.smul,
    rw r_bu_one,
    simp only [id_apply],
  end,
  mul_smul := λ r1 r2 m, begin
    -- rw limit_ext_iff,
    unfold has_scalar.smul,
    rw r_bu_mul,
    refl,
  end,
  ..(BundledModule.has_scalar 𝓕) }

instance distrib_mul_action : distrib_mul_action (limits.limit 𝓞 : Ring) (limits.limit 𝓜 : Ab) :=
{ smul_zero := λ r, begin
    unfold has_scalar.smul,
    simp only [map_zero],
  end,
  smul_add := λ r m1 m2, begin
    unfold has_scalar.smul,
    simp only [map_add],
  end,
  ..(BundledModule.mul_action 𝓕) }

instance module : module (limits.limit 𝓞 : Ring) (limits.limit 𝓜 : Ab) :=
{ add_smul := λ r1 r2 m, begin
    -- rw limit_ext_iff,
    unfold has_scalar.smul,
    rw r_bu_add,
    simp only [add_monoid_hom.add_apply],
  end,
  zero_smul := λ m, begin
    unfold has_scalar.smul,
    rw r_bu_zero,
    simp only [AddCommGroup.zero_apply],
  end,
  ..(BundledModule.distrib_mul_action 𝓕) }

def mk' (R : Ring) (A : Ab) [module R A] : BundledModule :=
{ R := R, M := ⟨A⟩ }

@[simp] lemma mk'_R (R : Ring) (A : Ab) [module R A] : (mk' R A).R = R := rfl
@[simp] lemma mk'_M (R : Ring) (A : Ab) [module R A] : (mk' R A).M.1 = A := rfl

lemma 𝓕_map_fst {i j : ι} (fij : i ⟶ j) : (𝓕.map fij).1 = 𝓞 .map fij := rfl

lemma aux1 {𝓢 : ι ⥤ BundledModule} {i j : ι} (fij : i ⟶ j) :
  𝓢.map fij = ⟨(𝓢 ⋙ forget_to_Ring).map fij,
    { to_fun := (𝓢 ⋙ forget_to_Ab).map fij,
      map_add' := by simp,
      map_smul' := λ r m, begin
        simp only [restriction_of_scalar.smul_def', functor.comp_map, ring_hom.id_apply],
        convert linear_map.map_smul _ _ _,
      end }⟩ :=
begin
  rw bundledMap.ext,
  split,
  { refl, },
  { intros m, refl, }
end

local notation `L` := mk' (limits.limit 𝓞) (limits.limit 𝓜)

def limits.cone.π : (category_theory.functor.const ι).obj L ⟶ 𝓕 :=
{ app := λ i, ⟨limits.limit.π 𝓞 i,
    { to_fun := λ m, limits.limit.π 𝓜 i m,
      map_add' := by simp,
      map_smul' := λ r m, begin
        simp only [restriction_of_scalar.smul_def', ring_hom.id_apply],
        change limits.limit.π 𝓜 i (r_bu 𝓕 r m) = _,
        rw [r_bu_π],
        refl,
      end } ⟩,
  naturality' := λ i j fij, begin
    rw bundledMap.ext,
    split,
    { ext r,
      simp only [functor.const.obj_map],
      change limits.limit.π 𝓞 j r = (limits.limit.π 𝓞 i ≫ 𝓞 .map fij) r,
      rw [comp_apply, show limits.limit.π 𝓞 i r =
        (isoRing .inv ≫ limits.limit.π 𝓞 i) (isoRing .hom r), by { rw [comp_apply], simp },
        limits.limit.iso_limit_cone_inv_π],
      have eq1 := (isoRing .hom r).2 fij,
      convert eq1.symm,
      conv_lhs { rw [show limits.limit.π 𝓞 j r = (isoRing .inv ≫ limits.limit.π 𝓞 j) (isoRing .hom r),
        by { rw [comp_apply], simp }, limits.limit.iso_limit_cone_inv_π] },
      refl, },
    { intro m,
      simp only [bundledMap.comp_snd],
      change limits.limit.π 𝓜 j _ = (𝓕.map fij).2 (limits.limit.π 𝓜 i m),
      rw [functor.const.obj_map L fij, show (𝟙 L : L ⟶ L).snd m = m, from rfl],
      have eq1 := (isoAb .hom m).2 fij,
      convert eq1.symm,
      { conv_lhs { rw [show limits.limit.π 𝓜 j m = (isoAb .inv ≫ limits.limit.π 𝓜 j) (isoAb .hom m),
          by { rw [comp_apply], simp }, limits.limit.iso_limit_cone_inv_π] },
        refl, },
      { conv_lhs { rw [show limits.limit.π 𝓜 i m = (isoAb .inv ≫ limits.limit.π 𝓜 i) (isoAb .hom m),
          by { rw [comp_apply], simp }, limits.limit.iso_limit_cone_inv_π] },
        refl, }, }
  end }

/-- The limit of `𝓕` is `limit 𝓜` as `limit 𝓞` where `𝓞` is the underlying rings of `𝓕` and
`𝓜` is underlying Ab -/
def limits.cone : limits.cone 𝓕 :=
{ X := L,
  π := limits.cone.π 𝓕 }

variable {𝓕}
def limits.cone_Ring (c : category_theory.limits.cone 𝓕) : category_theory.limits.cone 𝓞 :=
{ X := c.X.R,
  π := { app := λ i, (c.π.app i).1,
    naturality' := λ i j fij, begin
      ext,
      simp only [comp_apply, functor.comp_map, functor.const.obj_map, id_apply],
      change _ = (𝓕.map fij).1 ((c.π.app i).fst x),
      have eq1 : (c.π.app i ≫ 𝓕.map fij).1 = _ := congr_arg (λ (f : bundledMap _ _), f.1) (c.π.naturality fij).symm,
      rw [bundledMap.comp_fst, bundledMap.comp_fst] at eq1,
      convert (ring_hom.congr_fun eq1 x).symm,
      ext y,
      rw [comp_apply, functor.const.obj_map],
      refl,
    end } }

def limits.cone_Ab (c : category_theory.limits.cone 𝓕) : category_theory.limits.cone 𝓜 :=
{ X := ⟨c.X.M⟩,
  π := { app := λ i, { to_fun := (c.π.app i).2,
      map_zero' := by simp,
      map_add' := by simp },
    naturality' := λ i j fij, begin
      ext,
      simp only [comp_apply, functor.comp_map, add_monoid_hom.coe_mk,
        functor.const.obj_map, id_apply],
      change _ = (𝓕.map fij).2 ((c.π.app i).2 x),
      have eq1 := (c.π.naturality fij),
      rw [functor.const.obj_map c.X fij, (category.id_comp (c.π.app j) : 𝟙 c.X ≫ _ = _)] at eq1,
      rw [eq1, bundledMap.comp_snd],
      refl,
    end } }

instance (c : category_theory.limits.cone 𝓕) :
  module (limits.cone_Ring c).X (limits.cone_Ab c).X :=
begin
  have eq1 : (limits.cone_Ring c).X = c.X.R := rfl,
  have eq2 : (limits.cone_Ab c).X = ⟨c.X.M⟩ := rfl,
  rw [eq1, eq2],
  apply_instance,
end

def limits.cone_is_limit : limits.is_limit (limits.cone 𝓕) :=
{ lift := λ c, ⟨limits.limit.lift 𝓞 (limits.cone_Ring c),
    { to_fun := limits.limit.lift 𝓜 (limits.cone_Ab c),
      map_add' := by simp,
      map_smul' := λ r m, begin
        simp only [ring_hom.id_apply],
        rw [limit_ext_iff],
        sorry
      end, }
      ⟩,
  fac' := λ c i, begin
    rw bundledMap.ext,
    split,
    { ext r,
      rw [bundledMap.comp_fst, show ((limits.cone 𝓕).π.app i).fst = limits.limit.π 𝓞 i, from rfl,
        limits.limit.lift_π],
      refl, },
    { intro m,
      rw [bundledMap.comp_snd],
      simp only [linear_map.coe_mk],
      sorry, },
  end,
  uniq' := λ c ⟨f, g⟩ eq1, begin
    rw bundledMap.ext,
    split,
    { ext,
      simp only [limits.limit.lift_π, comp_apply],
      change _ = (c.π.app j).1 _,
      specialize eq1 j,
      rw ring_hom.congr_fun (congr_arg (λ f : bundledMap _ _, f.1) eq1.symm) x,
      refl, },
    { intro m,
      simp only [linear_map.coe_mk],
      sorry },
  end }

instance : limits.has_limit 𝓕 :=
{ exists_limit := ⟨{ cone := limits.cone 𝓕,
    is_limit := limits.cone_is_limit }⟩ }

end BundledModule
