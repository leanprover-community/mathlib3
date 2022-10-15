import algebra.category.RingModPair.basic
import algebra.category.Ring.limits
import algebra.category.Group.limits

noncomputable theory

namespace RingModPair
open category_theory category_theory.limits

universe v

section limits

variables {J : Type v} [small_category J] (F : J ⥤ RingModPair.{v v})

lemma comp_forget_to_Ab_map_smul (j j' : J) (m : j ⟶ j')
  (r : (F ⋙ RingModPair.forget_to_Ring).obj j)
  (x : (F ⋙ RingModPair.forget_to_Ab).obj j) :
((F ⋙ RingModPair.forget_to_Ab).map m) ((F.obj j).mod.3.smul r x) =
(F.obj j').mod.3.smul ((F.map m).1 r) (((F.map m).2 x)) :=
begin
  have := ((F.map m).2.map_smul r x).symm,
  erw this,
  refl,
end

@[reducible] def Ab.sections_equiv_limit :
  (AddCommGroup.limit_cone.{v v} (F ⋙ RingModPair.forget_to_Ab)).X ≅
  (limit.cone (F ⋙ RingModPair.forget_to_Ab)).X :=
(is_limit.cone_point_unique_up_to_iso (AddCommGroup.limit_cone_is_limit.{v v}
  ((F ⋙ RingModPair.forget_to_Ab))) (limit.is_limit _))

@[reducible] def Ring.sections_equiv_limit :
  (Ring.limit_cone.{v v} (F ⋙ RingModPair.forget_to_Ring)).X ≅
  (limit.cone (F ⋙ RingModPair.forget_to_Ring)).X :=
(is_limit.cone_point_unique_up_to_iso (Ring.limit_cone_is_limit.{v v}
  ((F ⋙ RingModPair.forget_to_Ring))) (limit.is_limit _))

def sections_smul_sections (r : (Ring.limit_cone.{v v} (F ⋙ RingModPair.forget_to_Ring)).X)
  (x : (AddCommGroup.limit_cone.{v v} (F ⋙ RingModPair.forget_to_Ab)).X) :
  (AddCommGroup.limit_cone.{v v} (F ⋙ RingModPair.forget_to_Ab)).X :=
⟨λ j, (F.obj j).mod.is_module.smul (r.1 j) (x.1 j),
  λ j j' h, begin
    dsimp only,
    rw [←r.2 h, ←x.2 h],
    convert (F.map h).2.map_smul (r.1 j) (x.1 j),
  end⟩

lemma one_smul_sections (x) : sections_smul_sections F 1 x = x :=
begin
  rw [subtype.ext_iff_val, sections_smul_sections],
  ext1 j,
  convert one_smul _ _,
end

lemma mul_smul_sections (r r') (x) :
  sections_smul_sections F (r * r') x =
  sections_smul_sections F r (sections_smul_sections F r' x) :=
begin
  rw [subtype.ext_iff_val, sections_smul_sections],
  ext1 j,
  convert mul_smul _ _ _,
end

lemma sections_smul_zero (r) : sections_smul_sections F r 0 = 0 :=
begin
  rw [subtype.ext_iff_val, sections_smul_sections],
  ext1 j,
  dsimp only,
  erw smul_zero,
  refl,
end

lemma sections_smul_add (r) (x x') :
  sections_smul_sections F r (x + x') =
  sections_smul_sections F r x + sections_smul_sections F r x' :=
begin
  rw [subtype.ext_iff_val, sections_smul_sections],
  ext1 j,
  dsimp only,
  erw [smul_add],
  refl,
end

lemma zero_smul_add (x) : sections_smul_sections F 0 x = 0 :=
begin
  rw [subtype.ext_iff_val, sections_smul_sections],
  ext1 j,
  dsimp only,
  erw [zero_smul],
  refl,
end

lemma add_smul_sections (r r') (x) :
  sections_smul_sections F (r + r') x =
  sections_smul_sections F r x + sections_smul_sections F r' x :=
begin
  rw [subtype.ext_iff_val, sections_smul_sections],
  ext1 j,
  dsimp only,
  erw [add_smul],
  refl,
end


instance has_smul :
  has_smul (@@limit _ _ (F ⋙ RingModPair.forget_to_Ring) _)
    (@@limit _ _ (F ⋙ RingModPair.forget_to_Ab) _) :=
{ smul := λ r x, (Ab.sections_equiv_limit F).hom $ sections_smul_sections F
    ((Ring.sections_equiv_limit F).inv r)
    ((Ab.sections_equiv_limit F).inv x) }

lemma limit_smul_def (r : limit (F ⋙ RingModPair.forget_to_Ring))
  (x : limit (F ⋙ RingModPair.forget_to_Ab)) :
  r • x =
  (Ab.sections_equiv_limit F).hom
    (sections_smul_sections F
      ((Ring.sections_equiv_limit F).inv r)
      ((Ab.sections_equiv_limit F).inv x)) := rfl

instance mul_action :
  mul_action (@@limit _ _ (F ⋙ RingModPair.forget_to_Ring) _)
  (@@limit _ _ (F ⋙ RingModPair.forget_to_Ab) _) :=
{ one_smul := λ x,
  begin
    rw [limit_smul_def, map_one, one_smul_sections],
    simp only [iso.inv_hom_id_apply],
  end,
  mul_smul := λ r x y,
  begin
    rw [limit_smul_def, limit_smul_def, limit_smul_def, map_mul, mul_smul_sections],
    congr' 2,
    simp only [iso.hom_inv_id_apply],
  end,
  ..RingModPair.has_smul F}

instance distrib_mul_action : distrib_mul_action (@@limit _ _ (F ⋙ RingModPair.forget_to_Ring) _)
  (@@limit _ _ (F ⋙ RingModPair.forget_to_Ab) _) :=
{ smul_zero := λ r,
  begin
    rw [limit_smul_def, map_zero, sections_smul_zero, map_zero],
  end,
  smul_add := λ r x y,
  begin
    rw [limit_smul_def, limit_smul_def, limit_smul_def, map_add, sections_smul_add, map_add],
  end,
  ..RingModPair.mul_action F }

instance module : module (@@limit _ _ (F ⋙ RingModPair.forget_to_Ring) _)
  (@@limit _ _ (F ⋙ RingModPair.forget_to_Ab) _) :=
{ zero_smul := λ x,
  begin
    rw [limit_smul_def, map_zero, zero_smul_add, map_zero],
  end,
  add_smul := λ r r' x,
  begin
    rw [limit_smul_def, limit_smul_def, limit_smul_def, map_add, add_smul_sections, map_add],
  end,
  ..RingModPair.distrib_mul_action F}

lemma Ab.limit_π_apply (j : J) (x) :
  limit.π (F ⋙ RingModPair.forget_to_Ab) j ((Ab.sections_equiv_limit F).hom x) =
  x.1 j :=
begin
  rw [Ab.sections_equiv_limit],
  change ((is_limit.cone_point_unique_up_to_iso (AddCommGroup.limit_cone_is_limit.{v v}
    ((F ⋙ RingModPair.forget_to_Ab))) (limit.is_limit _)).hom ≫ _) _ = _,
  rw limit.cone_point_unique_up_to_iso_hom_comp,
  refl,
end

lemma Ring.limit_π_apply (j : J) (x) :
  limit.π (F ⋙ RingModPair.forget_to_Ring) j ((Ring.sections_equiv_limit F).hom x) =
  x.1 j :=
begin
  rw [Ring.sections_equiv_limit],
  change ((is_limit.cone_point_unique_up_to_iso (Ring.limit_cone_is_limit.{v v}
    ((F ⋙ RingModPair.forget_to_Ring))) (limit.is_limit _)).hom ≫ _) _ = _,
  rw limit.cone_point_unique_up_to_iso_hom_comp,
  refl,
end

lemma Ab.limit_π_apply' (j : J) (x) :
  limit.π (F ⋙ RingModPair.forget_to_Ab) j x =
  ((Ab.sections_equiv_limit F).inv x).1 j :=
begin
  have : x = (Ab.sections_equiv_limit F).hom ((Ab.sections_equiv_limit F).inv x),
  { simp only [iso.inv_hom_id_apply], },
  rw [this, Ab.limit_π_apply],
  simp only [iso.inv_hom_id_apply],
end

lemma Ring.limit_π_apply' (j : J) (x) :
  limit.π (F ⋙ RingModPair.forget_to_Ring) j x =
  ((Ring.sections_equiv_limit F).inv x).1 j :=
begin
  have : x = (Ring.sections_equiv_limit F).hom ((Ring.sections_equiv_limit F).inv x),
  { simp only [iso.inv_hom_id_apply], },
  rw [this, Ring.limit_π_apply],
  simp only [iso.inv_hom_id_apply],
end

def limit_cone.π_app_snd_to_fun (j : J) :
  limit (F ⋙ RingModPair.forget_to_Ab) → (F.obj j).mod :=
limit.π (F ⋙ RingModPair.forget_to_Ab) j

lemma limit_cone.π_app_snd_to_fun_add (j : J) (x y) :
  limit_cone.π_app_snd_to_fun F j (x + y) =
  limit_cone.π_app_snd_to_fun F j x + limit_cone.π_app_snd_to_fun F j y :=
map_add _ _ _

lemma limit_cone.π_app_snd_to_fun_smul (j : J) (r) (x) :
  limit_cone.π_app_snd_to_fun F j (r • x) =
  limit.π (F ⋙ RingModPair.forget_to_Ring) j r • limit_cone.π_app_snd_to_fun F j x :=
begin
    rw [limit_cone.π_app_snd_to_fun, limit_smul_def, Ab.sections_equiv_limit],
    change ((is_limit.cone_point_unique_up_to_iso (AddCommGroup.limit_cone_is_limit.{v v}
      ((F ⋙ RingModPair.forget_to_Ab))) (limit.is_limit _)).hom ≫ _) _ = _,
    rw limit.cone_point_unique_up_to_iso_hom_comp,
    rw [sections_smul_sections, Ring.limit_π_apply'],
    have eq1 : ∀ j, (F.obj j).mod.is_module.smul
      (((Ring.sections_equiv_limit F).inv r).val j) (((Ab.sections_equiv_limit F).inv x).val j) =
      ((Ab.sections_equiv_limit F).inv ((RingModPair.module F).smul r x)).val j,
    { intros j,
      rw [limit_smul_def],
      simp only [iso.hom_inv_id_apply],
      refl, },
    simp_rw [eq1],
    rw [Ab.limit_π_apply'],
    rw eq1,
    refl,
end

@[simps] def limit_cone : cone F :=
{ X := ⟨limit (F ⋙ RingModPair.forget_to_Ring), ⟨@@limit _ _ (F ⋙ RingModPair.forget_to_Ab) _⟩⟩,
  π :=
  { app := λ j, ⟨(limit.π _ _ : limit (F ⋙ RingModPair.forget_to_Ring) ⟶ (F.obj j).ring),
    { to_fun := limit_cone.π_app_snd_to_fun F j,
      map_add' := limit_cone.π_app_snd_to_fun_add F j,
      map_smul' := limit_cone.π_app_snd_to_fun_smul F j }⟩,
    naturality' := λ j j' f,
    begin
      dsimp,
      rw RingModPair.hom.ext,
      split,
      { rintros (x : @@limit _ _ (F ⋙ RingModPair.forget_to_Ring.{v v}) _),
        rw [category.id_comp],
        dsimp only,
        rw Ring.limit_π_apply',
        have := (((Ring.sections_equiv_limit F).inv) x).prop f,
        rw [←subtype.val_eq_coe] at this,
        rw [←this, ←Ring.limit_π_apply', category_theory.functor.comp_map],
        refl, },
      { rintros (x : @@limit _ _ (F ⋙ RingModPair.forget_to_Ab.{v v}) _),
        rw [category.id_comp],
        dsimp only,
        rw [linear_map.coe_mk, limit_cone.π_app_snd_to_fun],
        rw Ab.limit_π_apply',
        have := (((Ab.sections_equiv_limit F).inv) x).prop f,
        rw [←subtype.val_eq_coe] at this,
        rw [←this, ←Ab.limit_π_apply', category_theory.functor.comp_map],
        refl, }
    end } }

@[simps] def cone_to_Ring_cone (C : cone F) : cone (F ⋙ RingModPair.forget_to_Ring) :=
{ X := C.X.ring,
  π :=
  { app := λ j, (C.π.app j).1,
    naturality' := λ j j' h,
    begin
      dsimp,
      rw [category.id_comp],
      have eq1 := C.π.naturality h,
      dsimp at eq1,
      rw category.id_comp at eq1,
      rw eq1,
      ext1 x,
      refl,
    end } }

@[simps] def cone_to_Ab_cone (C : cone F) : cone (F ⋙ RingModPair.forget_to_Ab) :=
{ X := ⟨C.X.mod⟩,
  π :=
  { app := λ j, (C.π.app j).2.to_add_monoid_hom,
    naturality' := λ j j' h,
    begin
      dsimp,
      rw [category.id_comp],
      have eq1 := C.π.naturality h,
      dsimp at eq1,
      rw category.id_comp at eq1,
      rw eq1,
      ext1 x,
      refl,
    end } }

@[simps] def limit_cone.lift_Ring (C : cone F) :
  C.X.ring ⟶ limit (F ⋙ RingModPair.forget_to_Ring) :=
{ to_fun := λ r, (Ring.sections_equiv_limit F).hom ⟨λ j, (C.π.app j).1 r, λ j j' h,
  begin
    dsimp,
    have := C.π.naturality h,
    erw category.id_comp at this,
    rw this,
    refl,
  end⟩,
  map_one' := begin
    simp_rw [map_one],
    convert (Ring.sections_equiv_limit F).hom.map_one,
  end,
  map_mul' := λ r r', begin
    simp_rw [map_mul],
    convert (Ring.sections_equiv_limit F).hom.map_mul _ _,
    refl,
  end,
  map_zero' := begin
    simp_rw [map_zero],
    convert (Ring.sections_equiv_limit F).hom.map_zero,
  end,
  map_add' := λ r r', begin
    simp_rw [map_add],
    convert (Ring.sections_equiv_limit F).hom.map_add _ _,
    refl,
  end }

@[simp] def limit_cone.lift_mod (C : cone F) :
  C.X.mod ⟶ (Module.restrict_scalars (limit_cone.lift_Ring F C)).obj (limit_cone F).X.mod :=
{ to_fun := λ x, (Ab.sections_equiv_limit F).hom ⟨λ j, (C.π.app j).2 x, λ j j' h, begin
    dsimp,
    have := C.π.naturality h,
    erw category.id_comp at this,
    rw this,
    refl,
  end⟩,
  map_add' := λ x y, begin
    simp_rw [map_add],
    convert (Ab.sections_equiv_limit F).hom.map_add _ _,
    refl,
  end,
  map_smul' := λ r x, begin
    rw [ring_hom.id_apply],
    change _ = (limit_cone.lift_Ring F C) r • _,
    simp_rw [λ j, (C.π.app j).snd.map_smul],
    simp only [Module.restrict_scalars.smul_def, limit_cone.lift_Ring_apply],
    rw [limit_smul_def],
    congr' 1,
    rw subtype.ext_iff_val,
    ext1 j,
    simp only [iso.hom_inv_id_apply],
    refl,
  end }

lemma Ring.sections_equiv_limit_hom_π (x : (limit_cone F).X.ring) :
  (Ring.sections_equiv_limit F).hom
    ⟨λ j, limit.π (F ⋙ RingModPair.forget_to_Ring) j x,
    λ j j' h, fun_like.congr_fun
        (limit.w (F ⋙ RingModPair.forget_to_Ring) h) x⟩ = x :=
begin
  apply_fun (Ring.sections_equiv_limit F).inv,
  simp only [iso.hom_inv_id_apply],
  rw subtype.ext_iff_val,
  ext1 j,
  dsimp,
  exact Ring.limit_π_apply' F _ _,
  exact concrete_category.injective_of_mono_of_preserves_pullback (Ring.sections_equiv_limit F).inv,
end

lemma Ab.sections_equiv_limit_hom_π (x : (limit_cone F).X.mod) :
  (Ab.sections_equiv_limit F).hom
    ⟨λ j, limit.π (F ⋙ RingModPair.forget_to_Ab) j x,
    λ j j' h, fun_like.congr_fun
        (limit.w (F ⋙ RingModPair.forget_to_Ab) h) x⟩ = x :=
begin
  apply_fun (Ab.sections_equiv_limit F).inv,
  simp only [iso.hom_inv_id_apply],
  rw subtype.ext_iff_val,
  ext1 j,
  dsimp,
  exact Ab.limit_π_apply' F _ _,
  exact concrete_category.injective_of_mono_of_preserves_pullback (Ab.sections_equiv_limit F).inv,
end


def limit_cone_is_limit : is_limit (RingModPair.limit_cone F) :=
{ lift := λ C, ⟨limit_cone.lift_Ring F C, limit_cone.lift_mod F C⟩,
  fac' := λ C j, begin
    rw RingModPair.hom.ext,
    split,
    { intros r,
      rw [RingModPair.hom.comp_fst],
      simp only [limit_cone_π_app_fst, comp_apply, limit_cone.lift_Ring_apply],
      dunfold Ring.sections_equiv_limit,
      convert fun_like.congr_fun (limit.cone_point_unique_up_to_iso_hom_comp
        (Ring.limit_cone_is_limit.{v v} (F ⋙ RingModPair.forget_to_Ring)) j) _,
    },
    { intros x,
      simp only [limit_cone.lift_mod, RingModPair.hom.comp_snd_apply, linear_map.coe_mk,
        limit_cone_π_app_snd_apply],
      dunfold limit_cone.π_app_snd_to_fun Ab.sections_equiv_limit,
      convert fun_like.congr_fun (limit.cone_point_unique_up_to_iso_hom_comp
        (AddCommGroup.limit_cone_is_limit.{v v} (F ⋙ RingModPair.forget_to_Ab)) j) _ },
  end,
  uniq' := λ C m h, begin
    rw RingModPair.hom.ext,
    split,
    { intros x, dsimp,
      simp_rw [←h, RingModPair.hom.comp_fst, comp_apply, limit_cone_π_app_fst],
      erw [Ring.sections_equiv_limit_hom_π], },
    { intros x, dsimp,
      have h' : ∀ j, ((limit_cone F).π.app j).2 (m.2 x) = (C.π.app j).2 x,
      { intros j, specialize h j, rw ←h, refl, },
      simp_rw [←h', limit_cone_π_app_snd_apply],
      erw [Ab.sections_equiv_limit_hom_π], }
  end }

end limits

instance : has_limits RingModPair.{v v} :=
{ has_limits_of_shape := λ J iJ,
  { has_limit := λ F, { exists_limit := nonempty.intro
    { cone := by exactI limit_cone F,
      is_limit := by exactI limit_cone_is_limit F } } } }

end RingModPair
