import category_theory.limits.limits
import category_theory.limits.preserves
import category_theory.products

open category_theory

namespace category_theory.limits

universes u v

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

variables {J K : Type v} [small_category J] [small_category K]

def switched (F : J ⥤ (K ⥤ C)) : K ⥤ (J ⥤ C) :=
{ obj := λ k,
  { obj := λ j, (F j) k,
    map' := λ j j' f, (F.map f) k,
    map_id' := λ X, begin rw category_theory.functor.map_id, refl end,
    map_comp' := λ X Y Z f g, by rw [functor.map_comp, ←functor.category.comp_app] },
  map' := λ c c' f, { app := λ j, (F j).map f, naturality' := λ X Y g, by dsimp; rw ←nat_trans.naturality } }.

@[simp] lemma switched_obj_map (F : J ⥤ (K ⥤ C)) {j j' : J} (f : j ⟶ j') (X : K) : ((switched F) X).map f = (F.map f) X := rfl

@[simp] lemma cone.functor_w {F : J ⥤ (K ⥤ C)} (c : cone F) {j j' : J} (f : j ⟶ j') (k : K) :
  (c.π j) k ≫ (F.map f) k = (c.π j') k :=
begin
  have h := congr_fun (congr_arg (nat_trans.app) (eq.symm (c.π.naturality f))) k,
  dsimp at h,
  rw category.id_comp at h,
  conv at h { to_rhs, simp },
  erw ←h,
  conv { to_rhs, rw nat_trans.app_eq_coe }, -- yuck
  refl,
end

@[simp] def functor_category_limit_cone [has_limits_of_shape.{u v} J C] (F : J ⥤ K ⥤ C) : cone F :=
{ X := switched F ⋙ lim,
  π :=
  { app := λ j,
    { app := λ k , limit.π _ j },
      naturality' := λ j j' f, begin dsimp, simp, ext k, dsimp, erw limit.w, end } }

@[simp] def evaluate_functor_category_limit_cone [has_limits_of_shape.{u v} J C] (F : J ⥤ K ⥤ C) (k : K) :
  (evaluation K C k).map_cone (functor_category_limit_cone F) ≅ limit.cone ((switched F) k) :=
begin
  ext,
  swap,
  tidy, -- FIXME why does tidy need the swap here??
end

def functor_category_is_limit_cone [has_limits_of_shape.{u v} J C] (F : J ⥤ K ⥤ C) :
  is_limit (functor_category_limit_cone F) :=
{ lift := λ s,
  { app := λ k, limit.lift ((switched F) k)
    { X := s.X k,
      π := { app := λ j, s.π j k } },
    naturality' := λ k k' f,
    begin
      ext, dsimp, simp, rw ←category.assoc, simp, rw nat_trans.naturality, refl,
    end },
  uniq' := λ s m w,
  begin
    ext k j, dsimp, simp,
    rw ← w j,
    refl
  end }

instance functor_category_has_limits_of_shape [has_limits_of_shape.{u v} J C] : has_limits_of_shape J (K ⥤ C) :=
{ cone := λ F, functor_category_limit_cone F,
  is_limit := λ F, functor_category_is_limit_cone F }
instance functor_category_has_colimits_of_shape [has_colimits_of_shape.{u v} J C] : has_colimits_of_shape J (K ⥤ C) :=
sorry

instance functor_category_has_limits [has_limits.{u v} C] : has_limits.{(max u v) v} (K ⥤ C) :=
{ cone := λ J 𝒥 F, by resetI; exact functor_category_limit_cone F,
  is_limit := λ J 𝒥 F, by resetI; exact functor_category_is_limit_cone F }
instance functor_category_has_colimits [has_colimits.{u v} C] : has_colimits.{(max u v) v} (K ⥤ C) :=
sorry

instance evaluation_preserves_limits_of_shape [has_limits_of_shape.{u v} J C] (k : K) :
  preserves_limits_of_shape J (evaluation.{v v u v} K C k) :=
{ preserves := λ F c h,
  begin
    have i : functor_category_limit_cone F ≅ c := limit_cone.ext (functor_category_is_limit_cone F) h,
    apply is_limit_invariance _ _ (functor.on_iso _ i),

    -- Next, we know exactly what the evaluation of the `product_cone F` is:
    apply is_limit_invariance _ _ (evaluate_functor_category_limit_cone F k).symm,

    -- Finally, it's just that the limit cone is a limit.
    exact limit.universal_property _
  end }

instance evaluation_preserves_limits [has_limits.{u v} C] (k : K) :
  preserves_limits (evaluation.{v v u v} K C k) := sorry

end category_theory.limits
