import category_theory.limits.limits
import category_theory.limits.preserves

open category_theory

namespace category_theory.limits

universes u v

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

variables {J K : Type v} [small_category J] [small_category K]

@[simp] def switched (F : J ⥤ (K ⥤ C)) : K ⥤ (J ⥤ C) :=
{ obj := λ k,
  { obj := λ j, (F j) k,
    map' := λ j j' f, (F.map f) k,
    map_id' := λ X, begin rw category_theory.functor.map_id, refl end,
    map_comp' := λ X Y Z f g, by rw [functor.map_comp, ←functor.category.comp_app] },
  map' := λ c c' f, { app := λ j, (F j).map f, naturality' := λ X Y g, by dsimp; rw ←nat_trans.naturality } }.

@[simp] lemma switched_obj_map (F : J ⥤ (K ⥤ C)) {j j' : J} (f : j ⟶ j') (X : K) : ((switched F) X).map f = (F.map f) X := rfl

@[simp] lemma cone.functor_w {F : J ⥤ (K ⥤ C)} (c : cone F) {j j' : J} (f : j ⟶ j') (k : K) :
  (c.π j) k ≫ (F.map f) k = (c.π j') k :=
sorry

@[simp] lemma discrete.functor_map_id (F : discrete K ⥤ C) (k : discrete K) (f : k ⟶ k) : F.map f = 𝟙 (F k) :=
begin
  have h : f = 𝟙 k, cases f, cases f, ext,
  rw h,
  simp,
end

def product_cone [has_limits_of_shape.{u v} J C] (F : J ⥤ (discrete K ⥤ C)) : cone F :=
{ X :=
  { obj := λ k, limit ((switched F) k),
    map' := λ k k' f, begin cases f, cases f, cases f, exact 𝟙 _ end },
  π :=
  { app := λ j,
    { app := λ k, limit.π _ _ },
      naturality' := λ j j' f, begin ext, dsimp, simp, erw limit.w, end } }.

@[simp] lemma product_cone_π [has_limits_of_shape.{u v} J C] (F : J ⥤ (discrete K ⥤ C)) (j : J) (k : K):
  ((product_cone F).π : Π j : J, _ ⟹ _) j k = limit.π _ _ := rfl

@[simp] lemma evaluate_product_cone [has_limits_of_shape.{u v} J C] (F : J ⥤ (discrete K ⥤ C)) (k : K) :
  (evaluation_at (discrete K) C k).map_cone (product_cone F) ≅ limit.cone ((switched F) k) :=
begin
  ext,
  swap,
  tidy, -- FIXME why does tidy need the swap here??
end

def product_cone_is_limit [has_limits_of_shape.{u v} J C] (F : J ⥤ (discrete K ⥤ C)) : is_limit (product_cone F) :=
{ lift := λ s,
    { app := λ k, limit.lift ((switched F) k)
      { X := s.X k,
        π := { app := λ j, s.π j k } } },
  uniq' := λ s m w,
  begin
    ext k j,
    dsimp,
    simp,
    have h := congr_fun (congr_arg nat_trans.app (w j)) k,
    simp at h, -- re-express in terms of coercions, yuck
    erw ←h,
    refl,
  end }

instance product_has_limits_of_shape [has_limits_of_shape.{u v} J C] : has_limits_of_shape J (discrete K ⥤ C) :=
{ cone := λ F, product_cone F,
  is_limit := λ F, product_cone_is_limit F }.

instance [has_limits_of_shape.{u v} J C] (k : K) : preserves_limits_of_shape J (evaluation_at.{v v u v} (discrete K) C k) :=
{ preserves := λ F c h,
  begin
    /-
    Emily justs says here:

    > It is easy to see that a limit of each of these component diagrams assembles into a
    > limit for the diagram in C^{ob A} ≅􏰺 Π_{􏰰ob A} C. In particular, C^{ob A} has all limits or
    > colimits that C does, and these are preserved by the evaluation functors ev_a : C^{ob A} ⥤ C.
    -/

    -- We first replace the arbitrary limit cone c with `product_cone F`.
    have i : product_cone F ≅ c := limit_cone.ext (product_cone_is_limit F) h,
    apply is_limit_invariance _ (functor.on_iso _ i),

    -- Next, we know exactly what the evaluation of the `product_cone F` is:
    apply is_limit_invariance _ (evaluate_product_cone F k).symm,

    -- Finally, it's just that the limit cone is a limit.
    exact limit.universal_property _
  end }

end category_theory.limits