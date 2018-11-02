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

def functor_category_limit_cone [has_limits_of_shape.{u v} J C] (F : J ⥤ K ⥤ C) : cone F :=
{ X := switched F ⋙ lim,
  π :=
  { app := λ j,
    { app := λ k , limit.π _ j },
      naturality' := λ j j' f, begin dsimp, simp, ext k, dsimp, erw limit.w, end } }

instance functor_category_has_limits_of_shape [has_limits_of_shape.{u v} J C] : has_limits_of_shape J (K ⥤ C) :=
{ cone := λ F, functor_category_limit_cone F,
  is_limit := sorry }

instance evaluation_preserves_limits [has_limits_of_shape.{u v} J C] (k : K) :
  preserves_limits_of_shape J (evaluation.{v v u v} K C k) :=
{ preserves := λ F c h,
  begin
    sorry
  end }

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

@[simp] def evaluate_product_cone [has_limits_of_shape.{u v} J C] (F : J ⥤ (discrete K ⥤ C)) (k : K) :
  (evaluation (discrete K) C k).map_cone (product_cone F) ≅ limit.cone ((switched F) k) :=
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

instance product_evaluation_preserves_limits [has_limits_of_shape.{u v} J C] (k : K) : preserves_limits_of_shape J (evaluation.{v v u v} (discrete K) C k) :=
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

instance : creates_limits (discrete.forget J C) :=
{ reflects := sorry,
  creates := λ K 𝒦 F c h,
  begin
    resetI,
    exact
    { X :=
      { obj := λ j, c.X j,
        map' := λ j j' f,
        begin
          -- math goes here. I'm apparently too dumb to work this out.
          let cjf : limits.cone ((F ⋙ discrete.forget J C) ⋙ (evaluation (discrete J) C) j') :=
          { X := c.X j,
            π :=
            { app := λ k, c.π k j ≫ (F k).map f,
              naturality' := λ k k' g,
              begin
                dsimp,
                erw [category.id_comp, category.assoc, nat_trans.naturality, ←category.assoc, cone.functor_w]
              end }},
          have w : (c.X) j = cjf.X := rfl,
          let cj' := (evaluation (discrete J) C j').map_cone c,
          have w' : cj'.X = (c.X) j' := rfl,
          refine (eq_to_iso w).hom ≫ _ ≫ (eq_to_iso w').hom,
          clear w w',
          have hj' : is_limit cj' := sorry,
          exact hj'.lift cjf,
        end,
        map_comp' := begin sorry end,
        map_id' := sorry
      },
      π := begin sorry end
    },
  end,
  image_is_limit := sorry,
  }

instance functor_category_has_limits_of_shape [has_limits_of_shape.{u v} J C] : has_limits_of_shape J (K ⥤ C) :=
created_limits_of_shape (discrete.forget K C)

end category_theory.limits