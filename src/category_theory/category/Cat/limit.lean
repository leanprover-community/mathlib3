import category_theory.category.Cat
import category_theory.limits.types

noncomputable theory

universes v u

open category_theory
open category_theory.limits

@[simp] lemma foo {C D E : Cat.{v u}} (f : C ⟶ D) (g : D ⟶ E) : f ≫ g = f ⋙ g := rfl
@[simp] lemma bar {C D : Cat.{v u}} (f : C ⟶ D) : 𝟙 C ⋙ f = f := sorry

variables {J : Type v} [small_category J]

set_option pp.universes true

instance category_objects {F : J ⥤ Cat.{v v}} {j} :
  small_category ((F ⋙ Cat.objects.{v v}).obj j) :=
(F.obj j).str

instance category_objects' {F : J ⥤ Cat.{v v}} {j} :
  small_category ((Cat.objects.{v v}).obj (F.obj j)) :=
(F.obj j).str


@[simps]
def hom_diagram {F : J ⥤ Cat.{v v}} (X Y : limit (F ⋙ Cat.objects.{v v})) : J ⥤ Type v :=
{ obj := λ j, limit.π (F ⋙ Cat.objects) j X ⟶ limit.π (F ⋙ Cat.objects) j Y,
  map := λ j j' f g,
  begin
    refine eq_to_hom _ ≫ (F.map f).map g ≫ eq_to_hom _,
    exact (congr_fun (limit.w (F ⋙ Cat.objects) f) X).symm,
    exact (congr_fun (limit.w (F ⋙ Cat.objects) f) Y),
  end,
  map_id' := λ X, begin ext f, dsimp, simp, sorry, end,
  map_comp' := sorry, }

@[simp]
lemma fooo {F : J ⥤ Cat.{v v}} (X Y : limit (F ⋙ Cat.objects.{v v})) (j : J) (h) :
limit.π (hom_diagram X Y) j (eq_to_hom h) = eq_to_hom sorry := sorry


@[simps]
def limit (F : J ⥤ Cat.{v v}) : Cat.{v v} :=
{ α := limit (F ⋙ Cat.objects),
  str :=
  { hom := λ X Y, limit (hom_diagram X Y),
    id := λ X, begin fapply types.limit.mk, intro j, dsimp, exact 𝟙 _, intros j j' f, simp, end,
    comp := λ X Y Z f g,
    begin
      fapply types.limit.mk,
      intro j,
      dsimp,
      exact limit.π (hom_diagram X Y) j f ≫ limit.π (hom_diagram Y Z) j g,
      intros j j' h,
      dsimp,
      conv_rhs { rw ←congr_fun (limit.w (hom_diagram X Y) h) f, },
      conv_rhs { rw ←congr_fun (limit.w (hom_diagram Y Z) h) g, },
      dsimp,
      simp,
    end } }.

instance quux (F : J ⥤ Cat.{v v}) : category.{v v} (limit.{v v+1} (F ⋙ Cat.objects.{v v})) :=
(limit F).str

@[simps]
def limit_cone (F : J ⥤ Cat.{v v}) : cone F :=
{ X := limit F,
  π :=
  { app := λ j,
    { obj := limit.π (F ⋙ Cat.objects) j,
      map := λ X Y, limit.π (hom_diagram X Y) j,
      map_id' := by tidy,
      map_comp' := by tidy, },
    naturality' := λ j j' f,
    begin
      fapply category_theory.functor.ext,
      intro X,
      dsimp,
      have := congr_fun (limit.w (F ⋙ Cat.objects) f) X,
      exact this.symm,
      intros X Y h,
      dsimp,
      sorry, -- scary!?
    end, } }

@[simps]
def limit_cone_lift (F : J ⥤ Cat.{v v}) (s : cone F) : s.X ⟶ limit F :=
{ obj := limit.lift (F ⋙ Cat.objects)
  { X := s.X,
    π :=
    { app := λ j, (s.π.app j).obj,
      naturality' := λ j j' f,
      begin
        ext X,
        exact congr_fun (congr_arg functor.obj (s.π.naturality f) : _) X,
      end, } },
  map := λ X Y f,
  begin
    dsimp, fapply types.limit.mk,
    { intro j,
      dsimp,
      refine eq_to_hom _ ≫ (s.π.app j).map f ≫ eq_to_hom _;
      simp only [types.lift_π_apply], },
    { intros j j' h,
      dsimp,
      simp,
      rw [←functor.comp_map],
      have := (s.π.naturality h).symm,
      -- change _ ⋙ _ = _ at this,
      conv at this { congr, skip, dsimp, simp, },
      -- rw this, -- equations between functors...
      sorry },
  end, }


-- set_option pp.proofs true
def limit_cone_is_limit (F : J ⥤ Cat.{v v}) : is_limit (limit_cone F) :=
{ lift := limit_cone_lift F,
  fac' := λ s j,
  begin
    fapply category_theory.functor.ext,
    { tidy, }, -- works by tidy
    { intros X Y f, dsimp, simp, convert types.limit.π_mk _ _ _ _, dsimp, simp, },
  end,
  uniq' := λ s m w,
  begin
    symmetry,
    fapply category_theory.functor.ext,
    dsimp,
    intro X,
    ext,
    simp,
    rw ←w j,
    refl,
    intros X Y f,
    dsimp only [limit_cone_lift],
    -- simp,

    simp_rw (λ j, functor.congr_hom (w j).symm f),
    dsimp,
    congr,

  end, }
