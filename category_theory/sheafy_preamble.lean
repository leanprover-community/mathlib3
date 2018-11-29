import category_theory.examples.topological_spaces

import category_theory.opposites
import category_theory.yoneda
import category_theory.commas
import category_theory.limits
import category_theory.limits.types
import category_theory.limits.functor_category
import category_theory.full_subcategory
import category_theory.adjunction

open category_theory category_theory.limits

universes u u₁ u₂ u₃ v v₁ v₂ v₃ w w₁ w₂


-- TODO: Move this
section
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def coext_equiv {X Y : C}
  (e : Π {Z : C}, (Y ⟶ Z) ≃ (X ⟶ Z))
  (n : Π {Z Z' : C} (f : Z ⟶ Z') (g : Y ⟶ Z), e.to_fun (g ≫ f) = e.to_fun g ≫ f) : X ≅ Y :=
{ hom := e.to_fun (𝟙 _),
  inv := e.inv_fun (𝟙 _),
  hom_inv_id' := begin rw ←n, simpa using e.right_inv _ end,
  inv_hom_id' := begin
    rw ←e.apply_eq_iff_eq,
    convert ←n _ _,
    convert category.id_comp _ _,
    apply e.right_inv
  end }

lemma coext_equiv_hom_comp {X Y Z : C} {e : Π {Z : C}, (Y ⟶ Z) ≃ (X ⟶ Z)} {n} {f : Y ⟶ Z} :
  (coext_equiv @e n).hom ≫ f = e.to_fun f :=
by convert (n _ _).symm; simp

lemma coext_equiv_hom {X Y : C} {e : Π {Z : C}, (Y ⟶ Z) ≃ (X ⟶ Z)} {n} :
  (coext_equiv @e n).hom = e.to_fun (𝟙 _) := rfl

end


def type_of {X Y : Type v} {p : Y → Prop} (h : X ≅ {y // p y}) : Type v := Y

namespace lattice

open lattice

lemma supr_image {α β γ : Type u} [complete_lattice α]
  {g : β → α} {f : γ → β} {s : set γ}:
  (⨆b∈f '' s, g b) = (⨆i∈s, g (f i)) :=
le_antisymm
  (supr_le $ assume b, supr_le $ assume ⟨c, hcs, eq⟩,
    eq ▸ le_supr_of_le c $ le_supr (λh, g (f c)) hcs)
  (supr_le $ assume c, supr_le $ assume hc,
    le_supr_of_le (f c) $ le_supr (λh, g (f c)) $ set.mem_image_of_mem _ hc)

end lattice

open lattice
open category_theory

namespace lattice.complete_lattice

variables {X : Type u} [complete_lattice X]
variables {J : Type u} [small_category J]

def limit (F : J ⥤ X) : cone F :=
{ X := infi F.obj,
  π := { app := λ j, ⟨⟨infi_le _ j⟩⟩ } }

def colimit (F : J ⥤ X) : cocone F :=
{ X := supr F.obj,
  ι := { app := λ j, ⟨⟨le_supr _ j⟩⟩ } }

def limit_is_limit (F : J ⥤ X) : is_limit (limit F) :=
{ lift := λ s, ⟨⟨le_infi (λ i, plift.down $ ulift.down $ s.π.app i)⟩⟩ }

def colimit_is_colimit (F : J ⥤ X) : is_colimit (colimit F) :=
{ desc := λ s, ⟨⟨supr_le (λ i, plift.down $ ulift.down $ s.ι.app i)⟩⟩ }

instance : has_limits.{u u} X :=
{ cone := λ J hJ F, @limit _ _ J hJ F,
  is_limit := λ J hJ F, @limit_is_limit _ _ J hJ F }

instance : has_colimits.{u u} X :=
{ cocone := λ J hJ F, @colimit _ _ J hJ F,
  is_colimit := λ J hJ F, @colimit_is_colimit _ _ J hJ F }

instance : has_products.{u u} X := has_products_of_has_limits

instance : has_coproducts.{u u} X := has_coproducts_of_has_colimits

instance : has_pullbacks.{u u} X :=
{ square := λ a b c f g, square.mk ⟨⟨inf_le_left a _⟩⟩ ⟨⟨inf_le_right a _⟩⟩ (by tidy),
  is_pullback := λ a b c f g,
  { lift := λ s, by {tidy, refine le_inf _ _ _ _ _,
    convert (plift.down $ ulift.down $ s.π.app walking_cospan.left),
    convert (plift.down $ ulift.down $ s.π.app walking_cospan.right) } } }

instance : has_pushouts.{u u} X :=
{ cosquare := λ a b c f g, cosquare.mk ⟨⟨le_sup_left _ c⟩⟩ ⟨⟨le_sup_right _ c⟩⟩ (by tidy),
  is_pushout := λ a b c f g,
  { desc := λ s, by {tidy, refine sup_le _ _ _ _ _,
    convert (plift.down $ ulift.down $ s.ι.app walking_span.left),
    convert (plift.down $ ulift.down $ s.ι.app walking_span.right) } } }

end lattice.complete_lattice

namespace category_theory

def ulift_trivial (V : Type u₁) : ulift.{u₁} V ≅ V := by tidy

@[simp] lemma ulift_trivial.hom (V : Type u₁) : (ulift_trivial V).hom = λ v, ulift.cases_on v id := rfl

@[simp] lemma ulift_trivial.inv (V : Type u₁) : (ulift_trivial V).inv = ulift.up := rfl

def equiv_of_iso {X Y : Type u} (i : X ≅ Y) : X ≃ Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := λ x, congr i.hom_inv_id rfl,
  right_inv := λ x, congr i.inv_hom_id rfl }

namespace category.hom
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def op {X Y : C} (f : X ⟶ Y) : @category.hom _ category_theory.opposite Y X := f

def deop {X Y : Cᵒᵖ} (f : X ⟶ Y) : @category.hom _ 𝒞 Y X := f

@[simp] lemma op_deop {X Y : C} (f : X ⟶ Y) : f.op.deop = f := rfl

@[simp] lemma deop_op {X Y : Cᵒᵖ} (f : X ⟶ Y) : f.deop.op = f := rfl

end category.hom

namespace functor
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def of : C ⥤ (punit ⥤ C) := const punit

namespace of
@[simp] lemma obj_obj (X : C) : (of.obj X).obj = λ _, X := rfl
@[simp] lemma obj_map (X : C) : (of.obj X).map = λ _ _ _, 𝟙 X := rfl
@[simp] lemma map_app {X Y : C} (f : X ⟶ Y) : (of.map f).app = λ _, f := rfl
end of

end functor

namespace comma
variables {A : Type u₁} [𝒜 : category.{u₁ v₁} A]
variables {B : Type u₂} [ℬ : category.{u₂ v₂} B]
variables {C : Type u} [𝒞 : category.{u v} C]
variables {D : Type u₃} [𝒟 : category.{u₃ v₃} D]
include 𝒜 ℬ 𝒞 𝒟

variables (L : A ⥤ C) (R : A ⥤ C)

def post (F : C ⥤ D) : comma L R ⥤ comma (L ⋙ F) (R ⋙ F) :=
{ obj := λ X, { hom := F.map X.hom, ..X },
  map := λ X Y f, { w' := by erw [← F.map_comp, ← F.map_comp, f.w], ..f } }

end comma

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def iso_of_is_iso {X Y : C} {f : X ⟶ Y} (h : is_iso f) : X ≅ Y :=
{ hom := f,
  ..h}

section over_under -- move somewhere else
set_option pp.universes true
def over (X : C) := comma (functor.id C) (functor.of.obj.{u v v} X)

def under (X : C) := comma (functor.of.obj X) (functor.id C)

end over_under

namespace over

instance {X : C} : category (over X) := by dunfold over; apply_instance
end over

section

@[simp] lemma comma_morphism.over_w {X : C} {A B : over X} (f : A ⟶ B) : f.left ≫ B.hom = A.hom :=
begin
  erw f.w,
  dsimp,
  simp,
end
end

namespace over

def forget (X : C) : (over X) ⥤ C :=
{ obj  := λ Y, Y.left,
  map := λ _ _ f, f.left }

def mk {X Y : C} (f : Y ⟶ X) : over X :=
{ left := Y, hom := f }

@[simp] lemma mk_left {X Y : C} (f : Y ⟶ X) : (mk f).left = Y := rfl
@[simp] lemma mk_hom {X Y : C} (f : Y ⟶ X) : (mk f).hom = f := rfl
@[simp] lemma mk_right {X Y : C} (f : Y ⟶ X) : (mk f).right = ⟨⟩ := rfl

def map {X Y : C} (f : X ⟶ Y) : over X ⥤ over Y :=
{ obj := λ U, mk (U.hom ≫ f),
  map := λ U V g,
  { left := g.left,
    w' :=
    begin
      dsimp,
      simp,
      rw [← category.assoc],
      simp,
    end } }

@[simp] lemma id_left {X : C} (x : over X) : comma_morphism.left (𝟙 x) = 𝟙 x.left := rfl
@[simp] lemma id_right {X : C} (x : over X) : comma_morphism.right (𝟙 x) = 𝟙 x.right := rfl

@[simp] lemma comp_left {X : C} (a b c : over X) (f : a ⟶ b) (g : b ⟶ c) :
  comma_morphism.left (f ≫ g) = comma_morphism.left f ≫ comma_morphism.left g := rfl
@[simp] lemma comp_right {X : C} (a b c : over X) (f : a ⟶ b) (g : b ⟶ c) :
  comma_morphism.right (f ≫ g) = comma_morphism.right f ≫ comma_morphism.right g := rfl

def comap [has_pullbacks.{u v} C] {X Y : C} (f : X ⟶ Y) : over Y ⥤ over X :=
{ obj  := λ V, mk $ pullback.π₁ f V.hom,
  map := λ V₁ V₂ g,
  { left := pullback.lift f _ (pullback.π₁ f V₁.hom) (pullback.π₂ f V₁.hom ≫ g.left) (by tidy) },
  map_comp' :=
  begin
    tidy, conv { to_rhs, rw ← category.assoc }, tidy,
  end }

section
variables {D : Type u₃} [𝒟 : category.{u₃ v₃} D]
include 𝒟

def post (F : C ⥤ D) {X : C} : over X ⥤ over (F.obj X) :=
{ obj := λ Y, mk $ F.map Y.hom,
  map := λ Y₁ Y₂ f, { left := F.map f.left, w' := by tidy; erw [← F.map_comp, f.over_w] } }

end

end over

namespace functor

section full_faithful
variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒟

instance {F : C ⥤ D} [full F] : full F.op :=
{ preimage := λ X Y f, F.preimage f }

instance {F : C ⥤ D} [faithful F] : faithful F.op :=
{ injectivity' := λ X Y f g h, by simpa using injectivity F h }

@[simp] lemma preimage_id (F : C ⥤ D) [fully_faithful F] (X : C) : F.preimage (𝟙 (F.obj X)) = 𝟙 X :=
injectivity F (by tidy)

end full_faithful

@[simp] lemma left_unitor_hom_app {J : Type v} [small_category J] (F : J ⥤ C) (j : J) :
((functor.left_unitor F).hom).app j = 𝟙 (F.obj j) := rfl

@[simp] lemma left_unitor_inv_app {J : Type v} [small_category J] (F : J ⥤ C) (j : J) :
((functor.left_unitor F).inv).app j = 𝟙 (F.obj j) := rfl

end functor

namespace nat_trans
variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒟

@[simp] lemma id_app' (F : C ⥤ D) (X : C) : nat_trans.app (𝟙 F) X = 𝟙 (F.obj X) := rfl

end nat_trans

namespace limits
open category_theory

variables {J : Type v} [small_category J] [has_colimits_of_shape.{u v} J C]

lemma colimit.pre_map {K : Type v} [small_category K] [has_colimits_of_shape.{u v} K C]
  (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟹ E₂) :
  colimit.pre F E₁ = colim.map (whisker_right α F) ≫ colimit.pre F E₂ :=
begin
  ext1, dsimp,
  conv {to_rhs, rw ←category.assoc},
  simp,
end

lemma colimit.pre_id (F : J ⥤ C) :
colimit.pre F (functor.id _) = colim.map (functor.left_unitor F).hom := by tidy

lemma colimit.pre_comp
{K : Type v} [small_category K] [has_colimits_of_shape.{u v} K C]
{L : Type v} [small_category L] [has_colimits_of_shape.{u v} L C]
(F : J ⥤ C) (E : K ⥤ J) (D : L ⥤ K) :
colimit.pre F (D ⋙ E) = colim.map (functor.associator D E F).hom
≫ colimit.pre _ D ≫ colimit.pre F E :=
begin
  tidy {trace_result := tt},
  erw ← category.assoc,
  erw colim_ι_map (functor.associator D E F).hom j,
  dsimp [functor.associator],
  simp,
  erw is_colimit.fac,
  refl
end

@[simp] lemma colim_obj (F : J ⥤ C) : colim.obj F = colimit F := rfl

def colimit.coyoneda {F : J ⥤ C} [has_colimit F] : coyoneda.obj (colimit F) ≅ F.cocones :=
{ hom :=
  { app := λ P f, cocones_of_cocone ((colimit.cocone F).extend f),
    naturality' :=
    begin
      tidy {trace_result := tt},
      sorry
    end },
  inv :=
  { app := λ P c, colimit.desc F (cocone_of_cocones c),
    naturality' :=
    begin
      tidy {trace_result := tt},
      sorry
    end } }

end limits

end category_theory