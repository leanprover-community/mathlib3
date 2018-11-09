import category_theory.examples.topological_spaces

import category_theory.opposites
import category_theory.yoneda
import category_theory.commas
import category_theory.limits
import category_theory.limits.types
import category_theory.limits.functor_category

open category_theory.limits

universes u u₁ u₂ v v₁ v₂ w w₁ w₂

namespace category_theory

section presheaf
variables (X : Type v) [𝒳 : small_category X] (C : Type u) [𝒞 : category.{u v} C]
include 𝒳 𝒞

def presheaf := Xᵒᵖ ⥤ C

variables {X} {C}

instance presheaf_category : category.{(max u v) v} (presheaf X C) := by unfold presheaf; apply_instance

set_option pp.universes true
instance presheaf.has_coequalizers [has_coequalizers.{u v} C] :
  has_coequalizers.{(max u v) v} (presheaf X C) := limits.functor_category_has_coequalizers
instance presheaf.has_coproducts [has_coproducts.{u v} C] :
  has_coproducts.{(max u v) v} (presheaf X C) := limits.functor_category_has_coproducts
instance presheaf.has_limits [has_limits.{u v} C] :
  has_limits.{(max u v) v} (presheaf X C) := limits.functor_category_has_limits
instance presheaf.has_pullbacks [has_pullbacks.{u v} C] :
  has_pullbacks.{(max u v) v} (presheaf X C) := limits.functor_category_has_pullbacks

omit 𝒞

-- TODO these can be removed; just checking they work
instance presheaf_of_types.has_coequalizers : has_coequalizers.{v+1 v} (presheaf X (Type v)) := by apply_instance
instance presheaf_of_types.has_coproducts : has_coproducts.{v+1 v} (presheaf X (Type v)) := by apply_instance
instance presheaf_of_types.has_limits : has_limits.{v+1 v} (presheaf X (Type v)) := by apply_instance
instance presheaf_of_types.has_pullbacks : has_pullbacks.{v+1 v} (presheaf X (Type v)) := by apply_instance

end presheaf

section over_under -- move somewhere else
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def over (X : C) := comma (functor.id C) (functor.of_obj X)

def under (X : C) := comma (functor.of_obj X) (functor.id C)

end over_under

namespace over
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

instance {X : C} : category (over X) := by dunfold over; apply_instance
end over

section
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

@[simp] lemma comma_morphism.over_w {X : C} {A B : over X} (f : A ⟶ B) : f.left ≫ B.hom = A.hom :=
begin
  erw f.w,
  dsimp,
  simp,
end
end

namespace over
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

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

end over

@[reducible]
def covering_family {X : Type v} [small_category X] (U : X) : Type v := set (over.{v v} U)

namespace covering_family
open category_theory.limits
variables {X : Type v} [𝒳 : small_category X]
include 𝒳

variables {U : X} (c : covering_family U)

def sieve : presheaf X (Type v) :=
let
  y (Ui : c) := (yoneda X).map Ui.val.hom,
  pb (Ujk : c × c) : presheaf X (Type v) := limits.pullback (y Ujk.1) (y Ujk.2),
  re (Ui : c) : presheaf X (Type v) := (yoneda X).obj Ui.val.left,
  left  : limits.sigma pb ⟶ limits.sigma re :=
    sigma.desc $ λ Ujk : c × c, pullback.π₁ (y Ujk.1) (y Ujk.2) ≫ sigma.ι re Ujk.1,
  right : limits.sigma pb ⟶ limits.sigma re :=
    sigma.desc $ λ Ujk : c × c, pullback.π₂ (y Ujk.1) (y Ujk.2) ≫ sigma.ι re Ujk.2
in coequalizer left right

def π : c.sieve ⟶ (yoneda X).obj U :=
coequalizer.desc _ _ (sigma.desc $ λ Ui, (yoneda X).map Ui.val.hom)
begin
  ext1, dsimp at *,
  rw ←category.assoc,
  rw ←category.assoc,
  simp,
end

def sheaf_condition (F : presheaf X (Type v)) :=
is_iso $ ((yoneda (presheaf X (Type v))).obj F).map c.π

end covering_family

structure coverage (X : Type u) [small_category.{u} X] :=
(covers   : Π (U : X), set (covering_family U))
(id       : ∀ (U : X), {(over.mk (𝟙 U))} ∈ covers U . obviously)
(property : ∀ {U V : X} (g : V ⟶ U),
            ∀ f ∈ covers U, ∃ h ∈ covers V,
            ∀ Vj ∈ (h : set _), ∃ (Ui ∈ f),
            nonempty $ ((over.map g).obj Vj) ⟶ Ui)

class site (X : Type u) extends category.{u u} X :=
(coverage : coverage X)

namespace site
variables {X : Type u₁} [𝒳 : site.{u₁} X]

definition covers := coverage.covers 𝒳.coverage

end site

def site.trivial (X : Type u) [small_category.{u} X] : site X :=
{ coverage :=
  { covers := λ U Us, Us = {(over.mk (𝟙 U))},
    property := λ U V g f (hf : _ = _), ⟨{(over.mk (𝟙 V))}, rfl,
    begin
      subst hf,
      intros Vj hVj,
      refine ⟨_, set.mem_singleton _, _⟩,
      { have : Vj = over.mk (𝟙 V) := set.mem_singleton_iff.mp hVj,
        subst this,
        tidy }
    end ⟩ } }

def site.discrete (X : Type u) [small_category.{u} X] : site X :=
{ coverage :=
  { covers := λ U Us, true,
    property := λ U V g f _, ⟨{Vj | false}, by simp, (λ Vj hVj, false.elim hVj)⟩ } }

structure sheaf (X : Type u) [𝒳 : site.{u} X] :=
(presheaf : presheaf X (Type u))
(sheaf_condition : ∀ {U : X}, ∀c ∈ site.covers U, (c : covering_family U).sheaf_condition presheaf)

end category_theory

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

instance : has_pullbacks.{u u} X := has_pullbacks_of_has_limits

instance : has_coproducts.{u u} X := has_coproducts_of_has_colimits

end lattice.complete_lattice

namespace topological_space

variables {X : Type u} [topological_space X]

instance : site (opens X) :=
{ coverage :=
  { covers := λ U Us, U = ⨆u∈Us, (u:over _).left,
    property := λ U V (i : V ⟶ U) (Us : covering_family U) (Us_cover : U = ⨆u∈Us, (u:over _).left),
    begin
      refine ⟨ (over.comap i).obj '' Us, _, _⟩,
      { show _ = _,
        rw [lattice.supr_image],
        apply le_antisymm,
        { show V.val ≤ (⨆ (Ui : over U) (H : Ui ∈ Us), ((over.comap i).obj Ui).left).val,
          intros x hx,
          have := plift.down (ulift.down i) hx,
          erw [Us_cover, set.mem_bUnion_iff] at this,
          rcases this with ⟨Ui, ⟨H, x_in_Ui⟩⟩,
          erw set.mem_bUnion_iff,
          existsi V ⊓ Ui, -- the order dual is messing things up
          dsimp at *,
          cases H,
          split,
          refine ⟨H_w, _⟩,
          { sorry },
          fsplit,
          sorry },
        { refine supr_le _,
          intro Ui,
          refine supr_le _,
          intro hUi,
          exact plift.down (ulift.down (pullback.π₁ i Ui.hom).hom), } },
      { rintros Vj ⟨Ui, H⟩,
        refine ⟨Ui, H.1, _⟩,
        have H' := H.2.symm,
        subst H',
        exact ⟨ { left := pullback.π₂ i Ui.hom } ⟩ }
    end } }

variables {B : set (opens X)}

instance basis.site {is_basis : opens.is_basis B} : site B :=
{ coverage :=
  { covers := λ U Us, U.val = ⨆u∈Us, (u:over _).left.val,
    property := λ U V (i : V ⟶ U) (Us : covering_family U) (Us_cover : U.val = ⨆ Ui ∈ Us, ((Ui : over _).left).val),
      ⟨ show covering_family V,
          from { Vj : over V | ∃ Ui ∈ Us, nonempty $ ((over.map i).obj Vj) ⟶ Ui },
        show V.val = ⨆ (Vj : over V) (hVj : ∃ Ui ∈ Us, nonempty $ ((over.map i).obj Vj) ⟶ Ui), Vj.left.val,
          from begin
            apply le_antisymm,
            { intros x x_in_V,
              rw opens.is_basis_iff_nbhd at is_basis,
              have i' := plift.down (ulift.down i),
              have := is_basis (i' x_in_V),
              sorry },
            { refine supr_le _,
              intro Vj,
              refine supr_le _,
              intro hVj,
              show Vj.left.val ≤ V.val,
              exact plift.down (ulift.down Vj.hom), }
          end,
        -- show ∀ (Vj : over V), Vj ∈ {Vj : over V | _ } → _,
          by obviously
      ⟩ } }

end topological_space
