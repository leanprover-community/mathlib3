import category_theory.examples.topological_spaces

import category_theory.opposites
import category_theory.yoneda
import category_theory.commas
import category_theory.limits
import category_theory.limits.types
import category_theory.limits.functor_category

open category_theory
open category_theory.limits

universes u u₁ u₂ v v₁ v₂ w w₁ w₂

section presheaf
variables (X : Type v) [𝒳 : small_category X] (C : Type u) [𝒞 : category.{u v} C]
include 𝒳 𝒞

def presheaf := Xᵒᵖ ⥤ C

variables {X} {C}

instance : category.{(max u v) v} (presheaf X C) := by unfold presheaf; apply_instance

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

def forget (X : C) : (over X) ⥤ C :=
{ obj  := λ Y, Y.left,
  map' := λ _ _ f, f.left }

def mk {X Y : C} (f : Y ⟶ X) : over X :=
{ left := Y, right := punit.star, hom := f }

@[simp] lemma mk_left {X Y : C} (f : Y ⟶ X) : (mk f).left = Y := rfl
@[simp] lemma mk_hom {X Y : C} (f : Y ⟶ X) : (mk f).hom = f := rfl
@[simp] lemma mk_right {X Y : C} (f : Y ⟶ X) : (mk f).right = ⟨⟩ := rfl

def map {X Y : C} (f : X ⟶ Y) : over X ⥤ over Y :=
{ obj := λ U, mk (U.hom ≫ f),
  map' := λ U V g,
  { left := g.left,
    right := punit.star,
    w' :=
    begin
      dsimp only [mk],
      rw [← category.assoc, g.w],
      dsimp [limits.functor.of_obj],
      simp
    end } }

@[simp] lemma id_left {X : C} (x : over X) : comma_morphism.left (𝟙 x) = 𝟙 x.left := rfl
@[simp] lemma id_right {X : C} (x : over X) : comma_morphism.right (𝟙 x) = 𝟙 x.right := rfl

@[simp] lemma comp_left {X : C} (a b c : over X) (f : a ⟶ b) (g : b ⟶ c) :
  comma_morphism.left (f ≫ g) = comma_morphism.left f ≫ comma_morphism.left g := rfl
@[simp] lemma comp_right {X : C} (a b c : over X) (f : a ⟶ b) (g : b ⟶ c) :
  comma_morphism.right (f ≫ g) = comma_morphism.right f ≫ comma_morphism.right g := rfl

def comap [has_pullbacks.{u v} C] {X Y : C} (f : X ⟶ Y) : over Y ⥤ over X :=
{ obj  := λ V, mk $ pullback.π₁ f V.hom,
  map' := λ V₁ V₂ g,
  { left := pullback.lift f _ (pullback.π₁ f V₁.hom) (pullback.π₂ f V₁.hom ≫ g.left)
      begin
        have := g.w,
        dsimp [functor.of_obj] at this,
        simp at this,
        rw [pullback.w, category.assoc, this],
      end,
    right := punit.star,
    w' := by dsimp [mk, functor.of_obj]; simp },
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
    sigma.desc $ λUjk:c×c, pullback.π₁ (y Ujk.1) (y Ujk.2) ≫ sigma.ι re Ujk.1,
  right : limits.sigma pb ⟶ limits.sigma re :=
    sigma.desc $ λUjk:c×c, pullback.π₂ (y Ujk.1) (y Ujk.2) ≫ sigma.ι re Ujk.2
in coequalizer left right

def π : c.sieve ⟶ yoneda X U :=
coequalizer.desc _ _ (sigma.desc $ λUi, (yoneda X).map Ui.val.hom)
begin
  ext1, dsimp at *,
  erw ←category.assoc,
  erw ←category.assoc,
  simp,
end

def sheaf_condition (F : presheaf X (Type v)) :=
is_iso $ ((yoneda (presheaf X (Type v))).obj F).map c.π

end covering_family

def coverage_on (X : Type u) [small_category.{u} X]
  (covers : Π (U : X), set (covering_family U)) : Prop :=
∀ {U V : X} (g : V ⟶ U),
∀f ∈ covers U, ∃h ∈ covers V,
∀ Vj : (h : set _), ∃ (Ui : f),
∃ k : Vj.val.left ⟶ Ui.val.left, Vj.val.hom ≫ g = k ≫ Ui.val.hom

structure coverage (X : Type u) [small_category.{u} X] :=
(covers   : Π (U : X), set (covering_family U))
(property : coverage_on X covers)

class site (X : Type u) extends category.{u u} X :=
(coverage : coverage X)

namespace site
variables {X : Type u₁} [𝒳 : site.{u₁} X]

definition covers := coverage.covers 𝒳.coverage

end site

def site.trivial (X : Type u) [small_category.{u} X] : site X :=
{ coverage :=
  { covers := λ U Us, false,
    property := λ U V g f hf, false.elim hf } }

def site.discrete (X : Type u) [small_category.{u} X] : site X :=
{ coverage :=
  { covers := λ U Us, true,
    property := λ U V g f _, ⟨{Vj | false}, by simp, (λ Vj, false.elim Vj.property)⟩ } }

structure sheaf (X : Type u) [𝒳 : site.{u} X] :=
(presheaf : presheaf X (Type u))
(sheaf_condition : ∀ {U : X}, ∀c ∈ site.covers U, (c : covering_family U).sheaf_condition presheaf)

namespace lattice

lemma supr_image {α β γ : Type u} [complete_lattice α]
  {g : β → α} {f : γ → β} {s : set γ}:
  (⨆b∈f '' s, g b) = (⨆i∈s, g (f i)) :=
le_antisymm
  (supr_le $ assume b, supr_le $ assume ⟨c, hcs, eq⟩,
    eq ▸ le_supr_of_le c $ le_supr (λh, g (f c)) hcs)
  (supr_le $ assume c, supr_le $ assume hc,
    le_supr_of_le (f c) $ le_supr (λh, g (f c)) $ set.mem_image_of_mem _ hc)

end lattice

namespace lattice.complete_lattice

open lattice

variables {X : Type u} [complete_lattice X]
variables {J : Type u} [small_category J]

def limit (F : J ⥤ X) : cone F :=
{ X := infi F.obj,
  π := { app := λ j, ⟨⟨infi_le _ j⟩⟩ } }

def limit_is_limit (F : J ⥤ X) : is_limit (limit F) :=
{ lift := λ s, ⟨⟨le_infi (λ i, plift.down $ ulift.down $ s.π i)⟩⟩ }

instance : has_limits.{u u} X :=
{ cone := λ J hJ F, @limit _ _ J hJ F,
  is_limit := λ J hJ F, @limit_is_limit _ _ J hJ F }

instance : has_pullbacks.{u u} X := has_pullbacks_of_has_limits

end lattice.complete_lattice

namespace topological_space

variables {X : Type u} [topological_space X]

-- instance opens.over.preorder {U : opens X} : preorder (over U) :=
-- { le := λ V₁ V₂, V₁.left ⊆ V₂.left,
--   le_refl := by obviously,
--   le_trans := by obviously }

-- def opens.over.gc {U V : opens X} (i : V ⟶ U) : galois_connection (over.map i) (over.comap i) :=
-- begin
--   intros V' U',
--   dsimp [(≤), preorder.le, over.map, over.comap] at *,
--   split; intro h,
--   { sorry },
--   { sorry }
-- end

instance : site (opens X) :=
{ coverage :=
  { covers := λ U Us, U = ⨆u∈Us, (u:over _).left,
    property :=
    begin
      refine λU V i Us (hUs : _ = _), ⟨over.comap i '' Us, _, _⟩,
      { show _ = _,
        rw [lattice.supr_image],
        sorry },
      { rintros ⟨Vj, Ui, H⟩,
        refine ⟨⟨Ui, H.1⟩, ⟨_, rfl⟩⟩,
        have H' := H.2.symm,
        subst H',
        exact (pullback.π₂ i Ui.hom) }
    end } }

variables {B : set (opens X)}

instance basis.site (is_basis : opens.is_basis B) : site B :=
{ coverage :=
  { covers := λ U Us, U.val = ⨆u∈Us, (u:over _).left.val,
    property :=
    begin
      refine λ U V i Us (hUs : _ = _), ⟨_, _, _⟩,
      { rw opens.is_basis_iff_cover at is_basis,
        have foo : ∀ (Vj : opens X) (hVj: ∃ Ui : Us, Vj = Ui.1.left ⊓ V),
          ∃ Ws : set (over V), Vj = ⨆w∈Ws, (w:over _).left :=
          begin
            intros Vj hVj,
            rcases is_basis Vj with ⟨Ws, ⟨Ws_are_basic, hWs⟩⟩,
            sorry
          end,
          sorry },
        sorry,
        sorry
    end } }

end topological_space
