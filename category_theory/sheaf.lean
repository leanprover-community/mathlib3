import category_theory.examples.topological_spaces

import category_theory.opposites
import category_theory.yoneda
import category_theory.commas
import category_theory.limits
import category_theory.limits.types
import category_theory.limits.functor_category
import category_theory.full_subcategory

open category_theory.limits

universes u u₁ u₂ u₃ v v₁ v₂ v₃ w w₁ w₂

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

instance : has_pullbacks.{u u} X := has_pullbacks_of_has_limits

instance : has_coproducts.{u u} X := has_coproducts_of_has_colimits

end lattice.complete_lattice

namespace category_theory

def ulift_trivial (V : Type u₁) : ulift.{u₁} V ≅ V := by tidy

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
def over (X : C) := comma (functor.id C) (functor.of_obj.{u v v} X)

def under (X : C) := comma (functor.of_obj X) (functor.id C)

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

def of_map {X Y : C} (f : X ⟶ Y) : of_obj X ⟹ of_obj Y :=
{ app := λ _, f }

@[simp] lemma of_map_id {X : C} : of_map (𝟙 X) = 𝟙 (of_obj X) := rfl

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

end functor

end category_theory

-- ##########################
-- # Proper start of the file

namespace category_theory
open category_theory.limits
variables (X : Type u) [𝒳 : small_category X]
include 𝒳

def presheaf := Xᵒᵖ ⥤ Type u
variables {X}

namespace presheaf

instance : category.{(u+1) u} (presheaf X) := by unfold presheaf; apply_instance
instance : has_limits.{(u+1) u} (presheaf X) := limits.functor_category_has_limits
instance : has_pullbacks.{(u+1) u} (presheaf X) := limits.has_pullbacks_of_has_limits
instance : has_colimits.{(u+1) u} (presheaf X) := limits.functor_category_has_colimits
instance : has_coproducts.{(u+1) u} (presheaf X) := limits.has_coproducts_of_has_colimits
instance : has_coequalizers.{(u+1) u} (presheaf X) := limits.has_coequalizers_of_has_colimits

variables {Y : Type u} [small_category Y] (f : X ⥤ Y)

def comap : presheaf Y ⥤ presheaf X :=
{ obj := λ F, f.op ⋙ F,
  map := λ F G α, whisker_left _ α }

section simp
variable {f}
@[simp] lemma comap_obj (F : presheaf Y) : (comap f).obj F = f.op ⋙ F := rfl
@[simp] lemma comap_map {F G : presheaf Y} (α : F ⟶ G) : (comap f).map α = whisker_left _ α := rfl
end simp

def map : presheaf X ⥤ presheaf Y :=
{ obj := λ F, yoneda.op ⋙ (comap f).op ⋙ yoneda.obj F,
  map := λ F G α, whisker_left _ $ whisker_left _ $ yoneda.map α }

section simp
variable {f}
@[simp] lemma map_obj (F : presheaf X) : (map f).obj F = yoneda.op ⋙ (comap f).op ⋙ yoneda.obj F := rfl
@[simp] lemma map_map {F G : presheaf X} (α : F ⟶ G) : (map f).map α = (whisker_left _ $ whisker_left _ $ yoneda.map α) := rfl
end simp

def unit : functor.id _ ⟶ comap f ⋙ map f :=
{ app := λ F,
  { app := λ U, whisker_left _ ∘
      (nat_iso.app (yoneda_lemma _) (U, F) ≪≫ ulift_trivial _).inv,
    naturality' := λ U₁ U₂ i,
    begin
      ext s V j,
      dsimp [yoneda_lemma, ulift_trivial],
      erw F.map_comp,
      refl
    end },
  naturality' := λ F G α,
  begin
    ext V t U i,
    dsimp [yoneda_lemma, ulift_trivial],
    exact (congr (α.naturality i) (rfl : t = t)).symm,
  end }

def counit : map f ⋙ comap f ⟶ functor.id _ :=
{ app := λ F,
  { app := λ U s, s.app U (𝟙 _),
    naturality' :=  λ U₁ U₂ i,
    begin
      ext s,
      have := (congr (s.naturality i) (rfl : (𝟙 (f.obj U₁)) = _)),
      tidy {trace_result := tt},
    end
     } }

def counit.is_iso [fully_faithful f] : is_iso (counit f) := sorry
-- { inv :=
--   { app := λ F,
--     { app := λ U s,
--       { app := λ V i, (functor.map F $ f.op.preimage i) s,
--         naturality' := λ V₁ V₂ i,
--         begin
--           ext j,
--           have := (congr $ F.map_comp (f.op.preimage j) i) (rfl : s = _),
--           dsimp at *,
--           erw ← this,
--           congr,
--           apply f.op.injectivity,
--           erw [f.op.map_comp, full.witness, full.witness],
--           tidy {trace_result := tt},
--         end },
--       naturality' := λ U₁ U₂ i,
--       begin
--         ext s V j,
--         have := (congr $ F.map_comp i (f.op.preimage j)) (rfl : _ = _),
--         dsimp at *,
--         erw ← this,
--         congr,
--         apply f.injectivity,
--         erw [f.op.map_comp, full.witness, full.witness],
--         tidy {trace_result := tt},
--       end },
--     naturality' := λ F G α,
--     begin
--       ext U s V j,
--       have := (congr $ α.naturality (f.op.preimage j)) rfl,
--       tidy {trace_result := tt},
--     end },
--   hom_inv_id' :=
--   begin
--     ext F U s V i,
--     tidy {trace_result := tt},
--     dsimp [counit],
--     have := (congr $ (s.naturality (f.op.preimage i))) rfl,
--     dsimp at this,
--     erw ← this,
--     tidy {trace_result := tt},
--     erw full.witness,
--   end,
--   inv_hom_id' :=
--   begin
--     ext F U s,
--     tidy {trace_result := tt},
--     dsimp [counit],
--     erw functor.preimage_id,
--     erw F.map_id,
--     tidy {trace_result := tt},
--   end, }

-- -- This needs essential surjectivity
-- noncomputable def unit.inv (h : function.surjective f.obj) : comap f ⋙ map f ⟶ functor.id _ :=
-- { app := λ F,
--   { app := λ U s,
--     begin
--       choose V hV using h U,
--       induction hV,
--       have := s.app V,
--       tidy {trace_result := tt},
--       exact this (𝟙 _)
--     end,
--     naturality' := λ U₁ U₂ i,
--     begin
--       tidy {trace_result := tt},
--       sorry
--     end } }

end presheaf

@[reducible]
def covering_family (U : X) : Type u := set (over.{u u} U)

namespace covering_family

variables {U : X} (c : covering_family U)

def sieve : presheaf X :=
let
  y (Ui : c) := yoneda.map Ui.val.hom,
  pb (Ujk : c × c) : presheaf X := limits.pullback (y Ujk.1) (y Ujk.2),
  re (Ui : c) : presheaf X := yoneda.obj Ui.val.left,
  left  : limits.sigma pb ⟶ limits.sigma re :=
    sigma.desc $ λ Ujk : c × c, pullback.π₁ (y Ujk.1) (y Ujk.2) ≫ sigma.ι re Ujk.1,
  right : limits.sigma pb ⟶ limits.sigma re :=
    sigma.desc $ λ Ujk : c × c, pullback.π₂ (y Ujk.1) (y Ujk.2) ≫ sigma.ι re Ujk.2
in coequalizer left right

def π : c.sieve ⟶ yoneda.obj U :=
coequalizer.desc _ _ (sigma.desc $ λ Ui, yoneda.map Ui.val.hom)
begin
  ext1, dsimp at *,
  rw ←category.assoc,
  rw ←category.assoc,
  simp,
end

def sheaf_condition (F : presheaf X) := is_iso $ (yoneda.obj F).map c.π

example {F : presheaf X} (h : c.sheaf_condition F) : true :=
begin
  let A := iso_of_is_iso h,
  let B := A,
  dsimp at B,
  let C := (nat_iso.app (yoneda_lemma _) (U, F) ≪≫ ulift_trivial _).symm ≪≫ B,
  dsimp at C,
  let D := C ≪≫ (coequalizer.hom_equiv _ _),
  dsimp at D,
  let Et := limits.sigma (λ (Ui : {x // x ∈ c}), yoneda.obj ((Ui.val).left)) ⟶ F,
  clear D,
  let E := iso.refl Et ≪≫ colimit.hom_equiv' _,
  have := @equiv.subtype_equiv_of_subtype,
  tauto
end

variables {Y : Type u} [small_category Y]
variables (F : X ⥤ Y)

def map {U : X} (c : covering_family U) : covering_family (F.obj U) :=
(over.post F).obj '' c

end covering_family

variable (X)
structure coverage :=
(covers   : Π (U : X), set (covering_family U))
(property : ∀ {U V : X} (g : V ⟶ U),
            ∀ f ∈ covers U, ∃ h ∈ covers V,
            ∀ Vj ∈ (h : set _), ∃ (Ui ∈ f),
            nonempty $ ((over.map g).obj Vj) ⟶ Ui)

end category_theory

namespace category_theory

class site (X : Type u) extends category.{u u} X :=
(coverage : coverage X)

namespace site

section covers_and_sheaf_condition
variables {X : Type u} [𝒳 : site X]
include 𝒳

definition covers (U : X) := 𝒳.coverage.covers U

def sheaf_condition (F : presheaf X) :=
∀ {U : X}, ∀c ∈ covers U, (c : covering_family U).sheaf_condition F

end covers_and_sheaf_condition

section examples
variables (X : Type u) [small_category X]

def trivial : site X :=
{ coverage :=
  { covers := λ U Us, false,
    property := λ U V g f hf, false.elim hf } }

def discrete : site X :=
{ coverage :=
  { covers := λ U Us, true,
    property := λ U V g f _,
      ⟨{Vj | false}, by simp, (λ Vj hVj, false.elim hVj)⟩ } }

end examples

end site

-- TODO turn this into a sigma_category once that is in mathlib
def sheaf (X : Type u) [𝒳 : site X] :=
{ F : presheaf X // nonempty (site.sheaf_condition F) }

instance sheaf_category (X : Type u) [𝒳 : site X] : category (sheaf X) := category_theory.full_subcategory _

namespace functor
open site

variables {X : Type u} [site X]
variables {Y : Type u} [site Y]

def preserves_covers (f : X ⥤ Y) :=
∀ {U : X}, ∀ c ∈ covers U, covering_family.map f c ∈ (covers $ f.obj U)

end functor

namespace site
variables {X : Type u} [site X]
variables {Y : Type u} [site Y]

lemma sheaf_condition_comap {f : X ⥤ Y} (hf : f.preserves_covers)
{F : presheaf Y} (hF : sheaf_condition F) :
sheaf_condition $ (presheaf.comap f).obj F := λ U c hc,
begin
  constructor,
  intro s,
  apply (nat_iso.app (yoneda_lemma _) (U, (presheaf.comap f).obj F) ≪≫ ulift_trivial _).inv,
  apply (nat_iso.app (yoneda_lemma _) (f.obj U, F) ≪≫ ulift_trivial _).hom,
  apply (hF (covering_family.map f c) (hf c hc)).inv,
  dsimp at *,
  constructor,
  intro V,
  have := s.app U,
  dsimp [covering_family.map, over.post],
  dsimp at *,
end

end site

end category_theory

namespace topological_space
open category_theory
local attribute [instance] classical.prop_decidable

variables {X : Type u} [topological_space X]

instance : site (opens X) :=
{ coverage :=
  { covers := λ U Us, U = ⨆u∈Us, (u:over _).left,
    property := λ U V (i : V ⟶ U) (Us : covering_family U) (Us_cover : U = ⨆u∈Us, (u:over _).left),
    begin sorry
      -- refine ⟨ (over.comap i).obj '' Us, _, _⟩,
      -- { show _ = _,
      --   rw [lattice.supr_image],
      --   apply le_antisymm,
      --   { show V.val ≤ (⨆ (Ui : over U) (H : Ui ∈ Us), ((over.comap i).obj Ui).left).val,
      --     intros x x_in_V,
      --     have := plift.down (ulift.down i) x_in_V,
      --     erw [Us_cover, set.mem_bUnion_iff] at this,
      --     rcases this with ⟨Ui, ⟨H, x_in_Ui⟩⟩,
      --     erw set.mem_bUnion_iff,
      --     show ∃ (W : opens X), (∃ Ui : over U, _) ∧ _,
      --     cases H with Ui' hUi',
      --     existsi ((over.comap i).obj Ui').left,
      --     split,
      --     { dsimp at hUi' ⊢,
      --       change opens X at Ui,
      --       existsi Ui',
      --       symmetry,
      --       apply supr_pos,
      --       by_contra,
      --       rw supr_neg a at hUi',
      --       subst hUi',
      --       assumption },
      --     fsplit,
      --     exact V.val ∩ Ui.val,
      --     have := is_open_inter _ _ _ V.2 Ui.2,
      --     fsplit, swap, {tidy},
      --     fsplit, {tidy},
      --     intros y hy,
      --     cases hy,
      --     erw set.mem_bInter_iff,
      --     intros W hW,
      --     change ∃ _, _ = _ at hW,
      --     cases hW with T hT,
      --     cases T; subst hT; dsimp; tidy,
      --     dsimp [infi,Inf,has_Inf.Inf,order_dual,complete_lattice.Inf] at h_2,
      --     rw h_2 at hy_right,
      --     tidy,
      --     rw hy_right_h_w_h at hy_right_h_h, simp * at *,
      --     cases hy_right_h_h, tidy,
      --     rw ← hy_right_h_h_h_w_left_right,
      --     assumption },
      --   { refine supr_le _,
      --     intro Ui,
      --     refine supr_le _,
      --     intro hUi,
      --     exact plift.down (ulift.down (pullback.π₁ i Ui.hom)), } },
      -- { rintros Vj ⟨Ui, H⟩,
      --   refine ⟨Ui, H.1, _⟩,
      --   have H' := H.2.symm,
      --   subst H',
      --   exact ⟨ { left := pullback.π₂ i Ui.hom } ⟩ }
    end } }

@[simp] lemma opens.mem_covers {U : opens X} (c : covering_family U) :
c ∈ site.covers U ↔ U = ⨆u∈c, (u:over _).left := ⟨id, id⟩

variables {B : set (opens X)}

instance basis.site (is_basis : opens.is_basis B) : site B :=
{ coverage :=
  { covers := λ U Us, U.val = ⨆u∈Us, (u:over _).left.val,
    property := λ U V (i : V ⟶ U) (Us : covering_family U) (Us_cover : U.val = ⨆ Ui ∈ Us, ((Ui : over _).left).val),
      ⟨ show covering_family V,
          from { Vj : over V | ∃ Ui ∈ Us, nonempty $ ((over.map i).obj Vj) ⟶ Ui },
        show V.val = ⨆ (Vj : over V) (hVj : ∃ Ui ∈ Us, nonempty $ ((over.map i).obj Vj) ⟶ Ui), Vj.left.val,
          from begin sorry
            -- apply le_antisymm,
            -- { intros x x_in_V,
            --   have := plift.down (ulift.down i) x_in_V,
            --   erw [Us_cover, set.mem_bUnion_iff] at this,
            --   rcases this with ⟨Ui, ⟨H, x_in_Ui⟩⟩,
            --   erw set.mem_bUnion_iff,
            --   change ∃ Vj' : opens X, ((∃ Vj : over V, Vj' = ⨆ _, _) ∧ _),
            --   change opens X at Ui,
            --   have x_in_W : @has_mem.mem _ (opens X) _ x (⟨_, is_open_inter _ _ _ Ui.2 V.val.2⟩) := by tidy,
            --   rw opens.is_basis_iff_nbhd at is_basis,
            --   cases is_basis x_in_W,
            --   existsi w,
            --   rcases h with ⟨h1, ⟨h2, h3⟩⟩,
            --   split, swap, assumption,
            --   fsplit,
            --   refine {left := ⟨_,h1⟩, hom := ⟨⟨_⟩⟩},
            --   dsimp,
            --   have w_subset : w.val ⊆ Ui.val ∩ V.val.val := by tidy,
            --   show _ ⊆ _,
            --   exact set.subset.trans w_subset (set.inter_subset_right Ui.val V.val.val),
            --   dsimp [over.map],
            --   cases H with Ui' hUi',
            --   have foo : w ⟶ (Ui'.left).val :=
            --   begin
            --     refine ⟨⟨_⟩⟩,
            --     show w ≤ Ui'.left,
            --     change w ≤ _ at h3,
            --     apply le_trans h3,
            --     change _ ⊆ Ui'.left.val,
            --     refine set.subset.trans (set.inter_subset_left _ _) _,
            --     intros y hy,
            --     cases hUi',
            --     cases hy, cases hy_h, cases hy_h_w, cases hy_h_w_h,
            --     dsimp * at *,
            --     cases hy_h_h, cases hy_h_h_h, cases hy_h_h_h_w,
            --     cases hy_h_h_h_w_w,
            --     rw [hy_h_h_h_w_h,hy_h_h_h_w_w_h] at hy_h_h_h_h,
            --     assumption
            --   end,
            --   symmetry,
            --   apply supr_pos,
            --   existsi Ui',
            --   change Ui = ⨆ _,_ at hUi',
            --   cases hUi',
            --   dsimp at *,
            --   fsplit,
            --   { cases x_in_Ui, cases x_in_Ui_h, cases x_in_Ui_h_w, cases x_in_Ui_h_w_h, cases x_in_Ui_h_h,
            --     cases x_in_Ui_h_h_h, cases x_in_Ui_h_h_h_w, cases x_in_Ui_h_h_h_w_w,
            --     assumption },
            --   dsimp [over.mk],
            --   refine ⟨{left := _, w' := _}⟩; dsimp,
            --   exact foo,
            --   congr,
            --   exact foo,
            --   exact Ui'.hom },
            -- { refine supr_le _,
            --   intro Vj,
            --   refine supr_le _,
            --   intro hVj,
            --   show Vj.left.val ≤ V.val,
            --   exact plift.down (ulift.down Vj.hom), }
          end,
        -- show ∀ (Vj : over V), Vj ∈ {Vj : over V | _ } → _,
          by obviously
      ⟩ } }

variable (X)
def presheaf := presheaf (opens X)
def sheaf    := sheaf    (opens X)
variable {X}
instance presheaf.category : category (presheaf X) := by unfold presheaf; apply_instance
instance sheaf.category    : category (sheaf X)    := by unfold sheaf; apply_instance

variable (B)
def restrict : presheaf X ⥤ category_theory.presheaf B :=
category_theory.presheaf.comap (full_subcategory_inclusion B)
variable {B}

def extend : category_theory.presheaf B ⥤ presheaf X :=
category_theory.presheaf.map (full_subcategory_inclusion B)

lemma extend_restrict : extend ⋙ (restrict B) ≅ functor.id _ :=
iso_of_is_iso $ presheaf.counit.is_iso (full_subcategory_inclusion B)

lemma basis_inclusion_preserves_covers (is_basis : opens.is_basis B) :
@functor.preserves_covers _ (basis.site is_basis) _ _ (full_subcategory_inclusion B) :=
λ U c hc,
begin
  simp, sorry
end

lemma sheaf_condition_iff {is_basis : opens.is_basis B} {F : category_theory.presheaf B} :
@site.sheaf_condition.{u} _ (basis.site is_basis) F ≃ site.sheaf_condition (extend.obj F) :=
{ to_fun := λ h U c hc, _,
  inv_fun := λ h U c hc,
  let foo := h (covering_family.map (full_subcategory_inclusion B) c) $
    (basis_inclusion_preserves_covers is_basis) _ hc
  in
  begin
    dsimp only [covering_family.sheaf_condition, extend] at *,
    erw [presheaf.map_obj] at foo,
  end
  }

namespace opens

open lattice
open category_theory
open category_theory.examples

instance : has_colimits.{u u} (opens X) := by apply_instance

-- This should be generalised to arbitrary diagrams
def colim_is_supr {U : opens X} {Us : covering_family U} :
colimit (functor.of_function (λ u : Us, u.val.left)) = ⨆ u ∈ Us, (u : over _).left := supr_subtype

def to_Top : opens X ⥤ Top :=
{ obj := λ U,
          { α := U.val,
            str := subtype.topological_space },
  map := λ U V i, ⟨λ x, ⟨x.1, (plift.down (ulift.down i)) x.2⟩,
    (embedding.continuous_iff embedding_subtype_val).mpr continuous_subtype_val ⟩ }

def to_Top.preserves_colimits : preserves_colimits (@to_Top X _) :=
{ preserves := λ J _ K c hc,
  { desc := λ s,
    begin
      fsplit,
      dsimp [functor.map_cocone, to_Top],
      rintros ⟨x,hx⟩,
    end } }

end opens

section ctu_func

open category_theory.examples

variables (X)

#print covering_family.sieve

def sheaf_of_functions (T : Top) : sheaf X :=
{ val := opens.to_Top.op ⋙ (yoneda.obj T),
  property :=
  begin
    refine ⟨_⟩,
    intros U Us hUs,
    constructor,
    dsimp,
    intro fs,
    constructor,
    intros V,
    dsimp,
    intro i,
    suffices : opens.to_Top.obj U ⟶ T,
    exact opens.to_Top.map i ≫ this,
    change U = _ at hUs,
    rw hUs,
    have : Πu ∈ Us, opens.to_Top.obj (u : over _).left ⟶ T,
    { intros u hu,
      suffices : yoneda.obj u.left ⟶ Us.sieve,
      { exact (this ≫ fs).app u.left (𝟙 u.left) },
      refine _ ≫ (coequalizer.π _ _),
      exact (sigma.ι (λ (Ui : {x // x ∈ Us}), yoneda.obj ((Ui.val).left)) ⟨u, hu⟩) },
    rw ← opens.colim_is_supr,
  end }



end ctu_func

end topological_space
