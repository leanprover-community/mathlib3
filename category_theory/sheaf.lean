-- Copyright (c) 2018 Johan Commelin. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Johan Commelin

import category_theory.presheaf
import category_theory.comma

namespace category_theory
open category_theory
open category_theory.limits

universes u v

-- TODO: How much of this should be generalized to a possibly large category?
variables {X : Type u} [small_category X]

@[reducible]
def covering_family (U : X) : Type u := set (over.{u u} U)

instance covering_family.has_mem (U : X) :
  has_mem (over U) (covering_family U) :=
by delta covering_family; apply_instance

def covering_family.is_sieve {U : X} (c : covering_family U) : Prop :=
∀ (Ui : c) (V : X) (f : V ⟶ Ui.val.left), over.mk (f ≫ Ui.val.hom) ∈ c

structure sieve (U : X) : Type u :=
(covering_family : covering_family U)
(is_sieve : covering_family.is_sieve)

namespace sieve
variables {U : X}

def to_presheaf (S : sieve U) : presheaf X :=
{ obj := λ V, { f : V ⟶ U // S.covering_family (over.mk f) },
  map := λ V₁ V₂ f g,
  begin
    cases g with g hg,
    split,
    change V₂ ⟶ V₁ at f,
    use over.mk (f ≫ g),
  end  }

end sieve

namespace covering_family
variables {U : X}

def sieve (c : covering_family U) : presheaf X :=
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
variables {Y : Type u} [small_category Y]
variables (f : X ⥤ Y)

def map {U : X} (c : covering_family U) : covering_family (f.obj U) :=
(over.post f).obj '' c

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
  -- dsimp [covering_family.map, over.post],
  dsimp at *,
  intro,
  have foo := (covering_family.π (covering_family.map f c)),
  change _ ⟹ _ at foo,
  have bar := foo.app V a,
  dsimp at bar,
  apply functor.map F bar,
  apply this,
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