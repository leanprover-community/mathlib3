import ring_theory.subring
import tactic.subtype_instance
import category_theory.examples.rings
import category_theory.limits.equalizers

universes u v w

namespace category_theory.examples

open category_theory
open category_theory.limits

variables {α : Type v}

-- TODO should this be in mathlib?
local attribute [extensionality] subtype.eq

def CommRing.equalizer {R S : CommRing.{v}} (f g : R ⟶ S) : CommRing :=
{ α := { r : R | f r = g r },
  str :=
  begin
    haveI h : is_subring { r : R | f r = g r } :=
    -- This is disgusting:
    { one_mem := begin tidy, erw f_property.map_one, erw g_property.map_one, end,
      zero_mem := begin tidy, resetI, erw is_ring_hom.map_zero f_val, erw is_ring_hom.map_zero g_val, end,
      mul_mem := begin tidy, erw f_property.map_mul, erw g_property.map_mul, rw [a_1, a_2], end,
      add_mem := begin tidy, erw f_property.map_add, erw g_property.map_add, rw [a_1, a_2], end,
      neg_mem := begin tidy, resetI, erw is_ring_hom.map_neg f_val, erw is_ring_hom.map_neg g_val, rw a_1, end },
    -- have : ring {r : R | f r = g r}, by subtype_instance,
    -- by subtype_instance,
    sorry, -- by subtype_instance, -- why doesn't this work?
    -- none of the sorries below are solvable until this works, as we won't even know we inherit the ring structure.
  end }.

@[simp] def CommRing.equalizer_ι {R S : CommRing} (f g : R ⟶ S) : CommRing.equalizer f g ⟶ R :=
{ val := λ x, x.val,
  property :=
  begin
    tidy,
    sorry,
    sorry,
    sorry,
  end }

-- Is this kosher? Why isn't it already a simp lemma?
@[simp] lemma subtype.val_simp {α : Type u} {p : α → Prop} (a1 a2 : {x // p x}) : a1 = a2 ↔ a1.val = a2.val := by tidy


instance CommRing_has_equalizers : has_equalizers.{v+1 v} CommRing :=
{ fork := λ X Y f g,
  { X := CommRing.equalizer f g,
    ι := CommRing.equalizer_ι f g },
  is_equalizer := λ X Y f g,
  { lift := λ s, ⟨ λ x, ⟨ s.ι x, begin have h := congr_fun (congr_arg subtype.val s.w) x, exact h, end ⟩,
                   begin
                     tidy,
                     erw [is_ring_hom.map_one (s.ι).val], sorry,
                     erw [is_ring_hom.map_mul (s.ι).val], sorry,
                     erw [is_ring_hom.map_add (s.ι).val], sorry
                   end ⟩,
    uniq' := begin tidy, end } }


end category_theory.examples