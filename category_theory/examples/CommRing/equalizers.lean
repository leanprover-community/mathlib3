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
    -- This is disgusting, it should all be automatic:
    { one_mem := begin tidy, erw f_property.map_one, erw g_property.map_one, end,
      zero_mem := begin tidy, resetI, erw is_ring_hom.map_zero f_val, erw is_ring_hom.map_zero g_val, end,
      mul_mem := begin tidy, erw f_property.map_mul, erw g_property.map_mul, rw [a_1, a_2], end,
      add_mem := begin tidy, erw f_property.map_add, erw g_property.map_add, rw [a_1, a_2], end,
      neg_mem := begin tidy, resetI, erw is_ring_hom.map_neg f_val, erw is_ring_hom.map_neg g_val, rw a_1, end },
    by apply_instance,
  end }.

@[simp] def CommRing.equalizer_ι {R S : CommRing} (f g : R ⟶ S) : CommRing.equalizer f g ⟶ R :=
{ val := λ x, x.val,
  property := by tidy }

-- Is this kosher? Why isn't it already a simp lemma?
@[simp] lemma subtype.val_simp {α : Type u} {p : α → Prop} (a1 a2 : {x // p x}) : a1 = a2 ↔ a1.val = a2.val := by tidy

@[simp] lemma bundled_hom_coe' 
  {c : Type u → Type v} (hom : ∀{α β : Type u}, c α → c β → (α → β) → Prop)
  [h : concrete_category @hom] {R S : bundled c} (f : R ⟶ S) (r : R) : 
  f r = f.val r := rfl

instance CommRing_has_equalizers : has_equalizers.{v+1 v} CommRing :=
{ fork := λ X Y f g, fork.of_ι (CommRing.equalizer_ι f g) (by tidy),
  is_equalizer := λ X Y f g,
  { lift := λ s : fork f g, ⟨ λ x, ⟨ s.ι x, begin have h := congr_fun (congr_arg subtype.val s.condition) x, exact h, end ⟩,
                   begin
                    -- sorry
                     tidy,
                     erw [is_ring_hom.map_one (s.ι).val], refl,
                     erw [is_ring_hom.map_mul (s.ι).val], refl,
                     erw [is_ring_hom.map_add (s.ι).val], refl
                   end ⟩,
    fac' := 
    begin 
      tidy, 
      cases j, 
      tidy, 
      dsimp [fork.ι], 
      have h := s.w walking_pair_hom.left, 
      replace h := congr_arg subtype.val h,
      replace h := congr_fun h x,
      exact h,
    end,
    uniq' := begin 
    -- sorry,
    tidy, have h := w (walking_pair.zero), tidy, 
    end } }


end category_theory.examples