/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import category_theory.abelian.basic
import category_theory.subobject.limits

/-!
# Essential monomorphisms

-/

noncomputable theory

open category_theory category_theory.limits

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

/-- A monomorphism `f` is called essential if whenever `f ≫ g` is mono, `g` is already mono. -/
@[nolint unused_arguments]
def essential_mono {X Y : C} (f : X ⟶ Y) [mono f] : Prop :=
∀ ⦃Z : C⦄ (g : Y ⟶ Z), mono (f ≫ g) → mono g

lemma essential_mono_iff [abelian C] {X Y : C} (f : X ⟶ Y) [mono f] :
  essential_mono f ↔ ∀ {Z : C} (g : Z ⟶ Y) [mono g], is_zero (pullback f g) → is_zero Z :=
begin
  split,
  { introsI hf Z g hg hfg,
    rw [is_zero.iff_id_eq_zero, ← cancel_mono g, category.id_comp, zero_comp],
    suffices : mono (cokernel.π g), { exactI eq_zero_of_mono_cokernel _ },
    refine hf _ (preadditive.mono_of_cancel_zero _ (λ T t ht, _)),
    rw ← category.assoc at ht,
    obtain ⟨u, ⟨rfl, -⟩⟩ := pullback.lift' _ _ (abelian.mono_lift_comp _ _ ht).symm,
    rw [hfg.eq_zero_of_tgt u, zero_comp] },
  { introsI h Z g hg,
    suffices : is_zero (kernel g), { exact preadditive.mono_of_kernel_iso_zero this.iso_zero },
    refine h (kernel.ι g) ((is_zero.iff_id_eq_zero _).2 _),
    have hfst : (pullback.fst : pullback f (kernel.ι g) ⟶ X) = 0,
    { rw [← cancel_mono (f ≫ g), zero_comp, ← category.assoc, pullback.condition, category.assoc,
        kernel.condition, comp_zero] },
    apply pullback.hom_ext;
    simp only [← cancel_mono (kernel.ι g), ← pullback.condition, hfst, category.id_comp, zero_comp,
      comp_zero] }
end

end category_theory
