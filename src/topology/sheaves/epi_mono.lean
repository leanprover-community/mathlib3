/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import topology.sheaves.sheaf
import category_theory.sites.sheafification

/-!
# Epimorphisms and monomorphisms in category of (pre)sheaves

Let `X` be a topological space and `F, G` be sheaves on `X`. Then `f : F ⟶ G` is monic iff it is
monic as presheaf morphisms; `f` is epic if `f` is epic as presheaf morphism, but in this case, the
converse is **not** necessarily true.

-/


universes v u

open category_theory category_theory.limits
open topological_space
open Top


variables {X : Top.{v}} {D : Type u} [category.{v u} D]

section sheaf

variables {F G : sheaf D X} (f : F ⟶ G)

instance mono_of_presheaf_mono [mono f.1] : mono f :=
{ right_cancellation := λ P g h eq₀, Sheaf.hom.ext _ _ $ (cancel_mono f.1).mp $
    (Sheaf.hom.ext_iff _ _).mp eq₀ }

instance sheaf.forget_reflects_mono : (sheaf.forget D X).reflects_monomorphisms :=
{ reflects := λ F G f m, @@mono_of_presheaf_mono _ f m }

instance epi_of_presheaf_epi [epi f.1] : epi f :=
{ left_cancellation := λ P g h eq₀, Sheaf.hom.ext _ _ $ (cancel_epi f.1).mp $
    (Sheaf.hom.ext_iff _ _).mp eq₀ }

instance sheaf_forget_reflects_epi : (sheaf.forget D X).reflects_epimorphisms :=
{ reflects := λ F G f m, @@epi_of_presheaf_epi _ f m }

section to_presheaf

/-!
Given two sheaves `F, G` on `X` in a cocomplete concrete category `D` where "sheafification" is
possible, then a monic sheaf morphism `f : F ⟶ G` is also a monic presheaf morphism.
-/

-- assumptions on target category so that "sheafification" is possible
variables [concrete_category.{v} D] [preserves_limits (forget D)] [has_colimits D]
variables [Π (P : presheaf D X) (U : opens X) (S : (opens.grothendieck_topology X).cover U),
  has_multiequalizer (S.index P)]
variables [Π (U : opens X),
    preserves_colimits_of_shape ((opens.grothendieck_topology X).cover U)ᵒᵖ (forget D)]
variables [reflects_isomorphisms (forget D)]

instance presheaf_mono_of_mono [mono f] : mono f.1 :=
{ right_cancellation := λ P g h eq₀,
  begin
    set P_plus : sheaf D X := (presheaf_to_Sheaf (opens.grothendieck_topology X) D).obj P,
    set g_plus : P_plus ⟶ F :=
      ⟨grothendieck_topology.sheafify_lift (opens.grothendieck_topology X) g F.2⟩ with g_plus_def,
    set h_plus : P_plus ⟶ F :=
      ⟨grothendieck_topology.sheafify_lift (opens.grothendieck_topology X) h F.2⟩ with h_plus_def,
    have eq₁ : g_plus ≫ f = h_plus ≫ f := Sheaf.hom.ext _ _ (grothendieck_topology.sheafify_hom_ext
      _ _ _ G.2 (by simp [*])),
    have eq₂ : g_plus = h_plus,
    { rwa cancel_mono at eq₁, },
    rw [g_plus_def, h_plus_def, Sheaf.hom.ext_iff] at eq₂,
    dsimp at eq₂,
    rw ←grothendieck_topology.to_sheafify_sheafify_lift (opens.grothendieck_topology X) g F.2,
    rw ←grothendieck_topology.to_sheafify_sheafify_lift (opens.grothendieck_topology X) h F.2,
    rw eq₂,
  end }

instance sheaf.forget_preserves_mono : (sheaf.forget D X).preserves_monomorphisms :=
{ preserves := λ F G f m, @presheaf_mono_of_mono X D _ F G f _ _ _ _ _ _ m }

lemma sheaf.mono_iff_presheaf_mono : mono f ↔ mono f.1 :=
⟨λ m, @@presheaf_mono_of_mono _ f _ _ _ _ _ _ m, λ m, @@mono_of_presheaf_mono _ f m⟩

/-
This is not always true
```
instance presheaf_epi_of_epi [epi f] : epi f.1 := not true
```
-/

end to_presheaf

end sheaf
