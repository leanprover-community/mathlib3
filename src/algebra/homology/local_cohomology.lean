/-
Copyright (c) 2023 Emily Witt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Witt, Scott Morrison
-/
import ring_theory.ideal.basic
import algebra.category.Module.colimits
import algebra.category.Module.projective
import category_theory.abelian.ext
import category_theory.limits.final

/-!
# Local cohomology.

We just give one definition, deferring for later the other equivalent definitions,
and basic properties.
-/

open opposite
open category_theory
open category_theory.limits

noncomputable theory

section local_cohomology

variables (R : Type) [comm_ring R]

variables {D : Type} [category.{0} D] (I : Dᵒᵖ ⥤ ideal R)

local attribute [ext] quiver.hom.unop_inj

def ring_mod_ideals : D ⥤ (Module.{0} R)ᵒᵖ :=
{
  obj := λ t, op $ Module.of R $ R ⧸ (I.obj (op t)),
  map := λ s t w, quiver.hom.op $
    submodule.mapq (I.obj (op t)) (I.obj (op s)) (linear_map.id)
    $ (I.map w.op).down.down
}

/-- The diagram we will take the colimit of to define local cohomology -/
def local_cohomology_diagram (i : ℕ) :
   D ⥤ Module.{0} R ⥤ Module.{0} R :=
ring_mod_ideals R I ⋙ Ext R (Module.{0} R) i

def local_cohomology_ideals (i : ℕ) : Module.{0} R ⥤ Module.{0} R :=
colimit (local_cohomology_diagram R I i)

def ideal_powers (J : ideal R) : ℕᵒᵖ ⥤ ideal R := {
  obj := λ t, J^(unop t),
  map := λ s t w, ⟨⟨ideal.pow_le_pow w.unop.down.down⟩⟩,
}

def local_cohomology_powers (J : ideal R) :=
  local_cohomology_ideals R (ideal_powers R J)

end local_cohomology

section cofinal

variables {E ι : Type} [category.{0} E]
  {D : ι → Type} [∀ i, category.{0} (D i)] (I : Π (i : ι), D i ⥤ E)

def train_tracks (I : Π (i : ι), D i ⥤ E) : Type :=
  induced_category E (λ x : Σ i, D i, (I x.1).obj x.2)

instance : category (train_tracks I) := begin
  dsimp [train_tracks],
  apply_instance,
end

namespace train_tracks

def inclusion (i) : D i ⥤ train_tracks I := {
  obj := λ x, ⟨i, x⟩,
  map := λ x y f, (I i).map f,
}

end train_tracks
end cofinal


section

variables {D E : Type} [category.{0} D] [category.{0} E]
  (F : D ⥤ E) [is_filtered D] [quiver.is_thin E]

lemma foo (e : E) (w : ∀ e, ∃ d, nonempty(e ⟶ F.obj d)) : nonempty (structured_arrow e F) :=
sorry

def bar (X : Type) [category X] (x1 x2 y : X) (f : x1 ⟶ y) (g : x2 ⟶ y) : zigzag x1 x2 :=
sorry

lemma final_of_filtered_of_thin_of_exists (w : ∀ e, ∃ d, nonempty(e ⟶ F.obj d)) : F.final :=
{ out := λ e, @zigzag_is_connected _ _ (foo _ e w) begin
  -- rintros ⟨p, d1, f1 : e ⟶ _⟩ ⟨p', d2, f2 : e ⟶ _⟩,
  intros j1 j2,
  have f := is_filtered.left_to_max j1.right j2.right,
  have g := is_filtered.right_to_max j1.right j2.right,
  apply bar _ _ _ (structured_arrow.mk _),
  show D,
  exact (is_filtered.max j1.right j2.right),
  show e ⟶ _,
  exact j1.hom ≫ F.map f,
  -- apply bar (is_filtered.max j1.right j2.right),
  fapply structured_arrow.hom_mk,

  exact f,
  apply subsingleton.elim,
  fapply structured_arrow.hom_mk,

  exact g,
  apply subsingleton.elim,
end,
}


end






--   obj := λ t, I^(unop t),
--   map := λ s t w, begin
--     have := ideal.pow_le_pow w.unop.down.down,
--   end
-- }

end
-- def local_cohomology_diagram' (I )
