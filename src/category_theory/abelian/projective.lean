/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison, Jakob von Raumer
-/
import algebra.homology.quasi_iso
import category_theory.abelian.exact
import category_theory.abelian.homology
import category_theory.preadditive.projective
import category_theory.preadditive.projective_resolution

/-!
# Abelian categories with enough projectives have projective resolutions

When `C` is abelian `projective.d f` and `f` are exact.
Hence, starting from an epimorphism `P ⟶ X`, where `P` is projective,
we can apply `projective.d` repeatedly to obtain a projective resolution of `X`.
-/

noncomputable theory

open category_theory
open category_theory.limits
open opposite

universes v u v' u'

namespace category_theory

open category_theory.projective

variables {C : Type u} [category.{v} C] [abelian C]

/--
When `C` is abelian, `projective.d f` and `f` are exact.
-/
lemma exact_d_f [enough_projectives C] {X Y : C} (f : X ⟶ Y) : exact (d f) f :=
(abelian.exact_iff _ _).2 $
  ⟨by simp, zero_of_epi_comp (π _) $ by rw [←category.assoc, cokernel.condition]⟩

/-- The preadditive Co-Yoneda functor on `P` preserves colimits if `P` is projective. -/
def preserves_finite_colimits_preadditive_coyoneda_obj_of_projective (P : C)
  [hP : projective P] : preserves_finite_colimits (preadditive_coyoneda_obj (op P)) :=
begin
  letI := (projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj' P).mp hP,
  apply functor.preserves_finite_colimits_of_preserves_epis_and_kernels,
end

/-- An object is projective if its preadditive Co-Yoneda functor preserves finite colimits. -/
lemma projective_of_preserves_finite_colimits_preadditive_coyoneda_obj (P : C)
  [hP : preserves_finite_colimits (preadditive_coyoneda_obj (op P))] : projective P :=
begin
  rw projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj',
  apply_instance
end

namespace ProjectiveResolution

/-!
Our goal is to define `ProjectiveResolution.of Z : ProjectiveResolution Z`.
The `0`-th object in this resolution will just be `projective.over Z`,
i.e. an arbitrarily chosen projective object with a map to `Z`.
After that, we build the `n+1`-st object as `projective.syzygies`
applied to the previously constructed morphism,
and the map to the `n`-th object as `projective.d`.
-/
variables [enough_projectives C]

/-- Auxiliary definition for `ProjectiveResolution.of`. -/
@[simps]
def of_complex (Z : C) : chain_complex C ℕ :=
chain_complex.mk'
  (projective.over Z) (projective.syzygies (projective.π Z)) (projective.d (projective.π Z))
  (λ ⟨X, Y, f⟩, ⟨projective.syzygies f, projective.d f, (exact_d_f f).w⟩)

/--
In any abelian category with enough projectives,
`ProjectiveResolution.of Z` constructs a projective resolution of the object `Z`.
-/
@[irreducible] def of (Z : C) : ProjectiveResolution Z :=
{ complex := of_complex Z,
  π := chain_complex.mk_hom _ _ (projective.π Z) 0
    (by { simp, exact (exact_d_f (projective.π Z)).w.symm, })
    (λ n _, ⟨0, by ext⟩),
  projective := by { rintros (_|_|_|n); apply projective.projective_over, },
  exact₀ := by simpa using exact_d_f (projective.π Z),
  exact := by { rintros (_|n); { simp, apply exact_d_f, }, },
  epi := projective.π_epi Z, }

@[priority 100]
instance (Z : C) : has_projective_resolution Z :=
{ out := ⟨of Z⟩ }

@[priority 100]
instance : has_projective_resolutions C :=
{ out := λ Z, by apply_instance }

end ProjectiveResolution

/-- An equivalence of abelian categories maps projective resolutions to projective resolutions. -/
def equivalence.map_ProjectiveResolution {D : Type*} [category D] [abelian D] (F : C ≌ D)
  [F.functor.additive] (X : C) (P : ProjectiveResolution X) :
  ProjectiveResolution (F.functor.obj X) :=
{ complex := (F.functor.map_homological_complex _).obj P.complex,
  π := (F.functor.map_homological_complex _).map P.π ≫
    ((chain_complex.single₀_map_homological_complex F.functor).app X).hom,
  projective := λ n, (F.map_projective_iff (P.1.X n)).2 (P.3 n),
  exact₀ :=
  begin
    show exact (F.functor.map _) (F.functor.map _ ≫ 𝟙 _),
    rw category.comp_id,
    haveI := @preserves_colimits.preserves_finite_colimits
      _ _ _ _ F.functor (adjunction.is_equivalence_preserves_colimits _),
    exact F.functor.map_exact _ _ P.4,
  end,
  exact := λ n,
  begin
    haveI := @preserves_colimits.preserves_finite_colimits
      _ _ _ _ F.functor (adjunction.is_equivalence_preserves_colimits _),
    exact F.functor.map_exact _ _ (P.5 n),
  end,
  epi :=
  begin
    show epi (F.functor.map _ ≫ 𝟙 _),
    rw category.comp_id,
    apply_instance,
  end }

end category_theory
