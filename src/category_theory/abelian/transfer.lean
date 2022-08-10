/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Jujian Zhang
-/
import category_theory.preadditive.additive_functor
import category_theory.abelian.basic
import category_theory.limits.preserves.shapes.kernels
import category_theory.adjunction.limits
import category_theory.abelian.exact
import category_theory.preadditive.injective
import category_theory.adjunction.limits

/-!
# Transferring categorical properties across a functor

## Transfering "abelian-ness" across a functor
If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.

See <https://stacks.math.columbia.edu/tag/03A3>

## Transfering "enough-injectiveness" across a functor
If `𝓐, 𝓑` are abelian categories and `L ⊣ R` is a pair of adjoint functors such that `L` is
faithful and exact (that is, preserves finite limits and colimits), then enough injectiveness of
`𝓑` implies enough injectiveness of `𝓐`.

## Notes
The hypotheses, following the statement from the Stacks project,
may appear suprising: we don't ask that the counit of the adjunction is an isomorphism,
but just that we have some potentially unrelated isomorphism `i : F ⋙ G ≅ 𝟭 C`.

However Lemma A1.1.1 from [Elephant] shows that in this situation the counit itself
must be an isomorphism, and thus that `C` is a reflective subcategory of `D`.

Someone may like to formalize that lemma, and restate this theorem in terms of `reflective`.
(That lemma has a nice string diagrammatic proof that holds in any bicategory.)
-/

noncomputable theory

namespace category_theory
open category_theory.limits

universes v u₁ u₂

namespace abelian_of_adjunction

variables {C : Type u₁} [category.{v} C] [preadditive C]
variables {D : Type u₂} [category.{v} D] [abelian D]
variables (F : C ⥤ D)
variables (G : D ⥤ C) [functor.preserves_zero_morphisms G]
variables (i : F ⋙ G ≅ 𝟭 C) (adj : G ⊣ F)

include i

/-- No point making this an instance, as it requires `i`. -/
lemma has_kernels [preserves_finite_limits G] : has_kernels C :=
{ has_limit := λ X Y f, begin
    have := nat_iso.naturality_1 i f,
    simp at this,
    rw ←this,
    haveI : has_kernel (G.map (F.map f) ≫ i.hom.app _) := limits.has_kernel_comp_mono _ _,
    apply limits.has_kernel_iso_comp,
  end }

include adj

/-- No point making this an instance, as it requires `i` and `adj`. -/
lemma has_cokernels : has_cokernels C :=
{ has_colimit := λ X Y f, begin
    haveI : preserves_colimits G := adj.left_adjoint_preserves_colimits,
    have := nat_iso.naturality_1 i f,
    simp at this,
    rw ←this,
    haveI : has_cokernel (G.map (F.map f) ≫ i.hom.app _) := limits.has_cokernel_comp_iso _ _,
    apply limits.has_cokernel_epi_comp,
  end }

variables [limits.has_cokernels C]

/-- Auxiliary construction for `coimage_iso_image` -/
def cokernel_iso {X Y : C} (f : X ⟶ Y) : G.obj (cokernel (F.map f)) ≅ cokernel f :=
begin
  -- We have to write an explicit `preserves_colimits` type here,
  -- as `left_adjoint_preserves_colimits` has universe variables.
  haveI : preserves_colimits G := adj.left_adjoint_preserves_colimits,
  calc G.obj (cokernel (F.map f))
      ≅ cokernel (G.map (F.map f)) : (as_iso (cokernel_comparison _ G)).symm
  ... ≅ cokernel (_ ≫ f ≫ _)       : cokernel_iso_of_eq (nat_iso.naturality_2 i f).symm
  ... ≅ cokernel (f ≫ _)           : cokernel_epi_comp _ _
  ... ≅ cokernel f                 : cokernel_comp_is_iso _ _
end

variables [limits.has_kernels C] [preserves_finite_limits G]

/-- Auxiliary construction for `coimage_iso_image` -/
def coimage_iso_image_aux {X Y : C} (f : X ⟶ Y) :
  kernel (G.map (cokernel.π (F.map f))) ≅ kernel (cokernel.π f) :=
begin
  haveI : preserves_colimits G := adj.left_adjoint_preserves_colimits,
  calc kernel (G.map (cokernel.π (F.map f)))
      ≅ kernel (cokernel.π (G.map (F.map f)) ≫ cokernel_comparison (F.map f) G)
          : kernel_iso_of_eq (π_comp_cokernel_comparison _ _).symm
  ... ≅ kernel (cokernel.π (G.map (F.map f))) : kernel_comp_mono _ _
  ... ≅ kernel (cokernel.π (_ ≫ f ≫ _) ≫ (cokernel_iso_of_eq _).hom)
          : kernel_iso_of_eq (π_comp_cokernel_iso_of_eq_hom (nat_iso.naturality_2 i f)).symm
  ... ≅ kernel (cokernel.π (_ ≫ f ≫ _))       : kernel_comp_mono _ _
  ... ≅ kernel (cokernel.π (f ≫ i.inv.app Y) ≫ (cokernel_epi_comp (i.hom.app X) _).inv)
          : kernel_iso_of_eq (by simp only [cokernel.π_desc, cokernel_epi_comp_inv])
  ... ≅ kernel (cokernel.π (f ≫ _))           : kernel_comp_mono _ _
  ... ≅ kernel (inv (i.inv.app Y) ≫ cokernel.π f ≫ (cokernel_comp_is_iso f (i.inv.app Y)).inv)
          : kernel_iso_of_eq (by simp only [cokernel.π_desc, cokernel_comp_is_iso_inv,
              iso.hom_inv_id_app_assoc, nat_iso.inv_inv_app])
  ... ≅ kernel (cokernel.π f ≫ _)             : kernel_is_iso_comp _ _
  ... ≅ kernel (cokernel.π f)                 : kernel_comp_mono _ _
end

variables [functor.preserves_zero_morphisms F]

/--
Auxiliary definition: the abelian coimage and abelian image agree.
We still need to check that this agrees with the canonical morphism.
-/
def coimage_iso_image {X Y : C} (f : X ⟶ Y) : abelian.coimage f ≅ abelian.image f :=
begin
  haveI : preserves_limits F := adj.right_adjoint_preserves_limits,
  haveI : preserves_colimits G := adj.left_adjoint_preserves_colimits,
  calc abelian.coimage f
      ≅ cokernel (kernel.ι f)                 : iso.refl _
  ... ≅ G.obj (cokernel (F.map (kernel.ι f))) : (cokernel_iso _ _ i adj _).symm
  ... ≅ G.obj (cokernel (kernel_comparison f F ≫ (kernel.ι (F.map f))))
                                              : G.map_iso (cokernel_iso_of_eq (by simp))
  ... ≅ G.obj (cokernel (kernel.ι (F.map f))) : G.map_iso (cokernel_epi_comp _ _)
  ... ≅ G.obj (abelian.coimage (F.map f))     : iso.refl _
  ... ≅ G.obj (abelian.image (F.map f))       : G.map_iso (abelian.coimage_iso_image _)
  ... ≅ G.obj (kernel (cokernel.π (F.map f))) : iso.refl _
  ... ≅ kernel (G.map (cokernel.π (F.map f))) : preserves_kernel.iso _ _
  ... ≅ kernel (cokernel.π f)                 : coimage_iso_image_aux F G i adj f
  ... ≅ abelian.image f                       : iso.refl _,
end

local attribute [simp] cokernel_iso coimage_iso_image coimage_iso_image_aux

-- The account of this proof in the Stacks project omits this calculation.
lemma coimage_iso_image_hom {X Y : C} (f : X ⟶ Y) :
  (coimage_iso_image F G i adj f).hom = abelian.coimage_image_comparison f :=
begin
  ext,
  simpa only [←G.map_comp_assoc, coimage_iso_image, nat_iso.inv_inv_app, cokernel_iso,
    coimage_iso_image_aux, iso.trans_symm, iso.symm_symm_eq, iso.refl_trans, iso.trans_refl,
    iso.trans_hom, iso.symm_hom, cokernel_comp_is_iso_inv, cokernel_epi_comp_inv, as_iso_hom,
    functor.map_iso_hom, cokernel_epi_comp_hom, preserves_kernel.iso_hom, kernel_comp_mono_hom,
    kernel_is_iso_comp_hom, cokernel_iso_of_eq_hom_comp_desc_assoc, cokernel.π_desc_assoc,
    category.assoc, π_comp_cokernel_iso_of_eq_inv_assoc, π_comp_cokernel_comparison_assoc,
    kernel.lift_ι, kernel.lift_ι_assoc, kernel_iso_of_eq_hom_comp_ι_assoc,
    kernel_comparison_comp_ι_assoc,
    abelian.coimage_image_factorisation] using nat_iso.naturality_1 i f
end

end abelian_of_adjunction

open abelian_of_adjunction

/--
If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.

See <https://stacks.math.columbia.edu/tag/03A3>
-/
def abelian_of_adjunction
  {C : Type u₁} [category.{v} C] [preadditive C] [has_finite_products C]
  {D : Type u₂} [category.{v} D] [abelian D]
  (F : C ⥤ D) [functor.preserves_zero_morphisms F]
  (G : D ⥤ C) [functor.preserves_zero_morphisms G] [preserves_finite_limits G]
  (i : F ⋙ G ≅ 𝟭 C) (adj : G ⊣ F) : abelian C :=
begin
  haveI := has_kernels F G i, haveI := has_cokernels F G i adj,
  haveI : ∀ {X Y : C} (f : X ⟶ Y), is_iso (abelian.coimage_image_comparison f),
  { intros X Y f, rw ←coimage_iso_image_hom F G i adj f, apply_instance, },
  apply abelian.of_coimage_image_comparison_is_iso,
end

/--
If `C` is an additive category equivalent to an abelian category `D`
via a functor that preserves zero morphisms,
then `C` is also abelian.
-/
def abelian_of_equivalence
  {C : Type u₁} [category.{v} C] [preadditive C] [has_finite_products C]
  {D : Type u₂} [category.{v} D] [abelian D]
  (F : C ⥤ D) [functor.preserves_zero_morphisms F] [is_equivalence F] : abelian C :=
abelian_of_adjunction F F.inv F.as_equivalence.unit_iso.symm F.as_equivalence.symm.to_adjunction

section transfer_enough_injectives

/-!
If `L ⊣ R` are a pair of adjoint functors between abelian categories `𝓐` and `𝓐` and `L` is
faithful and exact, then if `𝓑` has enough injectives, so does `𝓐`. We achieve this by considering
an arbitrary injective presentation of `L(A) ⟶ J`: by adjunction, there is an `A ⟶ R(J)`, we will
prove that this `A ⟶ R(J)` is an injective presentation of `A`.
-/

open limits adjunction

universes v₁ v₂

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D] [enough_injectives D]
variables (L : C ⥤ D) (R : D ⥤ C)

namespace enough_injectives_of_adjunction_auxs

/--
Given injective presentation `L(A) → J`, then `injective_object_of_adjunction A` is defined to be
`R(J)`. It will later be proven to be an injective object in `𝓐`.-/
def RJ (A : C) : C := R.obj $ injective.under (L.obj A)

local notation `RJ_of` := RJ L R

variables (adj : L ⊣ R)
variables {L R}

/--
If `g : X → R(J)` and `f : X → Y` is mono in `𝓐`, then there is an morphism `L(Y) → J`
See the diagram below:

𝓐                             𝓑

A ---> R(J)                 L(A) -----> J <--------
      /                                /          |
     /                                /           |
    /  g                           by adjunction  |
   /                                /             |
  /                                /         by injectivity
X                              L(X)               |
|                               |L.map f          |
v                               v                 |
Y                              L(Y) ---------------

-/
def LY_to_J [preserves_finite_limits L] {A X Y : C} (g : X ⟶ RJ_of A) (f : X ⟶ Y) [mono f] :
  L.obj Y ⟶ injective.under (L.obj A) :=
let factors := (injective.injective_under $ L.obj A).factors in
(factors ((adj.hom_equiv X $ injective.under $ L.obj A).symm g) (L.map f)).some

lemma L_map_comp_to_J_eq [preserves_finite_limits L] {A X Y : C} (g : X ⟶ RJ_of A) (f : X ⟶ Y)
  [mono f] : L.map f ≫ (LY_to_J _ adj g f) = (adj.hom_equiv X $ injective.under _).symm g :=
let factors := (injective.injective_under $ L.obj A).factors in
(factors ((adj.hom_equiv _ _).symm g) (L.map f)).some_spec


/--
If `g : X → R(J)` and `f : X → Y` is mono in `𝓐`, then there is an morphism `Y → R(J)`
See the diagram below:

𝓐                                                  𝓑

A ---> R(J) <---                                   L(A) -----> J <--------
      /        |                                              /          |
     /         |                                             /           |
    /  g   by adjunction                                    /            |
   /           |                                           /             |
  /            |                                          /        by injectivity
X              |                                      L(X)               |
|              |                                       |                 |
v              |                                       v                 |
Y --------------                                      L(Y) ---------------

-/
def Y_to_RJ [preserves_finite_limits L]
  {A X Y : C} (g : X ⟶ RJ_of A) (f : X ⟶ Y) [mono f] : Y ⟶ RJ_of A :=
adj.hom_equiv _ _ $ LY_to_J _ adj g f

lemma comp_Y_to_RJ [preserves_finite_limits L]
  {A X Y : C} (g : X ⟶ RJ_of A) (f : X ⟶ Y) [mono f] : f ≫ Y_to_RJ _ adj g f = g :=
begin
  have := L_map_comp_to_J_eq _ adj g f,
  rw ←adj.hom_equiv_apply_eq at this,
  rw [←this],
  simp only [LY_to_J, Y_to_RJ, L_map_comp_to_J_eq, hom_equiv_counit, hom_equiv_counit,
    functor.map_comp, category.assoc, counit_naturality, left_triangle_components_assoc,
    hom_equiv_naturality_left, hom_equiv_unit],
  generalize_proofs h₁ h₂,
  rw [←R.map_comp],
  simp only [counit_naturality_assoc, left_triangle_components_assoc, functor.map_comp,
    unit_naturality_assoc],
  congr,
  ext,
  rw h₁.some_spec,
end

include adj

lemma injective_RJ [preserves_finite_limits L] (A : C) : injective (RJ_of A) :=
⟨λ X Y g f m, ⟨by { resetI, exact Y_to_RJ _ adj g f }, by apply comp_Y_to_RJ⟩⟩

/-- the morphism `A → R(J)` obtained by `L(A) → J` via adjunction, this morphism is mono, so that
`A → R(J)` is an injective presentation of `A` in `𝓐`.-/
def to_RJ (A : C) : A ⟶ RJ_of A :=
adj.hom_equiv A (injective.under $ L.obj A) (injective.ι _)

local notation `to_RJ_of` A := to_RJ adj A

instance mono_to_RJ (A : C) [abelian C] [abelian D] [preserves_finite_limits L] [faithful L] :
  mono $ to_RJ_of A :=
have e2 : exact (L.map (kernel.ι $ to_RJ_of A)) (L.map $ to_RJ_of A),
begin
  haveI := left_adjoint_preserves_colimits adj,
  exact L.map_exact _ _ (exact_kernel_ι)
end,
have eq1 : L.map (to_RJ_of A) ≫ (adj.counit.app _) = injective.ι _, from by simp [to_RJ],
have m1 : mono (L.map (to_RJ_of A) ≫ (adj.counit.app _)),
begin
  rw eq1, exactI injective.ι_mono _
end,
have m2 : mono (L.map (to_RJ_of A)),
begin
  exactI mono_of_mono _ (adj.counit.app $ injective.under _),
end,
have eq2 : L.map (kernel.ι (to_RJ_of A)) =
  (preserves_kernel.iso L (to_RJ_of A)).hom ≫ kernel.ι (L.map (to_RJ_of A)), from by simp,
have eq3 : kernel.ι (to_RJ_of A) = 0, from L.zero_of_map_zero _
begin
  rw abelian.mono_iff_kernel_ι_eq_zero at m2,
  rw [eq2, m2, comp_zero],
end,
by rw [abelian.mono_iff_kernel_ι_eq_zero, eq3]

end enough_injectives_of_adjunction_auxs

-- Implementation note: only `abelian C` if `category C` and `category D` have the same morphism
-- universe level, in that case `abelian D` is implied by `abelian_of_adjunction`; but in this
-- implementation, we choose not to ask two categories with the same morphism universe level, so
-- we need an additional assumption `abelian D`.
/--
faithful and exact left adjoint functor transfers enough injectiveness.-/
lemma enough_injectives.of_adjunction {C : Type u₁} {D : Type u₂}
  [category.{v₁} C] [category.{v₂} D] [abelian C] [abelian D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [faithful L] [preserves_finite_limits L]
  [enough_injectives D] : enough_injectives C :=
{ presentation := λ A,
  ⟨⟨enough_injectives_of_adjunction_auxs.RJ L R A,
    enough_injectives_of_adjunction_auxs.injective_RJ adj A,
    enough_injectives_of_adjunction_auxs.to_RJ adj A,
    enough_injectives_of_adjunction_auxs.mono_to_RJ adj A⟩⟩ }

-- Implementation note: only `abelian C` if `category C` and `category D` have the same morphism
-- universe level, in that case `abelian D` is implied by `abelian_of_equivalence`; but in this
-- implementation, we choose not to ask two categories with the same morphism universe level, so
-- we need an additional assumption `abelian D`.
/--
equivalence of category transfers enough injectiveness.-/
lemma enough_injectives.of_equivalence {C : Type u₁} {D : Type u₂}
  [category.{v₁} C] [category.{v₂} D] [abelian C] [abelian D]
  (e : C ⥤ D) [is_equivalence e] [enough_injectives D] : enough_injectives C :=
@@enough_injectives.of_adjunction _ _ _ _ e.as_equivalence.to_adjunction _ _ _

end transfer_enough_injectives

end category_theory
