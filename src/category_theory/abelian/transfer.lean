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

open limits

universes v₁ v₂

variables {𝓐 : Type u₁} {𝓑 : Type u₂} [category.{v₁} 𝓐] [category.{v₂} 𝓑] [enough_injectives 𝓑]
variables (L : 𝓐 ⥤ 𝓑) (R : 𝓑 ⥤ 𝓐)

namespace enough_injectives_of_adjunction

/--
Since `𝓑` has enough injectives, `L(A)` has an injective presentation for all `A ∈ 𝓐`, i.e.
`L(A) → J` where `J` is injective.-/
def injective_presentation_of_apply (A : 𝓐) :
  injective_presentation (L.obj A) :=
(nonempty.some (enough_injectives.presentation (L.obj A)))

/--
Given injective presentation `L(A) → J`, then `injective_object_of_adjunction A` is defined to be
`R(J)`. It will later be proven to be an injective object in `𝓐`.-/
def injective_object_of_adjunction (A : 𝓐) : 𝓐 := R.obj $ (injective_presentation_of_apply L A).J

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
|                               |                 |
v                               v                 |
Y                              L(Y) ---------------

-/
def to_J_of_injective_presentation_of_apply [preserves_finite_limits L]
  {A X Y : 𝓐}
  (g : X ⟶ injective_object_of_adjunction L R A)
  (f : X ⟶ Y) [mono f] :
  L.obj Y ⟶ (injective_presentation_of_apply L A).J :=
let factors := (injective_presentation_of_apply L A).injective.factors in
(factors ((adj.hom_equiv X (injective_presentation_of_apply L A).J).symm g) (L.map f)).some

lemma comp_to_J_of_injective_presentation_of_apply [preserves_finite_limits L]
  {A X Y : 𝓐}
  (g : X ⟶ injective_object_of_adjunction L R A)
  (f : X ⟶ Y) [mono f] :
  L.map f ≫ (to_J_of_injective_presentation_of_apply adj g f) =
  (adj.hom_equiv X (injective_presentation_of_apply L A).J).symm g :=
let factors := (injective_presentation_of_apply L A).injective.factors in
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
def injective_object_of_adjunction.factor [preserves_finite_limits L]
  {A X Y : 𝓐}
  (g: X ⟶ injective_object_of_adjunction L R A)
  (f : X ⟶ Y) [mono f] :
  Y ⟶ injective_object_of_adjunction L R A :=
adj.hom_equiv _ _ $ to_J_of_injective_presentation_of_apply adj g f

lemma injective_object_of_adjunction.comp [preserves_finite_limits L]
  {A X Y : 𝓐}
  (g: X ⟶ injective_object_of_adjunction L R A)
  (f : X ⟶ Y) [mono f]:
  f ≫ injective_object_of_adjunction.factor adj g f = g :=
begin
  have := comp_to_J_of_injective_presentation_of_apply adj g f,
  rw ←adj.hom_equiv_apply_eq at this,
  rw [←this],
  simp only [injective_object_of_adjunction.factor, to_J_of_injective_presentation_of_apply,
    adjunction.hom_equiv_counit, adjunction.hom_equiv_naturality_left_symm,
    adjunction.hom_equiv_naturality_right_symm, adjunction.left_triangle_components,
    category.id_comp, adjunction.hom_equiv_naturality_left,
    adjunction.hom_equiv_unit, functor.map_comp, adjunction.unit_naturality_assoc],
  congr,
  ext,
  generalize_proofs h1,
  rw h1.some_spec,
end

section

include adj

lemma injective_object_of_adjunction_is_injective [preserves_finite_limits L] (A : 𝓐) :
  injective (injective_object_of_adjunction L R A) :=
{ factors := λ X Y g f m,
  ⟨by { resetI, exact injective_object_of_adjunction.factor adj g f },
    by apply injective_object_of_adjunction.comp⟩ }

end

/-- just `R(J)`, rename for better clarity-/
def of_adjunction.presentation.J (A : 𝓐) : 𝓐 :=
injective_object_of_adjunction L R A

section

include adj

/-- This `R(J)` is injective-/
lemma of_adjunction.presentation.injective [preserves_finite_limits L] (A : 𝓐) :
  injective (@of_adjunction.presentation.J 𝓐 𝓑 _ _ _ L R A) :=
by apply injective_object_of_adjunction_is_injective adj

end

/-- the morphism `A → R(J)` obtained by `L(A) → J` via adjunction, this morphism is mono, so that
`A → R(J)` is an injective presentation of `A` in `𝓐`.-/
def of_adjunction.presentation.f (A : 𝓐) :
  A ⟶ injective_object_of_adjunction L R A :=
adj.hom_equiv A (injective_presentation_of_apply L A).J (injective_presentation_of_apply L A).f

instance of_adjunction.presentation.mono (A : 𝓐)
  [abelian 𝓐] [abelian 𝓑] [preserves_finite_colimits L] [preserves_finite_limits L] [faithful L] :
  mono $ of_adjunction.presentation.f adj A :=
have e2 : exact (L.map (kernel.ι (of_adjunction.presentation.f adj A)))
  (L.map (of_adjunction.presentation.f adj A)), from L.map_exact _ _ (exact_kernel_ι),
have eq1 : L.map (of_adjunction.presentation.f adj A) ≫ (adj.counit.app _) =
  (injective_presentation_of_apply L A).f, begin
  simp only [of_adjunction.presentation.f, adjunction.hom_equiv_unit, functor.map_comp,
  category.assoc, adjunction.counit_naturality, adjunction.left_triangle_components_assoc],
end,
have m1 : mono (L.map (of_adjunction.presentation.f adj A) ≫ (adj.counit.app _)), begin
  rw eq1, exactI (injective_presentation_of_apply L A).mono
end,
have m2 : mono (L.map (of_adjunction.presentation.f adj A)), begin
  exactI mono_of_mono _ (adj.counit.app (injective_presentation_of_apply L A).J),
end,
have eq2 : L.map (kernel.ι (of_adjunction.presentation.f adj A)) =
  (preserves_kernel.iso L (of_adjunction.presentation.f adj A)).hom ≫
      kernel.ι (L.map (of_adjunction.presentation.f adj A)), begin
  simp only [preserves_kernel.iso_hom, kernel_comparison_comp_ι],
end,
have eq3 : kernel.ι (of_adjunction.presentation.f adj A) = 0, from L.zero_of_map_zero _ begin
  rw abelian.mono_iff_kernel_ι_eq_zero at m2,
  rw [eq2, m2, comp_zero],
end,
by rw [abelian.mono_iff_kernel_ι_eq_zero, eq3]

end enough_injectives_of_adjunction

/--
faithful and exact left adjoint functor transfers enough injectiveness.-/
lemma enough_injectives.of_adjunction {𝓐 : Type u₁} {𝓑 : Type u₂}
  [category.{v₁} 𝓐] [category.{v₂} 𝓑] [abelian 𝓐] [abelian 𝓑]
  {L : 𝓐 ⥤ 𝓑} {R : 𝓑 ⥤ 𝓐} (adj : L ⊣ R)
  [faithful L] [preserves_finite_limits L] [preserves_finite_colimits L]
  [enough_injectives 𝓑] : enough_injectives 𝓐 :=
{ presentation := λ A, nonempty.intro
  { J := enough_injectives_of_adjunction.of_adjunction.presentation.J _,
    injective := enough_injectives_of_adjunction.of_adjunction.presentation.injective adj _,
    f := enough_injectives_of_adjunction.of_adjunction.presentation.f adj _,
    mono := enough_injectives_of_adjunction.of_adjunction.presentation.mono adj _ } }

/--
equivalence of category transfers enough injectiveness.-/
lemma enough_injectives.of_equivalence {𝓐 : Type u₁} {𝓑 : Type u₂}
  [category.{v₁} 𝓐] [category.{v₂} 𝓑] [abelian 𝓐] [abelian 𝓑]
  (e : 𝓐 ⥤ 𝓑) [is_equivalence e] [enough_injectives 𝓑] : enough_injectives 𝓐 :=
@@enough_injectives.of_adjunction _ _ _ _ e.as_equivalence.to_adjunction _ _
  (@@limits.preserves_colimits.preserves_finite_colimits _ _ _
    (adjunction.is_equivalence_preserves_colimits e)) _

end transfer_enough_injectives

end category_theory
