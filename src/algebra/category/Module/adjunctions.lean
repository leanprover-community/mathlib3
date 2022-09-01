/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin
-/
import algebra.category.Module.monoidal
import category_theory.monoidal.functorial
import category_theory.monoidal.types
import linear_algebra.direct_sum.finsupp
import category_theory.linear.linear_functor

/-!
The functor of forming finitely supported functions on a type with values in a `[ring R]`
is the left adjoint of
the forgetful functor from `R`-modules to types.
-/

noncomputable theory

open category_theory

namespace Module

universe u

open_locale classical

variables (R : Type u)

section
variables [ring R]

/--
The free functor `Type u ⥤ Module R` sending a type `X` to the
free `R`-module with generators `x : X`, implemented as the type `X →₀ R`.
-/
@[simps]
def free : Type u ⥤ Module R :=
{ obj := λ X, Module.of R (X →₀ R),
  map := λ X Y f, finsupp.lmap_domain _ _ f,
  map_id' := by { intros, exact finsupp.lmap_domain_id _ _ },
  map_comp' := by { intros, exact finsupp.lmap_domain_comp _ _ _ _, } }

/--
The free-forgetful adjunction for R-modules.
-/
def adj : free R ⊣ forget (Module.{u} R) :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X M, (finsupp.lift M R X).to_equiv.symm,
  hom_equiv_naturality_left_symm' := λ _ _ M f g,
  finsupp.lhom_ext' (λ x, linear_map.ext_ring
    (finsupp.sum_map_domain_index_add_monoid_hom (λ y, ((smul_add_hom R M).flip) (g y))).symm) }

instance : is_right_adjoint (forget (Module.{u} R)) := ⟨_, adj R⟩

end

namespace free
variables [comm_ring R]
local attribute [ext] tensor_product.ext

/-- (Implementation detail) The unitor for `free R`. -/
def ε : 𝟙_ (Module.{u} R) ⟶ (free R).obj (𝟙_ (Type u)) :=
finsupp.lsingle punit.star

@[simp] lemma ε_apply (r : R) : ε R r = finsupp.single punit.star r := rfl

/-- (Implementation detail) The tensorator for `free R`. -/
def μ (α β : Type u) : (free R).obj α ⊗ (free R).obj β ≅ (free R).obj (α ⊗ β) :=
(finsupp_tensor_finsupp' R α β).to_Module_iso

lemma μ_natural {X Y X' Y' : Type u} (f : X ⟶ Y) (g : X' ⟶ Y') :
  ((free R).map f ⊗ (free R).map g) ≫ (μ R Y Y').hom =
    (μ R X X').hom ≫ (free R).map (f ⊗ g) :=
begin
  intros,
  ext x x' ⟨y, y'⟩,
  dsimp [μ],
  simp_rw [finsupp.map_domain_single, finsupp_tensor_finsupp'_single_tmul_single, mul_one,
    finsupp.map_domain_single, category_theory.tensor_apply],
end

lemma left_unitality (X : Type u) :
  (λ_ ((free R).obj X)).hom =
  (ε R ⊗ 𝟙 ((free R).obj X)) ≫ (μ R (𝟙_ (Type u)) X).hom ≫ map (free R).obj (λ_ X).hom :=
begin
  intros,
  ext,
  dsimp [ε, μ],
  simp_rw [finsupp_tensor_finsupp'_single_tmul_single,
    Module.monoidal_category.left_unitor_hom_apply, finsupp.smul_single', mul_one,
    finsupp.map_domain_single, category_theory.left_unitor_hom_apply],
end

lemma right_unitality (X : Type u) :
  (ρ_ ((free R).obj X)).hom =
  (𝟙 ((free R).obj X) ⊗ ε R) ≫ (μ R X (𝟙_ (Type u))).hom ≫ map (free R).obj (ρ_ X).hom :=
begin
  intros,
  ext,
  dsimp [ε, μ],
  simp_rw [finsupp_tensor_finsupp'_single_tmul_single,
    Module.monoidal_category.right_unitor_hom_apply, finsupp.smul_single', mul_one,
    finsupp.map_domain_single, category_theory.right_unitor_hom_apply],
end

lemma associativity (X Y Z : Type u) :
  ((μ R X Y).hom ⊗ 𝟙 ((free R).obj Z)) ≫ (μ R (X ⊗ Y) Z).hom ≫ map (free R).obj (α_ X Y Z).hom =
  (α_ ((free R).obj X) ((free R).obj Y) ((free R).obj Z)).hom ≫
    (𝟙 ((free R).obj X) ⊗ (μ R Y Z).hom) ≫ (μ R X (Y ⊗ Z)).hom :=
begin
  intros,
  ext,
  dsimp [μ],
  simp_rw [finsupp_tensor_finsupp'_single_tmul_single, finsupp.map_domain_single, mul_one,
    category_theory.associator_hom_apply],
end

/-- The free R-module functor is lax monoidal. -/
-- In fact, it's strong monoidal, but we don't yet have a typeclass for that.
@[simps]
instance : lax_monoidal.{u} (free R).obj :=
{ -- Send `R` to `punit →₀ R`
  ε := ε R,
  -- Send `(α →₀ R) ⊗ (β →₀ R)` to `α × β →₀ R`
  μ := λ X Y, (μ R X Y).hom,
  μ_natural' := λ X Y X' Y' f g, μ_natural R f g,
  left_unitality' := left_unitality R,
  right_unitality' := right_unitality R,
  associativity' := associativity R, }

instance : is_iso (lax_monoidal.ε (free R).obj) :=
⟨⟨finsupp.lapply punit.star, ⟨by { ext, simp, }, by { ext ⟨⟩ ⟨⟩, simp, }⟩⟩⟩

end free

variables [comm_ring R]

/-- The free functor `Type u ⥤ Module R`, as a monoidal functor. -/
def monoidal_free : monoidal_functor (Type u) (Module.{u} R) :=
{ ε_is_iso := by { dsimp, apply_instance, },
  μ_is_iso := λ X Y, by { dsimp, apply_instance, },
  ..lax_monoidal_functor.of (free R).obj }

example (X Y : Type u) : (free R).obj (X × Y) ≅ (free R).obj X ⊗ (free R).obj Y :=
((monoidal_free R).μ_iso X Y).symm

end Module

namespace category_theory

universes v u

/--
`Free R C` is a type synonym for `C`, which, given `[comm_ring R]` and `[category C]`,
we will equip with a category structure where the morphisms are formal `R`-linear combinations
of the morphisms in `C`.
-/
@[nolint unused_arguments has_nonempty_instance]
def Free (R : Type*) (C : Type u) := C

/--
Consider an object of `C` as an object of the `R`-linear completion.

It may be preferable to use `(Free.embedding R C).obj X` instead;
this functor can also be used to lift morphisms.
-/
def Free.of (R : Type*) {C : Type u} (X : C) : Free R C := X

variables (R : Type*) [comm_ring R] (C : Type u) [category.{v} C]

open finsupp

-- Conceptually, it would be nice to construct this via "transport of enrichment",
-- using the fact that `Module.free R : Type ⥤ Module R` and `Module.forget` are both lax monoidal.
-- This still seems difficult, so we just do it by hand.
instance category_Free : category (Free R C) :=
{ hom := λ (X Y : C), (X ⟶ Y) →₀ R,
  id := λ (X : C), finsupp.single (𝟙 X) 1,
  comp := λ (X Y Z : C) f g, f.sum (λ f' s, g.sum (λ g' t, finsupp.single (f' ≫ g') (s * t))),
  assoc' := λ W X Y Z f g h,
  begin
    dsimp,
    -- This imitates the proof of associativity for `monoid_algebra`.
    simp only [sum_sum_index, sum_single_index,
      single_zero, single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff,
      add_mul, mul_add, category.assoc, mul_assoc, zero_mul, mul_zero, sum_zero, sum_add],
  end }.

namespace Free

section
local attribute [reducible] category_theory.category_Free

instance : preadditive (Free R C) :=
{ hom_group := λ X Y, finsupp.add_comm_group,
  add_comp' := λ X Y Z f f' g, begin
    dsimp,
    rw [finsupp.sum_add_index];
    { simp [add_mul], }
  end,
  comp_add' := λ X Y Z f g g', begin
    dsimp,
    rw ← finsupp.sum_add,
    congr, ext r h,
    rw [finsupp.sum_add_index];
    { simp [mul_add], },
  end, }

instance : linear R (Free R C) :=
{ hom_module := λ X Y, finsupp.module (X ⟶ Y) R,
  smul_comp' := λ X Y Z r f g, begin
    dsimp,
    rw [finsupp.sum_smul_index];
    simp [finsupp.smul_sum, mul_assoc],
  end,
  comp_smul' := λ X Y Z f r g, begin
    dsimp,
    simp_rw [finsupp.smul_sum],
    congr, ext h s,
    rw [finsupp.sum_smul_index];
    simp [finsupp.smul_sum, mul_left_comm],
  end, }

lemma single_comp_single {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (r s : R) :
  (single f r ≫ single g s : (Free.of R X) ⟶ (Free.of R Z)) = single (f ≫ g) (r * s) :=
by { dsimp, simp, }

end

local attribute [simp] single_comp_single

/--
A category embeds into its `R`-linear completion.
-/
@[simps]
def embedding : C ⥤ Free R C :=
{ obj := λ X, X,
  map := λ X Y f, finsupp.single f 1,
  map_id' := λ X, rfl,
  map_comp' := λ X Y Z f g, by simp, }

variables (R) {C} {D : Type u} [category.{v} D] [preadditive D] [linear R D]

open preadditive linear

/--
A functor to an `R`-linear category lifts to a functor from its `R`-linear completion.
-/
@[simps]
def lift (F : C ⥤ D) : Free R C ⥤ D :=
{ obj := λ X, F.obj X,
  map := λ X Y f, f.sum (λ f' r, r • (F.map f')),
  map_id' := by { dsimp [category_theory.category_Free], simp },
  map_comp' := λ X Y Z f g, begin
    apply finsupp.induction_linear f,
    { simp only [limits.zero_comp, sum_zero_index] },
    { intros f₁ f₂ w₁ w₂,
      rw add_comp,
      rw [finsupp.sum_add_index, finsupp.sum_add_index],
      { simp only [w₁, w₂, add_comp] },
      { intros, rw zero_smul },
      { intros, simp only [add_smul], },
      { intros, rw zero_smul },
      { intros, simp only [add_smul], }, },
    { intros f' r,
      apply finsupp.induction_linear g,
      { simp only [limits.comp_zero, sum_zero_index] },
      { intros f₁ f₂ w₁ w₂,
        rw comp_add,
        rw [finsupp.sum_add_index, finsupp.sum_add_index],
        { simp only [w₁, w₂, comp_add], },
        { intros, rw zero_smul },
        { intros, simp only [add_smul], },
        { intros, rw zero_smul },
        { intros, simp only [add_smul], }, },
      { intros g' s,
        erw single_comp_single,
        simp [mul_comm r s, mul_smul] } }
  end, }

@[simp]
lemma lift_map_single (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (r : R) :
  (lift R F).map (single f r) = r • F.map f :=
by simp

instance lift_additive (F : C ⥤ D) : (lift R F).additive :=
{ map_add' := λ X Y f g, begin
    dsimp,
    rw finsupp.sum_add_index; simp [add_smul]
  end, }

instance lift_linear (F : C ⥤ D) : (lift R F).linear R :=
{ map_smul' := λ X Y f r, begin
    dsimp,
    rw finsupp.sum_smul_index;
    simp [finsupp.smul_sum, mul_smul],
  end, }

/--
The embedding into the `R`-linear completion, followed by the lift,
is isomorphic to the original functor.
-/
def embedding_lift_iso (F : C ⥤ D) : embedding R C ⋙ lift R F ≅ F :=
nat_iso.of_components
  (λ X, iso.refl _)
  (by tidy)

/--
Two `R`-linear functors out of the `R`-linear completion are isomorphic iff their
compositions with the embedding functor are isomorphic.
-/
@[ext]
def ext {F G : Free R C ⥤ D} [F.additive] [F.linear R] [G.additive] [G.linear R]
  (α : embedding R C ⋙ F ≅ embedding R C ⋙ G) : F ≅ G :=
nat_iso.of_components
  (λ X, α.app X)
  begin
    intros X Y f,
    apply finsupp.induction_linear f,
    { simp, },
    { intros f₁ f₂ w₁ w₂,
      simp only [F.map_add, G.map_add, add_comp, comp_add, w₁, w₂], },
    { intros f' r,
      rw [iso.app_hom, iso.app_hom, ←smul_single_one, F.map_smul, G.map_smul, smul_comp, comp_smul],
      change r • (embedding R C ⋙ F).map f' ≫ _ = r • _ ≫ (embedding R C ⋙ G).map f',
      rw α.hom.naturality f',
      apply_instance, -- Why are these not picked up automatically when we rewrite?
      apply_instance, }
  end

/--
`Free.lift` is unique amongst `R`-linear functors `Free R C ⥤ D`
which compose with `embedding ℤ C` to give the original functor.
-/
def lift_unique (F : C ⥤ D) (L : Free R C ⥤ D) [L.additive] [L.linear R]
  (α : embedding R C ⋙ L ≅ F) :
  L ≅ lift R F :=
ext R (α.trans (embedding_lift_iso R F).symm)

end Free

end category_theory

namespace change_of_rings

universes u₁ u₂

namespace extension_restriction_adj

open_locale change_of_rings
open tensor_product

universes v

variables {R : Type u₁} {S : Type u₂} [comm_ring R] [comm_ring S] (f : R →+* S)

/--
Given `R`-module X and `S`-module Y and a map `(extension_of_scalars.functor f).obj X ⟶ Y`,
there is a map `X ⟶ (restriction_of_scalars.functor f).obj Y`
-/
@[simps] def hom_equiv.to_restriction {X Y} (g : (extension_of_scalars.functor f).obj X ⟶ Y) :
  X ⟶ (restriction_of_scalars.functor f).obj Y :=
let m1 : module R S := module.comp_hom S f,
    m2 : module R Y := module.comp_hom Y f in
{ to_fun := λ x, g (x ⊗ₜ[R, f] 1),
  map_add' := λ x x', by rw [tensor_product.add_tmul, map_add],
  map_smul' := λ r x, begin
    resetI,
    rw [ring_hom.id_apply, smul_tmul, restriction_of_scalars.smul_def f ⟨S⟩],
    change _ = f r • _,
    rw [←linear_map.map_smul],
    congr,
  end }

/--
Given `R`-module X and `S`-module Y and a map `X ⟶ (restriction_of_scalars.functor f).obj Y`,
there is a map `(extension_of_scalars.functor f).obj X ⟶ Y`
-/
@[simps] def hom_equiv.to_extension {X Y} (g : X ⟶ (restriction_of_scalars.functor f).obj Y) :
  (extension_of_scalars.functor f).obj X ⟶ Y :=
{ to_fun := λ z,
  let m1 := module.comp_hom S f,
      m2 : module R Y := module.comp_hom Y f,
      m3 : module S ((restriction_of_scalars.functor f).obj Y) := Y.is_module in
  begin
    resetI,
    refine tensor_product.lift
      { to_fun := λ x,
          { to_fun := λ s, s • (g x : Y),
            map_add' := _,
            map_smul' := _, },
        map_add' := _,
        map_smul' := _ } z,
    { intros, rw add_smul, },
    { intros r s,
      rw [ring_hom.id_apply],
      calc  (r • s) • g x
          = (f r * s) • g x : rfl
      ... = f r • s • g x : by rw [mul_smul], },
    { intros x y,
      ext s,
      simp only [linear_map.coe_mk, smul_add, linear_map.add_apply, map_add], },
    { intros r x,
      ext s,
      simp only [linear_map.coe_mk, ring_hom.id_apply, linear_map.smul_apply,
        linear_map.map_smul],
      erw [← mul_smul, mul_comm, mul_smul],
      refl, },
  end,
  map_add' := λ z1 z2, by simp only [map_add],
  map_smul' := λ r z, begin
    rw [ring_hom.id_apply],
    induction z using tensor_product.induction_on with x y x y ih1 ih2,
    { simp only [smul_zero, map_zero], },
    { erw [extension_of_scalars.smul_pure_tensor],
      simp [tensor_product.lift.tmul, mul_smul], },
    { simp only [smul_add, map_add],
      dsimp only at ih1 ih2,
      rw [ih1, ih2], },
  end }

/--
Given `R`-module X and `S`-module Y, the linear maps `(extension_of_scalars.functor f).obj X ⟶ Y`
bijectively corresponding to `X ⟶ (restriction_of_scalars.functor f).obj Y`
-/
@[simps] def hom_equiv' {X Y} :
  ((extension_of_scalars.functor f).obj X ⟶ Y) ≃ (X ⟶ (restriction_of_scalars.functor f).obj Y) :=
{ to_fun := hom_equiv.to_restriction f,
  inv_fun := hom_equiv.to_extension f,
  left_inv := λ g, begin
    ext z,
    induction z using tensor_product.induction_on with x s z1 z2 ih1 ih2,
    { simp only [map_zero], },
    { erw tensor_product.lift.tmul,
      simp only [linear_map.coe_mk],
      erw [← linear_map.map_smul, extension_of_scalars.smul_pure_tensor, mul_one], },
    { rw [map_add, map_add, ih1, ih2], }
  end,
  right_inv := λ g, by { ext, simp } }

/--
For any `R`-module X, there is a natural `R`-linear map from `X` to `X ⨂ S` by sending `x ↦ x ⊗ 1`
-/
@[simps] def unit.map {X} :
  X ⟶ (extension_of_scalars.functor f ⋙ restriction_of_scalars.functor f).obj X :=
let m1 : module R S := module.comp_hom S f in
{ to_fun := λ x, x ⊗ₜ[R, f] 1,
  map_add' := λ x x', by { rw tensor_product.add_tmul, },
  map_smul' := λ r x, begin
    resetI,
    erw [smul_tmul, extension_of_scalars.smul_pure_tensor],
    congr,
  end }

/--
The natural transformation from ideantity functor on `R`-module to the composition of extension and
restriction of scalars.
-/
def unit : 𝟭 (Module R) ⟶ extension_of_scalars.functor f ⋙ restriction_of_scalars.functor f :=
{ app := λ _, unit.map f,
  naturality' := λ X X' g, begin
    ext,
    simp only [unit.map, functor.id_map, Module.coe_comp, linear_map.coe_mk,
      function.comp_app, functor.comp_map],
    rw show (restriction_of_scalars.functor f).map ((extension_of_scalars.functor f).map g) =
      { to_fun := (extension_of_scalars.functor f).map g, map_add' := _, map_smul' := _ }, from rfl,
    simp only [linear_map.coe_mk],
    erw tensor_product.lift.tmul,
    simp only [linear_map.coe_mk],
  end }

/--
For any `S`-module Y, there is a natural `R`-linear map from `Y ⨂ S` to `Y` by
`y ⊗ s ↦ s • y`-/
@[simps] def counit.map {Y} :
  (restriction_of_scalars.functor f ⋙ extension_of_scalars.functor f).obj Y ⟶ Y :=
let m1 : module R S := module.comp_hom S f,
    m2 : module R Y := module.comp_hom Y f in
{ to_fun :=
    begin
      resetI,
      refine tensor_product.lift
        { to_fun := λ y,
            { to_fun := λ s, _,
              map_add' := _,
              map_smul' := _ },
          map_add' := _,
          map_smul' := _ },
      { haveI t : has_smul S ((restriction_of_scalars.functor f).obj Y),
        { haveI : module S ((restriction_of_scalars.functor f).obj Y) :=
          (infer_instance : module S Y),
          apply_instance, },
        exact @has_smul.smul _ _ t s y, },
      { intros s s', rw add_smul, },
      { intros r s,
        rw [ring_hom.id_apply, restriction_of_scalars.smul_def f ⟨S⟩,
          restriction_of_scalars.smul_def f, smul_eq_mul, mul_smul], },
      { intros y1 y2,
        ext,
        simp only [linear_map.coe_mk, smul_add, linear_map.add_apply], },
      { intros r y,
        ext s,
        simp only [ring_hom.id_apply, restriction_of_scalars.smul_def,
          linear_map.coe_mk, linear_map.smul_apply],
        erw [← mul_smul, mul_comm, mul_smul],
        refl, },
    end,
  map_add' := λ z1 z2, by simp only [map_add],
  map_smul' := λ s z, begin
    simp only [ring_hom.id_apply],
    induction z using tensor_product.induction_on with x s' z1 z2 ih1 ih2,
    { simp only [smul_zero, map_zero], },
    { erw extension_of_scalars.smul_pure_tensor,
      simp only [linear_map.coe_mk, tensor_product.lift.tmul],
      rw mul_smul, },
    { rw [smul_add, map_add, map_add, ih1, ih2, smul_add], },
  end }

/--
The natural transformation from the composition of restriction and extension of scalars to the
identity functor on `S`-module.
-/
@[simps] def counit :
  (restriction_of_scalars.functor f ⋙ extension_of_scalars.functor f) ⟶ (𝟭 (Module S)) :=
{ app := λ _, counit.map f,
  naturality' := λ Y Y' g, begin
    ext z,
    simp only [functor.comp_map, Module.coe_comp, function.comp_app, functor.id_map],
    induction z using tensor_product.induction_on with y s z1 z2 ih1 ih2,
    { simp only [map_zero], },
    { unfold counit.map,
      erw [tensor_product.lift.tmul, tensor_product.lift.tmul],
      simp only [linear_map.coe_mk, linear_map.map_smulₛₗ, ring_hom.id_apply],
      refl },
    { rw [map_add, map_add, ih1, ih2, map_add, map_add], }
  end }

/--
extension of scalars ⊣ restriction of scalars
-/
def adjunction : adjunction (extension_of_scalars.functor f) (restriction_of_scalars.functor f) :=
{ hom_equiv := λ _ _, hom_equiv' f,
  unit := unit f,
  counit := counit f,
  hom_equiv_unit' := λ X Y g, by { ext, simpa },
  hom_equiv_counit' := λ X Y g,
  begin
    ext z,
    simp only [hom_equiv'_symm_apply, hom_equiv.to_extension_apply, counit_app, Module.coe_comp,
      function.comp_app, counit.map_apply],
    induction z using tensor_product.induction_on with x s z1 z2 ih1 ih2,
    { simp only [map_zero], },
    { erw tensor_product.lift.tmul, },
    { simp only [map_add, ih1, ih2], }
  end }

end extension_restriction_adj

end change_of_rings
