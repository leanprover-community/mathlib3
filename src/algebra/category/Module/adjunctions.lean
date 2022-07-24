/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin
-/
import algebra.category.Module.monoidal
import algebra.category.Group.basic
import algebra.category.Group.Z_Module_equivalence
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
@[nolint unused_arguments has_inhabited_instance]
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
    { simp, },
    { intros f₁ f₂ w₁ w₂,
      rw add_comp,
      rw [finsupp.sum_add_index, finsupp.sum_add_index],
      { simp [w₁, w₂, add_comp], },
      { simp, },
      { intros, simp only [add_smul], },
      { simp, },
      { intros, simp only [add_smul], }, },
    { intros f' r,
      apply finsupp.induction_linear g,
      { simp, },
      { intros f₁ f₂ w₁ w₂,
        rw comp_add,
        rw [finsupp.sum_add_index, finsupp.sum_add_index],
        { simp [w₁, w₂, add_comp], },
        { simp, },
        { intros, simp only [add_smul], },
        { simp, },
        { intros, simp only [add_smul], }, },
      { intros g' s,
        erw single_comp_single,
        simp [mul_comm r s, mul_smul], } }
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

namespace restriction_of_scalars

variables {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)
variable (M : Module S)

/--Any `S`-module M is also an `R`-module via a ring homomorphism `f : R ⟶ S` by defining
`r • m := f r • m`. This is called restriction of scalars. -/
def obj' : Module R :=
{ carrier := M,
  is_add_comm_group := infer_instance,
  is_module := module.comp_hom M f }

section

include f

/--The `R`-scalar multiplication on `S`-module M defined by `r • m := f r • m`
-/
protected def has_smul : has_smul R M :=
begin
  haveI : module R M := (obj' f M).is_module,
  apply_instance
end

end

localized "notation r ` r•[` f `] ` m :=
  @@has_smul.smul (restriction_of_scalars.has_smul f _) r m"
  in change_of_rings

@[simp] lemma smul_def (r : R) (m : M) :
  (r r•[f] m) = f r • m := rfl

/--
Given an `S`-linear map `g : M → M'` between `S`-modules, `g` is also `R`-linear between `M` and
`M'` by means of restriction of scalars.
-/
@[simps] def map' {M M' : Module S} (g : M ⟶ M') :
  obj' f M ⟶ obj' f M' :=
{ map_smul' := λ r (x : M), by simp,
  ..g }

private lemma map_id' : map' f (𝟙 M) = 𝟙 _ := linear_map.ext $ λ (m : M), rfl

private lemma map_comp' {M M' M'' : Module S} (g : M ⟶ M') (h : M' ⟶ M'') :
  map' f (g ≫ h) = map' f g ≫ map' f h :=
linear_map.ext $ λ (x : M), rfl

/--
The restriction of scalars operation is functorial. For any `f : R →+* S` a ring homomorphism,
* `S`-module `M` can be considered as `R`-module by `r • m = f r • m`
* `S`-linear map is also `R`-linear
-/
@[simps] protected def functor : Module S ⥤ Module R :=
{ obj := obj' f,
  map := λ _ _, map' f,
  map_id' := map_id' f,
  map_comp' := λ _ _ _ g h, map_comp' f _ _ }

end restriction_of_scalars

namespace coextension_of_scalars

variables {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)
variable (M : Module R)

local notation `Hom` M := (restriction_of_scalars.functor f).obj ⟨S⟩ →ₗ[R] M

/--
Given an `R`-module M, consider the Hom(S, M) -- the `R`-linear maps between S (as an `R`-module by
means of restriciton of scalars) and M. `S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)`
-/
protected def has_smul : has_smul S $ Hom M :=
{ smul := λ s g,
  { to_fun := λ (s' : S), g (s' • s : S),
    map_add' := λ (x y : S), by simp [add_smul, map_add],
    map_smul' := λ r (t : S), by rw [ring_hom.id_apply, restriction_of_scalars.smul_def f ⟨S⟩,
      ←linear_map.map_smul, restriction_of_scalars.smul_def f ⟨S⟩, smul_assoc] } }

localized "notation s ` c•[` f `] ` m :=
  @has_smul.smul _ _ (coextension_of_scalars.has_smul f _) s m" in change_of_rings

@[simp] lemma smul_apply (s : S) (g : Hom M) (s' : S) :
  (s c•[f] g) s' = g (s' • s : S) := rfl

/--
`S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)` such that `1 • g = g` and `(s * t) • g = s • t • g`
-/
protected def mul_action : mul_action S $ Hom M :=
{ one_smul := λ g, linear_map.ext $ λ (s : S), by simp,
  mul_smul := λ (s t : S) g, linear_map.ext $ λ (x : S), by simp [mul_assoc],
  ..coextension_of_scalars.has_smul f _ }

/--
`S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)` such that
* 1 • g = g
* (s * t) • g = s • t • g
* s • (g + h) = s • g + s • h
* s • 0 = 0
-/
protected def distrib_mul_action : distrib_mul_action S $ Hom M :=
{ smul_add := λ s g h, linear_map.ext $ λ (t : S), by simp,
  smul_zero := λ s, linear_map.ext $ λ (t : S), by simp,
  ..coextension_of_scalars.mul_action f _ }

/--
`S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)`, this action defines an `S`-module structure on
Hom(S, M).
-/
protected def is_module : module S $ Hom M :=
{ add_smul := λ s1 s2 g, linear_map.ext $ λ (x : S), by simp,
  zero_smul := λ g, linear_map.ext $ λ (x : S), by simp,
  ..coextension_of_scalars.distrib_mul_action f _ }

/--
Given any `R`-module M, Hom(S, M) has an `R`-module structure via `f : R →+* S`, this is called the
coextension of scalars.
-/
def obj' : Module S :=
{ carrier := Hom M,
  is_add_comm_group := infer_instance,
  is_module := coextension_of_scalars.is_module f _ }

/--
Given an `R`-linear map between `R`-modules `M` and `M'`, there is an `S`-linear map between
Hom(S, M) and Hom(S, M').
-/
@[simps] def map' {M M' : Module R} (g : M ⟶ M') :
  obj' f M ⟶ obj' f M' :=
{ to_fun := λ h, g.comp h,
  map_add' := λ _ _, linear_map.comp_add _ _ _,
  map_smul' := λ s h, linear_map.ext $ λ (t : S), by simp }

private lemma map_id' : map' f (𝟙 M) = 𝟙 _ := linear_map.ext $ λ h, linear_map.ext $ λ x, rfl
private lemma map_comp' {M M' M'' : Module R} (g : M ⟶ M') (h : M' ⟶ M'') :
  map' f (g ≫ h) = map' f g ≫ map' f h :=
linear_map.ext $ λ h, linear_map.ext $ λ x, rfl

/--
The coextension of scalars is functorial by sending `M ↦ Hom(S, M)` and `g ↦ (h ↦ g ∘ h)`
-/
@[simps] protected def functor : Module R ⥤ Module S :=
{ obj := obj' f,
  map := λ _ _, map' _,
  map_id' := map_id' _,
  map_comp' := λ _ _ _, map_comp' f }

end coextension_of_scalars

namespace extension_of_scalars

open_locale tensor_product
open tensor_product

variables {R : Type u₁} {S : Type u₂} [comm_ring R] [comm_ring S] (f : R →+* S) (M : Module R)
include f

include M
localized "notation M `⊗[` R `,` f `]` S := @tensor_product R _ M S _ _ _
  (module.comp_hom S f)" in change_of_rings
localized "notation m `⊗ₜ[` R `,` f `]` s := @tensor_product.tmul R _ _ _ _ _ _
  (module.comp_hom _ f) m s" in change_of_rings

/--
Given `R`-module M, consider M ⨂ S, we define an `S`-action on M ⨂ S by
  `s • (m ⊗ s') := m ⊗ (s * s')`.
-/
def smul_by (s : S) : (M ⊗[R, f] S) ⟶ (M ⊗[R, f] S) :=
let m : module R S := module.comp_hom S f in
begin
  resetI,
  refine tensor_product.lift ⟨_, _, _⟩,
  { -- we define `m ↦ (s' ↦ m ⊗ (s * s'))`
    refine λ m, ⟨λ s', m ⊗ₜ[R, f] (s * s'), _, _⟩,
    { -- map_add
      intros,
      erw [mul_add, tmul_add], },
    { -- map_smul
      intros,
      rw [ring_hom.id_apply, smul_tmul', smul_tmul],
      congr' 1,
      rw [restriction_of_scalars.smul_def f ⟨S⟩, smul_eq_mul, ← mul_assoc, mul_comm s,
        mul_assoc, restriction_of_scalars.smul_def f ⟨S⟩, smul_eq_mul],
    }, },
  { intros,
    ext,
    simp only [linear_map.coe_mk, map_add, add_tmul],
    refl, },
  { intros,
    ext,
    simp only [linear_map.coe_mk, ring_hom.id_apply, linear_map.smul_apply],
    rw [tensor_product.smul_tmul'], }
end

lemma smul_by.pure_tensor (s s' : S) (m : M) :
  (smul_by f M s (m ⊗ₜ[R, f] s')) =
  m ⊗ₜ[R, f] (s * s') :=
begin
  simp only [smul_by, tensor_product.lift.tmul, linear_map.coe_mk],
end

lemma smul_by.one : smul_by f M 1 = 𝟙 _ :=
begin
  ext,
  induction x using tensor_product.induction_on with _ _ _ _ ih1 ih2,
  { simpa only [smul_by, map_zero], },
  { simpa only [smul_by.pure_tensor, one_mul], },
  { simp only [category_theory.types_id_apply] at ih1 ih2 ⊢,
    conv_rhs { rw [← ih1, ← ih2] },
    convert map_add _ _ _, },
end

lemma smul_by.mul (s s' : S) : smul_by f M (s * s') = smul_by f M s' ≫ smul_by f M s :=
begin
  ext,
  induction x using tensor_product.induction_on with _ _ x y ih1 ih2,
  { simp only [smul_by, map_zero, types_comp_apply], },
  { simp [smul_by, mul_assoc], },
  { convert congr_arg2 (+) ih1 ih2 using 1,
    { convert map_add _ _ _ },
    { simp only [types_comp_apply],
      calc  smul_by f M s (smul_by f M s' (x + y))
          = smul_by f M s (smul_by f M s' x + smul_by f M s' y)
          : by { congr' 1, convert map_add _ _ _}
      ... = smul_by f M s (smul_by f M s' x) + smul_by f M s (smul_by f M s' y)
          : by convert map_add _ _ _, }, }
end

lemma smul_by.apply_zero (s : S) : smul_by f M s 0 = 0 :=
by simp only [smul_by, map_zero]

lemma smul_by.apply_add (s : S) (a b) : smul_by f M s (a + b) = smul_by f M s a + smul_by f M s b :=
by simp [smul_by, map_add]


lemma smul_by.add (s s') : smul_by f M (s + s') = smul_by f M s + smul_by f M s' :=
begin
  ext x,
  induction x using tensor_product.induction_on with _ _ x y ih1 ih2,
  { simp [smul_by], },
  { simp [smul_by, add_mul, tmul_add], },
  { simp only [pi.add_apply, smul_by.apply_add, ih1, ih2],
    rw show ∀ (a b c d : M ⊗[R, f] S), a + b + (c + d) = a + c + (b + d), from _,
    intros,
    -- `ring` doesn't work here for some reason
    rw calc a + b + (c + d) = a + (b + (c + d)) : by rw add_assoc
      ... = a + (b + c + d) : by rw add_assoc
      ... = a + (c + b + d) : by rw add_comm b c
      ... = a + (c + (b + d)) : by rw add_assoc
      ... = a + c + (b + d) : by rw add_assoc, }
end

lemma smul_by.zero : smul_by f M 0 = 0 :=
begin
  ext,
  induction x using tensor_product.induction_on with _ _ x y ih1 ih2,
  { simp [smul_by], },
  { simp [smul_by], },
  { simp [smul_by.apply_add, ih1, ih2], }
end

/--
Since `S` has an `R`-module structure, `M ⊗[R] S` can be given an `S`-module structure.
The scalar multiplication is defined by `s • (m ⊗ s') := m ⊗ (s * s')`
-/
@[reducible] def has_smul_S_M_tensor_S : has_smul S (M ⊗[R, f] S) :=
{ smul := λ s', smul_by f M s' }

local attribute [instance] has_smul_S_M_tensor_S

lemma smul_pure_tensor (s s' : S) (m : M) :
  (s • (m ⊗ₜ[R, f] s')) =
  m ⊗ₜ[R, f] (s * s') :=
by simp only [smul_by, tensor_product.lift.tmul, linear_map.coe_mk]

@[simp] lemma smul_zero (s : S) : s • (0 : M ⊗[R, f] S) = 0 :=
by simp [smul_by]

/--
Since `S` has an `R`-module structure, `M ⊗[R] S` can be given an `S`-module structure.
The scalar multiplication is defined by `s • (m ⊗ s') := m ⊗ (s * s')`
-/
def mul_action_S_M_tensor_S : mul_action S (M ⊗[R, f] S) :=
{ one_smul := λ x, begin
    change smul_by _ _ _ _ = _,
    rw smul_by.one f M,
    refl,
  end,
  mul_smul := λ s s' x, begin
    change smul_by _ _ _ _ = smul_by _ _ _ (smul_by _ _ _ _),
    rw smul_by.mul f M,
    refl,
  end,
  ..(has_smul_S_M_tensor_S f M) }.

localized "attribute [instance] extension_of_scalars.mul_action_S_M_tensor_S" in change_of_rings

/--
Since `S` has an `R`-module structure, `M ⊗[R] S` can be given an `S`-module structure.
The scalar multiplication is defined by `s • (m ⊗ s') := m ⊗ (s * s')`
-/
def distrib_mul_action_S_M_tensor_S : _root_.distrib_mul_action S (M ⊗[R, f] S) :=
{ smul_zero := λ s, by { change smul_by f M s 0 = 0, apply smul_by.apply_zero, },
  smul_add := λ s x y, begin
    change smul_by f M s (x + y) = smul_by f M s x + smul_by f M s y,
    apply smul_by.apply_add,
  end }

/--
Since `S` has an `R`-module structure, `M ⊗[R] S` can be given an `S`-module structure.
The scalar multiplication is defined by `s • (m ⊗ s') := m ⊗ (s * s')`
-/
def is_module : module S (M ⊗[R, f] S) :=
{ add_smul := λ s s' x, begin
    change smul_by _ _ _ _ = smul_by _ _ _ _ + smul_by _ _ _ _,
    rw smul_by.add,
    refl,
  end,
  zero_smul := λ x, begin
    change smul_by _ _ _ _ = _,
    rw smul_by.zero,
    refl,
  end,
  ..(distrib_mul_action_S_M_tensor_S f M) }.

/--
M ⨂ S is also an `R`-module
-/
def is_module' : module R (M ⊗[R, f] S) := infer_instance

localized "attribute [instance] extension_of_scalars.is_module extension_of_scalars.is_module'"
  in change_of_rings

def obj' : Module S :=
{ carrier := M ⊗[R, f] S,
  is_module := is_module f M }

omit M
/--
Extension of scalars is a functor where an `R`-module `M` is sent to `M ⊗ S` and
`l : M1 ⟶ M2` is sent to `m ⊗ s ↦ l m ⊗ s`
-/
@[simps] def map' {M1 M2 : Module R} (l : M1 ⟶ M2) : (obj' f M1) ⟶ (obj' f M2) :=
let im1 : module R S := module.comp_hom S f,
    im2 : module R (obj' f M2) := is_module' f M2 in
begin
  resetI,
  refine
    { to_fun := tensor_product.lift { to_fun := λ m1, _, map_add' := _, map_smul' := _ },
      map_add' := _,
      map_smul' := _ },
  { -- `S ⟶ f _* M2` given by `s ↦ l m ⊗ s`
    refine { to_fun := λ s, (l m1) ⊗ₜ[R, f] s, map_add' := _, map_smul' := _ },
    { -- map_add
      intros,
      rw [tmul_add], },
    { -- map_smul
      intros,
      rw [ring_hom.id_apply, restriction_of_scalars.smul_def f ⟨S⟩ r x, smul_tmul',
        smul_tmul],
      refl, } },
  { intros m m',
    ext s,
    simp only [add_tmul, map_add, linear_map.coe_mk, linear_map.add_apply], },
  { intros r m,
    ext s,
    rw [ring_hom.id_apply, linear_map.map_smul, linear_map.coe_mk, linear_map.smul_apply,
      linear_map.coe_mk, smul_tmul'], },
  { intros z1 z2,
    rw [map_add], },
  { intros s z,
    induction z using tensor_product.induction_on with _ _ z1 z2 ih1 ih2,
    { simp only [smul_zero, map_zero], },
    { simp only [smul_pure_tensor, ring_hom.id_apply, linear_map.coe_mk, lift.tmul], },
    { rw [smul_add, map_add, ring_hom.id_apply, ih1, ih2, map_add, smul_add,
        ring_hom.id_apply], } }
end

/--
Extension of scalars is a functor where an `R`-module `M` is sent to `M ⊗ S` and
`l : M1 ⟶ M2` is sent to `m ⊗ s ↦ l m ⊗ s`
-/
def functor : Module R ⥤ Module S :=
{ obj := λ M, obj' f M,
  map := λ M1 M2 l, map' f l,
  map_id' := λ M, begin
    ext x,
    rw [map', Module.id_apply],
    induction x using tensor_product.induction_on with _ _ m s ihx ihy,
    { rw map_zero },
    { rw [linear_map.coe_mk, tensor_product.lift.tmul], refl, },
    { rw [linear_map.coe_mk] at ihx ihy ⊢,
      rw [map_add, ihx, ihy], }
  end,
  map_comp' := λ M1 M2 M3 g h, begin
    ext x,
    rw [map', map', map', linear_map.coe_mk, category_theory.comp_apply,
      linear_map.coe_mk, linear_map.coe_mk],
    induction x using tensor_product.induction_on with _ _ m s ihx ihy,
    { rw [map_zero, map_zero, map_zero], },
    { rw [tensor_product.lift.tmul, tensor_product.lift.tmul], refl, },
    { rw [map_add, ihx, ihy, map_add, map_add], }
  end }

end extension_of_scalars

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

namespace restriction_coextension_adj

variables {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)

/--
Given `R`-module X and `S`-module Y, any `g : (restriction_of_scalars.functor f).obj Y ⟶ X`
corresponds to `Y ⟶ (coextension_of_scalars.functor f).obj X` by sendind `y ↦ (s ↦ g (s • y))`
-/
@[simps] def hom_equiv.from_restriction_to_to_coextension
  {X Y} (g : (restriction_of_scalars.functor f).obj Y ⟶ X) :
  Y ⟶ (coextension_of_scalars.functor f).obj X :=
{ to_fun := λ (y : Y),
  { to_fun := λ (s : S), g $ (s • y : Y),
    map_add' := λ (s1 s2 : S), by simp [add_smul],
    map_smul' := λ r (s : S),
    begin
      rw [restriction_of_scalars.smul_def f ⟨S⟩, ring_hom.id_apply,
        ←g.map_smul, smul_eq_mul, mul_smul],
      congr,
    end },
  map_add' := λ (y1 y2 : Y), linear_map.ext $ λ (s : S),
  begin
    rw [linear_map.add_apply, linear_map.coe_mk, linear_map.coe_mk, linear_map.coe_mk,
      smul_add, map_add],
  end,
  map_smul' := λ s y, linear_map.ext $ λ (t : S), by simp [mul_smul] }

/--
Given `R`-module X and `S`-module Y, any `g : Y ⟶ (coextension_of_scalars.functor f).obj X`
corresponds to `(restriction_of_scalars.functor f).obj Y ⟶ X` by `y ↦ g y 1`
-/
@[simps] def hom_equiv.to_coextension_to_from_restriction
  {X Y} (g : Y ⟶ (coextension_of_scalars.functor f).obj X) :
  (restriction_of_scalars.functor f).obj Y ⟶ X :=
{ to_fun := λ (y : Y), (g y).to_fun (1 : S),
  map_add' := λ x y, by simp only [g.map_add, linear_map.to_fun_eq_coe, linear_map.add_apply],
  map_smul' := λ r (y : Y),
  by rw [linear_map.to_fun_eq_coe, linear_map.to_fun_eq_coe, ring_hom.id_apply,
    ←linear_map.map_smul, restriction_of_scalars.smul_def f ⟨S⟩, smul_eq_mul, mul_one,
    restriction_of_scalars.smul_def f Y, linear_map.map_smul, coextension_of_scalars.smul_apply,
    smul_eq_mul, one_mul], }

lemma hom_equiv.fb {X Y} (g : (restriction_of_scalars.functor f).obj Y ⟶ X) :
  hom_equiv.to_coextension_to_from_restriction f
    (hom_equiv.from_restriction_to_to_coextension f g) = g :=
linear_map.ext $ λ (y : Y), by simp

lemma hom_equiv.bf {X Y} (g : Y ⟶ (coextension_of_scalars.functor f).obj X) :
  hom_equiv.from_restriction_to_to_coextension f
    (hom_equiv.to_coextension_to_from_restriction f g) = g :=
linear_map.ext $ λ (y : Y), by { ext, simp }

/--
The natural transformation from identity functor to the composition of restriction and coextension
of scalars.
-/
@[simps] protected def unit' :
  𝟭 (Module S) ⟶ restriction_of_scalars.functor f ⋙ coextension_of_scalars.functor f :=
{ app := λ Y,
  { to_fun := λ (y : Y),
    { to_fun := λ (s : S), (s • y : Y),
      map_add' := λ s s', add_smul _ _ _,
      map_smul' := λ r (s : S), by rw [ring_hom.id_apply, restriction_of_scalars.smul_def f ⟨S⟩,
        smul_eq_mul, mul_smul, restriction_of_scalars.smul_def] },
    map_add' := λ y1 y2, linear_map.ext $ λ (s : S), by rw [linear_map.add_apply, linear_map.coe_mk,
      linear_map.coe_mk, linear_map.coe_mk, smul_add],
    map_smul' := λ s (y : Y), linear_map.ext $ λ (t : S), by simp [mul_smul] },
  naturality' := λ Y Y' g, linear_map.ext $ λ (y : Y), linear_map.ext $ λ (s : S), by simp }

/--
The natural transforamtion from the composition of coextension and restriction of scalars to
identity functor.
-/
@[simps] protected def counit' :
  coextension_of_scalars.functor f ⋙ restriction_of_scalars.functor f ⟶ 𝟭 (Module R) :=
{ app := λ X,
  { to_fun := λ g, g.to_fun (1 : S),
    map_add' := λ x1 x2, by simp [linear_map.to_fun_eq_coe],
    map_smul' := λ r (g : (restriction_of_scalars.functor f).obj
      ((coextension_of_scalars.functor f).obj X)),
    begin
      simp only [linear_map.to_fun_eq_coe, ring_hom.id_apply],
      rw [restriction_of_scalars.smul_def f, coextension_of_scalars.smul_apply, smul_eq_mul,
        one_mul, ←linear_map.map_smul, restriction_of_scalars.smul_def f ⟨S⟩, smul_eq_mul, mul_one],
    end },
  naturality' := λ X X' g, linear_map.ext $ λ h, by simp }

/--
restriction of scalars ⊣ coextension of scalars
-/
@[simps] def _root_.change_of_rings.restriction_coextension_adj :
  restriction_of_scalars.functor f ⊣ coextension_of_scalars.functor f :=
{ hom_equiv := λ Y X, ⟨hom_equiv.from_restriction_to_to_coextension f,
    hom_equiv.to_coextension_to_from_restriction f, hom_equiv.fb f, hom_equiv.bf f⟩,
  unit := restriction_coextension_adj.unit' f,
  counit := restriction_coextension_adj.counit' f,
  hom_equiv_unit' := λ Y X g, linear_map.ext $ λ y, rfl,
  hom_equiv_counit' := λ Y X g, linear_map.ext $ λ (y : Y), by simp }

end restriction_coextension_adj

namespace coextension_forget₂_adj

universes u

variables {S : Type u} [ring S] (f : ℤ →+* S)

open_locale change_of_rings

/-- A more constructive version of `Ab ⥤ Module ℤ`-/
@[simps] def Ab_to_Z_Module : AddCommGroup ⥤ Module ℤ :=
{ obj := λ X, ⟨X⟩,
  map := λ X Y g,
  { map_smul' := λ z (x : X), by rw [add_monoid_hom.to_fun_eq_coe, g.map_zsmul, ring_hom.id_apply],
    ..g },
  map_id' := λ X, fun_like.ext _ _ $ λ (x : X), rfl,
  map_comp' := λ X Y Z g h, fun_like.ext _ _ $ λ (x : X), rfl }

/--
Given a group homomorphism `g : X ⟶ Y`, define linear map `X ⟶ Hom(S, Y)` by `x ↦ (s ↦ g (s • x))`
-/
@[simps] def hom_equiv.forget₂_to_coextension {X : Module S} {Y : AddCommGroup}
  (g : (forget₂ (Module S) AddCommGroup).obj X ⟶ Y) :
  X ⟶ (Ab_to_Z_Module ⋙ coextension_of_scalars.functor f).obj Y :=
{ to_fun := λ x,
  { to_fun := λ (s : S), g (s • x : X),
    map_add' := λ (s₁ s₂ : S), by simp [add_smul],
    map_smul' := λ z (s : S),
    begin
      rw [restriction_of_scalars.smul_def f ⟨S⟩, ring_hom.id_apply, smul_eq_mul, mul_smul,
        ←g.map_zsmul],
      induction z using int.induction_on with i ih i ih,
      { rw [map_zero, zero_smul, map_zero, zero_smul, map_zero], },
      { rw [map_add, add_smul, map_add, ih, map_one, one_smul, add_smul, one_smul, map_add], },
      { rw [map_sub, sub_smul, map_one, one_smul, map_sub, ih, sub_smul, one_smul, map_sub], },
    end },
  map_add' := λ X₁ X₂, by { ext, simp },
  map_smul' := λ s x, by { ext, simp [mul_smul], } }

/--
Given linear map `g : X ⟶ Hom(S, Y)`, define `X ⟶ Y` by `x ↦ g x 1`
-/
@[simps] def hom_equiv.coextension_to_forget₂ {X : Module S} {Y : AddCommGroup}
  (g : X ⟶ (Ab_to_Z_Module ⋙ coextension_of_scalars.functor f).obj Y) :
  (forget₂ (Module S) AddCommGroup).obj X ⟶ Y :=
{ to_fun := λ (x : X), (g x).to_fun (1 : S),
  map_zero' := by simp,
  map_add' := λ (x₁ x₂ : X), by simp }

lemma hom_equiv.fb {X : Module S} {Y : AddCommGroup}
  (g : (forget₂ (Module S) AddCommGroup).obj X ⟶ Y) :
  hom_equiv.coextension_to_forget₂ f (hom_equiv.forget₂_to_coextension f g) = g :=
by { ext, simp }

lemma hom_equiv.bf {X : Module S} {Y : AddCommGroup}
  (g : X ⟶ (Ab_to_Z_Module ⋙ coextension_of_scalars.functor f).obj Y) :
  hom_equiv.forget₂_to_coextension f (hom_equiv.coextension_to_forget₂ f g) = g :=
by { ext, simp }

/--
The natural transformation from identity functor to the composition of identity to the composition
of forgetful and coextension of scalars functor.
-/
@[simps] def unit' :
  𝟭 (Module S) ⟶
  forget₂ (Module S) AddCommGroup ⋙ Ab_to_Z_Module ⋙ coextension_of_scalars.functor f :=
{ app := λ X,
  { to_fun := λ (x : X),
    { to_fun := λ (s : S), (s • x : X),
      map_add' := λ x₁ x₂, add_smul _ _ _,
      map_smul' := λ z (s : S),
      begin
        rw [ring_hom.id_apply],

        induction z using int.induction_on with i ih i ih,
        { rw [zero_smul, restriction_of_scalars.smul_def f ⟨S⟩, map_zero, zero_smul, zero_smul], },
        { rw [add_smul, add_smul, one_smul, ih, add_smul, one_smul], },
        { rw [sub_smul, sub_smul, one_smul, ih, sub_smul, one_smul], },
      end },
    map_add' := λ (x₁ x₂ : X), by { ext, simp },
    map_smul' := λ s (x : X), by { ext, simp [mul_smul], } },
  naturality' := λ X Y g, by { ext, simp, } }

/--
The natural transformation from the coextension of scalars functor to the identity functor.
-/
@[simps] def counit' :
  (Ab_to_Z_Module ⋙ coextension_of_scalars.functor f) ⋙ forget₂ (Module S) AddCommGroup ⟶
  𝟭 AddCommGroup :=
{ app := λ X,
  { to_fun := λ g, g.to_fun (1 : S),
    map_zero' := by simp,
    map_add' := λ _ _, by simp },
  naturality' := λ X Y g, by { ext, simp, } }

/--
forgetful functor ⊣ coextension of scalars
-/
def _root_.change_of_rings.coextension_forget₂_adj :
  forget₂ (Module S) AddCommGroup ⊣
  (Ab_to_Z_Module.comp $ coextension_of_scalars.functor f) :=
{ hom_equiv := λ X Y, ⟨hom_equiv.forget₂_to_coextension f, hom_equiv.coextension_to_forget₂ f,
    hom_equiv.fb f, hom_equiv.bf f⟩,
  unit := unit' f,
  counit := counit' f,
  hom_equiv_unit' := λ X Y g, by { ext, simp },
  hom_equiv_counit' := λ X Y g, by { ext, simp } }

instance : is_left_adjoint (forget₂ (Module S) AddCommGroup) :=
⟨_, change_of_rings.coextension_forget₂_adj $ algebra_map ℤ S⟩

end coextension_forget₂_adj

end change_of_rings
#lint
