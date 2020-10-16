/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yury Kudryashov
-/
import category_theory.concrete_category.basic
import category_theory.concrete_category.bundled

/-!
# Category instances for algebraic structures that use bundled homs.

Many algebraic structures in Lean initially used unbundled homs (e.g. a bare function between types,
along with an `is_monoid_hom` typeclass), but the general trend is towards using bundled homs.

This file provides a basic infrastructure to define concrete categories using bundled homs, and
define forgetful functors between them.
-/

universes u

namespace category_theory

variables {c : Type u → Type u} (hom : Π ⦃α β : Type u⦄ (Iα : c α) (Iβ : c β), Type u)

/-- Class for bundled homs. Note that the arguments order follows that of lemmas for `monoid_hom`.
This way we can use `⟨@monoid_hom.to_fun, @monoid_hom.id ...⟩` in an instance. -/
structure bundled_hom :=
(to_fun : Π {α β : Type u} (Iα : c α) (Iβ : c β), hom Iα Iβ → α → β)
(id : Π {α : Type u} (I : c α), hom I I)
(comp : Π {α β γ : Type u} (Iα : c α) (Iβ : c β) (Iγ : c γ),
  hom Iβ Iγ → hom Iα Iβ → hom Iα Iγ)
(hom_ext : ∀ {α β : Type u} (Iα : c α) (Iβ : c β), function.injective (to_fun Iα Iβ) . obviously)
(id_to_fun : ∀ {α : Type u} (I : c α), to_fun I I (id I) = _root_.id . obviously)
(comp_to_fun : ∀ {α β γ : Type u} (Iα : c α) (Iβ : c β) (Iγ : c γ)
  (f : hom Iα Iβ) (g : hom Iβ Iγ),
  to_fun Iα Iγ (comp Iα Iβ Iγ g f) = (to_fun Iβ Iγ g) ∘ (to_fun Iα Iβ f) . obviously)

attribute [class] bundled_hom

attribute [simp] bundled_hom.id_to_fun bundled_hom.comp_to_fun

namespace bundled_hom

variable [𝒞 : bundled_hom hom]
include 𝒞

/-- Every `@bundled_hom c _` defines a category with objects in `bundled c`.

This instance generates the type-class problem `bundled_hom ?m` (which is why this is marked as
`[nolint]`). Currently that is not a problem, as there are almost no instances of `bundled_hom`. -/
@[nolint dangerous_instance] instance category : category (bundled c) :=
by refine
{ hom := λ X Y, @hom X Y X.str Y.str,
  id := λ X, @bundled_hom.id c hom 𝒞 X X.str,
  comp := λ X Y Z f g, @bundled_hom.comp c hom 𝒞 X Y Z X.str Y.str Z.str g f,
  comp_id' := _,
  id_comp' := _,
  assoc' := _};
intros; apply 𝒞.hom_ext;
  simp only [𝒞.id_to_fun, 𝒞.comp_to_fun, function.left_id, function.right_id]

/-- A category given by `bundled_hom` is a concrete category.

This instance generates the type-class problem `bundled_hom ?m` (which is why this is marked as
`[nolint]`). Currently that is not a problem, as there are almost no instances of `bundled_hom`. -/
@[nolint dangerous_instance] instance : concrete_category.{u} (bundled c) :=
{ forget := { obj := λ X, X,
              map := λ X Y f, 𝒞.to_fun X.str Y.str f,
              map_id' := λ X, 𝒞.id_to_fun X.str,
              map_comp' := by intros; erw 𝒞.comp_to_fun; refl },
  forget_faithful := { map_injective' := by intros; apply 𝒞.hom_ext } }

variables {hom}
local attribute [instance] concrete_category.has_coe_to_fun

/-- A version of `has_forget₂.mk'` for categories defined using `@bundled_hom`. -/
def mk_has_forget₂ {d : Type u → Type u} {hom_d : Π ⦃α β : Type u⦄ (Iα : d α) (Iβ : d β), Type u}
  [bundled_hom hom_d] (obj : Π ⦃α⦄, c α → d α)
  (map : Π {X Y : bundled c}, (X ⟶ Y) → ((bundled.map obj X) ⟶ (bundled.map obj Y)))
  (h_map : ∀ {X Y : bundled c} (f : X ⟶ Y), (map f : X → Y) = f)
  : has_forget₂ (bundled c) (bundled d) :=
has_forget₂.mk'
  (bundled.map @obj)
  (λ _, rfl)
  @map
  (by intros; apply heq_of_eq; apply h_map)

variables {d : Type u → Type u}
variables (hom)

section
omit 𝒞
/--
The `hom` corresponding to first forgetting along `F`, then taking the `hom` associated to `c`.

For typical usage, see the construction of `CommMon` from `Mon`.
-/
@[reducible] def map_hom (F : Π {α}, d α → c α) : Π ⦃α β : Type u⦄ (Iα : d α) (Iβ : d β), Type u :=
λ α β iα iβ, hom (F iα) (F iβ)
end

/--
Construct the `bundled_hom` induced by a map between type classes.
This is useful for building categories such as `CommMon` from `Mon`.
-/
def map (F : Π {α}, d α → c α) : bundled_hom (map_hom hom @F) :=
{ to_fun := λ α β iα iβ f, 𝒞.to_fun (F iα) (F iβ) f,
  id := λ α iα, 𝒞.id (F iα),
  comp := λ α β γ iα iβ iγ f g, 𝒞.comp (F iα) (F iβ) (F iγ) f g,
  hom_ext := λ α β iα iβ f g h, 𝒞.hom_ext (F iα) (F iβ) h }

section
omit 𝒞
/--
We use the empty `parent_projection` class to label functions like `comm_monoid.to_monoid`,
which we would like to use to automatically construct `bundled_hom` instances from.

Once we've set up `Mon` as the category of bundled monoids,
this allows us to set up `CommMon` by defining an instance
```instance : parent_projection (comm_monoid.to_monoid) := ⟨⟩```
-/
class parent_projection (F : Π {α}, d α → c α)
end

@[nolint unused_arguments] -- The `parent_projection` typeclass is just a marker, so won't be used.
instance bundled_hom_of_parent_projection (F : Π {α}, d α → c α) [parent_projection @F] :
  bundled_hom (map_hom hom @F) :=
map hom @F

instance forget₂ (F : Π {α}, d α → c α) [parent_projection @F] :
  has_forget₂ (bundled d) (bundled c) :=
{ forget₂ :=
  { obj := λ X, ⟨X, F X.2⟩,
    map := λ X Y f, f } }

instance forget₂_full (F : Π {α}, d α → c α) [parent_projection @F] :
  full (forget₂ (bundled d) (bundled c)) :=
{ preimage := λ X Y f, f }

end bundled_hom

end category_theory
