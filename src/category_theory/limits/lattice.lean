/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Justus Springer
-/
import category_theory.category.preorder
import category_theory.limits.shapes.finite_limits
import order.complete_lattice

universes u

open category_theory
open category_theory.limits

namespace category_theory.limits.complete_lattice

section semilattice

variables {α : Type u}

variables {J : Type u} [small_category J] [fin_category J]

/--
The limit cone over any functor from a finite diagram into a `semilattice_inf_top`.
-/
def finite_limit_cone [semilattice_inf_top α] (F : J ⥤ α) : limit_cone F :=
{ cone :=
  { X := finset.univ.inf F.obj,
    π := { app := λ j, hom_of_le (finset.inf_le (fintype.complete _)) } },
  is_limit := { lift := λ s, hom_of_le (finset.le_inf (λ j _, (s.π.app j).down.down)) } }

/--
The colimit cocone over any functor from a finite diagram into a `semilattice_sup_bot`.
-/
def finite_colimit_cocone [semilattice_sup_bot α] (F : J ⥤ α) : colimit_cocone F :=
{ cocone :=
  { X := finset.univ.sup F.obj,
    ι := { app := λ i, hom_of_le (finset.le_sup (fintype.complete _)) } },
  is_colimit := { desc := λ s, hom_of_le (finset.sup_le (λ j _, (s.ι.app j).down.down)) } }

@[priority 100] -- see Note [lower instance priority]
instance has_finite_limits_of_semilattice_inf_top [semilattice_inf_top α] :
  has_finite_limits α :=
⟨λ J 𝒥₁ 𝒥₂, by exactI { has_limit := λ F, has_limit.mk (finite_limit_cone F) }⟩

@[priority 100] -- see Note [lower instance priority]
instance has_finite_colimits_of_semilattice_sup_bot [semilattice_sup_bot α] :
  has_finite_colimits α :=
⟨λ J 𝒥₁ 𝒥₂, by exactI { has_colimit := λ F, has_colimit.mk (finite_colimit_cocone F) }⟩

/--
The limit of a functor from a finite diagram into a `semilattice_inf_top` is the infimum of the
objects in the image.
-/
lemma finite_limit_eq_finset_univ_inf [semilattice_inf_top α] (F : J ⥤ α) :
  limit F = finset.univ.inf F.obj :=
(is_limit.cone_point_unique_up_to_iso (limit.is_limit F)
  (finite_limit_cone F).is_limit).to_eq

/--
The colimit of a functor from a finite diagram into a `semilattice_sup_bot` is the supremum of the
objects in the image.
-/
lemma finite_colimit_eq_finset_univ_sup [semilattice_sup_bot α] (F : J ⥤ α) :
  colimit F = finset.univ.sup F.obj :=
(is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit F)
  (finite_colimit_cocone F).is_colimit).to_eq

/--
A finite product in the category of a `semilattice_inf_top` is the same as the infimum.
-/
lemma finite_product_eq_finset_inf [semilattice_inf_top α] {ι : Type u} [decidable_eq ι]
  [fintype ι] (f : ι → α) : (∏ f) = (fintype.elems ι).inf f :=
(is_limit.cone_point_unique_up_to_iso (limit.is_limit _)
  (finite_limit_cone (discrete.functor f)).is_limit).to_eq

/--
A finite coproduct in the category of a `semilattice_sup_bot` is the same as the supremum.
-/
lemma finite_coproduct_eq_finset_sup [semilattice_sup_bot α] {ι : Type u} [decidable_eq ι]
  [fintype ι] (f : ι → α) : (∐ f) = (fintype.elems ι).sup f :=
(is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _)
  (finite_colimit_cocone (discrete.functor f)).is_colimit).to_eq

/--
The binary product in the category of a `semilattice_inf_top` is the same as the infimum.
-/
@[simp]
lemma prod_eq_inf [semilattice_inf_top α] (x y : α) : limits.prod x y = x ⊓ y :=
calc limits.prod x y = limit (pair x y) : rfl
... = finset.univ.inf (pair x y).obj : by rw finite_limit_eq_finset_univ_inf (pair x y)
... = x ⊓ (y ⊓ ⊤) : rfl -- Note: finset.inf is realized as a fold, hence the definitional equality
... = x ⊓ y : by rw inf_top_eq

/--
The binary coproduct in the category of a `semilattice_sup_bot` is the same as the supremum.
-/
@[simp]
lemma coprod_eq_sup [semilattice_sup_bot α] (x y : α) : limits.coprod x y = x ⊔ y :=
calc limits.coprod x y = colimit (pair x y) : rfl
... = finset.univ.sup (pair x y).obj : by rw finite_colimit_eq_finset_univ_sup (pair x y)
... = x ⊔ (y ⊔ ⊥) : rfl -- Note: finset.sup is realized as a fold, hence the definitional equality
... = x ⊔ y : by rw sup_bot_eq

/--
The pullback in the category of a `semilattice_inf_top` is the same as the infimum over the objects.
-/
@[simp]
lemma pullback_eq_inf [semilattice_inf_top α] {x y z : α} (f : x ⟶ z) (g : y ⟶ z) :
  pullback f g = x ⊓ y :=
calc pullback f g = limit (cospan f g) : rfl
... = finset.univ.inf (cospan f g).obj : by rw finite_limit_eq_finset_univ_inf
... = z ⊓ (x ⊓ (y ⊓ ⊤)) : rfl
... = z ⊓ (x ⊓ y) : by rw inf_top_eq
... = x ⊓ y : inf_eq_right.mpr (inf_le_of_left_le f.le)

/--
The pushout in the category of a `semilattice_sup_bot` is the same as the supremum over the objects.
-/
@[simp]
lemma pushout_eq_sup [semilattice_sup_bot α] (x y z : α) (f : z ⟶ x) (g : z ⟶ y) :
  pushout f g = x ⊔ y :=
calc pushout f g = colimit (span f g) : rfl
... = finset.univ.sup (span f g).obj : by rw finite_colimit_eq_finset_univ_sup
... = z ⊔ (x ⊔ (y ⊔ ⊥)) : rfl
... = z ⊔ (x ⊔ y) : by rw sup_bot_eq
... = x ⊔ y : sup_eq_right.mpr (le_sup_of_le_left f.le)

end semilattice

variables {α : Type u} [complete_lattice α]
variables {J : Type u} [small_category J]

/--
The limit cone over any functor into a complete lattice.
-/
def limit_cone (F : J ⥤ α) : limit_cone F :=
{ cone :=
  { X := infi F.obj,
    π :=
    { app := λ j, hom_of_le (complete_lattice.Inf_le _ _ (set.mem_range_self _)) } },
  is_limit :=
  { lift := λ s, hom_of_le (complete_lattice.le_Inf _ _
    begin rintros _ ⟨j, rfl⟩, exact (s.π.app j).le, end) } }

/--
The colimit cocone over any functor into a complete lattice.
-/
def colimit_cocone (F : J ⥤ α) : colimit_cocone F :=
{ cocone :=
  { X := supr F.obj,
    ι :=
    { app := λ j, hom_of_le (complete_lattice.le_Sup _ _ (set.mem_range_self _)) } },
  is_colimit :=
  { desc := λ s, hom_of_le (complete_lattice.Sup_le _ _
    begin rintros _ ⟨j, rfl⟩, exact (s.ι.app j).le, end) } }

-- It would be nice to only use the `Inf` half of the complete lattice, but
-- this seems not to have been described separately.
@[priority 100] -- see Note [lower instance priority]
instance has_limits_of_complete_lattice : has_limits α :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit.mk (limit_cone F) } }

@[priority 100] -- see Note [lower instance priority]
instance has_colimits_of_complete_lattice : has_colimits α :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk (colimit_cocone F) } }

/--
The limit of a functor into a complete lattice is the infimum of the objects in the image.
-/
lemma limit_eq_infi (F : J ⥤ α) : limit F = infi F.obj :=
(is_limit.cone_point_unique_up_to_iso (limit.is_limit F)
  (limit_cone F).is_limit).to_eq

/--
The colimit of a functor into a complete lattice is the supremum of the objects in the image.
-/
lemma colimit_eq_supr (F : J ⥤ α) : colimit F = supr F.obj :=
(is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit F)
  (colimit_cocone F).is_colimit).to_eq

end category_theory.limits.complete_lattice
