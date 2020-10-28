/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import data.fintype.basic
import data.fin
import category_theory.concrete_category.bundled
import category_theory.concrete_category
import category_theory.full_subcategory
import category_theory.skeletal

/-!
# The category of finite types.

We define the category of finite types, denoted `FinType` as
(bundled) types with a `fintype` instance.

We also define `FinType.Skeleton`, the standard skeleton of `FinType` whose objects are `fin n`
for `n : ℕ`. We prove that the obvious inclusion functor `FinType.Skeleton ⥤ FinType` is an
equivalence of categories in `FinType.Skeleton.equivalence`.
-/

open_locale classical
open category_theory

/-- The category of finite types. -/
def FinType := bundled fintype

namespace FinType

instance : inhabited FinType := ⟨⟨pempty⟩⟩
instance : has_coe_to_sort FinType := ⟨Type*, bundled.α⟩
instance {X : FinType} : fintype X := X.2

instance : category FinType :=
{ hom := λ X Y, X → Y,
  id := λ _, id,
  comp := λ _ _ _ f g, g ∘ f }

/-- The fully faithful embedding of `FinType` into the category of types. -/
def incl : FinType ⥤ Type* :=
{ obj := λ X, X,
  map := λ _ _ f, f }

instance : full incl := { preimage := λ _ _ f, f }
instance : faithful incl := {}
instance : concrete_category FinType := ⟨incl⟩

/-- The "standard" skeleton for `FinType`. -/
def Skeleton := ℕ

namespace Skeleton

/-- Given any natural number `n`, this creates the associated object of `FinType.Skeleton`. -/
def mk : ℕ → Skeleton := id

instance : inhabited Skeleton := ⟨mk 0⟩

/-- Given any object of `FinType.Skeleton`, this returns the associated natural number. -/
def to_nat : Skeleton → ℕ := id

instance : category Skeleton :=
{ hom := λ X Y, fin X → fin Y,
  id := λ _, id,
  comp := λ _ _ _ f g, g ∘ f }

lemma is_skeletal : skeletal Skeleton := λ X Y ⟨h⟩, fin.equiv_iff_eq.mp $ nonempty.intro $
{ to_fun := h.1,
  inv_fun := h.2,
  left_inv := λ _, by {change (h.hom ≫ h.inv) _ = _, simpa},
  right_inv := λ _, by {change (h.inv ≫ h.hom) _ = _, simpa} }

/-- The canonical fully faithful embedding of `FinType.Skeleton` into `FinType`. -/
def incl : Skeleton ⥤ FinType :=
{ obj := λ X, { α := fin X },
  map := λ _ _ f, f }

instance : full incl := { preimage := λ _ _ f, f }
instance : faithful incl := {}
noncomputable instance : ess_surj incl :=
{ obj_preimage := λ X, fintype.card X,
  iso' := λ X,
  let F := trunc.out (fintype.equiv_fin X) in
  { hom := F.symm,
    inv := F,
    hom_inv_id' := by { change F.to_fun ∘ F.inv_fun = _, simpa },
    inv_hom_id' := by { change F.inv_fun ∘ F.to_fun = _, simpa } } }

noncomputable instance : is_equivalence incl :=
equivalence.equivalence_of_fully_faithfully_ess_surj _

/-- The equivalence between `FinType.Skeleton` and `FinType`. -/
noncomputable def equivalence : Skeleton ≌ FinType := incl.as_equivalence

@[simp] lemma incl_mk_nat_card (n : ℕ) : fintype.card (incl.obj (mk n)) = n := finset.card_fin n

end Skeleton

end FinType
