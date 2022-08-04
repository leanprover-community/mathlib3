/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebra.category.Module.basic

namespace category.Module

namespace restrict_scalars

universes u₁ u₂

variables {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)
variable (M : Module S)

/-- Any `S`-module M is also an `R`-module via a ring homomorphism `f : R ⟶ S` by defining
    `r • m := f r • m` (`module.comp_hom`). This is called restriction of scalars. -/
def obj' : Module R :=
{ carrier := M,
  is_add_comm_group := infer_instance,
  is_module := module.comp_hom M f }

section
include f

/-- The `R`-scalar multiplication on `S`-module M defined by `r • m := f r • m` -/
protected def has_smul : has_smul R M :=
(module.comp_hom M f).to_has_smul

end

localized "notation r ` r•[` f `] ` :=
  @@has_smul.smul (restrict_scalars.has_smul f _) r"
  in change_of_rings

@[simp] lemma smul_def (r : R) (m : M) : r r•[f] m = f r • m := rfl

/--
Given an `S`-linear map `g : M → M'` between `S`-modules, `g` is also `R`-linear between `M` and
`M'` by means of restriction of scalars.
-/
@[simps] def map' {M M' : Module S} (g : M ⟶ M') :
  obj' f M ⟶ obj' f M' :=
{ map_smul' := λ r (x : M), by simp,
  ..g }

/--
The restriction of scalars operation is functorial. For any `f : R →+* S` a ring homomorphism,
* an `S`-module `M` can be considered as `R`-module by `r • m = f r • m`
* an `S`-linear map is also `R`-linear
-/
@[simps] protected def functor : Module S ⥤ Module R :=
{ obj := obj' f,
  map := λ _ _, map' f,
  map_id' := λ _, linear_map.ext $ λ m, rfl,
  map_comp' := λ _ _ _ g h, linear_map.ext $ λ m, rfl }

end restrict_scalars


end category.Module
