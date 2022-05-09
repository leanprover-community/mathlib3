/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Module.epi_mono
import linear_algebra.pi

/-!
# The concrete products in the category of modules are products in the categorical sense.
-/

open category_theory
open category_theory.limits

universes u v w

namespace Module
variables {R : Type u} [ring R]

variables {ι : Type v} (Z : ι → Module.{max v w} R)

/-- The product cone induced by the concrete product. -/
def product_cone : fan Z :=
fan.mk (Module.of R (Π i : ι, Z i)) (λ i, (linear_map.proj i : (Π i : ι, Z i) →ₗ[R] Z i))

/-- The concrete product cone is limiting. -/
def product_cone_is_limit : is_limit (product_cone Z) :=
{ lift := λ s, (linear_map.pi s.π.app : s.X →ₗ[R] (Π i : ι, Z i)),
  fac' := by tidy,
  uniq' := λ s m w, by { ext x i, exact linear_map.congr_fun (w i) x, }, }

-- While we could use this to construct a `has_products (Module R)` instance,
-- we already have `has_limits (Module R)` in `algebra.category.Module.limits`.

variables [has_product Z]

/--
The categorical product of a family of objects in `Module`
agrees with the usual module-theoretical product.
-/
noncomputable def pi_iso_pi :
  ∏ Z ≅ Module.of R (Π i, Z i) :=
limit.iso_limit_cone ⟨_, product_cone_is_limit Z⟩

-- We now show this isomorphism commutes with the inclusion of the kernel into the source.

@[simp, elementwise] lemma pi_iso_pi_inv_kernel_ι (i : ι) :
  (pi_iso_pi Z).inv ≫ pi.π Z i = (linear_map.proj i : (Π i : ι, Z i) →ₗ[R] Z i) :=
limit.iso_limit_cone_inv_π _ _

@[simp, elementwise] lemma pi_iso_pi_hom_ker_subtype (i : ι) :
  (pi_iso_pi Z).hom ≫ (linear_map.proj i : (Π i : ι, Z i) →ₗ[R] Z i) = pi.π Z i :=
is_limit.cone_point_unique_up_to_iso_inv_comp _ (limit.is_limit _) _

end Module
