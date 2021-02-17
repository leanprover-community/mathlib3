/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import linear_algebra.dimension
import ring_theory.noetherian
import category_theory.adjunction.limits
import ring_theory.algebra_tower

namespace module
open function (injective)
open linear_map (lsmul)

open_locale tensor_product

/-- An `R`-module `M` is flat if for all finitely generated ideals `I` of `R`,
the map `I ⊗ M →ₗ M` is injective. -/
@[class]
def flat (R M : Type*) [comm_ring R] [add_comm_group M] [module R M] : Prop :=
∀ ⦃I : ideal R⦄ (hI : I.fg), injective (tensor_product.lift ((lsmul R M).comp I.subtype))

namespace flat

open tensor_product

instance self (R : Type*) [comm_ring R] : flat R R :=
begin
  intros I hI,
  -- rw ← equiv.injective_comp (tensor_product.rid R I).symm.to_equiv,
  -- convert subtype.coe_injective using 1,
  -- ext x,
  -- simp only [function.comp_app, linear_equiv.coe_to_equiv, rid_symm_apply, comp_apply,
  --   mul_one, lift.tmul, subtype_apply, algebra.id.smul_eq_mul, lsmul_apply]
end

end flat

end module
