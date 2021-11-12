/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import measure_theory.group.arithmetic

/-!
# (Scalar) multiplication and (vector) addition as measurable equivalences

In this file we define the following measurable equivalences:

* `measurable_equiv.smul`: if group `G` acts on `α` by measurable maps, then each element `c : G`
  defines a measurable automorphism of `α`;
* `measurable_equiv.vadd`: additive version of `measurable_equiv.smul`;
* `measurable_equiv.smul₀`: if group with zero `G` acts on `α` by measurable maps, then each
  nonzero element `c : G` defines a measurable automorphism of `α`;
* `measurable_equiv.mul_left`: if `G` is a group with measurable multiplication, then left
  multiplication by `g : G` is a measurable automorphism of `G`;
* `measurable_equiv.add_left`: additive version of `measurable_equiv.mul_left`;
* `measurable_equiv.mul_right`: if `G` is a group with measurable multiplication, then right
  multiplication by `g : G` is a measurable automorphism of `G`;
* `measurable_equiv.add_right`: additive version of `measurable_equiv.mul_right`.

## Tags

measurable, equivalence, group action
-/

namespace measurable_equiv

variables {G α : Type*} [measurable_space G] [measurable_space α]

/-- If group `G` acts on `α` by measurable maps, then each element `c : G` defines a measurable
automorphism of `α`. -/
@[to_additive "If additive group `G` acts on `α` by measurable maps, then each element `c : G`
defines a measurable automorphism of `α`.", simps]
def smul [group G] [mul_action G α] [has_measurable_smul G α] (c : G) : α ≃ᵐ α :=
{ to_equiv := mul_action.to_perm c,
  measurable_to_fun := measurable_const_smul c,
  measurable_inv_fun := measurable_const_smul c⁻¹ }

/-- If group with zero `G` acts on `α` by measurable maps, then each nonzero element `c : G` defines
a measurable automorphism of `α` -/
def smul₀ [group_with_zero G] [mul_action G α] [has_measurable_smul G α] (c : G) (hc : c ≠ 0) :
  α ≃ᵐ α :=
measurable_equiv.smul (units.mk0 c hc)

/-- If `G` is a group with measurable multiplication, then left multiplication by `g : G` is a
measurable automorphism of `G`. -/
@[to_additive "If `G` is an additive group with measurable addition, then addition of `g : G`
on the left is a measurable automorphism of `G`."]
def mul_left [group G] [has_measurable_mul G] (g : G) : G ≃ᵐ G := smul g

/-- If `G` is a group with measurable multiplication, then right multiplication by `g : G` is a
measurable automorphism of `G`. -/
@[to_additive "If `G` is an additive group with measurable addition, then addition of `g : G`
on the right is a measurable automorphism of `G`."]
def mul_right [group G] [has_measurable_mul G] (g : G) : G ≃ᵐ G :=
{ to_equiv := equiv.mul_right g,
  measurable_to_fun := measurable_mul_const g,
  measurable_inv_fun := measurable_mul_const g⁻¹ }

end measurable_equiv
