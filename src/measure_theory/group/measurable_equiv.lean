/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import measure_theory.group.arithmetic

/-!
# (Scalar) multiplication and (vector) addition as measurable equivalences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the following measurable equivalences:

* `measurable_equiv.smul`: if a group `G` acts on `α` by measurable maps, then each element `c : G`
  defines a measurable automorphism of `α`;
* `measurable_equiv.vadd`: additive version of `measurable_equiv.smul`;
* `measurable_equiv.smul₀`: if a group with zero `G` acts on `α` by measurable maps, then each
  nonzero element `c : G` defines a measurable automorphism of `α`;
* `measurable_equiv.mul_left`: if `G` is a group with measurable multiplication, then left
  multiplication by `g : G` is a measurable automorphism of `G`;
* `measurable_equiv.add_left`: additive version of `measurable_equiv.mul_left`;
* `measurable_equiv.mul_right`: if `G` is a group with measurable multiplication, then right
  multiplication by `g : G` is a measurable automorphism of `G`;
* `measurable_equiv.add_right`: additive version of `measurable_equiv.mul_right`;
* `measurable_equiv.mul_left₀`, `measurable_equiv.mul_right₀`: versions of
  `measurable_equiv.mul_left` and `measurable_equiv.mul_right` for groups with zero;
* `measurable_equiv.inv`: `has_inv.inv` as a measurable automorphism
  of a group (or a group with zero);
* `measurable_equiv.neg`: negation as a measurable automorphism of an additive group.

We also deduce that the corresponding maps are measurable embeddings.

## Tags

measurable, equivalence, group action
-/

namespace measurable_equiv

variables {G G₀ α : Type*} [measurable_space G] [measurable_space G₀] [measurable_space α]
  [group G] [group_with_zero G₀] [mul_action G α] [mul_action G₀ α]
  [has_measurable_smul G α] [has_measurable_smul G₀ α]

/-- If a group `G` acts on `α` by measurable maps, then each element `c : G` defines a measurable
automorphism of `α`. -/
@[to_additive "If an additive group `G` acts on `α` by measurable maps, then each element `c : G`
defines a measurable automorphism of `α`.", simps to_equiv apply { fully_applied := ff }]
def smul (c : G) : α ≃ᵐ α :=
{ to_equiv := mul_action.to_perm c,
  measurable_to_fun := measurable_const_smul c,
  measurable_inv_fun := measurable_const_smul c⁻¹ }

@[to_additive]
lemma _root_.measurable_embedding_const_smul (c : G) : measurable_embedding ((•) c : α → α) :=
(smul c).measurable_embedding

@[simp, to_additive]
lemma symm_smul (c : G) : (smul c : α ≃ᵐ α).symm = smul c⁻¹ := ext rfl

/-- If a group with zero `G₀` acts on `α` by measurable maps, then each nonzero element `c : G₀`
defines a measurable automorphism of `α` -/
def smul₀ (c : G₀) (hc : c ≠ 0) : α ≃ᵐ α :=
measurable_equiv.smul (units.mk0 c hc)

@[simp] lemma coe_smul₀ {c : G₀} (hc : c ≠ 0) : ⇑(smul₀ c hc : α ≃ᵐ α) = (•) c := rfl

@[simp] lemma symm_smul₀ {c : G₀} (hc : c ≠ 0) :
  (smul₀ c hc : α ≃ᵐ α).symm = smul₀ c⁻¹ (inv_ne_zero hc) :=
ext rfl

lemma _root_.measurable_embedding_const_smul₀ {c : G₀} (hc : c ≠ 0) :
  measurable_embedding ((•) c : α → α) :=
(smul₀ c hc).measurable_embedding

section mul

variables [has_measurable_mul G] [has_measurable_mul G₀]

/-- If `G` is a group with measurable multiplication, then left multiplication by `g : G` is a
measurable automorphism of `G`. -/
@[to_additive "If `G` is an additive group with measurable addition, then addition of `g : G`
on the left is a measurable automorphism of `G`."]
def mul_left (g : G) : G ≃ᵐ G := smul g

@[simp, to_additive] lemma coe_mul_left (g : G) : ⇑(mul_left g) = (*) g := rfl

@[simp, to_additive] lemma symm_mul_left (g : G) : (mul_left g).symm = mul_left g⁻¹ := ext rfl

@[simp, to_additive] lemma to_equiv_mul_left (g : G) :
  (mul_left g).to_equiv = equiv.mul_left g := rfl

@[to_additive]
lemma _root_.measurable_embedding_mul_left (g : G) : measurable_embedding ((*) g) :=
(mul_left g).measurable_embedding

/-- If `G` is a group with measurable multiplication, then right multiplication by `g : G` is a
measurable automorphism of `G`. -/
@[to_additive "If `G` is an additive group with measurable addition, then addition of `g : G`
on the right is a measurable automorphism of `G`."]
def mul_right (g : G) : G ≃ᵐ G :=
{ to_equiv := equiv.mul_right g,
  measurable_to_fun := measurable_mul_const g,
  measurable_inv_fun := measurable_mul_const g⁻¹ }

@[to_additive]
lemma _root_.measurable_embedding_mul_right (g : G) : measurable_embedding (λ x, x * g) :=
(mul_right g).measurable_embedding

@[simp, to_additive] lemma coe_mul_right (g : G) : ⇑(mul_right g) = (λ x, x * g) := rfl

@[simp, to_additive] lemma symm_mul_right (g : G) : (mul_right g).symm = mul_right g⁻¹ := ext rfl

@[simp, to_additive] lemma to_equiv_mul_right (g : G) :
  (mul_right g).to_equiv = equiv.mul_right g := rfl

/-- If `G₀` is a group with zero with measurable multiplication, then left multiplication by a
nonzero element `g : G₀` is a measurable automorphism of `G₀`. -/
def mul_left₀ (g : G₀) (hg : g ≠ 0) : G₀ ≃ᵐ G₀ := smul₀ g hg

lemma _root_.measurable_embedding_mul_left₀ {g : G₀} (hg : g ≠ 0) : measurable_embedding ((*) g) :=
(mul_left₀ g hg).measurable_embedding

@[simp] lemma coe_mul_left₀ {g : G₀} (hg : g ≠ 0) : ⇑(mul_left₀ g hg) = (*) g := rfl

@[simp] lemma symm_mul_left₀ {g : G₀} (hg : g ≠ 0) :
  (mul_left₀ g hg).symm = mul_left₀ g⁻¹ (inv_ne_zero hg)  := ext rfl

@[simp] lemma to_equiv_mul_left₀ {g : G₀} (hg : g ≠ 0) :
  (mul_left₀ g hg).to_equiv = equiv.mul_left₀ g hg := rfl

/-- If `G₀` is a group with zero with measurable multiplication, then right multiplication by a
nonzero element `g : G₀` is a measurable automorphism of `G₀`. -/
def mul_right₀ (g : G₀) (hg : g ≠ 0) : G₀ ≃ᵐ G₀ :=
{ to_equiv := equiv.mul_right₀ g hg,
  measurable_to_fun := measurable_mul_const g,
  measurable_inv_fun := measurable_mul_const g⁻¹ }

lemma _root_.measurable_embedding_mul_right₀ {g : G₀} (hg : g ≠ 0) :
  measurable_embedding (λ x, x * g) :=
(mul_right₀ g hg).measurable_embedding

@[simp] lemma coe_mul_right₀ {g : G₀} (hg : g ≠ 0) : ⇑(mul_right₀ g hg) = λ x, x * g := rfl

@[simp] lemma symm_mul_right₀ {g : G₀} (hg : g ≠ 0) :
  (mul_right₀ g hg).symm = mul_right₀ g⁻¹ (inv_ne_zero hg)  := ext rfl

@[simp] lemma to_equiv_mul_right₀ {g : G₀} (hg : g ≠ 0) :
  (mul_right₀ g hg).to_equiv = equiv.mul_right₀ g hg := rfl

end mul

/-- Inversion as a measurable automorphism of a group or group with zero. -/
@[to_additive "Negation as a measurable automorphism of an additive group.",
  simps to_equiv apply { fully_applied := ff }]
def inv (G) [measurable_space G] [has_involutive_inv G] [has_measurable_inv G] : G ≃ᵐ G :=
{ to_equiv := equiv.inv G,
  measurable_to_fun := measurable_inv,
  measurable_inv_fun := measurable_inv }

@[simp, to_additive]
lemma symm_inv {G} [measurable_space G] [has_involutive_inv G] [has_measurable_inv G] :
  (inv G).symm = inv G := rfl

/-- `equiv.div_right` as a `measurable_equiv`. -/
@[to_additive /-" `equiv.sub_right` as a `measurable_equiv` "-/]
def div_right [has_measurable_mul G] (g : G) : G ≃ᵐ G :=
{ to_equiv := equiv.div_right g,
  measurable_to_fun := measurable_div_const' g,
  measurable_inv_fun := measurable_mul_const g }

/-- `equiv.div_left` as a `measurable_equiv` -/
@[to_additive /-" `equiv.sub_left` as a `measurable_equiv` "-/]
def div_left [has_measurable_mul G] [has_measurable_inv G] (g : G) : G ≃ᵐ G :=
{ to_equiv := equiv.div_left g,
  measurable_to_fun := measurable_id.const_div g,
  measurable_inv_fun := measurable_inv.mul_const g }

end measurable_equiv
