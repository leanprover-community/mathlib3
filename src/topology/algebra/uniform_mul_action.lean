/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import topology.algebra.uniform_group
import topology.uniform_space.completion

/-!
# Multiplicative action on the completion of a uniform space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define typeclasses `has_uniform_continuous_const_vadd` and
`has_uniform_continuous_const_smul` and prove that a multiplicative action on `X` with uniformly
continuous `(•) c` can be extended to a multiplicative action on `uniform_space.completion X`.

In later files once the additive group structure is set up, we provide
* `uniform_space.completion.distrib_mul_action`
* `uniform_space.completion.mul_action_with_zero`
* `uniform_space.completion.module`

TODO: Generalise the results here from the concrete `completion` to any `abstract_completion`.
-/

universes u v w x y z

noncomputable theory

variables (R : Type u) (M : Type v) (N : Type w) (X : Type x) (Y : Type y)
  [uniform_space X] [uniform_space Y]

/-- An additive action such that for all `c`, the map `λ x, c +ᵥ x` is uniformly continuous. -/
class has_uniform_continuous_const_vadd [has_vadd M X] : Prop :=
(uniform_continuous_const_vadd : ∀ (c : M), uniform_continuous ((+ᵥ) c : X → X))

/-- A multiplicative action such that for all `c`, the map `λ x, c • x` is uniformly continuous. -/
@[to_additive]
class has_uniform_continuous_const_smul [has_smul M X] : Prop :=
(uniform_continuous_const_smul : ∀ (c : M), uniform_continuous ((•) c : X → X))

export has_uniform_continuous_const_vadd (uniform_continuous_const_vadd)
  has_uniform_continuous_const_smul (uniform_continuous_const_smul)

instance add_monoid.has_uniform_continuous_const_smul_nat [add_group X] [uniform_add_group X] :
  has_uniform_continuous_const_smul ℕ X :=
⟨uniform_continuous_const_nsmul⟩

instance add_group.has_uniform_continuous_const_smul_int [add_group X] [uniform_add_group X] :
  has_uniform_continuous_const_smul ℤ X :=
⟨uniform_continuous_const_zsmul⟩

/-- A `distrib_mul_action` that is continuous on a uniform group is uniformly continuous.
This can't be an instance due to it forming a loop with
`has_uniform_continuous_const_smul.to_has_continuous_const_smul` -/
lemma has_uniform_continuous_const_smul_of_continuous_const_smul [monoid R] [add_comm_group M]
  [distrib_mul_action R M] [uniform_space M] [uniform_add_group M] [has_continuous_const_smul R M] :
  has_uniform_continuous_const_smul R M :=
⟨λ r, uniform_continuous_of_continuous_at_zero (distrib_mul_action.to_add_monoid_hom M r)
  (continuous.continuous_at (continuous_const_smul r))⟩

/-- The action of `semiring.to_module` is uniformly continuous. -/
instance ring.has_uniform_continuous_const_smul [ring R] [uniform_space R]
  [uniform_add_group R] [has_continuous_mul R] : has_uniform_continuous_const_smul R R :=
has_uniform_continuous_const_smul_of_continuous_const_smul _ _

/-- The action of `semiring.to_opposite_module` is uniformly continuous. -/
instance ring.has_uniform_continuous_const_op_smul [ring R] [uniform_space R]
  [uniform_add_group R] [has_continuous_mul R] : has_uniform_continuous_const_smul Rᵐᵒᵖ R :=
has_uniform_continuous_const_smul_of_continuous_const_smul _ _

section has_smul

variable [has_smul M X]

@[priority 100, to_additive]
instance has_uniform_continuous_const_smul.to_has_continuous_const_smul
  [has_uniform_continuous_const_smul M X] : has_continuous_const_smul M X :=
⟨λ c, (uniform_continuous_const_smul c).continuous⟩

variables {M X Y}

@[to_additive] lemma uniform_continuous.const_smul [has_uniform_continuous_const_smul M X]
  {f : Y → X} (hf : uniform_continuous f) (c : M) :
  uniform_continuous (c • f) :=
(uniform_continuous_const_smul c).comp hf

/-- If a scalar action is central, then its right action is uniform continuous when its left action
is. -/
@[priority 100, to_additive "If an additive action is central, then its right action is uniform
continuous when its left action,is."]
instance has_uniform_continuous_const_smul.op [has_smul Mᵐᵒᵖ X] [is_central_scalar M X]
  [has_uniform_continuous_const_smul M X] : has_uniform_continuous_const_smul Mᵐᵒᵖ X :=
⟨mul_opposite.rec $ λ c, begin
  change uniform_continuous (λ m, mul_opposite.op c • m),
  simp_rw op_smul_eq_smul,
  exact uniform_continuous_const_smul c,
end⟩

@[to_additive] instance mul_opposite.has_uniform_continuous_const_smul
  [has_uniform_continuous_const_smul M X] : has_uniform_continuous_const_smul M Xᵐᵒᵖ :=
⟨λ c, mul_opposite.uniform_continuous_op.comp $ mul_opposite.uniform_continuous_unop.const_smul c⟩

end has_smul

@[to_additive] instance uniform_group.to_has_uniform_continuous_const_smul
  {G : Type u} [group G] [uniform_space G] [uniform_group G] :
  has_uniform_continuous_const_smul G G :=
⟨λ c, uniform_continuous_const.mul uniform_continuous_id⟩

namespace uniform_space

namespace completion

section has_smul

variable [has_smul M X]

@[to_additive] instance : has_smul M (completion X) :=
⟨λ c, completion.map ((•) c)⟩

@[to_additive] lemma smul_def (c : M) (x : completion X) : c • x = completion.map ((•) c) x := rfl

@[to_additive] instance : has_uniform_continuous_const_smul M (completion X) :=
⟨λ c, uniform_continuous_map⟩

@[to_additive] instance [has_smul N X] [has_smul M N]
  [has_uniform_continuous_const_smul M X] [has_uniform_continuous_const_smul N X]
  [is_scalar_tower M N X] : is_scalar_tower M N (completion X) :=
⟨λ m n x, begin
  have : _ = (_ : completion X → completion X) :=
    map_comp (uniform_continuous_const_smul m) (uniform_continuous_const_smul n),
  refine eq.trans _ (congr_fun this.symm x),
  exact congr_arg (λ f, completion.map f x) (by exact funext (smul_assoc _ _)),
end⟩

@[to_additive] instance [has_smul N X] [smul_comm_class M N X]
  [has_uniform_continuous_const_smul M X] [has_uniform_continuous_const_smul N X] :
  smul_comm_class M N (completion X) :=
⟨λ m n x, begin
  have hmn : m • n • x =
    (( completion.map (has_smul.smul m)) ∘ (completion.map (has_smul.smul n))) x := rfl,
  have hnm : n • m • x =
    (( completion.map (has_smul.smul n)) ∘ (completion.map (has_smul.smul m))) x := rfl,
  rw [hmn, hnm, map_comp, map_comp],
  exact congr_arg (λ f, completion.map f x) (by exact funext (smul_comm _ _)),
  repeat{ exact uniform_continuous_const_smul _},
 end⟩

@[to_additive]
instance [has_smul Mᵐᵒᵖ X] [is_central_scalar M X] : is_central_scalar M (completion X) :=
⟨λ c a, congr_arg (λ f, completion.map f a) $ by exact funext (op_smul_eq_smul c)⟩

variables {M X} [has_uniform_continuous_const_smul M X]

@[simp, norm_cast, to_additive]
lemma coe_smul (c : M) (x : X) : ↑(c • x) = (c • x : completion X) :=
(map_coe (uniform_continuous_const_smul c) x).symm

end has_smul

@[to_additive] instance [monoid M] [mul_action M X] [has_uniform_continuous_const_smul M X] :
  mul_action M (completion X) :=
{ smul := (•),
  one_smul := ext' (continuous_const_smul _) continuous_id $ λ a, by rw [← coe_smul, one_smul],
  mul_smul := λ x y, ext' (continuous_const_smul _) ((continuous_const_smul _).const_smul _) $
    λ a, by simp only [← coe_smul, mul_smul] }

end completion

end uniform_space
