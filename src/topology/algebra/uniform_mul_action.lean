/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import topology.algebra.group_completion

/-!
# Multiplicative action on the completion of a uniform space

In this file we define typeclasses `has_uniform_continuous_const_vadd` and
`has_uniform_continuous_const_smul` and prove that a multiplicative action on `X` with uniformly
continuous `(•) c` can be extended to a multiplicative action on `uniform_space.completion X`. We
also provide similar instances `distrib_mul_action`, `mul_action_with_zero`, and `module`.
-/

universes u v w x y z

noncomputable theory

variables (R : Type u) (M : Type v) (N : Type w) (X : Type x) (Y : Type y)
  [uniform_space X] [uniform_space Y]

/-- An additive action such that for all `c`, the map `λ x, c +ᵥ x` is uniformly continuous. -/
class has_uniform_continuous_const_vadd [uniform_space X] [has_vadd M X] : Prop :=
(uniform_continuous_const_vadd : ∀ (c : M), uniform_continuous ((+ᵥ) c : X → X))

/-- A multiplicative action such that for all `c`, the map `λ x, c • x` is uniformly continuous. -/
@[to_additive]
class has_uniform_continuous_const_smul [uniform_space X] [has_scalar M X] : Prop :=
(uniform_continuous_const_smul : ∀ (c : M), uniform_continuous ((•) c : X → X))

export has_uniform_continuous_const_vadd (uniform_continuous_const_vadd)
  has_uniform_continuous_const_smul (uniform_continuous_const_smul)

section has_scalar

variable [has_scalar M X]

@[priority 100, to_additive]
instance has_uniform_continuous_const_smul.to_has_continuous_const_smul
  [has_uniform_continuous_const_smul M X] : has_continuous_const_smul M X :=
⟨λ c, (uniform_continuous_const_smul c).continuous⟩

lemma uniform_continuous.const_smul [has_uniform_continuous_const_smul M X]
  {f : Y → X} (hf : uniform_continuous f) (c : M) :
  uniform_continuous (c • f) :=
(uniform_continuous_const_smul c).comp hf

/-- If a scalar is central, then its right action is uniform continuous when its left action is. -/
@[priority 100]
instance has_uniform_continuous_const_smul.op [has_scalar Mᵐᵒᵖ X] [is_central_scalar M X]
  [has_uniform_continuous_const_smul M X] : has_uniform_continuous_const_smul Mᵐᵒᵖ X :=
⟨mul_opposite.rec $ λ c, begin
  change uniform_continuous (λ m, mul_opposite.op c • m),
  simp_rw op_smul_eq_smul,
  exact uniform_continuous_const_smul c,
end⟩

end has_scalar

@[to_additive] instance uniform_group.to_has_uniform_continuous_const_smul
  {G : Type u} [group G] [uniform_space G] [uniform_group G] :
  has_uniform_continuous_const_smul G G :=
⟨λ c, uniform_continuous_const.mul uniform_continuous_id⟩

namespace uniform_space

namespace completion

section has_scalar

variable [has_scalar M X]

@[to_additive has_vadd] instance : has_scalar M (completion X) :=
⟨λ c, completion.map ((•) c)⟩

@[to_additive] instance : has_uniform_continuous_const_smul M (completion X) :=
⟨λ c, uniform_continuous_map⟩

instance [has_scalar Mᵐᵒᵖ X] [is_central_scalar M X] : is_central_scalar M (completion X) :=
⟨λ c a, congr_arg (λ f, completion.map f a) $ by exact funext (op_smul_eq_smul c)⟩

variables {M X} [has_uniform_continuous_const_smul M X]

@[simp, norm_cast, to_additive]
lemma coe_smul (c : M) (x : X) : ↑(c • x) = (c • x : completion X) :=
(map_coe (uniform_continuous_const_smul c) x).symm

end has_scalar

@[to_additive] instance [monoid M] [mul_action M X] [has_uniform_continuous_const_smul M X] :
  mul_action M (completion X) :=
{ smul := (•),
  one_smul := ext' (continuous_const_smul _) continuous_id $ λ a, by rw [← coe_smul, one_smul],
  mul_smul := λ x y, ext' (continuous_const_smul _) ((continuous_const_smul _).const_smul _) $
    λ a, by simp only [← coe_smul, mul_smul] }

instance [monoid_with_zero M] [has_zero X] [mul_action_with_zero M X]
  [has_uniform_continuous_const_smul M X] :
  mul_action_with_zero M (completion X) :=
{ smul := (•),
  smul_zero := λ r, by rw [← coe_zero, ← coe_smul, mul_action_with_zero.smul_zero r],
  zero_smul := ext' (continuous_const_smul _) continuous_const $ λ a,
    by rw [← coe_smul, zero_smul, coe_zero],
  .. completion.mul_action M X }

instance [monoid M] [add_group N] [distrib_mul_action M N] [uniform_space N]
  [uniform_add_group N] [has_uniform_continuous_const_smul M N] :
  distrib_mul_action M (completion N) :=
{ smul := (•),
  smul_add := λ r x y, induction_on₂ x y
    (is_closed_eq ((continuous_fst.add continuous_snd).const_smul _)
      ((continuous_fst.const_smul _).add (continuous_snd.const_smul _)))
    (λ a b, by simp only [← coe_add, ← coe_smul, smul_add]),
  smul_zero := λ r, by rw [← coe_zero, ← coe_smul, smul_zero r],
  .. completion.mul_action M N }

instance [semiring R] [add_comm_group M] [module R M] [uniform_space M] [uniform_add_group M]
  [has_uniform_continuous_const_smul R M] : module R (completion M) :=
{ smul := (•),
  add_smul := λ a b, ext' (continuous_const_smul _)
    ((continuous_const_smul _).add (continuous_const_smul _)) $ λ x, by { norm_cast, rw add_smul },
  .. completion.distrib_mul_action R M, .. completion.mul_action_with_zero R M }

end completion

end uniform_space
