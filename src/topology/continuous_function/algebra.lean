/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Nicolò Cavalleri
-/
import algebra.algebra.pi
import algebra.periodic
import algebra.algebra.subalgebra.basic
import algebra.star.star_alg_hom
import tactic.field_simp
import topology.algebra.module.basic
import topology.algebra.infinite_sum.basic
import topology.algebra.star
import topology.algebra.uniform_group
import topology.continuous_function.ordered
import topology.uniform_space.compact_convergence

/-!
# Algebraic structures over continuous functions

In this file we define instances of algebraic structures over the type `continuous_map α β`
(denoted `C(α, β)`) of **bundled** continuous maps from `α` to `β`. For example, `C(α, β)`
is a group when `β` is a group, a ring when `β` is a ring, etc.

For each type of algebraic structure, we also define an appropriate subobject of `α → β`
with carrier `{ f : α → β | continuous f }`. For example, when `β` is a group, a subgroup
`continuous_subgroup α β` of `α → β` is constructed with carrier `{ f : α → β | continuous f }`.

Note that, rather than using the derived algebraic structures on these subobjects
(for example, when `β` is a group, the derived group structure on `continuous_subgroup α β`),
one should use `C(α, β)` with the appropriate instance of the structure.
-/

local attribute [elab_simple] continuous.comp

namespace continuous_functions

variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]
variables {f g : {f : α → β | continuous f }}

instance : has_coe_to_fun {f : α → β | continuous f} (λ _, α → β) :=  ⟨subtype.val⟩

end continuous_functions

namespace continuous_map
variables {α : Type*} {β : Type*} {γ : Type*}
variables [topological_space α] [topological_space β] [topological_space γ]

/- ### "mul" and "add" -/

@[to_additive]
instance has_mul [has_mul β] [has_continuous_mul β] : has_mul C(α, β) :=
⟨λ f g, ⟨f * g, continuous_mul.comp (f.continuous.prod_mk g.continuous : _)⟩⟩

@[simp, norm_cast, to_additive]
lemma coe_mul [has_mul β] [has_continuous_mul β] (f g : C(α, β)) : ⇑(f * g) = f * g := rfl

@[simp, to_additive]
lemma mul_apply [has_mul β] [has_continuous_mul β] (f g : C(α, β)) (x : α) :
  (f * g) x = f x * g x := rfl

@[simp, to_additive] lemma mul_comp [has_mul γ] [has_continuous_mul γ]
  (f₁ f₂ : C(β, γ)) (g : C(α, β)) :
  (f₁ * f₂).comp g = f₁.comp g * f₂.comp g :=
rfl

/- ### "one" -/

@[to_additive] instance [has_one β] : has_one C(α, β) := ⟨const α 1⟩

@[simp, norm_cast, to_additive] lemma coe_one [has_one β]  : ⇑(1 : C(α, β)) = 1 := rfl

@[simp, to_additive] lemma one_apply [has_one β] (x : α) : (1 : C(α, β)) x = 1 := rfl

@[simp, to_additive] lemma one_comp [has_one γ] (g : C(α, β)) : (1 : C(β, γ)).comp g = 1 := rfl

/- ### "nat_cast" -/

instance [has_nat_cast β] : has_nat_cast C(α, β) := ⟨λ n, continuous_map.const _ n⟩

@[simp, norm_cast] lemma coe_nat_cast [has_nat_cast β] (n : ℕ) : ((n : C(α, β)) : α → β) = n := rfl

@[simp] lemma nat_cast_apply [has_nat_cast β] (n : ℕ) (x : α) : (n : C(α, β)) x = n := rfl

/- ### "int_cast" -/

instance [has_int_cast β] : has_int_cast C(α, β) :=
⟨λ n, continuous_map.const _ n⟩

@[simp, norm_cast]
lemma coe_int_cast [has_int_cast β] (n : ℤ) : ((n : C(α, β)) : α → β) = n := rfl

@[simp] lemma int_cast_apply [has_int_cast β] (n : ℤ) (x : α) : (n : C(α, β)) x = n := rfl

/- ### "nsmul" and "pow" -/

instance has_nsmul [add_monoid β] [has_continuous_add β] : has_smul ℕ C(α, β) :=
⟨λ n f, ⟨n • f, f.continuous.nsmul n⟩⟩

@[to_additive]
instance has_pow [monoid β] [has_continuous_mul β] : has_pow C(α, β) ℕ :=
⟨λ f n, ⟨f ^ n, f.continuous.pow n⟩⟩

@[norm_cast, to_additive]
lemma coe_pow [monoid β] [has_continuous_mul β] (f : C(α, β)) (n : ℕ) :
  ⇑(f ^ n) = f ^ n := rfl

@[to_additive] lemma pow_apply [monoid β] [has_continuous_mul β]
  (f : C(α, β)) (n : ℕ) (x : α) :
  (f ^ n) x = f x ^ n :=
rfl

-- don't make auto-generated `coe_nsmul` and `nsmul_apply` simp, as the linter complains they're
-- redundant WRT `coe_smul`
attribute [simp] coe_pow pow_apply

@[to_additive] lemma pow_comp [monoid γ] [has_continuous_mul γ]
  (f : C(β, γ)) (n : ℕ) (g : C(α, β)) :
  (f^n).comp g = (f.comp g)^n :=
rfl

-- don't make `nsmul_comp` simp as the linter complains it's redundant WRT `smul_comp`
attribute [simp] pow_comp

/- ### "inv" and "neg" -/

@[to_additive]
instance [group β] [topological_group β] : has_inv C(α, β) :=
{ inv := λ f, ⟨f⁻¹, f.continuous.inv⟩ }

@[simp, norm_cast, to_additive]
lemma coe_inv [group β] [topological_group β] (f : C(α, β)) :
  ⇑(f⁻¹) = f⁻¹ :=
rfl

@[simp, to_additive] lemma inv_apply [group β] [topological_group β] (f : C(α, β)) (x : α) :
  f⁻¹ x = (f x)⁻¹ :=
rfl

@[simp, to_additive] lemma inv_comp [group γ] [topological_group γ] (f : C(β, γ)) (g : C(α, β)) :
  (f⁻¹).comp g = (f.comp g)⁻¹ :=
rfl

/- ### "div" and "sub" -/

@[to_additive]
instance [has_div β] [has_continuous_div β] : has_div C(α, β) :=
{ div := λ f g, ⟨f / g, f.continuous.div' g.continuous⟩ }

@[simp, norm_cast, to_additive]
lemma coe_div [has_div β] [has_continuous_div β] (f g : C(α, β)) : ⇑(f / g) = f / g :=
rfl

@[simp, to_additive] lemma div_apply [has_div β] [has_continuous_div β] (f g : C(α, β)) (x : α) :
  (f / g) x = f x / g x :=
rfl

@[simp, to_additive] lemma div_comp [has_div γ] [has_continuous_div γ]
  (f g : C(β, γ)) (h : C(α, β)) :
  (f / g).comp h = (f.comp h) / (g.comp h) :=
rfl

/- ### "zpow" and "zsmul" -/

instance has_zsmul [add_group β] [topological_add_group β] : has_smul ℤ C(α, β) :=
{ smul := λ z f, ⟨z • f, f.continuous.zsmul z⟩ }

@[to_additive]
instance has_zpow [group β] [topological_group β] :
  has_pow C(α, β) ℤ :=
{ pow := λ f z, ⟨f ^ z, f.continuous.zpow z⟩ }

@[norm_cast, to_additive]
lemma coe_zpow [group β] [topological_group β] (f : C(α, β)) (z : ℤ) :
  ⇑(f ^ z) = f ^ z :=
rfl

@[to_additive] lemma zpow_apply [group β] [topological_group β]
  (f : C(α, β)) (z : ℤ) (x : α) :
  (f ^ z) x = f x ^ z :=
rfl

-- don't make auto-generated `coe_zsmul` and `zsmul_apply` simp as the linter complains they're
-- redundant WRT `coe_smul`
attribute [simp] coe_zpow zpow_apply

@[to_additive]
lemma zpow_comp [group γ] [topological_group γ] (f : C(β, γ)) (z : ℤ) (g : C(α, β)) :
  (f^z).comp g = (f.comp g)^z :=
rfl

-- don't make `zsmul_comp` simp as the linter complains it's redundant WRT `smul_comp`
attribute [simp] zpow_comp

end continuous_map

section group_structure

/-!
### Group stucture

In this section we show that continuous functions valued in a topological group inherit
the structure of a group.
-/

section subtype

/-- The `submonoid` of continuous maps `α → β`. -/
@[to_additive "The `add_submonoid` of continuous maps `α → β`. "]
def continuous_submonoid (α : Type*) (β : Type*) [topological_space α] [topological_space β]
  [monoid β] [has_continuous_mul β] : submonoid (α → β) :=
{ carrier := { f : α → β | continuous f },
  one_mem' := @continuous_const _ _ _ _ 1,
  mul_mem' := λ f g fc gc, fc.mul gc }

/-- The subgroup of continuous maps `α → β`. -/
@[to_additive "The `add_subgroup` of continuous maps `α → β`. "]
def continuous_subgroup (α : Type*) (β : Type*) [topological_space α] [topological_space β]
  [group β] [topological_group β] : subgroup (α → β) :=
{ inv_mem' := λ f fc, continuous.inv fc,
  ..continuous_submonoid α β, }.

end subtype

namespace continuous_map

variables {α β : Type*} [topological_space α] [topological_space β]

@[to_additive]
instance [semigroup β] [has_continuous_mul β] : semigroup C(α, β) :=
coe_injective.semigroup _ coe_mul

@[to_additive]
instance [comm_semigroup β] [has_continuous_mul β] : comm_semigroup C(α, β) :=
coe_injective.comm_semigroup _ coe_mul

@[to_additive]
instance [mul_one_class β] [has_continuous_mul β] : mul_one_class C(α, β) :=
coe_injective.mul_one_class _ coe_one coe_mul

instance [mul_zero_class β] [has_continuous_mul β] : mul_zero_class C(α, β) :=
coe_injective.mul_zero_class _ coe_zero coe_mul

instance [semigroup_with_zero β] [has_continuous_mul β] : semigroup_with_zero C(α, β) :=
coe_injective.semigroup_with_zero _ coe_zero coe_mul

@[to_additive]
instance [monoid β] [has_continuous_mul β] : monoid C(α, β) :=
coe_injective.monoid _ coe_one coe_mul coe_pow

instance [monoid_with_zero β] [has_continuous_mul β] : monoid_with_zero C(α, β) :=
coe_injective.monoid_with_zero _ coe_zero coe_one coe_mul coe_pow

@[to_additive]
instance [comm_monoid β] [has_continuous_mul β] : comm_monoid C(α, β) :=
coe_injective.comm_monoid _ coe_one coe_mul coe_pow

instance [comm_monoid_with_zero β] [has_continuous_mul β] : comm_monoid_with_zero C(α, β) :=
coe_injective.comm_monoid_with_zero _ coe_zero coe_one coe_mul coe_pow

@[to_additive]
instance [locally_compact_space α] [has_mul β] [has_continuous_mul β] :
  has_continuous_mul C(α, β) :=
⟨begin
  refine continuous_of_continuous_uncurry _ _,
  have h1 : continuous (λ x : (C(α, β) × C(α, β)) × α, x.fst.fst x.snd) :=
    continuous_eval'.comp (continuous_fst.prod_map continuous_id),
  have h2 : continuous (λ x : (C(α, β) × C(α, β)) × α, x.fst.snd x.snd) :=
    continuous_eval'.comp (continuous_snd.prod_map continuous_id),
  exact h1.mul h2,
end⟩

/-- Coercion to a function as an `monoid_hom`. Similar to `monoid_hom.coe_fn`. -/
@[to_additive "Coercion to a function as an `add_monoid_hom`. Similar to `add_monoid_hom.coe_fn`.",
  simps]
def coe_fn_monoid_hom [monoid β] [has_continuous_mul β] : C(α, β) →* (α → β) :=
{ to_fun := coe_fn, map_one' := coe_one, map_mul' := coe_mul }

variables (α)

/-- Composition on the left by a (continuous) homomorphism of topological monoids, as a
`monoid_hom`. Similar to `monoid_hom.comp_left`. -/
@[to_additive "Composition on the left by a (continuous) homomorphism of topological `add_monoid`s,
as an `add_monoid_hom`. Similar to `add_monoid_hom.comp_left`.", simps]
protected def _root_.monoid_hom.comp_left_continuous
  {γ : Type*} [monoid β] [has_continuous_mul β]
  [topological_space γ] [monoid γ] [has_continuous_mul γ] (g : β →* γ) (hg : continuous g)  :
  C(α, β) →* C(α, γ) :=
{ to_fun := λ f, (⟨g, hg⟩ : C(β, γ)).comp f,
  map_one' := ext $ λ x, g.map_one,
  map_mul' := λ f₁ f₂, ext $ λ x, g.map_mul _ _ }

variables {α}

/-- Composition on the right as a `monoid_hom`. Similar to `monoid_hom.comp_hom'`. -/
@[to_additive "Composition on the right as an `add_monoid_hom`. Similar to
`add_monoid_hom.comp_hom'`.", simps]
def comp_monoid_hom' {γ : Type*} [topological_space γ]
  [mul_one_class γ] [has_continuous_mul γ] (g : C(α, β)) : C(β, γ) →* C(α, γ) :=
{ to_fun := λ f, f.comp g, map_one' := one_comp g, map_mul' := λ f₁ f₂, mul_comp f₁ f₂ g }

open_locale big_operators
@[simp, to_additive] lemma coe_prod [comm_monoid β] [has_continuous_mul β]
  {ι : Type*} (s : finset ι) (f : ι → C(α, β)) :
  ⇑(∏ i in s, f i) = (∏ i in s, (f i : α → β)) :=
(coe_fn_monoid_hom : C(α, β) →* _).map_prod f s

@[to_additive]
lemma prod_apply [comm_monoid β] [has_continuous_mul β]
  {ι : Type*} (s : finset ι) (f : ι → C(α, β)) (a : α) :
  (∏ i in s, f i) a = (∏ i in s, f i a) :=
by simp

@[to_additive]
instance [group β] [topological_group β] : group C(α, β) :=
coe_injective.group _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]
instance [comm_group β] [topological_group β] : comm_group C(α, β) :=
coe_injective.comm_group _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive] instance [comm_group β] [topological_group β] : topological_group C(α, β) :=
{ continuous_mul := by
  { letI : uniform_space β := topological_group.to_uniform_space β,
    have : uniform_group β := topological_comm_group_is_uniform,
    rw continuous_iff_continuous_at,
    rintros ⟨f, g⟩,
    rw [continuous_at, tendsto_iff_forall_compact_tendsto_uniformly_on, nhds_prod_eq],
    exactI λ K hK, uniform_continuous_mul.comp_tendsto_uniformly_on
      ((tendsto_iff_forall_compact_tendsto_uniformly_on.mp filter.tendsto_id K hK).prod
      (tendsto_iff_forall_compact_tendsto_uniformly_on.mp filter.tendsto_id K hK)), },
  continuous_inv := by
  { letI : uniform_space β := topological_group.to_uniform_space β,
    have : uniform_group β := topological_comm_group_is_uniform,
    rw continuous_iff_continuous_at,
    intro f,
    rw [continuous_at, tendsto_iff_forall_compact_tendsto_uniformly_on],
    exactI λ K hK, uniform_continuous_inv.comp_tendsto_uniformly_on
      (tendsto_iff_forall_compact_tendsto_uniformly_on.mp filter.tendsto_id K hK), } }

-- TODO: rewrite the next three lemmas for products and deduce sum case via `to_additive`, once
-- definition of `tprod` is in place

/-- If `α` is locally compact, and an infinite sum of functions in `C(α, β)`
converges to `g` (for the compact-open topology), then the pointwise sum converges to `g x` for
all `x ∈ α`. -/
lemma has_sum_apply {γ : Type*} [locally_compact_space α] [add_comm_monoid β] [has_continuous_add β]
  {f : γ → C(α, β)} {g : C(α, β)} (hf : has_sum f g) (x : α) :
  has_sum (λ i : γ, f i x) (g x) :=
begin
  let evₓ : add_monoid_hom C(α, β) β := (pi.eval_add_monoid_hom _ x).comp coe_fn_add_monoid_hom,
  exact hf.map evₓ (continuous_map.continuous_eval_const' x),
end

lemma summable_apply [locally_compact_space α] [add_comm_monoid β] [has_continuous_add β]
  {γ : Type*} {f : γ → C(α, β)} (hf : summable f) (x : α) :
  summable (λ i : γ, f i x) :=
(has_sum_apply hf.has_sum x).summable

lemma tsum_apply [locally_compact_space α] [t2_space β] [add_comm_monoid β] [has_continuous_add β]
  {γ : Type*} {f : γ → C(α, β)} (hf : summable f) (x : α) :
  (∑' (i:γ), f i x) = (∑' (i:γ), f i) x :=
(has_sum_apply hf.has_sum x).tsum_eq

end continuous_map

end group_structure

section ring_structure

/-!
### Ring stucture

In this section we show that continuous functions valued in a topological semiring `R` inherit
the structure of a ring.
-/

section subtype

/-- The subsemiring of continuous maps `α → β`. -/
def continuous_subsemiring (α : Type*) (R : Type*) [topological_space α] [topological_space R]
  [semiring R] [topological_semiring R] : subsemiring (α → R) :=
{ ..continuous_add_submonoid α R,
  ..continuous_submonoid α R }

/-- The subring of continuous maps `α → β`. -/
def continuous_subring (α : Type*) (R : Type*) [topological_space α] [topological_space R]
  [ring R] [topological_ring R] : subring (α → R) :=
{ ..continuous_subsemiring α R,
  ..continuous_add_subgroup α R }

end subtype

namespace continuous_map

instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [non_unital_non_assoc_semiring β] [topological_semiring β] :
  non_unital_non_assoc_semiring C(α, β) :=
coe_injective.non_unital_non_assoc_semiring _ coe_zero coe_add coe_mul coe_nsmul

instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [non_unital_semiring β] [topological_semiring β] :
  non_unital_semiring C(α, β) :=
coe_injective.non_unital_semiring _ coe_zero coe_add coe_mul coe_nsmul

instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [add_monoid_with_one β] [has_continuous_add β] :
  add_monoid_with_one C(α, β) :=
coe_injective.add_monoid_with_one _ coe_zero coe_one coe_add coe_nsmul coe_nat_cast

instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [non_assoc_semiring β] [topological_semiring β] :
  non_assoc_semiring C(α, β) :=
coe_injective.non_assoc_semiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_nat_cast

instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [semiring β] [topological_semiring β] : semiring C(α, β) :=
coe_injective.semiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_pow coe_nat_cast

instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [non_unital_non_assoc_ring β] [topological_ring β] : non_unital_non_assoc_ring C(α, β) :=
coe_injective.non_unital_non_assoc_ring _ coe_zero coe_add coe_mul coe_neg coe_sub
  coe_nsmul coe_zsmul

instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [non_unital_ring β] [topological_ring β] : non_unital_ring C(α, β) :=
coe_injective.non_unital_ring _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul

instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [non_assoc_ring β] [topological_ring β] : non_assoc_ring C(α, β) :=
coe_injective.non_assoc_ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul
  coe_nat_cast coe_int_cast

instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [ring β] [topological_ring β] : ring C(α, β) :=
coe_injective.ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul coe_pow
  coe_nat_cast coe_int_cast

instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [non_unital_comm_semiring β] [topological_semiring β] : non_unital_comm_semiring C(α, β) :=
coe_injective.non_unital_comm_semiring _ coe_zero coe_add coe_mul coe_nsmul

instance {α : Type*} {β : Type*} [topological_space α]
  [topological_space β] [comm_semiring β] [topological_semiring β] : comm_semiring C(α, β) :=
coe_injective.comm_semiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_pow coe_nat_cast

instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [non_unital_comm_ring β] [topological_ring β] : non_unital_comm_ring C(α, β) :=
coe_injective.non_unital_comm_ring _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul

instance {α : Type*} {β : Type*} [topological_space α]
  [topological_space β] [comm_ring β] [topological_ring β] : comm_ring C(α, β) :=
coe_injective.comm_ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul
  coe_pow coe_nat_cast coe_int_cast

/-- Composition on the left by a (continuous) homomorphism of topological semirings, as a
`ring_hom`.  Similar to `ring_hom.comp_left`. -/
@[simps] protected def _root_.ring_hom.comp_left_continuous (α : Type*) {β : Type*} {γ : Type*}
  [topological_space α] [topological_space β] [semiring β] [topological_semiring β]
  [topological_space γ] [semiring γ] [topological_semiring γ] (g : β →+* γ) (hg : continuous g) :
  C(α, β) →+* C(α, γ) :=
{ .. g.to_monoid_hom.comp_left_continuous α hg,
  .. g.to_add_monoid_hom.comp_left_continuous α hg }

/-- Coercion to a function as a `ring_hom`. -/
@[simps]
def coe_fn_ring_hom {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [semiring β] [topological_semiring β] : C(α, β) →+* (α → β) :=
{ to_fun := coe_fn,
  ..(coe_fn_monoid_hom : C(α, β) →* _),
  ..(coe_fn_add_monoid_hom : C(α, β) →+ _) }

end continuous_map

end ring_structure

local attribute [ext] subtype.eq

section module_structure

/-!
### Semiodule stucture

In this section we show that continuous functions valued in a topological module `M` over a
topological semiring `R` inherit the structure of a module.
-/

section subtype

variables (α : Type*) [topological_space α]
variables (R : Type*) [semiring R]
variables (M : Type*) [topological_space M] [add_comm_group M]
variables [module R M] [has_continuous_const_smul R M] [topological_add_group M]

/-- The `R`-submodule of continuous maps `α → M`. -/
def continuous_submodule : submodule R (α → M) :=
{ carrier := { f : α → M | continuous f },
  smul_mem' := λ c f hf, hf.const_smul c,
  ..continuous_add_subgroup α M }

end subtype

namespace continuous_map
variables {α β : Type*} [topological_space α] [topological_space β]
  {R R₁ : Type*}
  {M : Type*} [topological_space M]
  {M₂ : Type*} [topological_space M₂]

@[to_additive continuous_map.has_vadd]
instance [has_smul R M] [has_continuous_const_smul R M] : has_smul R C(α, M) :=
⟨λ r f, ⟨r • f, f.continuous.const_smul r⟩⟩

@[to_additive]
instance [locally_compact_space α] [has_smul R M] [has_continuous_const_smul R M] :
  has_continuous_const_smul R C(α, M) :=
⟨λ γ, continuous_of_continuous_uncurry _ (continuous_eval'.const_smul γ)⟩

@[to_additive]
instance [locally_compact_space α] [topological_space R] [has_smul R M]
  [has_continuous_smul R M] : has_continuous_smul R C(α, M) :=
⟨begin
  refine continuous_of_continuous_uncurry _ _,
  have h : continuous (λ x : (R × C(α, M)) × α, x.fst.snd x.snd) :=
    continuous_eval'.comp (continuous_snd.prod_map continuous_id),
  exact (continuous_fst.comp continuous_fst).smul h,
end⟩

@[simp, norm_cast, to_additive]
lemma coe_smul [has_smul R M] [has_continuous_const_smul R M]
  (c : R) (f : C(α, M)) : ⇑(c • f) = c • f := rfl

@[to_additive]
lemma smul_apply [has_smul R M] [has_continuous_const_smul R M]
  (c : R) (f : C(α, M)) (a : α) : (c • f) a = c • (f a) :=
rfl

@[simp, to_additive] lemma smul_comp [has_smul R M] [has_continuous_const_smul R M]
  (r : R) (f : C(β, M)) (g : C(α, β)) :
  (r • f).comp g = r • (f.comp g) :=
rfl

@[to_additive]
instance [has_smul R M] [has_continuous_const_smul R M]
  [has_smul R₁ M] [has_continuous_const_smul R₁ M]
  [smul_comm_class R R₁ M] : smul_comm_class R R₁ C(α, M) :=
{ smul_comm := λ _ _ _, ext $ λ _, smul_comm _ _ _ }

instance [has_smul R M] [has_continuous_const_smul R M]
  [has_smul R₁ M] [has_continuous_const_smul R₁ M]
  [has_smul R R₁] [is_scalar_tower R R₁ M] : is_scalar_tower R R₁ C(α, M) :=
{ smul_assoc := λ _ _ _, ext $ λ _, smul_assoc _ _ _ }

instance [has_smul R M] [has_smul Rᵐᵒᵖ M] [has_continuous_const_smul R M]
  [is_central_scalar R M] : is_central_scalar R C(α, M) :=
{ op_smul_eq_smul := λ _ _, ext $ λ _, op_smul_eq_smul _ _ }

instance [monoid R] [mul_action R M] [has_continuous_const_smul R M] : mul_action R C(α, M) :=
function.injective.mul_action _ coe_injective coe_smul

instance [monoid R] [add_monoid M] [distrib_mul_action R M]
  [has_continuous_add M] [has_continuous_const_smul R M] :
  distrib_mul_action R C(α, M) :=
function.injective.distrib_mul_action coe_fn_add_monoid_hom coe_injective coe_smul

variables [semiring R] [add_comm_monoid M] [add_comm_monoid M₂]
variables [has_continuous_add M] [module R M] [has_continuous_const_smul R M]
variables [has_continuous_add M₂] [module R M₂] [has_continuous_const_smul R M₂]

instance module : module R C(α, M) :=
function.injective.module R coe_fn_add_monoid_hom coe_injective coe_smul

variables (R)

/-- Composition on the left by a continuous linear map, as a `linear_map`.
Similar to `linear_map.comp_left`. -/
@[simps] protected def _root_.continuous_linear_map.comp_left_continuous (α : Type*)
  [topological_space α] (g : M →L[R] M₂) :
  C(α, M) →ₗ[R] C(α, M₂) :=
{ map_smul' := λ c f, ext $ λ x, g.map_smul' c _,
  .. g.to_linear_map.to_add_monoid_hom.comp_left_continuous α g.continuous }

/-- Coercion to a function as a `linear_map`. -/
@[simps]
def coe_fn_linear_map : C(α, M) →ₗ[R] (α → M) :=
{ to_fun := coe_fn,
  map_smul' := coe_smul,
  ..(coe_fn_add_monoid_hom : C(α, M) →+ _) }

end continuous_map

end module_structure

section algebra_structure

/-!
### Algebra structure

In this section we show that continuous functions valued in a topological algebra `A` over a ring
`R` inherit the structure of an algebra. Note that the hypothesis that `A` is a topological algebra
is obtained by requiring that `A` be both a `has_continuous_smul` and a `topological_semiring`.-/

section subtype

variables {α : Type*} [topological_space α]
{R : Type*} [comm_semiring R]
{A : Type*} [topological_space A] [semiring A]
[algebra R A] [topological_semiring A]

/-- The `R`-subalgebra of continuous maps `α → A`. -/
def continuous_subalgebra : subalgebra R (α → A) :=
{ carrier := { f : α → A | continuous f },
  algebra_map_mem' := λ r, (continuous_const : continuous $ λ (x : α), algebra_map R A r),
  ..continuous_subsemiring α A }

end subtype

section continuous_map

variables {α : Type*} [topological_space α]
{R : Type*} [comm_semiring R]
{A : Type*} [topological_space A] [semiring A]
[algebra R A] [topological_semiring A]
{A₂ : Type*} [topological_space A₂] [semiring A₂]
[algebra R A₂] [topological_semiring A₂]

/-- Continuous constant functions as a `ring_hom`. -/
def continuous_map.C : R →+* C(α, A) :=
{ to_fun    := λ c : R, ⟨λ x: α, ((algebra_map R A) c), continuous_const⟩,
  map_one'  := by ext x; exact (algebra_map R A).map_one,
  map_mul'  := λ c₁ c₂, by ext x; exact (algebra_map R A).map_mul _ _,
  map_zero' := by ext x; exact (algebra_map R A).map_zero,
  map_add'  := λ c₁ c₂, by ext x; exact (algebra_map R A).map_add _ _ }

@[simp] lemma continuous_map.C_apply (r : R) (a : α) : continuous_map.C r a = algebra_map R A r :=
rfl

instance continuous_map.algebra : algebra R C(α, A) :=
{ to_ring_hom := continuous_map.C,
  commutes' := λ c f, by ext x; exact algebra.commutes' _ _,
  smul_def' := λ c f, by ext x; exact algebra.smul_def' _ _, }

variables (R)

/-- Composition on the left by a (continuous) homomorphism of topological `R`-algebras, as an
`alg_hom`. Similar to `alg_hom.comp_left`. -/
@[simps] protected def alg_hom.comp_left_continuous {α : Type*} [topological_space α]
  (g : A →ₐ[R] A₂) (hg : continuous g) :
  C(α, A) →ₐ[R] C(α, A₂) :=
{ commutes' := λ c, continuous_map.ext $ λ _, g.commutes' _,
  .. g.to_ring_hom.comp_left_continuous α hg }

variables (A)

/--
Precomposition of functions into a normed ring by a continuous map is an algebra homomorphism.
-/
@[simps] def continuous_map.comp_right_alg_hom {α β : Type*} [topological_space α]
  [topological_space β] (f : C(α, β)) : C(β, A) →ₐ[R] C(α, A) :=
{ to_fun := λ g, g.comp f,
  map_zero' := by { ext, refl, },
  map_add' := λ g₁ g₂, by { ext, refl, },
  map_one' := by { ext, refl, },
  map_mul' := λ g₁ g₂, by { ext, refl, },
  commutes' := λ r, by { ext, refl, }, }

variables {A}

/-- Coercion to a function as an `alg_hom`. -/
@[simps]
def continuous_map.coe_fn_alg_hom : C(α, A) →ₐ[R] (α → A) :=
{ to_fun := coe_fn,
  commutes' := λ r, rfl,
  ..(continuous_map.coe_fn_ring_hom : C(α, A) →+* _) }

variables {R}

/--
A version of `separates_points` for subalgebras of the continuous functions,
used for stating the Stone-Weierstrass theorem.
-/
abbreviation subalgebra.separates_points (s : subalgebra R C(α, A)) : Prop :=
set.separates_points ((λ f : C(α, A), (f : α → A)) '' (s : set C(α, A)))

lemma subalgebra.separates_points_monotone :
  monotone (λ s : subalgebra R C(α, A), s.separates_points) :=
λ s s' r h x y n,
begin
  obtain ⟨f, m, w⟩ := h n,
  rcases m with ⟨f, ⟨m, rfl⟩⟩,
  exact ⟨_, ⟨f, ⟨r m, rfl⟩⟩, w⟩,
end

@[simp] lemma algebra_map_apply (k : R) (a : α) :
  algebra_map R C(α, A) k a = k • 1 :=
by { rw algebra.algebra_map_eq_smul_one, refl, }

variables {𝕜 : Type*} [topological_space 𝕜]

/--
A set of continuous maps "separates points strongly"
if for each pair of distinct points there is a function with specified values on them.

We give a slightly unusual formulation, where the specified values are given by some
function `v`, and we ask `f x = v x ∧ f y = v y`. This avoids needing a hypothesis `x ≠ y`.

In fact, this definition would work perfectly well for a set of non-continuous functions,
but as the only current use case is in the Stone-Weierstrass theorem,
writing it this way avoids having to deal with casts inside the set.
(This may need to change if we do Stone-Weierstrass on non-compact spaces,
where the functions would be continuous functions vanishing at infinity.)
-/
def set.separates_points_strongly (s : set C(α, 𝕜)) : Prop :=
∀ (v : α → 𝕜) (x y : α), ∃ f : s, (f x : 𝕜) = v x ∧ f y = v y

variables [field 𝕜] [topological_ring 𝕜]

/--
Working in continuous functions into a topological field,
a subalgebra of functions that separates points also separates points strongly.

By the hypothesis, we can find a function `f` so `f x ≠ f y`.
By an affine transformation in the field we can arrange so that `f x = a` and `f x = b`.
-/
lemma subalgebra.separates_points.strongly {s : subalgebra 𝕜 C(α, 𝕜)} (h : s.separates_points) :
  (s : set C(α, 𝕜)).separates_points_strongly :=
λ v x y,
begin
  by_cases n : x = y,
  { subst n,
    use ((v x) • 1 : C(α, 𝕜)),
    { apply s.smul_mem,
      apply s.one_mem, },
    { simp [coe_fn_coe_base'] }, },
  obtain ⟨f, ⟨f, ⟨m, rfl⟩⟩, w⟩ := h n,
  replace w : f x - f y ≠ 0 := sub_ne_zero_of_ne w,
  let a := v x,
  let b := v y,
  let f' := ((b - a) * (f x - f y)⁻¹) • (continuous_map.C (f x) - f) + continuous_map.C a,
  refine ⟨⟨f', _⟩, _, _⟩,
  { simp only [f', set_like.mem_coe, subalgebra.mem_to_submodule],
    -- TODO should there be a tactic for this?
    -- We could add an attribute `@[subobject_mem]`, and a tactic
    -- ``def subobject_mem := `[solve_by_elim with subobject_mem { max_depth := 10 }]``
    solve_by_elim
      [subalgebra.add_mem, subalgebra.smul_mem, subalgebra.sub_mem, subalgebra.algebra_map_mem]
      { max_depth := 6 }, },
  { simp [f', coe_fn_coe_base'], },
  { simp [f', coe_fn_coe_base', inv_mul_cancel_right₀ w], },
end

end continuous_map

instance continuous_map.subsingleton_subalgebra (α : Type*) [topological_space α]
  (R : Type*) [comm_semiring R] [topological_space R] [topological_semiring R]
  [subsingleton α] : subsingleton (subalgebra R C(α, R)) :=
begin
  fsplit,
  intros s₁ s₂,
  by_cases n : nonempty α,
  { obtain ⟨x⟩ := n,
    ext f,
    have h : f = algebra_map R C(α, R) (f x),
    { ext x', simp only [mul_one, algebra.id.smul_eq_mul, algebra_map_apply], congr, },
    rw h,
    simp only [subalgebra.algebra_map_mem], },
  { ext f,
    have h : f = 0,
    { ext x', exact false.elim (n ⟨x'⟩), },
    subst h,
    simp only [subalgebra.zero_mem], },
end

end algebra_structure

section module_over_continuous_functions

/-!
### Structure as module over scalar functions

If `M` is a module over `R`, then we show that the space of continuous functions from `α` to `M`
is naturally a module over the ring of continuous functions from `α` to `R`. -/

namespace continuous_map

instance has_smul' {α : Type*} [topological_space α]
  {R : Type*} [semiring R] [topological_space R]
  {M : Type*} [topological_space M] [add_comm_monoid M]
  [module R M] [has_continuous_smul R M] :
  has_smul C(α, R) C(α, M) :=
⟨λ f g, ⟨λ x, (f x) • (g x), (continuous.smul f.2 g.2)⟩⟩

instance module' {α : Type*} [topological_space α]
  (R : Type*) [ring R] [topological_space R] [topological_ring R]
  (M : Type*) [topological_space M] [add_comm_monoid M] [has_continuous_add M]
  [module R M] [has_continuous_smul R M] :
  module C(α, R) C(α, M) :=
{ smul     := (•),
  smul_add := λ c f g, by ext x; exact smul_add (c x) (f x) (g x),
  add_smul := λ c₁ c₂ f, by ext x; exact add_smul (c₁ x) (c₂ x) (f x),
  mul_smul := λ c₁ c₂ f, by ext x; exact mul_smul (c₁ x) (c₂ x) (f x),
  one_smul := λ f, by ext x; exact one_smul R (f x),
  zero_smul := λ f, by ext x; exact zero_smul _ _,
  smul_zero := λ r, by ext x; exact smul_zero _, }

end continuous_map

end module_over_continuous_functions

/-!
We now provide formulas for `f ⊓ g` and `f ⊔ g`, where `f g : C(α, β)`,
in terms of `continuous_map.abs`.
-/

section
variables {R : Type*} [linear_ordered_field R]

-- TODO:
-- This lemma (and the next) could go all the way back in `algebra.order.field`,
-- except that it is tedious to prove without tactics.
-- Rather than stranding it at some intermediate location,
-- it's here, immediately prior to the point of use.
lemma min_eq_half_add_sub_abs_sub {x y : R} : min x y = 2⁻¹ * (x + y - |x - y|) :=
by cases le_total x y with h h; field_simp [h, abs_of_nonneg, abs_of_nonpos, mul_two]; abel

lemma max_eq_half_add_add_abs_sub {x y : R} : max x y = 2⁻¹ * (x + y + |x - y|) :=
by cases le_total x y with h h; field_simp [h, abs_of_nonneg, abs_of_nonpos, mul_two]; abel

end

namespace continuous_map

section lattice
variables {α : Type*} [topological_space α]
variables {β : Type*} [linear_ordered_field β] [topological_space β]
  [order_topology β] [topological_ring β]

lemma inf_eq (f g : C(α, β)) : f ⊓ g = (2⁻¹ : β) • (f + g - |f - g|) :=
ext (λ x, by simpa using min_eq_half_add_sub_abs_sub)

-- Not sure why this is grosser than `inf_eq`:
lemma sup_eq (f g : C(α, β)) : f ⊔ g = (2⁻¹ : β) • (f + g + |f - g|) :=
ext (λ x, by simpa [mul_add] using @max_eq_half_add_add_abs_sub _ _ (f x) (g x))

end lattice

/-!
### Star structure

If `β` has a continuous star operation, we put a star structure on `C(α, β)` by using the
star operation pointwise.

If `β` is a ⋆-ring, then `C(α, β)` inherits a ⋆-ring structure.

If `β` is a ⋆-ring and a ⋆-module over `R`, then the space of continuous functions from `α` to `β`
is a ⋆-module over `R`.

-/

section star_structure
variables {R α β : Type*}
variables [topological_space α] [topological_space β]

section has_star
variables [has_star β] [has_continuous_star β]

instance : has_star C(α, β) :=
{ star := λ f, star_continuous_map.comp f }

@[simp] lemma coe_star (f : C(α, β)) : ⇑(star f) = star f := rfl

@[simp] lemma star_apply (f : C(α, β)) (x : α) : star f x = star (f x) := rfl

end has_star

instance [has_involutive_star β] [has_continuous_star β] : has_involutive_star C(α, β) :=
{ star_involutive := λ f, ext $ λ x, star_star _ }

instance [add_monoid β] [has_continuous_add β] [star_add_monoid β] [has_continuous_star β] :
  star_add_monoid C(α, β) :=
{ star_add := λ f g, ext $ λ x, star_add _ _ }

instance [semigroup β] [has_continuous_mul β] [star_semigroup β] [has_continuous_star β] :
  star_semigroup C(α, β) :=
{ star_mul := λ f g, ext $ λ x, star_mul _ _ }

instance [non_unital_semiring β] [topological_semiring β] [star_ring β] [has_continuous_star β] :
  star_ring C(α, β) :=
{ ..continuous_map.star_add_monoid }

instance [has_star R] [has_star β] [has_smul R β] [star_module R β]
  [has_continuous_star β] [has_continuous_const_smul R β] :
  star_module R C(α, β) :=
{ star_smul := λ k f, ext $ λ x, star_smul _ _ }

end star_structure

variables {X Y Z : Type*} [topological_space X] [topological_space Y] [topological_space Z]
variables (𝕜 : Type*) [comm_semiring 𝕜]
variables (A : Type*) [topological_space A] [semiring A] [topological_semiring A] [star_ring A]
variables [has_continuous_star A] [algebra 𝕜 A]

/-- The functorial map taking `f : C(X, Y)` to `C(Y, A) →⋆ₐ[𝕜] C(X, A)` given by pre-composition
with the continuous function `f`. See `continuous_map.comp_monoid_hom'` and
`continuous_map.comp_add_monoid_hom'`, `continuous_map.comp_right_alg_hom` for bundlings of
pre-composition into a `monoid_hom`, an `add_monoid_hom` and an `alg_hom`, respectively, under
suitable assumptions on `A`. -/
@[simps] def comp_star_alg_hom' (f : C(X, Y)) : C(Y, A) →⋆ₐ[𝕜] C(X, A) :=
{ to_fun := λ g, g.comp f,
  map_one' := one_comp _,
  map_mul' := λ _ _, rfl,
  map_zero' := zero_comp _,
  map_add' := λ _ _, rfl,
  commutes' := λ _, rfl,
  map_star' := λ _, rfl }

/-- `continuous_map.comp_star_alg_hom'` sends the identity continuous map to the identity
`star_alg_hom` -/
lemma comp_star_alg_hom'_id :
  comp_star_alg_hom' 𝕜 A (continuous_map.id X) = star_alg_hom.id 𝕜 C(X, A) :=
star_alg_hom.ext $ λ _, continuous_map.ext $ λ _, rfl

/-- `continuous_map.comp_star_alg_hom` is functorial. -/
lemma comp_star_alg_hom'_comp (g : C(Y, Z)) (f : C(X, Y)) :
  comp_star_alg_hom' 𝕜 A (g.comp f) = (comp_star_alg_hom' 𝕜 A f).comp (comp_star_alg_hom' 𝕜 A g) :=
star_alg_hom.ext $ λ _, continuous_map.ext $ λ _, rfl

section periodicity

/-! ### Summing translates of a function -/

/-- Summing the translates of `f` by `ℤ • p` gives a map which is periodic with period `p`.
(This is true without any convergence conditions, since if the sum doesn't converge it is taken to
be the zero map, which is periodic.) -/
lemma periodic_tsum_comp_add_zsmul [locally_compact_space X] [add_comm_group X]
  [topological_add_group X] [add_comm_monoid Y] [has_continuous_add Y] [t2_space Y]
  (f : C(X, Y)) (p : X) :
  function.periodic ⇑(∑' (n : ℤ), f.comp (continuous_map.add_right (n • p))) p :=
begin
  intro x,
  by_cases h : summable (λ n : ℤ, f.comp (continuous_map.add_right (n • p))),
  { convert congr_arg (λ f : C(X, Y), f x) ((equiv.add_right (1 : ℤ)).tsum_eq _) using 1,
    simp_rw [←tsum_apply h, ←tsum_apply ((equiv.add_right (1 : ℤ)).summable_iff.mpr h),
      equiv.coe_add_right, comp_apply, coe_add_right, add_one_zsmul, add_comm (_ • p) p,
      ←add_assoc] },
  { rw tsum_eq_zero_of_not_summable h,
    simp only [coe_zero, pi.zero_apply] }
end

end periodicity

end continuous_map

namespace homeomorph

variables {X Y : Type*} [topological_space X] [topological_space Y]
variables (𝕜 : Type*) [comm_semiring 𝕜]
variables (A : Type*) [topological_space A] [semiring A] [topological_semiring A] [star_ring A]
variables [has_continuous_star A] [algebra 𝕜 A]

/-- `continuous_map.comp_star_alg_hom'` as a `star_alg_equiv` when the continuous map `f` is
actually a homeomorphism. -/
@[simps] def comp_star_alg_equiv' (f : X ≃ₜ Y) : C(Y, A) ≃⋆ₐ[𝕜] C(X, A) :=
{ to_fun := (f : C(X, Y)).comp_star_alg_hom' 𝕜 A,
  inv_fun := (f.symm : C(Y, X)).comp_star_alg_hom' 𝕜 A,
  left_inv := λ g, by simp only [continuous_map.comp_star_alg_hom'_apply, continuous_map.comp_assoc,
    to_continuous_map_comp_symm, continuous_map.comp_id],
  right_inv := λ g, by simp only [continuous_map.comp_star_alg_hom'_apply,
    continuous_map.comp_assoc, symm_comp_to_continuous_map, continuous_map.comp_id],
  map_smul' := λ k a, map_smul (f.to_continuous_map.comp_star_alg_hom' 𝕜 A) k a,
  .. (f.to_continuous_map.comp_star_alg_hom' 𝕜 A) }

end homeomorph
