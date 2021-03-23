/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Nicolò Cavalleri
-/
import topology.algebra.module
import topology.continuous_map
import algebra.algebra.subalgebra

/-!
# Algebraic structures over continuous functions

In this file we define instances of algebraic structures over continuous functions. Instances are
present both in the case of the subtype of continuous functions and the type of continuous bundled
functions. Both implementations have advantages and disadvantages, but many experienced people in
Zulip have expressed a preference towards continuous bundled maps, so when there is no particular
reason to use the subtype, continuous bundled functions should be used for the sake of uniformity.
-/

local attribute [elab_simple] continuous.comp

namespace continuous_functions

variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]
variables {f g : {f : α → β | continuous f }}

instance : has_coe_to_fun {f : α → β | continuous f} :=  ⟨_, subtype.val⟩

end continuous_functions

namespace continuous_map
variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]

@[to_additive]
instance has_mul [has_mul β] [has_continuous_mul β] : has_mul C(α, β) :=
⟨λ f g, ⟨f * g, continuous_mul.comp (f.continuous.prod_mk g.continuous : _)⟩⟩

@[simp, norm_cast, to_additive]
lemma mul_coe [has_mul β] [has_continuous_mul β] (f g : C(α, β)) :
  ((f * g : C(α, β)) : α → β) = (f : α → β) * (g : α → β) := rfl

@[to_additive]
instance [has_one β] : has_one C(α, β) := ⟨const (1 : β)⟩

@[simp, norm_cast, to_additive]
lemma one_coe [has_one β]  :
  ((1 : C(α, β)) : α → β) = (1 : α → β) := rfl

@[simp, to_additive] lemma mul_comp {α : Type*} {β : Type*} {γ : Type*}
  [topological_space α] [topological_space β] [topological_space γ]
  [semigroup γ] [has_continuous_mul γ] (f₁ f₂ : C(β, γ)) (g : C(α, β)) :
  (f₁ * f₂).comp g = f₁.comp g * f₂.comp g :=
by { ext, simp, }

end continuous_map

section group_structure

/-!
### Group stucture

In this section we show that continuous functions valued in a topological group inherit
the structure of a group.
-/

section subtype

@[to_additive]
instance continuous_submonoid (α : Type*) (β : Type*) [topological_space α] [topological_space β]
  [monoid β] [has_continuous_mul β] : is_submonoid { f : α → β | continuous f } :=
{ one_mem := @continuous_const _ _ _ _ 1,
  mul_mem := λ f g fc gc, continuous.comp
  has_continuous_mul.continuous_mul (continuous.prod_mk fc gc : _) }

@[to_additive]
instance continuous_subgroup (α : Type*) (β : Type*) [topological_space α] [topological_space β]
  [group β] [topological_group β] : is_subgroup { f : α → β | continuous f } :=
{ inv_mem := λ f fc, continuous.comp (@topological_group.continuous_inv β _ _ _) fc,
  ..continuous_submonoid α β, }.

@[to_additive]
instance continuous_monoid {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [monoid β] [has_continuous_mul β] : monoid { f : α → β | continuous f } :=
subtype.monoid

@[to_additive]
instance continuous_group {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [group β] [topological_group β] : group { f : α → β | continuous f } :=
subtype.group

@[to_additive]
instance continuous_comm_group {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [comm_group β] [topological_group β] : comm_group { f : α → β | continuous f } :=
@subtype.comm_group _ _ _ (continuous_subgroup α β) -- infer_instance doesn't work?!

end subtype

section continuous_map

@[to_additive]
instance continuous_map_semigroup {α : Type*} {β : Type*} [topological_space α]
  [topological_space β] [semigroup β] [has_continuous_mul β] : semigroup C(α, β) :=
{ mul_assoc := λ a b c, by ext; exact mul_assoc _ _ _,
  ..continuous_map.has_mul}

@[to_additive]
instance continuous_map_monoid {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [monoid β] [has_continuous_mul β] : monoid C(α, β) :=
{ one_mul := λ a, by ext; exact one_mul _,
  mul_one := λ a, by ext; exact mul_one _,
  ..continuous_map_semigroup,
  ..continuous_map.has_one }

@[simp, norm_cast]
lemma pow_coe {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [monoid β] [has_continuous_mul β] (f : C(α, β)) (n : ℕ) :
  ((f^n : C(α, β)) : α → β) = (f : α → β)^n :=
begin
  ext x,
  induction n with n ih,
  { simp, },
  { simp [pow_succ, ih], },
end

@[simp] lemma continuous_map.pow_comp {α : Type*} {β : Type*} {γ : Type*}
  [topological_space α] [topological_space β] [topological_space γ]
  [monoid γ] [has_continuous_mul γ] (f : C(β, γ)) (n : ℕ) (g : C(α, β)) :
  (f^n).comp g = (f.comp g)^n :=
begin
  induction n with n ih,
  { ext, simp, },
  { simp [pow_succ, ih], }
end

@[to_additive]
instance continuous_map_comm_monoid {α : Type*} {β : Type*} [topological_space α]
[topological_space β] [comm_monoid β] [has_continuous_mul β] : comm_monoid C(α, β) :=
{ one_mul := λ a, by ext; exact one_mul _,
  mul_one := λ a, by ext; exact mul_one _,
  mul_comm := λ a b, by ext; exact mul_comm _ _,
  ..continuous_map_semigroup,
  ..continuous_map.has_one }

@[to_additive]
instance continuous_map_group {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [group β] [topological_group β] : group C(α, β) :=
{ inv := λ f, ⟨λ x, (f x)⁻¹, continuous_inv.comp f.continuous⟩,
  mul_left_inv := λ a, by ext; exact mul_left_inv _,
  ..continuous_map_monoid }

@[simp, norm_cast, to_additive]
lemma inv_coe {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [group β] [topological_group β] (f : C(α, β)) :
  ((f⁻¹ : C(α, β)) : α → β) = (f⁻¹ : α → β) :=
rfl

@[simp, norm_cast, to_additive]
lemma div_coe {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [group β] [topological_group β] (f g : C(α, β)) :
  ((f / g : C(α, β)) : α → β) = (f : α → β) / (g : α → β) :=
by { simp only [div_eq_mul_inv], refl, }

@[simp, to_additive] lemma continuous_map.inv_comp {α : Type*} {β : Type*} {γ : Type*}
  [topological_space α] [topological_space β] [topological_space γ]
  [group γ] [topological_group γ] (f : C(β, γ)) (g : C(α, β)) :
  (f⁻¹).comp g = (f.comp g)⁻¹ :=
by { ext, simp, }

@[simp, to_additive] lemma continuous_map.div_comp {α : Type*} {β : Type*} {γ : Type*}
  [topological_space α] [topological_space β] [topological_space γ]
  [group γ] [topological_group γ] (f g : C(β, γ)) (h : C(α, β)) :
  (f / g).comp h = (f.comp h) / (g.comp h) :=
by { ext, simp, }

@[to_additive]
instance continuous_map_comm_group {α : Type*} {β : Type*} [topological_space α]
  [topological_space β] [comm_group β] [topological_group β] : comm_group C(α, β) :=
{ ..continuous_map_group,
  ..continuous_map_comm_monoid }

end continuous_map

end group_structure

section ring_structure

/-!
### Ring stucture

In this section we show that continuous functions valued in a topological ring `R` inherit
the structure of a ring.
-/

section subtype

instance continuous_subring (α : Type*) (R : Type*) [topological_space α] [topological_space R]
  [ring R] [topological_ring R] : is_subring { f : α → R | continuous f } :=
{ ..continuous_add_subgroup α R,
  ..continuous_submonoid α R }.

instance continuous_ring {α : Type*} {R : Type*} [topological_space α] [topological_space R]
  [ring R] [topological_ring R] : ring { f : α → R | continuous f } :=
@subtype.ring _ _ _ (continuous_subring α R) -- infer_instance doesn't work?!

instance continuous_comm_ring {α : Type*} {R : Type*} [topological_space α] [topological_space R]
  [comm_ring R] [topological_ring R] : comm_ring { f : α → R | continuous f } :=
@subtype.comm_ring _ _ _ (continuous_subring α R) -- infer_instance doesn't work?!

end subtype

section continuous_map

instance continuous_map_semiring {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [semiring β] [topological_semiring β] : semiring C(α, β) :=
{ left_distrib := λ a b c, by ext; exact left_distrib _ _ _,
  right_distrib := λ a b c, by ext; exact right_distrib _ _ _,
  zero_mul := λ a, by ext; exact zero_mul _,
  mul_zero := λ a, by ext; exact mul_zero _,
  ..continuous_map_add_comm_monoid,
  ..continuous_map_monoid }

instance continuous_map_ring {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [ring β] [topological_ring β] : ring C(α, β) :=
{ ..continuous_map_semiring,
  ..continuous_map_add_comm_group, }

instance continuous_map_comm_ring {α : Type*} {β : Type*} [topological_space α]
[topological_space β] [comm_ring β] [topological_ring β] : comm_ring C(α, β) :=
{ ..continuous_map_semiring,
  ..continuous_map_add_comm_group,
  ..continuous_map_comm_monoid,}

end continuous_map

end ring_structure

local attribute [ext] subtype.eq

section semimodule_structure

/-!
### Semiodule stucture

In this section we show that continuous functions valued in a topological semimodule `M` over a
topological semiring `R` inherit the structure of a semimodule.
-/

section subtype

instance continuous_has_scalar {α : Type*} [topological_space α]
  {R : Type*} [semiring R] [topological_space R]
  {M : Type*} [topological_space M] [add_comm_group M]
  [semimodule R M] [topological_semimodule R M] :
  has_scalar R { f : α → M | continuous f } :=
⟨λ r f, ⟨r • f, continuous_const.smul f.property⟩⟩

instance continuous_semimodule {α : Type*} [topological_space α]
{R : Type*} [semiring R] [topological_space R]
{M : Type*} [topological_space M] [add_comm_group M] [topological_add_group M]
[semimodule R M] [topological_semimodule R M] :
  semimodule R { f : α → M | continuous f } :=
  semimodule.of_core $
{ smul     := (•),
  smul_add := λ c f g, by ext x; exact smul_add c (f x) (g x),
  add_smul := λ c₁ c₂ f, by ext x; exact add_smul c₁ c₂ (f x),
  mul_smul := λ c₁ c₂ f, by ext x; exact mul_smul c₁ c₂ (f x),
  one_smul := λ f, by ext x; exact one_smul R (f x) }

end subtype

section continuous_map
variables {α : Type*} [topological_space α]
  {R : Type*} [semiring R] [topological_space R]
  {M : Type*} [topological_space M] [add_comm_monoid M]

instance continuous_map_has_scalar
  [semimodule R M] [topological_semimodule R M] :
  has_scalar R C(α, M) :=
⟨λ r f, ⟨r • f, continuous_const.smul f.continuous⟩⟩

@[simp] lemma continuous_map.smul_apply [semimodule R M] [topological_semimodule R M]
  (c : R) (f : C(α, M)) (a : α) : (c • f) a = c • (f a) :=
rfl

@[simp] lemma continuous_map.smul_comp {α : Type*} {β : Type*}
  [topological_space α] [topological_space β]
   [semimodule R M] [topological_semimodule R M] (r : R) (f : C(β, M)) (g : C(α, β)) :
  (r • f).comp g = r • (f.comp g) :=
by { ext, simp, }

variables [has_continuous_add M] [semimodule R M] [topological_semimodule R M]

instance continuous_map_semimodule : semimodule R C(α, M) :=
{ smul     := (•),
  smul_add := λ c f g, by { ext, exact smul_add c (f x) (g x) },
  add_smul := λ c₁ c₂ f, by { ext, exact add_smul c₁ c₂ (f x) },
  mul_smul := λ c₁ c₂ f, by { ext, exact mul_smul c₁ c₂ (f x) },
  one_smul := λ f, by { ext, exact one_smul R (f x) },
  zero_smul := λ f, by { ext, exact zero_smul _ _ },
  smul_zero := λ r, by { ext, exact smul_zero _ } }

end continuous_map

end semimodule_structure

section algebra_structure

/-!
### Algebra structure

In this section we show that continuous functions valued in a topological algebra `A` over a ring
`R` inherit the structure of an algebra. Note that the hypothesis that `A` is a topological algebra
is obtained by requiring that `A` be both a `topological_semimodule` and a `topological_semiring`
(by now we require `topological_ring`: see TODO below).-/

section subtype

variables {α : Type*} [topological_space α]
{R : Type*} [comm_semiring R]
{A : Type*} [topological_space A] [ring A]
[algebra R A] [topological_ring A]

/-- Continuous constant functions as a `ring_hom`. -/
def continuous.C : R →+* { f : α → A | continuous f } :=
{ to_fun    := λ c : R, ⟨λ x: α, ((algebra_map R A) c), continuous_const⟩,
  map_one'  := by ext x; exact (algebra_map R A).map_one,
  map_mul'  := λ c₁ c₂, by ext x; exact (algebra_map R A).map_mul _ _,
  map_zero' := by ext x; exact (algebra_map R A).map_zero,
  map_add'  := λ c₁ c₂, by ext x; exact (algebra_map R A).map_add _ _ }

variables [topological_space R] [topological_semimodule R A]

instance : algebra R { f : α → A | continuous f } :=
{ to_ring_hom := continuous.C,
  commutes' := λ c f, by ext x; exact algebra.commutes' _ _,
  smul_def' := λ c f, by ext x; exact algebra.smul_def' _ _,
  ..continuous_semimodule,
  ..continuous_ring }

/- TODO: We are assuming `A` to be a ring and not a semiring just because there is not yet an
instance of semiring. In turn, we do not want to define yet an instance of semiring because there is
no `is_subsemiring` but only `subsemiring`, and it will make sense to change this when the whole
file will have no more `is_subobject`s but only `subobject`s. It does not make sense to change
it yet in this direction as `subring` does not exist yet, so everything is being blocked by
`subring`: afterwards everything will need to be updated to the new conventions of Mathlib.
Then the instance of `topological_ring` can also be removed, as it is below for `continuous_map`. -/

end subtype

section continuous_map

variables {α : Type*} [topological_space α]
{R : Type*} [comm_semiring R]
{A : Type*} [topological_space A] [semiring A]
[algebra R A] [topological_semiring A]

/-- Continuous constant functions as a `ring_hom`. -/
def continuous_map.C : R →+* C(α, A) :=
{ to_fun    := λ c : R, ⟨λ x: α, ((algebra_map R A) c), continuous_const⟩,
  map_one'  := by ext x; exact (algebra_map R A).map_one,
  map_mul'  := λ c₁ c₂, by ext x; exact (algebra_map R A).map_mul _ _,
  map_zero' := by ext x; exact (algebra_map R A).map_zero,
  map_add'  := λ c₁ c₂, by ext x; exact (algebra_map R A).map_add _ _ }

@[simp] lemma continuous_map.C_apply (r : R) (a : α) : continuous_map.C r a = algebra_map R A r :=
rfl

variables [topological_space R] [topological_semimodule R A]

instance continuous_map_algebra : algebra R C(α, A) :=
{ to_ring_hom := continuous_map.C,
  commutes' := λ c f, by ext x; exact algebra.commutes' _ _,
  smul_def' := λ c f, by ext x; exact algebra.smul_def' _ _,
  ..continuous_map_semiring }

/--
A version of `separates_points` for subalgebras of the continuous functions,
used for stating the Stone-Weierstrass theorem.
-/
abbreviation subalgebra.separates_points (s : subalgebra R C(α, A)) : Prop :=
separates_points ((λ f : C(α, A), (f : α → A)) '' (s : set C(α, A)))

lemma subalgebra.separates_points_monotone :
  monotone (λ s : subalgebra R C(α, A), s.separates_points) :=
λ s s' r h x y n,
begin
  obtain ⟨f, m, w⟩ := h x y n,
  rcases m with ⟨f, ⟨m, rfl⟩⟩,
  exact ⟨_, ⟨f, ⟨r m, rfl⟩⟩, w⟩,
end

@[simp] lemma algebra_map_apply (k : R) (a : α) :
  algebra_map R C(α, A) k a = k • 1 :=
by { rw algebra.algebra_map_eq_smul_one, refl, }

variables {𝕜 : Type*} [field 𝕜] [topological_space 𝕜] [topological_ring 𝕜]

/--
Working in continuous functions into a topological field,
a subalgebra of functions that separates points also separates points strongly.

By the hypothesis, we can find a function `f` so `f x ≠ f y`.
By an affine transformation in the field we can arrange so that `f x = a` and `f x = b`.
-/
lemma subalgebra.separates_points.strongly {s : subalgebra 𝕜 C(α, 𝕜)} (h : s.separates_points) :
  separates_points_strongly ((λ f : C(α, 𝕜), (f : α → 𝕜)) '' (s : set C(α, 𝕜))) :=
λ x y n,
begin
  obtain ⟨f, ⟨f, ⟨m, rfl⟩⟩, w⟩ := h x y n,
  replace w : f x - f y ≠ 0 := sub_ne_zero_of_ne w,
  intros a b,
  let f' := ((b - a) * (f x - f y)⁻¹) • (continuous_map.C (f x) - f) + continuous_map.C a,
  refine ⟨f', _, _, _⟩,
  { simp only [set.mem_image, coe_coe],
    refine ⟨f', _, rfl⟩,
    simp only [f', submodule.mem_coe, subalgebra.mem_to_submodule],
    -- TODO should there be a tactic for this?
    -- We could add an attribute `@[subobject_mem]`, and a tactic
    -- ``def subobject_mem := `[solve_by_elim with subobject_mem { max_depth := 10 }]``
    solve_by_elim
      [subalgebra.add_mem, subalgebra.smul_mem, subalgebra.sub_mem, subalgebra.algebra_map_mem]
      { max_depth := 6 }, },
  { simp [f'], },
  { simp [f', inv_mul_cancel_right' w], },
end

end continuous_map

end algebra_structure

section module_over_continuous_functions

/-!
### Structure as module over scalar functions

If `M` is a module over `R`, then we show that the space of continuous functions from `α` to `M`
is naturally a module over the ring of continuous functions from `α` to `M`. -/

section subtype

instance continuous_has_scalar' {α : Type*} [topological_space α]
  {R : Type*} [semiring R] [topological_space R]
  {M : Type*} [topological_space M] [add_comm_group M]
  [semimodule R M] [topological_semimodule R M] :
  has_scalar { f : α → R | continuous f } { f : α → M | continuous f } :=
⟨λ f g, ⟨λ x, (f x) • (g x), (continuous.smul f.2 g.2)⟩⟩

instance continuous_module' {α : Type*} [topological_space α]
  (R : Type*) [ring R] [topological_space R] [topological_ring R]
  (M : Type*) [topological_space M] [add_comm_group M] [topological_add_group M]
  [module R M] [topological_module R M]
  : module { f : α → R | continuous f } { f : α → M | continuous f } :=
  semimodule.of_core $
{ smul     := (•),
  smul_add := λ c f g, by ext x; exact smul_add (c x) (f x) (g x),
  add_smul := λ c₁ c₂ f, by ext x; exact add_smul (c₁ x) (c₂ x) (f x),
  mul_smul := λ c₁ c₂ f, by ext x; exact mul_smul (c₁ x) (c₂ x) (f x),
  one_smul := λ f, by ext x; exact one_smul R (f x) }

end subtype

section continuous_map

instance continuous_map_has_scalar' {α : Type*} [topological_space α]
  {R : Type*} [semiring R] [topological_space R]
  {M : Type*} [topological_space M] [add_comm_monoid M]
  [semimodule R M] [topological_semimodule R M] :
  has_scalar C(α, R) C(α, M) :=
⟨λ f g, ⟨λ x, (f x) • (g x), (continuous.smul f.2 g.2)⟩⟩

instance continuous_map_module' {α : Type*} [topological_space α]
  (R : Type*) [ring R] [topological_space R] [topological_ring R]
  (M : Type*) [topological_space M] [add_comm_monoid M] [has_continuous_add M]
  [semimodule R M] [topological_semimodule R M] :
  semimodule C(α, R) C(α, M) :=
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
-- This lemma (and the next) could go all the way back in `algebra.ordered_field`,
-- except that it is tedious to prove without tactics.
-- Rather than stranding it at some intermediate location,
-- it's here, immediately prior to the point of use.
lemma min_eq_half_add_sub_abs_sub {x y : R} : min x y = 2⁻¹ * (x + y - abs (x - y)) :=
begin
  dsimp [min, max, abs],
  simp only [neg_le_self_iff, if_congr, sub_nonneg, neg_sub],
  split_ifs; ring; linarith,
end

lemma max_eq_half_add_add_abs_sub {x y : R} : max x y = 2⁻¹ * (x + y + abs (x - y)) :=
begin
  dsimp [min, max, abs],
  simp only [neg_le_self_iff, if_congr, sub_nonneg, neg_sub],
  split_ifs; ring; linarith,
end
end

namespace continuous_map

section lattice
variables {α : Type*} [topological_space α]
variables {β : Type*} [linear_ordered_field β] [topological_space β]
  [order_topology β] [topological_ring β]

lemma inf_eq (f g : C(α, β)) : f ⊓ g = (2⁻¹ : β) • (f + g - (f - g).abs) :=
ext (λ x, by simpa using min_eq_half_add_sub_abs_sub)

-- Not sure why this is grosser than `inf_eq`:
lemma sup_eq (f g : C(α, β)) : f ⊔ g = (2⁻¹ : β) • (f + g + (f - g).abs) :=
ext (λ x, by simpa [mul_add] using @max_eq_half_add_add_abs_sub _ _ (f x) (g x))

end lattice

end continuous_map
