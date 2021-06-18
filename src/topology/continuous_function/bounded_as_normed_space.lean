/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth
-/
import analysis.normed_space.basic
import topology.continuous_function.bounded

/-!
# Normed space structure on the space of bounded continuous functions

We show that, when the space `β` is a normed group, then the space of bounded continuous functions
from `α` to `β` inherits a normed space structure. The same goes for normed spaces, normed rings
and normed algebras.
-/

noncomputable theory
open_locale topological_space classical nnreal bounded_continuous_function

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace bounded_continuous_function

section normed_group
/- In this section, if β is a normed group, then we show that the space of bounded
continuous functions from α to β inherits a normed group structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

variables [topological_space α] [normed_group β]
variables (f g : α →ᵇ β) {x : α} {C : ℝ}

instance : has_zero (α →ᵇ β) := ⟨const α 0⟩

@[simp] lemma coe_zero : ((0 : α →ᵇ β) : α → β) = 0 := rfl

instance : has_norm (α →ᵇ β) := ⟨λu, dist u 0⟩

lemma norm_def : ∥f∥ = dist f 0 := rfl

/-- The norm of a bounded continuous function is the supremum of `∥f x∥`.
We use `Inf` to ensure that the definition works if `α` has no elements. -/
lemma norm_eq (f : α →ᵇ β) :
  ∥f∥ = Inf {C : ℝ | 0 ≤ C ∧ ∀ (x : α), ∥f x∥ ≤ C} :=
by simp [norm_def, bounded_continuous_function.dist_eq]

lemma norm_coe_le_norm (x : α) : ∥f x∥ ≤ ∥f∥ := calc
  ∥f x∥ = dist (f x) ((0 : α →ᵇ β) x) : by simp [dist_zero_right]
  ... ≤ ∥f∥ : dist_coe_le_dist _

lemma dist_le_two_norm' {f : γ → β} {C : ℝ} (hC : ∀ x, ∥f x∥ ≤ C) (x y : γ) :
  dist (f x) (f y) ≤ 2 * C :=
calc dist (f x) (f y) ≤ ∥f x∥ + ∥f y∥ : dist_le_norm_add_norm _ _
                  ... ≤ C + C         : add_le_add (hC x) (hC y)
                  ... = 2 * C         : (two_mul _).symm

/-- Distance between the images of any two points is at most twice the norm of the function. -/
lemma dist_le_two_norm (x y : α) : dist (f x) (f y) ≤ 2 * ∥f∥ :=
dist_le_two_norm' f.norm_coe_le_norm x y

variable {f}

/-- The norm of a function is controlled by the supremum of the pointwise norms -/
lemma norm_le (C0 : (0 : ℝ) ≤ C) : ∥f∥ ≤ C ↔ ∀x:α, ∥f x∥ ≤ C :=
by simpa using @dist_le _ _ _ _ f 0 _ C0

lemma norm_le_of_nonempty [nonempty α]
  {f : α →ᵇ β} {M : ℝ} : ∥f∥ ≤ M ↔ ∀ x, ∥f x∥ ≤ M :=
begin
  simp_rw [norm_def, ←dist_zero_right],
  exact dist_le_iff_of_nonempty,
end

lemma norm_lt_iff_of_compact [compact_space α]
  {f : α →ᵇ β} {M : ℝ} (M0 : 0 < M) : ∥f∥ < M ↔ ∀ x, ∥f x∥ < M :=
begin
  simp_rw [norm_def, ←dist_zero_right],
  exact dist_lt_iff_of_compact M0,
end

lemma norm_lt_iff_of_nonempty_compact [nonempty α] [compact_space α]
  {f : α →ᵇ β} {M : ℝ} : ∥f∥ < M ↔ ∀ x, ∥f x∥ < M :=
begin
  simp_rw [norm_def, ←dist_zero_right],
  exact dist_lt_iff_of_nonempty_compact,
end

variable (f)

/-- Norm of `const α b` is less than or equal to `∥b∥`. If `α` is nonempty,
then it is equal to `∥b∥`. -/
lemma norm_const_le (b : β) : ∥const α b∥ ≤ ∥b∥ :=
(norm_le (norm_nonneg b)).2 $ λ x, le_refl _

@[simp] lemma norm_const_eq [h : nonempty α] (b : β) : ∥const α b∥ = ∥b∥ :=
le_antisymm (norm_const_le b) $ h.elim $ λ x, (const α b).norm_coe_le_norm x

/-- Constructing a bounded continuous function from a uniformly bounded continuous
function taking values in a normed group. -/
def of_normed_group {α : Type u} {β : Type v} [topological_space α] [normed_group β]
  (f : α → β) (Hf : continuous f) (C : ℝ) (H : ∀x, ∥f x∥ ≤ C) : α →ᵇ β :=
⟨⟨λn, f n, Hf⟩, ⟨_, dist_le_two_norm' H⟩⟩

@[simp] lemma coe_of_normed_group
  {α : Type u} {β : Type v} [topological_space α] [normed_group β]
  (f : α → β) (Hf : continuous f) (C : ℝ) (H : ∀x, ∥f x∥ ≤ C) :
  (of_normed_group f Hf C H : α → β) = f := rfl

lemma norm_of_normed_group_le {f : α → β} (hfc : continuous f) {C : ℝ} (hC : 0 ≤ C)
  (hfC : ∀ x, ∥f x∥ ≤ C) : ∥of_normed_group f hfc C hfC∥ ≤ C :=
(norm_le hC).2 hfC

/-- Constructing a bounded continuous function from a uniformly bounded
function on a discrete space, taking values in a normed group -/
def of_normed_group_discrete {α : Type u} {β : Type v}
  [topological_space α] [discrete_topology α] [normed_group β]
  (f : α  → β) (C : ℝ) (H : ∀x, norm (f x) ≤ C) : α →ᵇ β :=
of_normed_group f continuous_of_discrete_topology C H

@[simp] lemma coe_of_normed_group_discrete
  {α : Type u} {β : Type v} [topological_space α] [discrete_topology α] [normed_group β]
  (f : α → β) (C : ℝ) (H : ∀x, ∥f x∥ ≤ C) :
  (of_normed_group_discrete f C H : α → β) = f := rfl

/-- The pointwise sum of two bounded continuous functions is again bounded continuous. -/
instance : has_add (α →ᵇ β) :=
⟨λf g, of_normed_group (f + g) (f.continuous.add g.continuous) (∥f∥ + ∥g∥) $ λ x,
  le_trans (norm_add_le _ _) (add_le_add (f.norm_coe_le_norm x) (g.norm_coe_le_norm x))⟩

/-- The pointwise opposite of a bounded continuous function is again bounded continuous. -/
instance : has_neg (α →ᵇ β) :=
⟨λf, of_normed_group (-f) f.continuous.neg ∥f∥ $ λ x,
  trans_rel_right _ (norm_neg _) (f.norm_coe_le_norm x)⟩

/-- The pointwise difference of two bounded continuous functions is again bounded continuous. -/
instance : has_sub (α →ᵇ β) :=
⟨λf g, of_normed_group (f - g) (f.continuous.sub g.continuous) (∥f∥ + ∥g∥) $ λ x,
  by { simp only [sub_eq_add_neg],
       exact le_trans (norm_add_le _ _) (add_le_add (f.norm_coe_le_norm x) $
         trans_rel_right _ (norm_neg _) (g.norm_coe_le_norm x)) }⟩

@[simp] lemma coe_add : ⇑(f + g) = f + g := rfl
lemma add_apply : (f + g) x = f x + g x := rfl
@[simp] lemma coe_neg : ⇑(-f) = -f := rfl
lemma neg_apply : (-f) x = -f x := rfl

lemma forall_coe_zero_iff_zero : (∀x, f x = 0) ↔ f = 0 :=
(@ext_iff _ _ _ _ f 0).symm

instance : add_comm_group (α →ᵇ β) :=
{ add_assoc      := assume f g h, by ext; simp [add_assoc],
  zero_add       := assume f, by ext; simp,
  add_zero       := assume f, by ext; simp,
  add_left_neg   := assume f, by ext; simp,
  add_comm       := assume f g, by ext; simp [add_comm],
  sub_eq_add_neg := assume f g, by { ext, apply sub_eq_add_neg },
  ..bounded_continuous_function.has_add,
  ..bounded_continuous_function.has_neg,
  ..bounded_continuous_function.has_sub,
  ..bounded_continuous_function.has_zero }

@[simp] lemma coe_sub : ⇑(f - g) = f - g := rfl
lemma sub_apply : (f - g) x = f x - g x := rfl

/-- Coercion of a `normed_group_hom` is an `add_monoid_hom`. Similar to `add_monoid_hom.coe_fn` -/
@[simps]
def coe_fn_add_hom : (α →ᵇ β) →+ (α → β) :=
{ to_fun := coe_fn, map_zero' := coe_zero, map_add' := coe_add}

open_locale big_operators
@[simp] lemma coe_sum {ι : Type*} (s : finset ι) (f : ι → (α →ᵇ β)) :
  ⇑(∑ i in s, f i) = (∑ i in s, (f i : α → β)) :=
(@coe_fn_add_hom α β _ _).map_sum f s

lemma sum_apply {ι : Type*} (s : finset ι) (f : ι → (α →ᵇ β)) (a : α) :
  (∑ i in s, f i) a = (∑ i in s, f i a) :=
by simp

instance : normed_group (α →ᵇ β) :=
{ dist_eq := λ f g, by simp only [norm_eq, dist_eq, dist_eq_norm, sub_apply] }

lemma abs_diff_coe_le_dist : ∥f x - g x∥ ≤ dist f g :=
by { rw dist_eq_norm, exact (f - g).norm_coe_le_norm x }

lemma coe_le_coe_add_dist {f g : α →ᵇ ℝ} : f x ≤ g x + dist f g :=
sub_le_iff_le_add'.1 $ (abs_le.1 $ @dist_coe_le_dist _ _ _ _ f g x).2

variables (α β)

/--
The additive map forgetting that a bounded continuous function is bounded.
-/
@[simps]
def forget_boundedness_add_hom : (α →ᵇ β) →+ C(α, β) :=
{ to_fun := forget_boundedness α β,
  map_zero' := by { ext, simp, },
  map_add' := by { intros, ext, simp, }, }

end normed_group

section normed_space
/-!
### Normed space structure

In this section, if `β` is a normed space, then we show that the space of bounded
continuous functions from `α` to `β` inherits a normed space structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

variables {𝕜 : Type*} [normed_field 𝕜]
variables [topological_space α] [normed_group β] [normed_space 𝕜 β]
variables {f g : α →ᵇ β} {x : α} {C : ℝ}

instance : has_scalar 𝕜 (α →ᵇ β) :=
⟨λ c f, of_normed_group (c • f) (f.continuous.const_smul c) (∥c∥ * ∥f∥) $ λ x,
  trans_rel_right _ (norm_smul _ _)
    (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _))⟩

@[simp] lemma coe_smul (c : 𝕜) (f : α →ᵇ β) : ⇑(c • f) = λ x, c • (f x) := rfl
lemma smul_apply (c : 𝕜) (f : α →ᵇ β) (x : α) : (c • f) x = c • f x := rfl

instance : module 𝕜 (α →ᵇ β) :=
module.of_core $
{ smul     := (•),
  smul_add := λ c f g, ext $ λ x, smul_add c (f x) (g x),
  add_smul := λ c₁ c₂ f, ext $ λ x, add_smul c₁ c₂ (f x),
  mul_smul := λ c₁ c₂ f, ext $ λ x, mul_smul c₁ c₂ (f x),
  one_smul := λ f, ext $ λ x, one_smul 𝕜 (f x) }

instance : normed_space 𝕜 (α →ᵇ β) := ⟨λ c f, norm_of_normed_group_le _
  (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _⟩

variables (𝕜)
/-- The evaluation at a point, as a continuous linear map from `α →ᵇ β` to `β`. -/
def eval_clm (x : α) : (α →ᵇ β) →L[𝕜] β :=
{ to_fun := λ f, f x,
  map_add' := λ f g, by simp only [pi.add_apply, coe_add],
  map_smul' := λ c f, by simp only [coe_smul] }

@[simp] lemma eval_clm_apply (x : α) (f : α →ᵇ β) :
  eval_clm 𝕜 x f = f x := rfl

variables (α β)

/-- The linear map forgetting that a bounded continuous function is bounded. -/
@[simps]
def forget_boundedness_linear_map : (α →ᵇ β) →ₗ[𝕜] C(α, β) :=
{ to_fun := forget_boundedness α β,
  map_smul' := by { intros, ext, simp, },
  map_add' := by { intros, ext, simp, }, }

end normed_space

section normed_ring
/-!
### Normed ring structure

In this section, if `R` is a normed ring, then we show that the space of bounded
continuous functions from `α` to `R` inherits a normed ring structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

variables [topological_space α] {R : Type*} [normed_ring R]

instance : ring (α →ᵇ R) :=
{ one := const α 1,
  mul := λ f g, of_normed_group (f * g) (f.continuous.mul g.continuous) (∥f∥ * ∥g∥) $ λ x,
    le_trans (normed_ring.norm_mul (f x) (g x)) $
      mul_le_mul (f.norm_coe_le_norm x) (g.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _),
  one_mul := λ f, ext $ λ x, one_mul (f x),
  mul_one := λ f, ext $ λ x, mul_one (f x),
  mul_assoc := λ f₁ f₂ f₃, ext $ λ x, mul_assoc _ _ _,
  left_distrib := λ f₁ f₂ f₃, ext $ λ x, left_distrib _ _ _,
  right_distrib := λ f₁ f₂ f₃, ext $ λ x, right_distrib _ _ _,
  .. bounded_continuous_function.add_comm_group }

@[simp] lemma coe_mul (f g : α →ᵇ R) : ⇑(f * g) = f * g := rfl
lemma mul_apply (f g : α →ᵇ R) (x : α) : (f * g) x = f x * g x := rfl

instance : normed_ring (α →ᵇ R) :=
{ norm_mul := λ f g, norm_of_normed_group_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _,
  .. bounded_continuous_function.normed_group }

end normed_ring

section normed_comm_ring
/-!
### Normed commutative ring structure

In this section, if `R` is a normed commutative ring, then we show that the space of bounded
continuous functions from `α` to `R` inherits a normed commutative ring structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

variables [topological_space α] {R : Type*} [normed_comm_ring R]

instance : comm_ring (α →ᵇ R) :=
{ mul_comm := λ f₁ f₂, ext $ λ x, mul_comm _ _,
  .. bounded_continuous_function.ring }

instance : normed_comm_ring (α →ᵇ R) :=
{ .. bounded_continuous_function.comm_ring, .. bounded_continuous_function.normed_group }

end normed_comm_ring

section normed_algebra
/-!
### Normed algebra structure

In this section, if `γ` is a normed algebra, then we show that the space of bounded
continuous functions from `α` to `γ` inherits a normed algebra structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

variables {𝕜 : Type*} [normed_field 𝕜]
variables [topological_space α] [normed_group β] [normed_space 𝕜 β]
variables [normed_ring γ] [normed_algebra 𝕜 γ]
variables {f g : α →ᵇ γ} {x : α} {c : 𝕜}

/-- `bounded_continuous_function.const` as a `ring_hom`. -/
def C : 𝕜 →+* (α →ᵇ γ) :=
{ to_fun    := λ (c : 𝕜), const α ((algebra_map 𝕜 γ) c),
  map_one'  := ext $ λ x, (algebra_map 𝕜 γ).map_one,
  map_mul'  := λ c₁ c₂, ext $ λ x, (algebra_map 𝕜 γ).map_mul _ _,
  map_zero' := ext $ λ x, (algebra_map 𝕜 γ).map_zero,
  map_add'  := λ c₁ c₂, ext $ λ x, (algebra_map 𝕜 γ).map_add _ _ }

instance : algebra 𝕜 (α →ᵇ γ) :=
{ to_ring_hom := C,
  commutes' := λ c f, ext $ λ x, algebra.commutes' _ _,
  smul_def' := λ c f, ext $ λ x, algebra.smul_def' _ _,
  ..bounded_continuous_function.module,
  ..bounded_continuous_function.ring }

@[simp] lemma algebra_map_apply (k : 𝕜) (a : α) :
  algebra_map 𝕜 (α →ᵇ γ) k a = k • 1 :=
by { rw algebra.algebra_map_eq_smul_one, refl, }

instance [nonempty α] : normed_algebra 𝕜 (α →ᵇ γ) :=
{ norm_algebra_map_eq := λ c, begin
    calc ∥ (algebra_map 𝕜 (α →ᵇ γ)).to_fun c∥ = ∥(algebra_map 𝕜 γ) c∥ : _
    ... = ∥c∥ : norm_algebra_map_eq _ _,
    apply norm_const_eq ((algebra_map 𝕜 γ) c), assumption,
  end,
  ..bounded_continuous_function.algebra }

/-!
### Structure as normed module over scalar functions

If `β` is a normed `𝕜`-space, then we show that the space of bounded continuous
functions from `α` to `β` is naturally a module over the algebra of bounded continuous
functions from `α` to `𝕜`. -/

instance has_scalar' : has_scalar (α →ᵇ 𝕜) (α →ᵇ β) :=
⟨λ (f : α →ᵇ 𝕜) (g : α →ᵇ β), of_normed_group (λ x, (f x) • (g x))
(f.continuous.smul g.continuous) (∥f∥ * ∥g∥) (λ x, calc
  ∥f x • g x∥ ≤ ∥f x∥ * ∥g x∥ : normed_space.norm_smul_le _ _
  ... ≤ ∥f∥ * ∥g∥ : mul_le_mul (f.norm_coe_le_norm _) (g.norm_coe_le_norm _) (norm_nonneg _)
    (norm_nonneg _)) ⟩

instance module' : module (α →ᵇ 𝕜) (α →ᵇ β) :=
module.of_core $
{ smul     := (•),
  smul_add := λ c f₁ f₂, ext $ λ x, smul_add _ _ _,
  add_smul := λ c₁ c₂ f, ext $ λ x, add_smul _ _ _,
  mul_smul := λ c₁ c₂ f, ext $ λ x, mul_smul _ _ _,
  one_smul := λ f, ext $ λ x, one_smul 𝕜 (f x) }

lemma norm_smul_le (f : α →ᵇ 𝕜) (g : α →ᵇ β) : ∥f • g∥ ≤ ∥f∥ * ∥g∥ :=
norm_of_normed_group_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _

/- TODO: When `normed_module` has been added to `normed_space.basic`, the above facts
show that the space of bounded continuous functions from `α` to `β` is naturally a normed
module over the algebra of bounded continuous functions from `α` to `𝕜`. -/

end normed_algebra

end bounded_continuous_function
