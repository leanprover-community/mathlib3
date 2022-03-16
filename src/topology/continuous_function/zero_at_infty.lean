/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import topology.continuous_function.bounded

/-!
# Continuous functions vanishing at infinity

The type of continuous functions vanishing at infinity. When the domain is compact
`C(α, β) ≃ (α →C₀ β)` via the identity map. When the codomain is a metric space, every continuous
map which vanishes at infinity is a bounded continuous function. When the domain is a locally
compact space, this type has nice properties.
-/
universes u v w

variables {F : Type*} {α : Type u} {β : Type v} {γ : Type w} [topological_space α]

open_locale bounded_continuous_function topological_space
open filter metric

section preliminaries
--- these results need to be moved to appropriate places

@[simp]
lemma filter.cocompact_eq_bot [compact_space α] : cocompact α = ⊥ :=
has_basis_cocompact.eq_bot_iff.mpr ⟨set.univ, compact_univ, set.compl_univ⟩

end preliminaries

/-- `α →C₀ β)` is the type of continuous functions `α → β` which vanish at infinity from a
topological space to a metric space with a zero element.

When possible, instead of parametrizing results over `(f : α →C₀ β)`,
you should parametrize over `(F : Type*) [zero_at_infty_continuous_map_class F α β] (f : F)`.

When you extend this structure, make sure to extend `zero_at_infty_continuous_map_class`. -/
structure zero_at_infty_continuous_map (α : Type u) (β : Type v)
  [topological_space α] [has_zero β] [topological_space β] extends continuous_map α β :
  Type (max u v) :=
(zero_at_infty' : tendsto to_fun (cocompact α) (𝓝 0))

localized "notation  α ` →C₀ ` β := zero_at_infty_continuous_map α β" in zero_at_infty

/-- `zero_at_infty_continuous_map_class F α β` states that `F` is a type of continuous maps which
vanish at infinity.

You should also extend this typeclass when you extend `zero_at_infty_continuous_map`. -/
class zero_at_infty_continuous_map_class (F α β : Type*) [topological_space α] [has_zero β]
  [topological_space β] extends continuous_map_class F α β :=
(zero_at_infty (f : F) : tendsto f (cocompact α) (𝓝 0))

export zero_at_infty_continuous_map_class (zero_at_infty)

namespace zero_at_infty_continuous_map

section basics

variables [topological_space β] [has_zero β] [zero_at_infty_continuous_map_class F α β]

instance : zero_at_infty_continuous_map_class (α →C₀ β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_continuous := λ f, f.continuous_to_fun,
  zero_at_infty := λ f, f.zero_at_infty' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (α →C₀ β) (λ _, α → β) := fun_like.has_coe_to_fun

instance : has_coe_t F (α →C₀ β) :=
⟨λ f, { to_fun := f, continuous_to_fun := map_continuous f, zero_at_infty' := zero_at_infty f }⟩

@[simp] lemma coe_to_continuous_fun (f : α →C₀ β) : (f.to_continuous_map : α → β) = f := rfl


@[ext] lemma ext {f g : α →C₀ β} (h : ∀ x, f x = g x) : f = g := fun_like.ext _ _ h

/-- Copy of a `zero_at_infinity_continuous_map` with a new `to_fun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : α →C₀ β) (f' : α → β) (h : f' = f) : α →C₀ β :=
{ to_fun := f',
  continuous_to_fun := by { rw h, exact f.continuous_to_fun },
  zero_at_infty' := by { simp_rw h, exact f.zero_at_infty' } }

lemma eq_of_empty [is_empty α] (f g : α →C₀ β) : f = g :=
ext $ is_empty.elim ‹_›

/-
lemma coe_injective : @function.injective (α →C₀ β) (α → β) coe_fn :=
λ f g h, by cases f; cases g; congr'

@[simp] lemma coe_mk (f : α → β) (h : continuous f) :
  ⇑(⟨f, h⟩ : C(α, β)) = f := rfl
-/

/-- A continuous function on a compact space is automatically a continuous function vanishing at
infitnity. -/
@[simps]
def continuous_map.lift [compact_space α] : C(α, β) ≃ (α →C₀ β) :=
{ to_fun := λ f, { to_fun := f, continuous_to_fun := f.continuous, zero_at_infty' := by simp },
  inv_fun := λ f, f,
  left_inv := λ f, by { ext, refl },
  right_inv := λ f, by { ext, refl } }

/-- A continuous function on a compact space is automatically a continuous function vanishing at
infitnity. This is not an instance to avoid type class loops. -/
def zero_at_infty_continuous_map_class.of_compact {G : Type*} [continuous_map_class G α β]
  [compact_space α] : zero_at_infty_continuous_map_class G α β :=
{ coe := λ g, g,
  coe_injective' := λ f g h, fun_like.coe_fn_eq.mp h,
  map_continuous := map_continuous,
  zero_at_infty := by simp }

end basics

section metric

variables [metric_space β] [has_zero β] [zero_at_infty_continuous_map_class F α β]

protected lemma bounded (f : F) : ∃ C, ∀ x y : α, dist ((f : α → β) x) (f y) ≤ C :=
begin
  obtain ⟨K : set α, hK₁, hK₂⟩ := mem_cocompact.mp (tendsto_def.mp (zero_at_infty (f : F)) _
    (metric.closed_ball_mem_nhds (0 : β) zero_lt_one)),
  obtain ⟨C, hC⟩ := (hK₁.image (map_continuous f)).bounded.subset_ball (0 : β),
  refine ⟨max C 1 + max C 1, (λ x y, _)⟩,
  have : ∀ x, f x ∈ metric.closed_ball (0 : β) (max C 1),
  { intro x,
    by_cases hx : x ∈ K,
    { exact (metric.mem_closed_ball.mp $ hC ⟨x, hx, rfl⟩).trans (le_max_left _ _) },
    { exact (metric.mem_closed_ball.mp $ set.mem_preimage.mp (hK₂ hx)).trans (le_max_right _ _) } },
  exact  (dist_triangle (f x) 0 (f y)).trans
    (add_le_add (metric.mem_closed_ball.mp $ this x) (metric.mem_closed_ball'.mp $ this y)),
end

@[priority 100]
instance : bounded_continuous_map_class F α β :=
{ coe := λ f, f,
  coe_injective' := λ f g h, fun_like.coe_fn_eq.mp h,
  map_continuous := λ f, map_continuous f,
  map_bounded := λ f, zero_at_infty_continuous_map.bounded f }

end metric

section algebraic_structure

variables [topological_space β] (x : α)

instance [has_zero β] : has_zero (α →C₀ β) :=
{ zero := { to_continuous_map := 0, zero_at_infty' := tendsto_const_nhds } }

instance [has_zero β] : inhabited (α →C₀ β) :=
{ default := 0 }

@[simp] lemma coe_zero [has_zero β] : ⇑(0 : α →C₀ β) = 0 := rfl
lemma zero_apply [has_zero β] : (0 : α →C₀ β) x = 0 := rfl

instance [mul_zero_class β] [has_continuous_mul β] : has_mul (α →C₀ β) :=
{ mul := λ f g,
  { to_continuous_map := f * g,
    zero_at_infty' := by simpa only [mul_zero] using ((zero_at_infty f).mul (zero_at_infty g) :
      tendsto (λ x : α, f x * g x) (cocompact α) (𝓝 (0 * 0))) } }

@[simp] lemma coe_mul [mul_zero_class β] [has_continuous_mul β] (f g : α →C₀ β) :
  ⇑(f * g) = f * g := rfl
lemma mul_apply [mul_zero_class β] [has_continuous_mul β] (f g : α →C₀ β) :
  (f * g) x = f x * g x := rfl

instance [mul_zero_class β] [has_continuous_mul β] : mul_zero_class (α →C₀ β) :=
fun_like.coe_injective.mul_zero_class _ coe_zero coe_mul

instance [semigroup_with_zero β] [has_continuous_mul β] : semigroup_with_zero (α →C₀ β) :=
fun_like.coe_injective.semigroup_with_zero _ coe_zero coe_mul

instance [add_zero_class β] [has_continuous_add β] : has_add (α →C₀ β) :=
{ add := λ f g,
  { to_continuous_map := f + g,
    zero_at_infty' := by simpa only [add_zero] using ((zero_at_infty f).add (zero_at_infty g) :
      tendsto (λ x : α, f x + g x) (cocompact α) (𝓝 (0 + 0))) } }

@[simp] lemma coe_add [add_zero_class β] [has_continuous_add β] (f g : α →C₀ β) :
  ⇑(f + g) = f + g := rfl
lemma add_apply [add_zero_class β] [has_continuous_add β] (f g : α →C₀ β) :
  (f + g) x = f x + g x := rfl

instance [add_zero_class β] [has_continuous_add β] : add_zero_class (α →C₀ β) :=
fun_like.coe_injective.add_zero_class _ coe_zero coe_add

section add_monoid

variables [add_monoid β] [has_continuous_add β] (f g : α →C₀ β)

@[simp] lemma coe_nsmul_rec : ∀ n, ⇑(nsmul_rec n f) = n • f
| 0 := by rw [nsmul_rec, zero_smul, coe_zero]
| (n + 1) := by rw [nsmul_rec, succ_nsmul, coe_add, coe_nsmul_rec]

instance has_nat_scalar : has_scalar ℕ (α →C₀ β) :=
{ smul := λ n f,
  { to_continuous_map := n • f.to_continuous_map,
    zero_at_infty' := by simpa [coe_nsmul_rec] using (nsmul_rec n f).zero_at_infty' } }

@[simp] lemma coe_nsmul (r : ℕ) (f : α →C₀ β) : ⇑(r • f) = r • f := rfl
@[simp] lemma nsmul_apply (r : ℕ) (f : α →C₀ β) (v : α) : (r • f) v = r • f v := rfl

instance : add_monoid (α →C₀ β) :=
fun_like.coe_injective.add_monoid _ coe_zero coe_add (λ _ _, coe_nsmul _ _)

end add_monoid

instance [add_comm_monoid β] [has_continuous_add β] : add_comm_monoid (α →C₀ β) :=
fun_like.coe_injective.add_comm_monoid _ coe_zero coe_add (λ _ _, coe_nsmul _ _)

section add_group

variables [add_group β] [topological_add_group β] (f g : α →C₀ β)

instance : has_neg (α →C₀ β) :=
{ neg := λ f,
  { to_continuous_map := -f,
    zero_at_infty' := by simpa only [neg_zero] using
      (zero_at_infty f : tendsto f (cocompact α) (𝓝 0)).neg } }

@[simp] lemma coe_neg : ⇑(-f) = -f := rfl
lemma neg_apply : (-f) x = -f x := rfl

instance : has_sub (α →C₀ β) :=
{ sub := λ f g,
  { to_continuous_map := f - g,
    zero_at_infty' :=
    begin
      rw sub_eq_add_neg,
      simpa only [add_zero] using ((zero_at_infty f).add (zero_at_infty (-g)) :
        tendsto (λ x, f x + (-g) x) (cocompact α) (𝓝 (0 + 0))),
    end } }

@[simp] lemma coe_sub : ⇑(f - g) = f - g := rfl
lemma sub_apply : (f - g) x = f x - g x := rfl

@[simp] lemma coe_zsmul_rec : ∀ z, ⇑(zsmul_rec z f) = z • f
| (int.of_nat n) := by rw [zsmul_rec, int.of_nat_eq_coe, coe_nsmul_rec, coe_nat_zsmul]
| -[1+ n] := by rw [zsmul_rec, zsmul_neg_succ_of_nat, coe_neg, coe_nsmul_rec]

instance has_int_scalar : has_scalar ℤ (α →C₀ β) :=
{ smul := λ n f,
  { to_continuous_map := n • f,
    zero_at_infty' := by simpa using (zsmul_rec n f).zero_at_infty' } }

@[simp] lemma coe_zsmul (r : ℤ) (f : α →C₀ β) :
  ⇑(r • f) = r • f := rfl
@[simp] lemma zsmul_apply (r : ℤ) (f : α →C₀ β) (v : α) :
  (r • f) v = r • f v := rfl

instance [add_group β] [topological_add_group β] : add_group (α →C₀ β) :=
fun_like.coe_injective.add_group _ coe_zero coe_add coe_neg coe_sub (λ _ _, coe_nsmul _ _)
  (λ _ _, coe_zsmul _ _)

end add_group

instance [add_comm_group β] [topological_add_group β] : add_comm_group (α →C₀ β) :=
fun_like.coe_injective.add_comm_group _ coe_zero coe_add coe_neg coe_sub (λ _ _, coe_nsmul _ _)
  (λ _ _, coe_zsmul _ _)

instance [has_zero β] {R : Type*} [has_zero R] [smul_with_zero R β]
  [has_continuous_const_smul R β] : has_scalar R (α →C₀ β) :=
{ smul := λ r f,
  { to_continuous_map := r • f,
    zero_at_infty' := by simpa [smul_zero] using
      (zero_at_infty f : tendsto f (cocompact α) (𝓝 0)).const_smul r } }

@[simp] lemma coe_smul [has_zero β] {R : Type*} [has_zero R] [smul_with_zero R β]
  [has_continuous_const_smul R β] (r : R) (f : α →C₀ β) : ⇑(r • f) = r • f := rfl

lemma smul_apply [has_zero β] {R : Type*} [has_zero R] [smul_with_zero R β]
  [has_continuous_const_smul R β] (r : R) (f : α →C₀ β) (x : α) : (r • f) x = r • f x := rfl

instance [has_zero β] {R : Type*} [has_zero R] [smul_with_zero R β]
  [has_continuous_const_smul R β] : smul_with_zero R (α →C₀ β) :=
function.injective.smul_with_zero ⟨_, coe_zero⟩ fun_like.coe_injective coe_smul

instance [has_zero β] {R : Type*} [monoid_with_zero R] [mul_action_with_zero R β]
  [has_continuous_const_smul R β] : mul_action_with_zero R (α →C₀ β) :=
function.injective.mul_action_with_zero ⟨_, coe_zero⟩ fun_like.coe_injective coe_smul

instance [add_comm_monoid β] [has_continuous_add β] {R : Type*} [comm_semiring R] [module R β]
  [has_continuous_const_smul R β] : module R (α →C₀ β) :=
function.injective.module R ⟨_, coe_zero, coe_add⟩ fun_like.coe_injective coe_smul

instance [non_unital_semiring β] [has_continuous_add β] [has_continuous_mul β] :
  non_unital_semiring (α →C₀ β) :=
fun_like.coe_injective.non_unital_semiring _ coe_zero coe_add coe_mul (λ _ _, coe_nsmul _ _)

end algebraic_structure

end zero_at_infty_continuous_map
