/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import topology.algebra.monoid
import algebra.group.pi
import topology.homeomorph

/-!
# Topological group with zero

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `has_continuous_inv₀` to be a mixin typeclass a type with `has_inv` and
`has_zero` (e.g., a `group_with_zero`) such that `λ x, x⁻¹` is continuous at all nonzero points. Any
normed (semi)field has this property. Currently the only example of `has_continuous_inv₀` in
`mathlib` which is not a normed field is the type `nnnreal` (a.k.a. `ℝ≥0`) of nonnegative real
numbers.

Then we prove lemmas about continuity of `x ↦ x⁻¹` and `f / g` providing dot-style `*.inv'` and
`*.div` operations on `filter.tendsto`, `continuous_at`, `continuous_within_at`, `continuous_on`,
and `continuous`. As a special case, we provide `*.div_const` operations that require only
`group_with_zero` and `has_continuous_mul` instances.

All lemmas about `(⁻¹)` use `inv'` in their names because lemmas without `'` are used for
`topological_group`s. We also use `'` in the typeclass name `has_continuous_inv₀` for the sake of
consistency of notation.

On a `group_with_zero` with continuous multiplication, we also define left and right multiplication
as homeomorphisms.
-/

open_locale topology filter
open filter function

/-!
### A group with zero with continuous multiplication

If `G₀` is a group with zero with continuous `(*)`, then `(/y)` is continuous for any `y`. In this
section we prove lemmas that immediately follow from this fact providing `*.div_const` dot-style
operations on `filter.tendsto`, `continuous_at`, `continuous_within_at`, `continuous_on`, and
`continuous`.
-/

variables {α β G₀ : Type*}

section div_const

variables [group_with_zero G₀] [topological_space G₀] [has_continuous_mul G₀]
  {f : α → G₀} {s : set α} {l : filter α}

lemma filter.tendsto.div_const {x : G₀} (hf : tendsto f l (𝓝 x)) (y : G₀) :
  tendsto (λa, f a / y) l (𝓝 (x / y)) :=
by simpa only [div_eq_mul_inv] using hf.mul tendsto_const_nhds

variables [topological_space α]

lemma continuous_at.div_const {a : α} (hf : continuous_at f a) (y : G₀) :
  continuous_at (λ x, f x / y) a :=
by simpa only [div_eq_mul_inv] using hf.mul continuous_at_const

lemma continuous_within_at.div_const {a} (hf : continuous_within_at f s a) (y : G₀) :
  continuous_within_at (λ x, f x / y) s a :=
hf.div_const _

lemma continuous_on.div_const (hf : continuous_on f s) (y : G₀) : continuous_on (λ x, f x / y) s :=
by simpa only [div_eq_mul_inv] using hf.mul continuous_on_const

@[continuity] lemma continuous.div_const (hf : continuous f) (y : G₀) :
  continuous (λ x, f x / y) :=
by simpa only [div_eq_mul_inv] using hf.mul continuous_const

end div_const

/-- A type with `0` and `has_inv` such that `λ x, x⁻¹` is continuous at all nonzero points. Any
normed (semi)field has this property. -/
class has_continuous_inv₀ (G₀ : Type*) [has_zero G₀] [has_inv G₀] [topological_space G₀] : Prop :=
(continuous_at_inv₀ : ∀ ⦃x : G₀⦄, x ≠ 0 → continuous_at has_inv.inv x)

export has_continuous_inv₀ (continuous_at_inv₀)

section inv₀

variables [has_zero G₀] [has_inv G₀] [topological_space G₀] [has_continuous_inv₀ G₀]
  {l : filter α} {f : α → G₀} {s : set α} {a : α}

/-!
### Continuity of `λ x, x⁻¹` at a non-zero point

We define `topological_group_with_zero` to be a `group_with_zero` such that the operation `x ↦ x⁻¹`
is continuous at all nonzero points. In this section we prove dot-style `*.inv'` lemmas for
`filter.tendsto`, `continuous_at`, `continuous_within_at`, `continuous_on`, and `continuous`.
-/

lemma tendsto_inv₀ {x : G₀}  (hx : x ≠ 0) : tendsto has_inv.inv (𝓝 x) (𝓝 x⁻¹) :=
continuous_at_inv₀ hx

lemma continuous_on_inv₀ : continuous_on (has_inv.inv : G₀ → G₀) {0}ᶜ :=
λ x hx, (continuous_at_inv₀ hx).continuous_within_at

/-- If a function converges to a nonzero value, its inverse converges to the inverse of this value.
We use the name `tendsto.inv₀` as `tendsto.inv` is already used in multiplicative topological
groups. -/
lemma filter.tendsto.inv₀ {a : G₀} (hf : tendsto f l (𝓝 a))
  (ha : a ≠ 0) :
  tendsto (λ x, (f x)⁻¹) l (𝓝 a⁻¹) :=
(tendsto_inv₀ ha).comp hf

variables [topological_space α]

lemma continuous_within_at.inv₀ (hf : continuous_within_at f s a) (ha : f a ≠ 0) :
  continuous_within_at (λ x, (f x)⁻¹) s a :=
hf.inv₀ ha

lemma continuous_at.inv₀ (hf : continuous_at f a) (ha : f a ≠ 0) :
  continuous_at (λ x, (f x)⁻¹) a :=
hf.inv₀ ha

@[continuity] lemma continuous.inv₀ (hf : continuous f) (h0 : ∀ x, f x ≠ 0) :
  continuous (λ x, (f x)⁻¹) :=
continuous_iff_continuous_at.2 $ λ x, (hf.tendsto x).inv₀ (h0 x)

lemma continuous_on.inv₀ (hf : continuous_on f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
  continuous_on (λ x, (f x)⁻¹) s :=
λ x hx, (hf x hx).inv₀ (h0 x hx)

end inv₀

/-- If `G₀` is a group with zero with topology such that `x ↦ x⁻¹` is continuous at all nonzero
points. Then the coercion `Mˣ → M` is a topological embedding. -/
theorem units.embedding_coe₀ [group_with_zero G₀] [topological_space G₀] [has_continuous_inv₀ G₀] :
  embedding (coe : G₀ˣ → G₀) :=
units.embedding_coe_mk $ continuous_on_inv₀.mono $ λ x, is_unit.ne_zero

/-!
### Continuity of division

If `G₀` is a `group_with_zero` with `x ↦ x⁻¹` continuous at all nonzero points and `(*)`, then
division `(/)` is continuous at any point where the denominator is continuous.
-/

section div

variables [group_with_zero G₀] [topological_space G₀] [has_continuous_inv₀ G₀]
  [has_continuous_mul G₀] {f g : α → G₀}

lemma filter.tendsto.div {l : filter α} {a b : G₀} (hf : tendsto f l (𝓝 a))
  (hg : tendsto g l (𝓝 b)) (hy : b ≠ 0) :
  tendsto (f / g) l (𝓝 (a / b)) :=
by simpa only [div_eq_mul_inv] using hf.mul (hg.inv₀ hy)

lemma filter.tendsto_mul_iff_of_ne_zero [t1_space G₀]
  {f g : α → G₀} {l : filter α} {x y : G₀}
  (hg : tendsto g l (𝓝 y)) (hy : y ≠ 0) :
  tendsto (λ n, f n * g n) l (𝓝 $ x * y) ↔ tendsto f l (𝓝 x) :=
begin
  refine ⟨λ hfg, _, λ hf, hf.mul hg⟩,
  rw ←mul_div_cancel x hy,
  refine tendsto.congr' _ (hfg.div hg hy),
  refine eventually.mp (hg.eventually_ne hy) (eventually_of_forall (λ n hn, mul_div_cancel _ hn)),
end

variables [topological_space α] [topological_space β] {s : set α} {a : α}

lemma continuous_within_at.div (hf : continuous_within_at f s a) (hg : continuous_within_at g s a)
  (h₀ : g a ≠ 0) :
  continuous_within_at (f / g) s a :=
hf.div hg h₀

lemma continuous_on.div (hf : continuous_on f s) (hg : continuous_on g s) (h₀ : ∀ x ∈ s, g x ≠ 0) :
  continuous_on (f / g) s :=
λ x hx, (hf x hx).div (hg x hx) (h₀ x hx)

/-- Continuity at a point of the result of dividing two functions continuous at that point, where
the denominator is nonzero. -/
lemma continuous_at.div (hf : continuous_at f a) (hg : continuous_at g a) (h₀ : g a ≠ 0) :
  continuous_at (f / g) a :=
hf.div hg h₀

@[continuity] lemma continuous.div (hf : continuous f) (hg : continuous g) (h₀ : ∀ x, g x ≠ 0) :
  continuous (f / g) :=
by simpa only [div_eq_mul_inv] using hf.mul (hg.inv₀ h₀)

lemma continuous_on_div : continuous_on (λ p : G₀ × G₀, p.1 / p.2) {p | p.2 ≠ 0} :=
continuous_on_fst.div continuous_on_snd $ λ _, id

/-- The function `f x / g x` is discontinuous when `g x = 0`.
However, under appropriate conditions, `h x (f x / g x)` is still continuous.
The condition is that if `g a = 0` then `h x y` must tend to `h a 0` when `x` tends to `a`,
with no information about `y`. This is represented by the `⊤` filter.
Note: `filter.tendsto_prod_top_iff` characterizes this convergence in uniform spaces.
See also `filter.prod_top` and `filter.mem_prod_top`. -/
lemma continuous_at.comp_div_cases {f g : α → G₀} (h : α → G₀ → β)
  (hf : continuous_at f a) (hg : continuous_at g a)
  (hh : g a ≠ 0 → continuous_at ↿h (a, f a / g a))
  (h2h : g a = 0 → tendsto ↿h (𝓝 a ×ᶠ ⊤) (𝓝 (h a 0))) :
  continuous_at (λ x, h x (f x / g x)) a :=
begin
  show continuous_at (↿h ∘ (λ x, (x, f x / g x))) a,
  by_cases hga : g a = 0,
  { rw [continuous_at], simp_rw [comp_app, hga, div_zero],
    exact (h2h hga).comp (continuous_at_id.prod_mk tendsto_top) },
  { exact continuous_at.comp (hh hga) (continuous_at_id.prod (hf.div hg hga)) }
end

/-- `h x (f x / g x)` is continuous under certain conditions, even if the denominator is sometimes
  `0`. See docstring of `continuous_at.comp_div_cases`. -/
lemma continuous.comp_div_cases {f g : α → G₀} (h : α → G₀ → β)
  (hf : continuous f) (hg : continuous g)
  (hh : ∀ a, g a ≠ 0 → continuous_at ↿h (a, f a / g a))
  (h2h : ∀ a, g a = 0 → tendsto ↿h (𝓝 a ×ᶠ ⊤) (𝓝 (h a 0))) :
  continuous (λ x, h x (f x / g x)) :=
continuous_iff_continuous_at.mpr $
  λ a, hf.continuous_at.comp_div_cases _ hg.continuous_at (hh a) (h2h a)

end div

/-! ### Left and right multiplication as homeomorphisms -/

namespace homeomorph

variables [topological_space α] [group_with_zero α] [has_continuous_mul α]

/-- Left multiplication by a nonzero element in a `group_with_zero` with continuous multiplication
is a homeomorphism of the underlying type. -/
protected def mul_left₀ (c : α) (hc : c ≠ 0) : α ≃ₜ α :=
{ continuous_to_fun := continuous_mul_left _,
  continuous_inv_fun := continuous_mul_left _,
  .. equiv.mul_left₀ c hc }

/-- Right multiplication by a nonzero element in a `group_with_zero` with continuous multiplication
is a homeomorphism of the underlying type. -/
protected def mul_right₀ (c : α) (hc : c ≠ 0) : α ≃ₜ α :=
{ continuous_to_fun := continuous_mul_right _,
  continuous_inv_fun := continuous_mul_right _,
  .. equiv.mul_right₀ c hc }

@[simp] lemma coe_mul_left₀ (c : α) (hc : c ≠ 0) : ⇑(homeomorph.mul_left₀ c hc) = (*) c := rfl

@[simp] lemma mul_left₀_symm_apply (c : α) (hc : c ≠ 0) :
  ((homeomorph.mul_left₀ c hc).symm : α → α) = (*) c⁻¹ := rfl

@[simp] lemma coe_mul_right₀ (c : α) (hc : c ≠ 0) :
  ⇑(homeomorph.mul_right₀ c hc) = λ x, x * c := rfl

@[simp] lemma mul_right₀_symm_apply (c : α) (hc : c ≠ 0) :
  ((homeomorph.mul_right₀ c hc).symm : α → α) = λ x, x * c⁻¹ := rfl

end homeomorph

section zpow

variables [group_with_zero G₀] [topological_space G₀] [has_continuous_inv₀ G₀]
  [has_continuous_mul G₀]

lemma continuous_at_zpow₀ (x : G₀) (m : ℤ) (h : x ≠ 0 ∨ 0 ≤ m) : continuous_at (λ x, x ^ m) x :=
begin
  cases m,
  { simpa only [zpow_of_nat] using continuous_at_pow x m },
  { simp only [zpow_neg_succ_of_nat],
    have hx : x ≠ 0, from h.resolve_right (int.neg_succ_of_nat_lt_zero m).not_le,
    exact (continuous_at_pow x (m + 1)).inv₀ (pow_ne_zero _ hx) }
end

lemma continuous_on_zpow₀ (m : ℤ) : continuous_on (λ x : G₀, x ^ m) {0}ᶜ :=
λ x hx, (continuous_at_zpow₀ _ _ (or.inl hx)).continuous_within_at

lemma filter.tendsto.zpow₀ {f : α → G₀} {l : filter α} {a : G₀} (hf : tendsto f l (𝓝 a)) (m : ℤ)
  (h : a ≠ 0 ∨ 0 ≤ m) :
  tendsto (λ x, (f x) ^ m) l (𝓝 (a ^ m)) :=
(continuous_at_zpow₀ _ m h).tendsto.comp hf

variables {X : Type*} [topological_space X] {a : X} {s : set X} {f : X → G₀}

lemma continuous_at.zpow₀ (hf : continuous_at f a) (m : ℤ) (h : f a ≠ 0 ∨ 0 ≤ m) :
  continuous_at (λ x, (f x) ^ m) a :=
hf.zpow₀ m h

lemma continuous_within_at.zpow₀ (hf : continuous_within_at f s a) (m : ℤ) (h : f a ≠ 0 ∨ 0 ≤ m) :
  continuous_within_at (λ x, f x ^ m) s a :=
hf.zpow₀ m h

lemma continuous_on.zpow₀ (hf : continuous_on f s) (m : ℤ) (h : ∀ a ∈ s, f a ≠ 0 ∨ 0 ≤ m) :
  continuous_on (λ x, f x ^ m) s :=
λ a ha, (hf a ha).zpow₀ m (h a ha)

@[continuity] lemma continuous.zpow₀ (hf : continuous f) (m : ℤ) (h0 : ∀ a, f a ≠ 0 ∨ 0 ≤ m) :
  continuous (λ x, (f x) ^ m) :=
continuous_iff_continuous_at.2 $ λ x, (hf.tendsto x).zpow₀ m (h0 x)

end zpow
