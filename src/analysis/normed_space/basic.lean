/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import algebra.algebra.restrict_scalars
import algebra.algebra.subalgebra
import data.matrix.basic
import topology.algebra.group_completion
import topology.instances.ennreal
import topology.metric_space.completion
import topology.sequences
import analysis.normed.group.basic

/-!
# Normed spaces

In this file we define (semi)normed rings, fields, spaces, and algebras. We also prove some theorems
about these definitions.
-/

variables {α : Type*} {β : Type*} {γ : Type*} {ι : Type*}

noncomputable theory
open filter metric
open_locale topological_space big_operators nnreal ennreal uniformity pointwise

section semi_normed_ring

/-- A seminormed ring is a ring endowed with a seminorm which satisfies the inequality
`∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class semi_normed_ring (α : Type*) extends has_norm α, ring α, pseudo_metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

/-- A normed ring is a ring endowed with a norm which satisfies the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class normed_ring (α : Type*) extends has_norm α, ring α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

/-- A normed ring is a seminormed ring. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_ring.to_semi_normed_ring [β : normed_ring α] : semi_normed_ring α :=
{ ..β }

/-- A seminormed commutative ring is a commutative ring endowed with a seminorm which satisfies
the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class semi_normed_comm_ring (α : Type*) extends semi_normed_ring α :=
(mul_comm : ∀ x y : α, x * y = y * x)

/-- A normed commutative ring is a commutative ring endowed with a norm which satisfies
the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class normed_comm_ring (α : Type*) extends normed_ring α :=
(mul_comm : ∀ x y : α, x * y = y * x)

/-- A normed commutative ring is a seminormed commutative ring. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_comm_ring.to_semi_normed_comm_ring [β : normed_comm_ring α] :
  semi_normed_comm_ring α := { ..β }

instance : normed_comm_ring punit :=
{ norm_mul := λ _ _, by simp,
  ..punit.normed_group,
  ..punit.comm_ring, }

/-- A mixin class with the axiom `∥1∥ = 1`. Many `normed_ring`s and all `normed_field`s satisfy this
axiom. -/
class norm_one_class (α : Type*) [has_norm α] [has_one α] : Prop :=
(norm_one : ∥(1:α)∥ = 1)

export norm_one_class (norm_one)

attribute [simp] norm_one

@[simp] lemma nnnorm_one [semi_normed_group α] [has_one α] [norm_one_class α] : ∥(1 : α)∥₊ = 1 :=
nnreal.eq norm_one

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_comm_ring.to_comm_ring [β : semi_normed_comm_ring α] : comm_ring α := { ..β }

@[priority 100] -- see Note [lower instance priority]
instance normed_ring.to_normed_group [β : normed_ring α] : normed_group α := { ..β }

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_ring.to_semi_normed_group [β : semi_normed_ring α] :
  semi_normed_group α := { ..β }

instance prod.norm_one_class [normed_group α] [has_one α] [norm_one_class α]
  [normed_group β] [has_one β] [norm_one_class β] :
  norm_one_class (α × β) :=
⟨by simp [prod.norm_def]⟩

variables [semi_normed_ring α]

lemma norm_mul_le (a b : α) : (∥a*b∥) ≤ (∥a∥) * (∥b∥) :=
semi_normed_ring.norm_mul _ _

/-- A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance subalgebra.semi_normed_ring {𝕜 : Type*} {_ : comm_ring 𝕜}
  {E : Type*} [semi_normed_ring E] {_ : algebra 𝕜 E} (s : subalgebra 𝕜 E) : semi_normed_ring s :=
{ norm_mul := λ a b, norm_mul_le a.1 b.1,
  ..s.to_submodule.semi_normed_group }

/-- A subalgebra of a normed ring is also a normed ring, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance subalgebra.normed_ring {𝕜 : Type*} {_ : comm_ring 𝕜}
  {E : Type*} [normed_ring E] {_ : algebra 𝕜 E} (s : subalgebra 𝕜 E) : normed_ring s :=
{ ..s.semi_normed_ring }

lemma list.norm_prod_le' : ∀ {l : list α}, l ≠ [] → ∥l.prod∥ ≤ (l.map norm).prod
| [] h := (h rfl).elim
| [a] _ := by simp
| (a :: b :: l) _ :=
  begin
    rw [list.map_cons, list.prod_cons, @list.prod_cons _ _ _ ∥a∥],
    refine le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_left _ (norm_nonneg _)),
    exact list.norm_prod_le' (list.cons_ne_nil b l)
  end

lemma list.norm_prod_le [norm_one_class α] : ∀ l : list α, ∥l.prod∥ ≤ (l.map norm).prod
| [] := by simp
| (a::l) := list.norm_prod_le' (list.cons_ne_nil a l)

lemma finset.norm_prod_le' {α : Type*} [normed_comm_ring α] (s : finset ι) (hs : s.nonempty)
  (f : ι → α) :
  ∥∏ i in s, f i∥ ≤ ∏ i in s, ∥f i∥ :=
begin
  rcases s with ⟨⟨l⟩, hl⟩,
  have : l.map f ≠ [], by simpa using hs,
  simpa using list.norm_prod_le' this
end

lemma finset.norm_prod_le {α : Type*} [normed_comm_ring α] [norm_one_class α] (s : finset ι)
  (f : ι → α) :
  ∥∏ i in s, f i∥ ≤ ∏ i in s, ∥f i∥ :=
begin
  rcases s with ⟨⟨l⟩, hl⟩,
  simpa using (l.map f).norm_prod_le
end

/-- If `α` is a seminormed ring, then `∥a^n∥≤ ∥a∥^n` for `n > 0`. See also `norm_pow_le`. -/
lemma norm_pow_le' (a : α) : ∀ {n : ℕ}, 0 < n → ∥a^n∥ ≤ ∥a∥^n
| 1 h := by simp
| (n+2) h := by { rw [pow_succ _ (n+1),  pow_succ _ (n+1)],
  exact le_trans (norm_mul_le a (a^(n+1)))
           (mul_le_mul (le_refl _)
                       (norm_pow_le' (nat.succ_pos _)) (norm_nonneg _) (norm_nonneg _)) }

/-- If `α` is a seminormed ring with `∥1∥=1`, then `∥a^n∥≤ ∥a∥^n`. See also `norm_pow_le'`. -/
lemma norm_pow_le [norm_one_class α] (a : α) : ∀ (n : ℕ), ∥a^n∥ ≤ ∥a∥^n
| 0 := by simp
| (n+1) := norm_pow_le' a n.zero_lt_succ

lemma eventually_norm_pow_le (a : α) : ∀ᶠ (n:ℕ) in at_top, ∥a ^ n∥ ≤ ∥a∥ ^ n :=
eventually_at_top.mpr ⟨1, λ b h, norm_pow_le' a (nat.succ_le_iff.mp h)⟩

/-- In a seminormed ring, the left-multiplication `add_monoid_hom` is bounded. -/
lemma mul_left_bound (x : α) :
  ∀ (y:α), ∥add_monoid_hom.mul_left x y∥ ≤ ∥x∥ * ∥y∥ :=
norm_mul_le x

/-- In a seminormed ring, the right-multiplication `add_monoid_hom` is bounded. -/
lemma mul_right_bound (x : α) :
  ∀ (y:α), ∥add_monoid_hom.mul_right x y∥ ≤ ∥x∥ * ∥y∥ :=
λ y, by {rw mul_comm, convert norm_mul_le y x}

/-- Seminormed ring structure on the product of two seminormed rings, using the sup norm. -/
instance prod.semi_normed_ring [semi_normed_ring β] : semi_normed_ring (α × β) :=
{ norm_mul := assume x y,
  calc
    ∥x * y∥ = ∥(x.1*y.1, x.2*y.2)∥ : rfl
        ... = (max ∥x.1*y.1∥  ∥x.2*y.2∥) : rfl
        ... ≤ (max (∥x.1∥*∥y.1∥) (∥x.2∥*∥y.2∥)) :
          max_le_max (norm_mul_le (x.1) (y.1)) (norm_mul_le (x.2) (y.2))
        ... = (max (∥x.1∥*∥y.1∥) (∥y.2∥*∥x.2∥)) : by simp[mul_comm]
        ... ≤ (max (∥x.1∥) (∥x.2∥)) * (max (∥y.2∥) (∥y.1∥)) :
          by apply max_mul_mul_le_max_mul_max; simp [norm_nonneg]
        ... = (max (∥x.1∥) (∥x.2∥)) * (max (∥y.1∥) (∥y.2∥)) : by simp [max_comm]
        ... = (∥x∥*∥y∥) : rfl,
  ..prod.semi_normed_group }

/-- Seminormed group instance (using sup norm of sup norm) for matrices over a seminormed ring. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
def matrix.semi_normed_group {n m : Type*} [fintype n] [fintype m] :
  semi_normed_group (matrix n m α) :=
pi.semi_normed_group

local attribute [instance] matrix.semi_normed_group

lemma semi_norm_matrix_le_iff {n m : Type*} [fintype n] [fintype m] {r : ℝ} (hr : 0 ≤ r)
  {A : matrix n m α} :
  ∥A∥ ≤ r ↔ ∀ i j, ∥A i j∥ ≤ r :=
by simp [pi_semi_norm_le_iff hr]

end semi_normed_ring

section normed_ring

variables [normed_ring α]

lemma units.norm_pos [nontrivial α] (x : units α) : 0 < ∥(x:α)∥ :=
norm_pos_iff.mpr (units.ne_zero x)

/-- Normed ring structure on the product of two normed rings, using the sup norm. -/
instance prod.normed_ring [normed_ring β] : normed_ring (α × β) :=
{ norm_mul := norm_mul_le,
  ..prod.semi_normed_group }

/-- Normed group instance (using sup norm of sup norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
def matrix.normed_group {n m : Type*} [fintype n] [fintype m] : normed_group (matrix n m α) :=
pi.normed_group

end normed_ring

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_ring_top_monoid [semi_normed_ring α] : has_continuous_mul α :=
⟨ continuous_iff_continuous_at.2 $ λ x, tendsto_iff_norm_tendsto_zero.2 $
    begin
      have : ∀ e : α × α, ∥e.1 * e.2 - x.1 * x.2∥ ≤ ∥e.1∥ * ∥e.2 - x.2∥ + ∥e.1 - x.1∥ * ∥x.2∥,
      { intro e,
        calc ∥e.1 * e.2 - x.1 * x.2∥ ≤ ∥e.1 * (e.2 - x.2) + (e.1 - x.1) * x.2∥ :
          by rw [mul_sub, sub_mul, sub_add_sub_cancel]
        ... ≤ ∥e.1∥ * ∥e.2 - x.2∥ + ∥e.1 - x.1∥ * ∥x.2∥ :
          norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _) },
      refine squeeze_zero (λ e, norm_nonneg _) this _,
      convert ((continuous_fst.tendsto x).norm.mul ((continuous_snd.tendsto x).sub
        tendsto_const_nhds).norm).add
        (((continuous_fst.tendsto x).sub tendsto_const_nhds).norm.mul _),
      show tendsto _ _ _, from tendsto_const_nhds,
      simp
    end ⟩

/-- A seminormed ring is a topological ring. -/
@[priority 100] -- see Note [lower instance priority]
instance semi_normed_top_ring [semi_normed_ring α] : topological_ring α := { }

/-- A normed field is a field with a norm satisfying ∥x y∥ = ∥x∥ ∥y∥. -/
class normed_field (α : Type*) extends has_norm α, field α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul' : ∀ a b, norm (a * b) = norm a * norm b)

/-- A nondiscrete normed field is a normed field in which there is an element of norm different from
`0` and `1`. This makes it possible to bring any element arbitrarily close to `0` by multiplication
by the powers of any element, and thus to relate algebra and topology. -/
class nondiscrete_normed_field (α : Type*) extends normed_field α :=
(non_trivial : ∃x:α, 1<∥x∥)

namespace normed_field

section normed_field

variables [normed_field α]

@[simp] lemma norm_mul (a b : α) : ∥a * b∥ = ∥a∥ * ∥b∥ :=
normed_field.norm_mul' a b

@[priority 100] -- see Note [lower instance priority]
instance to_normed_comm_ring : normed_comm_ring α :=
{ norm_mul := λ a b, (norm_mul a b).le, ..‹normed_field α› }

@[priority 900]
instance to_norm_one_class : norm_one_class α :=
⟨mul_left_cancel₀ (mt norm_eq_zero.1 (@one_ne_zero α _ _)) $
  by rw [← norm_mul, mul_one, mul_one]⟩

@[simp] lemma nnnorm_mul (a b : α) : ∥a * b∥₊ = ∥a∥₊ * ∥b∥₊ :=
nnreal.eq $ norm_mul a b

/-- `norm` as a `monoid_hom`. -/
@[simps] def norm_hom : monoid_with_zero_hom α ℝ := ⟨norm, norm_zero, norm_one, norm_mul⟩

/-- `nnnorm` as a `monoid_hom`. -/
@[simps] def nnnorm_hom : monoid_with_zero_hom α ℝ≥0 :=
⟨nnnorm, nnnorm_zero, nnnorm_one, nnnorm_mul⟩

@[simp] lemma norm_pow (a : α) : ∀ (n : ℕ), ∥a ^ n∥ = ∥a∥ ^ n :=
(norm_hom.to_monoid_hom : α →* ℝ).map_pow a

@[simp] lemma nnnorm_pow (a : α) (n : ℕ) : ∥a ^ n∥₊ = ∥a∥₊ ^ n :=
(nnnorm_hom.to_monoid_hom : α →* ℝ≥0).map_pow a n

@[simp] lemma norm_prod (s : finset β) (f : β → α) :
  ∥∏ b in s, f b∥ = ∏ b in s, ∥f b∥ :=
(norm_hom.to_monoid_hom : α →* ℝ).map_prod f s

@[simp] lemma nnnorm_prod (s : finset β) (f : β → α) :
  ∥∏ b in s, f b∥₊ = ∏ b in s, ∥f b∥₊ :=
(nnnorm_hom.to_monoid_hom : α →* ℝ≥0).map_prod f s

@[simp] lemma norm_div (a b : α) : ∥a / b∥ = ∥a∥ / ∥b∥ :=
(norm_hom : monoid_with_zero_hom α ℝ).map_div a b

@[simp] lemma nnnorm_div (a b : α) : ∥a / b∥₊ = ∥a∥₊ / ∥b∥₊ :=
(nnnorm_hom : monoid_with_zero_hom α ℝ≥0).map_div a b

@[simp] lemma norm_inv (a : α) : ∥a⁻¹∥ = ∥a∥⁻¹ :=
(norm_hom : monoid_with_zero_hom α ℝ).map_inv a

@[simp] lemma nnnorm_inv (a : α) : ∥a⁻¹∥₊ = ∥a∥₊⁻¹ :=
nnreal.eq $ by simp

@[simp] lemma norm_fpow : ∀ (a : α) (n : ℤ), ∥a^n∥ = ∥a∥^n :=
(norm_hom : monoid_with_zero_hom α ℝ).map_fpow

@[simp] lemma nnnorm_fpow : ∀ (a : α) (n : ℤ), ∥a ^ n∥₊ = ∥a∥₊ ^ n :=
(nnnorm_hom : monoid_with_zero_hom α ℝ≥0).map_fpow

@[priority 100] -- see Note [lower instance priority]
instance : has_continuous_inv₀ α :=
begin
  refine ⟨λ r r0, tendsto_iff_norm_tendsto_zero.2 _⟩,
  have r0' : 0 < ∥r∥ := norm_pos_iff.2 r0,
  rcases exists_between r0' with ⟨ε, ε0, εr⟩,
  have : ∀ᶠ e in 𝓝 r, ∥e⁻¹ - r⁻¹∥ ≤ ∥r - e∥ / ∥r∥ / ε,
  { filter_upwards [(is_open_lt continuous_const continuous_norm).eventually_mem εr],
    intros e he,
    have e0 : e ≠ 0 := norm_pos_iff.1 (ε0.trans he),
    calc ∥e⁻¹ - r⁻¹∥ = ∥r - e∥ / ∥r∥ / ∥e∥ : by field_simp [mul_comm]
    ... ≤ ∥r - e∥ / ∥r∥ / ε :
      div_le_div_of_le_left (div_nonneg (norm_nonneg _) (norm_nonneg _)) ε0 he.le },
  refine squeeze_zero' (eventually_of_forall $ λ _, norm_nonneg _) this _,
  refine (continuous_const.sub continuous_id).norm.div_const.div_const.tendsto' _ _ _,
  simp
end

end normed_field

variables (α) [nondiscrete_normed_field α]

lemma exists_one_lt_norm : ∃x : α, 1 < ∥x∥ := ‹nondiscrete_normed_field α›.non_trivial

lemma exists_norm_lt_one : ∃x : α, 0 < ∥x∥ ∧ ∥x∥ < 1 :=
begin
  rcases exists_one_lt_norm α with ⟨y, hy⟩,
  refine ⟨y⁻¹, _, _⟩,
  { simp only [inv_eq_zero, ne.def, norm_pos_iff],
    rintro rfl,
    rw norm_zero at hy,
    exact lt_asymm zero_lt_one hy },
  { simp [inv_lt_one hy] }
end

lemma exists_lt_norm (r : ℝ) : ∃ x : α, r < ∥x∥ :=
let ⟨w, hw⟩ := exists_one_lt_norm α in
let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw in
⟨w^n, by rwa norm_pow⟩

lemma exists_norm_lt {r : ℝ} (hr : 0 < r) : ∃ x : α, 0 < ∥x∥ ∧ ∥x∥ < r :=
let ⟨w, hw⟩ := exists_one_lt_norm α in
let ⟨n, hle, hlt⟩ := exists_int_pow_near' hr hw in
⟨w^n, by { rw norm_fpow; exact fpow_pos_of_pos (lt_trans zero_lt_one hw) _},
by rwa norm_fpow⟩

variable {α}

@[instance]
lemma punctured_nhds_ne_bot (x : α) : ne_bot (𝓝[{x}ᶜ] x) :=
begin
  rw [← mem_closure_iff_nhds_within_ne_bot, metric.mem_closure_iff],
  rintros ε ε0,
  rcases normed_field.exists_norm_lt α ε0 with ⟨b, hb0, hbε⟩,
  refine ⟨x + b, mt (set.mem_singleton_iff.trans add_right_eq_self).1 $ norm_pos_iff.1 hb0, _⟩,
  rwa [dist_comm, dist_eq_norm, add_sub_cancel'],
end

@[instance]
lemma nhds_within_is_unit_ne_bot : ne_bot (𝓝[{x : α | is_unit x}] 0) :=
by simpa only [is_unit_iff_ne_zero] using punctured_nhds_ne_bot (0:α)

end normed_field

instance : normed_field ℝ :=
{ norm_mul' := abs_mul,
  .. real.normed_group }

instance : nondiscrete_normed_field ℝ :=
{ non_trivial := ⟨2, by { unfold norm, rw abs_of_nonneg; norm_num }⟩ }

namespace real

lemma norm_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ∥x∥ = x :=
abs_of_nonneg hx

lemma norm_of_nonpos {x : ℝ} (hx : x ≤ 0) : ∥x∥ = -x :=
abs_of_nonpos hx

@[simp] lemma norm_coe_nat (n : ℕ) : ∥(n : ℝ)∥ = n := abs_of_nonneg n.cast_nonneg

@[simp] lemma nnnorm_coe_nat (n : ℕ) : ∥(n : ℝ)∥₊ = n := nnreal.eq $ by simp

@[simp] lemma norm_two : ∥(2 : ℝ)∥ = 2 := abs_of_pos (@zero_lt_two ℝ _ _)

@[simp] lemma nnnorm_two : ∥(2 : ℝ)∥₊ = 2 := nnreal.eq $ by simp

lemma nnnorm_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ∥x∥₊ = ⟨x, hx⟩ :=
nnreal.eq $ norm_of_nonneg hx

lemma ennnorm_eq_of_real {x : ℝ} (hx : 0 ≤ x) : (∥x∥₊ : ℝ≥0∞) = ennreal.of_real x :=
by { rw [← of_real_norm_eq_coe_nnnorm, norm_of_nonneg hx] }

lemma of_real_le_ennnorm (x : ℝ) : ennreal.of_real x ≤ ∥x∥₊ :=
begin
  by_cases hx : 0 ≤ x,
  { rw real.ennnorm_eq_of_real hx, refl' },
  { rw [ennreal.of_real_eq_zero.2 (le_of_lt (not_le.1 hx))],
    exact bot_le }
end

/-- If `E` is a nontrivial topological module over `ℝ`, then `E` has no isolated points.
This is a particular case of `module.punctured_nhds_ne_bot`. -/
instance punctured_nhds_module_ne_bot
  {E : Type*} [add_comm_group E] [topological_space E] [has_continuous_add E] [nontrivial E]
  [module ℝ E] [has_continuous_smul ℝ E] (x : E) :
  ne_bot (𝓝[{x}ᶜ] x) :=
module.punctured_nhds_ne_bot ℝ E x

end real

namespace nnreal

open_locale nnreal

@[simp] lemma norm_eq (x : ℝ≥0) : ∥(x : ℝ)∥ = x :=
by rw [real.norm_eq_abs, x.abs_eq]

@[simp] lemma nnnorm_eq (x : ℝ≥0) : ∥(x : ℝ)∥₊ = x :=
nnreal.eq $ real.norm_of_nonneg x.2

end nnreal

@[simp] lemma norm_norm [semi_normed_group α] (x : α) : ∥∥x∥∥ = ∥x∥ :=
real.norm_of_nonneg (norm_nonneg _)

@[simp] lemma nnnorm_norm [semi_normed_group α] (a : α) : ∥∥a∥∥₊ = ∥a∥₊ :=
by simpa [real.nnnorm_of_nonneg (norm_nonneg a)]

/-- A restatement of `metric_space.tendsto_at_top` in terms of the norm. -/
lemma normed_group.tendsto_at_top [nonempty α] [semilattice_sup α] {β : Type*} [semi_normed_group β]
  {f : α → β} {b : β} :
  tendsto f at_top (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ∥f n - b∥ < ε :=
(at_top_basis.tendsto_iff metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

/--
A variant of `normed_group.tendsto_at_top` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
lemma normed_group.tendsto_at_top' [nonempty α] [semilattice_sup α] [no_top_order α]
  {β : Type*} [semi_normed_group β]
  {f : α → β} {b : β} :
  tendsto f at_top (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N < n → ∥f n - b∥ < ε :=
(at_top_basis_Ioi.tendsto_iff metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

instance : normed_comm_ring ℤ :=
{ norm := λ n, ∥(n : ℝ)∥,
  norm_mul := λ m n, le_of_eq $ by simp only [norm, int.cast_mul, abs_mul],
  dist_eq := λ m n, by simp only [int.dist_eq, norm, int.cast_sub],
  mul_comm := mul_comm }

@[norm_cast] lemma int.norm_cast_real (m : ℤ) : ∥(m : ℝ)∥ = ∥m∥ := rfl

lemma int.norm_eq_abs (n : ℤ) : ∥n∥ = |n| := rfl

lemma nnreal.coe_nat_abs (n : ℤ) : (n.nat_abs : ℝ≥0) = ∥n∥₊ :=
nnreal.eq $ calc ((n.nat_abs : ℝ≥0) : ℝ)
               = (n.nat_abs : ℤ) : by simp only [int.cast_coe_nat, nnreal.coe_nat_cast]
           ... = |n|           : by simp only [← int.abs_eq_nat_abs, int.cast_abs]
           ... = ∥n∥              : rfl

instance : norm_one_class ℤ :=
⟨by simp [← int.norm_cast_real]⟩

instance : normed_field ℚ :=
{ norm := λ r, ∥(r : ℝ)∥,
  norm_mul' := λ r₁ r₂, by simp only [norm, rat.cast_mul, abs_mul],
  dist_eq := λ r₁ r₂, by simp only [rat.dist_eq, norm, rat.cast_sub] }

instance : nondiscrete_normed_field ℚ :=
{ non_trivial := ⟨2, by { unfold norm, rw abs_of_nonneg; norm_num }⟩ }

@[norm_cast, simp] lemma rat.norm_cast_real (r : ℚ) : ∥(r : ℝ)∥ = ∥r∥ := rfl

@[norm_cast, simp] lemma int.norm_cast_rat (m : ℤ) : ∥(m : ℚ)∥ = ∥m∥ :=
by rw [← rat.norm_cast_real, ← int.norm_cast_real]; congr' 1; norm_cast

-- Now that we've installed the norm on `ℤ`,
-- we can state some lemmas about `nsmul` and `gsmul`.
section
variables [semi_normed_group α]

lemma norm_nsmul_le (n : ℕ) (a : α) : ∥n • a∥ ≤ n * ∥a∥ :=
begin
  induction n with n ih,
  { simp only [norm_zero, nat.cast_zero, zero_mul, zero_smul] },
  simp only [nat.succ_eq_add_one, add_smul, add_mul, one_mul, nat.cast_add,
    nat.cast_one, one_nsmul],
  exact norm_add_le_of_le ih le_rfl
end

lemma norm_gsmul_le (n : ℤ) (a : α) : ∥n • a∥ ≤ ∥n∥ * ∥a∥ :=
begin
  induction n with n n,
  { simp only [int.of_nat_eq_coe, gsmul_coe_nat],
    convert norm_nsmul_le n a,
    exact nat.abs_cast n },
  { simp only [int.neg_succ_of_nat_coe, neg_smul, norm_neg, gsmul_coe_nat],
    convert norm_nsmul_le n.succ a,
    exact nat.abs_cast n.succ, }
end

lemma nnnorm_nsmul_le (n : ℕ) (a : α) : ∥n • a∥₊ ≤ n * ∥a∥₊ :=
by simpa only [←nnreal.coe_le_coe, nnreal.coe_mul, nnreal.coe_nat_cast]
  using norm_nsmul_le n a

lemma nnnorm_gsmul_le (n : ℤ) (a : α) : ∥n • a∥₊ ≤ ∥n∥₊ * ∥a∥₊ :=
by simpa only [←nnreal.coe_le_coe, nnreal.coe_mul] using norm_gsmul_le n a

end

section semi_normed_space

section prio
set_option extends_priority 920
-- Here, we set a rather high priority for the instance `[semi_normed_space α β] : module α β`
-- to take precedence over `semiring.to_module` as this leads to instance paths with better
-- unification properties.
/-- A seminormed space over a normed field is a vector space endowed with a seminorm which satisfies
the equality `∥c • x∥ = ∥c∥ ∥x∥`. We require only `∥c • x∥ ≤ ∥c∥ ∥x∥` in the definition, then prove
`∥c • x∥ = ∥c∥ ∥x∥` in `norm_smul`. -/
class semi_normed_space (α : Type*) (β : Type*) [normed_field α] [semi_normed_group β]
  extends module α β :=
(norm_smul_le : ∀ (a:α) (b:β), ∥a • b∥ ≤ ∥a∥ * ∥b∥)

set_option extends_priority 920
-- Here, we set a rather high priority for the instance `[normed_space α β] : module α β`
-- to take precedence over `semiring.to_module` as this leads to instance paths with better
-- unification properties.
/-- A normed space over a normed field is a vector space endowed with a norm which satisfies the
equality `∥c • x∥ = ∥c∥ ∥x∥`. We require only `∥c • x∥ ≤ ∥c∥ ∥x∥` in the definition, then prove
`∥c • x∥ = ∥c∥ ∥x∥` in `norm_smul`. -/
class normed_space (α : Type*) (β : Type*) [normed_field α] [normed_group β]
  extends module α β :=
(norm_smul_le : ∀ (a:α) (b:β), ∥a • b∥ ≤ ∥a∥ * ∥b∥)

/-- A normed space is a seminormed space. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_space.to_semi_normed_space [normed_field α] [normed_group β]
  [γ : normed_space α β] : semi_normed_space α β := { ..γ }

end prio

variables [normed_field α] [semi_normed_group β]

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_space.has_bounded_smul [semi_normed_space α β] : has_bounded_smul α β :=
{ dist_smul_pair' := λ x y₁ y₂,
    by simpa [dist_eq_norm, smul_sub] using semi_normed_space.norm_smul_le x (y₁ - y₂),
  dist_pair_smul' := λ x₁ x₂ y,
    by simpa [dist_eq_norm, sub_smul] using semi_normed_space.norm_smul_le (x₁ - x₂) y }

instance normed_field.to_normed_space : normed_space α α :=
{ norm_smul_le := λ a b, le_of_eq (normed_field.norm_mul a b) }

lemma norm_smul [semi_normed_space α β] (s : α) (x : β) : ∥s • x∥ = ∥s∥ * ∥x∥ :=
begin
  by_cases h : s = 0,
  { simp [h] },
  { refine le_antisymm (semi_normed_space.norm_smul_le s x) _,
    calc ∥s∥ * ∥x∥ = ∥s∥ * ∥s⁻¹ • s • x∥     : by rw [inv_smul_smul₀ h]
               ... ≤ ∥s∥ * (∥s⁻¹∥ * ∥s • x∥) :
      mul_le_mul_of_nonneg_left (semi_normed_space.norm_smul_le _ _) (norm_nonneg _)
               ... = ∥s • x∥                 :
      by rw [normed_field.norm_inv, ← mul_assoc, mul_inv_cancel (mt norm_eq_zero.1 h), one_mul] }
end

@[simp] lemma abs_norm_eq_norm (z : β) : |∥z∥| = ∥z∥ :=
  (abs_eq (norm_nonneg z)).mpr (or.inl rfl)

lemma dist_smul [semi_normed_space α β] (s : α) (x y : β) : dist (s • x) (s • y) = ∥s∥ * dist x y :=
by simp only [dist_eq_norm, (norm_smul _ _).symm, smul_sub]

lemma nnnorm_smul [semi_normed_space α β] (s : α) (x : β) : ∥s • x∥₊ = ∥s∥₊ * ∥x∥₊ :=
nnreal.eq $ norm_smul s x

lemma nndist_smul [semi_normed_space α β] (s : α) (x y : β) :
  nndist (s • x) (s • y) = ∥s∥₊ * nndist x y :=
nnreal.eq $ dist_smul s x y

lemma norm_smul_of_nonneg [semi_normed_space ℝ β] {t : ℝ} (ht : 0 ≤ t) (x : β) :
  ∥t • x∥ = t * ∥x∥ := by rw [norm_smul, real.norm_eq_abs, abs_of_nonneg ht]

variables {E : Type*} [semi_normed_group E] [semi_normed_space α E]
variables {F : Type*} [semi_normed_group F] [semi_normed_space α F]

theorem eventually_nhds_norm_smul_sub_lt (c : α) (x : E) {ε : ℝ} (h : 0 < ε) :
  ∀ᶠ y in 𝓝 x, ∥c • (y - x)∥ < ε :=
have tendsto (λ y, ∥c • (y - x)∥) (𝓝 x) (𝓝 0),
  from (continuous_const.smul (continuous_id.sub continuous_const)).norm.tendsto' _ _ (by simp),
this.eventually (gt_mem_nhds h)

theorem closure_ball [semi_normed_space ℝ E] (x : E) {r : ℝ} (hr : 0 < r) :
  closure (ball x r) = closed_ball x r :=
begin
  refine set.subset.antisymm closure_ball_subset_closed_ball (λ y hy, _),
  have : continuous_within_at (λ c : ℝ, c • (y - x) + x) (set.Ico 0 1) 1 :=
    ((continuous_id.smul continuous_const).add continuous_const).continuous_within_at,
  convert this.mem_closure _ _,
  { rw [one_smul, sub_add_cancel] },
  { simp [closure_Ico (@zero_lt_one ℝ _ _), zero_le_one] },
  { rintros c ⟨hc0, hc1⟩,
    rw [set.mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel, norm_smul, real.norm_eq_abs,
      abs_of_nonneg hc0, mul_comm, ← mul_one r],
    rw [mem_closed_ball, dist_eq_norm] at hy,
    apply mul_lt_mul'; assumption }
end

theorem frontier_ball [semi_normed_space ℝ E] (x : E) {r : ℝ} (hr : 0 < r) :
  frontier (ball x r) = sphere x r :=
begin
  rw [frontier, closure_ball x hr, is_open_ball.interior_eq],
  ext x, exact (@eq_iff_le_not_lt ℝ _ _ _).symm
end

theorem interior_closed_ball [semi_normed_space ℝ E] (x : E) {r : ℝ} (hr : 0 < r) :
  interior (closed_ball x r) = ball x r :=
begin
  refine set.subset.antisymm _ ball_subset_interior_closed_ball,
  intros y hy,
  rcases le_iff_lt_or_eq.1 (mem_closed_ball.1 $ interior_subset hy) with hr|rfl, { exact hr },
  set f : ℝ → E := λ c : ℝ, c • (y - x) + x,
  suffices : f ⁻¹' closed_ball x (dist y x) ⊆ set.Icc (-1) 1,
  { have hfc : continuous f := (continuous_id.smul continuous_const).add continuous_const,
    have hf1 : (1:ℝ) ∈ f ⁻¹' (interior (closed_ball x $ dist y x)), by simpa [f],
    have h1 : (1:ℝ) ∈ interior (set.Icc (-1:ℝ) 1) :=
      interior_mono this (preimage_interior_subset_interior_preimage hfc hf1),
    contrapose h1,
    simp },
  intros c hc,
  rw [set.mem_Icc, ← abs_le, ← real.norm_eq_abs, ← mul_le_mul_right hr],
  simpa [f, dist_eq_norm, norm_smul] using hc
end

theorem frontier_closed_ball [semi_normed_space ℝ E] (x : E) {r : ℝ} (hr : 0 < r) :
  frontier (closed_ball x r) = sphere x r :=
by rw [frontier, closure_closed_ball, interior_closed_ball x hr,
  closed_ball_diff_ball]

theorem smul_ball {c : α} (hc : c ≠ 0) (x : E) (r : ℝ) :
  c • ball x r = ball (c • x) (∥c∥ * r) :=
begin
  ext y,
  rw mem_smul_set_iff_inv_smul_mem₀ hc,
  conv_lhs { rw ←inv_smul_smul₀ hc x },
  simp [← div_eq_inv_mul, div_lt_iff (norm_pos_iff.2 hc), mul_comm _ r, dist_smul],
end

theorem smul_closed_ball' {c : α} (hc : c ≠ 0) (x : E) (r : ℝ) :
  c • closed_ball x r = closed_ball (c • x) (∥c∥ * r) :=
begin
  ext y,
  rw mem_smul_set_iff_inv_smul_mem₀ hc,
  conv_lhs { rw ←inv_smul_smul₀ hc x },
  simp [dist_smul, ← div_eq_inv_mul, div_le_iff (norm_pos_iff.2 hc), mul_comm _ r],
end

theorem smul_closed_ball {E : Type*} [normed_group E] [normed_space α E]
  (c : α) (x : E) {r : ℝ} (hr : 0 ≤ r) :
  c • closed_ball x r = closed_ball (c • x) (∥c∥ * r) :=
begin
  rcases eq_or_ne c 0 with rfl|hc,
  { simp [hr, zero_smul_set, set.singleton_zero, ← nonempty_closed_ball] },
  { exact smul_closed_ball' hc x r }
end

variables (α)

lemma ne_neg_of_mem_sphere [char_zero α] {r : ℝ} (hr : 0 < r) (x : sphere (0:E) r) : x ≠ - x :=
λ h, nonzero_of_mem_sphere hr x (eq_zero_of_eq_neg α (by { conv_lhs {rw h}, simp }))

lemma ne_neg_of_mem_unit_sphere [char_zero α] (x : sphere (0:E) 1) : x ≠ - x :=
ne_neg_of_mem_sphere α  (by norm_num) x

variables {α}

open normed_field

/-- The product of two seminormed spaces is a seminormed space, with the sup norm. -/
instance prod.semi_normed_space : semi_normed_space α (E × F) :=
{ norm_smul_le := λ s x, le_of_eq $ by simp [prod.semi_norm_def, norm_smul, mul_max_of_nonneg],
  ..prod.normed_group,
  ..prod.module }

/-- The product of finitely many seminormed spaces is a seminormed space, with the sup norm. -/
instance pi.semi_normed_space {E : ι → Type*} [fintype ι] [∀i, semi_normed_group (E i)]
  [∀i, semi_normed_space α (E i)] : semi_normed_space α (Πi, E i) :=
{ norm_smul_le := λ a f, le_of_eq $
    show (↑(finset.sup finset.univ (λ (b : ι), ∥a • f b∥₊)) : ℝ) =
      ∥a∥₊ * ↑(finset.sup finset.univ (λ (b : ι), ∥f b∥₊)),
    by simp only [(nnreal.coe_mul _ _).symm, nnreal.mul_finset_sup, nnnorm_smul] }

/-- A subspace of a seminormed space is also a normed space, with the restriction of the norm. -/
instance submodule.semi_normed_space {𝕜 R : Type*} [has_scalar 𝕜 R] [normed_field 𝕜] [ring R]
  {E : Type*} [semi_normed_group E] [semi_normed_space 𝕜 E] [module R E]
  [is_scalar_tower 𝕜 R E] (s : submodule R E) :
  semi_normed_space 𝕜 s :=
{ norm_smul_le := λc x, le_of_eq $ norm_smul c (x : E) }

/-- If there is a scalar `c` with `∥c∥>1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `∥c∥`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
lemma rescale_to_shell_semi_normed {c : α} (hc : 1 < ∥c∥) {ε : ℝ} (εpos : 0 < ε) {x : E}
  (hx : ∥x∥ ≠ 0) : ∃d:α, d ≠ 0 ∧ ∥d • x∥ < ε ∧ (ε/∥c∥ ≤ ∥d • x∥) ∧ (∥d∥⁻¹ ≤ ε⁻¹ * ∥c∥ * ∥x∥) :=
begin
  have xεpos : 0 < ∥x∥/ε := div_pos ((ne.symm hx).le_iff_lt.1 (norm_nonneg x)) εpos,
  rcases exists_int_pow_near xεpos hc with ⟨n, hn⟩,
  have cpos : 0 < ∥c∥ := lt_trans (zero_lt_one : (0 :ℝ) < 1) hc,
  have cnpos : 0 < ∥c^(n+1)∥ := by { rw norm_fpow, exact lt_trans xεpos hn.2 },
  refine ⟨(c^(n+1))⁻¹, _, _, _, _⟩,
  show (c ^ (n + 1))⁻¹  ≠ 0,
    by rwa [ne.def, inv_eq_zero, ← ne.def, ← norm_pos_iff],
  show ∥(c ^ (n + 1))⁻¹ • x∥ < ε,
  { rw [norm_smul, norm_inv, ← div_eq_inv_mul, div_lt_iff cnpos, mul_comm, norm_fpow],
    exact (div_lt_iff εpos).1 (hn.2) },
  show ε / ∥c∥ ≤ ∥(c ^ (n + 1))⁻¹ • x∥,
  { rw [div_le_iff cpos, norm_smul, norm_inv, norm_fpow, fpow_add (ne_of_gt cpos),
        gpow_one, mul_inv_rev₀, mul_comm, ← mul_assoc, ← mul_assoc, mul_inv_cancel (ne_of_gt cpos),
        one_mul, ← div_eq_inv_mul, le_div_iff (fpow_pos_of_pos cpos _), mul_comm],
    exact (le_div_iff εpos).1 hn.1 },
  show ∥(c ^ (n + 1))⁻¹∥⁻¹ ≤ ε⁻¹ * ∥c∥ * ∥x∥,
  { have : ε⁻¹ * ∥c∥ * ∥x∥ = ε⁻¹ * ∥x∥ * ∥c∥, by ring,
    rw [norm_inv, inv_inv₀, norm_fpow, fpow_add (ne_of_gt cpos), gpow_one, this, ← div_eq_inv_mul],
    exact mul_le_mul_of_nonneg_right hn.1 (norm_nonneg _) }
end

end semi_normed_space

section normed_space

variables [normed_field α]
variables {E : Type*} [normed_group E] [normed_space α E]
variables {F : Type*} [normed_group F] [normed_space α F]

open normed_field

theorem interior_closed_ball' [normed_space ℝ E] [nontrivial E] (x : E) (r : ℝ) :
  interior (closed_ball x r) = ball x r :=
begin
  rcases lt_trichotomy r 0 with hr|rfl|hr,
  { simp [closed_ball_eq_empty.2 hr, ball_eq_empty.2 hr.le] },
  { rw [closed_ball_zero, ball_zero, interior_singleton] },
  { exact interior_closed_ball x hr }
end

theorem frontier_closed_ball' [normed_space ℝ E] [nontrivial E] (x : E) (r : ℝ) :
  frontier (closed_ball x r) = sphere x r :=
by rw [frontier, closure_closed_ball, interior_closed_ball' x r, closed_ball_diff_ball]

variables {α}

/-- If there is a scalar `c` with `∥c∥>1`, then any element can be moved by scalar multiplication to
any shell of width `∥c∥`. Also recap information on the norm of the rescaling element that shows
up in applications. -/
lemma rescale_to_shell {c : α} (hc : 1 < ∥c∥) {ε : ℝ} (εpos : 0 < ε) {x : E} (hx : x ≠ 0) :
  ∃d:α, d ≠ 0 ∧ ∥d • x∥ < ε ∧ (ε/∥c∥ ≤ ∥d • x∥) ∧ (∥d∥⁻¹ ≤ ε⁻¹ * ∥c∥ * ∥x∥) :=
rescale_to_shell_semi_normed hc εpos (ne_of_lt (norm_pos_iff.2 hx)).symm

/-- The product of two normed spaces is a normed space, with the sup norm. -/
instance : normed_space α (E × F) := { ..prod.semi_normed_space }

/-- The product of finitely many normed spaces is a normed space, with the sup norm. -/
instance pi.normed_space {E : ι → Type*} [fintype ι] [∀i, normed_group (E i)]
  [∀i, normed_space α (E i)] : normed_space α (Πi, E i) :=
{ ..pi.semi_normed_space }

section
local attribute [instance] matrix.normed_group

/-- Normed space instance (using sup norm of sup norm) for matrices over a normed field.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
def matrix.normed_space {α : Type*} [normed_field α] {n m : Type*} [fintype n] [fintype m] :
  normed_space α (matrix n m α) :=
pi.normed_space

end

/-- A subspace of a normed space is also a normed space, with the restriction of the norm. -/
instance submodule.normed_space {𝕜 R : Type*} [has_scalar 𝕜 R] [normed_field 𝕜] [ring R]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] [module R E]
  [is_scalar_tower 𝕜 R E] (s : submodule R E) :
  normed_space 𝕜 s :=
{ ..submodule.semi_normed_space s }

end normed_space

section normed_algebra

/-- A seminormed algebra `𝕜'` over `𝕜` is an algebra endowed with a seminorm for which the
embedding of `𝕜` in `𝕜'` is an isometry. -/
class semi_normed_algebra (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜] [semi_normed_ring 𝕜']
  extends algebra 𝕜 𝕜' :=
(norm_algebra_map_eq : ∀x:𝕜, ∥algebra_map 𝕜 𝕜' x∥ = ∥x∥)

/-- A normed algebra `𝕜'` over `𝕜` is an algebra endowed with a norm for which the embedding of
`𝕜` in `𝕜'` is an isometry. -/
class normed_algebra (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜] [normed_ring 𝕜']
  extends algebra 𝕜 𝕜' :=
(norm_algebra_map_eq : ∀x:𝕜, ∥algebra_map 𝕜 𝕜' x∥ = ∥x∥)

/-- A normed algebra is a seminormed algebra. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_algebra.to_semi_normed_algebra (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜]
  [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] : semi_normed_algebra 𝕜 𝕜' :=
{ norm_algebra_map_eq := normed_algebra.norm_algebra_map_eq }

@[simp] lemma norm_algebra_map_eq {𝕜 : Type*} (𝕜' : Type*) [normed_field 𝕜] [semi_normed_ring 𝕜']
  [h : semi_normed_algebra 𝕜 𝕜'] (x : 𝕜) : ∥algebra_map 𝕜 𝕜' x∥ = ∥x∥ :=
semi_normed_algebra.norm_algebra_map_eq _

/-- In a normed algebra, the inclusion of the base field in the extended field is an isometry. -/
lemma algebra_map_isometry (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜] [semi_normed_ring 𝕜']
  [semi_normed_algebra 𝕜 𝕜'] : isometry (algebra_map 𝕜 𝕜') :=
begin
  refine isometry_emetric_iff_metric.2 (λx y, _),
  rw [dist_eq_norm, dist_eq_norm, ← ring_hom.map_sub, norm_algebra_map_eq],
end

variables (𝕜 : Type*) [normed_field 𝕜]
variables (𝕜' : Type*) [semi_normed_ring 𝕜']

@[priority 100]
instance semi_normed_algebra.to_semi_normed_space [h : semi_normed_algebra 𝕜 𝕜'] :
  semi_normed_space 𝕜 𝕜' :=
{ norm_smul_le := λ s x, calc
    ∥s • x∥ = ∥((algebra_map 𝕜 𝕜') s) * x∥ : by { rw h.smul_def', refl }
    ... ≤ ∥algebra_map 𝕜 𝕜' s∥ * ∥x∥ : semi_normed_ring.norm_mul _ _
    ... = ∥s∥ * ∥x∥ : by rw norm_algebra_map_eq,
  ..h }

/-- While this may appear identical to `semi_normed_algebra.to_semi_normed_space`, it contains an
implicit argument involving `normed_ring.to_semi_normed_ring` that typeclass inference has trouble
inferring.

Specifically, the following instance cannot be found without this
`semi_normed_algebra.to_semi_normed_space'`:
```lean
example
  (𝕜 ι : Type*) (E : ι → Type*)
  [normed_field 𝕜] [Π i, normed_ring (E i)] [Π i, normed_algebra 𝕜 (E i)] :
  Π i, module 𝕜 (E i) := by apply_instance
```

See `semi_normed_space.to_module'` for a similar situation. -/
@[priority 100]
instance semi_normed_algebra.to_semi_normed_space' (𝕜 : Type*) [normed_field 𝕜] (𝕜' : Type*)
  [normed_ring 𝕜'] [semi_normed_algebra 𝕜 𝕜'] :
  semi_normed_space 𝕜 𝕜' := by apply_instance

@[priority 100]
instance normed_algebra.to_normed_space (𝕜 : Type*) [normed_field 𝕜] (𝕜' : Type*)
  [normed_ring 𝕜'] [h : normed_algebra 𝕜 𝕜'] : normed_space 𝕜 𝕜' :=
{ norm_smul_le := semi_normed_space.norm_smul_le,
  ..h }

instance normed_algebra.id : normed_algebra 𝕜 𝕜 :=
{ norm_algebra_map_eq := by simp,
.. algebra.id 𝕜}

variables (𝕜') [semi_normed_algebra 𝕜 𝕜']
include 𝕜

lemma normed_algebra.norm_one : ∥(1:𝕜')∥ = 1 :=
by simpa using (norm_algebra_map_eq 𝕜' (1:𝕜))

lemma normed_algebra.norm_one_class : norm_one_class 𝕜' :=
⟨normed_algebra.norm_one 𝕜 𝕜'⟩

lemma normed_algebra.zero_ne_one : (0:𝕜') ≠ 1 :=
begin
  refine (ne_zero_of_norm_pos _).symm,
  rw normed_algebra.norm_one 𝕜 𝕜', norm_num,
end

lemma normed_algebra.nontrivial : nontrivial 𝕜' :=
⟨⟨0, 1, normed_algebra.zero_ne_one 𝕜 𝕜'⟩⟩

end normed_algebra

section restrict_scalars

variables (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜] [normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
(E : Type*) [normed_group E] [normed_space 𝕜' E]
(F : Type*) [semi_normed_group F] [semi_normed_space 𝕜' F]

/-- Warning: This declaration should be used judiciously.
Please consider using `is_scalar_tower` instead.

`𝕜`-seminormed space structure induced by a `𝕜'`-seminormed space structure when `𝕜'` is a
seminormed algebra over `𝕜`. Not registered as an instance as `𝕜'` can not be inferred.

The type synonym `module.restrict_scalars 𝕜 𝕜' E` will be endowed with this instance by default.
-/
def semi_normed_space.restrict_scalars : semi_normed_space 𝕜 F :=
{ norm_smul_le := λc x, le_of_eq $ begin
    change ∥(algebra_map 𝕜 𝕜' c) • x∥ = ∥c∥ * ∥x∥,
    simp [norm_smul]
  end,
  ..restrict_scalars.module 𝕜 𝕜' F }

/-- Warning: This declaration should be used judiciously.
Please consider using `is_scalar_tower` instead.

`𝕜`-normed space structure induced by a `𝕜'`-normed space structure when `𝕜'` is a
normed algebra over `𝕜`. Not registered as an instance as `𝕜'` can not be inferred.

The type synonym `restrict_scalars 𝕜 𝕜' E` will be endowed with this instance by default.
-/
def normed_space.restrict_scalars : normed_space 𝕜 E :=
{ norm_smul_le := λc x, le_of_eq $ begin
    change ∥(algebra_map 𝕜 𝕜' c) • x∥ = ∥c∥ * ∥x∥,
    simp [norm_smul]
  end,
  ..restrict_scalars.module 𝕜 𝕜' E }

instance {𝕜 : Type*} {𝕜' : Type*} {F : Type*} [I : semi_normed_group F] :
  semi_normed_group (restrict_scalars 𝕜 𝕜' F) := I

instance {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [I : normed_group E] :
  normed_group (restrict_scalars 𝕜 𝕜' E) := I

instance module.restrict_scalars.semi_normed_space_orig {𝕜 : Type*} {𝕜' : Type*} {F : Type*}
  [normed_field 𝕜'] [semi_normed_group F] [I : semi_normed_space 𝕜' F] :
  semi_normed_space 𝕜' (restrict_scalars 𝕜 𝕜' F) := I

instance module.restrict_scalars.normed_space_orig {𝕜 : Type*} {𝕜' : Type*} {E : Type*}
  [normed_field 𝕜'] [normed_group E] [I : normed_space 𝕜' E] :
  normed_space 𝕜' (restrict_scalars 𝕜 𝕜' E) := I

instance : semi_normed_space 𝕜 (restrict_scalars 𝕜 𝕜' F) :=
(semi_normed_space.restrict_scalars 𝕜 𝕜' F : semi_normed_space 𝕜 F)

instance : normed_space 𝕜 (restrict_scalars 𝕜 𝕜' E) :=
(normed_space.restrict_scalars 𝕜 𝕜' E : normed_space 𝕜 E)

end restrict_scalars

section summable
open_locale classical
open finset filter
variables [semi_normed_group α] [semi_normed_group β]

lemma cauchy_seq_finset_iff_vanishing_norm {f : ι → α} :
  cauchy_seq (λ s : finset ι, ∑ i in s, f i) ↔
    ∀ε > (0 : ℝ), ∃s:finset ι, ∀t, disjoint t s → ∥ ∑ i in t, f i ∥ < ε :=
begin
  rw [cauchy_seq_finset_iff_vanishing, nhds_basis_ball.forall_iff],
  { simp only [ball_zero_eq, set.mem_set_of_eq] },
  { rintros s t hst ⟨s', hs'⟩,
    exact ⟨s', λ t' ht', hst $ hs' _ ht'⟩ }
end

lemma summable_iff_vanishing_norm [complete_space α] {f : ι → α} :
  summable f ↔ ∀ε > (0 : ℝ), ∃s:finset ι, ∀t, disjoint t s → ∥ ∑ i in t, f i ∥ < ε :=
by rw [summable_iff_cauchy_seq_finset, cauchy_seq_finset_iff_vanishing_norm]

lemma cauchy_seq_finset_of_norm_bounded {f : ι → α} (g : ι → ℝ) (hg : summable g)
  (h : ∀i, ∥f i∥ ≤ g i) : cauchy_seq (λ s : finset ι, ∑ i in s, f i) :=
cauchy_seq_finset_iff_vanishing_norm.2 $ assume ε hε,
  let ⟨s, hs⟩ := summable_iff_vanishing_norm.1 hg ε hε in
  ⟨s, assume t ht,
    have ∥∑ i in t, g i∥ < ε := hs t ht,
    have nn : 0 ≤ ∑ i in t, g i := finset.sum_nonneg (assume a _, le_trans (norm_nonneg _) (h a)),
    lt_of_le_of_lt (norm_sum_le_of_le t (λ i _, h i)) $
      by rwa [real.norm_eq_abs, abs_of_nonneg nn] at this⟩

lemma cauchy_seq_finset_of_summable_norm {f : ι → α} (hf : summable (λa, ∥f a∥)) :
  cauchy_seq (λ s : finset ι, ∑ a in s, f a) :=
cauchy_seq_finset_of_norm_bounded _ hf (assume i, le_refl _)

/-- If a function `f` is summable in norm, and along some sequence of finsets exhausting the space
its sum is converging to a limit `a`, then this holds along all finsets, i.e., `f` is summable
with sum `a`. -/
lemma has_sum_of_subseq_of_summable {f : ι → α} (hf : summable (λa, ∥f a∥))
  {s : γ → finset ι} {p : filter γ} [ne_bot p]
  (hs : tendsto s p at_top) {a : α} (ha : tendsto (λ b, ∑ i in s b, f i) p (𝓝 a)) :
  has_sum f a :=
tendsto_nhds_of_cauchy_seq_of_subseq (cauchy_seq_finset_of_summable_norm hf) hs ha

lemma has_sum_iff_tendsto_nat_of_summable_norm {f : ℕ → α} {a : α} (hf : summable (λi, ∥f i∥)) :
  has_sum f a ↔ tendsto (λn:ℕ, ∑ i in range n, f i) at_top (𝓝 a) :=
⟨λ h, h.tendsto_sum_nat,
λ h, has_sum_of_subseq_of_summable hf tendsto_finset_range h⟩

/-- The direct comparison test for series:  if the norm of `f` is bounded by a real function `g`
which is summable, then `f` is summable. -/
lemma summable_of_norm_bounded
  [complete_space α] {f : ι → α} (g : ι → ℝ) (hg : summable g) (h : ∀i, ∥f i∥ ≤ g i) :
  summable f :=
by { rw summable_iff_cauchy_seq_finset, exact cauchy_seq_finset_of_norm_bounded g hg h }

lemma has_sum.norm_le_of_bounded {f : ι → α} {g : ι → ℝ} {a : α} {b : ℝ}
  (hf : has_sum f a) (hg : has_sum g b) (h : ∀ i, ∥f i∥ ≤ g i) :
  ∥a∥ ≤ b :=
le_of_tendsto_of_tendsto' hf.norm hg $ λ s, norm_sum_le_of_le _ $ λ i hi, h i

/-- Quantitative result associated to the direct comparison test for series:  If `∑' i, g i` is
summable, and for all `i`, `∥f i∥ ≤ g i`, then `∥∑' i, f i∥ ≤ ∑' i, g i`. Note that we do not
assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
lemma tsum_of_norm_bounded {f : ι → α} {g : ι → ℝ} {a : ℝ} (hg : has_sum g a)
  (h : ∀ i, ∥f i∥ ≤ g i) :
  ∥∑' i : ι, f i∥ ≤ a :=
begin
  by_cases hf : summable f,
  { exact hf.has_sum.norm_le_of_bounded hg h },
  { rw [tsum_eq_zero_of_not_summable hf, norm_zero],
    exact ge_of_tendsto' hg (λ s, sum_nonneg $ λ i hi, (norm_nonneg _).trans (h i)) }
end

/-- If `∑' i, ∥f i∥` is summable, then `∥∑' i, f i∥ ≤ (∑' i, ∥f i∥)`. Note that we do not assume
that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
lemma norm_tsum_le_tsum_norm {f : ι → α} (hf : summable (λi, ∥f i∥)) :
  ∥∑' i, f i∥ ≤ ∑' i, ∥f i∥ :=
tsum_of_norm_bounded hf.has_sum $ λ i, le_rfl

/-- Quantitative result associated to the direct comparison test for series: If `∑' i, g i` is
summable, and for all `i`, `nnnorm (f i) ≤ g i`, then `nnnorm (∑' i, f i) ≤ ∑' i, g i`. Note that we
do not assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete
space. -/
lemma tsum_of_nnnorm_bounded {f : ι → α} {g : ι → ℝ≥0} {a : ℝ≥0} (hg : has_sum g a)
  (h : ∀ i, nnnorm (f i) ≤ g i) :
  nnnorm (∑' i : ι, f i) ≤ a :=
begin
  simp only [← nnreal.coe_le_coe, ← nnreal.has_sum_coe, coe_nnnorm] at *,
  exact tsum_of_norm_bounded hg h
end

/-- If `∑' i, nnnorm (f i)` is summable, then `nnnorm (∑' i, f i) ≤ ∑' i, nnnorm (f i)`. Note that
we do not assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete
space. -/
lemma nnnorm_tsum_le {f : ι → α} (hf : summable (λi, nnnorm (f i))) :
  nnnorm (∑' i, f i) ≤ ∑' i, nnnorm (f i) :=
tsum_of_nnnorm_bounded hf.has_sum (λ i, le_rfl)

variable [complete_space α]

/-- Variant of the direct comparison test for series:  if the norm of `f` is eventually bounded by a
real function `g` which is summable, then `f` is summable. -/
lemma summable_of_norm_bounded_eventually {f : ι → α} (g : ι → ℝ) (hg : summable g)
  (h : ∀ᶠ i in cofinite, ∥f i∥ ≤ g i) : summable f :=
begin
  replace h := mem_cofinite.1 h,
  refine h.summable_compl_iff.mp _,
  refine summable_of_norm_bounded _ (h.summable_compl_iff.mpr hg) _,
  rintros ⟨a, h'⟩,
  simpa using h'
end

lemma summable_of_nnnorm_bounded {f : ι → α} (g : ι → ℝ≥0) (hg : summable g)
  (h : ∀i, ∥f i∥₊ ≤ g i) : summable f :=
summable_of_norm_bounded (λ i, (g i : ℝ)) (nnreal.summable_coe.2 hg) (λ i, by exact_mod_cast h i)

lemma summable_of_summable_norm {f : ι → α} (hf : summable (λa, ∥f a∥)) : summable f :=
summable_of_norm_bounded _ hf (assume i, le_refl _)

lemma summable_of_summable_nnnorm {f : ι → α} (hf : summable (λ a, ∥f a∥₊)) : summable f :=
summable_of_nnnorm_bounded _ hf (assume i, le_refl _)

end summable

section cauchy_product

/-! ## Multiplying two infinite sums in a normed ring

In this section, we prove various results about `(∑' x : ι, f x) * (∑' y : ι', g y)` in a normed
ring. There are similar results proven in `topology/algebra/infinite_sum` (e.g `tsum_mul_tsum`),
but in a normed ring we get summability results which aren't true in general.

We first establish results about arbitrary index types, `β` and `γ`, and then we specialize to
`β = γ = ℕ` to prove the Cauchy product formula
(see `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`).

### Arbitrary index types
-/

variables {ι' : Type*} [normed_ring α]

open finset
open_locale classical

lemma summable.mul_of_nonneg {f : ι → ℝ} {g : ι' → ℝ}
  (hf : summable f) (hg : summable g) (hf' : 0 ≤ f) (hg' : 0 ≤ g) :
  summable (λ (x : ι × ι'), f x.1 * g x.2) :=
let ⟨s, hf⟩ := hf in
let ⟨t, hg⟩ := hg in
suffices this : ∀ u : finset (ι × ι'), ∑ x in u, f x.1 * g x.2 ≤ s*t,
  from summable_of_sum_le (λ x, mul_nonneg (hf' _) (hg' _)) this,
assume u,
calc  ∑ x in u, f x.1 * g x.2
    ≤ ∑ x in (u.image prod.fst).product (u.image prod.snd), f x.1 * g x.2 :
      sum_mono_set_of_nonneg (λ x, mul_nonneg (hf' _) (hg' _)) subset_product
... = ∑ x in u.image prod.fst, ∑ y in u.image prod.snd, f x * g y : sum_product
... = ∑ x in u.image prod.fst, f x * ∑ y in u.image prod.snd, g y :
      sum_congr rfl (λ x _, mul_sum.symm)
... ≤ ∑ x in u.image prod.fst, f x * t :
      sum_le_sum
        (λ x _, mul_le_mul_of_nonneg_left (sum_le_has_sum _ (λ _ _, hg' _) hg) (hf' _))
... = (∑ x in u.image prod.fst, f x) * t : sum_mul.symm
... ≤ s * t :
      mul_le_mul_of_nonneg_right (sum_le_has_sum _ (λ _ _, hf' _) hf) (hg.nonneg $ λ _, hg' _)

lemma summable.mul_norm {f : ι → α} {g : ι' → α}
  (hf : summable (λ x, ∥f x∥)) (hg : summable (λ x, ∥g x∥)) :
  summable (λ (x : ι × ι'), ∥f x.1 * g x.2∥) :=
summable_of_nonneg_of_le (λ x, norm_nonneg (f x.1 * g x.2)) (λ x, norm_mul_le (f x.1) (g x.2))
  (hf.mul_of_nonneg hg (λ x, norm_nonneg $ f x) (λ x, norm_nonneg $ g x) : _)

lemma summable_mul_of_summable_norm [complete_space α] {f : ι → α} {g : ι' → α}
  (hf : summable (λ x, ∥f x∥)) (hg : summable (λ x, ∥g x∥)) :
  summable (λ (x : ι × ι'), f x.1 * g x.2) :=
summable_of_summable_norm (hf.mul_norm hg)

/-- Product of two infinites sums indexed by arbitrary types.
    See also `tsum_mul_tsum` if `f` and `g` are *not* absolutely summable. -/
lemma tsum_mul_tsum_of_summable_norm [complete_space α] {f : ι → α} {g : ι' → α}
  (hf : summable (λ x, ∥f x∥)) (hg : summable (λ x, ∥g x∥)) :
  (∑' x, f x) * (∑' y, g y) = (∑' z : ι × ι', f z.1 * g z.2) :=
tsum_mul_tsum (summable_of_summable_norm hf) (summable_of_summable_norm hg)
  (summable_mul_of_summable_norm hf hg)

/-! ### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`, where the `n`-th term is a sum over
`finset.range (n+1)` involving `nat` substraction.
In order to avoid `nat` substraction, we also provide
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`finset` `finset.nat.antidiagonal n`. -/

section nat

open finset.nat

lemma summable_norm_sum_mul_antidiagonal_of_summable_norm {f g : ℕ → α}
  (hf : summable (λ x, ∥f x∥)) (hg : summable (λ x, ∥g x∥)) :
  summable (λ n, ∥∑ kl in antidiagonal n, f kl.1 * g kl.2∥) :=
begin
  have := summable_sum_mul_antidiagonal_of_summable_mul
    (summable.mul_of_nonneg hf hg (λ _, norm_nonneg _) (λ _, norm_nonneg _)),
  refine summable_of_nonneg_of_le (λ _, norm_nonneg _) _ this,
  intros n,
  calc  ∥∑ kl in antidiagonal n, f kl.1 * g kl.2∥
      ≤ ∑ kl in antidiagonal n, ∥f kl.1 * g kl.2∥ : norm_sum_le _ _
  ... ≤ ∑ kl in antidiagonal n, ∥f kl.1∥ * ∥g kl.2∥ : sum_le_sum (λ i _, norm_mul_le _ _)
end

/-- The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
    expressed by summing on `finset.nat.antidiagonal`.
    See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal` if `f` and `g` are
    *not* absolutely summable. -/
lemma tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [complete_space α] {f g : ℕ → α}
  (hf : summable (λ x, ∥f x∥)) (hg : summable (λ x, ∥g x∥)) :
  (∑' n, f n) * (∑' n, g n) = ∑' n, ∑ kl in antidiagonal n, f kl.1 * g kl.2 :=
tsum_mul_tsum_eq_tsum_sum_antidiagonal (summable_of_summable_norm hf) (summable_of_summable_norm hg)
  (summable_mul_of_summable_norm hf hg)

lemma summable_norm_sum_mul_range_of_summable_norm {f g : ℕ → α}
  (hf : summable (λ x, ∥f x∥)) (hg : summable (λ x, ∥g x∥)) :
  summable (λ n, ∥∑ k in range (n+1), f k * g (n - k)∥) :=
begin
  simp_rw ← sum_antidiagonal_eq_sum_range_succ (λ k l, f k * g l),
  exact summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
end

/-- The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
    expressed by summing on `finset.range`.
    See also `tsum_mul_tsum_eq_tsum_sum_range` if `f` and `g` are
    *not* absolutely summable. -/
lemma tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm [complete_space α] {f g : ℕ → α}
  (hf : summable (λ x, ∥f x∥)) (hg : summable (λ x, ∥g x∥)) :
  (∑' n, f n) * (∑' n, g n) = ∑' n, ∑ k in range (n+1), f k * g (n - k) :=
begin
  simp_rw ← sum_antidiagonal_eq_sum_range_succ (λ k l, f k * g l),
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
end

end nat

end cauchy_product

namespace uniform_space
namespace completion

variables (V : Type*)

instance [uniform_space V] [has_norm V] :
  has_norm (completion V) :=
{ norm := completion.extension has_norm.norm }

@[simp] lemma norm_coe {V} [semi_normed_group V] (v : V) :
  ∥(v : completion V)∥ = ∥v∥ :=
completion.extension_coe uniform_continuous_norm v

instance [semi_normed_group V] : normed_group (completion V) :=
{ dist_eq :=
  begin
    intros x y,
    apply completion.induction_on₂ x y; clear x y,
    { refine is_closed_eq (completion.uniform_continuous_extension₂ _).continuous _,
      exact continuous.comp completion.continuous_extension continuous_sub },
    { intros x y,
      rw [← completion.coe_sub, norm_coe, metric.completion.dist_eq, dist_eq_norm] }
  end,
  .. (show add_comm_group (completion V), by apply_instance),
  .. (show metric_space (completion V), by apply_instance) }

end completion
end uniform_space
