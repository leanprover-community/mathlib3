/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import analysis.normed.group.infinite_sum
import topology.algebra.module.basic
import topology.instances.ennreal
import topology.instances.rat

/-!
# Normed fields

In this file we define (semi)normed rings and fields. We also prove some theorems about these
definitions.
-/

variables {α : Type*} {β : Type*} {γ : Type*} {ι : Type*}

noncomputable theory
open filter metric
open_locale topological_space big_operators nnreal ennreal uniformity pointwise

/-- A non-unital seminormed ring is a not-necessarily-unital ring
endowed with a seminorm which satisfies the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class non_unital_semi_normed_ring (α : Type*)
  extends has_norm α, non_unital_ring α, pseudo_metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

/-- A seminormed ring is a ring endowed with a seminorm which satisfies the inequality
`∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class semi_normed_ring (α : Type*) extends has_norm α, ring α, pseudo_metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

/-- A seminormed ring is a non-unital seminormed ring. -/
@[priority 100] -- see Note [lower instance priority]
instance semi_normed_ring.to_non_unital_semi_normed_ring [β : semi_normed_ring α] :
  non_unital_semi_normed_ring α :=
{ ..β }

/-- A non-unital normed ring is a not-necessarily-unital ring
endowed with a norm which satisfies the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class non_unital_normed_ring (α : Type*) extends has_norm α, non_unital_ring α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

/-- A non-unital normed ring is a non-unital seminormed ring. -/
@[priority 100] -- see Note [lower instance priority]
instance non_unital_normed_ring.to_non_unital_semi_normed_ring [β : non_unital_normed_ring α] :
  non_unital_semi_normed_ring α :=
{ ..β }

/-- A normed ring is a ring endowed with a norm which satisfies the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class normed_ring (α : Type*) extends has_norm α, ring α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

/-- A normed division ring is a division ring endowed with a seminorm which satisfies the equality
`∥x y∥ = ∥x∥ ∥y∥`. -/
class normed_division_ring (α : Type*) extends has_norm α, division_ring α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul' : ∀ a b, norm (a * b) = norm a * norm b)

/-- A normed division ring is a normed ring. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_division_ring.to_normed_ring [β : normed_division_ring α] : normed_ring α :=
{ norm_mul := λ a b, (normed_division_ring.norm_mul' a b).le,
  ..β }

/-- A normed ring is a seminormed ring. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_ring.to_semi_normed_ring [β : normed_ring α] : semi_normed_ring α :=
{ ..β }

/-- A normed ring is a non-unital normed ring. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_ring.to_non_unital_normed_ring [β : normed_ring α] : non_unital_normed_ring α :=
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

lemma norm_one_class.nontrivial (α : Type*) [semi_normed_group α] [has_one α] [norm_one_class α] :
  nontrivial α :=
nontrivial_of_ne 0 1 $ ne_of_apply_ne norm $ by simp

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_comm_ring.to_comm_ring [β : semi_normed_comm_ring α] : comm_ring α := { ..β }

@[priority 100] -- see Note [lower instance priority]
instance non_unital_normed_ring.to_normed_group [β : non_unital_normed_ring α] : normed_group α :=
{ ..β }

@[priority 100] -- see Note [lower instance priority]
instance non_unital_semi_normed_ring.to_semi_normed_group [β : non_unital_semi_normed_ring α] :
  semi_normed_group α := { ..β }

instance [semi_normed_group α] [has_one α] [norm_one_class α] : norm_one_class (ulift α) :=
⟨by simp [ulift.norm_def]⟩

instance prod.norm_one_class [semi_normed_group α] [has_one α] [norm_one_class α]
  [semi_normed_group β] [has_one β] [norm_one_class β] :
  norm_one_class (α × β) :=
⟨by simp [prod.norm_def]⟩

instance pi.norm_one_class {ι : Type*} {α : ι → Type*} [nonempty ι] [fintype ι]
  [Π i, semi_normed_group (α i)] [Π i, has_one (α i)] [∀ i, norm_one_class (α i)] :
  norm_one_class (Π i, α i) :=
⟨by simp [pi.norm_def, finset.sup_const finset.univ_nonempty]⟩

section non_unital_semi_normed_ring
variables [non_unital_semi_normed_ring α]

lemma norm_mul_le (a b : α) : (∥a*b∥) ≤ (∥a∥) * (∥b∥) :=
non_unital_semi_normed_ring.norm_mul _ _

lemma nnnorm_mul_le (a b : α) : ∥a * b∥₊ ≤ ∥a∥₊ * ∥b∥₊ :=
by simpa only [←norm_to_nnreal, ←real.to_nnreal_mul (norm_nonneg _)]
  using real.to_nnreal_mono (norm_mul_le _ _)

lemma one_le_norm_one (β) [normed_ring β] [nontrivial β] : 1 ≤ ∥(1 : β)∥ :=
(le_mul_iff_one_le_left $ norm_pos_iff.mpr (one_ne_zero : (1 : β) ≠ 0)).mp
  (by simpa only [mul_one] using norm_mul_le (1 : β) 1)

lemma one_le_nnnorm_one (β) [normed_ring β] [nontrivial β] : 1 ≤ ∥(1 : β)∥₊ :=
one_le_norm_one β

lemma filter.tendsto.zero_mul_is_bounded_under_le {f g : ι → α} {l : filter ι}
  (hf : tendsto f l (𝓝 0)) (hg : is_bounded_under (≤) l (norm ∘ g)) :
  tendsto (λ x, f x * g x) l (𝓝 0) :=
hf.op_zero_is_bounded_under_le hg (*) norm_mul_le

lemma filter.is_bounded_under_le.mul_tendsto_zero {f g : ι → α} {l : filter ι}
  (hf : is_bounded_under (≤) l (norm ∘ f)) (hg : tendsto g l (𝓝 0)) :
  tendsto (λ x, f x * g x) l (𝓝 0) :=
hg.op_zero_is_bounded_under_le hf (flip (*)) (λ x y, ((norm_mul_le y x).trans_eq (mul_comm _ _)))

/-- In a seminormed ring, the left-multiplication `add_monoid_hom` is bounded. -/
lemma mul_left_bound (x : α) :
  ∀ (y:α), ∥add_monoid_hom.mul_left x y∥ ≤ ∥x∥ * ∥y∥ :=
norm_mul_le x

/-- In a seminormed ring, the right-multiplication `add_monoid_hom` is bounded. -/
lemma mul_right_bound (x : α) :
  ∀ (y:α), ∥add_monoid_hom.mul_right x y∥ ≤ ∥x∥ * ∥y∥ :=
λ y, by {rw mul_comm, convert norm_mul_le y x}

instance : non_unital_semi_normed_ring (ulift α) :=
{ norm_mul := λ x y, (norm_mul_le x.down y.down : _),
  .. ulift.semi_normed_group }

/-- Non-unital seminormed ring structure on the product of two non-unital seminormed rings,
  using the sup norm. -/
instance prod.non_unital_semi_normed_ring [non_unital_semi_normed_ring β] :
  non_unital_semi_normed_ring (α × β) :=
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

/-- Non-unital seminormed ring structure on the product of finitely many non-unital seminormed
rings, using the sup norm. -/
instance pi.non_unital_semi_normed_ring {π : ι → Type*} [fintype ι]
  [Π i, non_unital_semi_normed_ring (π i)] :
  non_unital_semi_normed_ring (Π i, π i) :=
{ norm_mul := λ x y, nnreal.coe_mono $
    calc  finset.univ.sup (λ i, ∥x i * y i∥₊)
        ≤ finset.univ.sup ((λ i, ∥x i∥₊) * (λ i, ∥y i∥₊)) :
            finset.sup_mono_fun $ λ b hb, norm_mul_le _ _
    ... ≤ finset.univ.sup (λ i, ∥x i∥₊) * finset.univ.sup (λ i, ∥y i∥₊) :
            finset.sup_mul_le_mul_sup_of_nonneg _ (λ i _, zero_le _) (λ i _, zero_le _),
  ..pi.semi_normed_group }

end non_unital_semi_normed_ring

section semi_normed_ring

variables [semi_normed_ring α]

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

lemma nat.norm_cast_le : ∀ n : ℕ, ∥(n : α)∥ ≤ n * ∥(1 : α)∥
| 0 := by simp
| (n + 1) := by { rw [n.cast_succ, n.cast_succ, add_mul, one_mul],
                  exact norm_add_le_of_le (nat.norm_cast_le n) le_rfl }

lemma list.norm_prod_le' : ∀ {l : list α}, l ≠ [] → ∥l.prod∥ ≤ (l.map norm).prod
| [] h := (h rfl).elim
| [a] _ := by simp
| (a :: b :: l) _ :=
  begin
    rw [list.map_cons, list.prod_cons, @list.prod_cons _ _ _ ∥a∥],
    refine le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_left _ (norm_nonneg _)),
    exact list.norm_prod_le' (list.cons_ne_nil b l)
  end

lemma list.nnnorm_prod_le' {l : list α} (hl : l ≠ []) : ∥l.prod∥₊ ≤ (l.map nnnorm).prod :=
(list.norm_prod_le' hl).trans_eq $ by simp [nnreal.coe_list_prod, list.map_map]

lemma list.norm_prod_le [norm_one_class α] : ∀ l : list α, ∥l.prod∥ ≤ (l.map norm).prod
| [] := by simp
| (a::l) := list.norm_prod_le' (list.cons_ne_nil a l)

lemma list.nnnorm_prod_le [norm_one_class α] (l : list α) : ∥l.prod∥₊ ≤ (l.map nnnorm).prod :=
l.norm_prod_le.trans_eq $ by simp [nnreal.coe_list_prod, list.map_map]

lemma finset.norm_prod_le' {α : Type*} [normed_comm_ring α] (s : finset ι) (hs : s.nonempty)
  (f : ι → α) :
  ∥∏ i in s, f i∥ ≤ ∏ i in s, ∥f i∥ :=
begin
  rcases s with ⟨⟨l⟩, hl⟩,
  have : l.map f ≠ [], by simpa using hs,
  simpa using list.norm_prod_le' this
end

lemma finset.nnnorm_prod_le' {α : Type*} [normed_comm_ring α] (s : finset ι) (hs : s.nonempty)
  (f : ι → α) :
  ∥∏ i in s, f i∥₊ ≤ ∏ i in s, ∥f i∥₊ :=
(s.norm_prod_le' hs f).trans_eq $ by simp [nnreal.coe_prod]

lemma finset.norm_prod_le {α : Type*} [normed_comm_ring α] [norm_one_class α] (s : finset ι)
  (f : ι → α) :
  ∥∏ i in s, f i∥ ≤ ∏ i in s, ∥f i∥ :=
begin
  rcases s with ⟨⟨l⟩, hl⟩,
  simpa using (l.map f).norm_prod_le
end

lemma finset.nnnorm_prod_le {α : Type*} [normed_comm_ring α] [norm_one_class α] (s : finset ι)
  (f : ι → α) :
  ∥∏ i in s, f i∥₊ ≤ ∏ i in s, ∥f i∥₊ :=
(s.norm_prod_le f).trans_eq $ by simp [nnreal.coe_prod]

/-- If `α` is a seminormed ring, then `∥a ^ n∥₊ ≤ ∥a∥₊ ^ n` for `n > 0`.
See also `nnnorm_pow_le`. -/
lemma nnnorm_pow_le' (a : α) : ∀ {n : ℕ}, 0 < n → ∥a ^ n∥₊ ≤ ∥a∥₊ ^ n
| 1 h := by simp only [pow_one]
| (n + 2) h := by simpa only [pow_succ _ (n + 1)] using
    le_trans (nnnorm_mul_le _ _) (mul_le_mul_left' (nnnorm_pow_le' n.succ_pos) _)

/-- If `α` is a seminormed ring with `∥1∥₊ = 1`, then `∥a ^ n∥₊ ≤ ∥a∥₊ ^ n`.
See also `nnnorm_pow_le'`.-/
lemma nnnorm_pow_le [norm_one_class α] (a : α) (n : ℕ) : ∥a ^ n∥₊ ≤ ∥a∥₊ ^ n :=
nat.rec_on n (by simp only [pow_zero, nnnorm_one]) (λ k hk, nnnorm_pow_le' a k.succ_pos)

/-- If `α` is a seminormed ring, then `∥a ^ n∥ ≤ ∥a∥ ^ n` for `n > 0`. See also `norm_pow_le`. -/
lemma norm_pow_le' (a : α) {n : ℕ} (h : 0 < n) : ∥a ^ n∥ ≤ ∥a∥ ^ n :=
by simpa only [nnreal.coe_pow, coe_nnnorm] using nnreal.coe_mono (nnnorm_pow_le' a h)

/-- If `α` is a seminormed ring with `∥1∥ = 1`, then `∥a ^ n∥ ≤ ∥a∥ ^ n`. See also `norm_pow_le'`.-/
lemma norm_pow_le [norm_one_class α] (a : α) (n : ℕ) : ∥a ^ n∥ ≤ ∥a∥ ^ n :=
nat.rec_on n (by simp only [pow_zero, norm_one]) (λ n hn, norm_pow_le' a n.succ_pos)

lemma eventually_norm_pow_le (a : α) : ∀ᶠ (n:ℕ) in at_top, ∥a ^ n∥ ≤ ∥a∥ ^ n :=
eventually_at_top.mpr ⟨1, λ b h, norm_pow_le' a (nat.succ_le_iff.mp h)⟩

instance : semi_normed_ring (ulift α) :=
{ .. ulift.non_unital_semi_normed_ring,
  .. ulift.semi_normed_group }

/-- Seminormed ring structure on the product of two seminormed rings,
  using the sup norm. -/
instance prod.semi_normed_ring [semi_normed_ring β] :
  semi_normed_ring (α × β) :=
{ ..prod.non_unital_semi_normed_ring,
  ..prod.semi_normed_group, }

/-- Seminormed ring structure on the product of finitely many seminormed rings,
  using the sup norm. -/
instance pi.semi_normed_ring {π : ι → Type*} [fintype ι] [Π i, semi_normed_ring (π i)] :
  semi_normed_ring (Π i, π i) :=
{ ..pi.non_unital_semi_normed_ring,
  ..pi.semi_normed_group, }

end semi_normed_ring

section non_unital_normed_ring
variables [non_unital_normed_ring α]

instance : non_unital_normed_ring (ulift α) :=
{ .. ulift.non_unital_semi_normed_ring,
  .. ulift.semi_normed_group }

/-- Non-unital normed ring structure on the product of two non-unital normed rings,
using the sup norm. -/
instance prod.non_unital_normed_ring [non_unital_normed_ring β] : non_unital_normed_ring (α × β) :=
{ norm_mul := norm_mul_le,
  ..prod.semi_normed_group }

/-- Normed ring structure on the product of finitely many non-unital normed rings, using the sup
norm. -/
instance pi.non_unital_normed_ring {π : ι → Type*} [fintype ι] [Π i, non_unital_normed_ring (π i)] :
  non_unital_normed_ring (Π i, π i) :=
{ norm_mul := norm_mul_le,
  ..pi.normed_group }

end non_unital_normed_ring

section normed_ring

variables [normed_ring α]

lemma units.norm_pos [nontrivial α] (x : αˣ) : 0 < ∥(x:α)∥ :=
norm_pos_iff.mpr (units.ne_zero x)

lemma units.nnnorm_pos [nontrivial α] (x : αˣ) : 0 < ∥(x:α)∥₊ :=
x.norm_pos

instance : normed_ring (ulift α) :=
{ .. ulift.semi_normed_ring,
  .. ulift.normed_group }

/-- Normed ring structure on the product of two normed rings, using the sup norm. -/
instance prod.normed_ring [normed_ring β] : normed_ring (α × β) :=
{ norm_mul := norm_mul_le,
  ..prod.normed_group }

/-- Normed ring structure on the product of finitely many normed rings, using the sup norm. -/
instance pi.normed_ring {π : ι → Type*} [fintype ι] [Π i, normed_ring (π i)] :
  normed_ring (Π i, π i) :=
{ norm_mul := norm_mul_le,
  ..pi.normed_group }

end normed_ring

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_ring_top_monoid [non_unital_semi_normed_ring α] : has_continuous_mul α :=
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
instance semi_normed_top_ring [non_unital_semi_normed_ring α] : topological_ring α := { }

section normed_division_ring

variables [normed_division_ring α]

@[simp] lemma norm_mul (a b : α) : ∥a * b∥ = ∥a∥ * ∥b∥ :=
normed_division_ring.norm_mul' a b

@[priority 900]
instance normed_division_ring.to_norm_one_class : norm_one_class α :=
⟨mul_left_cancel₀ (mt norm_eq_zero.1 (@one_ne_zero α _ _)) $
  by rw [← norm_mul, mul_one, mul_one]⟩

@[simp] lemma nnnorm_mul (a b : α) : ∥a * b∥₊ = ∥a∥₊ * ∥b∥₊ :=
nnreal.eq $ norm_mul a b

/-- `norm` as a `monoid_with_zero_hom`. -/
@[simps] def norm_hom : α →*₀ ℝ := ⟨norm, norm_zero, norm_one, norm_mul⟩

/-- `nnnorm` as a `monoid_with_zero_hom`. -/
@[simps] def nnnorm_hom : α →*₀ ℝ≥0 := ⟨nnnorm, nnnorm_zero, nnnorm_one, nnnorm_mul⟩

@[simp] lemma norm_pow (a : α) : ∀ (n : ℕ), ∥a ^ n∥ = ∥a∥ ^ n :=
(norm_hom.to_monoid_hom : α →* ℝ).map_pow a

@[simp] lemma nnnorm_pow (a : α) (n : ℕ) : ∥a ^ n∥₊ = ∥a∥₊ ^ n :=
(nnnorm_hom.to_monoid_hom : α →* ℝ≥0).map_pow a n

protected lemma list.norm_prod (l : list α) : ∥l.prod∥ = (l.map norm).prod :=
(norm_hom.to_monoid_hom : α →* ℝ).map_list_prod _

protected lemma list.nnnorm_prod (l : list α) : ∥l.prod∥₊ = (l.map nnnorm).prod :=
(nnnorm_hom.to_monoid_hom : α →* ℝ≥0).map_list_prod _

@[simp] lemma norm_div (a b : α) : ∥a / b∥ = ∥a∥ / ∥b∥ := (norm_hom : α →*₀ ℝ).map_div a b

@[simp] lemma nnnorm_div (a b : α) : ∥a / b∥₊ = ∥a∥₊ / ∥b∥₊ := (nnnorm_hom : α →*₀ ℝ≥0).map_div a b

@[simp] lemma norm_inv (a : α) : ∥a⁻¹∥ = ∥a∥⁻¹ := (norm_hom : α →*₀ ℝ).map_inv a

@[simp] lemma nnnorm_inv (a : α) : ∥a⁻¹∥₊ = ∥a∥₊⁻¹ :=
nnreal.eq $ by simp

@[simp] lemma norm_zpow : ∀ (a : α) (n : ℤ), ∥a^n∥ = ∥a∥^n := (norm_hom : α →*₀ ℝ).map_zpow

@[simp] lemma nnnorm_zpow : ∀ (a : α) (n : ℤ), ∥a ^ n∥₊ = ∥a∥₊ ^ n :=
(nnnorm_hom : α →*₀ ℝ≥0).map_zpow

/-- Multiplication on the left by a nonzero element of a normed division ring tends to infinity at
infinity. TODO: use `bornology.cobounded` instead of `filter.comap has_norm.norm filter.at_top`. -/
lemma filter.tendsto_mul_left_cobounded {a : α} (ha : a ≠ 0) :
  tendsto ((*) a) (comap norm at_top) (comap norm at_top) :=
by simpa only [tendsto_comap_iff, (∘), norm_mul]
  using tendsto_const_nhds.mul_at_top (norm_pos_iff.2 ha) tendsto_comap

/-- Multiplication on the right by a nonzero element of a normed division ring tends to infinity at
infinity. TODO: use `bornology.cobounded` instead of `filter.comap has_norm.norm filter.at_top`. -/
lemma filter.tendsto_mul_right_cobounded {a : α} (ha : a ≠ 0) :
  tendsto (λ x, x * a) (comap norm at_top) (comap norm at_top) :=
by simpa only [tendsto_comap_iff, (∘), norm_mul]
  using tendsto_comap.at_top_mul (norm_pos_iff.2 ha) tendsto_const_nhds

@[priority 100] -- see Note [lower instance priority]
instance normed_division_ring.to_has_continuous_inv₀ : has_continuous_inv₀ α :=
begin
  refine ⟨λ r r0, tendsto_iff_norm_tendsto_zero.2 _⟩,
  have r0' : 0 < ∥r∥ := norm_pos_iff.2 r0,
  rcases exists_between r0' with ⟨ε, ε0, εr⟩,
  have : ∀ᶠ e in 𝓝 r, ∥e⁻¹ - r⁻¹∥ ≤ ∥r - e∥ / ∥r∥ / ε,
  { filter_upwards [(is_open_lt continuous_const continuous_norm).eventually_mem εr] with e he,
    have e0 : e ≠ 0 := norm_pos_iff.1 (ε0.trans he),
    calc ∥e⁻¹ - r⁻¹∥ = ∥r∥⁻¹ * ∥r - e∥ * ∥e∥⁻¹ : by
      { rw [←norm_inv, ←norm_inv, ←norm_mul, ←norm_mul, mul_sub, sub_mul, mul_assoc _ e,
          inv_mul_cancel r0, mul_inv_cancel e0, one_mul, mul_one] }
    ...              = ∥r - e∥ / ∥r∥ / ∥e∥ : by field_simp [mul_comm]
    ... ≤ ∥r - e∥ / ∥r∥ / ε :
      div_le_div_of_le_left (div_nonneg (norm_nonneg _) (norm_nonneg _)) ε0 he.le },
  refine squeeze_zero' (eventually_of_forall $ λ _, norm_nonneg _) this _,
  refine (continuous_const.sub continuous_id).norm.div_const.div_const.tendsto' _ _ _,
  simp,
end

end normed_division_ring

/-- A normed field is a field with a norm satisfying ∥x y∥ = ∥x∥ ∥y∥. -/
class normed_field (α : Type*) extends has_norm α, field α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul' : ∀ a b, norm (a * b) = norm a * norm b)

/-- A nontrivially normed field is a normed field in which there is an element of norm different
from `0` and `1`. This makes it possible to bring any element arbitrarily close to `0` by
multiplication by the powers of any element, and thus to relate algebra and topology. -/
class nontrivially_normed_field (α : Type*) extends normed_field α :=
(non_trivial : ∃ x : α, 1 < ∥x∥)

/-- A densely normed field is a normed field for which the image of the norm is dense in `ℝ`,
which means it is also nontrivially normed. However, not all nontrivally normed fields are densely
normed; in particular, the `padic`s exhibit this fact. -/
class densely_normed_field (α : Type*) extends normed_field α :=
(lt_norm_lt : ∀ x y : ℝ, 0 ≤ x → x < y → ∃ a : α, x < ∥a∥ ∧ ∥a∥ < y)

section normed_field

instance densely_normed_field.to_nontrivially_normed_field [densely_normed_field α] :
  nontrivially_normed_field α :=
{ non_trivial := let ⟨a, h, _⟩ := densely_normed_field.lt_norm_lt 1 2 zero_le_one one_lt_two in
    ⟨a, h⟩ }

variables [normed_field α]

@[priority 100] -- see Note [lower instance priority]
instance normed_field.to_normed_division_ring : normed_division_ring α :=
{ ..‹normed_field α› }

@[priority 100] -- see Note [lower instance priority]
instance normed_field.to_normed_comm_ring : normed_comm_ring α :=
{ norm_mul := λ a b, (norm_mul a b).le, ..‹normed_field α› }

@[simp] lemma norm_prod (s : finset β) (f : β → α) :
  ∥∏ b in s, f b∥ = ∏ b in s, ∥f b∥ :=
(norm_hom.to_monoid_hom : α →* ℝ).map_prod f s

@[simp] lemma nnnorm_prod (s : finset β) (f : β → α) :
  ∥∏ b in s, f b∥₊ = ∏ b in s, ∥f b∥₊ :=
(nnnorm_hom.to_monoid_hom : α →* ℝ≥0).map_prod f s

end normed_field

namespace normed_field

section nontrivially

variables (α) [nontrivially_normed_field α]

lemma exists_one_lt_norm : ∃x : α, 1 < ∥x∥ := ‹nontrivially_normed_field α›.non_trivial

lemma exists_lt_norm (r : ℝ) : ∃ x : α, r < ∥x∥ :=
let ⟨w, hw⟩ := exists_one_lt_norm α in
let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw in
⟨w^n, by rwa norm_pow⟩

lemma exists_norm_lt {r : ℝ} (hr : 0 < r) : ∃ x : α, 0 < ∥x∥ ∧ ∥x∥ < r :=
let ⟨w, hw⟩ := exists_lt_norm α r⁻¹ in
⟨w⁻¹, by rwa [← set.mem_Ioo, norm_inv, ← set.mem_inv, set.inv_Ioo_0_left hr]⟩

lemma exists_norm_lt_one : ∃x : α, 0 < ∥x∥ ∧ ∥x∥ < 1 :=
exists_norm_lt α one_pos

variable {α}

@[instance]
lemma punctured_nhds_ne_bot (x : α) : ne_bot (𝓝[≠] x) :=
begin
  rw [← mem_closure_iff_nhds_within_ne_bot, metric.mem_closure_iff],
  rintros ε ε0,
  rcases exists_norm_lt α ε0 with ⟨b, hb0, hbε⟩,
  refine ⟨x + b, mt (set.mem_singleton_iff.trans add_right_eq_self).1 $ norm_pos_iff.1 hb0, _⟩,
  rwa [dist_comm, dist_eq_norm, add_sub_cancel'],
end

@[instance]
lemma nhds_within_is_unit_ne_bot : ne_bot (𝓝[{x : α | is_unit x}] 0) :=
by simpa only [is_unit_iff_ne_zero] using punctured_nhds_ne_bot (0:α)

end nontrivially

section densely

variables (α) [densely_normed_field α]

lemma exists_lt_norm_lt {r₁ r₂ : ℝ} (h₀ : 0 ≤ r₁) (h : r₁ < r₂) : ∃ x : α, r₁ < ∥x∥ ∧ ∥x∥ < r₂ :=
densely_normed_field.lt_norm_lt r₁ r₂ h₀ h

lemma exists_lt_nnnorm_lt {r₁ r₂ : ℝ≥0} (h : r₁ < r₂) : ∃ x : α, r₁ < ∥x∥₊ ∧ ∥x∥₊ < r₂ :=
by exact_mod_cast exists_lt_norm_lt α r₁.prop h

instance densely_ordered_range_norm : densely_ordered (set.range (norm : α → ℝ)) :=
{ dense :=
  begin
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy,
    exact let ⟨z, h⟩ := exists_lt_norm_lt α (norm_nonneg _) hxy in ⟨⟨∥z∥, z, rfl⟩, h⟩,
  end }

instance densely_ordered_range_nnnorm : densely_ordered (set.range (nnnorm : α → ℝ≥0)) :=
{ dense :=
  begin
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy,
    exact let ⟨z, h⟩ := exists_lt_nnnorm_lt α hxy in ⟨⟨∥z∥₊, z, rfl⟩, h⟩,
  end }

lemma dense_range_nnnorm : dense_range (nnnorm : α → ℝ≥0) :=
dense_of_exists_between $ λ _ _ hr, let ⟨x, h⟩ := exists_lt_nnnorm_lt α hr in ⟨∥x∥₊, ⟨x, rfl⟩, h⟩

end densely

end normed_field

instance : normed_field ℝ :=
{ norm_mul' := abs_mul,
  .. real.normed_group }

instance : densely_normed_field ℝ :=
{ lt_norm_lt := λ _ _ h₀ hr, let ⟨x, h⟩ := exists_between hr in
    ⟨x, by rwa [real.norm_eq_abs, abs_of_nonneg (h₀.trans h.1.le)]⟩ }

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
  ne_bot (𝓝[≠] x) :=
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
lemma normed_group.tendsto_at_top' [nonempty α] [semilattice_sup α] [no_max_order α]
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

lemma int.abs_le_floor_nnreal_iff (z : ℤ) (c : ℝ≥0) : |z| ≤ ⌊c⌋₊ ↔ ∥z∥₊ ≤ c :=
begin
  rw [int.abs_eq_nat_abs, int.coe_nat_le, nat.le_floor_iff (zero_le c)],
  congr',
  exact nnreal.coe_nat_abs z,
end

instance : norm_one_class ℤ :=
⟨by simp [← int.norm_cast_real]⟩

instance : normed_field ℚ :=
{ norm := λ r, ∥(r : ℝ)∥,
  norm_mul' := λ r₁ r₂, by simp only [norm, rat.cast_mul, abs_mul],
  dist_eq := λ r₁ r₂, by simp only [rat.dist_eq, norm, rat.cast_sub] }

instance : densely_normed_field ℚ :=
{ lt_norm_lt := λ r₁ r₂ h₀ hr, let ⟨q, h⟩ := exists_rat_btwn hr in
    ⟨q, by { unfold norm, rwa abs_of_pos (h₀.trans_lt h.1) } ⟩ }

@[norm_cast, simp] lemma rat.norm_cast_real (r : ℚ) : ∥(r : ℝ)∥ = ∥r∥ := rfl

@[norm_cast, simp] lemma int.norm_cast_rat (m : ℤ) : ∥(m : ℚ)∥ = ∥m∥ :=
by rw [← rat.norm_cast_real, ← int.norm_cast_real]; congr' 1; norm_cast

-- Now that we've installed the norm on `ℤ`,
-- we can state some lemmas about `nsmul` and `zsmul`.
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

lemma norm_zsmul_le (n : ℤ) (a : α) : ∥n • a∥ ≤ ∥n∥ * ∥a∥ :=
begin
  induction n with n n,
  { simp only [int.of_nat_eq_coe, coe_nat_zsmul],
    convert norm_nsmul_le n a,
    exact nat.abs_cast n },
  { simp only [int.neg_succ_of_nat_coe, neg_smul, norm_neg, coe_nat_zsmul],
    convert norm_nsmul_le n.succ a,
    exact nat.abs_cast n.succ, }
end

lemma nnnorm_nsmul_le (n : ℕ) (a : α) : ∥n • a∥₊ ≤ n * ∥a∥₊ :=
by simpa only [←nnreal.coe_le_coe, nnreal.coe_mul, nnreal.coe_nat_cast]
  using norm_nsmul_le n a

lemma nnnorm_zsmul_le (n : ℤ) (a : α) : ∥n • a∥₊ ≤ ∥n∥₊ * ∥a∥₊ :=
by simpa only [←nnreal.coe_le_coe, nnreal.coe_mul] using norm_zsmul_le n a

end

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

section ring_hom_isometric

variables {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

/-- This class states that a ring homomorphism is isometric. This is a sufficient assumption
for a continuous semilinear map to be bounded and this is the main use for this typeclass. -/
class ring_hom_isometric [semiring R₁] [semiring R₂] [has_norm R₁] [has_norm R₂]
  (σ : R₁ →+* R₂) : Prop :=
(is_iso : ∀ {x : R₁}, ∥σ x∥ = ∥x∥)

attribute [simp] ring_hom_isometric.is_iso

variables [semi_normed_ring R₁] [semi_normed_ring R₂] [semi_normed_ring R₃]

instance ring_hom_isometric.ids : ring_hom_isometric (ring_hom.id R₁) :=
⟨λ x, rfl⟩

end ring_hom_isometric
