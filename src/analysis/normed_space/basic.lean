/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Normed spaces.

Authors: Patrick Massot, Johannes Hölzl
-/

import algebra.pi_instances
import topology.instances.nnreal topology.instances.complex
variables {α : Type*} {β : Type*} {γ : Type*} {ι : Type*}

noncomputable theory
open filter metric
local notation f `→_{`:50 a `}`:0 b := tendsto f (nhds a) (nhds b)

class has_norm (α : Type*) := (norm : α → ℝ)

export has_norm (norm)

notation `∥`:1024 e:1 `∥`:1 := norm e

class normed_group (α : Type*) extends has_norm α, add_comm_group α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))

/-- Construct a normed group from a translation invariant distance -/
def normed_group.of_add_dist [has_norm α] [add_comm_group α] [metric_space α]
  (H1 : ∀ x:α, ∥x∥ = dist x 0)
  (H2 : ∀ x y z : α, dist x y ≤ dist (x + z) (y + z)) : normed_group α :=
{ dist_eq := λ x y, begin
    rw H1, apply le_antisymm,
    { rw [sub_eq_add_neg, ← add_right_neg y], apply H2 },
    { have := H2 (x-y) 0 y, rwa [sub_add_cancel, zero_add] at this }
  end }

/-- Construct a normed group from a translation invariant distance -/
def normed_group.of_add_dist' [has_norm α] [add_comm_group α] [metric_space α]
  (H1 : ∀ x:α, ∥x∥ = dist x 0)
  (H2 : ∀ x y z : α, dist (x + z) (y + z) ≤ dist x y) : normed_group α :=
{ dist_eq := λ x y, begin
    rw H1, apply le_antisymm,
    { have := H2 (x-y) 0 y, rwa [sub_add_cancel, zero_add] at this },
    { rw [sub_eq_add_neg, ← add_right_neg y], apply H2 }
  end }

section normed_group
variables [normed_group α] [normed_group β]

lemma dist_eq_norm (g h : α) : dist g h = ∥g - h∥ :=
normed_group.dist_eq _ _

@[simp] lemma dist_zero_right (g : α) : dist g 0 = ∥g∥ :=
by { rw[dist_eq_norm], simp }

lemma norm_triangle (g h : α) : ∥g + h∥ ≤ ∥g∥ + ∥h∥ :=
calc ∥g + h∥ = ∥g - (-h)∥             : by simp
         ... = dist g (-h)            : by simp[dist_eq_norm]
         ... ≤ dist g 0 + dist 0 (-h) : by apply dist_triangle
         ... = ∥g∥ + ∥h∥               : by simp[dist_eq_norm]

@[simp] lemma norm_nonneg (g : α) : 0 ≤ ∥g∥ :=
by { rw[←dist_zero_right], exact dist_nonneg }

lemma norm_eq_zero (g : α) : ∥g∥ = 0 ↔ g = 0 :=
by { rw[←dist_zero_right], exact dist_eq_zero }

@[simp] lemma norm_zero : ∥(0:α)∥ = 0 := (norm_eq_zero _).2 (by simp)

lemma norm_triangle_sum {β} : ∀(s : finset β) (f : β → α), ∥s.sum f∥ ≤ s.sum (λa, ∥ f a ∥) :=
finset.le_sum_of_subadditive norm norm_zero norm_triangle

lemma norm_pos_iff (g : α) : 0 < ∥ g ∥ ↔ g ≠ 0 :=
begin
  split ; intro h ; rw[←dist_zero_right] at *,
  { exact dist_pos.1 h },
  { exact dist_pos.2 h }
end

lemma norm_le_zero_iff (g : α) : ∥g∥ ≤ 0 ↔ g = 0 :=
by { rw[←dist_zero_right], exact dist_le_zero }

@[simp] lemma norm_neg (g : α) : ∥-g∥ = ∥g∥ :=
calc ∥-g∥ = ∥0 - g∥ : by simp
      ... = dist 0 g : (dist_eq_norm 0 g).symm
      ... = dist g 0 : dist_comm _ _
      ... = ∥g - 0∥ : (dist_eq_norm g 0)
      ... = ∥g∥ : by simp

lemma norm_reverse_triangle' (a b : α) : ∥a∥ - ∥b∥ ≤ ∥a - b∥ :=
by simpa using add_le_add (norm_triangle (a - b) (b)) (le_refl (-∥b∥))

lemma norm_reverse_triangle (a b : α) : abs(∥a∥ - ∥b∥) ≤ ∥a - b∥ :=
suffices -(∥a∥ - ∥b∥) ≤ ∥a - b∥, from abs_le_of_le_of_neg_le (norm_reverse_triangle' a b) this,
calc -(∥a∥ - ∥b∥) = ∥b∥ - ∥a∥ : by abel
             ... ≤ ∥b - a∥ : norm_reverse_triangle' b a
             ... = ∥a - b∥ : by rw ← norm_neg (a - b); simp

lemma norm_triangle_sub {a b : α} : ∥a - b∥ ≤ ∥a∥ + ∥b∥ :=
by simpa only [sub_eq_add_neg, norm_neg] using norm_triangle a (-b)

lemma abs_norm_sub_norm_le (g h : α) : abs(∥g∥ - ∥h∥) ≤ ∥g - h∥ :=
abs_le.2 $ and.intro
  (suffices -∥g - h∥ ≤ -(∥h∥ - ∥g∥), by simpa,
    neg_le_neg $ sub_right_le_of_le_add $
    calc ∥h∥ = ∥h - g + g∥ : by simp
      ... ≤ ∥h - g∥ + ∥g∥ : norm_triangle _ _
      ... = ∥-(g - h)∥ + ∥g∥ : by simp
      ... = ∥g - h∥ + ∥g∥ : by { rw [norm_neg (g-h)] })
  (sub_right_le_of_le_add $ calc ∥g∥ = ∥g - h + h∥ : by simp ... ≤ ∥g-h∥ + ∥h∥ : norm_triangle _ _)

lemma dist_norm_norm_le (g h : α) : dist ∥g∥ ∥h∥ ≤ ∥g - h∥ :=
abs_norm_sub_norm_le g h

lemma norm_sub_rev (g h : α) : ∥g - h∥ = ∥h - g∥ :=
by rw ←norm_neg; simp

lemma ball_0_eq (ε : ℝ) : ball (0:α) ε = {x | ∥x∥ < ε} :=
set.ext $ assume a, by simp

theorem normed_space.tendsto_nhds_zero {f : γ → α} {l : filter γ} :
  tendsto f l (nhds 0) ↔ ∀ ε > 0, { x | ∥ f x ∥ < ε } ∈ l :=
begin
  rw [metric.tendsto_nhds], simp only [normed_group.dist_eq, sub_zero],
  split,
  { intros h ε εgt0,
    rcases h ε εgt0 with ⟨s, ssets, hs⟩,
    exact mem_sets_of_superset ssets hs },
  intros h ε εgt0,
  exact ⟨_, h ε εgt0, set.subset.refl _⟩
end


section nnnorm

def nnnorm (a : α) : nnreal := ⟨norm a, norm_nonneg a⟩

@[simp] lemma coe_nnnorm (a : α) : (nnnorm a : ℝ) = norm a := rfl

lemma nndist_eq_nnnorm (a b : α) : nndist a b = nnnorm (a - b) := nnreal.eq $ dist_eq_norm _ _

lemma nnnorm_eq_zero (a : α) : nnnorm a = 0 ↔ a = 0 :=
by simp only [nnreal.eq_iff.symm, nnreal.coe_zero, coe_nnnorm, norm_eq_zero]

@[simp] lemma nnnorm_zero : nnnorm (0 : α) = 0 :=
nnreal.eq norm_zero

lemma nnnorm_triangle (g h : α) : nnnorm (g + h) ≤ nnnorm g + nnnorm h :=
by simpa [nnreal.coe_le] using norm_triangle g h

@[simp] lemma nnnorm_neg (g : α) : nnnorm (-g) = nnnorm g :=
nnreal.eq $ norm_neg g

lemma nndist_nnnorm_nnnorm_le (g h : α) : nndist (nnnorm g) (nnnorm h) ≤ nnnorm (g - h) :=
nnreal.coe_le.2 $ dist_norm_norm_le g h

end nnnorm

instance prod.normed_group [normed_group β] : normed_group (α × β) :=
{ norm := λx, max ∥x.1∥ ∥x.2∥,
  dist_eq := assume (x y : α × β),
    show max (dist x.1 y.1) (dist x.2 y.2) = (max ∥(x - y).1∥ ∥(x - y).2∥), by simp [dist_eq_norm] }

lemma norm_fst_le (x : α × β) : ∥x.1∥ ≤ ∥x∥ :=
begin have : ∥x∥ = max (∥x.fst∥) (∥x.snd∥) := rfl, rw this, simp[le_max_left] end

lemma norm_snd_le (x : α × β) : ∥x.2∥ ≤ ∥x∥ :=
begin have : ∥x∥ = max (∥x.fst∥) (∥x.snd∥) := rfl, rw this, simp[le_max_right] end

instance fintype.normed_group {π : α → Type*} [fintype α] [∀i, normed_group (π i)] :
  normed_group (Πb, π b) :=
{ norm := λf, ((finset.sup finset.univ (λ b, nnnorm (f b)) : nnreal) : ℝ),
  dist_eq := assume x y,
    congr_arg (coe : nnreal → ℝ) $ congr_arg (finset.sup finset.univ) $ funext $ assume a,
    show nndist (x a) (y a) = nnnorm (x a - y a), from nndist_eq_nnnorm _ _ }

lemma tendsto_iff_norm_tendsto_zero {f : ι → β} {a : filter ι} {b : β} :
  tendsto f a (nhds b) ↔ tendsto (λ e, ∥ f e - b ∥) a (nhds 0) :=
by rw tendsto_iff_dist_tendsto_zero ; simp only [(dist_eq_norm _ _).symm]

lemma tendsto_zero_iff_norm_tendsto_zero [normed_group α] [normed_group β]
  {f : γ → β} {a : filter γ} :
  tendsto f a (nhds 0) ↔ tendsto (λ e, ∥ f e ∥) a (nhds 0) :=
have tendsto f a (nhds 0) ↔ tendsto (λ e, ∥ f e - 0 ∥) a (nhds 0) :=
  tendsto_iff_norm_tendsto_zero,
by simpa

lemma lim_norm (x : α) : (λg:α, ∥g - x∥) →_{x} 0 :=
tendsto_iff_norm_tendsto_zero.1 (continuous_iff_continuous_at.1 continuous_id x)

lemma lim_norm_zero : (λg:α, ∥g∥) →_{0} 0 :=
by simpa using lim_norm (0:α)

lemma continuous_norm : continuous (λg:α, ∥g∥) :=
begin
  rw continuous_iff_continuous_at,
  intro x,
  rw [continuous_at, tendsto_iff_dist_tendsto_zero],
  exact squeeze_zero (λ t, abs_nonneg _) (λ t, abs_norm_sub_norm_le _ _) (lim_norm x)
end

lemma continuous_nnnorm : continuous (nnnorm : α → nnreal) :=
continuous_subtype_mk _ continuous_norm

instance normed_uniform_group : uniform_add_group α :=
begin
  refine ⟨metric.uniform_continuous_iff.2 $ assume ε hε, ⟨ε / 2, half_pos hε, assume a b h, _⟩⟩,
  rw [prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at h,
  calc dist (a.1 - a.2) (b.1 - b.2) = ∥(a.1 - b.1) - (a.2 - b.2)∥  : by simp [dist_eq_norm]
    ... ≤ ∥a.1 - b.1∥ + ∥a.2 - b.2∥ : norm_triangle_sub
    ... < ε / 2 + ε / 2 : add_lt_add h.1 h.2
    ... = ε : add_halves _
end

instance normed_top_monoid : topological_add_monoid α := by apply_instance
instance normed_top_group : topological_add_group α := by apply_instance

end normed_group

section normed_ring

class normed_ring (α : Type*) extends has_norm α, ring α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

instance normed_ring.to_normed_group [β : normed_ring α] : normed_group α := { ..β }

lemma norm_mul_le {α : Type*} [normed_ring α] (a b : α) : (∥a*b∥) ≤ (∥a∥) * (∥b∥) :=
normed_ring.norm_mul _ _

lemma norm_pow_le {α : Type*} [normed_ring α] (a : α) : ∀ {n : ℕ}, n > 0 → ∥a^n∥ ≤ ∥a∥^n
| 1 h := by simp
| (n+2) h :=
  le_trans (norm_mul_le a (a^(n+1)))
           (mul_le_mul (le_refl _)
                       (norm_pow_le (nat.succ_pos _)) (norm_nonneg _) (norm_nonneg _))

instance prod.normed_ring [normed_ring α] [normed_ring β] : normed_ring (α × β) :=
{ norm_mul := assume x y,
  calc
    ∥x * y∥ = ∥(x.1*y.1, x.2*y.2)∥ : rfl
        ... = (max ∥x.1*y.1∥  ∥x.2*y.2∥) : rfl
        ... ≤ (max (∥x.1∥*∥y.1∥) (∥x.2∥*∥y.2∥)) :
          max_le_max (norm_mul_le (x.1) (y.1)) (norm_mul_le (x.2) (y.2))
        ... = (max (∥x.1∥*∥y.1∥) (∥y.2∥*∥x.2∥)) : by simp[mul_comm]
        ... ≤ (max (∥x.1∥) (∥x.2∥)) * (max (∥y.2∥) (∥y.1∥)) : by { apply max_mul_mul_le_max_mul_max; simp [norm_nonneg] }
        ... = (max (∥x.1∥) (∥x.2∥)) * (max (∥y.1∥) (∥y.2∥)) : by simp[max_comm]
        ... = (∥x∥*∥y∥) : rfl,
  ..prod.normed_group }
end normed_ring

instance normed_ring_top_monoid [normed_ring α] : topological_monoid α :=
⟨ continuous_iff_continuous_at.2 $ λ x, tendsto_iff_norm_tendsto_zero.2 $
    have ∀ e : α × α, e.fst * e.snd - x.fst * x.snd =
      e.fst * e.snd - e.fst * x.snd + (e.fst * x.snd - x.fst * x.snd), by intro; rw sub_add_sub_cancel,
    begin
      apply squeeze_zero,
      { intro, apply norm_nonneg },
      { simp only [this], intro, apply norm_triangle },
      { rw ←zero_add (0 : ℝ), apply tendsto_add,
        { apply squeeze_zero,
          { intro, apply norm_nonneg },
          { intro t, show ∥t.fst * t.snd - t.fst * x.snd∥ ≤ ∥t.fst∥ * ∥t.snd - x.snd∥,
            rw ←mul_sub, apply norm_mul_le },
          { rw ←mul_zero (∥x.fst∥), apply tendsto_mul,
            { apply continuous_iff_continuous_at.1,
              apply continuous.comp,
              { apply continuous_fst },
              { apply continuous_norm }},
            { apply tendsto_iff_norm_tendsto_zero.1,
              apply continuous_iff_continuous_at.1,
              apply continuous_snd }}},
        { apply squeeze_zero,
          { intro, apply norm_nonneg },
          { intro t, show ∥t.fst * x.snd - x.fst * x.snd∥ ≤ ∥t.fst - x.fst∥ * ∥x.snd∥,
            rw ←sub_mul, apply norm_mul_le },
          { rw ←zero_mul (∥x.snd∥), apply tendsto_mul,
            { apply tendsto_iff_norm_tendsto_zero.1,
              apply continuous_iff_continuous_at.1,
              apply continuous_fst },
            { apply tendsto_const_nhds }}}}
    end ⟩

instance normed_top_ring [normed_ring α] : topological_ring α :=
⟨ continuous_iff_continuous_at.2 $ λ x, tendsto_iff_norm_tendsto_zero.2 $
    have ∀ e : α, -e - -x = -(e - x), by intro; simp,
    by simp only [this, norm_neg]; apply lim_norm ⟩

section normed_field

class normed_field (α : Type*) extends has_norm α, discrete_field α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) = norm a * norm b)

class nondiscrete_normed_field (α : Type*) extends normed_field α :=
(non_trivial : ∃x:α, 1<∥x∥)

instance normed_field.to_normed_ring [i : normed_field α] : normed_ring α :=
{ norm_mul := by finish [i.norm_mul], ..i }

@[simp] lemma norm_one {α : Type*} [normed_field α] : ∥(1 : α)∥ = 1 :=
have  ∥(1 : α)∥ * ∥(1 : α)∥ = ∥(1 : α)∥ * 1, by calc
 ∥(1 : α)∥ * ∥(1 : α)∥ = ∥(1 : α) * (1 : α)∥ : by rw normed_field.norm_mul
                  ... = ∥(1 : α)∥ * 1 : by simp,
eq_of_mul_eq_mul_left (ne_of_gt ((norm_pos_iff _).2 (by simp))) this

@[simp] lemma norm_mul [normed_field α] (a b : α) : ∥a * b∥ = ∥a∥ * ∥b∥ :=
normed_field.norm_mul a b

instance normed_field.is_monoid_hom_norm [normed_field α] : is_monoid_hom (norm : α → ℝ) :=
{ map_one := norm_one, map_mul := norm_mul }

@[simp] lemma norm_pow [normed_field α] (a : α) : ∀ (n : ℕ), ∥a^n∥ = ∥a∥^n :=
is_monoid_hom.map_pow norm a

@[simp] lemma norm_prod {β : Type*} [normed_field α] (s : finset β) (f : β → α) :
  ∥s.prod f∥ = s.prod (λb, ∥f b∥) :=
eq.symm (finset.prod_hom norm)

@[simp] lemma norm_div {α : Type*} [normed_field α] (a b : α) : ∥a/b∥ = ∥a∥/∥b∥ :=
if hb : b = 0 then by simp [hb] else
begin
  apply eq_div_of_mul_eq,
  { apply ne_of_gt, apply (norm_pos_iff _).mpr hb },
  { rw [←normed_field.norm_mul, div_mul_cancel _ hb] }
end

@[simp] lemma norm_inv {α : Type*} [normed_field α] (a : α) : ∥a⁻¹∥ = ∥a∥⁻¹ :=
by simp only [inv_eq_one_div, norm_div, norm_one]

@[simp] lemma norm_fpow {α : Type*} [normed_field α] (a : α) : ∀n : ℤ,
  ∥a^n∥ = ∥a∥^n
| (n : ℕ) := norm_pow a n
| -[1+ n] := by simp [fpow_neg_succ_of_nat]

lemma exists_one_lt_norm (α : Type*) [i : nondiscrete_normed_field α] : ∃x : α, 1 < ∥x∥ :=
i.non_trivial

lemma exists_norm_lt_one (α : Type*) [nondiscrete_normed_field α] : ∃x : α, 0 < ∥x∥ ∧ ∥x∥ < 1 :=
begin
  rcases exists_one_lt_norm α with ⟨y, hy⟩,
  refine ⟨y⁻¹, _, _⟩,
  { simp only [inv_eq_zero, ne.def, norm_pos_iff],
    assume h,
    rw ← norm_eq_zero at h,
    rw h at hy,
    exact lt_irrefl _ (lt_trans zero_lt_one hy) },
  { simp [inv_lt_one hy] }
end

instance : normed_field ℝ :=
{ norm := λ x, abs x,
  dist_eq := assume x y, rfl,
  norm_mul := abs_mul }

instance : nondiscrete_normed_field ℝ :=
{ non_trivial := ⟨2, by { unfold norm, rw abs_of_nonneg; norm_num }⟩ }

lemma real.norm_eq_abs (r : ℝ): norm r = abs r := rfl

end normed_field

@[simp] lemma norm_norm [normed_group α] (x : α) : ∥∥x∥∥ = ∥x∥ :=
by rw [real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]

section normed_space

class normed_space (α : Type*) (β : Type*) [normed_field α]
  extends normed_group β, vector_space α β :=
(norm_smul : ∀ (a:α) b, norm (a • b) = has_norm.norm a * norm b)

variables [normed_field α]

instance normed_field.to_normed_space : normed_space α α :=
{ dist_eq := normed_field.dist_eq,
  norm_smul := normed_field.norm_mul }

set_option class.instance_max_depth 43

lemma norm_smul [normed_space α β] (s : α) (x : β) : ∥s • x∥ = ∥s∥ * ∥x∥ :=
normed_space.norm_smul s x

lemma nnnorm_smul [normed_space α β] (s : α) (x : β) : nnnorm (s • x) = nnnorm s * nnnorm x :=
nnreal.eq $ norm_smul s x

variables {E : Type*} {F : Type*} [normed_space α E] [normed_space α F]

lemma tendsto_smul {f : γ → α} { g : γ → F} {e : filter γ} {s : α} {b : F} :
  (tendsto f e (nhds s)) → (tendsto g e (nhds b)) → tendsto (λ x, (f x) • (g x)) e (nhds (s • b)) :=
begin
  intros limf limg,
  rw tendsto_iff_norm_tendsto_zero,
  have ineq := λ x : γ, calc
      ∥f x • g x - s • b∥ = ∥(f x • g x - s • g x) + (s • g x - s • b)∥ : by simp[add_assoc]
                      ... ≤ ∥f x • g x - s • g x∥ + ∥s • g x - s • b∥ : norm_triangle (f x • g x - s • g x) (s • g x - s • b)
                      ... ≤ ∥f x - s∥*∥g x∥ + ∥s∥*∥g x - b∥ : by { rw [←smul_sub, ←sub_smul, norm_smul, norm_smul] },
  apply squeeze_zero,
  { intro t, exact norm_nonneg _ },
  { exact ineq },
  { clear ineq,

    have limf': tendsto (λ x, ∥f x - s∥) e (nhds 0) := tendsto_iff_norm_tendsto_zero.1 limf,
    have limg' : tendsto (λ x, ∥g x∥) e (nhds ∥b∥) := filter.tendsto.comp limg (continuous_iff_continuous_at.1 continuous_norm _),

    have lim1 := tendsto_mul limf' limg',
    simp only [zero_mul, sub_eq_add_neg] at lim1,

    have limg3 := tendsto_iff_norm_tendsto_zero.1 limg,

    have lim2 := tendsto_mul (tendsto_const_nhds : tendsto _ _ (nhds ∥ s ∥)) limg3,
    simp only [sub_eq_add_neg, mul_zero] at lim2,

    rw [show (0:ℝ) = 0 + 0, by simp],
    exact tendsto_add lim1 lim2  }
end

lemma tendsto_smul_const {g : γ → F} {e : filter γ} (s : α) {b : F} :
  (tendsto g e (nhds b)) → tendsto (λ x, s • (g x)) e (nhds (s • b)) :=
tendsto_smul tendsto_const_nhds

lemma continuous_smul [topological_space γ] {f : γ → α} {g : γ → E}
  (hf : continuous f) (hg : continuous g) : continuous (λc, f c • g c) :=
continuous_iff_continuous_at.2 $ assume c,
  tendsto_smul (continuous_iff_continuous_at.1 hf _) (continuous_iff_continuous_at.1 hg _)

/-- If there is a scalar `c` with `∥c∥>1`, then any element can be moved by scalar multiplication to
any shell of width `∥c∥`. Also recap information on the norm of the rescaling element that shows
up in applications. -/
lemma rescale_to_shell {c : α} (hc : 1 < ∥c∥) {ε : ℝ} (εpos : 0 < ε) {x : E} (hx : x ≠ 0) :
  ∃d:α, d ≠ 0 ∧ ∥d • x∥ ≤ ε ∧ (ε/∥c∥ ≤ ∥d • x∥) ∧ (∥d∥⁻¹ ≤ ε⁻¹ * ∥c∥ * ∥x∥) :=
begin
  have xεpos : 0 < ∥x∥/ε := div_pos_of_pos_of_pos ((norm_pos_iff _).2 hx) εpos,
  rcases exists_int_pow_near xεpos hc with ⟨n, hn⟩,
  have cpos : 0 < ∥c∥ := lt_trans (zero_lt_one : (0 :ℝ) < 1) hc,
  have cnpos : 0 < ∥c^(n+1)∥ := by { rw norm_fpow, exact lt_trans xεpos hn.2 },
  refine ⟨(c^(n+1))⁻¹, _, _, _, _⟩,
  show (c ^ (n + 1))⁻¹  ≠ 0,
    by rwa [ne.def, inv_eq_zero, ← ne.def, ← norm_pos_iff],
  show ∥(c ^ (n + 1))⁻¹ • x∥ ≤ ε,
  { rw [norm_smul, norm_inv, ← div_eq_inv_mul, div_le_iff cnpos, mul_comm, norm_fpow],
    exact (div_le_iff εpos).1 (le_of_lt (hn.2)) },
  show ε / ∥c∥ ≤ ∥(c ^ (n + 1))⁻¹ • x∥,
  { rw [div_le_iff cpos, norm_smul, norm_inv, norm_fpow, fpow_add (ne_of_gt cpos),
        fpow_one, mul_inv', mul_comm, ← mul_assoc, ← mul_assoc, mul_inv_cancel (ne_of_gt cpos),
        one_mul, ← div_eq_inv_mul, le_div_iff (fpow_pos_of_pos cpos _), mul_comm],
    exact (le_div_iff εpos).1 hn.1 },
  show ∥(c ^ (n + 1))⁻¹∥⁻¹ ≤ ε⁻¹ * ∥c∥ * ∥x∥,
  { have : ε⁻¹ * ∥c∥ * ∥x∥ = ε⁻¹ * ∥x∥ * ∥c∥, by ring,
    rw [norm_inv, inv_inv', norm_fpow, fpow_add (ne_of_gt cpos), fpow_one, this, ← div_eq_inv_mul],
    exact mul_le_mul_of_nonneg_right hn.1 (norm_nonneg _) }
end

instance : normed_space α (E × F) :=
{ norm_smul :=
  begin
    intros s x,
    cases x with x₁ x₂,
    change max (∥s • x₁∥) (∥s • x₂∥) = ∥s∥ * max (∥x₁∥) (∥x₂∥),
    rw [norm_smul, norm_smul, ← mul_max_of_nonneg _ _ (norm_nonneg _)]
  end,

  add_smul := λ r x y, prod.ext (add_smul _ _ _) (add_smul _ _ _),
  smul_add := λ r x y, prod.ext (smul_add _ _ _) (smul_add _ _ _),
  ..prod.normed_group,
  ..prod.vector_space }

instance fintype.normed_space {ι : Type*} {E : ι → Type*} [fintype ι] [∀i, normed_space α (E i)] :
  normed_space α (Πi, E i) :=
{ norm := λf, ((finset.univ.sup (λb, nnnorm (f b)) : nnreal) : ℝ),
  dist_eq :=
    assume f g, congr_arg coe $ congr_arg (finset.sup finset.univ) $
    by funext i; exact nndist_eq_nnnorm _ _,
  norm_smul := λ a f,
    show (↑(finset.sup finset.univ (λ (b : ι), nnnorm (a • f b))) : ℝ) =
      nnnorm a * ↑(finset.sup finset.univ (λ (b : ι), nnnorm (f b))),
    by simp only [(nnreal.coe_mul _ _).symm, nnreal.mul_finset_sup, nnnorm_smul],
  ..metric_space_pi,
  ..pi.vector_space α }

/-- A normed space can be built from a norm that satisfies algebraic properties. This is
formalised in this structure. -/
structure normed_space.core (α : Type*) (β : Type*)
  [normed_field α] [add_comm_group β] [has_scalar α β] [has_norm β] :=
(norm_eq_zero_iff : ∀ x : β, ∥x∥ = 0 ↔ x = 0)
(norm_smul : ∀ c : α, ∀ x : β, ∥c • x∥ = ∥c∥ * ∥x∥)
(triangle : ∀ x y : β, ∥x + y∥ ≤ ∥x∥ + ∥y∥)

noncomputable def normed_space.of_core (α : Type*) (β : Type*)
  [normed_field α] [add_comm_group β] [vector_space α β] [has_norm β]
  (C : normed_space.core α β) : normed_space α β :=
{ dist := λ x y, ∥x - y∥,
  dist_eq := assume x y, by refl,
  dist_self := assume x, (C.norm_eq_zero_iff (x - x)).mpr (show x - x = 0, by simp),
  eq_of_dist_eq_zero := assume x y h, show (x = y), from sub_eq_zero.mp $ (C.norm_eq_zero_iff (x - y)).mp h,
  dist_triangle := assume x y z,
    calc ∥x - z∥ = ∥x - y + (y - z)∥ : by simp
            ... ≤ ∥x - y∥ + ∥y - z∥  : C.triangle _ _,
  dist_comm := assume x y,
    calc ∥x - y∥ = ∥ -(1 : α) • (y - x)∥ : by simp
             ... = ∥y - x∥ : begin rw[C.norm_smul], simp end,
  norm_smul := C.norm_smul }

end normed_space

section summable
local attribute [instance] classical.prop_decidable
open finset filter
variables [normed_group α] [complete_space α]

lemma summable_iff_vanishing_norm {f : ι → α} :
  summable f ↔ ∀ε>0, (∃s:finset ι, ∀t, disjoint t s → ∥ t.sum f ∥ < ε) :=
begin
  simp only [summable_iff_vanishing, metric.mem_nhds_iff, exists_imp_distrib],
  split,
  { assume h ε hε, refine h {x | ∥x∥ < ε} ε hε _, rw [ball_0_eq ε] },
  { assume h s ε hε hs,
    rcases h ε hε with ⟨t, ht⟩,
    refine ⟨t, assume u hu, hs _⟩,
    rw [ball_0_eq],
    exact ht u hu }
end

lemma summable_of_norm_bounded {f : ι → α} (g : ι → ℝ) (hf : summable g) (h : ∀i, ∥f i∥ ≤ g i) :
  summable f :=
summable_iff_vanishing_norm.2 $ assume ε hε,
  let ⟨s, hs⟩ := summable_iff_vanishing_norm.1 hf ε hε in
  ⟨s, assume t ht,
    have ∥t.sum g∥ < ε := hs t ht,
    have nn : 0 ≤ t.sum g := finset.zero_le_sum (assume a _, le_trans (norm_nonneg _) (h a)),
    lt_of_le_of_lt (norm_triangle_sum t f) $ lt_of_le_of_lt (finset.sum_le_sum $ assume i _, h i) $
      by rwa [real.norm_eq_abs, abs_of_nonneg nn] at this⟩

lemma summable_of_summable_norm {f : ι → α} (hf : summable (λa, ∥f a∥)) : summable f :=
summable_of_norm_bounded _ hf (assume i, le_refl _)

lemma norm_tsum_le_tsum_norm {f : ι → α} (hf : summable (λi, ∥f i∥)) : ∥(∑i, f i)∥ ≤ (∑ i, ∥f i∥) :=
have h₁ : tendsto (λs:finset ι, ∥s.sum f∥) at_top (nhds ∥(∑ i, f i)∥) :=
  (has_sum_tsum $ summable_of_summable_norm hf).comp (continuous_norm.tendsto _),
have h₂ : tendsto (λs:finset ι, s.sum (λi, ∥f i∥)) at_top (nhds (∑ i, ∥f i∥)) :=
  has_sum_tsum hf,
le_of_tendsto_of_tendsto at_top_ne_bot h₁ h₂ $ univ_mem_sets' $ assume s, norm_triangle_sum _ _

end summable

namespace complex

instance : normed_field ℂ :=
{ norm := complex.abs,
  dist_eq := λ _ _, rfl,
  norm_mul := complex.abs_mul,
  .. complex.discrete_field }

instance : nondiscrete_normed_field ℂ :=
{ non_trivial := ⟨2, by simp [norm]; norm_num⟩ }

@[simp] lemma norm_real (r : ℝ) : ∥(r : ℂ)∥ = ∥r∥ := complex.abs_of_real _

@[simp] lemma norm_rat (r : ℚ) : ∥(r : ℂ)∥ = _root_.abs (r : ℝ) :=
suffices ∥((r : ℝ) : ℂ)∥ = _root_.abs r, by simpa,
by rw [norm_real, real.norm_eq_abs]

@[simp] lemma norm_nat (n : ℕ) : ∥(n : ℂ)∥ = n := complex.abs_of_nat _

@[simp] lemma norm_int {n : ℤ} : ∥(n : ℂ)∥ = _root_.abs n :=
suffices ∥((n : ℝ) : ℂ)∥ = _root_.abs n, by simpa,
by rw [norm_real, real.norm_eq_abs]

lemma norm_int_of_nonneg {n : ℤ} (hn : n ≥ 0) : ∥(n : ℂ)∥ = n :=
by rw [norm_int, _root_.abs_of_nonneg]; exact int.cast_nonneg.2 hn

end complex
