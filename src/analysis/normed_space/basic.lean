/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import analysis.normed.normed_field
import analysis.normed.group.infinite_sum
import data.matrix.basic
import topology.sequences

/-!
# Normed spaces

In this file we define (semi)normed spaces and algebras. We also prove some theorems
about these definitions.
-/

variables {α : Type*} {β : Type*} {γ : Type*} {ι : Type*}

noncomputable theory
open filter metric
open_locale topological_space big_operators nnreal ennreal uniformity pointwise

section semi_normed_group

section prio
set_option extends_priority 920
-- Here, we set a rather high priority for the instance `[normed_space α β] : module α β`
-- to take precedence over `semiring.to_module` as this leads to instance paths with better
-- unification properties.
/-- A normed space over a normed field is a vector space endowed with a norm which satisfies the
equality `∥c • x∥ = ∥c∥ ∥x∥`. We require only `∥c • x∥ ≤ ∥c∥ ∥x∥` in the definition, then prove
`∥c • x∥ = ∥c∥ ∥x∥` in `norm_smul`.

Note that since this requires `semi_normed_group` and not `normed_group`, this typeclass can be
used for "semi normed spaces" too, just as `module` can be used for "semi modules". -/
class normed_space (α : Type*) (β : Type*) [normed_field α] [semi_normed_group β]
  extends module α β :=
(norm_smul_le : ∀ (a:α) (b:β), ∥a • b∥ ≤ ∥a∥ * ∥b∥)
end prio

variables [normed_field α] [semi_normed_group β]

@[priority 100] -- see Note [lower instance priority]
instance normed_space.has_bounded_smul [normed_space α β] : has_bounded_smul α β :=
{ dist_smul_pair' := λ x y₁ y₂,
    by simpa [dist_eq_norm, smul_sub] using normed_space.norm_smul_le x (y₁ - y₂),
  dist_pair_smul' := λ x₁ x₂ y,
    by simpa [dist_eq_norm, sub_smul] using normed_space.norm_smul_le (x₁ - x₂) y }

instance normed_field.to_normed_space : normed_space α α :=
{ norm_smul_le := λ a b, le_of_eq (norm_mul a b) }

lemma norm_smul [normed_space α β] (s : α) (x : β) : ∥s • x∥ = ∥s∥ * ∥x∥ :=
begin
  by_cases h : s = 0,
  { simp [h] },
  { refine le_antisymm (normed_space.norm_smul_le s x) _,
    calc ∥s∥ * ∥x∥ = ∥s∥ * ∥s⁻¹ • s • x∥     : by rw [inv_smul_smul₀ h]
               ... ≤ ∥s∥ * (∥s⁻¹∥ * ∥s • x∥) :
      mul_le_mul_of_nonneg_left (normed_space.norm_smul_le _ _) (norm_nonneg _)
               ... = ∥s • x∥                 :
      by rw [norm_inv, ← mul_assoc, mul_inv_cancel (mt norm_eq_zero.1 h), one_mul] }
end

@[simp] lemma abs_norm_eq_norm (z : β) : |∥z∥| = ∥z∥ :=
  (abs_eq (norm_nonneg z)).mpr (or.inl rfl)

lemma inv_norm_smul_mem_closed_unit_ball [normed_space ℝ β] (x : β) :
  ∥x∥⁻¹ • x ∈ closed_ball (0 : β) 1 :=
by simp only [mem_closed_ball_zero_iff, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul,
  div_self_le_one]

lemma dist_smul [normed_space α β] (s : α) (x y : β) : dist (s • x) (s • y) = ∥s∥ * dist x y :=
by simp only [dist_eq_norm, (norm_smul _ _).symm, smul_sub]

lemma nnnorm_smul [normed_space α β] (s : α) (x : β) : ∥s • x∥₊ = ∥s∥₊ * ∥x∥₊ :=
nnreal.eq $ norm_smul s x

lemma nndist_smul [normed_space α β] (s : α) (x y : β) :
  nndist (s • x) (s • y) = ∥s∥₊ * nndist x y :=
nnreal.eq $ dist_smul s x y

lemma lipschitz_with_smul [normed_space α β] (s : α) : lipschitz_with ∥s∥₊ ((•) s : β → β) :=
lipschitz_with_iff_dist_le_mul.2 $ λ x y, by rw [dist_smul, coe_nnnorm]

lemma norm_smul_of_nonneg [normed_space ℝ β] {t : ℝ} (ht : 0 ≤ t) (x : β) :
  ∥t • x∥ = t * ∥x∥ := by rw [norm_smul, real.norm_eq_abs, abs_of_nonneg ht]

variables {E : Type*} [semi_normed_group E] [normed_space α E]
variables {F : Type*} [semi_normed_group F] [normed_space α F]

theorem eventually_nhds_norm_smul_sub_lt (c : α) (x : E) {ε : ℝ} (h : 0 < ε) :
  ∀ᶠ y in 𝓝 x, ∥c • (y - x)∥ < ε :=
have tendsto (λ y, ∥c • (y - x)∥) (𝓝 x) (𝓝 0),
  from ((continuous_id.sub continuous_const).const_smul _).norm.tendsto' _ _ (by simp),
this.eventually (gt_mem_nhds h)

lemma filter.tendsto.zero_smul_is_bounded_under_le {f : ι → α} {g : ι → E} {l : filter ι}
  (hf : tendsto f l (𝓝 0)) (hg : is_bounded_under (≤) l (norm ∘ g)) :
  tendsto (λ x, f x • g x) l (𝓝 0) :=
hf.op_zero_is_bounded_under_le hg (•) (λ x y, (norm_smul x y).le)

lemma filter.is_bounded_under.smul_tendsto_zero {f : ι → α} {g : ι → E} {l : filter ι}
  (hf : is_bounded_under (≤) l (norm ∘ f)) (hg : tendsto g l (𝓝 0)) :
  tendsto (λ x, f x • g x) l (𝓝 0) :=
hg.op_zero_is_bounded_under_le hf (flip (•)) (λ x y, ((norm_smul y x).trans (mul_comm _ _)).le)

theorem closure_ball [normed_space ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
  closure (ball x r) = closed_ball x r :=
begin
  refine set.subset.antisymm closure_ball_subset_closed_ball (λ y hy, _),
  have : continuous_within_at (λ c : ℝ, c • (y - x) + x) (set.Ico 0 1) 1 :=
    ((continuous_id.smul continuous_const).add continuous_const).continuous_within_at,
  convert this.mem_closure _ _,
  { rw [one_smul, sub_add_cancel] },
  { simp [closure_Ico (@zero_ne_one ℝ _ _), zero_le_one] },
  { rintros c ⟨hc0, hc1⟩,
    rw [mem_ball, dist_eq_norm, add_sub_cancel, norm_smul, real.norm_eq_abs,
      abs_of_nonneg hc0, mul_comm, ← mul_one r],
    rw [mem_closed_ball, dist_eq_norm] at hy,
    replace hr : 0 < r, from ((norm_nonneg _).trans hy).lt_of_ne hr.symm,
    apply mul_lt_mul'; assumption }
end

theorem frontier_ball [normed_space ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
  frontier (ball x r) = sphere x r :=
begin
  rw [frontier, closure_ball x hr, is_open_ball.interior_eq],
  ext x, exact (@eq_iff_le_not_lt ℝ _ _ _).symm
end

theorem interior_closed_ball [normed_space ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
  interior (closed_ball x r) = ball x r :=
begin
  cases hr.lt_or_lt with hr hr,
  { rw [closed_ball_eq_empty.2 hr, ball_eq_empty.2 hr.le, interior_empty] },
  refine set.subset.antisymm _ ball_subset_interior_closed_ball,
  intros y hy,
  rcases (mem_closed_ball.1 $ interior_subset hy).lt_or_eq with hr|rfl, { exact hr },
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

theorem frontier_closed_ball [normed_space ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
  frontier (closed_ball x r) = sphere x r :=
by rw [frontier, closure_closed_ball, interior_closed_ball x hr,
  closed_ball_diff_ball]

/-- A (semi) normed real vector space is homeomorphic to the unit ball in the same space.
This homeomorphism sends `x : E` to `(1 + ∥x∥)⁻¹ • x`.

In many cases the actual implementation is not important, so we don't mark the projection lemmas
`homeomorph_unit_ball_apply_coe` and `homeomorph_unit_ball_symm_apply` as `@[simp]`. -/
@[simps { attrs := [] }]
def homeomorph_unit_ball {E : Type*} [semi_normed_group E] [normed_space ℝ E] :
  E ≃ₜ ball (0 : E) 1 :=
{ to_fun := λ x, ⟨(1 + ∥x∥)⁻¹ • x, begin
    have : ∥x∥ < |1 + ∥x∥| := (lt_one_add _).trans_le (le_abs_self _),
    rwa [mem_ball_zero_iff, norm_smul, real.norm_eq_abs, abs_inv, ← div_eq_inv_mul,
      div_lt_one ((norm_nonneg x).trans_lt this)],
  end⟩,
  inv_fun := λ x, (1 - ∥(x : E)∥)⁻¹ • (x : E),
  left_inv := λ x,
    begin
      have : 0 < 1 + ∥x∥ := (norm_nonneg x).trans_lt (lt_one_add _),
      field_simp [this.ne', abs_of_pos this, norm_smul, smul_smul, real.norm_eq_abs, abs_div]
    end,
  right_inv := λ x, subtype.ext
    begin
      have : 0 < 1 - ∥(x : E)∥ := sub_pos.2 (mem_ball_zero_iff.1 x.2),
      field_simp [norm_smul, smul_smul, real.norm_eq_abs, abs_div, abs_of_pos this, this.ne']
    end,
  continuous_to_fun := continuous_subtype_mk _ $
    ((continuous_const.add continuous_norm).inv₀
      (λ x, ((norm_nonneg x).trans_lt (lt_one_add _)).ne')).smul continuous_id,
  continuous_inv_fun := continuous.smul
    ((continuous_const.sub continuous_subtype_coe.norm).inv₀ $
      λ x, (sub_pos.2 $ mem_ball_zero_iff.1 x.2).ne') continuous_subtype_coe }

variables (α)

lemma ne_neg_of_mem_sphere [char_zero α] {r : ℝ} (hr : r ≠ 0) (x : sphere (0:E) r) : x ≠ - x :=
λ h, ne_zero_of_mem_sphere hr x ((self_eq_neg α _).mp (by { conv_lhs {rw h}, simp }))

lemma ne_neg_of_mem_unit_sphere [char_zero α] (x : sphere (0:E) 1) : x ≠ - x :=
ne_neg_of_mem_sphere α one_ne_zero x

variables {α}

open normed_field

/-- The product of two normed spaces is a normed space, with the sup norm. -/
instance prod.normed_space : normed_space α (E × F) :=
{ norm_smul_le := λ s x, le_of_eq $ by simp [prod.norm_def, norm_smul, mul_max_of_nonneg],
  ..prod.normed_group,
  ..prod.module }

/-- The product of finitely many normed spaces is a normed space, with the sup norm. -/
instance pi.normed_space {E : ι → Type*} [fintype ι] [∀i, semi_normed_group (E i)]
  [∀i, normed_space α (E i)] : normed_space α (Πi, E i) :=
{ norm_smul_le := λ a f, le_of_eq $
    show (↑(finset.sup finset.univ (λ (b : ι), ∥a • f b∥₊)) : ℝ) =
      ∥a∥₊ * ↑(finset.sup finset.univ (λ (b : ι), ∥f b∥₊)),
    by simp only [(nnreal.coe_mul _ _).symm, nnreal.mul_finset_sup, nnnorm_smul] }

/-- A subspace of a normed space is also a normed space, with the restriction of the norm. -/
instance submodule.normed_space {𝕜 R : Type*} [has_scalar 𝕜 R] [normed_field 𝕜] [ring R]
  {E : Type*} [semi_normed_group E] [normed_space 𝕜 E] [module R E]
  [is_scalar_tower 𝕜 R E] (s : submodule R E) :
  normed_space 𝕜 s :=
{ norm_smul_le := λc x, le_of_eq $ norm_smul c (x : E) }

/-- If there is a scalar `c` with `∥c∥>1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `∥c∥`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
lemma rescale_to_shell_semi_normed {c : α} (hc : 1 < ∥c∥) {ε : ℝ} (εpos : 0 < ε) {x : E}
  (hx : ∥x∥ ≠ 0) : ∃d:α, d ≠ 0 ∧ ∥d • x∥ < ε ∧ (ε/∥c∥ ≤ ∥d • x∥) ∧ (∥d∥⁻¹ ≤ ε⁻¹ * ∥c∥ * ∥x∥) :=
begin
  have xεpos : 0 < ∥x∥/ε := div_pos ((ne.symm hx).le_iff_lt.1 (norm_nonneg x)) εpos,
  rcases exists_mem_Ico_zpow xεpos hc with ⟨n, hn⟩,
  have cpos : 0 < ∥c∥ := lt_trans (zero_lt_one : (0 :ℝ) < 1) hc,
  have cnpos : 0 < ∥c^(n+1)∥ := by { rw norm_zpow, exact lt_trans xεpos hn.2 },
  refine ⟨(c^(n+1))⁻¹, _, _, _, _⟩,
  show (c ^ (n + 1))⁻¹  ≠ 0,
    by rwa [ne.def, inv_eq_zero, ← ne.def, ← norm_pos_iff],
  show ∥(c ^ (n + 1))⁻¹ • x∥ < ε,
  { rw [norm_smul, norm_inv, ← div_eq_inv_mul, div_lt_iff cnpos, mul_comm, norm_zpow],
    exact (div_lt_iff εpos).1 (hn.2) },
  show ε / ∥c∥ ≤ ∥(c ^ (n + 1))⁻¹ • x∥,
  { rw [div_le_iff cpos, norm_smul, norm_inv, norm_zpow, zpow_add₀ (ne_of_gt cpos),
        zpow_one, mul_inv_rev, mul_comm, ← mul_assoc, ← mul_assoc, mul_inv_cancel (ne_of_gt cpos),
        one_mul, ← div_eq_inv_mul, le_div_iff (zpow_pos_of_pos cpos _), mul_comm],
    exact (le_div_iff εpos).1 hn.1 },
  show ∥(c ^ (n + 1))⁻¹∥⁻¹ ≤ ε⁻¹ * ∥c∥ * ∥x∥,
  { have : ε⁻¹ * ∥c∥ * ∥x∥ = ε⁻¹ * ∥x∥ * ∥c∥, by ring,
    rw [norm_inv, inv_inv, norm_zpow, zpow_add₀ (ne_of_gt cpos), zpow_one, this, ← div_eq_inv_mul],
    exact mul_le_mul_of_nonneg_right hn.1 (norm_nonneg _) }
end

end semi_normed_group

section normed_group

variables [normed_field α]
variables {E : Type*} [normed_group E] [normed_space α E]
variables {F : Type*} [normed_group F] [normed_space α F]

open normed_field

/-- While this may appear identical to `normed_space.to_module`, it contains an implicit argument
involving `normed_group.to_semi_normed_group` that typeclass inference has trouble inferring.

Specifically, the following instance cannot be found without this `normed_space.to_module'`:
```lean
example
  (𝕜 ι : Type*) (E : ι → Type*)
  [normed_field 𝕜] [Π i, normed_group (E i)] [Π i, normed_space 𝕜 (E i)] :
  Π i, module 𝕜 (E i) := by apply_instance
```

[This Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclass.20resolution.20under.20binders/near/245151099)
gives some more context. -/
@[priority 100]
instance normed_space.to_module' : module α F := normed_space.to_module

theorem interior_closed_ball' [normed_space ℝ E] [nontrivial E] (x : E) (r : ℝ) :
  interior (closed_ball x r) = ball x r :=
begin
  rcases eq_or_ne r 0 with rfl|hr,
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

end normed_group

section normed_space_nondiscrete

variables (𝕜 E : Type*) [nondiscrete_normed_field 𝕜] [normed_group E] [normed_space 𝕜 E]
  [nontrivial E]

include 𝕜

/-- If `E` is a nontrivial normed space over a nondiscrete normed field `𝕜`, then `E` is unbounded:
for any `c : ℝ`, there exists a vector `x : E` with norm strictly greater than `c`. -/
lemma normed_space.exists_lt_norm (c : ℝ) : ∃ x : E, c < ∥x∥ :=
begin
  rcases exists_ne (0 : E) with ⟨x, hx⟩,
  rcases normed_field.exists_lt_norm 𝕜 (c / ∥x∥) with ⟨r, hr⟩,
  use r • x,
  rwa [norm_smul, ← div_lt_iff],
  rwa norm_pos_iff
end

protected lemma normed_space.unbounded_univ : ¬bounded (set.univ : set E) :=
λ h, let ⟨R, hR⟩ := bounded_iff_forall_norm_le.1 h, ⟨x, hx⟩ := normed_space.exists_lt_norm 𝕜 E R
in hx.not_le (hR x trivial)

/-- A normed vector space over a nondiscrete normed field is a noncompact space. This cannot be
an instance because in order to apply it, Lean would have to search for `normed_space 𝕜 E` with
unknown `𝕜`. We register this as an instance in two cases: `𝕜 = E` and `𝕜 = ℝ`. -/
protected lemma normed_space.noncompact_space : noncompact_space E :=
⟨λ h, normed_space.unbounded_univ 𝕜 _ h.bounded⟩

@[priority 100]
instance nondiscrete_normed_field.noncompact_space : noncompact_space 𝕜 :=
normed_space.noncompact_space 𝕜 𝕜

omit 𝕜

@[priority 100]
instance real_normed_space.noncompact_space [normed_space ℝ E] : noncompact_space E :=
normed_space.noncompact_space ℝ E

end normed_space_nondiscrete

section normed_algebra

/-- A normed algebra `𝕜'` over `𝕜` is normed module that is also an algebra.

See the implementation notes for `algebra` for a discussion about non-unital algebras. Following
the strategy there, a non-unital *normed* algebra can be written as:
```lean
variables [normed_field 𝕜] [non_unital_semi_normed_ring 𝕜']
variables [normed_module 𝕜 𝕜'] [smul_comm_class 𝕜 𝕜' 𝕜'] [is_scalar_tower 𝕜 𝕜' 𝕜']
```
-/
class normed_algebra (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜] [semi_normed_ring 𝕜']
  extends algebra 𝕜 𝕜' :=
(norm_smul_le : ∀ (r : 𝕜) (x : 𝕜'), ∥r • x∥ ≤ ∥r∥ * ∥x∥)

variables {𝕜 : Type*} (𝕜' : Type*) [normed_field 𝕜] [semi_normed_ring 𝕜'] [normed_algebra 𝕜 𝕜']

@[priority 100]
instance normed_algebra.to_normed_space : normed_space 𝕜 𝕜' :=
{ norm_smul_le := normed_algebra.norm_smul_le }

/-- While this may appear identical to `normed_algebra.to_normed_space`, it contains an implicit
argument involving `normed_ring.to_semi_normed_ring` that typeclass inference has trouble inferring.

Specifically, the following instance cannot be found without this `normed_space.to_module'`:
```lean
example
  (𝕜 ι : Type*) (E : ι → Type*)
  [normed_field 𝕜] [Π i, normed_ring (E i)] [Π i, normed_algebra 𝕜 (E i)] :
  Π i, module 𝕜 (E i) := by apply_instance
```

See `normed_space.to_module'` for a similar situation. -/
@[priority 100]
instance normed_algebra.to_normed_space' {𝕜'} [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] :
  normed_space 𝕜 𝕜' := by apply_instance

lemma norm_algebra_map (x : 𝕜) : ∥algebra_map 𝕜 𝕜' x∥ = ∥x∥ * ∥(1 : 𝕜')∥ :=
begin
  rw algebra.algebra_map_eq_smul_one,
  exact norm_smul _ _,
end

lemma nnnorm_algebra_map (x : 𝕜) : ∥algebra_map 𝕜 𝕜' x∥₊ = ∥x∥₊ * ∥(1 : 𝕜')∥₊ :=
subtype.ext $ norm_algebra_map 𝕜' x

@[simp] lemma norm_algebra_map' [norm_one_class 𝕜'] (x : 𝕜) : ∥algebra_map 𝕜 𝕜' x∥ = ∥x∥ :=
by rw [norm_algebra_map, norm_one, mul_one]

@[simp] lemma nnnorm_algebra_map' [norm_one_class 𝕜'] (x : 𝕜) : ∥algebra_map 𝕜 𝕜' x∥₊ = ∥x∥₊ :=
subtype.ext $ norm_algebra_map' _ _

variables (𝕜 𝕜')

/-- In a normed algebra, the inclusion of the base field in the extended field is an isometry. -/
lemma algebra_map_isometry [norm_one_class 𝕜'] : isometry (algebra_map 𝕜 𝕜') :=
begin
  refine isometry_emetric_iff_metric.2 (λx y, _),
  rw [dist_eq_norm, dist_eq_norm, ← ring_hom.map_sub, norm_algebra_map'],
end

/-- The inclusion of the base field in a normed algebra as a continuous linear map. -/
@[simps]
def algebra_map_clm : 𝕜 →L[𝕜] 𝕜' :=
{ to_fun := algebra_map 𝕜 𝕜',
  map_add' := (algebra_map 𝕜 𝕜').map_add,
  map_smul' := λ r x, by rw [algebra.id.smul_eq_mul, map_mul, ring_hom.id_apply, algebra.smul_def],
  cont :=
    have lipschitz_with ∥(1 : 𝕜')∥₊ (algebra_map 𝕜 𝕜') := λ x y, begin
      rw [edist_eq_coe_nnnorm_sub, edist_eq_coe_nnnorm_sub, ←map_sub, ←ennreal.coe_mul,
        ennreal.coe_le_coe, mul_comm],
      exact (nnnorm_algebra_map _ _).le,
    end, this.continuous }

lemma algebra_map_clm_coe :
  (algebra_map_clm 𝕜 𝕜' : 𝕜 → 𝕜') = (algebra_map 𝕜 𝕜' : 𝕜 → 𝕜') := rfl

lemma algebra_map_clm_to_linear_map :
  (algebra_map_clm 𝕜 𝕜').to_linear_map = algebra.linear_map 𝕜 𝕜' := rfl

instance normed_algebra.id : normed_algebra 𝕜 𝕜 :=
{ .. normed_field.to_normed_space,
  .. algebra.id 𝕜}

/-- Any normed characteristic-zero division ring that is a normed_algebra over the reals is also a
normed algebra over the rationals.

Phrased another way, if `𝕜` is a normed algebra over the reals, then `algebra_rat` respects that
norm. -/
instance normed_algebra_rat {𝕜} [normed_division_ring 𝕜] [char_zero 𝕜] [normed_algebra ℝ 𝕜] :
  normed_algebra ℚ 𝕜 :=
{ norm_smul_le := λ q x,
    by rw [←smul_one_smul ℝ q x, rat.smul_one_eq_coe, norm_smul, rat.norm_cast_real], }

instance punit.normed_algebra : normed_algebra 𝕜 punit :=
{ norm_smul_le := λ q x, by simp only [punit.norm_eq_zero, mul_zero] }

/-- The product of two normed algebras is a normed algebra, with the sup norm. -/
instance prod.normed_algebra {E F : Type*} [semi_normed_ring E] [semi_normed_ring F]
  [normed_algebra 𝕜 E] [normed_algebra 𝕜 F] :
  normed_algebra 𝕜 (E × F) :=
{ ..prod.normed_space }

/-- The product of finitely many normed algebras is a normed algebra, with the sup norm. -/
instance pi.normed_algebra {E : ι → Type*} [fintype ι]
  [Π i, semi_normed_ring (E i)] [Π i, normed_algebra 𝕜 (E i)] :
  normed_algebra 𝕜 (Π i, E i) :=
{ .. pi.normed_space,
  .. pi.algebra _ E }

end normed_algebra

section restrict_scalars

variables (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜] [normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
(E : Type*) [semi_normed_group E] [normed_space 𝕜' E]

instance {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [I : semi_normed_group E] :
  semi_normed_group (restrict_scalars 𝕜 𝕜' E) := I

instance {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [I : normed_group E] :
  normed_group (restrict_scalars 𝕜 𝕜' E) := I

/-- If `E` is a normed space over `𝕜'` and `𝕜` is a normed algebra over `𝕜'`, then
`restrict_scalars.module` is additionally a `normed_space`. -/
instance : normed_space 𝕜 (restrict_scalars 𝕜 𝕜' E) :=
{ norm_smul_le := λ c x, (normed_space.norm_smul_le (algebra_map 𝕜 𝕜' c) (_ : E)).trans_eq $
    by rw norm_algebra_map',
  ..restrict_scalars.module 𝕜 𝕜' E }

/--
The action of the original normed_field on `restrict_scalars 𝕜 𝕜' E`.
This is not an instance as it would be contrary to the purpose of `restrict_scalars`.
-/
-- If you think you need this, consider instead reproducing `restrict_scalars.lsmul`
-- appropriately modified here.
def module.restrict_scalars.normed_space_orig {𝕜 : Type*} {𝕜' : Type*} {E : Type*}
  [normed_field 𝕜'] [semi_normed_group E] [I : normed_space 𝕜' E] :
  normed_space 𝕜' (restrict_scalars 𝕜 𝕜' E) := I

/-- Warning: This declaration should be used judiciously.
Please consider using `is_scalar_tower` and/or `restrict_scalars 𝕜 𝕜' E` instead.

This definition allows the `restrict_scalars.normed_space` instance to be put directly on `E`
rather on `restrict_scalars 𝕜 𝕜' E`. This would be a very bad instance; both because `𝕜'` cannot be
inferred, and because it is likely to create instance diamonds.
-/
def normed_space.restrict_scalars : normed_space 𝕜 E :=
restrict_scalars.normed_space _ 𝕜' _

end restrict_scalars
