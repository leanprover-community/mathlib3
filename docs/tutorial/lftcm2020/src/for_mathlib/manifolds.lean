/- Missing bits that should be added to mathlib after the workshop and after cleaning them up -/

import geometry.manifold.times_cont_mdiff
import geometry.manifold.real_instances

open set

open_locale big_operators

instance : has_zero (Icc (0 : ℝ) 1) := ⟨⟨(0 : ℝ), ⟨le_refl _, zero_le_one⟩⟩⟩
instance : has_one (Icc (0 : ℝ) 1) := ⟨⟨(1 : ℝ), ⟨zero_le_one, le_refl _⟩⟩⟩

@[simp] lemma homeomorph_mk_coe {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  (a : equiv α β) (b c) : ((homeomorph.mk a b c) : α → β) = a :=
rfl

@[simp] lemma homeomorph_mk_coe_symm {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  (a : equiv α β) (b c) : ((homeomorph.mk a b c).symm : β → α) = a.symm :=
rfl

namespace metric

lemma is_closed_sphere {α : Type*} [metric_space α] {x : α} {r : ℝ} :
  is_closed (sphere x r) :=
is_closed_eq (continuous_id.dist continuous_const) continuous_const

end metric

section fderiv_id

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]

lemma fderiv_id' {x : E} : fderiv 𝕜 (λ (x : E), x) x = continuous_linear_map.id 𝕜 E :=
fderiv_id

end fderiv_id

section times_cont_diff_sum

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [normed_group G] [normed_space 𝕜 G]
{ι : Type*} {f : ι → E → F} {s : finset ι} {n : with_top ℕ} {t : set E} {x : E}

/- When adding it to mathlib, make `x` explicit in times_cont_diff_within_at.comp -/

/-- The sum of two `C^n`functions on a domain is `C^n`. -/
lemma times_cont_diff_within_at.add {n : with_top ℕ} {s : set E} {f g : E → F}
  (hf : times_cont_diff_within_at 𝕜 n f s x) (hg : times_cont_diff_within_at 𝕜 n g s x) :
  times_cont_diff_within_at 𝕜 n (λx, f x + g x) s x :=
begin
  have A : times_cont_diff 𝕜 n (λp : F × F, p.1 + p.2),
  { apply is_bounded_linear_map.times_cont_diff,
    exact is_bounded_linear_map.add is_bounded_linear_map.fst is_bounded_linear_map.snd },
  have B : times_cont_diff_within_at 𝕜 n (λp : F × F, p.1 + p.2) univ (prod.mk (f x) (g x)) :=
    A.times_cont_diff_at.times_cont_diff_within_at,
  exact @times_cont_diff_within_at.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x B (hf.prod hg) (subset_preimage_univ),
end

/-- The sum of two `C^n`functions on a domain is `C^n`. -/
lemma times_cont_diff_at.add {n : with_top ℕ} {f g : E → F}
  (hf : times_cont_diff_at 𝕜 n f x) (hg : times_cont_diff_at 𝕜 n g x) :
  times_cont_diff_at 𝕜 n (λx, f x + g x) x :=
begin
  simp [← times_cont_diff_within_at_univ] at *,
  exact hf.add hg
end

lemma times_cont_diff_within_at.sum (h : ∀ i ∈ s, times_cont_diff_within_at 𝕜 n (λ x, f i x) t x) :
  times_cont_diff_within_at 𝕜 n (λ x, (∑ i in s, f i x)) t x :=
begin
  classical,
  induction s using finset.induction_on with i s is IH,
  { simp [times_cont_diff_within_at_const] },
  { simp only [is, finset.sum_insert, not_false_iff],
    exact (h _ (finset.mem_insert_self i s)).add (IH (λ j hj, h _ (finset.mem_insert_of_mem hj))) }
end

lemma times_cont_diff_at.sum (h : ∀ i ∈ s, times_cont_diff_at 𝕜 n (λ x, f i x) x) :
  times_cont_diff_at 𝕜 n (λ x, (∑ i in s, f i x)) x :=
begin
  simp [← times_cont_diff_within_at_univ] at *,
  exact times_cont_diff_within_at.sum h
end

lemma times_cont_diff_on.sum (h : ∀ i ∈ s, times_cont_diff_on 𝕜 n (λ x, f i x) t) :
  times_cont_diff_on 𝕜 n (λ x, (∑ i in s, f i x)) t :=
λ x hx, times_cont_diff_within_at.sum (λ i hi, h i hi x hx)

lemma times_cont_diff.sum (h : ∀ i ∈ s, times_cont_diff 𝕜 n (λ x, f i x)) :
  times_cont_diff 𝕜 n (λ x, (∑ i in s, f i x)) :=
begin
  simp [← times_cont_diff_on_univ] at *,
  exact times_cont_diff_on.sum h
end

lemma times_cont_diff.comp_times_cont_diff_within_at {g : F → G} {f : E → F} (h : times_cont_diff 𝕜 n g)
  (hf : times_cont_diff_within_at 𝕜 n f t x) :
  times_cont_diff_within_at 𝕜 n (g ∘ f) t x :=
begin
  have : times_cont_diff_within_at 𝕜 n g univ (f x) :=
    h.times_cont_diff_at.times_cont_diff_within_at,
  exact this.comp hf (subset_univ _),
end

end times_cont_diff_sum

section pi_Lp_smooth

variables
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {ι : Type*} [fintype ι]
  {p : ℝ} {hp : 1 ≤ p} {α : ι → Type*} {n : with_top ℕ} (i : ι)
  [∀i, normed_group (α i)] [∀i, normed_space 𝕜 (α i)]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] {f : E → pi_Lp p hp α} {s : set E} {x : E}

lemma pi_Lp.norm_coord_le_norm (x : pi_Lp p hp α) (i : ι) : ∥x i∥ ≤ ∥x∥ :=
calc
  ∥x i∥ ≤ (∥x i∥ ^ p) ^ (1/p) :
  begin
    have : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp),
    rw [← real.rpow_mul (norm_nonneg _), mul_one_div_cancel this, real.rpow_one],
  end
  ... ≤ _ :
  begin
    have A : ∀ j, 0 ≤ ∥x j∥ ^ p := λ j, real.rpow_nonneg_of_nonneg (norm_nonneg _) _,
    simp only [pi_Lp.norm_eq, one_mul, linear_map.coe_mk],
    apply real.rpow_le_rpow (A i),
    { exact finset.single_le_sum (λ j hj, A j) (finset.mem_univ _) },
    { exact div_nonneg zero_le_one (lt_of_lt_of_le zero_lt_one hp) }
  end

lemma pi_Lp.times_cont_diff_coord :
  times_cont_diff 𝕜 n (λ x : pi_Lp p hp α, x i) :=
let F : pi_Lp p hp α →ₗ[𝕜] α i :=
{ to_fun := λ x, x i, map_add' := λ x y, rfl, map_smul' := λ x c, rfl } in
(F.mk_continuous 1 (λ x, by simpa using pi_Lp.norm_coord_le_norm x i)).times_cont_diff

lemma pi_Lp.times_cont_diff_within_at_iff_coord :
  times_cont_diff_within_at 𝕜 n f s x ↔ ∀ i, times_cont_diff_within_at 𝕜 n (λ x, (f x) i) s x:=
begin
  classical,
  split,
  { assume h i,
   exact (pi_Lp.times_cont_diff_coord i).comp_times_cont_diff_within_at h, },
  { assume h,
    let F : Π (i : ι), α i →ₗ[𝕜] pi_Lp p hp α := λ i,
    { to_fun := λ y, function.update 0 i y,
      map_add' := begin
        assume y y',
        ext j,
        by_cases h : j = i,
        { rw h, simp },
        { simp [h], }
      end,
      map_smul' := begin
        assume c x,
        ext j,
        by_cases h : j = i,
        { rw h, simp },
        { simp [h], }
      end },
    let G : Π (i : ι), α i →L[𝕜] pi_Lp p hp α := λ i,
    begin
      have p_ne_0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp),
      refine (F i).mk_continuous 1 (λ x, _),
      have : (λ j, ∥function.update 0 i x j∥ ^ p) = (λ j, if j = i then ∥x∥ ^ p else 0),
      { ext j,
        by_cases h : j = i,
        { rw h, simp },
        { simp [h, p_ne_0] } },
      simp only [pi_Lp.norm_eq, this, one_mul, finset.mem_univ, if_true, linear_map.coe_mk, finset.sum_ite_eq'],
      rw [← real.rpow_mul (norm_nonneg _), mul_one_div_cancel p_ne_0, real.rpow_one]
    end,
    have : times_cont_diff_within_at 𝕜 n (λ x, (∑ (i : ι), G i ((f x) i))) s x,
    { apply times_cont_diff_within_at.sum (λ i hi, _),
      exact (G i).times_cont_diff.comp_times_cont_diff_within_at (h i) },
    convert this,
    ext x j,
    simp,
    change f x j = (∑ (i : ι), function.update 0 i (f x i)) j,
    rw finset.sum_apply,
    have : ∀ i, function.update 0 i (f x i) j = (if j = i then f x j else 0),
    { assume i,
      by_cases h : j = i,
      { rw h, simp },
      { simp [h] } },
    simp [this] }
end

lemma pi_Lp.times_cont_diff_at_iff_coord :
  times_cont_diff_at 𝕜 n f x ↔ ∀ i, times_cont_diff_at 𝕜 n (λ x, (f x) i) x :=
by simp [← times_cont_diff_within_at_univ, pi_Lp.times_cont_diff_within_at_iff_coord]

lemma pi_Lp.times_cont_diff_on_iff_coord :
  times_cont_diff_on 𝕜 n f s ↔ ∀ i, times_cont_diff_on 𝕜 n (λ x, (f x) i) s :=
by { simp_rw [times_cont_diff_on, pi_Lp.times_cont_diff_within_at_iff_coord], tauto }

lemma pi_Lp.times_cont_diff_iff_coord :
  times_cont_diff 𝕜 n f ↔ ∀ i, times_cont_diff 𝕜 n (λ x, (f x) i) :=
by simp [← times_cont_diff_on_univ, pi_Lp.times_cont_diff_on_iff_coord]

end pi_Lp_smooth

lemma inducing.continuous_on_iff
  {α : Type*} {β : Type*} {γ : Type*}
  [topological_space α] [topological_space β] [topological_space γ]
  {f : α → β} {g : β → γ} (hg : inducing g) {s : set α} :
  continuous_on f s ↔ continuous_on (g ∘ f) s :=
begin
  simp only [continuous_on_iff_continuous_restrict, restrict_eq],
  conv_rhs { rw [function.comp.assoc, ← (inducing.continuous_iff hg)] },
end

lemma embedding.continuous_on_iff
  {α : Type*} {β : Type*} {γ : Type*}
  [topological_space α] [topological_space β] [topological_space γ]
  {f : α → β} {g : β → γ} (hg : embedding g) {s : set α} :
  continuous_on f s ↔ continuous_on (g ∘ f) s :=
inducing.continuous_on_iff hg.1

section tangent_map

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{s : set M} {x : M}
variables {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

@[simp, mfld_simps] lemma tangent_map_id : tangent_map I I (id : M → M) = id :=
by { ext1 p, simp [tangent_map] }

lemma tangent_map_within_id {p : tangent_bundle I M}
  (hs : unique_mdiff_within_at I s (tangent_bundle.proj I M p)) :
  tangent_map_within I I (id : M → M) s p = p :=
begin
  simp only [tangent_map_within, id.def],
  rw mfderiv_within_id,
  { rcases p, refl },
  { exact hs }
end

lemma mfderiv_within_congr {f f₁ : M → M'} (hs : unique_mdiff_within_at I s x)
  (hL : ∀ x ∈ s, f₁ x = f x) (hx : f₁ x = f x) :
  mfderiv_within I I' f₁ s x = (mfderiv_within I I' f s x : _) :=
filter.eventually_eq.mfderiv_within_eq hs (filter.eventually_eq_of_mem (self_mem_nhds_within) hL) hx

lemma tangent_map_within_congr {f g : M → M'} {s : set M}
  (h : ∀ x ∈ s, f x = g x)
  (p : tangent_bundle I M) (hp : p.1 ∈ s) (hs : unique_mdiff_within_at I s p.1) :
  tangent_map_within I I' f s p = tangent_map_within I I' g s p :=
begin
  simp only [tangent_map_within, h p.fst hp, true_and, prod.mk.inj_iff, eq_self_iff_true],
  congr' 1,
  exact mfderiv_within_congr hs h (h _ hp)
end

end tangent_map
