/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.calculus.specific_functions
import geometry.manifold.diffeomorph
import geometry.manifold.instances.real

/-!
# Smooth bump functions on a smooth manifold

In this file we define `smooth_bump_function I c` to be a bundled smooth "bump" function centered at
`c`. It is a structure that consists of two real numbers `0 < r < R` with small enough `R`. We
define a coercion to function for this type, and for `f : smooth_bump_function I c`, the function
`⇑f` written in the extended chart at `f.c` has the following properties:

* `f x = 1` in the closed euclidean ball of radius `f.r` centered at `f.c`;
* `f x = 0` outside of the euclidean ball of radius `f.R` centered at `f.c`;
* `0 ≤ f x ≤ 1` for all `x`.

The actual statements involve (pre)images under `ext_chart_at I f.c` and are given as lemmas in the
`smooth_bump_function` namespace.

We also define `smooth_bump_covering` of a set `s : set M` to be a collection of
`smooth_bump_function`s such that their supports is a locally finite family of sets, and for each
point `x ∈ s` there exists a bump function `f i` in the collection such that `f i =ᶠ[𝓝 x] 1`. This
structure is the main building block in the construction of a smooth partition of unity (see TODO),
and can be used instead of a partition of unity in some proofs.

We say that `f : smooth_bump_covering I s` is *subordinate* to a map `U : M → set M` if for each
index `i`, we have `closure (support (f i)) ⊆ U (f i).c`. This notion is a bit more general than
being subordinate to an open covering of `M`, because we make no assumption about the way `U x`
depends on `x`.

We prove that on a smooth finitely dimensional real manifold with `Σ`-countable Hausdorff topology,
for any `U : M → set M` such that `∀ x ∈ s, U x ∈ 𝓝 x` there exists a `smooth_bump_covering I s`
subordinate to `U`. Then we use this fact to prove a version of the Whitney embedding theorem: any
compact real manifold can be embedded into `ℝ^n` for large enough `n`.

## TODO

* Prove the weak Whitney embedding theorem. This requires a version of Sard's theorem: for a locally
  Lipschitz continuous map `f : ℝ^m → ℝ^n`, `m < n`, the range has Hausdorff dimension at most `m`,
  hence it has measure zero.

* Construct a smooth partition of unity. While we can do it now, the formulas will be much nicer if
  we wait for `finprod` and `finsum` coming in #6832.

* Deduce some corollaries from existence of a smooth partition of unity.

  - Prove that for any disjoint closed sets `s`, `t` there exists a smooth function `f` suth that
  `f` equals zero on `s` and `f` equals one on `t`.

  - Build a framework for to transfer local definitions to global using partition of unity and use
    it to define, e.g., the integral of a differential form over a manifold.

## Tags

manifold, smooth bump function, partition of unity, Whitney theorem
-/

universes uE uF uH uM
variables
{E : Type uE} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
{H : Type uH} [topological_space H] (I : model_with_corners ℝ E H)
{M : Type uM} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

open function filter finite_dimensional set
open_locale topological_space manifold classical filter big_operators

noncomputable theory

/-!
### Smooth bump function

In this section we define a structure for a bundled smooth bump function and prove its properties.
-/

/-- Given a smooth manifold modelled on a finite dimensional space `E`,
`f : smooth_bump_function I M` is a smooth function on `M` such that in the extended chart `e` at
`f.c`:

* `f x = 1` in the closed euclidean ball of radius `f.r` centered at `f.c`;
* `f x = 0` outside of the euclidean ball of radius `f.R` centered at `f.c`;
* `0 ≤ f x ≤ 1` for all `x`.

The structure contains data required to construct a function with these properties. The function is
available as `⇑f` or `f x`. Formal statements of the properties listed above involve some
(pre)images under `ext_chart_at I f.c` and are given as lemmas in the `msmooth_bump_function`
namespace. -/
structure smooth_bump_function (c : M) extends times_cont_diff_bump (ext_chart_at I c c) :=
(closed_ball_subset :
  (euclidean.closed_ball (ext_chart_at I c c) R) ∩ range I ⊆ (ext_chart_at I c).target)

variable {M}

namespace smooth_bump_function

open euclidean (renaming dist -> eudist)

variables {c : M} (f : smooth_bump_function I c) {x : M} {I}

instance : has_coe_to_fun (smooth_bump_function I c) :=
⟨_, λ f, indicator (chart_at H c).source (f.to_times_cont_diff_bump ∘ ext_chart_at I c)⟩

lemma coe_def :
  ⇑f = indicator (chart_at H c).source (f.to_times_cont_diff_bump ∘ ext_chart_at I c) :=
rfl

lemma R_pos : 0 < f.R := f.to_times_cont_diff_bump.R_pos

lemma ball_subset :
  ball (ext_chart_at I c c) f.R ∩ range I ⊆ (ext_chart_at I c).target :=
subset.trans (inter_subset_inter_left _ ball_subset_closed_ball) f.closed_ball_subset

lemma eq_on_source :
  eq_on f (f.to_times_cont_diff_bump ∘ ext_chart_at I c) (chart_at H c).source :=
eq_on_indicator

lemma eventually_eq_of_mem_source (hx : x ∈ (chart_at H c).source) :
  f =ᶠ[𝓝 x] f.to_times_cont_diff_bump ∘ ext_chart_at I c :=
f.eq_on_source.eventually_eq_of_mem $ mem_nhds_sets (chart_at H c).open_source hx

lemma one_of_dist_le (hs : x ∈ (chart_at H c).source)
  (hd : eudist (ext_chart_at I c x) (ext_chart_at I c c) ≤ f.r) :
  f x = 1 :=
by simp only [f.eq_on_source hs, (∘), f.to_times_cont_diff_bump.one_of_mem_closed_ball hd]

lemma support_eq_inter_preimage :
  support f =
    (chart_at H c).source ∩ (ext_chart_at I c ⁻¹' ball (ext_chart_at I c c) f.R) :=
by rw [coe_def, support_indicator, (∘), support_comp_eq_preimage, ← ext_chart_at_source I,
  ← (ext_chart_at I c).symm_image_target_inter_eq',
  ← (ext_chart_at I c).symm_image_target_inter_eq', f.to_times_cont_diff_bump.support_eq]

lemma support_eq_symm_image :
  support f = (ext_chart_at I c).symm '' (ball (ext_chart_at I c c) f.R ∩ range I) :=
begin
  rw [f.support_eq_inter_preimage, ← ext_chart_at_source I,
    ← (ext_chart_at I c).symm_image_target_inter_eq', inter_comm],
  congr' 1 with y,
  exact and.congr_right_iff.2
    (λ hy, ⟨λ h, ext_chart_at_target_subset_range _ _ h, λ h, f.ball_subset ⟨hy, h⟩⟩)
end

lemma support_subset_source : support f ⊆ (chart_at H c).source :=
by { rw [f.support_eq_inter_preimage, ← ext_chart_at_source I], exact inter_subset_left _ _ }

lemma mem_Icc : f x ∈ Icc (0 : ℝ) 1 :=
begin
  have : f x = 0 ∨ f x = _, from indicator_eq_zero_or_self _ _ _,
  cases this; rw this,
  exacts [left_mem_Icc.2 zero_le_one,
    ⟨f.to_times_cont_diff_bump.nonneg, f.to_times_cont_diff_bump.le_one⟩]
end

lemma nonneg : 0 ≤ f x := f.mem_Icc.1

lemma le_one : f x ≤ 1 := f.mem_Icc.2

lemma eventually_eq_one_of_dist_lt (hs : x ∈ (chart_at H c).source)
  (hd : eudist (ext_chart_at I c x) (ext_chart_at I c c) < f.r) :
  f =ᶠ[𝓝 x] 1 :=
begin
  filter_upwards [mem_nhds_sets (ext_chart_preimage_open_of_open I c is_open_ball) ⟨hs, hd⟩],
  rintro z ⟨hzs, hzd : _ < _⟩,
  exact f.one_of_dist_le hzs hzd.le
end

lemma eventually_eq_one : f =ᶠ[𝓝 c] 1 :=
f.eventually_eq_one_of_dist_lt (mem_chart_source _ _) $
by { rw [euclidean.dist, dist_self], exact f.r_pos }

@[simp] lemma eq_one : f c = 1 := f.eventually_eq_one.eq_of_nhds

lemma c_mem_support : c ∈ support f := by { rw [mem_support, f.eq_one], exact one_ne_zero }

lemma nonempty_support : (support f).nonempty := ⟨c, f.c_mem_support⟩

lemma compact_symm_image_closed_ball :
  is_compact ((ext_chart_at I c).symm '' (closed_ball (ext_chart_at I c c) f.R ∩ range I)) :=
(compact_ball.inter_right I.closed_range).image_of_continuous_on $
  (ext_chart_at_continuous_on_symm _ _).mono f.closed_ball_subset

variables [t2_space M]

lemma closed_symm_image_closed_ball :
  is_closed ((ext_chart_at I c).symm '' (closed_ball (ext_chart_at I c c) f.R ∩ range I)) :=
f.compact_symm_image_closed_ball.is_closed

lemma closure_support_subset_symm_image_closed_ball :
  closure (support f) ⊆
    (ext_chart_at I c).symm '' (closed_ball (ext_chart_at I c c) f.R ∩ range I) :=
begin
  rw support_eq_symm_image,
  exact closure_minimal (image_subset _ $ inter_subset_inter_left _ ball_subset_closed_ball)
    f.closed_symm_image_closed_ball
end

lemma closure_support_subset_ext_chart_at_source :
  closure (support f) ⊆ (ext_chart_at I c).source :=
calc closure (support f)
    ⊆ (ext_chart_at I c).symm '' (closed_ball (ext_chart_at I c c) f.R ∩ range I) :
  f.closure_support_subset_symm_image_closed_ball
... ⊆ (ext_chart_at I c).symm '' (ext_chart_at I c).target :
  image_subset _ f.closed_ball_subset
... = (ext_chart_at I c).source :
  (ext_chart_at I c).symm_image_target_eq_source

lemma closure_support_subset_chart_at_source :
  closure (support f) ⊆ (chart_at H c).source :=
by simpa only [ext_chart_at_source] using f.closure_support_subset_ext_chart_at_source

lemma compact_closure_support : is_compact (closure $ support f) :=
compact_of_is_closed_subset f.compact_symm_image_closed_ball is_closed_closure
 f.closure_support_subset_symm_image_closed_ball

variables [smooth_manifold_with_corners I M]

protected lemma smooth : smooth I 𝓘(ℝ) f :=
begin
  refine times_cont_mdiff_of_support (λ x hx, _),
  have : x ∈ (chart_at H c).source := f.closure_support_subset_chart_at_source hx,
  refine times_cont_mdiff_at.congr_of_eventually_eq _
    (f.eq_on_source.eventually_eq_of_mem $ mem_nhds_sets (chart_at _ _).open_source this),
  exact f.to_times_cont_diff_bump.times_cont_diff_at.times_cont_mdiff_at.comp _
    (times_cont_mdiff_at_ext_chart_at' this)
end

protected lemma smooth_at {x} : smooth_at I 𝓘(ℝ) f x := f.smooth.smooth_at

lemma smooth_smul {G} [normed_group G] [normed_space ℝ G]
  {g : M → G} (hg : smooth_on I 𝓘(ℝ, G) g (chart_at H c).source) :
  smooth I 𝓘(ℝ, G) (λ x, f x • g x) :=
begin
  apply times_cont_mdiff_of_support (λ x hx, _),
  have : x ∈ (chart_at H c).source,
  calc x ∈ closure (support (λ x, f x • g x)) : hx
     ... ⊆ closure (support f) : closure_mono (support_smul_subset_left _ _)
     ... ⊆ (chart_at _ c).source : f.closure_support_subset_chart_at_source,
  exact f.smooth_at.smul ((hg _ this).times_cont_mdiff_at $
    mem_nhds_sets (chart_at _ _).open_source this)
end

end smooth_bump_function

/-!
### Covering by supports of smooth bump functions

In this section we define `smooth_bump_covering I s` to be a collection of `smooth_bump_function`s
such that their supports is a locally finite family of sets and for each `x ∈ s` some function `f i`
from the collection is equal to `1` in a neighborhood of `x`. A covering of this type is useful to
construct a smooth partition of unity and can be used instead of a partition of unity in some
proofs.

We prove that on a smooth finitely dimensional real manifold with `Σ`-countable Hausdorff topology,
for any `U : M → set M` such that `∀ x ∈ s, U x ∈ 𝓝 x` there exists a `smooth_bump_covering I s`
subordinate to `U`. Then we use this fact to prove a version of the Whitney embedding theorem: any
compact real manifold can be embedded into `ℝ^n` for large enough `n`.
-/

/-- We say that a collection of `smooth_bump_function`s is a `smooth_bump_covering` of a set `s` if

* `(f i).c ∈ s` for all `i`;
* the family `λ i, support (f i)` is locally finite;
* for each point `x ∈ s` there exists `i` such that `f i =ᶠ[𝓝 x] 1`;
  in other words, `x` belongs to the interior of `{y | f i y = 1}`;

If `M` is a finite dimensional real manifold which is a sigma-compact Hausdorff topological space,
then a choice of `smooth_bump_covering` is available as `smooth_bump_covering.choice_set`, see also
`smooth_bump_covering.choice` for the case `s = univ` and
`smooth_bump_covering.exists_is_subordinate` for a lemma providing a covering subordinate to a given
`U : M → set M`.

This covering can be used, e.g., to construct a partition of unity and to prove the weak
Whitney embedding theorem. -/
structure smooth_bump_covering (s : set M) :=
(ι : Type uM)
(c : ι → M)
(to_fun : Π i, smooth_bump_function I (c i))
(c_mem' : ∀ i, c i ∈ s)
(locally_finite' : locally_finite (λ i, support (to_fun i)))
(eventually_eq_one' : ∀ x ∈ s, ∃ i, to_fun i =ᶠ[𝓝 x] 1)

namespace smooth_bump_covering

variables {s : set M} {U : M → set M} (f : smooth_bump_covering I s) {I}

instance : has_coe_to_fun (smooth_bump_covering I s) := ⟨_, to_fun⟩

/-- 
We say that `f : smooth_bump_covering I s` is *subordinate* to a map `U : M → set M` if for each
index `i`, we have `closure (support (f i)) ⊆ U (f i).c`. This notion is a bit more general than
being subordinate to an open covering of `M`, because we make no assumption about the way `U x`
depends on `x`.
-/
def is_subordinate {s : set M} (f : smooth_bump_covering I s) (U : M → set M) :=
∀ i, closure (support $ f i) ⊆ U (f.c i)

variable (I)

/-- Let `M` be a smooth manifold with corners modelled on a finite dimensional real vector space.
Suppose also that `M` is a Hausdorff `Σ`-compact topological space. Let `s` be a closed set
in `M` and `U : M → set M` be a collection of sets such that `U x ∈ 𝓝 x` for every `x ∈ s`.
Then there exists a smooth bump covering of `s` that is subordinate to `U`. -/
lemma exists_is_subordinate [t2_space M] [sigma_compact_space M] (hs : is_closed s)
  (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
  ∃ f : smooth_bump_covering I s, f.is_subordinate U :=
begin
  /- The proof is similar to the proof of `exists_locally_finite_subset_Union_ball_radius_lt`.
  This proof is longer because we need to move the properties and sets back and forth along
  extended charts at different points. -/
  -- First we deduce some missing instances
  haveI : locally_compact_space H := I.locally_compact,
  haveI : locally_compact_space M := charted_space.locally_compact H,
  haveI : normal_space M := normal_of_paracompact_t2,
  -- Then we introduce some notation
  set e : M → local_equiv M E := ext_chart_at I,
  set cBE : M → ℝ → set E := λ x r, euclidean.closed_ball (e x x) r ∩ range I,
  set cB : M → ℝ → set M := λ x r, (e x).symm '' cBE x r,
  set BE : M → ℝ → set E := λ x r, euclidean.ball (e x x) r ∩ range I,
  set B : M → ℝ → set M := λ x r, (e x).symm '' BE x r,
  have BEcBE : ∀ x r, BE x r ⊆ cBE x r,
    from λ x r, inter_subset_inter_left _ euclidean.ball_subset_closed_ball,
  have BcB : ∀ x r, B x r ⊆ cB x r, from λ x r, image_subset _ (BEcBE x r),
  have memB : ∀ x r, 0 < r → x ∈ B x r,
    from λ x r hr, ⟨e x x, ⟨euclidean.mem_ball_self hr, mem_range_self _⟩, ext_chart_at_to_inv _ _⟩,
  have B_eq : ∀ x r, cBE x r ⊆ (e x).target →
    B x r = (e x).source ∩ e x ⁻¹' euclidean.ball (e x x) r,
  { intros x r h,
    have : BE x r ⊆ (e x).target, from subset.trans (BEcBE x r) h,
    simp only [B],
    rw [← (e x).symm_image_target_inter_eq', inter_comm],
    congr' 1,
    refine subset.antisymm (subset_inter (inter_subset_left _ _) this)
      (inter_subset_inter_right _ (ext_chart_at_target_subset_range _ _)) },
  have Bo : ∀ x r, cBE x r ⊆ (e x).target → is_open (B x r),
  { intros x r h,
    rw B_eq _ _ h,
    exact ext_chart_preimage_open_of_open' _ _ euclidean.is_open_ball },
  /- Next we prove that the balls `B x r` such that `cB x r ⊆ U x` and `cBE x r ⊆ (e x).target`
  form a basis of the filter `𝓝 x`. -/
  have hcB : ∀ x ∈ s,
    (𝓝 x).has_basis (λ r : ℝ, 0 < r ∧ cBE x r ⊆ (e x).target ∧ cB x r ⊆ U x) (cB x),
  { intros x hx,
    simp only [← and.assoc],
    refine has_basis.restrict_subset _ (hU x hx),
    rw ← ext_chart_at_symm_map_nhds_within_range I x,
    exact ((nhds_within_has_basis euclidean.nhds_basis_closed_ball _).restrict_subset
      (ext_chart_at_target_mem_nhds_within _ _)).map _ },
  have hB : ∀ x ∈ s, (𝓝 x).has_basis (λ r : ℝ, 0 < r ∧ cBE x r ⊆ (e x).target ∧ cB x r ⊆ U x) (B x),
  { refine λ x hx, (hcB x hx).to_subset (λ r hr, BcB _ _) _,
    rintro r ⟨h0, hrE, hrU⟩,
    exact mem_nhds_sets (Bo _ _ hrE) (memB _ _ h0) },
  /- Then we use paracompactness of `M` to find a locally finite covering by the balls
  `B (c i) (R i)`. More precisely, we use lemma
  `refinement_of_locally_compact_sigma_compact_of_nhds_basis_set` which is a more precise
  version of “locally compact sigma compact space is paracompact”. -/
  rcases refinement_of_locally_compact_sigma_compact_of_nhds_basis_set hs hB
    with ⟨ι, c, R, hR, hsub', hfin⟩, choose hcs hR0 hcBER hcBR using hR,
  have Bio : ∀ i, is_open (B (c i) (R i)), from λ i, Bo _ _ (hcBER i),
  -- We introduce an auxiliary family of bump functions to use lemmas about them.
  set f' : Π i, smooth_bump_function I (c i) :=
    λ i, ⟨⟨⟨R i / 2, R i, half_pos (hR0 i), half_lt_self (hR0 i)⟩⟩, hcBER i⟩,
  have compact_cB : ∀ i, is_compact (cB (c i) (R i)),
    from λ i, (f' i).compact_symm_image_closed_ball,
  have Bsrc : ∀ i, B (c i) (R i) ⊆ (e (c i)).source,
    from λ i, (B_eq (c i) (R i) (hcBER i)).symm ▸ inter_subset_left _ _,
  /- Finally, we use the shrinking lemma to get a covering by smaller balls `B (c i) (r i)`,
  then use `c`, `r`, and `R` to construct the desired covering. -/
  choose V hsV hVo hVB
    using exists_subset_Union_closure_subset hs Bio (λ x hx, hfin.point_finite x) hsub',
  have hVcB : ∀ i, closure (V i) ⊆ cB (c i) (R i), from λ i, subset.trans (hVB i) (BcB _ _),
  have hVc : ∀ i, is_compact (closure (V i)),
    from λ i, compact_of_is_closed_subset
      (compact_cB i) is_closed_closure (hVcB i),
  have hVBE : ∀ i, closure (e (c i) '' V i) ⊆ BE (c i) (R i),
  { intro i,
    rw [← image_closure_of_compact (hVc i) ((ext_chart_at_continuous_on I (c i)).mono $
      subset.trans (hVB i) (Bsrc i)), image_subset_iff],
    refine subset.trans (hVB i) (λ x' hx', mem_preimage.2 _),
    rw B_eq (c i) (R i) (hcBER i) at hx',
    exact ⟨hx'.2, mem_range_self _⟩ },
  have : ∀ i, ∃ r ∈ Ioo 0 (R i), closure (e (c i) '' V i) ⊆ BE (c i) r,
  { intro i,
    rcases euclidean.exists_pos_lt_subset_ball (hR0 i) is_closed_closure
      (subset.trans (hVBE i) (inter_subset_left _ _)) with ⟨r, hIoo, hrV⟩,
    exact ⟨r, hIoo, subset_inter hrV (subset.trans (hVBE i) (inter_subset_right _ _))⟩ },
  choose r hlt hrV,
  set f : Π i, smooth_bump_function I (c i) := λ i, ⟨⟨⟨r i, R i, (hlt i).1, (hlt i).2⟩⟩, hcBER i⟩,
  refine ⟨⟨ι, c, f, hcs, _, λ x hx, _⟩, λ i, _⟩,
  { simpa only [(f _).support_eq_symm_image] },
  { refine (mem_Union.1 $ hsV hx).imp (λ i hi, _),
    refine mem_nhds_sets_iff.2 ⟨V i, λ x' hx', _, hVo i, hi⟩,
    simp only [ext_chart_at_source] at Bsrc,
    exact (f i).one_of_dist_le (Bsrc _ $ hVB _ $ subset_closure hx')
      (le_of_lt (hrV i (subset_closure $ mem_image_of_mem _ hx')).1) },
  { calc closure (support (f i)) ⊆ cB (c i) (R i) :
      (f i).closure_support_subset_symm_image_closed_ball
    ... ⊆ U (c i) : hcBR i }
end

/-- Choice of a covering of a closed set `s` by supports of smooth bump functions. -/
def choice_set [t2_space M] [sigma_compact_space M] (s : set M) (hs : is_closed s) :
  smooth_bump_covering I s :=
(exists_is_subordinate I hs (λ x hx, univ_mem_sets)).some

variable (M)

/-- Choice of a covering of a manifold by supports of smooth bump functions. -/
def choice [t2_space M] [sigma_compact_space M] :
  smooth_bump_covering I (univ : set M) :=
choice_set I univ is_closed_univ

variables {I M}

protected lemma locally_finite : locally_finite (λ i, support (f i)) := f.locally_finite'

protected lemma point_finite (x : M) : {i | f i x ≠ 0}.finite :=
f.locally_finite.point_finite x

lemma mem_chart_at_source_of_eq_one {i : f.ι} {x : M} (h : f i x = 1) :
  x ∈ (chart_at H (f.c i)).source :=
(f i).support_subset_source $ by simp [h]

lemma mem_ext_chart_at_source_of_eq_one {i : f.ι} {x : M} (h : f i x = 1) :
  x ∈ (ext_chart_at I (f.c i)).source :=
by { rw ext_chart_at_source, exact f.mem_chart_at_source_of_eq_one h }

/-- Index of a bump function such that `f i =ᶠ[𝓝 x] 1`. -/
def ind (x : M) (hx : x ∈ s) : f.ι := (f.eventually_eq_one' x hx).some

lemma eventually_eq_one (x : M) (hx : x ∈ s) : f (f.ind x hx) =ᶠ[𝓝 x] 1 :=
(f.eventually_eq_one' x hx).some_spec

lemma apply_ind (x : M) (hx : x ∈ s) : f (f.ind x hx) x = 1 :=
(f.eventually_eq_one x hx).eq_of_nhds

lemma mem_support_ind (x : M) (hx : x ∈ s) : x ∈ support (f $ f.ind x hx) :=
by simp [f.apply_ind x hx]

lemma mem_chart_at_ind_source (x : M) (hx : x ∈ s) :
  x ∈ (chart_at H (f.c (f.ind x hx))).source :=
f.mem_chart_at_source_of_eq_one (f.apply_ind x hx)

lemma mem_ext_chart_at_ind_source (x : M) (hx : x ∈ s) :
  x ∈ (ext_chart_at I (f.c (f.ind x hx))).source :=
f.mem_ext_chart_at_source_of_eq_one (f.apply_ind x hx)

section embedding

/-!
### Whitney embedding theorem

In this section we prove a version of the Whitney embedding theorem: for any compact real manifold
`M`, for sufficiently large `n` there exists a smooth embedding `M → ℝ^n`.
-/

instance fintype_ι_of_compact [compact_space M] : fintype f.ι :=
f.locally_finite.fintype_of_compact $ λ i, (f i).nonempty_support

variables [t2_space M] [fintype f.ι]

/-- Smooth embedding of `M` into `(E × ℝ) ^ f.ι`. -/
def embedding_pi_tangent : C^∞⟮I, M; 𝓘(ℝ, f.ι → (E × ℝ)), f.ι → (E × ℝ)⟯ :=
{ to_fun := λ x i, (f i x • ext_chart_at I (f.c i) x, f i x),
  times_cont_mdiff_to_fun := times_cont_mdiff_pi_space.2 $ λ i,
    ((f i).smooth_smul times_cont_mdiff_on_ext_chart_at).prod_mk_space ((f i).smooth) }

local attribute [simp] lemma embedding_pi_tangent_coe :
  ⇑f.embedding_pi_tangent = λ x i, (f i x • ext_chart_at I (f.c i) x, f i x) :=
rfl

lemma embedding_pi_tangent_inj_on : inj_on f.embedding_pi_tangent s :=
begin
  intros x hx y hy h,
  simp only [embedding_pi_tangent_coe, funext_iff] at h,
  obtain ⟨h₁, h₂⟩ := prod.mk.inj_iff.1 (h (f.ind x hx)),
  rw [f.apply_ind x hx] at h₂,
  rw [← h₂, f.apply_ind x hx, one_smul, one_smul] at h₁,
  have := f.mem_ext_chart_at_source_of_eq_one h₂.symm,
  exact (ext_chart_at I (f.c _)).inj_on (f.mem_ext_chart_at_ind_source x hx) this h₁
end

lemma embedding_pi_tangent_injective (f : smooth_bump_covering I (univ : set M))
  [fintype f.ι] :
  injective f.embedding_pi_tangent :=
injective_iff_inj_on_univ.2 f.embedding_pi_tangent_inj_on

lemma comp_embedding_pi_tangent_mfderiv (x : M) (hx : x ∈ s) :
  ((continuous_linear_map.fst ℝ E ℝ).comp
    (@continuous_linear_map.proj ℝ _ f.ι (λ _, E × ℝ) _ _ (λ _, infer_instance) (f.ind x hx))).comp
      (mfderiv I 𝓘(ℝ, f.ι → (E × ℝ)) f.embedding_pi_tangent x) =
  mfderiv I I (chart_at H (f.c (f.ind x hx))) x :=
begin
  set L := ((continuous_linear_map.fst ℝ E ℝ).comp
    (@continuous_linear_map.proj ℝ _ f.ι (λ _, E × ℝ) _ _ (λ _, infer_instance) (f.ind x hx))),
  have := (L.has_mfderiv_at.comp x (f.embedding_pi_tangent.mdifferentiable_at.has_mfderiv_at)),
  convert has_mfderiv_at_unique this _,
  refine (has_mfderiv_at_ext_chart_at I (f.mem_chart_at_ind_source x hx)).congr_of_eventually_eq _,
  refine (f.eventually_eq_one x hx).mono (λ y hy, _),
  simp only [embedding_pi_tangent_coe, continuous_linear_map.coe_comp', (∘),
    continuous_linear_map.coe_fst', continuous_linear_map.proj_apply],
  rw [hy, pi.one_apply, one_smul]
end

lemma embedding_pi_tangent_ker_mfderiv (x : M) (hx : x ∈ s) :
  (mfderiv I 𝓘(ℝ, f.ι → (E × ℝ)) f.embedding_pi_tangent x).ker = ⊥ :=
begin
  apply bot_unique,
  rw [← (mdifferentiable_chart I (f.c (f.ind x hx))).ker_mfderiv_eq_bot
    (f.mem_chart_at_ind_source x hx), ← comp_embedding_pi_tangent_mfderiv],
  exact linear_map.ker_le_ker_comp _ _
end

lemma embedding_pi_tangent_injective_mfderiv (x : M) (hx : x ∈ s) :
  injective (mfderiv I 𝓘(ℝ, f.ι → (E × ℝ)) f.embedding_pi_tangent x) :=
linear_map.ker_eq_bot.1 (f.embedding_pi_tangent_ker_mfderiv x hx)

end embedding

/-- Baby version of the Whitney weak embedding theorem: if `M` admits a finite covering by
supports of bump functions, then for some `n` it can be embedded into the `n`-dimensional
Euclidean space. -/
lemma exists_embedding_findim [t2_space M] (f : smooth_bump_covering I (univ : set M))
  [fintype f.ι] :
  ∃ (n : ℕ) (e : M → euclidean_space ℝ (fin n)), smooth I (𝓡 n) e ∧
    injective e ∧ ∀ x : M, injective (mfderiv I (𝓡 n) e x) :=
begin
  set F := euclidean_space ℝ (fin $ findim ℝ (f.ι → (E × ℝ))),
  letI : finite_dimensional ℝ (E × ℝ) := by apply_instance,
  set eEF : (f.ι → (E × ℝ)) ≃L[ℝ] F :=
    continuous_linear_equiv.of_findim_eq findim_euclidean_space_fin.symm,
  refine ⟨_, eEF ∘ f.embedding_pi_tangent,
    eEF.to_diffeomorph.smooth.comp f.embedding_pi_tangent.smooth,
    eEF.injective.comp f.embedding_pi_tangent_injective, λ x, _⟩,
  rw [mfderiv_comp _ eEF.differentiable_at.mdifferentiable_at
    f.embedding_pi_tangent.mdifferentiable_at, eEF.mfderiv_eq],
  exact eEF.injective.comp (f.embedding_pi_tangent_injective_mfderiv _ trivial)
end

end smooth_bump_covering

/-- Baby version of the Whitney weak embedding theorem: if `M` admits a finite covering by
supports of bump functions, then for some `n` it can be embedded into the `n`-dimensional
Euclidean space. -/
lemma exists_embedding_findim_of_compact [t2_space M] [compact_space M] :
  ∃ (n : ℕ) (e : M → euclidean_space ℝ (fin n)), smooth I (𝓡 n) e ∧
    injective e ∧ ∀ x : M, injective (mfderiv I (𝓡 n) e x) :=
(smooth_bump_covering.choice I M).exists_embedding_findim
