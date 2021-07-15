/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import geometry.manifold.bump_function

/-!
# Smooth partition of unity

In this file we define `smooth_bump_covering`, a structure that will be used to construct a smooth
partition of unity. Namely, a `smooth_bump_covering` of a set `s : set M` is a collection of
`smooth_bump_function`s such that their supports is a locally finite family of sets, and for each
point `x ∈ s` there exists a bump function `f i` in the collection such that `f i =ᶠ[𝓝 x] 1`. This
structure is the main building block in the construction of a smooth partition of unity (see TODO),
and can be used instead of a partition of unity in some proofs.

We say that `f : smooth_bump_covering I s` is *subordinate* to a map `U : M → set M` if for each
index `i`, we have `closure (support (f i)) ⊆ U (f i).c`. This notion is a bit more general than
being subordinate to an open covering of `M`, because we make no assumption about the way `U x`
depends on `x`.

We prove that on a smooth finitely dimensional real manifold with `σ`-compact Hausdorff topology,
for any `U : M → set M` such that `∀ x ∈ s, U x ∈ 𝓝 x` there exists a `smooth_bump_covering I s`
subordinate to `U`.

## TODO

* Construct a smooth partition of unity.

* Deduce some corollaries from existence of a smooth partition of unity.

  - Prove that for any disjoint closed sets `s`, `t` there exists a smooth function `f` suth that
  `f` equals zero on `s` and `f` equals one on `t`.

  - Build a framework for to transfer local definitions to global using partition of unity and use
    it to define, e.g., the integral of a differential form over a manifold.

## Tags

manifold, smooth bump function, partition of unity
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
### Covering by supports of smooth bump functions

In this section we define `smooth_bump_covering I s` to be a collection of `smooth_bump_function`s
such that their supports is a locally finite family of sets and for each `x ∈ s` some function `f i`
from the collection is equal to `1` in a neighborhood of `x`. A covering of this type is useful to
construct a smooth partition of unity and can be used instead of a partition of unity in some
proofs.

We prove that on a smooth finite dimensional real manifold with `σ`-compact Hausdorff topology,
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

variables {s : set M} {U : M → set M} (fs : smooth_bump_covering I s) {I}

instance : has_coe_to_fun (smooth_bump_covering I s) := ⟨_, to_fun⟩

@[simp] lemma coe_mk (ι : Type uM) (c : ι → M) (to_fun : Π i, smooth_bump_function I (c i))
  (h₁ h₂ h₃) : ⇑(mk ι c to_fun h₁ h₂ h₃ : smooth_bump_covering I s) = to_fun :=
rfl

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
Suppose also that `M` is a Hausdorff `σ`-compact topological space. Let `s` be a closed set
in `M` and `U : M → set M` be a collection of sets such that `U x ∈ 𝓝 x` for every `x ∈ s`.
Then there exists a smooth bump covering of `s` that is subordinate to `U`. -/
lemma exists_is_subordinate [t2_space M] [sigma_compact_space M] (hs : is_closed s)
  (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
  ∃ f : smooth_bump_covering I s, f.is_subordinate U :=
begin
  -- First we deduce some missing instances
  haveI : locally_compact_space H := I.locally_compact,
  haveI : locally_compact_space M := charted_space.locally_compact H,
  haveI : normal_space M := normal_of_paracompact_t2,
  -- Next we choose a covering by supports of smooth bump functions
  have hB := λ x hx, smooth_bump_function.nhds_basis_support I (hU x hx),
  rcases refinement_of_locally_compact_sigma_compact_of_nhds_basis_set hs hB
    with ⟨ι, c, f, hf, hsub', hfin⟩, choose hcs hfU using hf,
  /- Then we use the shrinking lemma to get a covering by smaller open -/
  rcases exists_subset_Union_closed_subset hs (λ i, (f i).open_support)
    (λ x hx, hfin.point_finite x) hsub' with ⟨V, hsV, hVc, hVf⟩,
  choose r hrR hr using λ i, (f i).exists_r_pos_lt_subset_ball (hVc i) (hVf i),
  refine ⟨⟨ι, c, λ i, (f i).update_r (r i) (hrR i), hcs, _, λ x hx, _⟩, λ i, _⟩,
  { simpa only [smooth_bump_function.support_update_r] },
  { refine (mem_Union.1 $ hsV hx).imp (λ i hi, _),
    exact ((f i).update_r _ _).eventually_eq_one_of_dist_lt
      ((f i).support_subset_source $ hVf _ hi) (hr i hi).2 },
  { simpa only [coe_mk, smooth_bump_function.support_update_r] using hfU i }
end

/-- Choice of a covering of a closed set `s` by supports of smooth bump functions. -/
def choice_set [t2_space M] [sigma_compact_space M] (s : set M) (hs : is_closed s) :
  smooth_bump_covering I s :=
(exists_is_subordinate I hs (λ x hx, univ_mem_sets)).some

instance [t2_space M] [sigma_compact_space M] {s : set M} [is_closed s] :
  inhabited (smooth_bump_covering I s) :=
⟨choice_set I s ‹_›⟩

variable (M)

/-- Choice of a covering of a manifold by supports of smooth bump functions. -/
def choice [t2_space M] [sigma_compact_space M] :
  smooth_bump_covering I (univ : set M) :=
choice_set I univ is_closed_univ

variables {I M}

protected lemma locally_finite : locally_finite (λ i, support (fs i)) := fs.locally_finite'

protected lemma point_finite (x : M) : {i | fs i x ≠ 0}.finite :=
fs.locally_finite.point_finite x

lemma mem_chart_at_source_of_eq_one {i : fs.ι} {x : M} (h : fs i x = 1) :
  x ∈ (chart_at H (fs.c i)).source :=
(fs i).support_subset_source $ by simp [h]

lemma mem_ext_chart_at_source_of_eq_one {i : fs.ι} {x : M} (h : fs i x = 1) :
  x ∈ (ext_chart_at I (fs.c i)).source :=
by { rw ext_chart_at_source, exact fs.mem_chart_at_source_of_eq_one h }

/-- Index of a bump function such that `fs i =ᶠ[𝓝 x] 1`. -/
def ind (x : M) (hx : x ∈ s) : fs.ι := (fs.eventually_eq_one' x hx).some

lemma eventually_eq_one (x : M) (hx : x ∈ s) : fs (fs.ind x hx) =ᶠ[𝓝 x] 1 :=
(fs.eventually_eq_one' x hx).some_spec

lemma apply_ind (x : M) (hx : x ∈ s) : fs (fs.ind x hx) x = 1 :=
(fs.eventually_eq_one x hx).eq_of_nhds

lemma mem_support_ind (x : M) (hx : x ∈ s) : x ∈ support (fs $ fs.ind x hx) :=
by simp [fs.apply_ind x hx]

lemma mem_chart_at_ind_source (x : M) (hx : x ∈ s) :
  x ∈ (chart_at H (fs.c (fs.ind x hx))).source :=
fs.mem_chart_at_source_of_eq_one (fs.apply_ind x hx)

lemma mem_ext_chart_at_ind_source (x : M) (hx : x ∈ s) :
  x ∈ (ext_chart_at I (fs.c (fs.ind x hx))).source :=
fs.mem_ext_chart_at_source_of_eq_one (fs.apply_ind x hx)

instance fintype_ι_of_compact [compact_space M] : fintype fs.ι :=
fs.locally_finite.fintype_of_compact $ λ i, (fs i).nonempty_support

end smooth_bump_covering
