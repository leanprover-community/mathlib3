/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.calculus.times_cont_diff geometry.manifold.manifold linear_algebra.finite_dimensional

/-!
# Smooth manifolds (possibly with boundary or corners)

A smooth manifold is a manifold modelled on a normed vector space, or a subset like a
half-space (to get manifolds with boundaries) for which the change of coordinates are smooth maps.
We define the groupoid of smooth maps (with regularity n : with_top ℕ), and then define smooth
manifolds as manifolds for which the changes of coordinates are C^∞.

## Main definitions

`model_with_corners 𝕜 E H` :
          a structure containing informations on the way a space H embeds in a
          model vector space E over the field 𝕜. This is all that is needed to
          define a smooth manifold with model space H, and model vector space E.
`model_with_corners_self 𝕜 E` :
          trivial model with corners structure on the space E embedded in itself by the identity.
`times_cont_diff_groupoid n I` :
          when I is a model with corners on (𝕜, E, H), this is the groupoid of local homeos of H
          which are of class C^n over the normed field 𝕜, when read in E.
`smooth_manifold_with_corners I M` :
          a type class saying that the manifold M, modelled on the space H, has C^∞ changes of
          coordinates with respect to the model with corners I on (𝕜, E, H). This type class is just
          a shortcut for `has_groupoid M (times_cont_diff_groupoid ⊤ I)`

As a specific example of a model with corners, we define
`model_with_corners ℝ (euclidean_space n) (euclidean_half_space n)` for the model space used
to define `n`-dimensional real manifolds with boundary.

To invoke an `n`-dimensional real manifold one could use

  `variables {n : ℕ} {M : Type*} [topological_space M] [manifold (euclidean_space n)]
   [smooth_manifold_with_corners (model_with_corners_self ℝ (euclidean_space n)) M]`.

However, this is not the recommended way: a theorem proved using this assumption would not apply
for instance to the tangent space of such a manifold, which is modelled on
`(euclidean_space n) × (euclidean_space n)` and not on `euclidean_space (2 * n)`! In the same way,
it would not apply to product manifolds, modelled on `(euclidean_space n) × (euclidean_space m)`.
The right invocation does not focus on one specific construction, but on all constructions sharing
the right properties, like

  `variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {I : model_with_corners ℝ E E} [I.boundaryless]
  {M : Type*} [topological_space M] [manifold E M] [smooth_manifold_with_corners I M]`

Here, `I.boundaryless` is a typeclass property ensuring that there is no boundary (this is for
instance the case for model_with_corners_self, or products of these). Note that one could consider
as a natural assumption to only use the trivial model with corners `model_with_corners_self ℝ E`,
but again in product manifolds the natural model with corners will not be this one but the product
one (and they are not defeq as (λp : E × F, (p.1, p.2)) is not defeq to the identity). So, it is
important to use the above incantation to maximize the applicability of theorems.

## Implementation notes

We want to talk about manifolds modelled on a vector space, but also on manifolds with
boundary, modelled on a half space (or even manifolds with corners). For the latter examples,
we still want to define smooth functions, tangent bundles, and so on. As smooth functions are
well defined on vector spaces or subsets of these, one could take for model space a subtype of a
vector space. With the drawback that the whole vector space itself (which is the most basic
example) is not directly a subtype of itself: the inclusion of `univ : set E` in `set E` would
show up in the definition, instead of `id`.

A good abstraction covering both cases it to have a vector
space E (with basic example the Euclidean space), a model space H (with basic example the upper half
space), and an embedding of H into E (which can be the identity for H = E, or
subtype.val for manifolds with corners). We say that the pair (E, H) with their embedding is a model
with corners, and we encompass all the relevant properties (in particular the fact that the image of
H in E should have unique differentials) in the definition of `model_with_corners`.

We concentrate on C^∞ manifolds: all the definitions work equally well for C^n manifolds, but later
on it is a pain to carry all over the smoothness parameter, especially when one wants to deal with
C^k functions as there would be additional conditions k ≤ n everywhere. Since one deals almost all
the time with C^∞ (or analytic) manifolds, this seems to be a reasonable choice that one could
revisit later if needed. C^k manifolds are still available, but they should be called using
`has_groupoid M (times_cont_diff_groupoid k I)` where `I` is the model with corners.

I have considered using the model with corners `I` as a typeclass argument, possibly out_param, to
get lighter notations later on, but it did not turn out right, as on `E × F` there are two natural
model with corners, the trivial (identity) one, and the product one, and they are not defeq and one
needs to indicate to Lean which one we want to use.
This means that when talking on objects on manifolds one will most often need to specify the model
with corners one is using. For instance, the tangent bundle will be `tangent_bundle I M` and the
derivative will be `mfderiv I I' f`, instead of the more natural notations `tangent_bundle 𝕜 M` and
`mfderiv 𝕜 f` (the field has to be explicit anyway, as some manifolds could be considered both as
real and complex manifolds).
-/

noncomputable theory
local attribute [instance, priority 10] classical.decidable_inhabited classical.prop_decidable

universes u v w u' v' w'

open set

section model_with_corners

/-- A structure containing informations on the way a space H embeds in a
model vector space E over the field 𝕜. This is all what is needed to
define a smooth manifold with model space H, and model vector space E.
We register it as a type class-/
structure model_with_corners (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [normed_group E] [normed_space 𝕜 E] (H : Type*) [topological_space H]
  extends local_equiv H E :=
(source_eq          : source = univ)
(unique_diff        : unique_diff_on 𝕜 (range to_fun))
(continuous_to_fun  : continuous to_fun)
(continuous_inv_fun : continuous inv_fun)

attribute [simp] model_with_corners.source_eq

/-- A vector space is a model with corners. -/
def model_with_corners_self (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [normed_group E] [normed_space 𝕜 E] : model_with_corners 𝕜 E E :=
{ to_fun     := id,
  inv_fun    := id,
  source     := univ,
  target     := univ,
  source_eq  := rfl,
  map_source := λ_ _, mem_univ _,
  map_target := λ_ _, mem_univ _,
  left_inv   := λ_ _, rfl,
  right_inv  := λ_ _, rfl,
  unique_diff := by { rw range_id, exact is_open_univ.unique_diff_on },
  continuous_to_fun  := continuous_id,
  continuous_inv_fun := continuous_id }

/-- In the trivial model with corners, the associated local equiv is the identity. -/
@[simp] lemma model_with_corners_self_local_equiv (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [normed_group E] [normed_space 𝕜 E] :
  (model_with_corners_self 𝕜 E).to_local_equiv = local_equiv.refl E := rfl

section
/- Basic properties of models with corners. -/
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H)

@[simp] lemma model_with_corners_target : I.target = range I.to_fun :=
by rw [← image_univ, ← local_equiv.image_source_eq_target, I.source_eq]

@[simp] lemma model_with_corners_left_inv (x : H) : I.inv_fun (I.to_fun x) = x :=
by simp [I.left_inv, I.source_eq]

@[simp] lemma model_with_corners_inv_fun_comp : I.inv_fun ∘ I.to_fun = id :=
by { ext x, exact model_with_corners_left_inv _ _ }

@[simp] lemma model_with_corners_right_inv {x : E} (hx : x ∈ range I.to_fun) :
  I.to_fun (I.inv_fun x) = x :=
begin
  apply I.right_inv,
  simp [hx]
end

lemma model_with_corners.image (s : set H) :
  I.to_fun '' s = I.inv_fun ⁻¹' s ∩ range I.to_fun :=
begin
  ext x,
  simp only [mem_image, mem_inter_eq, mem_range, mem_preimage],
  split,
  { rintros ⟨y, ⟨ys, hy⟩⟩,
    rw ← hy,
    simp [ys],
    exact ⟨y, rfl⟩ },
  { rintros ⟨xs, ⟨y, yx⟩⟩,
    rw ← yx at xs,
    simp at xs,
    exact ⟨y, ⟨xs, yx⟩⟩ }
end

end

/-- Given two model_with_corners I on (E, H) and I' on (E', H'), we define the model with corners
I.prod I' on (E × E', H × H'). This appears in particular for the manifold structure on the tangent
bundle to a manifold modelled on (E, H): it will be modelled on (E × E, H × E). -/
def model_with_corners.prod
  {𝕜 : Type u} [nondiscrete_normed_field 𝕜]
  {E : Type v} [normed_group E] [normed_space 𝕜 E] {H : Type w} [topological_space H]
  (I : model_with_corners 𝕜 E H)
  {E' : Type v'} [normed_group E'] [normed_space 𝕜 E'] {H' : Type w'} [topological_space H']
  (I' : model_with_corners 𝕜 E' H') : model_with_corners 𝕜 (E × E') (H × H') :=
{ to_fun      := λp, (I.to_fun p.1, I'.to_fun p.2),
  inv_fun     := λp, (I.inv_fun p.1, I'.inv_fun p.2),
  source      := (univ : set (H × H')),
  target      := set.prod (range I.to_fun) (range I'.to_fun),
  map_source  := λ ⟨x, x'⟩ _, by simp [-mem_range, mem_range_self],
  map_target  := λ ⟨x, x'⟩ _, mem_univ _,
  left_inv    := λ ⟨x, x'⟩ _, by simp,
  right_inv   := λ ⟨x, x'⟩ ⟨hx, hx'⟩, by rw [I.right_inv, I'.right_inv]; rwa model_with_corners_target,
  source_eq   := rfl,
  unique_diff := begin
    have : range (λ(p : H × H'), (I.to_fun p.1, I'.to_fun p.2)) = set.prod (range I.to_fun) (range I'.to_fun),
      by { rw ← prod_range_range_eq },
    rw this,
    exact unique_diff_on.prod I.unique_diff I'.unique_diff,
  end,
  continuous_to_fun := (continuous.comp I.continuous_to_fun continuous_fst).prod_mk
    (continuous.comp I'.continuous_to_fun continuous_snd),
  continuous_inv_fun := (continuous.comp I.continuous_inv_fun continuous_fst).prod_mk
    (continuous.comp I'.continuous_inv_fun continuous_snd) }

/-- Special case of product model with corners, which is trivial on the second factor. This shows up
as the model to tangent bundles. -/
@[reducible] def model_with_corners.tangent
  {𝕜 : Type u} [nondiscrete_normed_field 𝕜]
  {E : Type v} [normed_group E] [normed_space 𝕜 E] {H : Type w} [topological_space H]
  (I : model_with_corners 𝕜 E H) : model_with_corners 𝕜 (E × E) (H × E) :=
 I.prod (model_with_corners_self 𝕜 E)

section boundaryless

/-- Property ensuring that the model with corners I defines manifolds without boundary. -/
class model_with_corners.boundaryless {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H) : Prop :=
(range_eq_univ : range I.to_fun = univ)

/-- The trivial model with corners has no boundary -/
instance model_with_corners_self_range (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [normed_group E] [normed_space 𝕜 E] : (model_with_corners_self 𝕜 E).boundaryless :=
⟨ by simp ⟩

/-- If two model with corners are boundaryless, their product also is -/
instance model_with_corners.range_eq_univ_prod {𝕜 : Type u} [nondiscrete_normed_field 𝕜]
  {E : Type v} [normed_group E] [normed_space 𝕜 E] {H : Type w} [topological_space H]
  (I : model_with_corners 𝕜 E H) [I.boundaryless]
  {E' : Type v'} [normed_group E'] [normed_space 𝕜 E'] {H' : Type w'} [topological_space H']
  (I' : model_with_corners 𝕜 E' H') [I'.boundaryless] :
  (I.prod I').boundaryless :=
begin
  split,
  dsimp [model_with_corners.prod],
  rw [← prod_range_range_eq, model_with_corners.boundaryless.range_eq_univ,
      model_with_corners.boundaryless.range_eq_univ, univ_prod_univ]
end

end boundaryless

section times_cont_diff_groupoid

/-- Given a model with corners (E, H), we define the groupoid of C^n transformations of H as the
maps that are C^n when read in E through I. -/
def times_cont_diff_groupoid (n : with_top ℕ) {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H) :
  structure_groupoid H :=
groupoid_of_pregroupoid
{ property := λf s, times_cont_diff_on 𝕜 n (I.to_fun ∘ f ∘ I.inv_fun) (I.inv_fun ⁻¹' s ∩ range I.to_fun),
  comp     := λf g u v hf hg huv, begin
    have A : unique_diff_on 𝕜 (I.inv_fun ⁻¹' (u ∩ (f ⁻¹' v)) ∩ range (I.to_fun)),
      by { rw inter_comm, exact I.unique_diff.inter (I.continuous_inv_fun _ huv) },
    have : I.to_fun ∘ (g ∘ f) ∘ I.inv_fun = (I.to_fun ∘ g ∘ I.inv_fun) ∘ (I.to_fun ∘ f ∘ I.inv_fun),
      by { ext x, simp },
    rw this,
    apply times_cont_diff_on.comp hg _ A,
    { change I.inv_fun ⁻¹' (u ∩ (f ⁻¹' v)) ∩ (range (I.to_fun)) ⊆
        I.to_fun ∘ f ∘ I.inv_fun ⁻¹' ((I.inv_fun ⁻¹' v) ∩ (range (I.to_fun))),
      rintros x ⟨hx1, hx2⟩,
      simp at ⊢ hx1,
      exact ⟨hx1.2, (f (I.inv_fun x)), rfl⟩ },
    { refine hf.mono _ A,
      rintros x ⟨hx1, hx2⟩,
      exact ⟨hx1.1, hx2⟩ }
  end,
  id_mem   := begin
    have A : unique_diff_on 𝕜 ((I.inv_fun ⁻¹' univ) ∩ (range I.to_fun)),
      by simp [I.unique_diff],
    apply times_cont_diff_on.congr (times_cont_diff_id.times_cont_diff_on A) A _,
    rintros x ⟨hx1, hx2⟩,
    rcases mem_range.1 hx2 with ⟨y, hy⟩,
    rw ← hy,
    simp,
  end,
  locality := λf u hu H, begin
    apply times_cont_diff_on_of_locally_times_cont_diff_on,
    show unique_diff_on 𝕜 ((I.inv_fun ⁻¹' u) ∩ (range (I.to_fun))),
      by { rw inter_comm, exact I.unique_diff.inter (I.continuous_inv_fun _ hu) },
    rintros y ⟨hy1, hy2⟩,
    rcases mem_range.1 hy2 with ⟨x, hx⟩,
    rw ← hx at ⊢ hy1,
    simp at ⊢ hy1,
    rcases H x hy1 with ⟨v, v_open, xv, hv⟩,
    have : (set.inter (I.inv_fun ⁻¹' set.inter u v) (range (I.to_fun)))
      = (set.inter (I.inv_fun ⁻¹' u) (range (I.to_fun)) ∩ I.inv_fun ⁻¹' v),
    { change ((I.inv_fun ⁻¹' (u ∩ v)) ∩ (range (I.to_fun)))
        = ((I.inv_fun ⁻¹' u) ∩ (range (I.to_fun)) ∩ I.inv_fun ⁻¹' v),
      rw [preimage_inter, inter_assoc, inter_assoc],
      congr' 1,
      rw inter_comm },
    rw this at hv,
    exact ⟨I.inv_fun ⁻¹' v, I.continuous_inv_fun _ v_open, by simpa, hv⟩
  end,
  congr    := λf g u hu fg hf, begin
    apply hf.congr,
    show unique_diff_on 𝕜 ((I.inv_fun ⁻¹' u) ∩ (range (I.to_fun))),
      by { rw inter_comm, exact I.unique_diff.inter (I.continuous_inv_fun _ hu) },
    rintros y ⟨hy1, hy2⟩,
    rcases mem_range.1 hy2 with ⟨x, hx⟩,
    rw ← hx at ⊢ hy1,
    simp at ⊢ hy1,
    rw fg _ hy1
  end }

/-- Inclusion of the groupoid of C^n local diffeos in the groupoid of C^m local diffeos when m ≤ n -/
lemma times_cont_diff_groupoid_le {n m : with_top ℕ} {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H) (h : m ≤ n) :
  times_cont_diff_groupoid n I ≤ times_cont_diff_groupoid m I :=
begin
  rw [times_cont_diff_groupoid, times_cont_diff_groupoid],
  apply groupoid_of_pregroupoid_le,
  assume f s hfs,
  exact times_cont_diff_on.of_le hfs h
end

/-- The groupoid of 0-times continuously differentiable maps is just the groupoid of all
local homeomorphisms -/
lemma times_cont_diff_groupoid_zero_eq {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H) :
  times_cont_diff_groupoid 0 I = continuous_groupoid H :=
begin
  apply le_antisymm lattice.le_top,
  assume u hu,
  change u ∈ times_cont_diff_groupoid 0 I,
  rw [times_cont_diff_groupoid, mem_groupoid_of_pregroupoid],
  simp only [times_cont_diff_on_zero],
  split,
  { apply continuous_on.comp (@continuous.continuous_on _ _ _ _ _ univ I.continuous_to_fun)
      _ (subset_univ _),
    apply continuous_on.comp u.continuous_to_fun I.continuous_inv_fun.continuous_on
      (inter_subset_left _ _) },
  { apply continuous_on.comp (@continuous.continuous_on _ _ _ _ _ univ I.continuous_to_fun)
      _ (subset_univ _),
    apply continuous_on.comp u.continuous_inv_fun I.continuous_inv_fun.continuous_on
      (inter_subset_left _ _) },
end

end times_cont_diff_groupoid

end model_with_corners

/- Typeclass defining smooth manifolds with corners with respect to a model with corners, over a
field 𝕜 and with infinite smoothness to simplify typeclass search and statements later on. -/
class smooth_manifold_with_corners {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [manifold H M] extends
  has_groupoid M (times_cont_diff_groupoid ⊤ I) : Prop

/-- For any model with corners, the model space is a smooth manifold -/
instance model_space_smooth {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] {H : Type*} [topological_space H]
  {I : model_with_corners 𝕜 E H} :
  smooth_manifold_with_corners I H := {}

/-- the space ℝ^n. Note that the name is slightly misleading, as we only need a normed space
structure on ℝ^n, but the one we use here is the sup norm and not the euclidean one -- this is not
a problem for the manifold applications, but should probably be refactored at some point. -/
def euclidean_space (n : ℕ) : Type := (fin n → ℝ)
/-- the half-space in ℝ^n, used to model manifolds with boundary. The definition is a little bit
convoluted as one can not require `0 ≤ x 0`: if n=0, then there is no 0 in `fin n`...-/
def euclidean_half_space (n : ℕ) : Type := {x : euclidean_space n // ∀i:fin n, i.val = 0 → 0 ≤ x i}

section
/- Register class instances for euclidean space and half-space -/
local attribute [reducible] euclidean_space euclidean_half_space
variable {n : ℕ}

instance : vector_space ℝ (euclidean_space n) := by apply_instance
instance : normed_group (euclidean_space n) := by apply_instance
instance : normed_space ℝ (euclidean_space n) := by apply_instance
instance : topological_space (euclidean_half_space n) := by apply_instance

end

lemma range_half_space (n : ℕ) :
  range (λx : euclidean_half_space n, x.val) = {y | ∀i:fin n, i.val = 0 → 0 ≤ y i } :=
by simp [euclidean_half_space]

/-- Definition of the model with corners (euclidean_space n, euclidean_half_space n), used as a
model for manifolds with boundary -/
def model_with_corners_euclidean_half_space (n : ℕ) :
  model_with_corners ℝ (euclidean_space n) (euclidean_half_space n) :=
{ to_fun     := λx, x.val,
  inv_fun    := λx, ⟨λi, if h : i.val = 0 then max (x i) 0 else x i,
                    λi, by { by_cases h : i.val = 0; simp [h, le_refl] } ⟩,
  source     := univ,
  target     := range (λx : euclidean_half_space n, x.val),
  map_source := λx hx, by simpa [-mem_range, mem_range_self] using x.property,
  map_target := λx hx, mem_univ _,
  left_inv   := λ⟨xval, xprop⟩ hx, begin
    rw subtype.mk_eq_mk,
    ext1 i,
    by_cases hi : i.val = 0,
    simp [hi, xprop i hi],
    simp [hi],
  end,
  right_inv := λx hx, begin
    rw range_half_space at hx,
    ext1 i,
    by_cases hi : i.val = 0,
    { simp [hi, hx i hi] },
    { simp [hi] }
  end,
  source_eq   := rfl,
  unique_diff := begin
    /- To check that the half-space has the unique differentiability property, we use the criterion
    `unique_diff_on_convex`: it suffices to check that it is convex and with nonempty interior. -/
    rw range_half_space,
    apply unique_diff_on_convex,
    show convex {y : euclidean_space n | ∀ (i : fin n), i.val = 0 → 0 ≤ y i},
    { assume x y a b hx hy ha hb hab i hi,
      simpa using add_le_add (mul_nonneg' ha (hx i hi)) (mul_nonneg' hb (hy i hi)) },
    show interior {y : euclidean_space n | ∀ (i : fin n), i.val = 0 → 0 ≤ y i} ≠ ∅,
    { rw ne_empty_iff_exists_mem,
      use (λi, 1),
      rw mem_interior,
      refine ⟨(pi (univ : set (fin n)) (λi, (Ioi 0 : set ℝ))), _,
        is_open_set_pi finite_univ (λa ha, is_open_Ioi), _⟩,
      { assume x hx i hi,
        simp [pi] at hx,
        exact le_of_lt (hx i) },
      { simp [pi],
        assume i,
        exact zero_lt_one } }
  end,
  continuous_to_fun  := continuous_subtype_val,
  continuous_inv_fun := begin
    apply continuous_subtype_mk,
    apply continuous_pi,
    assume i,
    by_cases h : i.val = 0,
    { simp only [h, dif_pos],
      have : continuous (λx:ℝ, max x 0) := continuous_max continuous_id continuous_const,
      exact this.comp (continuous_apply i) },
    { simp [h],
      exact continuous_apply i }
  end }
