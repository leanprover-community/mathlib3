/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.times_cont_diff
import geometry.manifold.charted_space

/-!
# Smooth manifolds (possibly with boundary or corners)

A smooth manifold is a manifold modelled on a normed vector space, or a subset like a
half-space (to get manifolds with boundaries) for which the changes of coordinates are smooth maps.
We define a model with corners as a map `I : H → E` embedding nicely the topological space `H` in
the vector space `E` (or more precisely as a structure containing all the relevant properties).
Given such a model with corners `I` on `(E, H)`, we define the groupoid of local
homeomorphisms of `H` which are smooth when read in `E` (for any regularity `n : with_top ℕ`).
With this groupoid at hand and the general machinery of charted spaces, we thus get the notion
of `C^n` manifold with respect to any model with corners `I` on `(E, H)`. We also introduce a
specific type class for `C^∞` manifolds as these are the most commonly used.

## Main definitions

* `model_with_corners 𝕜 E H` :
  a structure containing informations on the way a space `H` embeds in a
  model vector space E over the field `𝕜`. This is all that is needed to
  define a smooth manifold with model space `H`, and model vector space `E`.
* `model_with_corners_self 𝕜 E` :
  trivial model with corners structure on the space `E` embedded in itself by the identity.
* `times_cont_diff_groupoid n I` :
  when `I` is a model with corners on `(𝕜, E, H)`, this is the groupoid of local homeos of `H`
  which are of class `C^n` over the normed field `𝕜`, when read in `E`.
* `smooth_manifold_with_corners I M` :
  a type class saying that the charted space `M`, modelled on the space `H`, has `C^∞` changes of
  coordinates with respect to the model with corners `I` on `(𝕜, E, H)`. This type class is just
  a shortcut for `has_groupoid M (times_cont_diff_groupoid ⊤ I)`.
* `ext_chart_at I x`:
  in a smooth manifold with corners with the model `I` on `(E, H)`, the charts take values in `H`,
  but often we may want to use their `E`-valued version, obtained by composing the charts with `I`.
  Since the target is in general not open, we can not register them as local homeomorphisms, but
  we register them as local equivs. `ext_chart_at I x` is the canonical such local equiv around `x`.

As specific examples of models with corners, we define (in the file `real_instances.lean`)
* `model_with_corners_self ℝ (euclidean_space (fin n))` for the model space used to define
  `n`-dimensional real manifolds without boundary (with notation `𝓡 n` in the locale `manifold`)
* `model_with_corners ℝ (euclidean_space (fin n)) (euclidean_half_space n)` for the model space
  used to define `n`-dimensional real manifolds with boundary (with notation `𝓡∂ n` in the locale
  `manifold`)
* `model_with_corners ℝ (euclidean_space (fin n)) (euclidean_quadrant n)` for the model space used
  to define `n`-dimensional real manifolds with corners

With these definitions at hand, to invoke an `n`-dimensional real manifold without boundary,
one could use

  `variables {n : ℕ} {M : Type*} [topological_space M] [charted_space (euclidean_space (fin n)) M]
   [smooth_manifold_with_corners (𝓡 n) M]`.

However, this is not the recommended way: a theorem proved using this assumption would not apply
for instance to the tangent space of such a manifold, which is modelled on
`(euclidean_space (fin n)) × (euclidean_space (fin n))` and not on `euclidean_space (fin (2 * n))`!
In the same way, it would not apply to product manifolds, modelled on
`(euclidean_space (fin n)) × (euclidean_space (fin m))`.
The right invocation does not focus on one specific construction, but on all constructions sharing
the right properties, like

  `variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {I : model_with_corners ℝ E E} [I.boundaryless]
  {M : Type*} [topological_space M] [charted_space E M] [smooth_manifold_with_corners I M]`

Here, `I.boundaryless` is a typeclass property ensuring that there is no boundary (this is for
instance the case for `model_with_corners_self`, or products of these). Note that one could consider
as a natural assumption to only use the trivial model with corners `model_with_corners_self ℝ E`,
but again in product manifolds the natural model with corners will not be this one but the product
one (and they are not defeq as `(λp : E × F, (p.1, p.2))` is not defeq to the identity). So, it is
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
space `E` (with basic example the Euclidean space), a model space `H` (with basic example the upper
half space), and an embedding of `H` into `E` (which can be the identity for `H = E`, or
`subtype.val` for manifolds with corners). We say that the pair `(E, H)` with their embedding is a
model with corners, and we encompass all the relevant properties (in particular the fact that the
image of `H` in `E` should have unique differentials) in the definition of `model_with_corners`.

We concentrate on `C^∞` manifolds: all the definitions work equally well for `C^n` manifolds, but
later on it is a pain to carry all over the smoothness parameter, especially when one wants to deal
with `C^k` functions as there would be additional conditions `k ≤ n` everywhere. Since one deals
almost all the time with `C^∞` (or analytic) manifolds, this seems to be a reasonable choice that
one could revisit later if needed. `C^k` manifolds are still available, but they should be called
using `has_groupoid M (times_cont_diff_groupoid k I)` where `I` is the model with corners.

I have considered using the model with corners `I` as a typeclass argument, possibly `out_param`, to
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

universes u v w u' v' w'

open set

section model_with_corners
/-! ### Models with corners. -/

/-- A structure containing informations on the way a space `H` embeds in a
model vector space `E` over the field `𝕜`. This is all what is needed to
define a smooth manifold with model space `H`, and model vector space `E`.
-/
@[nolint has_inhabited_instance]
structure model_with_corners (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [normed_group E] [normed_space 𝕜 E] (H : Type*) [topological_space H]
  extends local_equiv H E :=
(source_eq          : source = univ)
(unique_diff'       : unique_diff_on 𝕜 (range to_fun))
(continuous_to_fun  : continuous to_fun)
(continuous_inv_fun : continuous inv_fun)

attribute [simp] model_with_corners.source_eq

/-- A vector space is a model with corners. -/
def model_with_corners_self (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [normed_group E] [normed_space 𝕜 E] : model_with_corners 𝕜 E E :=
{ to_fun       := id,
  inv_fun      := id,
  source       := univ,
  target       := univ,
  source_eq    := rfl,
  map_source'  := λ_ _, mem_univ _,
  map_target'  := λ_ _, mem_univ _,
  left_inv'    := λ_ _, rfl,
  right_inv'   := λ_ _, rfl,
  unique_diff' := by { rw range_id, exact unique_diff_on_univ },
  continuous_to_fun  := continuous_id,
  continuous_inv_fun := continuous_id }

section
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H)

instance : has_coe_to_fun (model_with_corners 𝕜 E H) := ⟨_, λ e, e.to_fun⟩

/-- The inverse to a model with corners, only registered as a local equiv. -/
protected def model_with_corners.symm : local_equiv E H := I.to_local_equiv.symm

/- Register a few lemmas to make sure that `simp` puts expressions in normal form -/
@[simp] lemma model_with_corners.to_local_equiv_coe : (I.to_local_equiv : H → E) = I := rfl

@[simp] lemma model_with_corners.mk_coe (e : local_equiv H E) (a b c d) :
  ((model_with_corners.mk e a b c d : model_with_corners 𝕜 E H) : H → E) = (e : H → E) := rfl

@[simp] lemma model_with_corners.to_local_equiv_coe_symm :
  (I.to_local_equiv.symm : E → H) = I.symm := rfl

@[simp] lemma model_with_corners.mk_coe_symm (e : local_equiv H E) (a b c d) :
  ((model_with_corners.mk e a b c d : model_with_corners 𝕜 E H).symm : E → H) = (e.symm : E → H) :=
rfl

lemma model_with_corners.unique_diff : unique_diff_on 𝕜 (range I) := I.unique_diff'

protected lemma model_with_corners.continuous : continuous I := I.continuous_to_fun

lemma model_with_corners.continuous_symm : continuous I.symm := I.continuous_inv_fun

section
variables (𝕜 E)

/-- In the trivial model with corners, the associated local equiv is the identity. -/
@[simp] lemma model_with_corners_self_local_equiv :
  (model_with_corners_self 𝕜 E).to_local_equiv = local_equiv.refl E := rfl

@[simp] lemma model_with_corners_self_coe :
  (model_with_corners_self 𝕜 E : E → E) = id := rfl

@[simp] lemma model_with_corners_self_coe_symm :
  ((model_with_corners_self 𝕜 E).symm : E → E) = id := rfl

end

@[simp] lemma model_with_corners.target : I.target = range (I : H → E) :=
by { rw [← image_univ, ← I.source_eq], exact (I.to_local_equiv.image_source_eq_target).symm }

@[simp] lemma model_with_corners.left_inv (x : H) : I.symm (I x) = x :=
by { convert I.left_inv' _, simp }

@[simp] lemma model_with_corners.left_inv' : I.symm ∘ I = id :=
by { ext x, exact model_with_corners.left_inv _ _ }

@[simp] lemma model_with_corners.right_inv {x : E} (hx : x ∈ range I) :
  I (I.symm x) = x :=
by { apply I.right_inv', simp [hx] }

lemma model_with_corners.image (s : set H) :
  I '' s = I.symm ⁻¹' s ∩ range I :=
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

lemma model_with_corners.unique_diff_preimage {s : set H} (hs : is_open s) :
  unique_diff_on 𝕜 (I.symm ⁻¹' s ∩ range I) :=
by { rw inter_comm, exact I.unique_diff.inter (I.continuous_inv_fun _ hs) }

lemma model_with_corners.unique_diff_preimage_source {β : Type*} [topological_space β]
  {e : local_homeomorph H β} : unique_diff_on 𝕜 (I.symm ⁻¹' (e.source) ∩ range I) :=
I.unique_diff_preimage e.open_source

lemma model_with_corners.unique_diff_at_image {x : H} : unique_diff_within_at 𝕜 (range I) (I x) :=
I.unique_diff _ (mem_range_self _)

end

/-- Given two model_with_corners `I` on `(E, H)` and `I'` on `(E', H')`, we define the model with
corners `I.prod I'` on `(E × E', H × H')`. This appears in particular for the manifold structure on
the tangent bundle to a manifold modelled on `(E, H)`: it will be modelled on `(E × E, H × E)`. -/
def model_with_corners.prod
  {𝕜 : Type u} [nondiscrete_normed_field 𝕜]
  {E : Type v} [normed_group E] [normed_space 𝕜 E] {H : Type w} [topological_space H]
  (I : model_with_corners 𝕜 E H)
  {E' : Type v'} [normed_group E'] [normed_space 𝕜 E'] {H' : Type w'} [topological_space H']
  (I' : model_with_corners 𝕜 E' H') : model_with_corners 𝕜 (E × E') (H × H') :=
{ to_fun       := λp, (I p.1, I' p.2),
  inv_fun      := λp, (I.symm p.1, I'.symm p.2),
  source       := (univ : set (H × H')),
  target       := set.prod (range I) (range I'),
  map_source'  := λ ⟨x, x'⟩ _, by simp [-mem_range, mem_range_self],
  map_target'  := λ ⟨x, x'⟩ _, mem_univ _,
  left_inv'    := λ ⟨x, x'⟩ _, by simp,
  right_inv'   := λ ⟨x, x'⟩ ⟨hx, hx'⟩, by simp [hx, hx'],
  source_eq    := rfl,
  unique_diff' := begin
    have : range (λ(p : H × H'), (I p.1, I' p.2)) = set.prod (range I) (range I'),
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

/-- Property ensuring that the model with corners `I` defines manifolds without boundary. -/
class model_with_corners.boundaryless {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H) : Prop :=
(range_eq_univ : range I = univ)

/-- The trivial model with corners has no boundary -/
instance model_with_corners_self_boundaryless (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [normed_group E] [normed_space 𝕜 E] : (model_with_corners_self 𝕜 E).boundaryless :=
⟨by simp⟩

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
/-! ### Smooth functions on models with corners -/

variables {m n : with_top ℕ} {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H]
(I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M]

variable (n)
/-- Given a model with corners `(E, H)`, we define the groupoid of `C^n` transformations of `H` as
the maps that are `C^n` when read in `E` through `I`. -/
def times_cont_diff_groupoid : structure_groupoid H :=
pregroupoid.groupoid
{ property := λf s, times_cont_diff_on 𝕜 n (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I),
  comp     := λf g u v hf hg hu hv huv, begin
    have : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ (I ∘ f ∘ I.symm),
      by { ext x, simp },
    rw this,
    apply times_cont_diff_on.comp hg _,
    { rintros x ⟨hx1, hx2⟩,
      simp at ⊢ hx1,
      exact ⟨hx1.2, (f (I.symm x)), rfl⟩ },
    { refine hf.mono _,
      rintros x ⟨hx1, hx2⟩,
      exact ⟨hx1.1, hx2⟩ }
  end,
  id_mem   := begin
    apply times_cont_diff_on.congr (times_cont_diff_id.times_cont_diff_on),
    rintros x ⟨hx1, hx2⟩,
    rcases mem_range.1 hx2 with ⟨y, hy⟩,
    rw ← hy,
    simp,
  end,
  locality := λf u hu H, begin
    apply times_cont_diff_on_of_locally_times_cont_diff_on,
    rintros y ⟨hy1, hy2⟩,
    rcases mem_range.1 hy2 with ⟨x, hx⟩,
    rw ← hx at ⊢ hy1,
    simp at ⊢ hy1,
    rcases H x hy1 with ⟨v, v_open, xv, hv⟩,
    have : ((I.symm ⁻¹' (u ∩ v)) ∩ (range I))
        = ((I.symm ⁻¹' u) ∩ (range I) ∩ I.symm ⁻¹' v),
    { rw [preimage_inter, inter_assoc, inter_assoc],
      congr' 1,
      rw inter_comm },
    rw this at hv,
    exact ⟨I.symm ⁻¹' v, I.continuous_symm _ v_open, by simpa, hv⟩
  end,
  congr    := λf g u hu fg hf, begin
    apply hf.congr,
    rintros y ⟨hy1, hy2⟩,
    rcases mem_range.1 hy2 with ⟨x, hx⟩,
    rw ← hx at ⊢ hy1,
    simp at ⊢ hy1,
    rw fg _ hy1
  end }

variable {n}
/-- Inclusion of the groupoid of `C^n` local diffeos in the groupoid of `C^m` local diffeos when
`m ≤ n` -/
lemma times_cont_diff_groupoid_le (h : m ≤ n) :
  times_cont_diff_groupoid n I ≤ times_cont_diff_groupoid m I :=
begin
  rw [times_cont_diff_groupoid, times_cont_diff_groupoid],
  apply groupoid_of_pregroupoid_le,
  assume f s hfs,
  exact times_cont_diff_on.of_le hfs h
end

/-- The groupoid of `0`-times continuously differentiable maps is just the groupoid of all
local homeomorphisms -/
lemma times_cont_diff_groupoid_zero_eq :
  times_cont_diff_groupoid 0 I = continuous_groupoid H :=
begin
  apply le_antisymm le_top,
  assume u hu,
  -- we have to check that every local homeomorphism belongs to `times_cont_diff_groupoid 0 I`,
  -- by unfolding its definition
  change u ∈ times_cont_diff_groupoid 0 I,
  rw [times_cont_diff_groupoid, mem_groupoid_of_pregroupoid],
  simp only [times_cont_diff_on_zero],
  split,
  { apply continuous_on.comp (@continuous.continuous_on _ _ _ _ _ univ I.continuous)
      _ (subset_univ _),
    apply continuous_on.comp u.continuous_to_fun I.continuous_symm.continuous_on
      (inter_subset_left _ _) },
  { apply continuous_on.comp (@continuous.continuous_on _ _ _ _ _ univ I.continuous)
      _ (subset_univ _),
    apply continuous_on.comp u.continuous_inv_fun I.continuous_inv_fun.continuous_on
      (inter_subset_left _ _) },
end

variable (n)
/-- An identity local homeomorphism belongs to the `C^n` groupoid. -/
lemma of_set_mem_times_cont_diff_groupoid {s : set H} (hs : is_open s) :
  local_homeomorph.of_set s hs ∈ times_cont_diff_groupoid n I :=
begin
  rw [times_cont_diff_groupoid, mem_groupoid_of_pregroupoid],
  suffices h : times_cont_diff_on 𝕜 n (I ∘ I.symm) (I.symm ⁻¹' s ∩ range I),
    by simp [h],
  have : times_cont_diff_on 𝕜 n id (univ : set E) :=
    times_cont_diff_id.times_cont_diff_on,
  exact this.congr_mono (λ x hx, by simp [hx.2]) (subset_univ _)
end

/-- The composition of a local homeomorphism from `H` to `M` and its inverse belongs to
the `C^n` groupoid. -/
lemma symm_trans_mem_times_cont_diff_groupoid (e : local_homeomorph M H) :
  e.symm.trans e ∈ times_cont_diff_groupoid n I :=
begin
  have : e.symm.trans e ≈ local_homeomorph.of_set e.target e.open_target :=
    local_homeomorph.trans_symm_self _,
  exact structure_groupoid.eq_on_source _
    (of_set_mem_times_cont_diff_groupoid n I e.open_target) this
end

end times_cont_diff_groupoid

end model_with_corners

/-! ### Smooth manifolds with corners -/

/-- Typeclass defining smooth manifolds with corners with respect to a model with corners, over a
field `𝕜` and with infinite smoothness to simplify typeclass search and statements later on. -/
class smooth_manifold_with_corners {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M] extends
  has_groupoid M (times_cont_diff_groupoid ⊤ I) : Prop

/-- For any model with corners, the model space is a smooth manifold -/
instance model_space_smooth {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] {H : Type*} [topological_space H]
  {I : model_with_corners 𝕜 E H} :
  smooth_manifold_with_corners I H := {}

namespace smooth_manifold_with_corners
/- We restate in the namespace `smooth_manifolds_with_corners` some lemmas that hold for general
charted space with a structure groupoid, avoiding the need to specify the groupoid
`times_cont_diff_groupoid ⊤ I` explicitly. -/

variables  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M]

/-- The maximal atlas of `M` for the smooth manifold with corners structure corresponding to the
modle with corners `I`. -/
def maximal_atlas := (times_cont_diff_groupoid ⊤ I).maximal_atlas M

variable {M}

lemma compatible [smooth_manifold_with_corners I M]
  {e e' : local_homeomorph M H} (he : e ∈ atlas H M) (he' : e' ∈ atlas H M) :
  e.symm.trans e' ∈ times_cont_diff_groupoid ⊤ I :=
has_groupoid.compatible _ he he'

lemma mem_maximal_atlas_of_mem_atlas [smooth_manifold_with_corners I M]
  {e : local_homeomorph M H} (he : e ∈ atlas H M) : e ∈ maximal_atlas I M :=
structure_groupoid.mem_maximal_atlas_of_mem_atlas _ he

lemma chart_mem_maximal_atlas [smooth_manifold_with_corners I M] (x : M) :
  chart_at H x ∈ maximal_atlas I M :=
structure_groupoid.chart_mem_maximal_atlas _ x

variable {I}

lemma compatible_of_mem_maximal_atlas
  {e e' : local_homeomorph M H} (he : e ∈ maximal_atlas I M) (he' : e' ∈ maximal_atlas I M) :
  e.symm.trans e' ∈ times_cont_diff_groupoid ⊤ I :=
structure_groupoid.compatible_of_mem_maximal_atlas he he'

end smooth_manifold_with_corners

section extended_charts
open_locale topological_space

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  {M : Type*} [topological_space M] [charted_space H M]
  (x : M) {s t : set M}

/-!
### Extended charts

In a smooth manifold with corners, the model space is the space `H`. However, we will also
need to use extended charts taking values in the model vector space `E`. These extended charts are
not `local_homeomorph` as the target is not open in `E` in general, but we can still register them
as `local_equiv`.
-/

/-- The preferred extended chart on a manifold with corners around a point `x`, from a neighborhood
of `x` to the model vector space. -/
def ext_chart_at (x : M) : local_equiv M E :=
(chart_at H x).to_local_equiv.trans I.to_local_equiv

lemma ext_chart_at_source : (ext_chart_at I x).source = (chart_at H x).source :=
by rw [ext_chart_at, local_equiv.trans_source, I.source_eq, preimage_univ, inter_univ]

lemma ext_chart_at_open_source : is_open (ext_chart_at I x).source :=
by { rw ext_chart_at_source, exact (chart_at H x).open_source }

@[simp] lemma mem_ext_chart_source : x ∈ (ext_chart_at I x).source :=
by { rw ext_chart_at_source, exact mem_chart_source _ _ }

@[simp] lemma ext_chart_at_to_inv :
  (ext_chart_at I x).symm ((ext_chart_at I x) x) = x :=
by rw (ext_chart_at I x).left_inv (mem_ext_chart_source _ _)

lemma ext_chart_at_source_mem_nhds : (ext_chart_at I x).source ∈ 𝓝 x :=
mem_nhds_sets (ext_chart_at_open_source I x) (mem_ext_chart_source I x)

lemma ext_chart_at_continuous_on :
  continuous_on (ext_chart_at I x) (ext_chart_at I x).source :=
begin
  refine continuous_on.comp I.continuous.continuous_on _ subset_preimage_univ,
  rw ext_chart_at_source,
  exact (chart_at H x).continuous_on
end

lemma ext_chart_at_continuous_at :
  continuous_at (ext_chart_at I x) x :=
(ext_chart_at_continuous_on I x x (mem_ext_chart_source I x)).continuous_at
  (ext_chart_at_source_mem_nhds I x)

lemma ext_chart_at_continuous_on_symm :
  continuous_on (ext_chart_at I x).symm (ext_chart_at I x).target :=
begin
  apply continuous_on.comp (chart_at H x).continuous_on_symm I.continuous_symm.continuous_on,
  simp [ext_chart_at, local_equiv.trans_target]
end

lemma ext_chart_at_target_mem_nhds_within :
  (ext_chart_at I x).target ∈ nhds_within ((ext_chart_at I x) x) (range I) :=
begin
  rw [ext_chart_at, local_equiv.trans_target],
  simp only [function.comp_app, local_equiv.coe_trans, model_with_corners.target],
  refine inter_mem_nhds_within _
    (mem_nhds_sets (I.continuous_symm _ (chart_at H x).open_target) _),
  simp
end

lemma ext_chart_at_coe (p : M) : (ext_chart_at I x) p = I ((chart_at H x : M → H) p) := rfl

lemma ext_chart_at_coe_symm (p : E) :
  (ext_chart_at I x).symm p = ((chart_at H x).symm : H → M) (I.symm p) := rfl

lemma nhds_within_ext_chart_target_eq :
  nhds_within ((ext_chart_at I x) x) (ext_chart_at I x).target =
  nhds_within ((ext_chart_at I x) x) (range I) :=
begin
  apply le_antisymm,
  { apply nhds_within_mono,
    simp [ext_chart_at, local_equiv.trans_target], },
  { apply nhds_within_le_of_mem (ext_chart_at_target_mem_nhds_within _ _) }
end

lemma ext_chart_continuous_at_symm' {x' : M} (h : x' ∈ (ext_chart_at I x).source) :
  continuous_at (ext_chart_at I x).symm ((ext_chart_at I x) x') :=
begin
  apply continuous_at.comp,
  { rw ext_chart_at_source at h,
    simp [ext_chart_at],
    exact ((chart_at H x).continuous_on_symm _
      ((chart_at H x).map_source h)).continuous_at
        (mem_nhds_sets (chart_at H x).open_target
          ((chart_at H x).map_source h)) },
  { exact I.continuous_symm.continuous_at }
end

lemma ext_chart_continuous_at_symm :
  continuous_at (ext_chart_at I x).symm ((ext_chart_at I x) x) :=
ext_chart_continuous_at_symm' I x (mem_ext_chart_source I x)

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
in the source is a neighborhood of the preimage, within a set. -/
lemma ext_chart_preimage_mem_nhds_within' {x' : M} (h : x' ∈ (ext_chart_at I x).source)
  (ht : t ∈ nhds_within x' s) :
  (ext_chart_at I x).symm ⁻¹' t ∈ nhds_within ((ext_chart_at I x) x')
    ((ext_chart_at I x).symm ⁻¹' s ∩ range I) :=
begin
  apply (ext_chart_continuous_at_symm' I x h).continuous_within_at.tendsto_nhds_within_image,
  rw (ext_chart_at I x).left_inv h,
  apply nhds_within_mono _ _ ht,
  have : (ext_chart_at I x).symm '' ((ext_chart_at I x).symm ⁻¹' s) ⊆ s :=
    image_preimage_subset _ _,
  exact subset.trans (image_subset _ (inter_subset_left _ _)) this
end

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of the
base point is a neighborhood of the preimage, within a set. -/
lemma ext_chart_preimage_mem_nhds_within (ht : t ∈ nhds_within x s) :
  (ext_chart_at I x).symm ⁻¹' t ∈ nhds_within ((ext_chart_at I x) x)
    ((ext_chart_at I x).symm ⁻¹' s ∩ range I) :=
ext_chart_preimage_mem_nhds_within' I x (mem_ext_chart_source I x) ht

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
is a neighborhood of the preimage. -/
lemma ext_chart_preimage_mem_nhds (ht : t ∈ 𝓝 x) :
  (ext_chart_at I x).symm ⁻¹' t ∈ 𝓝 ((ext_chart_at I x) x) :=
begin
  apply (ext_chart_continuous_at_symm I x).preimage_mem_nhds,
  rwa (ext_chart_at I x).left_inv (mem_ext_chart_source _ _)
end

/-- Technical lemma to rewrite suitably the preimage of an intersection under an extended chart, to
bring it into a convenient form to apply derivative lemmas. -/
lemma ext_chart_preimage_inter_eq : ((ext_chart_at I x).symm ⁻¹' (s ∩ t) ∩ range I)
  = ((ext_chart_at I x).symm ⁻¹' s ∩ range I)
    ∩ ((ext_chart_at I x).symm ⁻¹' t) :=
begin
  rw [preimage_inter, inter_assoc, inter_assoc],
  congr' 1,
  rw inter_comm
end

end extended_charts

/-- In the case of the manifold structure on a vector space, the extended charts are just the
identity.-/
@[simp] lemma ext_chart_model_space_eq_id (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (x : E) :
  ext_chart_at (model_with_corners_self 𝕜 E) x = local_equiv.refl E :=
by simp [ext_chart_at]
