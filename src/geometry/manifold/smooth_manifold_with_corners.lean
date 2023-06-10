/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.cont_diff
import geometry.manifold.charted_space

/-!
# Smooth manifolds (possibly with boundary or corners)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A smooth manifold is a manifold modelled on a normed vector space, or a subset like a
half-space (to get manifolds with boundaries) for which the changes of coordinates are smooth maps.
We define a model with corners as a map `I : H → E` embedding nicely the topological space `H` in
the vector space `E` (or more precisely as a structure containing all the relevant properties).
Given such a model with corners `I` on `(E, H)`, we define the groupoid of local
homeomorphisms of `H` which are smooth when read in `E` (for any regularity `n : ℕ∞`).
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
* `cont_diff_groupoid n I` :
  when `I` is a model with corners on `(𝕜, E, H)`, this is the groupoid of local homeos of `H`
  which are of class `C^n` over the normed field `𝕜`, when read in `E`.
* `smooth_manifold_with_corners I M` :
  a type class saying that the charted space `M`, modelled on the space `H`, has `C^∞` changes of
  coordinates with respect to the model with corners `I` on `(𝕜, E, H)`. This type class is just
  a shortcut for `has_groupoid M (cont_diff_groupoid ∞ I)`.
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

  `variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
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
using `has_groupoid M (cont_diff_groupoid k I)` where `I` is the model with corners.

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

open set filter function
open_locale manifold filter topology

localized "notation (name := with_top.nat.top) `∞` := (⊤ : ℕ∞)" in manifold

/-! ### Models with corners. -/

/-- A structure containing informations on the way a space `H` embeds in a
model vector space `E` over the field `𝕜`. This is all what is needed to
define a smooth manifold with model space `H`, and model vector space `E`.
-/
@[ext, nolint has_nonempty_instance]
structure model_with_corners (𝕜 : Type*) [nontrivially_normed_field 𝕜]
  (E : Type*) [normed_add_comm_group E] [normed_space 𝕜 E] (H : Type*) [topological_space H]
  extends local_equiv H E :=
(source_eq          : source = univ)
(unique_diff'       : unique_diff_on 𝕜 to_local_equiv.target)
(continuous_to_fun  : continuous to_fun . tactic.interactive.continuity')
(continuous_inv_fun : continuous inv_fun . tactic.interactive.continuity')

attribute [simp, mfld_simps] model_with_corners.source_eq

/-- A vector space is a model with corners. -/
def model_with_corners_self (𝕜 : Type*) [nontrivially_normed_field 𝕜]
  (E : Type*) [normed_add_comm_group E] [normed_space 𝕜 E] : model_with_corners 𝕜 E E :=
{ to_local_equiv := local_equiv.refl E,
  source_eq    := rfl,
  unique_diff' := unique_diff_on_univ,
  continuous_to_fun  := continuous_id,
  continuous_inv_fun := continuous_id }

localized "notation (name := model_with_corners_self) `𝓘(` 𝕜 `, ` E `)` :=
  model_with_corners_self 𝕜 E" in manifold

localized "notation (name := model_with_corners_self.self) `𝓘(` 𝕜 `)` :=
  model_with_corners_self 𝕜 𝕜" in manifold

section
variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H)

namespace model_with_corners

instance : has_coe_to_fun (model_with_corners 𝕜 E H) (λ _, H → E) := ⟨λ e, e.to_fun⟩

/-- The inverse to a model with corners, only registered as a local equiv. -/
protected def symm : local_equiv E H := I.to_local_equiv.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (𝕜 : Type*) [nontrivially_normed_field 𝕜]
  (E : Type*) [normed_add_comm_group E] [normed_space 𝕜 E] (H : Type*) [topological_space H]
  (I : model_with_corners 𝕜 E H) : H → E := I

/-- See Note [custom simps projection] -/
def simps.symm_apply (𝕜 : Type*) [nontrivially_normed_field 𝕜]
  (E : Type*) [normed_add_comm_group E] [normed_space 𝕜 E] (H : Type*) [topological_space H]
  (I : model_with_corners 𝕜 E H) : E → H := I.symm

initialize_simps_projections model_with_corners
  (to_local_equiv_to_fun → apply, to_local_equiv_inv_fun → symm_apply,
   to_local_equiv_source → source, to_local_equiv_target → target, -to_local_equiv)

/- Register a few lemmas to make sure that `simp` puts expressions in normal form -/
@[simp, mfld_simps] lemma to_local_equiv_coe : (I.to_local_equiv : H → E) = I :=
rfl

@[simp, mfld_simps] lemma mk_coe (e : local_equiv H E) (a b c d) :
  ((model_with_corners.mk e a b c d : model_with_corners 𝕜 E H) : H → E) = (e : H → E) := rfl

@[simp, mfld_simps] lemma to_local_equiv_coe_symm : (I.to_local_equiv.symm : E → H) = I.symm := rfl

@[simp, mfld_simps] lemma mk_symm (e : local_equiv H E) (a b c d) :
  (model_with_corners.mk e a b c d : model_with_corners 𝕜 E H).symm = e.symm :=
rfl

@[continuity] protected lemma continuous : continuous I := I.continuous_to_fun

protected lemma continuous_at {x} : continuous_at I x := I.continuous.continuous_at

protected lemma continuous_within_at {s x} : continuous_within_at I s x :=
I.continuous_at.continuous_within_at

@[continuity] lemma continuous_symm : continuous I.symm := I.continuous_inv_fun

lemma continuous_at_symm {x} : continuous_at I.symm x := I.continuous_symm.continuous_at

lemma continuous_within_at_symm {s x} : continuous_within_at I.symm s x :=
I.continuous_symm.continuous_within_at

lemma continuous_on_symm {s} : continuous_on I.symm s := I.continuous_symm.continuous_on

@[simp, mfld_simps] lemma target_eq : I.target = range (I : H → E) :=
by { rw [← image_univ, ← I.source_eq], exact (I.to_local_equiv.image_source_eq_target).symm }

protected lemma unique_diff : unique_diff_on 𝕜 (range I) := I.target_eq ▸ I.unique_diff'

@[simp, mfld_simps] protected lemma left_inv (x : H) : I.symm (I x) = x :=
by { refine I.left_inv' _, simp }

protected lemma left_inverse : left_inverse I.symm I := I.left_inv

lemma injective : injective I :=
I.left_inverse.injective

@[simp, mfld_simps] lemma symm_comp_self : I.symm ∘ I = id :=
I.left_inverse.comp_eq_id

protected lemma right_inv_on : right_inv_on I.symm I (range I) :=
I.left_inverse.right_inv_on_range

@[simp, mfld_simps] protected lemma right_inv {x : E} (hx : x ∈ range I) : I (I.symm x) = x :=
I.right_inv_on hx

lemma preimage_image (s : set H) : I ⁻¹' (I '' s) = s :=
I.injective.preimage_image s

protected lemma image_eq (s : set H) : I '' s = I.symm ⁻¹' s ∩ range I :=
begin
  refine (I.to_local_equiv.image_eq_target_inter_inv_preimage _).trans _,
  { rw I.source_eq, exact subset_univ _ },
  { rw [inter_comm, I.target_eq, I.to_local_equiv_coe_symm] }
end

protected lemma closed_embedding : closed_embedding I :=
I.left_inverse.closed_embedding I.continuous_symm I.continuous

lemma closed_range : is_closed (range I) :=
I.closed_embedding.closed_range

lemma map_nhds_eq (x : H) : map I (𝓝 x) = 𝓝[range I] (I x) :=
I.closed_embedding.to_embedding.map_nhds_eq x

lemma map_nhds_within_eq (s : set H) (x : H) : map I (𝓝[s] x) = 𝓝[I '' s] (I x) :=
I.closed_embedding.to_embedding.map_nhds_within_eq s x

lemma image_mem_nhds_within {x : H} {s : set H} (hs : s ∈ 𝓝 x) :
  I '' s ∈ 𝓝[range I] (I x) :=
I.map_nhds_eq x ▸ image_mem_map hs

lemma symm_map_nhds_within_image {x : H} {s : set H} :
  map I.symm (𝓝[I '' s] (I x)) = 𝓝[s] x :=
by rw [← I.map_nhds_within_eq, map_map, I.symm_comp_self, map_id]

lemma symm_map_nhds_within_range (x : H) :
  map I.symm (𝓝[range I] (I x)) = 𝓝 x :=
by rw [← I.map_nhds_eq, map_map, I.symm_comp_self, map_id]

lemma unique_diff_preimage {s : set H} (hs : is_open s) :
  unique_diff_on 𝕜 (I.symm ⁻¹' s ∩ range I) :=
by { rw inter_comm, exact I.unique_diff.inter (hs.preimage I.continuous_inv_fun) }

lemma unique_diff_preimage_source {β : Type*} [topological_space β]
  {e : local_homeomorph H β} : unique_diff_on 𝕜 (I.symm ⁻¹' (e.source) ∩ range I) :=
I.unique_diff_preimage e.open_source

lemma unique_diff_at_image {x : H} : unique_diff_within_at 𝕜 (range I) (I x) :=
I.unique_diff _ (mem_range_self _)

lemma symm_continuous_within_at_comp_right_iff {X} [topological_space X]
  {f : H → X} {s : set H} {x : H} :
  continuous_within_at (f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x) ↔ continuous_within_at f s x :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { have := h.comp I.continuous_within_at (maps_to_preimage _ _),
    simp_rw [preimage_inter, preimage_preimage, I.left_inv, preimage_id', preimage_range,
      inter_univ] at this,
    rwa [function.comp.assoc, I.symm_comp_self] at this },
  { rw [← I.left_inv x] at h, exact h.comp I.continuous_within_at_symm (inter_subset_left _ _) }
end

protected lemma locally_compact [locally_compact_space E] (I : model_with_corners 𝕜 E H) :
  locally_compact_space H :=
begin
  have : ∀ (x : H), (𝓝 x).has_basis (λ s, s ∈ 𝓝 (I x) ∧ is_compact s)
    (λ s, I.symm '' (s ∩ range ⇑I)),
  { intro x,
    rw ← I.symm_map_nhds_within_range,
    exact ((compact_basis_nhds (I x)).inf_principal _).map _ },
  refine locally_compact_space_of_has_basis this _,
  rintro x s ⟨-, hsc⟩,
  exact (hsc.inter_right I.closed_range).image I.continuous_symm
end

open topological_space

protected lemma second_countable_topology [second_countable_topology E]
  (I : model_with_corners 𝕜 E H) : second_countable_topology H :=
I.closed_embedding.to_embedding.second_countable_topology

end model_with_corners

section
variables (𝕜 E)

/-- In the trivial model with corners, the associated local equiv is the identity. -/
@[simp, mfld_simps] lemma model_with_corners_self_local_equiv :
  (𝓘(𝕜, E)).to_local_equiv = local_equiv.refl E := rfl

@[simp, mfld_simps] lemma model_with_corners_self_coe :
  (𝓘(𝕜, E) : E → E) = id := rfl

@[simp, mfld_simps] lemma model_with_corners_self_coe_symm :
  (𝓘(𝕜, E).symm : E → E) = id := rfl

end

end

section model_with_corners_prod

/-- Given two model_with_corners `I` on `(E, H)` and `I'` on `(E', H')`, we define the model with
corners `I.prod I'` on `(E × E', model_prod H H')`. This appears in particular for the manifold
structure on the tangent bundle to a manifold modelled on `(E, H)`: it will be modelled on
`(E × E, H × E)`. See note [Manifold type tags] for explanation about `model_prod H H'`
vs `H × H'`. -/
@[simps (lemmas_only)] def model_with_corners.prod
  {𝕜 : Type u} [nontrivially_normed_field 𝕜]
  {E : Type v} [normed_add_comm_group E] [normed_space 𝕜 E] {H : Type w} [topological_space H]
  (I : model_with_corners 𝕜 E H) {E' : Type v'} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {H' : Type w'} [topological_space H'] (I' : model_with_corners 𝕜 E' H') :
  model_with_corners 𝕜 (E × E') (model_prod H H') :=
{ to_fun := λ x, (I x.1, I' x.2),
  inv_fun := λ x, (I.symm x.1, I'.symm x.2),
  source := {x | x.1 ∈ I.source ∧ x.2 ∈ I'.source},
  source_eq    := by simp only [set_of_true] with mfld_simps,
  unique_diff' := I.unique_diff'.prod I'.unique_diff',
  continuous_to_fun := I.continuous_to_fun.prod_map I'.continuous_to_fun,
  continuous_inv_fun := I.continuous_inv_fun.prod_map I'.continuous_inv_fun,
  .. I.to_local_equiv.prod I'.to_local_equiv }

/-- Given a finite family of `model_with_corners` `I i` on `(E i, H i)`, we define the model with
corners `pi I` on `(Π i, E i, model_pi H)`. See note [Manifold type tags] for explanation about
`model_pi H`. -/
def model_with_corners.pi
  {𝕜 : Type u} [nontrivially_normed_field 𝕜] {ι : Type v} [fintype ι]
  {E : ι → Type w} [Π i, normed_add_comm_group (E i)] [Π i, normed_space 𝕜 (E i)]
  {H : ι → Type u'} [Π i, topological_space (H i)] (I : Π i, model_with_corners 𝕜 (E i) (H i)) :
  model_with_corners 𝕜 (Π i, E i) (model_pi H) :=
{ to_local_equiv := local_equiv.pi (λ i, (I i).to_local_equiv),
  source_eq := by simp only [set.pi_univ] with mfld_simps,
  unique_diff' := unique_diff_on.pi ι E _ _ (λ i _, (I i).unique_diff'),
  continuous_to_fun := continuous_pi $ λ i, (I i).continuous.comp (continuous_apply i),
  continuous_inv_fun := continuous_pi $ λ i, (I i).continuous_symm.comp (continuous_apply i) }

/-- Special case of product model with corners, which is trivial on the second factor. This shows up
as the model to tangent bundles. -/
@[reducible] def model_with_corners.tangent
  {𝕜 : Type u} [nontrivially_normed_field 𝕜]
  {E : Type v} [normed_add_comm_group E] [normed_space 𝕜 E] {H : Type w} [topological_space H]
  (I : model_with_corners 𝕜 E H) : model_with_corners 𝕜 (E × E) (model_prod H E) :=
I.prod (𝓘(𝕜, E))

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜] {E : Type*} [normed_add_comm_group E]
  [normed_space 𝕜 E] {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E'] {F : Type*}
   [normed_add_comm_group F] [normed_space 𝕜 F] {F' : Type*} [normed_add_comm_group F']
   [normed_space 𝕜 F']
{H : Type*} [topological_space H] {H' : Type*} [topological_space H']
{G : Type*} [topological_space G] {G' : Type*} [topological_space G']
{I : model_with_corners 𝕜 E H} {J : model_with_corners 𝕜 F G}

@[simp, mfld_simps] lemma model_with_corners_prod_to_local_equiv :
  (I.prod J).to_local_equiv = I.to_local_equiv.prod (J.to_local_equiv) :=
rfl

@[simp, mfld_simps] lemma model_with_corners_prod_coe
  (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') :
  (I.prod I' : _ × _ → _ × _) = prod.map I I' := rfl

@[simp, mfld_simps] lemma model_with_corners_prod_coe_symm
  (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') :
  ((I.prod I').symm : _ × _ → _ × _) = prod.map I.symm I'.symm := rfl

lemma model_with_corners_self_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜, E).prod 𝓘(𝕜, F) :=
by { ext1, simp }

lemma model_with_corners.range_prod : range (I.prod J) = range I ×ˢ range J :=
by { simp_rw [← model_with_corners.target_eq], refl }

end model_with_corners_prod

section boundaryless

/-- Property ensuring that the model with corners `I` defines manifolds without boundary. -/
class model_with_corners.boundaryless {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H) : Prop :=
(range_eq_univ : range I = univ)

/-- The trivial model with corners has no boundary -/
instance model_with_corners_self_boundaryless (𝕜 : Type*) [nontrivially_normed_field 𝕜]
  (E : Type*) [normed_add_comm_group E] [normed_space 𝕜 E] :
  (model_with_corners_self 𝕜 E).boundaryless :=
⟨by simp⟩

/-- If two model with corners are boundaryless, their product also is -/
instance model_with_corners.range_eq_univ_prod {𝕜 : Type u} [nontrivially_normed_field 𝕜]
  {E : Type v} [normed_add_comm_group E] [normed_space 𝕜 E] {H : Type w} [topological_space H]
  (I : model_with_corners 𝕜 E H) [I.boundaryless] {E' : Type v'} [normed_add_comm_group E']
  [normed_space 𝕜 E'] {H' : Type w'} [topological_space H']
  (I' : model_with_corners 𝕜 E' H') [I'.boundaryless] :
  (I.prod I').boundaryless :=
begin
  split,
  dsimp [model_with_corners.prod, model_prod],
  rw [← prod_range_range_eq, model_with_corners.boundaryless.range_eq_univ,
      model_with_corners.boundaryless.range_eq_univ, univ_prod_univ]
end

end boundaryless

section cont_diff_groupoid
/-! ### Smooth functions on models with corners -/

variables {m n : ℕ∞} {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H]
(I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M]

variable (n)
/-- Given a model with corners `(E, H)`, we define the groupoid of `C^n` transformations of `H` as
the maps that are `C^n` when read in `E` through `I`. -/
def cont_diff_groupoid : structure_groupoid H :=
pregroupoid.groupoid
{ property := λf s, cont_diff_on 𝕜 n (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I),
  comp     := λf g u v hf hg hu hv huv, begin
    have : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ (I ∘ f ∘ I.symm),
      by { ext x, simp },
    rw this,
    apply cont_diff_on.comp hg _,
    { rintros x ⟨hx1, hx2⟩,
      simp only with mfld_simps at ⊢ hx1,
      exact hx1.2 },
    { refine hf.mono _,
      rintros x ⟨hx1, hx2⟩,
      exact ⟨hx1.1, hx2⟩ }
  end,
  id_mem   := begin
    apply cont_diff_on.congr (cont_diff_id.cont_diff_on),
    rintros x ⟨hx1, hx2⟩,
    rcases mem_range.1 hx2 with ⟨y, hy⟩,
    rw ← hy,
    simp only with mfld_simps,
  end,
  locality := λf u hu H, begin
    apply cont_diff_on_of_locally_cont_diff_on,
    rintros y ⟨hy1, hy2⟩,
    rcases mem_range.1 hy2 with ⟨x, hx⟩,
    rw ← hx at ⊢ hy1,
    simp only with mfld_simps at ⊢ hy1,
    rcases H x hy1 with ⟨v, v_open, xv, hv⟩,
    have : ((I.symm ⁻¹' (u ∩ v)) ∩ (range I))
        = ((I.symm ⁻¹' u) ∩ (range I) ∩ I.symm ⁻¹' v),
    { rw [preimage_inter, inter_assoc, inter_assoc],
      congr' 1,
      rw inter_comm },
    rw this at hv,
    exact ⟨I.symm ⁻¹' v, v_open.preimage I.continuous_symm, by simpa, hv⟩
  end,
  congr    := λf g u hu fg hf, begin
    apply hf.congr,
    rintros y ⟨hy1, hy2⟩,
    rcases mem_range.1 hy2 with ⟨x, hx⟩,
    rw ← hx at ⊢ hy1,
    simp only with mfld_simps at ⊢ hy1,
    rw fg _ hy1
  end }

variable {n}
/-- Inclusion of the groupoid of `C^n` local diffeos in the groupoid of `C^m` local diffeos when
`m ≤ n` -/
lemma cont_diff_groupoid_le (h : m ≤ n) :
  cont_diff_groupoid n I ≤ cont_diff_groupoid m I :=
begin
  rw [cont_diff_groupoid, cont_diff_groupoid],
  apply groupoid_of_pregroupoid_le,
  assume f s hfs,
  exact cont_diff_on.of_le hfs h
end

/-- The groupoid of `0`-times continuously differentiable maps is just the groupoid of all
local homeomorphisms -/
lemma cont_diff_groupoid_zero_eq :
  cont_diff_groupoid 0 I = continuous_groupoid H :=
begin
  apply le_antisymm le_top,
  assume u hu,
  -- we have to check that every local homeomorphism belongs to `cont_diff_groupoid 0 I`,
  -- by unfolding its definition
  change u ∈ cont_diff_groupoid 0 I,
  rw [cont_diff_groupoid, mem_groupoid_of_pregroupoid],
  simp only [cont_diff_on_zero],
  split,
  { refine I.continuous.comp_continuous_on (u.continuous_on.comp I.continuous_on_symm _),
    exact (maps_to_preimage _ _).mono_left (inter_subset_left _ _) },
  { refine I.continuous.comp_continuous_on (u.symm.continuous_on.comp I.continuous_on_symm _),
    exact (maps_to_preimage _ _).mono_left (inter_subset_left _ _) },
end

variable (n)
/-- An identity local homeomorphism belongs to the `C^n` groupoid. -/
lemma of_set_mem_cont_diff_groupoid {s : set H} (hs : is_open s) :
  local_homeomorph.of_set s hs ∈ cont_diff_groupoid n I :=
begin
  rw [cont_diff_groupoid, mem_groupoid_of_pregroupoid],
  suffices h : cont_diff_on 𝕜 n (I ∘ I.symm) (I.symm ⁻¹' s ∩ range I),
    by simp [h],
  have : cont_diff_on 𝕜 n id (univ : set E) :=
    cont_diff_id.cont_diff_on,
  exact this.congr_mono (λ x hx, by simp [hx.2]) (subset_univ _)
end

/-- The composition of a local homeomorphism from `H` to `M` and its inverse belongs to
the `C^n` groupoid. -/
lemma symm_trans_mem_cont_diff_groupoid (e : local_homeomorph M H) :
  e.symm.trans e ∈ cont_diff_groupoid n I :=
begin
  have : e.symm.trans e ≈ local_homeomorph.of_set e.target e.open_target :=
    local_homeomorph.trans_symm_self _,
  exact structure_groupoid.eq_on_source _
    (of_set_mem_cont_diff_groupoid n I e.open_target) this
end

variables {E' H' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E'] [topological_space H']

/-- The product of two smooth local homeomorphisms is smooth. -/
lemma cont_diff_groupoid_prod
  {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
  {e : local_homeomorph H H} {e' : local_homeomorph H' H'}
  (he : e ∈ cont_diff_groupoid ⊤ I) (he' : e' ∈ cont_diff_groupoid ⊤ I') :
  e.prod e' ∈ cont_diff_groupoid ⊤ (I.prod I') :=
begin
  cases he with he he_symm,
  cases he' with he' he'_symm,
  simp only at he he_symm he' he'_symm,
  split;
  simp only [local_equiv.prod_source, local_homeomorph.prod_to_local_equiv],
  { have h3 := cont_diff_on.prod_map he he',
    rw [← I.image_eq, ← I'.image_eq, set.prod_image_image_eq] at h3,
    rw ← (I.prod I').image_eq,
    exact h3, },
  { have h3 := cont_diff_on.prod_map he_symm he'_symm,
    rw [← I.image_eq, ← I'.image_eq, set.prod_image_image_eq] at h3,
    rw ← (I.prod I').image_eq,
    exact h3, }
end

/-- The `C^n` groupoid is closed under restriction. -/
instance : closed_under_restriction (cont_diff_groupoid n I) :=
(closed_under_restriction_iff_id_le _).mpr
begin
  apply structure_groupoid.le_iff.mpr,
  rintros e ⟨s, hs, hes⟩,
  apply (cont_diff_groupoid n I).eq_on_source' _ _ _ hes,
  exact of_set_mem_cont_diff_groupoid n I hs,
end

end cont_diff_groupoid

section smooth_manifold_with_corners

/-! ### Smooth manifolds with corners -/

/-- Typeclass defining smooth manifolds with corners with respect to a model with corners, over a
field `𝕜` and with infinite smoothness to simplify typeclass search and statements later on. -/
@[ancestor has_groupoid]
class smooth_manifold_with_corners {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M] extends
  has_groupoid M (cont_diff_groupoid ∞ I) : Prop

lemma smooth_manifold_with_corners.mk' {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M]
  [gr : has_groupoid M (cont_diff_groupoid ∞ I)] :
  smooth_manifold_with_corners I M := { ..gr }

lemma smooth_manifold_with_corners_of_cont_diff_on
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M]
  (h : ∀ (e e' : local_homeomorph M H), e ∈ atlas H M → e' ∈ atlas H M →
    cont_diff_on 𝕜 ⊤ (I ∘ (e.symm ≫ₕ e') ∘ I.symm)
      (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I)) :
  smooth_manifold_with_corners I M :=
{ compatible :=
  begin
    haveI : has_groupoid M (cont_diff_groupoid ∞ I) := has_groupoid_of_pregroupoid _ h,
    apply structure_groupoid.compatible,
  end }

/-- For any model with corners, the model space is a smooth manifold -/
instance model_space_smooth {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] {H : Type*} [topological_space H]
  {I : model_with_corners 𝕜 E H} :
  smooth_manifold_with_corners I H := { .. has_groupoid_model_space _ _ }

end smooth_manifold_with_corners

namespace smooth_manifold_with_corners
/- We restate in the namespace `smooth_manifolds_with_corners` some lemmas that hold for general
charted space with a structure groupoid, avoiding the need to specify the groupoid
`cont_diff_groupoid ∞ I` explicitly. -/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M]

/-- The maximal atlas of `M` for the smooth manifold with corners structure corresponding to the
model with corners `I`. -/
def maximal_atlas := (cont_diff_groupoid ∞ I).maximal_atlas M

variable {M}

lemma subset_maximal_atlas [smooth_manifold_with_corners I M] :
  atlas H M ⊆ maximal_atlas I M :=
structure_groupoid.subset_maximal_atlas _

lemma chart_mem_maximal_atlas [smooth_manifold_with_corners I M] (x : M) :
  chart_at H x ∈ maximal_atlas I M :=
structure_groupoid.chart_mem_maximal_atlas _ x

variable {I}

lemma compatible_of_mem_maximal_atlas
  {e e' : local_homeomorph M H} (he : e ∈ maximal_atlas I M) (he' : e' ∈ maximal_atlas I M) :
  e.symm.trans e' ∈ cont_diff_groupoid ∞ I :=
structure_groupoid.compatible_of_mem_maximal_atlas he he'

/-- The product of two smooth manifolds with corners is naturally a smooth manifold with corners. -/
instance prod {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  (M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] :
  smooth_manifold_with_corners (I.prod I') (M×M') :=
{ compatible :=
  begin
    rintros f g ⟨f1, f2, hf1, hf2, rfl⟩ ⟨g1, g2, hg1, hg2, rfl⟩,
    rw [local_homeomorph.prod_symm, local_homeomorph.prod_trans],
    have h1 := has_groupoid.compatible (cont_diff_groupoid ⊤ I) hf1 hg1,
    have h2 := has_groupoid.compatible (cont_diff_groupoid ⊤ I') hf2 hg2,
    exact cont_diff_groupoid_prod h1 h2,
  end }

end smooth_manifold_with_corners

lemma local_homeomorph.singleton_smooth_manifold_with_corners
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  {M : Type*} [topological_space M]
  (e : local_homeomorph M H) (h : e.source = set.univ) :
  @smooth_manifold_with_corners 𝕜 _ E _ _ H _ I M _ (e.singleton_charted_space h) :=
@smooth_manifold_with_corners.mk' _ _ _ _ _ _ _ _ _ _ (id _) $
e.singleton_has_groupoid h (cont_diff_groupoid ∞ I)

lemma open_embedding.singleton_smooth_manifold_with_corners
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  {M : Type*} [topological_space M]
  [nonempty M] {f : M → H} (h : open_embedding f) :
  @smooth_manifold_with_corners 𝕜 _ E _ _ H _ I M _ h.singleton_charted_space :=
(h.to_local_homeomorph f).singleton_smooth_manifold_with_corners I (by simp)

namespace topological_space.opens

open topological_space

variables  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  {M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  (s : opens M)

instance : smooth_manifold_with_corners I s := { ..s.has_groupoid (cont_diff_groupoid ∞ I) }

end topological_space.opens

section extended_charts
open_locale topology

variables {𝕜 E M H E' M' H' : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E] [topological_space H] [topological_space M]
  (f f' : local_homeomorph M H) (I : model_with_corners 𝕜 E H)
  [normed_add_comm_group E'] [normed_space 𝕜 E'] [topological_space H'] [topological_space M']
  (I' : model_with_corners 𝕜 E' H')
  (x : M) {s t : set M}

/-!
### Extended charts

In a smooth manifold with corners, the model space is the space `H`. However, we will also
need to use extended charts taking values in the model vector space `E`. These extended charts are
not `local_homeomorph` as the target is not open in `E` in general, but we can still register them
as `local_equiv`.
-/

namespace local_homeomorph
/-- Given a chart `f` on a manifold with corners, `f.extend I` is the extended chart to the model
vector space. -/
@[simp, mfld_simps] def extend : local_equiv M E :=
f.to_local_equiv ≫ I.to_local_equiv

lemma extend_coe : ⇑(f.extend I) = I ∘ f := rfl

lemma extend_coe_symm : ⇑(f.extend I).symm = f.symm ∘ I.symm := rfl

lemma extend_source : (f.extend I).source = f.source :=
by rw [extend, local_equiv.trans_source, I.source_eq, preimage_univ, inter_univ]

lemma is_open_extend_source : is_open (f.extend I).source :=
by { rw extend_source, exact f.open_source }

lemma extend_target : (f.extend I).target = I.symm ⁻¹' f.target ∩ range I :=
by simp_rw [extend, local_equiv.trans_target, I.target_eq, I.to_local_equiv_coe_symm, inter_comm]

lemma maps_to_extend (hs : s ⊆ f.source) :
  maps_to (f.extend I) s ((f.extend I).symm ⁻¹' s ∩ range I) :=
begin
  rw [maps_to', extend_coe, extend_coe_symm, preimage_comp, ← I.image_eq, image_comp,
    f.image_eq_target_inter_inv_preimage hs],
  exact image_subset _ (inter_subset_right _ _)
end

lemma extend_left_inv {x : M} (hxf : x ∈ f.source) : (f.extend I).symm (f.extend I x) = x :=
(f.extend I).left_inv $ by rwa f.extend_source

lemma extend_source_mem_nhds {x : M} (h : x ∈ f.source) :
  (f.extend I).source ∈ 𝓝 x :=
(is_open_extend_source f I).mem_nhds $ by rwa f.extend_source I

lemma extend_source_mem_nhds_within {x : M} (h : x ∈ f.source) :
  (f.extend I).source ∈ 𝓝[s] x :=
mem_nhds_within_of_mem_nhds $ extend_source_mem_nhds f I h

lemma continuous_on_extend : continuous_on (f.extend I) (f.extend I).source :=
begin
  refine I.continuous.comp_continuous_on _,
  rw extend_source,
  exact f.continuous_on
end

lemma continuous_at_extend {x : M} (h : x ∈ f.source) :
  continuous_at (f.extend I) x :=
(continuous_on_extend f I).continuous_at $ extend_source_mem_nhds f I h

lemma map_extend_nhds {x : M} (hy : x ∈ f.source) :
  map (f.extend I) (𝓝 x) = 𝓝[range I] (f.extend I x) :=
by rwa [extend_coe, (∘), ← I.map_nhds_eq, ← f.map_nhds_eq, map_map]

lemma extend_target_mem_nhds_within {y : M} (hy : y ∈ f.source) :
  (f.extend I).target ∈ 𝓝[range I] (f.extend I y) :=
begin
  rw [← local_equiv.image_source_eq_target, ← map_extend_nhds f I hy],
  exact image_mem_map (extend_source_mem_nhds _ _ hy)
end

lemma extend_target_subset_range : (f.extend I).target ⊆ range I :=
by simp only with mfld_simps

lemma nhds_within_extend_target_eq {y : M} (hy : y ∈ f.source) :
  𝓝[(f.extend I).target] (f.extend I y) =
  𝓝[range I] (f.extend I y) :=
(nhds_within_mono _ (extend_target_subset_range _ _)).antisymm $
  nhds_within_le_of_mem (extend_target_mem_nhds_within _ _ hy)

lemma continuous_at_extend_symm' {x : E} (h : x ∈ (f.extend I).target) :
  continuous_at (f.extend I).symm x :=
continuous_at.comp (f.continuous_at_symm h.2) (I.continuous_symm.continuous_at)

lemma continuous_at_extend_symm {x : M} (h : x ∈ f.source) :
  continuous_at (f.extend I).symm (f.extend I x) :=
continuous_at_extend_symm' f I $ (f.extend I).map_source $ by rwa f.extend_source

lemma continuous_on_extend_symm :
  continuous_on (f.extend I).symm (f.extend I).target :=
λ y hy, (continuous_at_extend_symm' _ _ hy).continuous_within_at

lemma extend_symm_continuous_within_at_comp_right_iff {X} [topological_space X] {g : M → X}
  {s : set M} {x : M} :
  continuous_within_at (g ∘ (f.extend I).symm) ((f.extend I).symm ⁻¹' s ∩ range I) (f.extend I x) ↔
  continuous_within_at (g ∘ f.symm) (f.symm ⁻¹' s) (f x) :=
by convert I.symm_continuous_within_at_comp_right_iff; refl

lemma is_open_extend_preimage' {s : set E} (hs : is_open s) :
  is_open ((f.extend I).source ∩ f.extend I ⁻¹' s) :=
(continuous_on_extend f I).preimage_open_of_open (is_open_extend_source _ _) hs

lemma is_open_extend_preimage {s : set E} (hs : is_open s) :
  is_open (f.source ∩ f.extend I ⁻¹' s) :=
by { rw ← extend_source f I, exact is_open_extend_preimage' f I hs }

lemma map_extend_nhds_within_eq_image {y : M} (hy : y ∈ f.source) :
  map (f.extend I) (𝓝[s] y) =
    𝓝[f.extend I '' ((f.extend I).source ∩ s)] (f.extend I y) :=
by set e := f.extend I;
calc map e (𝓝[s] y) = map e (𝓝[e.source ∩ s] y) :
  congr_arg (map e) (nhds_within_inter_of_mem (extend_source_mem_nhds_within f I hy)).symm
... = 𝓝[e '' (e.source ∩ s)] (e y) :
  ((f.extend I).left_inv_on.mono $ inter_subset_left _ _).map_nhds_within_eq
    ((f.extend I).left_inv $ by rwa f.extend_source)
    (continuous_at_extend_symm f I hy).continuous_within_at
    (continuous_at_extend f I hy).continuous_within_at

lemma map_extend_nhds_within {y : M} (hy : y ∈ f.source) :
  map (f.extend I) (𝓝[s] y) =
    𝓝[(f.extend I).symm ⁻¹' s ∩ range I] (f.extend I y) :=
by rw [map_extend_nhds_within_eq_image f I hy, nhds_within_inter,
  ← nhds_within_extend_target_eq _ _ hy, ← nhds_within_inter,
  (f.extend I).image_source_inter_eq', inter_comm]

lemma map_extend_symm_nhds_within {y : M} (hy : y ∈ f.source) :
  map (f.extend I).symm
    (𝓝[(f.extend I).symm ⁻¹' s ∩ range I] (f.extend I y)) = 𝓝[s] y :=
begin
  rw [← map_extend_nhds_within f I hy, map_map, map_congr, map_id],
  exact (f.extend I).left_inv_on.eq_on.eventually_eq_of_mem
    (extend_source_mem_nhds_within _ _ hy)
end

lemma map_extend_symm_nhds_within_range {y : M} (hy : y ∈ f.source) :
  map (f.extend I).symm (𝓝[range I] (f.extend I y)) = 𝓝 y :=
by rw [← nhds_within_univ, ← map_extend_symm_nhds_within f I hy, preimage_univ, univ_inter]

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
in the source is a neighborhood of the preimage, within a set. -/
lemma extend_preimage_mem_nhds_within {x : M} (h : x ∈ f.source)
  (ht : t ∈ 𝓝[s] x) :
  (f.extend I).symm ⁻¹' t ∈
    𝓝[(f.extend I).symm ⁻¹' s ∩ range I] (f.extend I x) :=
by rwa [← map_extend_symm_nhds_within f I h, mem_map] at ht

lemma extend_preimage_mem_nhds {x : M} (h : x ∈ f.source) (ht : t ∈ 𝓝 x) :
  (f.extend I).symm ⁻¹' t ∈ 𝓝 (f.extend I x) :=
begin
  apply (continuous_at_extend_symm f I h).preimage_mem_nhds,
  rwa (f.extend I).left_inv,
  rwa f.extend_source
end

/-- Technical lemma to rewrite suitably the preimage of an intersection under an extended chart, to
bring it into a convenient form to apply derivative lemmas. -/
lemma extend_preimage_inter_eq :
  ((f.extend I).symm ⁻¹' (s ∩ t) ∩ range I)
  = ((f.extend I).symm ⁻¹' s ∩ range I) ∩ ((f.extend I).symm ⁻¹' t) :=
by mfld_set_tac

lemma extend_symm_preimage_inter_range_eventually_eq_aux {s : set M} {x : M} (hx : x ∈ f.source) :
  ((f.extend I).symm ⁻¹' s ∩ range I : set _) =ᶠ[𝓝 (f.extend I x)]
  ((f.extend I).target ∩ (f.extend I).symm ⁻¹' s : set _) :=
begin
  rw [f.extend_target, inter_assoc, inter_comm (range I)],
  conv { congr, skip, rw [← @univ_inter _ (_ ∩ _)] },
  refine (eventually_eq_univ.mpr _).symm.inter eventually_eq.rfl,
  refine I.continuous_at_symm.preimage_mem_nhds (f.open_target.mem_nhds _),
  simp_rw [f.extend_coe, function.comp_apply, I.left_inv, f.maps_to hx]
end

lemma extend_symm_preimage_inter_range_eventually_eq {s : set M} {x : M}
  (hs : s ⊆ f.source) (hx : x ∈ f.source) :
  ((f.extend I).symm ⁻¹' s ∩ range I : set _) =ᶠ[𝓝 (f.extend I x)] f.extend I '' s :=
begin
  rw [← f.extend_source I] at hs,
  rw [(f.extend I).image_eq_target_inter_inv_preimage hs],
  exact f.extend_symm_preimage_inter_range_eventually_eq_aux I hx
end

/-! We use the name `extend_coord_change` for `(f'.extend I).symm ≫ f.extend I`. -/

lemma extend_coord_change_source :
  ((f.extend I).symm ≫ f'.extend I).source =
  I '' (f.symm ≫ₕ f').source :=
by { simp_rw [local_equiv.trans_source, I.image_eq, extend_source, local_equiv.symm_source,
      extend_target, inter_right_comm _ (range I)], refl }

lemma extend_image_source_inter :
  f.extend I '' (f.source ∩ f'.source) = ((f.extend I).symm ≫ f'.extend I).source :=
by simp_rw [f.extend_coord_change_source, f.extend_coe, image_comp I f, trans_source'', symm_symm,
  symm_target]

lemma extend_coord_change_source_mem_nhds_within {x : E}
  (hx : x ∈ ((f.extend I).symm ≫ f'.extend I).source) :
  ((f.extend I).symm ≫ f'.extend I).source ∈ 𝓝[range I] x :=
begin
  rw [f.extend_coord_change_source] at hx ⊢,
  obtain ⟨x, hx, rfl⟩ := hx,
  refine I.image_mem_nhds_within _,
  refine (local_homeomorph.open_source _).mem_nhds hx
end

lemma extend_coord_change_source_mem_nhds_within' {x : M}
  (hxf : x ∈ f.source) (hxf' : x ∈ f'.source) :
  ((f.extend I).symm ≫ f'.extend I).source ∈ 𝓝[range I] f.extend I x :=
begin
  apply extend_coord_change_source_mem_nhds_within,
  rw [← extend_image_source_inter],
  exact mem_image_of_mem _ ⟨hxf, hxf'⟩,
end

variables {f f'}
open smooth_manifold_with_corners

lemma cont_diff_on_extend_coord_change [charted_space H M]
  (hf : f ∈ maximal_atlas I M) (hf' : f' ∈ maximal_atlas I M) :
  cont_diff_on 𝕜 ⊤ (f.extend I ∘ (f'.extend I).symm)
  ((f'.extend I).symm ≫ f.extend I).source :=
begin
  rw [extend_coord_change_source, I.image_eq],
  exact (structure_groupoid.compatible_of_mem_maximal_atlas hf' hf).1
end

lemma cont_diff_within_at_extend_coord_change [charted_space H M]
  (hf : f ∈ maximal_atlas I M) (hf' : f' ∈ maximal_atlas I M) {x : E}
  (hx : x ∈ ((f'.extend I).symm ≫ f.extend I).source) :
  cont_diff_within_at 𝕜 ⊤ (f.extend I ∘ (f'.extend I).symm) (range I) x :=
begin
  apply (cont_diff_on_extend_coord_change I hf hf' x hx).mono_of_mem,
  rw [extend_coord_change_source] at hx ⊢,
  obtain ⟨z, hz, rfl⟩ := hx,
  exact I.image_mem_nhds_within ((local_homeomorph.open_source _).mem_nhds hz)
end

lemma cont_diff_within_at_extend_coord_change' [charted_space H M]
  (hf : f ∈ maximal_atlas I M) (hf' : f' ∈ maximal_atlas I M) {x : M}
  (hxf : x ∈ f.source) (hxf' : x ∈ f'.source) :
  cont_diff_within_at 𝕜 ⊤ (f.extend I ∘ (f'.extend I).symm) (range I) (f'.extend I x) :=
begin
  refine cont_diff_within_at_extend_coord_change I hf hf' _,
  rw [← extend_image_source_inter],
  exact mem_image_of_mem _ ⟨hxf', hxf⟩
end

end local_homeomorph
open local_homeomorph

variables [charted_space H M] [charted_space H' M']

/-- The preferred extended chart on a manifold with corners around a point `x`, from a neighborhood
of `x` to the model vector space. -/
@[simp, mfld_simps] def ext_chart_at (x : M) : local_equiv M E :=
(chart_at H x).extend I

lemma ext_chart_at_coe : ⇑(ext_chart_at I x) = I ∘ chart_at H x := rfl

lemma ext_chart_at_coe_symm :
  ⇑(ext_chart_at I x).symm = (chart_at H x).symm ∘ I.symm := rfl

lemma ext_chart_at_source : (ext_chart_at I x).source = (chart_at H x).source :=
extend_source _ _

lemma is_open_ext_chart_at_source : is_open (ext_chart_at I x).source :=
is_open_extend_source _ _

lemma mem_ext_chart_source : x ∈ (ext_chart_at I x).source :=
by simp only [ext_chart_at_source, mem_chart_source]

lemma ext_chart_at_target (x : M) : (ext_chart_at I x).target =
  I.symm ⁻¹' (chart_at H x).target ∩ range I :=
extend_target _ _

lemma ext_chart_at_to_inv : (ext_chart_at I x).symm ((ext_chart_at I x) x) = x :=
(ext_chart_at I x).left_inv (mem_ext_chart_source I x)

lemma maps_to_ext_chart_at (hs : s ⊆ (chart_at H x).source) :
  maps_to (ext_chart_at I x) s ((ext_chart_at I x).symm ⁻¹' s ∩ range I) :=
maps_to_extend _ _ hs

lemma ext_chart_at_source_mem_nhds' {x' : M} (h : x' ∈ (ext_chart_at I x).source) :
  (ext_chart_at I x).source ∈ 𝓝 x' :=
extend_source_mem_nhds _ _ $ by rwa ← ext_chart_at_source I

lemma ext_chart_at_source_mem_nhds : (ext_chart_at I x).source ∈ 𝓝 x :=
ext_chart_at_source_mem_nhds' I x (mem_ext_chart_source I x)

lemma ext_chart_at_source_mem_nhds_within' {x' : M} (h : x' ∈ (ext_chart_at I x).source) :
  (ext_chart_at I x).source ∈ 𝓝[s] x' :=
mem_nhds_within_of_mem_nhds (ext_chart_at_source_mem_nhds' I x h)

lemma ext_chart_at_source_mem_nhds_within :
  (ext_chart_at I x).source ∈ 𝓝[s] x :=
mem_nhds_within_of_mem_nhds (ext_chart_at_source_mem_nhds I x)

lemma continuous_on_ext_chart_at :
  continuous_on (ext_chart_at I x) (ext_chart_at I x).source :=
continuous_on_extend _ _

lemma continuous_at_ext_chart_at' {x' : M} (h : x' ∈ (ext_chart_at I x).source) :
  continuous_at (ext_chart_at I x) x' :=
continuous_at_extend _ _ $ by rwa ← ext_chart_at_source I

lemma continuous_at_ext_chart_at : continuous_at (ext_chart_at I x) x :=
continuous_at_ext_chart_at' _ _ (mem_ext_chart_source I x)

lemma map_ext_chart_at_nhds' {x y : M} (hy : y ∈ (ext_chart_at I x).source) :
  map (ext_chart_at I x) (𝓝 y) = 𝓝[range I] (ext_chart_at I x y) :=
map_extend_nhds _ _ $ by rwa ← ext_chart_at_source I

lemma map_ext_chart_at_nhds :
  map (ext_chart_at I x) (𝓝 x) = 𝓝[range I] (ext_chart_at I x x) :=
map_ext_chart_at_nhds' I $ mem_ext_chart_source I x

lemma ext_chart_at_target_mem_nhds_within' {y : M} (hy : y ∈ (ext_chart_at I x).source) :
  (ext_chart_at I x).target ∈ 𝓝[range I] (ext_chart_at I x y) :=
extend_target_mem_nhds_within _ _ $ by rwa ← ext_chart_at_source I

lemma ext_chart_at_target_mem_nhds_within :
  (ext_chart_at I x).target ∈ 𝓝[range I] (ext_chart_at I x x) :=
ext_chart_at_target_mem_nhds_within' I x (mem_ext_chart_source I x)

lemma ext_chart_at_target_subset_range : (ext_chart_at I x).target ⊆ range I :=
by simp only with mfld_simps

lemma nhds_within_ext_chart_at_target_eq' {y : M} (hy : y ∈ (ext_chart_at I x).source) :
  𝓝[(ext_chart_at I x).target] (ext_chart_at I x y) =
  𝓝[range I] (ext_chart_at I x y) :=
nhds_within_extend_target_eq _ _ $ by rwa ← ext_chart_at_source I

lemma nhds_within_ext_chart_at_target_eq :
  𝓝[(ext_chart_at I x).target] ((ext_chart_at I x) x) =
  𝓝[range I] ((ext_chart_at I x) x) :=
nhds_within_ext_chart_at_target_eq' I x (mem_ext_chart_source I x)

lemma continuous_at_ext_chart_at_symm'' {y : E} (h : y ∈ (ext_chart_at I x).target) :
  continuous_at (ext_chart_at I x).symm y :=
continuous_at_extend_symm' _ _ h

lemma continuous_at_ext_chart_at_symm' {x' : M} (h : x' ∈ (ext_chart_at I x).source) :
  continuous_at (ext_chart_at I x).symm (ext_chart_at I x x') :=
continuous_at_ext_chart_at_symm'' I _ $ (ext_chart_at I x).map_source h

lemma continuous_at_ext_chart_at_symm :
  continuous_at (ext_chart_at I x).symm ((ext_chart_at I x) x) :=
continuous_at_ext_chart_at_symm' I x (mem_ext_chart_source I x)

lemma continuous_on_ext_chart_at_symm :
  continuous_on (ext_chart_at I x).symm (ext_chart_at I x).target :=
λ y hy, (continuous_at_ext_chart_at_symm'' _ _ hy).continuous_within_at

lemma is_open_ext_chart_at_preimage' {s : set E} (hs : is_open s) :
  is_open ((ext_chart_at I x).source ∩ ext_chart_at I x ⁻¹' s) :=
is_open_extend_preimage' _ _ hs

lemma is_open_ext_chart_at_preimage {s : set E} (hs : is_open s) :
  is_open ((chart_at H x).source ∩ ext_chart_at I x ⁻¹' s) :=
by { rw ← ext_chart_at_source I, exact is_open_ext_chart_at_preimage' I x hs }

lemma map_ext_chart_at_nhds_within_eq_image' {y : M} (hy : y ∈ (ext_chart_at I x).source) :
  map (ext_chart_at I x) (𝓝[s] y) =
    𝓝[ext_chart_at I x '' ((ext_chart_at I x).source ∩ s)] (ext_chart_at I x y) :=
map_extend_nhds_within_eq_image _ _ $ by rwa ← ext_chart_at_source I

lemma map_ext_chart_at_nhds_within_eq_image :
  map (ext_chart_at I x) (𝓝[s] x) =
    𝓝[ext_chart_at I x '' ((ext_chart_at I x).source ∩ s)] (ext_chart_at I x x) :=
map_ext_chart_at_nhds_within_eq_image' I x (mem_ext_chart_source I x)

lemma map_ext_chart_at_nhds_within' {y : M} (hy : y ∈ (ext_chart_at I x).source) :
  map (ext_chart_at I x) (𝓝[s] y) =
    𝓝[(ext_chart_at I x).symm ⁻¹' s ∩ range I] (ext_chart_at I x y) :=
map_extend_nhds_within _ _ $ by rwa ← ext_chart_at_source I

lemma map_ext_chart_at_nhds_within :
  map (ext_chart_at I x) (𝓝[s] x) =
    𝓝[(ext_chart_at I x).symm ⁻¹' s ∩ range I] (ext_chart_at I x x) :=
map_ext_chart_at_nhds_within' I x (mem_ext_chart_source I x)

lemma map_ext_chart_at_symm_nhds_within' {y : M} (hy : y ∈ (ext_chart_at I x).source) :
  map (ext_chart_at I x).symm
    (𝓝[(ext_chart_at I x).symm ⁻¹' s ∩ range I] (ext_chart_at I x y)) = 𝓝[s] y :=
map_extend_symm_nhds_within _ _ $ by rwa ← ext_chart_at_source I

lemma map_ext_chart_at_symm_nhds_within_range' {y : M} (hy : y ∈ (ext_chart_at I x).source) :
  map (ext_chart_at I x).symm (𝓝[range I] (ext_chart_at I x y)) = 𝓝 y :=
map_extend_symm_nhds_within_range _ _ $ by rwa ← ext_chart_at_source I

lemma map_ext_chart_at_symm_nhds_within :
  map (ext_chart_at I x).symm
    (𝓝[(ext_chart_at I x).symm ⁻¹' s ∩ range I] (ext_chart_at I x x)) = 𝓝[s] x :=
map_ext_chart_at_symm_nhds_within' I x (mem_ext_chart_source I x)

lemma map_ext_chart_at_symm_nhds_within_range :
  map (ext_chart_at I x).symm (𝓝[range I] (ext_chart_at I x x)) = 𝓝 x :=
map_ext_chart_at_symm_nhds_within_range' I x (mem_ext_chart_source I x)

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
in the source is a neighborhood of the preimage, within a set. -/
lemma ext_chart_at_preimage_mem_nhds_within' {x' : M} (h : x' ∈ (ext_chart_at I x).source)
  (ht : t ∈ 𝓝[s] x') :
  (ext_chart_at I x).symm ⁻¹' t ∈
    𝓝[(ext_chart_at I x).symm ⁻¹' s ∩ range I] ((ext_chart_at I x) x') :=
by rwa [← map_ext_chart_at_symm_nhds_within' I x h, mem_map] at ht

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of the
base point is a neighborhood of the preimage, within a set. -/
lemma ext_chart_at_preimage_mem_nhds_within (ht : t ∈ 𝓝[s] x) :
  (ext_chart_at I x).symm ⁻¹' t ∈
    𝓝[(ext_chart_at I x).symm ⁻¹' s ∩ range I] ((ext_chart_at I x) x) :=
ext_chart_at_preimage_mem_nhds_within' I x (mem_ext_chart_source I x) ht

lemma ext_chart_at_preimage_mem_nhds' {x' : M}
  (h : x' ∈ (ext_chart_at I x).source) (ht : t ∈ 𝓝 x') :
  (ext_chart_at I x).symm ⁻¹' t ∈ 𝓝 (ext_chart_at I x x') :=
extend_preimage_mem_nhds _ _ (by rwa ← ext_chart_at_source I) ht

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
is a neighborhood of the preimage. -/
lemma ext_chart_at_preimage_mem_nhds (ht : t ∈ 𝓝 x) :
  (ext_chart_at I x).symm ⁻¹' t ∈ 𝓝 ((ext_chart_at I x) x) :=
begin
  apply (continuous_at_ext_chart_at_symm I x).preimage_mem_nhds,
  rwa (ext_chart_at I x).left_inv (mem_ext_chart_source _ _)
end

/-- Technical lemma to rewrite suitably the preimage of an intersection under an extended chart, to
bring it into a convenient form to apply derivative lemmas. -/
lemma ext_chart_at_preimage_inter_eq :
  ((ext_chart_at I x).symm ⁻¹' (s ∩ t) ∩ range I)
  = ((ext_chart_at I x).symm ⁻¹' s ∩ range I) ∩ ((ext_chart_at I x).symm ⁻¹' t) :=
by mfld_set_tac

/-! We use the name `ext_coord_change` for `(ext_chart_at I x').symm ≫ ext_chart_at I x`. -/

lemma ext_coord_change_source (x x' : M) :
  ((ext_chart_at I x').symm ≫ ext_chart_at I x).source =
  I '' ((chart_at H x').symm ≫ₕ (chart_at H x)).source :=
extend_coord_change_source _ _ _

open smooth_manifold_with_corners

lemma cont_diff_on_ext_coord_change [smooth_manifold_with_corners I M] (x x' : M) :
  cont_diff_on 𝕜 ⊤ (ext_chart_at I x ∘ (ext_chart_at I x').symm)
  ((ext_chart_at I x').symm ≫ ext_chart_at I x).source :=
cont_diff_on_extend_coord_change I (chart_mem_maximal_atlas I x) (chart_mem_maximal_atlas I x')

lemma cont_diff_within_at_ext_coord_change [smooth_manifold_with_corners I M] (x x' : M) {y : E}
  (hy : y ∈ ((ext_chart_at I x').symm ≫ ext_chart_at I x).source) :
  cont_diff_within_at 𝕜 ⊤ (ext_chart_at I x ∘ (ext_chart_at I x').symm) (range I) y :=
cont_diff_within_at_extend_coord_change I
  (chart_mem_maximal_atlas I x) (chart_mem_maximal_atlas I x') hy

/-- Conjugating a function to write it in the preferred charts around `x`.
The manifold derivative of `f` will just be the derivative of this conjugated function. -/
@[simp, mfld_simps] def written_in_ext_chart_at (x : M) (f : M → M') : E → E' :=
ext_chart_at I' (f x) ∘ f ∘ (ext_chart_at I x).symm

variable (𝕜)

lemma ext_chart_at_self_eq {x : H} : ⇑(ext_chart_at I x) = I := rfl
lemma ext_chart_at_self_apply {x y : H} : ext_chart_at I x y = I y := rfl

/-- In the case of the manifold structure on a vector space, the extended charts are just the
identity.-/
lemma ext_chart_at_model_space_eq_id (x : E) : ext_chart_at 𝓘(𝕜, E) x = local_equiv.refl E :=
by simp only with mfld_simps

lemma ext_chart_model_space_apply {x y : E} : ext_chart_at 𝓘(𝕜, E) x y = y := rfl

variable {𝕜}

lemma ext_chart_at_prod (x : M × M') :
  ext_chart_at (I.prod I') x = (ext_chart_at I x.1).prod (ext_chart_at I' x.2) :=
by simp only with mfld_simps

end extended_charts
