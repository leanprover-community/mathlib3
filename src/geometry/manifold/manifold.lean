/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import topology.local_homeomorph

/-!
# Manifolds

A manifold is a topological space M locally modelled on a model space H, i.e., the manifold is
covered by open subsets on which there are local homeomorphisms (the charts) going to H. If the
changes of charts satisfy some additional property (for instance if they are smooth), then M
inherits additional structure (it makes sense to talk about smooth manifolds). There are therefore
two different ingredients in a manifold:
* the set of charts, which is data
* the fact that changes of charts belong to some group (in fact groupoid), which is additional Prop.

We separate these two parts in the definition: the manifold structure is just the set of charts, and
then the different smoothness requirements (smooth manifold, orientable manifold, contact manifold,
and so on) are additional properties of these charts. These properties are formalized through the
notion of structure groupoid, i.e., a set of local homeomorphisms stable under composition and
inverse, to which the change of coordinates should belong.

## Main definitions
`structure_groupoid H`   : a subset of local homeomorphisms of `H` stable under composition, inverse
                           and restriction (ex: local diffeos)
`pregroupoid H`          : a subset of local homeomorphisms of `H` stable under composition and
                           restriction, but not inverse (ex: smooth maps)
`groupoid_of_pregroupoid`: construct a groupoid from a pregroupoid, by requiring that a map and its
                           inverse both belong to the pregroupoid (ex: construct diffeos from smooth
                           maps)
`continuous_groupoid H`  : the groupoid of all local homeomorphisms of `H`

`manifold H M`           : manifold structure on M modelled on H, given by an atlas of local
                           homeomorphisms from M to H whose sources cover M. This is a type class.
`has_groupoid M G`       : when `G` is a structure groupoid on `H` and `M` is a manifold modelled on
                           `H`, require that all coordinate changes belong to `G`. This is a type
                           class
`atlas H M`              : when `M` is a manifold modelled on `H`, the atlas of this manifold
                           structure, i.e., the set of charts
`structomorph G M M'`    : the set of diffeomorphisms between the manifolds M and M' for the
                           groupoid G. We avoid the word diffeomorphisms, keeping it for the
                           smooth category.

As a basic example, we give the instance
`instance manifold_model_space (H : Type*) [topological_space H] : manifold H H`
saying that a topological space is a manifold over itself, with the identity as unique chart. This
manifold structure is compatible with any groupoid.

## Implementation notes

The atlas in a manifold is *not* a maximal atlas in general: the notion of maximality depends on the
groupoid one considers, and changing groupoids changes the maximal atlas. With the current
formalization, it makes sense first to choose the atlas, and then to ask whether this precise atlas
defines a smooth manifold, an orientable manifold, and so on. A consequence is that structomorphisms
between M and M' do *not* induce a bijection between the atlases of M and M': the definition is only
that, read in charts, the structomorphism locally belongs to the groupoid under consideration.
(This is equivalent to inducing a bijection between elements of the maximal atlas). A consequence
is that the invariance under structomorphisms of properties defined in terms of the atlas is not
obvious in general, and could require some work in theory (amounting to the fact that these
properties only depend on the maximal atlas, for instance). In practice, this does not create any
real difficulty.

We use the letter `H` for the model space thinking of the case of manifolds with boundary, where the
model space is a half space.

Manifolds are sometimes defined as topological spaces with an atlas of local diffeomorphisms, and
sometimes as spaces with an atlas from which a topology is deduced. We use the former approach:
otherwise, there would be an instance from manifolds to topological spaces, which means that any
instance search for topological spaces would try to find manifold structures involving a yet
unknown model space, leading to problems. However, we also introduce the latter approach,
through a structure `manifold_core` making it possible to construct a topology out of a set of local
equivs with compatibility conditions (but we do not register it as an instance).

In the definition of a manifold, the model space is written as an explicit parameter as there can be
several model spaces for a given topological space. For instance, a complex manifold (modelled over
ℂ^n) will also be seen sometimes as a real manifold modelled over ℝ^(2n).
-/

noncomputable theory
local attribute [instance, priority 0] classical.decidable_inhabited classical.prop_decidable

universes u

variables {H : Type u} {M : Type*} {M' : Type*} {M'' : Type*}

/- Notational shortcut for the composition of local homeomorphisms, i.e., `local_homeomorph.trans`.
Note that, as is usual for equivs, the composition is from left to right, hence the direction of
the arrow. -/
local infixr  ` ≫ₕ `:100 := local_homeomorph.trans

open set local_homeomorph

section groupoid

/- One could add to the definition of a structure groupoid the fact that the restriction of an
element of the groupoid to any open set still belongs to the groupoid.
(This is in Kobayashi-Nomizu.)
I am not sure I want this, for instance on H × E where E is a vector space, and the groupoid is made
of functions respecting the fibers and linear in the fibers (so that a manifold over this groupoid
is naturally a vector bundle) I prefer that the members of the groupoid are always defined on
sets of the form s × E

The only nontrivial requirement is locality: if a local homeomorphism belongs to the groupoid
around each point in its domain of definition, then it belongs to the groupoid. Without this
requirement, the composition of diffeomorphisms does not have to be a diffeomorphism. Note that
this implies that a local homeomorphism with empty source belongs to any structure groupoid, as
it trivially satisfies this condition.

There is also a technical point, related to the fact that a local homeomorphism is by definition a
global map which is a homeomorphism when restricted to its source subset (and its values outside
of the source are not relevant). Therefore, we also require that being a member of the groupoid only
depends on the values on the source.
-/
/-- A structure groupoid is a set of local homeomorphisms of a topological space stable under
composition and inverse. They appear in the definition of the smoothness class of a manifold. -/
structure structure_groupoid (H : Type u) [topological_space H] :=
(members      : set (local_homeomorph H H))
(comp         : ∀e e' : local_homeomorph H H, e ∈ members → e' ∈ members → e ≫ₕ e' ∈ members)
(inv          : ∀e : local_homeomorph H H, e ∈ members → e.symm ∈ members)
(id_mem       : local_homeomorph.refl H ∈ members)
(locality     : ∀e : local_homeomorph H H, (∀x ∈ e.source, ∃s, is_open s ∧
                  x ∈ s ∧ e.restr s ∈ members) → e ∈ members)
(eq_on_source : ∀ e e' : local_homeomorph H H, e ∈ members → e' ≈ e → e' ∈ members)

variable [topological_space H]

@[reducible] instance : has_mem (local_homeomorph H H) (structure_groupoid H) :=
⟨λ(e : local_homeomorph H H) (G : structure_groupoid H), e ∈ G.members⟩

/-- Partial order on the set of groupoids, given by inclusion of the members of the groupoid -/
instance structure_groupoid.partial_order : partial_order (structure_groupoid H) :=
partial_order.lift structure_groupoid.members
(λa b h, by { cases a, cases b, dsimp at h, induction h, refl }) (by apply_instance)

/-- The trivial groupoid, containing only the identity (and maps with empty source, as this is
necessary from the definition) -/
def id_groupoid (H : Type u) [topological_space H] : structure_groupoid H :=
{ members := {local_homeomorph.refl H} ∪ {e : local_homeomorph H H | e.source = ∅},
  comp := λe e' he he', begin
    cases he; simp at he he',
    { simpa [he] },
    { have : (e ≫ₕ e').source ⊆ e.source := sep_subset _ _,
      rw he at this,
      have : (e ≫ₕ e') ∈ {e : local_homeomorph H H | e.source = ∅} := disjoint_iff.1 this,
      exact (mem_union _ _ _).2 (or.inr this) },
  end,
  inv := λe he, begin
    cases (mem_union _ _ _).1 he with E E,
    { finish },
    { right,
      simpa [e.to_local_equiv.image_source_eq_target.symm] using E },
  end,
  id_mem := mem_union_left _ (mem_insert _ ∅),
  locality := λe he, begin
    by_cases h : e.source = ∅,
    { right, exact h },
    { left,
      rcases ne_empty_iff_exists_mem.1 h with ⟨x, hx⟩,
      rcases he x hx with ⟨s, open_s, xs, hs⟩,
      have x's : x ∈ (e.restr s).source,
      { rw [restr_source, interior_eq_of_open open_s],
        exact ⟨hx, xs⟩ },
      cases hs,
      { replace hs : local_homeomorph.restr e s = local_homeomorph.refl H,
          by simpa using hs,
        have : (e.restr s).source = univ, by { rw hs, simp },
        change (e.to_local_equiv).source ∩ interior s = univ at this,
        have : univ ⊆ interior s, by { rw ← this, exact inter_subset_right _ _ },
        have : s = univ, by rwa [interior_eq_of_open open_s, univ_subset_iff] at this,
        simpa [this, restr_univ] using hs },
      { exfalso,
        rw mem_set_of_eq at hs,
        rwa hs at x's } },
  end,
  eq_on_source := λe e' he he'e, begin
    cases he,
    { left,
      have : e = e',
      { refine eq_of_eq_on_source_univ (setoid.symm he'e) _ _;
        rw set.mem_singleton_iff.1 he ; refl },
      rwa ← this },
    { right,
      change (e.to_local_equiv).source = ∅ at he,
      rwa [set.mem_set_of_eq, source_eq_of_eq_on_source he'e] }
  end }

/-- Every structure groupoid contains the identity groupoid -/
instance : lattice.order_bot (structure_groupoid H) :=
{ bot    := id_groupoid H,
  bot_le := begin
    assume u f hf,
    change f ∈ {local_homeomorph.refl H} ∪ {e : local_homeomorph H H | e.source = ∅} at hf,
    simp only [singleton_union, mem_set_of_eq, mem_insert_iff] at hf,
    cases hf,
    { rw hf,
      apply u.id_mem },
    { apply u.locality,
      assume x hx,
      rw [hf, mem_empty_eq] at hx,
      exact hx.elim }
  end,
  ..structure_groupoid.partial_order }

/-- To construct a groupoid, one may consider classes of local homeos such that both the function
and its inverse have some property. If this property is stable under composition,
one gets a groupoid. `pregroupoid` bundles the properties needed for this construction, with the
groupoid of smooth functions with smooth inverses as an application. -/
structure pregroupoid (H : Type*) [topological_space H] :=
(property : (H → H) → (set H) → Prop)
(comp     : ∀{f g u v}, property f u → property g v → is_open (u ∩ f ⁻¹' v)
              → property (g ∘ f) (u ∩ f ⁻¹' v))
(id_mem   : property id univ)
(locality : ∀{f u}, is_open u → (∀x∈u, ∃v, is_open v ∧ x ∈ v ∧ property f (u ∩ v)) → property f u)
(congr    : ∀{f g : H → H} {u}, is_open u → (∀x∈u, g x = f x) → property f u → property g u)

/-- Construct a groupoid of local homeos for which the map and its inverse have some property,
from a pregroupoid asserting that this property is stable under composition. -/
def groupoid_of_pregroupoid (PG : pregroupoid H) : structure_groupoid H :=
{ members  := {e : local_homeomorph H H | PG.property e.to_fun e.source ∧ PG.property e.inv_fun e.target},
  comp     := λe e' he he', begin
    split,
    { apply PG.comp he.1 he'.1,
      apply e.continuous_to_fun.preimage_open_of_open e.open_source e'.open_source },
    { apply PG.comp he'.2 he.2,
      apply e'.continuous_inv_fun.preimage_open_of_open e'.open_target e.open_target }
  end,
  inv      := λe he, ⟨he.2, he.1⟩,
  id_mem   := ⟨PG.id_mem, PG.id_mem⟩,
  locality := λe he, begin
    split,
    { apply PG.locality e.open_source (λx xu, _),
      rcases he x xu with ⟨s, s_open, xs, hs⟩,
      refine ⟨s, s_open, xs, _⟩,
      convert hs.1,
      exact (interior_eq_of_open s_open).symm },
    { apply PG.locality e.open_target (λx xu, _),
      rcases he (e.inv_fun x) (e.map_target xu) with ⟨s, s_open, xs, hs⟩,
      refine ⟨e.target ∩ e.inv_fun ⁻¹' s, _, ⟨xu, xs⟩, _⟩,
      { exact continuous_on.preimage_open_of_open e.continuous_inv_fun e.open_target s_open },
      { rw [← inter_assoc, inter_self],
        convert hs.2,
        exact (interior_eq_of_open s_open).symm } },
  end,
  eq_on_source := λe e' he ee', begin
    split,
    { apply PG.congr e'.open_source ee'.2,
      simp only [ee'.1, he.1] },
    { have A := eq_on_source_symm ee',
      apply PG.congr e'.symm.open_source A.2,
      convert he.2,
      rw A.1,
      refl }
  end }

lemma mem_groupoid_of_pregroupoid (PG : pregroupoid H) (e : local_homeomorph H H) :
  e ∈ groupoid_of_pregroupoid PG ↔ PG.property e.to_fun e.source ∧ PG.property e.inv_fun e.target :=
iff.rfl

lemma groupoid_of_pregroupoid_le (PG₁ PG₂ : pregroupoid H)
  (h : ∀f s, PG₁.property f s → PG₂.property f s) :
  groupoid_of_pregroupoid PG₁ ≤ groupoid_of_pregroupoid PG₂ :=
begin
  assume e he,
  rw mem_groupoid_of_pregroupoid at he ⊢,
  exact ⟨h _ _ he.1, h _ _ he.2⟩
end

/-- The groupoid of all local homeomorphisms on a topological space H -/
def continuous_groupoid (H : Type*) [topological_space H] : structure_groupoid H :=
groupoid_of_pregroupoid
{ property := λf s, true,
  comp     := λf g u v hf hg huv, trivial,
  id_mem   := trivial,
  locality := λf u u_open h, trivial,
  congr    := λf g u u_open hcongr hf, trivial }

/-- Every structure groupoid is contained in the groupoid of all local homeomorphisms -/
instance : lattice.order_top (structure_groupoid H) :=
{ top    := continuous_groupoid H,
  le_top := λ u f hf, by { split; exact dec_trivial },
  ..structure_groupoid.partial_order }

end groupoid

/-- A manifold is a topological space endowed with an atlas, i.e., a set of local homeomorphisms
taking value in a model space H, called charts, such that the domains of the charts cover the whole
space. We express the covering property by chosing for each x a member `chart_at x` of the atlas
containing x in its source: in the smooth case, this is convenient to construct the tangent bundle
in an efficient way.
The model space is written as an explicit parameter as there can be several model spaces for a
given topological space. For instance, a complex manifold (modelled over ℂ^n) will also be seen
sometimes as a real manifold over ℝ^(2n).
-/
class manifold (H : Type*) [topological_space H] (M : Type*) [topological_space M] :=
(atlas            : set (local_homeomorph M H))
(chart_at         : M → local_homeomorph M H)
(mem_chart_source : ∀x, x ∈ (chart_at x).source)
(chart_mem_atlas  : ∀x, chart_at x ∈ atlas)

export manifold
attribute [simp] mem_chart_source chart_mem_atlas

section manifold

/-- Any space is a manifold modelled over itself, by just using the identity chart -/
instance manifold_model_space (H : Type*) [topological_space H] : manifold H H :=
{ atlas            := {local_homeomorph.refl H},
  chart_at         := λx, local_homeomorph.refl H,
  mem_chart_source := λx, mem_univ x,
  chart_mem_atlas  := λx, mem_singleton _ }

/-- In the trivial manifold structure of a space modelled over itself through the identity, the
atlas members are just the identity -/
@[simp] lemma model_space_atlas {H : Type*} [topological_space H] {e : local_homeomorph H H} :
  e ∈ atlas H H ↔ e = local_homeomorph.refl H :=
by simp [atlas, manifold.atlas]

/-- In the model space, chart_at is always the identity -/
@[simp] lemma chart_at_model_space_eq {H : Type*} [topological_space H] {x : H} :
  chart_at H x = local_homeomorph.refl H :=
by simpa using chart_mem_atlas H x

end manifold

/-- Sometimes, one may want to construct a manifold structure on a space which does not yet have
a topological structure, where the topology would come from the charts. For this, one needs charts
that are only local equivs, and continuity properties for their composition.
This is formalised in `manifold_core`. -/
structure manifold_core (H : Type*) [topological_space H] (M : Type*) :=
(atlas            : set (local_equiv M H))
(chart_at         : M → local_equiv M H)
(mem_chart_source : ∀x, x ∈ (chart_at x).source)
(chart_mem_atlas  : ∀x, chart_at x ∈ atlas)
(open_source : ∀e e' : local_equiv M H, e ∈ atlas → e' ∈ atlas → is_open (e.symm.trans e').source)
(continuous_to_fun : ∀e e' : local_equiv M H, e ∈ atlas → e' ∈ atlas →
                       continuous_on (e.symm.trans e').to_fun (e.symm.trans e').source)

namespace manifold_core

variables [topological_space H] (c : manifold_core H M) {e : local_equiv M H}

/-- Topology generated by a set of charts on a Type. -/
protected def to_topological_space : topological_space M :=
topological_space.generate_from $ ⋃ (e : local_equiv M H) (he : e ∈ c.atlas)
  (s : set H) (s_open : is_open s), {e.to_fun ⁻¹' s ∩ e.source}

lemma open_source' (he : e ∈ c.atlas) : @is_open M c.to_topological_space e.source :=
begin
  apply topological_space.generate_open.basic,
  simp only [exists_prop, mem_Union, mem_singleton_iff],
  refine ⟨e, he, univ, is_open_univ, _⟩,
  simp only [set.univ_inter, set.preimage_univ]
end

lemma open_target (he : e ∈ c.atlas) : is_open e.target :=
begin
  have E : e.target ∩ e.inv_fun ⁻¹' e.source = e.target :=
  subset.antisymm (inter_subset_left _ _) (λx hx, ⟨hx,
    local_equiv.target_subset_preimage_source _ hx⟩),
  simpa [local_equiv.trans_source, E] using c.open_source e e he he
end

def local_homeomorph (e : local_equiv M H) (he : e ∈ c.atlas) :
  @local_homeomorph M H c.to_topological_space _ :=
{ open_source := by convert c.open_source' he,
  open_target := by convert c.open_target he,
  continuous_to_fun := begin
    letI : topological_space M := c.to_topological_space,
    rw continuous_on_open_iff (c.open_source' he),
    assume s s_open,
    rw inter_comm,
    apply topological_space.generate_open.basic,
    simp only [exists_prop, mem_Union, mem_singleton_iff],
    exact ⟨e, he, ⟨s, s_open, rfl⟩⟩
  end,
  continuous_inv_fun := begin
    letI : topological_space M := c.to_topological_space,
    apply continuous_on_open_of_generate_from (c.open_target he),
    assume t ht,
    simp only [exists_prop, mem_Union, mem_singleton_iff] at ht,
    rcases ht with ⟨e', e'_atlas, s, s_open, ts⟩,
    rw ts,
    let f := e.symm.trans e',
    have : is_open (f.to_fun ⁻¹' s ∩ f.source),
      by simpa [inter_comm] using (continuous_on_open_iff (c.open_source e e' he e'_atlas)).1
        (c.continuous_to_fun e e' he e'_atlas) s s_open,
    have A : e'.to_fun ∘ e.inv_fun ⁻¹' s ∩ (e.target ∩ e.inv_fun ⁻¹' e'.source) =
             e.target ∩ (e'.to_fun ∘ e.inv_fun ⁻¹' s ∩ e.inv_fun ⁻¹' e'.source),
      by { rw [← inter_assoc, ← inter_assoc], congr' 1, exact inter_comm _ _ },
    simpa [local_equiv.trans_source, preimage_inter, preimage_comp.symm, A] using this
  end,
  ..e }

def to_manifold : @manifold H _ M c.to_topological_space :=
{ atlas := ⋃ (e : local_equiv M H) (he : e ∈ c.atlas), {c.local_homeomorph e he},
  chart_at := λx, c.local_homeomorph (c.chart_at x) (c.chart_mem_atlas x),
  mem_chart_source := λx, c.mem_chart_source x,
  chart_mem_atlas := λx, begin
    simp only [mem_Union, mem_singleton_iff],
    exact ⟨c.chart_at x, c.chart_mem_atlas x, rfl⟩,
  end }

end manifold_core

section has_groupoid
variables [topological_space H] [topological_space M] [manifold H M]

/-- A manifold has an atlas in a groupoid G if the change of coordinates belong to the groupoid -/
class has_groupoid {H : Type*} [topological_space H] (M : Type*) [topological_space M]
  [manifold H M] (G : structure_groupoid H) : Prop :=
(compatible : ∀{e e' : local_homeomorph M H}, e ∈ atlas H M → e' ∈ atlas H M → e.symm ≫ₕ e' ∈ G)

lemma has_groupoid_of_le {G₁ G₂ : structure_groupoid H} (h : has_groupoid M G₁) (hle : G₁ ≤ G₂) :
  has_groupoid M G₂ :=
⟨ λ e e' he he', hle ((h.compatible : _) he he') ⟩

/-- The trivial manifold structure on the model space is compatible with any groupoid -/
instance has_groupoid_model_space (H : Type*) [topological_space H] (G : structure_groupoid H) :
  has_groupoid H G :=
{ compatible := λe e' he he', begin
    replace he : e ∈ atlas H H := he,
    replace he' : e' ∈ atlas H H := he',
    rw model_space_atlas at he he',
    simp [he, he', structure_groupoid.id_mem]
  end }

/-- Any manifold structure is compatible with the groupoid of all local homeomorphisms -/
instance has_groupoid_continuous_groupoid : has_groupoid M (continuous_groupoid H) :=
⟨begin
  assume e e' he he',
  rw [continuous_groupoid, mem_groupoid_of_pregroupoid],
  simp only [and_self]
end⟩

/-- A G-diffeomorphism between two manifolds is a homeomorphism which, when read in the charts,
belongs to G. We avoid the word diffeomorph as it is too related to the smooth category, and use
structomorph instead. -/
structure structomorph (G : structure_groupoid H) (M : Type*) (M' : Type*)
  [topological_space M] [topological_space M'] [manifold H M] [manifold H M']
  extends homeomorph M M' :=
(to_fun_mem_groupoid : ∀c : local_homeomorph M H, ∀c' : local_homeomorph M' H,
  c ∈ atlas H M → c' ∈ atlas H M' → c.symm ≫ₕ to_homeomorph.to_local_homeomorph ≫ₕ c' ∈ G)

variables [topological_space M'] [topological_space M'']
{G : structure_groupoid H} [manifold H M'] [manifold H M'']

/-- The identity is a diffeomorphism of any manifold, for any groupoid. -/
def structomorph.refl (M : Type*) [topological_space M] [manifold H M]
  [has_groupoid M G] : structomorph G M M :=
{ to_fun_mem_groupoid := λc c' hc hc', begin
    change (local_homeomorph.symm c) ≫ₕ (local_homeomorph.refl M) ≫ₕ c' ∈ G,
    rw local_homeomorph.refl_trans,
    exact has_groupoid.compatible G hc hc'
  end,
  ..homeomorph.refl M }

/-- The inverse of a structomorphism is a structomorphism -/
def structomorph.symm (e : structomorph G M M') : structomorph G M' M :=
{ to_fun_mem_groupoid := begin
    assume c c' hc hc',
    have : (c'.symm ≫ₕ e.to_homeomorph.to_local_homeomorph ≫ₕ c).symm ∈ G :=
      G.inv _ (e.to_fun_mem_groupoid c' c hc' hc),
    simp at this,
    rwa [trans_symm_eq_symm_trans_symm, trans_symm_eq_symm_trans_symm, symm_symm, trans_assoc]
      at this,
  end,
  ..e.to_homeomorph.symm}

/-- The composition of structomorphisms is a structomorphism -/
def structomorph.trans (e : structomorph G M M') (e' : structomorph G M' M'') : structomorph G M M'' :=
{ to_fun_mem_groupoid := begin
    /- Let c and c' be two charts in M and M''. We want to show that e' ∘ e is smooth in these
    charts, around any point x. For this, let y = e (c⁻¹ x), and consider a chart g around y.
    Then g ∘ e ∘ c⁻¹ and c' ∘ e' ∘ g⁻¹ are both smooth as e and e' are structomorphisms, so
    their composition is smooth, and it coincides with c' ∘ e' ∘ e ∘ c⁻¹ around x. -/
    assume c c' hc hc',
    refine G.locality _ (λx hx, _),
    let f₁ := e.to_homeomorph.to_local_homeomorph,
    let f₂ := e'.to_homeomorph.to_local_homeomorph,
    let f  := (e.to_homeomorph.trans e'.to_homeomorph).to_local_homeomorph,
    have feq : f = f₁ ≫ₕ f₂ := homeomorph.trans_to_local_homeomorph _ _,
    -- define the atlas g around y
    let y := (c.symm ≫ₕ f₁).to_fun x,
    let g := chart_at H y,
    have hg₁ := chart_mem_atlas H y,
    have hg₂ := mem_chart_source H y,
    let s := (c.symm ≫ₕ f₁).source ∩ (c.symm ≫ₕ f₁).to_fun ⁻¹' g.source,
    have open_s : is_open s,
      by apply (c.symm ≫ₕ f₁).continuous_to_fun.preimage_open_of_open; apply open_source,
    have : x ∈ s,
    { split,
      { simp only [trans_source, preimage_univ, inter_univ, homeomorph.to_local_homeomorph_source],
        rw trans_source at hx,
        exact hx.1 },
      { exact hg₂ } },
    refine ⟨s, open_s, ⟨this, _⟩⟩,
    let F₁ := (c.symm ≫ₕ f₁ ≫ₕ g) ≫ₕ (g.symm ≫ₕ f₂ ≫ₕ c'),
    have A : F₁ ∈ G :=
      G.comp _ _ (e.to_fun_mem_groupoid c g hc hg₁) (e'.to_fun_mem_groupoid g c' hg₁ hc'),
    let F₂ := (c.symm ≫ₕ f ≫ₕ c').restr s,
    have : F₁ ≈ F₂ := calc
      F₁ ≈ c.symm ≫ₕ f₁ ≫ₕ (g ≫ₕ g.symm) ≫ₕ f₂ ≫ₕ c' : by simp [F₁, trans_assoc]
      ... ≈ c.symm ≫ₕ f₁ ≫ₕ (of_set g.source g.open_source) ≫ₕ f₂ ≫ₕ c' :
        by simp [eq_on_source_trans, trans_self_symm g]
      ... ≈ ((c.symm ≫ₕ f₁) ≫ₕ (of_set g.source g.open_source)) ≫ₕ (f₂ ≫ₕ c') :
        by simp [trans_assoc]
      ... ≈ ((c.symm ≫ₕ f₁).restr s) ≫ₕ (f₂ ≫ₕ c') : by simp [s, trans_of_set']
      ... ≈ ((c.symm ≫ₕ f₁) ≫ₕ (f₂ ≫ₕ c')).restr s : by simp [restr_trans]
      ... ≈ (c.symm ≫ₕ (f₁ ≫ₕ f₂) ≫ₕ c').restr s : by simp [eq_on_source_restr, trans_assoc]
      ... ≈ F₂ : by simp [F₂, feq],
    have : F₂ ∈ G := G.eq_on_source F₁ F₂ A (setoid.symm this),
    exact this
  end,
  ..homeomorph.trans e.to_homeomorph e'.to_homeomorph }

end has_groupoid
