/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Heather Macbeth
-/
import topology.fiber_bundle.trivialization

/-!
# Fiber bundles

Mathematically, a (topological) fiber bundle with fiber `F` over a base `B` is a space projecting on
`B` for which the fibers are all homeomorphic to `F`, such that the local situation around each
point is a direct product.

In our formalism, a fiber bundle is by definition the type
`bundle.total_space E` where `E : B → Type*` is a function associating to
`x : B` the fiber over `x`. This type `bundle.total_space E` is just a type synonym for
`Σ (x : B), E x`, with the interest that one can put another topology than on `Σ (x : B), E x`
which has the disjoint union topology.

To have a fiber bundle structure on `bundle.total_space E`, one should
additionally have the following data:

* `F` should be a topological space;
* There should be a topology on `bundle.total_space E`, for which the projection to `B` is
a fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological space, and the injection
from `E x` to `bundle.total_space F E` should be an embedding;
* There should be a distinguished set of bundle trivializations, the "trivialization atlas"
* There should be a choice of bundle trivialization at each point, which belongs to this atlas.

If all these conditions are satisfied, we register the typeclass `fiber_bundle F E`.

It is in general nontrivial to construct a fiber bundle. A way is to start from the knowledge of
how changes of local trivializations act on the fiber. From this, one can construct the total space
of the bundle and its topology by a suitable gluing construction. The main content of this file is
an implementation of this construction: starting from an object of type
`fiber_bundle_core` registering the trivialization changes, one gets the corresponding
fiber bundle and projection.

Similarly we implement the object `fiber_prebundle` which allows to define a topological
fiber bundle from trivializations given as local equivalences with minimum additional properties.

## Main definitions

### Basic definitions

* `fiber_bundle F E` : Structure saying that `E : B → Type*` is a fiber bundle with fiber `F`.

### Construction of a bundle from trivializations

* `bundle.total_space E` is a type synonym for `Σ (x : B), E x`, that we can endow with a suitable
  topology.
* `fiber_bundle_core ι B F` : structure registering how changes of coordinates act
  on the fiber `F` above open subsets of `B`, where local trivializations are indexed by `ι`.

Let `Z : fiber_bundle_core ι B F`. Then we define

* `Z.fiber x`     : the fiber above `x`, homeomorphic to `F` (and defeq to `F` as a type).
* `Z.total_space` : the total space of `Z`, defined as a `Type` as `Σ (b : B), F`, but with a
  twisted topology coming from the fiber bundle structure. It is (reducibly) the same as
  `bundle.total_space Z.fiber`.
* `Z.proj`        : projection from `Z.total_space` to `B`. It is continuous.
* `Z.local_triv i`: for `i : ι`, bundle trivialization above the set `Z.base_set i`, which is an
                    open set in `B`.

* `fiber_prebundle F E` : structure registering a cover of prebundle trivializations
  and requiring that the relative transition maps are local homeomorphisms.
* `fiber_prebundle.total_space_topology a` : natural topology of the total space, making
  the prebundle into a bundle.

## Implementation notes

### Data vs mixins

For both fiber and vector bundles, one faces a choice: should the definition state the *existence*
of local trivializations (a propositional typeclass), or specify a fixed atlas of trivializations (a
typeclass containing data)?

In their initial mathlib implementations, both fiber and vector bundles were defined
propositionally. For vector bundles, this turns out to be mathematically wrong: in infinite
dimension, the transition function between two trivializations is not automatically continuous as a
map from the base `B` to the endomorphisms `F →L[R] F` of the fiber (considered with the
operator-norm topology), and so the definition needs to be modified by restricting consideration to
a family of trivializations (constituting the data) which are all mutually-compatible in this sense.
The PRs #13052 and #13175 implemented this change.

There is still the choice about whether to hold this data at the level of fiber bundles or of vector
bundles. As of PR #17505, the data is all held in `fiber_bundle`, with `vector_bundle` a
(propositional) mixin stating fiberwise-linearity.

This allows bundles to carry instances of typeclasses in which the scalar field, `R`, does not
appear as a parameter. Notably, we would like a vector bundle over `R` with fiber `F` over base `B`
to be a `charted_space (B × F)`, with the trivializations providing the charts. This would be a
dangerous instance for typeclass inference, because `R` does not appear as a parameter in
`charted_space (B × F)`. But if the data of the trivializations is held in `fiber_bundle`, then a
fiber bundle with fiber `F` over base `B` can be a `charted_space (B × F)`, and this is safe for
typeclass inference.

We expect that this choice of definition will also streamline constructions of fiber bundles with
similar underlying structure (e.g., the same bundle being both a real and complex vector bundle).

### Core construction

A fiber bundle with fiber `F` over a base `B` is a family of spaces isomorphic to `F`,
indexed by `B`, which is locally trivial in the following sense: there is a covering of `B` by open
sets such that, on each such open set `s`, the bundle is isomorphic to `s × F`.

To construct a fiber bundle formally, the main data is what happens when one changes trivializations
from `s × F` to `s' × F` on `s ∩ s'`: one should get a family of homeomorphisms of `F`, depending
continuously on the base point, satisfying basic compatibility conditions (cocycle property).
Useful classes of bundles can then be specified by requiring that these homeomorphisms of `F`
belong to some subgroup, preserving some structure (the "structure group of the bundle"): then
these structures are inherited by the fibers of the bundle.

Given such trivialization change data (encoded below in a structure called
`fiber_bundle_core`), one can construct the fiber bundle. The intrinsic canonical
mathematical construction is the following.
The fiber above `x` is the disjoint union of `F` over all trivializations, modulo the gluing
identifications: one gets a fiber which is isomorphic to `F`, but non-canonically
(each choice of one of the trivializations around `x` gives such an isomorphism). Given a
trivialization over a set `s`, one gets an isomorphism between `s × F` and `proj^{-1} s`, by using
the identification corresponding to this trivialization. One chooses the topology on the bundle that
makes all of these into homeomorphisms.

For the practical implementation, it turns out to be more convenient to avoid completely the
gluing and quotienting construction above, and to declare above each `x` that the fiber is `F`,
but thinking that it corresponds to the `F` coming from the choice of one trivialization around `x`.
This has several practical advantages:
* without any work, one gets a topological space structure on the fiber. And if `F` has more
structure it is inherited for free by the fiber.
* In the case of the tangent bundle of manifolds, this implies that on vector spaces the derivative
(from `F` to `F`) and the manifold derivative (from `tangent_space I x` to `tangent_space I' (f x)`)
are equal.

A drawback is that some silly constructions will typecheck: in the case of the tangent bundle, one
can add two vectors in different tangent spaces (as they both are elements of `F` from the point of
view of Lean). To solve this, one could mark the tangent space as irreducible, but then one would
lose the identification of the tangent space to `F` with `F`. There is however a big advantage of
this situation: even if Lean can not check that two basepoints are defeq, it will accept the fact
that the tangent spaces are the same. For instance, if two maps `f` and `g` are locally inverse to
each other, one can express that the composition of their derivatives is the identity of
`tangent_space I x`. One could fear issues as this composition goes from `tangent_space I x` to
`tangent_space I (g (f x))` (which should be the same, but should not be obvious to Lean
as it does not know that `g (f x) = x`). As these types are the same to Lean (equal to `F`), there
are in fact no dependent type difficulties here!

For this construction of a fiber bundle from a `fiber_bundle_core`, we should thus
choose for each `x` one specific trivialization around it. We include this choice in the definition
of the `fiber_bundle_core`, as it makes some constructions more
functorial and it is a nice way to say that the trivializations cover the whole space `B`.

With this definition, the type of the fiber bundle space constructed from the core data is just
`Σ (b : B), F `, but the topology is not the product one, in general.

We also take the indexing type (indexing all the trivializations) as a parameter to the fiber bundle
core: it could always be taken as a subtype of all the maps from open subsets of `B` to continuous
maps of `F`, but in practice it will sometimes be something else. For instance, on a manifold, one
will use the set of charts as a good parameterization for the trivializations of the tangent bundle.
Or for the pullback of a `fiber_bundle_core`, the indexing type will be the same as
for the initial bundle.

## Tags
Fiber bundle, topological bundle, structure group
-/

variables {ι : Type*} {B : Type*} {F : Type*}

open topological_space filter set bundle
open_locale topology classical bundle

attribute [mfld_simps] total_space.proj total_space_mk coe_fst coe_snd coe_snd_map_apply
  coe_snd_map_smul total_space.mk_cast

/-! ### General definition of fiber bundles -/

section fiber_bundle

variables (F) [topological_space B] [topological_space F] (E : B → Type*)
  [topological_space (total_space E)] [∀ b, topological_space (E b)]

/-- A (topological) fiber bundle with fiber `F` over a base `B` is a space projecting on `B`
for which the fibers are all homeomorphic to `F`, such that the local situation around each point
is a direct product. -/
class fiber_bundle :=
(total_space_mk_inducing [] : ∀ (b : B), inducing (@total_space_mk B E b))
(trivialization_atlas [] : set (trivialization F (π E)))
(trivialization_at [] : B → trivialization F (π E))
(mem_base_set_trivialization_at [] : ∀ b : B, b ∈ (trivialization_at b).base_set)
(trivialization_mem_atlas [] : ∀ b : B, trivialization_at b ∈ trivialization_atlas)

export fiber_bundle

variables {F E}

/-- Given a type `E` equipped with a fiber bundle structure, this is a `Prop` typeclass
for trivializations of `E`, expressing that a trivialization is in the designated atlas for the
bundle.  This is needed because lemmas about the linearity of trivializations or the continuity (as
functions to `F →L[R] F`, where `F` is the model fiber) of the transition functions are only
expected to hold for trivializations in the designated atlas. -/
@[mk_iff]
class mem_trivialization_atlas [fiber_bundle F E] (e : trivialization F (π E)) : Prop :=
(out : e ∈ trivialization_atlas F E)

instance [fiber_bundle F E] (b : B) : mem_trivialization_atlas (trivialization_at F E b) :=
{ out := trivialization_mem_atlas F E b }

namespace fiber_bundle
variables (F) {E} [fiber_bundle F E]

lemma map_proj_nhds (x : total_space E) :
  map (π E) (𝓝 x) = 𝓝 x.proj :=
(trivialization_at F E x.proj).map_proj_nhds $
  (trivialization_at F E x.proj).mem_source.2 $ mem_base_set_trivialization_at F E x.proj

variables (E)

/-- The projection from a fiber bundle to its base is continuous. -/
@[continuity] lemma continuous_proj : continuous (π E) :=
continuous_iff_continuous_at.2 $ λ x, (map_proj_nhds F x).le

/-- The projection from a fiber bundle to its base is an open map. -/
lemma is_open_map_proj : is_open_map (π E) :=
is_open_map.of_nhds_le $ λ x, (map_proj_nhds F x).ge

/-- The projection from a fiber bundle with a nonempty fiber to its base is a surjective
map. -/
lemma surjective_proj [nonempty F] : function.surjective (π E) :=
λ b, let ⟨p, _, hpb⟩ :=
  (trivialization_at F E b).proj_surj_on_base_set (mem_base_set_trivialization_at F E b) in ⟨p, hpb⟩

/-- The projection from a fiber bundle with a nonempty fiber to its base is a quotient
map. -/
lemma quotient_map_proj [nonempty F] : quotient_map (π E) :=
(is_open_map_proj F E).to_quotient_map (continuous_proj F E) (surjective_proj F E)

lemma continuous_total_space_mk (x : B) : continuous (@total_space_mk B E x) :=
(total_space_mk_inducing F E x).continuous

end fiber_bundle

variables (F E)

/-- If `E` is a fiber bundle over a conditionally complete linear order,
then it is trivial over any closed interval. -/
lemma fiber_bundle.exists_trivialization_Icc_subset
  [conditionally_complete_linear_order B] [order_topology B] [fiber_bundle F E] (a b : B) :
  ∃ e : trivialization F (π E), Icc a b ⊆ e.base_set :=
begin
  classical,
  obtain ⟨ea, hea⟩ : ∃ ea : trivialization F (π E), a ∈ ea.base_set :=
    ⟨trivialization_at F E a, mem_base_set_trivialization_at F E a⟩,
  -- If `a < b`, then `[a, b] = ∅`, and the statement is trivial
  cases le_or_lt a b with hab hab; [skip, exact ⟨ea, by simp *⟩],
  /- Let `s` be the set of points `x ∈ [a, b]` such that `E` is trivializable over `[a, x]`.
  We need to show that `b ∈ s`. Let `c = Sup s`. We will show that `c ∈ s` and `c = b`. -/
  set s : set B := {x ∈ Icc a b | ∃ e : trivialization F (π E), Icc a x ⊆ e.base_set},
  have ha : a ∈ s, from ⟨left_mem_Icc.2 hab, ea, by simp [hea]⟩,
  have sne : s.nonempty := ⟨a, ha⟩,
  have hsb : b ∈ upper_bounds s, from λ x hx, hx.1.2,
  have sbd : bdd_above s := ⟨b, hsb⟩,
  set c := Sup s,
  have hsc : is_lub s c, from is_lub_cSup sne sbd,
  have hc : c ∈ Icc a b, from ⟨hsc.1 ha, hsc.2 hsb⟩,
  obtain ⟨-, ec : trivialization F (π E), hec : Icc a c ⊆ ec.base_set⟩ : c ∈ s,
  { cases hc.1.eq_or_lt with heq hlt, { rwa ← heq },
    refine ⟨hc, _⟩,
    /- In order to show that `c ∈ s`, consider a trivialization `ec` of `proj` over a neighborhood
    of `c`. Its base set includes `(c', c]` for some `c' ∈ [a, c)`. -/
    obtain ⟨ec, hc⟩ : ∃ ec : trivialization F (π E), c ∈ ec.base_set :=
      ⟨trivialization_at F E c, mem_base_set_trivialization_at F E c⟩,
    obtain ⟨c', hc', hc'e⟩ : ∃ c' ∈ Ico a c, Ioc c' c ⊆ ec.base_set :=
      (mem_nhds_within_Iic_iff_exists_mem_Ico_Ioc_subset hlt).1
        (mem_nhds_within_of_mem_nhds $ is_open.mem_nhds ec.open_base_set hc),
    /- Since `c' < c = Sup s`, there exists `d ∈ s ∩ (c', c]`. Let `ead` be a trivialization of
    `proj` over `[a, d]`. Then we can glue `ead` and `ec` into a trivialization over `[a, c]`. -/
    obtain ⟨d, ⟨hdab, ead, had⟩, hd⟩ : ∃ d ∈ s, d ∈ Ioc c' c := hsc.exists_between hc'.2,
    refine ⟨ead.piecewise_le ec d (had ⟨hdab.1, le_rfl⟩) (hc'e hd), subset_ite.2 _⟩,
    refine ⟨λ x hx, had ⟨hx.1.1, hx.2⟩, λ x hx, hc'e ⟨hd.1.trans (not_le.1 hx.2), hx.1.2⟩⟩ },
  /- So, `c ∈ s`. Let `ec` be a trivialization of `proj` over `[a, c]`.  If `c = b`, then we are
  done. Otherwise we show that `proj` can be trivialized over a larger interval `[a, d]`,
  `d ∈ (c, b]`, hence `c` is not an upper bound of `s`. -/
  cases hc.2.eq_or_lt with heq hlt, { exact ⟨ec, heq ▸ hec⟩ },
  rsuffices ⟨d, hdcb, hd⟩ : ∃ (d ∈ Ioc c b) (e : trivialization F (π E)), Icc a d ⊆ e.base_set,
  { exact ((hsc.1 ⟨⟨hc.1.trans hdcb.1.le, hdcb.2⟩, hd⟩).not_lt hdcb.1).elim },
  /- Since the base set of `ec` is open, it includes `[c, d)` (hence, `[a, d)`) for some
  `d ∈ (c, b]`. -/
  obtain ⟨d, hdcb, hd⟩ : ∃ d ∈ Ioc c b, Ico c d ⊆ ec.base_set :=
    (mem_nhds_within_Ici_iff_exists_mem_Ioc_Ico_subset hlt).1
      (mem_nhds_within_of_mem_nhds $ is_open.mem_nhds ec.open_base_set (hec ⟨hc.1, le_rfl⟩)),
  have had : Ico a d ⊆ ec.base_set,
    from Ico_subset_Icc_union_Ico.trans (union_subset hec hd),
  by_cases he : disjoint (Iio d) (Ioi c),
  { /- If `(c, d) = ∅`, then let `ed` be a trivialization of `proj` over a neighborhood of `d`.
    Then the disjoint union of `ec` restricted to `(-∞, d)` and `ed` restricted to `(c, ∞)` is
    a trivialization over `[a, d]`. -/
    obtain ⟨ed, hed⟩ : ∃ ed : trivialization F (π E), d ∈ ed.base_set :=
      ⟨trivialization_at F E d, mem_base_set_trivialization_at F E d⟩,
    refine ⟨d, hdcb, (ec.restr_open (Iio d) is_open_Iio).disjoint_union
      (ed.restr_open (Ioi c) is_open_Ioi) (he.mono (inter_subset_right _ _)
        (inter_subset_right _ _)), λ x hx, _⟩,
    rcases hx.2.eq_or_lt with rfl|hxd,
    exacts [or.inr ⟨hed, hdcb.1⟩, or.inl ⟨had ⟨hx.1, hxd⟩, hxd⟩] },
  { /- If `(c, d)` is nonempty, then take `d' ∈ (c, d)`. Since the base set of `ec` includes
    `[a, d)`, it includes `[a, d'] ⊆ [a, d)` as well. -/
    rw [disjoint_left] at he, push_neg at he, rcases he with ⟨d', hdd' : d' < d, hd'c⟩,
    exact ⟨d', ⟨hd'c, hdd'.le.trans hdcb.2⟩, ec, (Icc_subset_Ico_right hdd').trans had⟩ }
end

end fiber_bundle

/-! ### Core construction for constructing fiber bundles -/

/-- Core data defining a locally trivial bundle with fiber `F` over a topological
space `B`. Note that "bundle" is used in its mathematical sense. This is the (computer science)
bundled version, i.e., all the relevant data is contained in the following structure. A family of
local trivializations is indexed by a type `ι`, on open subsets `base_set i` for each `i : ι`.
Trivialization changes from `i` to `j` are given by continuous maps `coord_change i j` from
`base_set i ∩ base_set j` to the set of homeomorphisms of `F`, but we express them as maps
`B → F → F` and require continuity on `(base_set i ∩ base_set j) × F` to avoid the topology on the
space of continuous maps on `F`. -/
@[nolint has_nonempty_instance]
structure fiber_bundle_core (ι : Type*) (B : Type*) [topological_space B]
  (F : Type*) [topological_space F] :=
(base_set          : ι → set B)
(is_open_base_set  : ∀ i, is_open (base_set i))
(index_at          : B → ι)
(mem_base_set_at   : ∀ x, x ∈ base_set (index_at x))
(coord_change      : ι → ι → B → F → F)
(coord_change_self : ∀ i, ∀ x ∈ base_set i, ∀ v, coord_change i i x v = v)
(continuous_on_coord_change : ∀ i j, continuous_on (λp : B × F, coord_change i j p.1 p.2)
                                               (((base_set i) ∩ (base_set j)) ×ˢ univ))
(coord_change_comp : ∀ i j k, ∀ x ∈ (base_set i) ∩ (base_set j) ∩ (base_set k), ∀ v,
  (coord_change j k x) (coord_change i j x v) = coord_change i k x v)

namespace fiber_bundle_core

variables [topological_space B] [topological_space F] (Z : fiber_bundle_core ι B F)

include Z

/-- The index set of a fiber bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments has_nonempty_instance]
def index := ι

/-- The base space of a fiber bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments, reducible]
def base := B

/-- The fiber of a fiber bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_nonempty_instance]
def fiber (x : B) := F

section fiber_instances
local attribute [reducible] fiber

instance topological_space_fiber (x : B) : topological_space (Z.fiber x) := by apply_instance

end fiber_instances

/-- The total space of the fiber bundle, as a convenience function for dot notation.
It is by definition equal to `bundle.total_space Z.fiber`, a.k.a. `Σ x, Z.fiber x` but with a
different name for typeclass inference. -/
@[nolint unused_arguments, reducible]
def total_space := bundle.total_space Z.fiber

/-- The projection from the total space of a fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps] def proj : Z.total_space → B := bundle.total_space.proj

/-- Local homeomorphism version of the trivialization change. -/
def triv_change (i j : ι) : local_homeomorph (B × F) (B × F) :=
{ source      := (Z.base_set i ∩ Z.base_set j) ×ˢ univ,
  target      := (Z.base_set i ∩ Z.base_set j) ×ˢ univ,
  to_fun      := λp, ⟨p.1, Z.coord_change i j p.1 p.2⟩,
  inv_fun     := λp, ⟨p.1, Z.coord_change j i p.1 p.2⟩,
  map_source' := λp hp, by simpa using hp,
  map_target' := λp hp, by simpa using hp,
  left_inv'   := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx,
    rw [Z.coord_change_comp, Z.coord_change_self],
    { exact hx.1 },
    { simp [hx] }
  end,
  right_inv'  := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx,
    rw [Z.coord_change_comp, Z.coord_change_self],
    { exact hx.2 },
    { simp [hx] },
  end,
  open_source :=
    (is_open.inter (Z.is_open_base_set i) (Z.is_open_base_set j)).prod is_open_univ,
  open_target :=
    (is_open.inter (Z.is_open_base_set i) (Z.is_open_base_set j)).prod is_open_univ,
  continuous_to_fun  :=
    continuous_on.prod continuous_fst.continuous_on (Z.continuous_on_coord_change i j),
  continuous_inv_fun := by simpa [inter_comm]
    using continuous_on.prod continuous_fst.continuous_on (Z.continuous_on_coord_change j i) }

@[simp, mfld_simps] lemma mem_triv_change_source (i j : ι) (p : B × F) :
  p ∈ (Z.triv_change i j).source ↔ p.1 ∈ Z.base_set i ∩ Z.base_set j :=
by { erw [mem_prod], simp }

/-- Associate to a trivialization index `i : ι` the corresponding trivialization, i.e., a bijection
between `proj ⁻¹ (base_set i)` and `base_set i × F`. As the fiber above `x` is `F` but read in the
chart with index `index_at x`, the trivialization in the fiber above x is by definition the
coordinate change from i to `index_at x`, so it depends on `x`.
The local trivialization will ultimately be a local homeomorphism. For now, we only introduce the
local equiv version, denoted with a prime. In further developments, avoid this auxiliary version,
and use `Z.local_triv` instead.
-/
def local_triv_as_local_equiv (i : ι) : local_equiv Z.total_space (B × F) :=
{ source      := Z.proj ⁻¹' (Z.base_set i),
  target      := Z.base_set i ×ˢ univ,
  inv_fun     := λp, ⟨p.1, Z.coord_change i (Z.index_at p.1) p.1 p.2⟩,
  to_fun      := λp, ⟨p.1, Z.coord_change (Z.index_at p.1) i p.1 p.2⟩,
  map_source' := λp hp,
    by simpa only [set.mem_preimage, and_true, set.mem_univ, set.prod_mk_mem_set_prod_eq] using hp,
  map_target' := λp hp,
    by simpa only [set.mem_preimage, and_true, set.mem_univ, set.mem_prod] using hp,
  left_inv'   := begin
    rintros ⟨x, v⟩ hx,
    change x ∈ Z.base_set i at hx,
    dsimp only,
    rw [Z.coord_change_comp, Z.coord_change_self],
    { exact Z.mem_base_set_at _ },
    { simp only [hx, mem_inter_iff, and_self, mem_base_set_at] }
  end,
  right_inv' := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, and_true, mem_univ] at hx,
    rw [Z.coord_change_comp, Z.coord_change_self],
    { exact hx },
    { simp only [hx, mem_inter_iff, and_self, mem_base_set_at] }
  end }

variable (i : ι)

lemma mem_local_triv_as_local_equiv_source (p : Z.total_space) :
  p ∈ (Z.local_triv_as_local_equiv i).source ↔ p.1 ∈ Z.base_set i :=
iff.rfl

lemma mem_local_triv_as_local_equiv_target (p : B × F) :
  p ∈ (Z.local_triv_as_local_equiv i).target ↔ p.1 ∈ Z.base_set i :=
by { erw [mem_prod], simp only [and_true, mem_univ] }

lemma local_triv_as_local_equiv_apply (p : Z.total_space) :
  (Z.local_triv_as_local_equiv i) p = ⟨p.1, Z.coord_change (Z.index_at p.1) i p.1 p.2⟩ := rfl

/-- The composition of two local trivializations is the trivialization change Z.triv_change i j. -/
lemma local_triv_as_local_equiv_trans (i j : ι) :
  (Z.local_triv_as_local_equiv i).symm.trans
    (Z.local_triv_as_local_equiv j) ≈ (Z.triv_change i j).to_local_equiv :=
begin
  split,
  { ext x, simp only [mem_local_triv_as_local_equiv_target] with mfld_simps, refl, },
  { rintros ⟨x, v⟩ hx,
    simp only [triv_change, local_triv_as_local_equiv, local_equiv.symm, true_and, prod.mk.inj_iff,
      prod_mk_mem_set_prod_eq, local_equiv.trans_source, mem_inter_iff, and_true, mem_preimage,
      proj, mem_univ, local_equiv.coe_mk, eq_self_iff_true, local_equiv.coe_trans,
      total_space.proj] at hx ⊢,
    simp only [Z.coord_change_comp, hx, mem_inter_iff, and_self, mem_base_set_at], }
end

/-- Topological structure on the total space of a fiber bundle created from core, designed so
that all the local trivialization are continuous. -/
instance to_topological_space : topological_space (bundle.total_space Z.fiber) :=
topological_space.generate_from $ ⋃ (i : ι) (s : set (B × F)) (s_open : is_open s),
  {(Z.local_triv_as_local_equiv i).source ∩ (Z.local_triv_as_local_equiv i) ⁻¹' s}

variables (b : B) (a : F)

lemma open_source' (i : ι) : is_open (Z.local_triv_as_local_equiv i).source :=
begin
  apply topological_space.generate_open.basic,
  simp only [exists_prop, mem_Union, mem_singleton_iff],
  refine ⟨i, Z.base_set i ×ˢ univ, (Z.is_open_base_set i).prod is_open_univ, _⟩,
  ext p,
  simp only [local_triv_as_local_equiv_apply, prod_mk_mem_set_prod_eq, mem_inter_iff, and_self,
    mem_local_triv_as_local_equiv_source, and_true, mem_univ, mem_preimage],
end

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def local_triv (i : ι) : trivialization F Z.proj :=
{ base_set      := Z.base_set i,
  open_base_set := Z.is_open_base_set i,
  source_eq     := rfl,
  target_eq     := rfl,
  proj_to_fun   := λ p hp, by { simp only with mfld_simps, refl },
  open_source := Z.open_source' i,
  open_target := (Z.is_open_base_set i).prod is_open_univ,
  continuous_to_fun := begin
    rw continuous_on_open_iff (Z.open_source' i),
    assume s s_open,
    apply topological_space.generate_open.basic,
    simp only [exists_prop, mem_Union, mem_singleton_iff],
    exact ⟨i, s, s_open, rfl⟩
  end,
  continuous_inv_fun := begin
    apply continuous_on_open_of_generate_from ((Z.is_open_base_set i).prod is_open_univ),
    assume t ht,
    simp only [exists_prop, mem_Union, mem_singleton_iff] at ht,
    obtain ⟨j, s, s_open, ts⟩ : ∃ j s, is_open s ∧ t =
      (local_triv_as_local_equiv Z j).source ∩ (local_triv_as_local_equiv Z j) ⁻¹' s := ht,
    rw ts,
    simp only [local_equiv.right_inv, preimage_inter, local_equiv.left_inv],
    let e := Z.local_triv_as_local_equiv i,
    let e' := Z.local_triv_as_local_equiv j,
    let f := e.symm.trans e',
    have : is_open (f.source ∩ f ⁻¹' s),
    { rw [(Z.local_triv_as_local_equiv_trans i j).source_inter_preimage_eq],
      exact (continuous_on_open_iff (Z.triv_change i j).open_source).1
        ((Z.triv_change i j).continuous_on) _ s_open },
    convert this using 1,
    dsimp [local_equiv.trans_source],
    rw [← preimage_comp, inter_assoc],
    refl,
  end,
  to_local_equiv := Z.local_triv_as_local_equiv i }

/-- Preferred local trivialization of a fiber bundle constructed from core, at a given point, as
a bundle trivialization -/
def local_triv_at (b : B) : trivialization F (π Z.fiber) :=
Z.local_triv (Z.index_at b)

@[simp, mfld_simps] lemma local_triv_at_def (b : B) :
  Z.local_triv (Z.index_at b) = Z.local_triv_at b := rfl

/-- If an element of `F` is invariant under all coordinate changes, then one can define a
corresponding section of the fiber bundle, which is continuous. This applies in particular to the
zero section of a vector bundle. Another example (not yet defined) would be the identity
section of the endomorphism bundle of a vector bundle. -/
lemma continuous_const_section (v : F)
  (h : ∀ i j, ∀ x ∈ (Z.base_set i) ∩ (Z.base_set j), Z.coord_change i j x v = v) :
  continuous (show B → Z.total_space, from λ x, ⟨x, v⟩) :=
begin
  apply continuous_iff_continuous_at.2 (λ x, _),
  have A : Z.base_set (Z.index_at x) ∈ 𝓝 x :=
    is_open.mem_nhds (Z.is_open_base_set (Z.index_at x)) (Z.mem_base_set_at x),
  apply ((Z.local_triv_at x).to_local_homeomorph.continuous_at_iff_continuous_at_comp_left _).2,
  { simp only [(∘)] with mfld_simps,
    apply continuous_at_id.prod,
    have : continuous_on (λ (y : B), v) (Z.base_set (Z.index_at x)) := continuous_on_const,
    apply (this.congr _).continuous_at A,
    assume y hy,
    simp only [h, hy, mem_base_set_at] with mfld_simps },
  { exact A }
end

@[simp, mfld_simps] lemma local_triv_as_local_equiv_coe :
  ⇑(Z.local_triv_as_local_equiv i) = Z.local_triv i := rfl

@[simp, mfld_simps] lemma local_triv_as_local_equiv_source :
  (Z.local_triv_as_local_equiv i).source = (Z.local_triv i).source := rfl

@[simp, mfld_simps] lemma local_triv_as_local_equiv_target :
  (Z.local_triv_as_local_equiv i).target = (Z.local_triv i).target := rfl

@[simp, mfld_simps] lemma local_triv_as_local_equiv_symm :
  (Z.local_triv_as_local_equiv i).symm = (Z.local_triv i).to_local_equiv.symm := rfl

@[simp, mfld_simps] lemma base_set_at : Z.base_set i = (Z.local_triv i).base_set := rfl

@[simp, mfld_simps] lemma local_triv_apply (p : Z.total_space) :
  (Z.local_triv i) p = ⟨p.1, Z.coord_change (Z.index_at p.1) i p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma local_triv_at_apply (p : Z.total_space) :
  ((Z.local_triv_at p.1) p) = ⟨p.1, p.2⟩ :=
by { rw [local_triv_at, local_triv_apply, coord_change_self], exact Z.mem_base_set_at p.1 }

@[simp, mfld_simps] lemma local_triv_at_apply_mk (b : B) (a : F) :
  ((Z.local_triv_at b) ⟨b, a⟩) = ⟨b, a⟩ :=
Z.local_triv_at_apply _

@[simp, mfld_simps] lemma mem_local_triv_source (p : Z.total_space) :
  p ∈ (Z.local_triv i).source ↔ p.1 ∈ (Z.local_triv i).base_set := iff.rfl

@[simp, mfld_simps] lemma mem_local_triv_at_source (p : Z.total_space) (b : B) :
  p ∈ (Z.local_triv_at b).source ↔ p.1 ∈ (Z.local_triv_at b).base_set := iff.rfl

@[simp, mfld_simps] lemma mem_source_at : (⟨b, a⟩ : Z.total_space) ∈ (Z.local_triv_at b).source :=
by { rw [local_triv_at, mem_local_triv_source], exact Z.mem_base_set_at b }

@[simp, mfld_simps] lemma mem_local_triv_target (p : B × F) :
  p ∈ (Z.local_triv i).target ↔ p.1 ∈ (Z.local_triv i).base_set :=
trivialization.mem_target _

@[simp, mfld_simps] lemma mem_local_triv_at_target (p : B × F) (b : B) :
  p ∈ (Z.local_triv_at b).target ↔ p.1 ∈ (Z.local_triv_at b).base_set :=
trivialization.mem_target _

@[simp, mfld_simps] lemma local_triv_symm_apply (p : B × F) :
  (Z.local_triv i).to_local_homeomorph.symm p =
    ⟨p.1, Z.coord_change i (Z.index_at p.1) p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma mem_local_triv_at_base_set (b : B) :
  b ∈ (Z.local_triv_at b).base_set :=
by { rw [local_triv_at, ←base_set_at], exact Z.mem_base_set_at b, }

/-- The inclusion of a fiber into the total space is a continuous map. -/
@[continuity]
lemma continuous_total_space_mk (b : B) :
  continuous (total_space_mk b : Z.fiber b → bundle.total_space Z.fiber) :=
begin
  rw [continuous_iff_le_induced, fiber_bundle_core.to_topological_space],
  apply le_induced_generate_from,
  simp only [total_space_mk, mem_Union, mem_singleton_iff, local_triv_as_local_equiv_source,
    local_triv_as_local_equiv_coe],
  rintros s ⟨i, t, ht, rfl⟩,
  rw [←((Z.local_triv i).source_inter_preimage_target_inter t), preimage_inter, ←preimage_comp,
    trivialization.source_eq],
  apply is_open.inter,
  { simp only [total_space.proj, proj, ←preimage_comp],
    by_cases (b ∈ (Z.local_triv i).base_set),
    { rw preimage_const_of_mem h, exact is_open_univ, },
    { rw preimage_const_of_not_mem h, exact is_open_empty, }},
  { simp only [function.comp, local_triv_apply],
    rw [preimage_inter, preimage_comp],
    by_cases (b ∈ Z.base_set i),
    { have hc : continuous (λ (x : Z.fiber b), (Z.coord_change (Z.index_at b) i b) x),
        from (Z.continuous_on_coord_change (Z.index_at b) i).comp_continuous
          (continuous_const.prod_mk continuous_id) (λ x, ⟨⟨Z.mem_base_set_at b, h⟩, mem_univ x⟩),
      exact (((Z.local_triv i).open_target.inter ht).preimage (continuous.prod.mk b)).preimage hc },
    { rw [(Z.local_triv i).target_eq, ←base_set_at, mk_preimage_prod_right_eq_empty h,
        preimage_empty, empty_inter],
      exact is_open_empty, }}
end

/-- A fiber bundle constructed from core is indeed a fiber bundle. -/
instance fiber_bundle : fiber_bundle F Z.fiber :=
{ total_space_mk_inducing := λ b, ⟨ begin refine le_antisymm _ (λ s h, _),
    { rw ←continuous_iff_le_induced,
      exact continuous_total_space_mk Z b, },
    { refine is_open_induced_iff.mpr ⟨(Z.local_triv_at b).source ∩ (Z.local_triv_at b) ⁻¹'
        ((Z.local_triv_at b).base_set ×ˢ s), (continuous_on_open_iff
        (Z.local_triv_at b).open_source).mp (Z.local_triv_at b).continuous_to_fun _
        ((Z.local_triv_at b).open_base_set.prod h), _⟩,
      rw [preimage_inter, ←preimage_comp, function.comp],
      simp only [total_space_mk],
      refine ext_iff.mpr (λ a, ⟨λ ha, _, λ ha, ⟨Z.mem_base_set_at b, _⟩⟩),
      { simp only [mem_prod, mem_preimage, mem_inter_iff, local_triv_at_apply_mk] at ha,
        exact ha.2.2, },
      { simp only [mem_prod, mem_preimage, mem_inter_iff, local_triv_at_apply_mk],
        exact ⟨Z.mem_base_set_at b, ha⟩, } } end⟩,
  trivialization_atlas := set.range Z.local_triv,
  trivialization_at := Z.local_triv_at,
  mem_base_set_trivialization_at := Z.mem_base_set_at,
  trivialization_mem_atlas := λ b, ⟨Z.index_at b, rfl⟩ }

/-- The projection on the base of a fiber bundle created from core is continuous -/
lemma continuous_proj : continuous Z.proj := continuous_proj F Z.fiber

/-- The projection on the base of a fiber bundle created from core is an open map -/
lemma is_open_map_proj : is_open_map Z.proj := is_open_map_proj F Z.fiber

end fiber_bundle_core

/-! ### Prebundle construction for constructing fiber bundles -/

variables (F) (E : B → Type*) [topological_space B] [topological_space F]

/-- This structure permits to define a fiber bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space. The total space is hence given a
topology in such a way that there is a fiber bundle structure for which the local equivalences
are also local homeomorphism and hence local trivializations. -/
@[nolint has_nonempty_instance]
structure fiber_prebundle :=
(pretrivialization_atlas : set (pretrivialization F (π E)))
(pretrivialization_at : B → pretrivialization F (π E))
(mem_base_pretrivialization_at : ∀ x : B, x ∈ (pretrivialization_at x).base_set)
(pretrivialization_mem_atlas : ∀ x : B, pretrivialization_at x ∈ pretrivialization_atlas)
(continuous_triv_change : ∀ e e' ∈ pretrivialization_atlas,
  continuous_on (e ∘ e'.to_local_equiv.symm) (e'.target ∩ (e'.to_local_equiv.symm ⁻¹' e.source)))

namespace fiber_prebundle

variables {F E} (a : fiber_prebundle F E) {e : pretrivialization F (π E)}

/-- Topology on the total space that will make the prebundle into a bundle. -/
def total_space_topology (a : fiber_prebundle F E) : topological_space (total_space E) :=
⨆ (e : pretrivialization F (π E)) (he : e ∈ a.pretrivialization_atlas),
  coinduced e.set_symm (subtype.topological_space)

lemma continuous_symm_of_mem_pretrivialization_atlas (he : e ∈ a.pretrivialization_atlas) :
  @continuous_on _ _ _ a.total_space_topology
  e.to_local_equiv.symm e.target :=
begin
  refine id (λ z H, id (λ U h, preimage_nhds_within_coinduced' H
    e.open_target (le_def.1 (nhds_mono _) U h))),
  exact le_supr₂ e he,
end

lemma is_open_source (e : pretrivialization F (π E)) : is_open[a.total_space_topology] e.source :=
begin
  letI := a.total_space_topology,
  refine is_open_supr_iff.mpr (λ e', _),
  refine is_open_supr_iff.mpr (λ he', _),
  refine is_open_coinduced.mpr (is_open_induced_iff.mpr ⟨e.target, e.open_target, _⟩),
  rw [pretrivialization.set_symm, restrict, e.target_eq,
    e.source_eq, preimage_comp, subtype.preimage_coe_eq_preimage_coe_iff,
    e'.target_eq, prod_inter_prod, inter_univ,
    pretrivialization.preimage_symm_proj_inter],
end

lemma is_open_target_of_mem_pretrivialization_atlas_inter (e e' : pretrivialization F (π E))
  (he' : e' ∈ a.pretrivialization_atlas) :
  is_open (e'.to_local_equiv.target ∩ e'.to_local_equiv.symm ⁻¹' e.source) :=
begin
  letI := a.total_space_topology,
  obtain ⟨u, hu1, hu2⟩ := continuous_on_iff'.mp (a.continuous_symm_of_mem_pretrivialization_atlas
    he') e.source (a.is_open_source e),
  rw [inter_comm, hu2],
  exact hu1.inter e'.open_target,
end

/-- Promotion from a `pretrivialization` to a `trivialization`. -/
def trivialization_of_mem_pretrivialization_atlas (he : e ∈ a.pretrivialization_atlas) :
  @trivialization B F _ _ _ a.total_space_topology (π E) :=
{ open_source := a.is_open_source e,
  continuous_to_fun := begin
    letI := a.total_space_topology,
    refine continuous_on_iff'.mpr (λ s hs, ⟨e ⁻¹' s ∩ e.source, (is_open_supr_iff.mpr (λ e', _)),
      by { rw [inter_assoc, inter_self], refl }⟩),
    refine (is_open_supr_iff.mpr (λ he', _)),
    rw [is_open_coinduced, is_open_induced_iff],
    obtain ⟨u, hu1, hu2⟩ := continuous_on_iff'.mp (a.continuous_triv_change _ he _ he') s hs,
    have hu3 := congr_arg (λ s, (λ x : e'.target, (x : B × F)) ⁻¹' s) hu2,
    simp only [subtype.coe_preimage_self, preimage_inter, univ_inter] at hu3,
    refine ⟨u ∩ e'.to_local_equiv.target ∩
      (e'.to_local_equiv.symm ⁻¹' e.source), _, by
      { simp only [preimage_inter, inter_univ, subtype.coe_preimage_self, hu3.symm], refl }⟩,
    rw inter_assoc,
    exact hu1.inter (a.is_open_target_of_mem_pretrivialization_atlas_inter e e' he'),
  end,
  continuous_inv_fun := a.continuous_symm_of_mem_pretrivialization_atlas he,
  .. e }

lemma mem_trivialization_at_source (b : B) (x : E b) :
  total_space_mk b x ∈ (a.pretrivialization_at b).source :=
begin
  simp only [(a.pretrivialization_at b).source_eq, mem_preimage, total_space.proj],
  exact a.mem_base_pretrivialization_at b,
end

@[simp] lemma total_space_mk_preimage_source (b : B) :
  (total_space_mk b) ⁻¹' (a.pretrivialization_at b).source = univ :=
begin
  apply eq_univ_of_univ_subset,
  rw [(a.pretrivialization_at b).source_eq, ←preimage_comp, function.comp],
  simp only [total_space.proj],
  rw preimage_const_of_mem _,
  exact a.mem_base_pretrivialization_at b,
end

/-- Topology on the fibers `E b` induced by the map `E b → E.total_space`. -/
def fiber_topology (b : B) : topological_space (E b) :=
topological_space.induced (total_space_mk b) a.total_space_topology

@[continuity] lemma inducing_total_space_mk (b : B) :
  @inducing _ _ (a.fiber_topology b) a.total_space_topology (total_space_mk b) :=
by { letI := a.total_space_topology, letI := a.fiber_topology b, exact ⟨rfl⟩ }

@[continuity] lemma continuous_total_space_mk (b : B) :
  @continuous _ _ (a.fiber_topology b) a.total_space_topology (total_space_mk b) :=
begin
  letI := a.total_space_topology, letI := a.fiber_topology b,
  exact (a.inducing_total_space_mk b).continuous
end

/-- Make a `fiber_bundle` from a `fiber_prebundle`.  Concretely this means
that, given a `fiber_prebundle` structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`fiber_prebundle.total_space_topology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
def to_fiber_bundle :
  @fiber_bundle B F _ _ E a.total_space_topology a.fiber_topology :=
{ total_space_mk_inducing := a.inducing_total_space_mk,
  trivialization_atlas := {e | ∃ e₀ (he₀ : e₀ ∈ a.pretrivialization_atlas),
    e = a.trivialization_of_mem_pretrivialization_atlas he₀},
  trivialization_at := λ x, a.trivialization_of_mem_pretrivialization_atlas
    (a.pretrivialization_mem_atlas x),
  mem_base_set_trivialization_at := a.mem_base_pretrivialization_at,
  trivialization_mem_atlas := λ x, ⟨_, a.pretrivialization_mem_atlas x, rfl⟩ }

lemma continuous_proj : @continuous _ _ a.total_space_topology _ (π E) :=
begin
  letI := a.total_space_topology,
  letI := a.fiber_topology,
  letI := a.to_fiber_bundle,
  exact continuous_proj F E,
end

/-- For a fiber bundle `E` over `B` constructed using the `fiber_prebundle` mechanism,
continuity of a function `total_space E → X` on an open set `s` can be checked by precomposing at
each point with the pretrivialization used for the construction at that point. -/
lemma continuous_on_of_comp_right {X : Type*} [topological_space X] {f : total_space E → X}
  {s : set B} (hs : is_open s)
  (hf : ∀ b ∈ s, continuous_on (f ∘ (a.pretrivialization_at b).to_local_equiv.symm)
    ((s ∩ (a.pretrivialization_at b).base_set) ×ˢ (set.univ : set F))) :
  @continuous_on _ _ a.total_space_topology _ f ((π E) ⁻¹' s) :=
begin
  letI := a.total_space_topology,
  intros z hz,
  let e : trivialization F (π E) :=
  a.trivialization_of_mem_pretrivialization_atlas (a.pretrivialization_mem_atlas z.proj),
  refine (e.continuous_at_of_comp_right _
    ((hf z.proj hz).continuous_at (is_open.mem_nhds _ _))).continuous_within_at,
  { exact a.mem_base_pretrivialization_at z.proj },
  { exact ((hs.inter (a.pretrivialization_at z.proj).open_base_set).prod is_open_univ) },
  refine ⟨_, mem_univ _⟩,
  rw e.coe_fst,
  { exact ⟨hz, a.mem_base_pretrivialization_at z.proj⟩ },
  { rw e.mem_source,
    exact a.mem_base_pretrivialization_at z.proj },
end

end fiber_prebundle
