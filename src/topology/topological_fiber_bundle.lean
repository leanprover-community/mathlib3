/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import topology.local_homeomorph

/-!
# Fiber bundles

A topological fiber bundle with fiber F over a base B is a space projecting on B for which the
fibers are all homeomorphic to F, such that the local situation around each point is a direct
product. We define a predicate `is_topological_fiber_bundle F p` saying that `p : Z → B` is a
topological fiber bundle with fiber `F`.

It is in general nontrivial to construct a fiber bundle. A way is to start from the knowledge of
how changes of local trivializations act on the fiber. From this, one can construct the total space
of the bundle and its topology by a suitable gluing construction. The main content of this file is
an implementation of this construction: starting from an object of type
`topological_fiber_bundle_core` registering the trivialization changes, one gets the corresponding
fiber bundle and projection.

## Main definitions

`bundle_trivialization F p` : structure extending local homeomorphisms, defining a local
                  trivialization of a topological space `Z` with projection `p` and fiber `F`.
`is_topological_fiber_bundle F p` : Prop saying that the map `p` between topological spaces is a
                  fiber bundle with fiber `F`.

`topological_fiber_bundle_core ι B F` : structure registering how changes of coordinates act on the
                  fiber `F` above open subsets of `B`, where local trivializations are indexed by ι.
Let `Z : topological_fiber_bundle_core ι B F`. Then we define
`Z.total_space` : the total space of `Z`, defined as a Type as `B × F`, but with a twisted topology
                  coming from the fiber bundle structure
`Z.proj`        : projection from `Z.total_space` to `B`. It is continuous.
`Z.fiber x`     : the fiber above `x`, homeomorphic to `F` (and defeq to `F` as a type).
`Z.local_triv i`: for `i : ι`, a local homeomorphism from `Z.total_space` to `B × F`, that realizes
                  a trivialization above the set `Z.base_set i`, which is an open set in `B`.

## Implementation notes

A topological fiber bundle with fiber F over a base B is a family of spaces isomorphic to F,
indexed by B, which is locally trivial in the following sense: there is a covering of B by open
sets such that, on each such open set `s`, the bundle is isomorphic to `s × F`.

To construct a fiber bundle formally, the main data is what happens when one changes trivializations
from `s × F` to `s' × F` on `s ∩ s'`: one should get a family of homeomorphisms of `F`, depending
continuously on the base point, satisfying basic compatibility conditions (cocycle property).
Useful classes of bundles can then be specified by requiring that these homeomorphisms of `F`
belong to some subgroup, preserving some structure (the "structure group of the bundle"): then
these structures are inherited by the fibers of the bundle.

Given such trivialization change data (encoded below in a structure called
`topological_fiber_bundle_core`), one can construct the fiber bundle. The intrinsic canonical
mathematical construction is the following.
The fiber above x is the disjoint union of F over all trivializations, modulo the gluing
identifications: one gets a fiber which is isomorphic to F, but non-canonically
(each choice of one of the trivializations around x gives such an isomorphism). Given a
trivialization over a set `s`, one gets an isomorphism between `s × F` and `proj^{-1} s`, by using
the identification corresponding to this trivialization. One chooses the topology on the bundle that
makes all of these into homeomorphisms.

For the practical implementation, it turns out to be more convenient to avoid completely the
gluing and quotienting construction above, and to declare above each `x` that the fiber is `F`,
but thinking that it corresponds to the `F` coming from the choice of one trivialization around `x`.
This has several practical advantages:
* without any work, one gets a topological space structure on the fiber. And if `F` has more
structure it is inherited for free by the fiber.
* In the trivial situation of the trivial bundle where there is only one chart and one
trivialization, this construction gives the product space B × F with the product topology. In the
case of the tangent bundle of manifolds, this also implies that on vector spaces the derivative and
the manifold derivative are equal.

A drawback is that some silly constructions will typecheck: in the case of the tangent bundle, one
can add two vectors in different tangent spaces (as they both are elements of F from the point of
view of Lean). To solve this, one could mark the tangent space as irreducible, but then one would
lose the identification of the tangent space to F with F. There is however a big advantage of this
situation: even if Lean can not check that two basepoints are defeq, it will accept the fact that
the tangent spaces are the same. For instance, if two maps f and g are locally inverse to each
other, one can express that the composition of their derivatives is the identity of
`tangent_space I x`. One could fear issues as this composition goes from `tangent_space I x` to
`tangent_space I (g (f x))` (which should be the same, but should not be obvious to Lean
as it does not know that `g (f x) = x`). As these types are the same to Lean (equal to `F`), there
are in fact no dependent type difficulties here!

For this construction of a fiber bundle from a `topological_fiber_bundle_core`, we should thus
choose for each `x` one specific trivialization around it. We include this choice in the definition
of the `topological_fiber_bundle_core`, as it makes some constructions more
functorial and it is a nice way to say that the trivializations cover the whole space B.

With this definition, the type of the fiber bundle space constructed from the core data is just
`B × F`, but the topology is not the product one.

We also take the indexing type (indexing all the trivializations) as a parameter to the fiber bundle
core: it could always be taken as a subtype of all the maps from open subsets of B to continuous
maps of F, but in practice it will sometimes be something else. For instance, on a manifold, one
will use the set of charts as a good parameterization for the trivializations of the tangent bundle.
Or for the pullback of a `topological_fiber_bundle_core`, the indexing type will be the same as
for the initial bundle.

## Tags
Fiber bundle, topological bundle, vector bundle, local trivialization, structure group
-/

variables {ι : Type*} {B : Type*} {F : Type*}

open topological_space set

section topological_fiber_bundle

variables {Z : Type*} [topological_space B] [topological_space Z]
  [topological_space F] (proj : Z → B)

variable (F)

/--
A structure extending local homeomorphisms, defining a local trivialization of a projection
`proj : Z → B` with fiber `F`, as a local homeomorphism between `Z` and `B × F` defined between two
sets of the form `proj ⁻¹' base_set` and `base_set × F`, acting trivially on the first coordinate.
-/
structure bundle_trivialization extends local_homeomorph Z (B × F) :=
(base_set      : set B)
(open_base_set : is_open base_set)
(source_eq     : source = proj ⁻¹' base_set)
(target_eq     : target = set.prod base_set univ)
(proj_to_fun   : ∀ p ∈ source, (to_fun p).1 = proj p)

/-- A topological fiber bundle with fiber F over a base B is a space projecting on B for which the
fibers are all homeomorphic to F, such that the local situation around each point is a direct
product. -/
def is_topological_fiber_bundle : Prop :=
∀ x : Z, ∃e : bundle_trivialization F proj, x ∈ e.source

variables {F} {proj}

/-- In the domain of a bundle trivialization, the projection is continuous-/
lemma bundle_trivialization.continuous_at_proj (e : bundle_trivialization F proj) {x : Z}
  (ex : x ∈ e.source) : continuous_at proj x :=
begin
  assume s hs,
  obtain ⟨t, st, t_open, xt⟩ : ∃ t ⊆ s, is_open t ∧ proj x ∈ t,
    from mem_nhds_sets_iff.1 hs,
  rw e.source_eq at ex,
  let u := e.base_set ∩ t,
  have u_open : is_open u := is_open_inter e.open_base_set t_open,
  have xu : proj x ∈ u := ⟨ex, xt⟩,
  /- Take a small enough open neighborhood u of `proj x`, contained in a trivialization domain o.
    One should show that its preimage is open. -/
  suffices : is_open (proj ⁻¹' u),
  { have : proj ⁻¹' u ∈ nhds x := mem_nhds_sets this xu,
    apply filter.mem_sets_of_superset this,
    exact preimage_mono (subset.trans (inter_subset_right _ _) st) },
  -- to do this, rewrite `proj ⁻¹' u` in terms of the trivialization, and use its continuity.
  have : proj ⁻¹' u = e.to_fun ⁻¹' (set.prod u univ) ∩ e.source,
  { ext p,
    split,
    { assume h,
      have : p ∈ e.source,
      { rw e.source_eq,
        have : u ⊆ e.base_set := inter_subset_left _ _,
        exact preimage_mono this h },
      simp [this, e.proj_to_fun, h.1, h.2] },
    { rintros ⟨h, h_source⟩,
      simpa [e.proj_to_fun, h_source] using h } },
  rw [this, inter_comm],
  exact continuous_on.preimage_open_of_open e.continuous_to_fun e.open_source
    (is_open_prod u_open is_open_univ)
end

/-- The projection from a topological fiber bundle to its base is continuous. -/
lemma is_topological_fiber_bundle.continuous_proj (h : is_topological_fiber_bundle F proj) :
  continuous proj :=
begin
  rw continuous_iff_continuous_at,
  assume x,
  rcases h x with ⟨e, ex⟩,
  exact e.continuous_at_proj ex
end

/-- The projection from a topological fiber bundle to its base is an open map. -/
lemma is_topological_fiber_bundle.is_open_map_proj (h : is_topological_fiber_bundle F proj) :
  is_open_map proj :=
begin
  assume s hs,
  rw is_open_iff_forall_mem_open,
  assume x xs,
  obtain ⟨y, ys, yx⟩ : ∃ y, y ∈ s ∧ proj y = x, from (mem_image _ _ _).1 xs,
  obtain ⟨e, he⟩ : ∃ (e : bundle_trivialization F proj), y ∈ e.source, from h y,
  refine ⟨proj '' (s ∩ e.source), image_subset _ (inter_subset_left _ _), _, ⟨y, ⟨ys, he⟩, yx⟩⟩,
  have : ∀z ∈ s ∩ e.source, prod.fst (e.to_fun z) = proj z := λz hz, e.proj_to_fun z hz.2,
  rw [← image_congr this, image_comp],
  have : is_open (e.to_fun '' (s ∩ e.source)) :=
    e.to_local_homeomorph.image_open_of_open (is_open_inter hs e.to_local_homeomorph.open_source)
    (inter_subset_right _ _),
  exact is_open_map_fst _ this
end

/-- The first projection in a product is a topological fiber bundle. -/
lemma is_topological_fiber_bundle_fst : is_topological_fiber_bundle F (prod.fst : B × F → B) :=
begin
  let F : bundle_trivialization F (prod.fst : B × F → B) :=
  { base_set      := univ,
    open_base_set := is_open_univ,
    source_eq     := rfl,
    target_eq     := by simp,
    proj_to_fun   := by simp,
     ..local_homeomorph.refl _ },
  exact λx, ⟨F, by simp⟩
end

/-- The second projection in a product is a topological fiber bundle. -/
lemma is_topological_fiber_bundle_snd : is_topological_fiber_bundle F (prod.snd : F × B → B) :=
begin
  let F : bundle_trivialization F (prod.snd : F × B → B) :=
  { base_set      := univ,
    open_base_set := is_open_univ,
    source_eq     := rfl,
    target_eq     := by simp,
    proj_to_fun   := λp, by { simp, refl },
     ..(homeomorph.prod_comm F B).to_local_homeomorph },
  exact λx, ⟨F, by simp⟩
end

end topological_fiber_bundle

/-- Core data defining a locally trivial topological bundle with fiber `F` over a topological
space `B`. Note that "bundle" is used in its mathematical sense. This is the (computer science)
bundled version, i.e., all the relevant data is contained in the following structure. A family of
local trivializations is indexed by a type ι, on open subsets `base_set i` for each `i : ι`.
Trivialization changes from `i` to `j` are given by continuous maps `coord_change i j` from
`base_set i ∩ base_set j` to the set of homeomorphisms of `F`, but we express them as maps
`B → F → F` and require continuity on `(base_set i ∩ base_set j) × F` to avoid the topology on the
space of continuous maps on `F`. -/
structure topological_fiber_bundle_core (ι : Type*) (B : Type*) [topological_space B]
  (F : Type*) [topological_space F] :=
(base_set          : ι → set B)
(is_open_base_set  : ∀i, is_open (base_set i))
(index_at          : B → ι)
(mem_base_set_at   : ∀x, x ∈ base_set (index_at x))
(coord_change      : ι → ι → B → F → F)
(coord_change_self : ∀i, ∀ x ∈ base_set i, ∀v, coord_change i i x v = v)
(coord_change_continuous : ∀i j, continuous_on (λp : B × F, coord_change i j p.1 p.2)
                                               (set.prod ((base_set i) ∩ (base_set j)) univ))
(coord_change_comp : ∀i j k, ∀x ∈ (base_set i) ∩ (base_set j) ∩ (base_set k), ∀v,
  (coord_change j k x) (coord_change i j x v) = coord_change i k x v)

attribute [simp] topological_fiber_bundle_core.mem_base_set_at

namespace topological_fiber_bundle_core

variables [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F)

include Z

/-- The index set of a topological fiber bundle core, as a convenience function for dot notation -/
@[nolint] def index := ι

/-- The base space of a topological fiber bundle core, as a convenience function for dot notation -/
@[nolint] def base := B

/-- The fiber of a topological fiber bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint] def fiber (x : B) := F

instance (x : B) : topological_space (Z.fiber x) := by { dsimp [fiber], apply_instance }

/-- Total space of a topological bundle created from core. It is equal to `Σ x : B, F`, but as it is
not marked as reducible, typeclass inference will not infer the wrong topology, and will use the
instance `topological_fiber_bundle_core.to_topological_space` with the right topology. -/
@[nolint] def total_space := B × F

/-- The projection from the total space of a topological fiber bundle core, on its base. -/
@[simp] def proj : Z.total_space → B := λp, p.1

/-- Local homeomorphism version of the trivialization change. -/
def triv_change (i j : ι) : local_homeomorph (B × F) (B × F) :=
{ source     := set.prod (Z.base_set i ∩ Z.base_set j) univ,
  target     := set.prod (Z.base_set i ∩ Z.base_set j) univ,
  to_fun     := λp, ⟨p.1, Z.coord_change i j p.1 p.2⟩,
  inv_fun    := λp, ⟨p.1, Z.coord_change j i p.1 p.2⟩,
  map_source := λp hp, by simpa using hp,
  map_target := λp hp, by simpa using hp,
  left_inv   := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, mem_inter_eq, and_true, mem_univ] at hx,
    rw [Z.coord_change_comp, Z.coord_change_self],
    { exact hx.1 },
    { simp [hx] }
  end,
  right_inv  := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, mem_inter_eq, and_true, mem_univ] at hx,
    rw [Z.coord_change_comp, Z.coord_change_self],
    { exact hx.2 },
    { simp [hx] },
  end,
  open_source :=
    is_open_prod (is_open_inter (Z.is_open_base_set i) (Z.is_open_base_set j)) is_open_univ,
  open_target :=
    is_open_prod (is_open_inter (Z.is_open_base_set i) (Z.is_open_base_set j)) is_open_univ,
  continuous_to_fun  :=
    continuous_on.prod continuous_fst.continuous_on (Z.coord_change_continuous i j),
  continuous_inv_fun := by simpa [inter_comm]
    using continuous_on.prod continuous_fst.continuous_on (Z.coord_change_continuous j i) }

@[simp] lemma mem_triv_change_source (i j : ι) (p : B × F) :
  p ∈ (Z.triv_change i j).source ↔ p.1 ∈ Z.base_set i ∩ Z.base_set j :=
by { erw [mem_prod], simp }

/-- Associate to a trivialization index `i : ι` the corresponding trivialization, i.e., a bijection
between `proj ⁻¹ (base_set i)` and `base_set i × F`. As the fiber above `x` is `F` but read in the
chart with index `index_at x`, the trivialization in the fiber above x is by definition the
coordinate change from i to `index_at x`, so it depends on `x`.
The local trivialization will ultimately be a local homeomorphism. For now, we only introduce the
local equiv version, denoted with a prime. In further developments, avoid this auxiliary version,
and use Z.local_triv instead.
-/
def local_triv' (i : ι) : local_equiv Z.total_space (B × F) :=
{ source     := Z.proj ⁻¹' (Z.base_set i),
  target     := set.prod (Z.base_set i) univ,
  inv_fun    := λp, ⟨p.1, Z.coord_change i (Z.index_at p.1) p.1 p.2⟩,
  to_fun     := λp, ⟨p.1, Z.coord_change (Z.index_at p.1) i p.1 p.2⟩,
  map_source := λp hp,
    by simpa only [set.mem_preimage, and_true, set.mem_univ, set.prod_mk_mem_set_prod_eq] using hp,
  map_target := λp hp,
    by simpa only [set.mem_preimage, and_true, set.mem_univ, set.mem_prod] using hp,
  left_inv   := begin
    rintros ⟨x, v⟩ hx,
    change x ∈ Z.base_set i at hx,
    dsimp,
    rw [Z.coord_change_comp, Z.coord_change_self],
    { exact Z.mem_base_set_at _ },
    { simp [hx] }
  end,
  right_inv := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, and_true, mem_univ] at hx,
    rw [Z.coord_change_comp, Z.coord_change_self],
    { exact hx },
    { simp [hx] }
  end }

@[simp] lemma mem_local_triv'_source (i : ι) (p : Z.total_space) :
  p ∈ (Z.local_triv' i).source ↔ p.1 ∈ Z.base_set i :=
by refl

@[simp] lemma mem_local_triv'_target (i : ι) (p : B × F) :
  p ∈ (Z.local_triv' i).target ↔ p.1 ∈ Z.base_set i :=
by { erw [mem_prod], simp }

@[simp] lemma local_triv'_fst (i : ι) (p : Z.total_space) :
  ((Z.local_triv' i).to_fun p).1 = p.1 := rfl

@[simp] lemma local_triv'_inv_fst (i : ι) (p : B × F) :
  ((Z.local_triv' i).inv_fun p).1 = p.1 := rfl

/-- The composition of two local trivializations is the trivialization change Z.triv_change i j. -/
lemma local_triv'_trans (i j : ι) :
  (Z.local_triv' i).symm.trans (Z.local_triv' j) ≈ (Z.triv_change i j).to_local_equiv :=
begin
  split,
  { ext x, erw [mem_prod], simp [local_equiv.trans_source] },
  { rintros ⟨x, v⟩ hx,
    simp only [triv_change, local_triv', local_equiv.symm, true_and, local_equiv.right_inv,
               prod_mk_mem_set_prod_eq, local_equiv.trans_source, mem_inter_eq, and_true,
               mem_univ, prod.mk.inj_iff, local_equiv.trans_apply, mem_preimage, proj,
               local_equiv.left_inv] at hx ⊢,
    simp [Z.coord_change_comp, hx] }
end

/-- Topological structure on the total space of a topological bundle created from core, designed so
that all the local trivialization are continuous. -/
instance to_topological_space : topological_space Z.total_space :=
topological_space.generate_from $ ⋃ (i : ι) (s : set (B × F)) (s_open : is_open s),
  {(Z.local_triv' i).source ∩ (Z.local_triv' i).to_fun ⁻¹' s }

lemma open_source' (i : ι) : is_open (Z.local_triv' i).source :=
begin
  apply topological_space.generate_open.basic,
  simp only [exists_prop, mem_Union, mem_singleton_iff],
  refine ⟨i, set.prod (Z.base_set i) univ, is_open_prod (Z.is_open_base_set i) (is_open_univ), _⟩,
  ext p,
  simp [topological_fiber_bundle_core.local_triv'_fst,
        topological_fiber_bundle_core.mem_local_triv'_source]
end

lemma open_target' (i : ι) : is_open (Z.local_triv' i).target :=
is_open_prod (Z.is_open_base_set i) (is_open_univ)

/-- Local trivialization of a topological bundle created from core, as a local homeomorphism. -/
def local_triv (i : ι) : local_homeomorph Z.total_space (B × F) :=
{ open_source := Z.open_source' i,
  open_target := Z.open_target' i,
  continuous_to_fun := begin
    rw continuous_on_open_iff (Z.open_source' i),
    assume s s_open,
    apply topological_space.generate_open.basic,
    simp only [exists_prop, mem_Union, mem_singleton_iff],
    exact ⟨i, s, s_open, rfl⟩
  end,
  continuous_inv_fun := begin
    apply continuous_on_open_of_generate_from (Z.open_target' i),
    assume t ht,
    simp only [exists_prop, mem_Union, mem_singleton_iff] at ht,
    obtain ⟨j, s, s_open, ts⟩ : ∃ j s,
      is_open s ∧ t = (local_triv' Z j).source ∩ (local_triv' Z j).to_fun ⁻¹' s := ht,
    rw ts,
    simp only [local_equiv.right_inv, preimage_inter, local_equiv.left_inv],
    let e := Z.local_triv' i,
    let e' := Z.local_triv' j,
    let f := e.symm.trans e',
    have : is_open (f.source ∩ f.to_fun ⁻¹' s),
    { rw [local_equiv.eq_on_source_preimage (Z.local_triv'_trans i j)],
      exact (continuous_on_open_iff (Z.triv_change i j).open_source).1
        ((Z.triv_change i j).continuous_to_fun) _ s_open },
    convert this using 1,
    dsimp [local_equiv.trans_source],
    rw [← preimage_comp, inter_assoc]
  end,
  ..Z.local_triv' i }

/- We will now state again the basic properties of the local trivializations, but without primes,
i.e., for the local homeomorphism instead of the local equiv. -/

@[simp] lemma mem_local_triv_source (i : ι) (p : Z.total_space) :
  p ∈ (Z.local_triv i).source ↔ p.1 ∈ Z.base_set i :=
by refl

@[simp] lemma mem_local_triv_target (i : ι) (p : B × F) :
  p ∈ (Z.local_triv i).target ↔ p.1 ∈ Z.base_set i :=
by { erw [mem_prod], simp }

@[simp] lemma local_triv_fst (i : ι) (p : Z.total_space) :
  ((Z.local_triv i).to_fun p).1 = p.1 := rfl

@[simp] lemma local_triv_symm_fst (i : ι) (p : B × F) :
  ((Z.local_triv i).inv_fun p).1 = p.1 := rfl

/-- The composition of two local trivializations is the trivialization change Z.triv_change i j. -/
lemma local_triv_trans (i j : ι) :
  (Z.local_triv i).symm.trans (Z.local_triv j) ≈ Z.triv_change i j :=
Z.local_triv'_trans i j

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def local_triv_ext (i : ι) : bundle_trivialization F Z.proj :=
{ base_set      := Z.base_set i,
  open_base_set := Z.is_open_base_set i,
  source_eq     := rfl,
  target_eq     := rfl,
  proj_to_fun   := λp hp, by simp,
  ..Z.local_triv i }

/-- A topological fiber bundle constructed from core is indeed a topological fiber bundle. -/
theorem is_topological_fiber_bundle : is_topological_fiber_bundle F Z.proj :=
λx, ⟨Z.local_triv_ext (Z.index_at (Z.proj x)), by simp [local_triv_ext]⟩

/-- The projection on the base of a topological bundle created from core is continuous -/
lemma continuous_proj : continuous Z.proj :=
Z.is_topological_fiber_bundle.continuous_proj

/-- The projection on the base of a topological bundle created from core is an open map -/
lemma is_open_map_proj : is_open_map Z.proj :=
Z.is_topological_fiber_bundle.is_open_map_proj

/-- Preferred local trivialization of a fiber bundle constructed from core, at a given point, as
a local homeomorphism -/
def local_triv_at (p : Z.total_space) : local_homeomorph Z.total_space (B × F) :=
  Z.local_triv (Z.index_at (Z.proj p))

@[simp] lemma mem_local_triv_at_source (p : Z.total_space) : p ∈ (Z.local_triv_at p).source :=
by simp [local_triv_at]

@[simp] lemma local_triv_at_fst (p q : Z.total_space) :
  ((Z.local_triv_at p).to_fun q).1 = q.1 := rfl

@[simp] lemma local_triv_at_symm_fst (p : Z.total_space) (q : B × F) :
  ((Z.local_triv_at p).inv_fun q).1 = q.1 := rfl

/-- Preferred local trivialization of a fiber bundle constructed from core, at a given point, as
a bundle trivialization -/
def local_triv_at_ext (p : Z.total_space) : bundle_trivialization F Z.proj :=
  Z.local_triv_ext (Z.index_at (Z.proj p))

@[simp] lemma local_triv_at_ext_to_local_homeomorph (p : Z.total_space) :
  (Z.local_triv_at_ext p).to_local_homeomorph = Z.local_triv_at p := rfl

end topological_fiber_bundle_core

#lint
