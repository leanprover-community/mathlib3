/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.local_homeomorph

/-!
# Fiber bundles

A topological fiber bundle with fiber `F` over a base `B` is a space projecting on `B` for which the
fibers are all homeomorphic to `F`, such that the local situation around each point is a direct
product. We define a predicate `is_topological_fiber_bundle F p` saying that `p : Z → B` is a
topological fiber bundle with fiber `F`.

It is in general nontrivial to construct a fiber bundle. A way is to start from the knowledge of
how changes of local trivializations act on the fiber. From this, one can construct the total space
of the bundle and its topology by a suitable gluing construction. The main content of this file is
an implementation of this construction: starting from an object of type
`topological_fiber_bundle_core` registering the trivialization changes, one gets the corresponding
fiber bundle and projection.

## Main definitions

### Basic definitions

* `bundle_trivialization F p` : structure extending local homeomorphisms, defining a local
                  trivialization of a topological space `Z` with projection `p` and fiber `F`.

* `is_topological_fiber_bundle F p` : Prop saying that the map `p` between topological spaces is a
                  fiber bundle with fiber `F`.

* `is_trivial_topological_fiber_bundle F p` : Prop saying that the map `p : Z → B` between
  topological spaces is a trivial topological fiber bundle, i.e., there exists a homeomorphism
  `h : Z ≃ₜ B × F` such that `proj x = (h x).1`.

### Operations on bundles

We provide the following operations on `bundle_trivialization`s.

* `bundle_trivialization.comap`: given a local trivialization `e` of a fiber bundle `p : Z → B`, a
  continuous map `f : B' → B` and a point `b' : B'` such that `f b' ∈ e.base_set`,
  `e.comap f hf b' hb'` is a trivialization of the pullback bundle. The pullback bundle
  (a.k.a., the induced bundle) has total space `{(x, y) : B' × Z | f x = p y}`, and is given by
  `λ ⟨(x, y), h⟩, x`.

* `is_topological_fiber_bundle.comap`: if `p : Z → B` is a topological fiber bundle, then its
  pullback along a continuous map `f : B' → B` is a topological fiber bundle as well.

* `bundle_trivialization.comp_homeomorph`: given a local trivialization `e` of a fiber bundle
  `p : Z → B` and a homeomorphism `h : Z' ≃ₜ Z`, returns a local trivialization of the fiber bundle
  `p ∘ h`.

* `is_topological_fiber_bundle.comp_homeomorph`: if `p : Z → B` is a topological fiber bundle
  and `h : Z' ≃ₜ Z` is a homeomorphism, then `p ∘ h : Z' → B` is a topological fiber bundle with
  the same fiber.

### Construction of a bundle from trivializations

* `bundle.total_space E` is a type synonym for `Σ (x : B), E x`, that we can endow with a suitable
  topology.
* `topological_fiber_bundle_core ι B F` : structure registering how changes of coordinates act
  on the fiber `F` above open subsets of `B`, where local trivializations are indexed by `ι`.

Let `Z : topological_fiber_bundle_core ι B F`. Then we define

* `Z.fiber x`     : the fiber above `x`, homeomorphic to `F` (and defeq to `F` as a type).
* `Z.total_space` : the total space of `Z`, defined as a `Type` as `Σ (b : B), F`, but with a
  twisted topology coming from the fiber bundle structure. It is (reducibly) the same as
  `bundle.total_space Z.fiber`.
* `Z.proj`        : projection from `Z.total_space` to `B`. It is continuous.
* `Z.local_triv i`: for `i : ι`, a local homeomorphism from `Z.total_space` to `B × F`, that
  realizes a trivialization above the set `Z.base_set i`, which is an open set in `B`.

## Implementation notes

A topological fiber bundle with fiber `F` over a base `B` is a family of spaces isomorphic to `F`,
indexed by `B`, which is locally trivial in the following sense: there is a covering of `B` by open
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

For this construction of a fiber bundle from a `topological_fiber_bundle_core`, we should thus
choose for each `x` one specific trivialization around it. We include this choice in the definition
of the `topological_fiber_bundle_core`, as it makes some constructions more
functorial and it is a nice way to say that the trivializations cover the whole space `B`.

With this definition, the type of the fiber bundle space constructed from the core data is just
`Σ (b : B), F `, but the topology is not the product one, in general.

We also take the indexing type (indexing all the trivializations) as a parameter to the fiber bundle
core: it could always be taken as a subtype of all the maps from open subsets of `B` to continuous
maps of `F`, but in practice it will sometimes be something else. For instance, on a manifold, one
will use the set of charts as a good parameterization for the trivializations of the tangent bundle.
Or for the pullback of a `topological_fiber_bundle_core`, the indexing type will be the same as
for the initial bundle.

## Tags
Fiber bundle, topological bundle, vector bundle, local trivialization, structure group
-/

variables {ι : Type*} {B : Type*} {F : Type*}

open topological_space filter set
open_locale topological_space

/-! ### General definition of topological fiber bundles -/

section topological_fiber_bundle

variables (F) {Z : Type*} [topological_space B] [topological_space Z]
  [topological_space F] {proj : Z → B}

/--
A structure extending local homeomorphisms, defining a local trivialization of a projection
`proj : Z → B` with fiber `F`, as a local homeomorphism between `Z` and `B × F` defined between two
sets of the form `proj ⁻¹' base_set` and `base_set × F`, acting trivially on the first coordinate.
-/
@[nolint has_inhabited_instance]
structure bundle_trivialization (proj : Z → B) extends local_homeomorph Z (B × F) :=
(base_set      : set B)
(open_base_set : is_open base_set)
(source_eq     : source = proj ⁻¹' base_set)
(target_eq     : target = set.prod base_set univ)
(proj_to_fun   : ∀ p ∈ source, (to_local_homeomorph p).1 = proj p)

instance : has_coe_to_fun (bundle_trivialization F proj) := ⟨_, λ e, e.to_fun⟩

variable {F}

@[simp, mfld_simps] lemma bundle_trivialization.coe_coe (e : bundle_trivialization F proj) :
  ⇑e.to_local_homeomorph = e := rfl

@[simp, mfld_simps] lemma bundle_trivialization.coe_mk
  (e : local_homeomorph Z (B × F)) (i j k l m) (x : Z) :
  (bundle_trivialization.mk e i j k l m : bundle_trivialization F proj) x = e x := rfl

variable (F)

/-- A topological fiber bundle with fiber `F` over a base `B` is a space projecting on `B`
for which the fibers are all homeomorphic to `F`, such that the local situation around each point
is a direct product. -/
def is_topological_fiber_bundle (proj : Z → B) : Prop :=
∀ x : B, ∃e : bundle_trivialization F proj, x ∈ e.base_set

/-- A trivial topological fiber bundle with fiber `F` over a base `B` is a space `Z`
projecting on `B` for which there exists a homeomorphism to `B × F` that sends `proj`
to `prod.fst`. -/
def is_trivial_topological_fiber_bundle (proj : Z → B) : Prop :=
∃ e : Z ≃ₜ (B × F), ∀ x, (e x).1 = proj x

variables {F}

lemma bundle_trivialization.mem_source (e : bundle_trivialization F proj)
  {x : Z} : x ∈ e.source ↔ proj x ∈ e.base_set :=
by rw [e.source_eq, mem_preimage]

lemma bundle_trivialization.mem_target (e : bundle_trivialization F proj)
  {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.base_set :=
by rw [e.target_eq, prod_univ, mem_preimage]

@[simp, mfld_simps] lemma bundle_trivialization.coe_fst (e : bundle_trivialization F proj) {x : Z}
  (ex : x ∈ e.source) : (e x).1 = proj x :=
e.proj_to_fun x ex

lemma bundle_trivialization.coe_fst' (e : bundle_trivialization F proj) {x : Z}
  (ex : proj x ∈ e.base_set) : (e x).1 = proj x :=
e.coe_fst (e.mem_source.2 ex)

lemma bundle_trivialization.proj_symm_apply (e : bundle_trivialization F proj) {x : B × F}
  (hx : x ∈ e.target) : proj (e.to_local_homeomorph.symm x) = x.1 :=
begin
  have := (e.coe_fst (e.to_local_homeomorph.map_target hx)).symm,
  rwa [← e.coe_coe, e.to_local_homeomorph.right_inv hx] at this
end

lemma bundle_trivialization.proj_symm_apply' (e : bundle_trivialization F proj) {b : B} {x : F}
  (hx : b ∈ e.base_set) : proj (e.to_local_homeomorph.symm (b, x)) = b :=
e.proj_symm_apply (e.mem_target.2 hx)

lemma bundle_trivialization.apply_symm_apply (e : bundle_trivialization F proj)
  {x : B × F} (hx : x ∈ e.target) : e (e.to_local_homeomorph.symm x) = x :=
e.to_local_homeomorph.right_inv hx

lemma bundle_trivialization.apply_symm_apply' (e : bundle_trivialization F proj)
  {b : B} {x : F} (hx : b ∈ e.base_set) : e (e.to_local_homeomorph.symm (b, x)) = (b, x) :=
e.apply_symm_apply (e.mem_target.2 hx)

@[simp, mfld_simps] lemma bundle_trivialization.symm_apply_mk_proj
  (e : bundle_trivialization F proj) {x : Z} (ex : x ∈ e.source) :
  e.to_local_homeomorph.symm (proj x, (e x).2) = x :=
by rw [← e.coe_fst ex, prod.mk.eta, ← e.coe_coe, e.to_local_homeomorph.left_inv ex]

lemma bundle_trivialization.coe_fst_eventually_eq_proj (e : bundle_trivialization F proj)
  {x : Z} (ex : x ∈ e.source) : prod.fst ∘ e =ᶠ[𝓝 x] proj  :=
mem_nhds_sets_iff.2 ⟨e.source, λ y hy, e.coe_fst hy, e.open_source, ex⟩

lemma bundle_trivialization.coe_fst_eventually_eq_proj' (e : bundle_trivialization F proj)
  {x : Z} (ex : proj x ∈ e.base_set) : prod.fst ∘ e =ᶠ[𝓝 x] proj  :=
e.coe_fst_eventually_eq_proj (e.mem_source.2 ex)

lemma is_trivial_topological_fiber_bundle.is_topological_fiber_bundle
  (h : is_trivial_topological_fiber_bundle F proj) :
  is_topological_fiber_bundle F proj :=
let ⟨e, he⟩ := h in λ x,
⟨⟨e.to_local_homeomorph, univ, is_open_univ, rfl, univ_prod_univ.symm, λ x _, he x⟩, mem_univ x⟩

lemma bundle_trivialization.map_proj_nhds (e : bundle_trivialization F proj) {x : Z}
  (ex : x ∈ e.source) : map proj (𝓝 x) = 𝓝 (proj x) :=
by rw [← e.coe_fst ex, ← map_congr (e.coe_fst_eventually_eq_proj ex), ← map_map, ← e.coe_coe,
  e.to_local_homeomorph.map_nhds_eq ex, map_fst_nhds]

/-- In the domain of a bundle trivialization, the projection is continuous-/
lemma bundle_trivialization.continuous_at_proj (e : bundle_trivialization F proj) {x : Z}
  (ex : x ∈ e.source) : continuous_at proj x :=
(e.map_proj_nhds ex).le

/-- The projection from a topological fiber bundle to its base is continuous. -/
lemma is_topological_fiber_bundle.continuous_proj (h : is_topological_fiber_bundle F proj) :
  continuous proj :=
begin
  rw continuous_iff_continuous_at,
  assume x,
  rcases h (proj x) with ⟨e, ex⟩,
  apply e.continuous_at_proj,
  rwa e.source_eq
end

/-- The projection from a topological fiber bundle to its base is an open map. -/
lemma is_topological_fiber_bundle.is_open_map_proj (h : is_topological_fiber_bundle F proj) :
  is_open_map proj :=
begin
  refine is_open_map_iff_nhds_le.2 (λ x, _),
  rcases h (proj x) with ⟨e, ex⟩,
  refine (e.map_proj_nhds _).ge,
  rwa e.source_eq
end

/-- The first projection in a product is a trivial topological fiber bundle. -/
lemma is_trivial_topological_fiber_bundle_fst :
  is_trivial_topological_fiber_bundle F (prod.fst : B × F → B) :=
⟨homeomorph.refl _, λ x, rfl⟩

/-- The first projection in a product is a topological fiber bundle. -/
lemma is_topological_fiber_bundle_fst : is_topological_fiber_bundle F (prod.fst : B × F → B) :=
is_trivial_topological_fiber_bundle_fst.is_topological_fiber_bundle

/-- The second projection in a product is a trivial topological fiber bundle. -/
lemma is_trivial_topological_fiber_bundle_snd :
  is_trivial_topological_fiber_bundle F (prod.snd : F × B → B) :=
⟨homeomorph.prod_comm _ _, λ x, rfl⟩

/-- The second projection in a product is a topological fiber bundle. -/
lemma is_topological_fiber_bundle_snd : is_topological_fiber_bundle F (prod.snd : F × B → B) :=
is_trivial_topological_fiber_bundle_snd.is_topological_fiber_bundle

/-- Composition of a `bundle_trivialization` and a `homeomorph`. -/
def bundle_trivialization.comp_homeomorph {Z' : Type*} [topological_space Z']
  (e : bundle_trivialization F proj) (h : Z' ≃ₜ Z) :
  bundle_trivialization F (proj ∘ h) :=
{ to_local_homeomorph := h.to_local_homeomorph.trans e.to_local_homeomorph,
  base_set := e.base_set,
  open_base_set := e.open_base_set,
  source_eq := by simp [e.source_eq, preimage_preimage],
  target_eq := by simp [e.target_eq],
  proj_to_fun := λ p hp,
    have hp : h p ∈ e.source, by simpa using hp,
    by simp [hp] }

lemma is_topological_fiber_bundle.comp_homeomorph {Z' : Type*} [topological_space Z']
  (e : is_topological_fiber_bundle F proj) (h : Z' ≃ₜ Z) :
  is_topological_fiber_bundle F (proj ∘ h) :=
λ x, let ⟨e, he⟩ := e x in
⟨e.comp_homeomorph h, by simpa [bundle_trivialization.comp_homeomorph] using he⟩

section induced

open_locale classical

variables {B' : Type*} [topological_space B']

/-- Given a bundle trivialization of `proj : Z → B` and a continuous map `f : B' → B`,
construct a bundle trivialization of `φ : {p : B' × Z | f p.1 = proj p.2} → B'`
given by `φ x = (x : B' × Z).1`. -/
noncomputable def bundle_trivialization.comap
  (e : bundle_trivialization F proj) (f : B' → B) (hf : continuous f)
  (b' : B') (hb' : f b' ∈ e.base_set) :
  bundle_trivialization F (λ x : {p : B' × Z | f p.1 = proj p.2}, (x : B' × Z).1) :=
{ to_fun := λ p, ((p : B' × Z).1, (e (p : B' × Z).2).2),
  inv_fun := λ p, if h : f p.1 ∈ e.base_set
    then ⟨⟨p.1, e.to_local_homeomorph.symm (f p.1, p.2)⟩, by simp [e.proj_symm_apply' h]⟩
    else ⟨⟨b', e.to_local_homeomorph.symm (f b', p.2)⟩, by simp [e.proj_symm_apply' hb']⟩,
  source := {p | f (p : B' × Z).1 ∈ e.base_set},
  target := {p | f p.1 ∈ e.base_set},
  map_source' := λ p hp, hp,
  map_target' := λ p (hp : f p.1 ∈ e.base_set), by simp [hp],
  left_inv' :=
    begin
      rintro ⟨⟨b, x⟩, hbx⟩ hb,
      dsimp at *,
      have hx : x ∈ e.source, from e.mem_source.2 (hbx ▸ hb),
      ext; simp *
    end,
  right_inv' := λ p (hp : f p.1 ∈ e.base_set), by simp [*, e.apply_symm_apply'],
  open_source := e.open_base_set.preimage (hf.comp $ continuous_fst.comp continuous_subtype_coe),
  open_target := e.open_base_set.preimage (hf.comp continuous_fst),
  continuous_to_fun := ((continuous_fst.comp continuous_subtype_coe).continuous_on).prod $
    continuous_snd.comp_continuous_on $ e.continuous_to_fun.comp
      (continuous_snd.comp continuous_subtype_coe).continuous_on $
      by { rintro ⟨⟨b, x⟩, (hbx : f b = proj x)⟩ (hb : f b ∈ e.base_set),
           rw hbx at hb,
           exact e.mem_source.2 hb },
  continuous_inv_fun :=
    begin
      rw [embedding_subtype_coe.continuous_on_iff],
      suffices : continuous_on (λ p : B' × F, (p.1, e.to_local_homeomorph.symm (f p.1, p.2)))
        {p : B' × F | f p.1 ∈ e.base_set},
      { refine this.congr (λ p (hp : f p.1 ∈ e.base_set), _),
        simp [hp] },
      { refine continuous_on_fst.prod (e.to_local_homeomorph.symm.continuous_on.comp _ _),
        { exact ((hf.comp continuous_fst).prod_mk continuous_snd).continuous_on },
        { exact λ p hp, e.mem_target.2 hp } }
    end,
  base_set := f ⁻¹' e.base_set,
  source_eq := rfl,
  target_eq := by { ext, simp },
  open_base_set := e.open_base_set.preimage hf,
  proj_to_fun := λ _ _, rfl }

/-- If `proj : Z → B` is a topological fiber bundle with fiber `F` and `f : B' → B` is a continuous
map, then the pullback bundle (a.k.a. induced bundle) is the topological bundle with the total space
`{(x, y) : B' × Z | f x = proj y}` given by `λ ⟨(x, y), h⟩, x`. -/
lemma is_topological_fiber_bundle.comap (h : is_topological_fiber_bundle F proj)
  {f : B' → B} (hf : continuous f) :
  is_topological_fiber_bundle F (λ x : {p : B' × Z | f p.1 = proj p.2}, (x : B' × Z).1) :=
λ x, let ⟨e, he⟩ := h (f x) in ⟨e.comap f hf x he, he⟩

end induced

end topological_fiber_bundle

/-! ### Constructing topological fiber bundles -/

namespace bundle
/- We provide a type synonym of `Σ x, E x` as `bundle.total_space E`, to be able to endow it with
a topology which is not the disjoint union topology. In general, the constructions of fiber bundles
we will make will be of this form. -/

variable (E : B → Type*)

/--
`total_space E` is the total space of the bundle `Σ x, E x`. This type synonym is used to avoid
conflicts with general sigma types.
-/
def total_space := Σ x, E x

instance [inhabited B] [inhabited (E (default B))] :
  inhabited (total_space E) := ⟨⟨default B, default (E (default B))⟩⟩

/-- `bundle.proj E` is the canonical projection `total_space E → B` on the base space. -/
@[simp, mfld_simps] def proj : total_space E → B :=
λ (y : total_space E), y.1

instance {x : B} : has_coe_t (E x) (total_space E) := ⟨λ y, (⟨x, y⟩ : total_space E)⟩

lemma to_total_space_coe {x : B} (v : E x) : (v : total_space E) = ⟨x, v⟩ := rfl

end bundle

/-- Core data defining a locally trivial topological bundle with fiber `F` over a topological
space `B`. Note that "bundle" is used in its mathematical sense. This is the (computer science)
bundled version, i.e., all the relevant data is contained in the following structure. A family of
local trivializations is indexed by a type ι, on open subsets `base_set i` for each `i : ι`.
Trivialization changes from `i` to `j` are given by continuous maps `coord_change i j` from
`base_set i ∩ base_set j` to the set of homeomorphisms of `F`, but we express them as maps
`B → F → F` and require continuity on `(base_set i ∩ base_set j) × F` to avoid the topology on the
space of continuous maps on `F`. -/
@[nolint has_inhabited_instance]
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

attribute [simp, mfld_simps] topological_fiber_bundle_core.mem_base_set_at

namespace topological_fiber_bundle_core

variables [topological_space B] [topological_space F] (Z : topological_fiber_bundle_core ι B F)

include Z

/-- The index set of a topological fiber bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments has_inhabited_instance]
def index := ι

/-- The base space of a topological fiber bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments, reducible]
def base := B

/-- The fiber of a topological fiber bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_inhabited_instance]
def fiber (x : B) := F

instance topological_space_fiber (x : B) : topological_space (Z.fiber x) :=
by { dsimp [fiber], apply_instance }

/-- The total space of the topological fiber bundle, as a convenience function for dot notation.
It is by definition equal to `bundle.total_space Z.fiber`, a.k.a. `Σ x, Z.fiber x` but with a
different name for typeclass inference. -/
@[nolint unused_arguments, reducible]
def total_space := bundle.total_space Z.fiber

/-- The projection from the total space of a topological fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps] def proj : Z.total_space → B := bundle.proj Z.fiber

/-- Local homeomorphism version of the trivialization change. -/
def triv_change (i j : ι) : local_homeomorph (B × F) (B × F) :=
{ source      := set.prod (Z.base_set i ∩ Z.base_set j) univ,
  target      := set.prod (Z.base_set i ∩ Z.base_set j) univ,
  to_fun      := λp, ⟨p.1, Z.coord_change i j p.1 p.2⟩,
  inv_fun     := λp, ⟨p.1, Z.coord_change j i p.1 p.2⟩,
  map_source' := λp hp, by simpa using hp,
  map_target' := λp hp, by simpa using hp,
  left_inv'   := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, mem_inter_eq, and_true, mem_univ] at hx,
    rw [Z.coord_change_comp, Z.coord_change_self],
    { exact hx.1 },
    { simp [hx] }
  end,
  right_inv'  := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, mem_inter_eq, and_true, mem_univ] at hx,
    rw [Z.coord_change_comp, Z.coord_change_self],
    { exact hx.2 },
    { simp [hx] },
  end,
  open_source :=
    (is_open_inter (Z.is_open_base_set i) (Z.is_open_base_set j)).prod is_open_univ,
  open_target :=
    (is_open_inter (Z.is_open_base_set i) (Z.is_open_base_set j)).prod is_open_univ,
  continuous_to_fun  :=
    continuous_on.prod continuous_fst.continuous_on (Z.coord_change_continuous i j),
  continuous_inv_fun := by simpa [inter_comm]
    using continuous_on.prod continuous_fst.continuous_on (Z.coord_change_continuous j i) }

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
def local_triv' (i : ι) : local_equiv Z.total_space (B × F) :=
{ source      := Z.proj ⁻¹' (Z.base_set i),
  target      := set.prod (Z.base_set i) univ,
  inv_fun     := λp, ⟨p.1, Z.coord_change i (Z.index_at p.1) p.1 p.2⟩,
  to_fun      := λp, ⟨p.1, Z.coord_change (Z.index_at p.1) i p.1 p.2⟩,
  map_source' := λp hp,
    by simpa only [set.mem_preimage, and_true, set.mem_univ, set.prod_mk_mem_set_prod_eq] using hp,
  map_target' := λp hp,
    by simpa only [set.mem_preimage, and_true, set.mem_univ, set.mem_prod] using hp,
  left_inv'   := begin
    rintros ⟨x, v⟩ hx,
    change x ∈ Z.base_set i at hx,
    dsimp,
    rw [Z.coord_change_comp, Z.coord_change_self],
    { exact Z.mem_base_set_at _ },
    { simp [hx] }
  end,
  right_inv' := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, and_true, mem_univ] at hx,
    rw [Z.coord_change_comp, Z.coord_change_self],
    { exact hx },
    { simp [hx] }
  end }

@[simp, mfld_simps] lemma mem_local_triv'_source (i : ι) (p : Z.total_space) :
  p ∈ (Z.local_triv' i).source ↔ p.1 ∈ Z.base_set i :=
iff.rfl

@[simp, mfld_simps] lemma mem_local_triv'_target (i : ι) (p : B × F) :
  p ∈ (Z.local_triv' i).target ↔ p.1 ∈ Z.base_set i :=
by { erw [mem_prod], simp }

@[simp, mfld_simps] lemma local_triv'_apply (i : ι) (p : Z.total_space) :
  (Z.local_triv' i) p = ⟨p.1, Z.coord_change (Z.index_at p.1) i p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma local_triv'_symm_apply (i : ι) (p : B × F) :
  (Z.local_triv' i).symm p = ⟨p.1, Z.coord_change i (Z.index_at p.1) p.1 p.2⟩ := rfl

/-- The composition of two local trivializations is the trivialization change Z.triv_change i j. -/
lemma local_triv'_trans (i j : ι) :
  (Z.local_triv' i).symm.trans (Z.local_triv' j) ≈ (Z.triv_change i j).to_local_equiv :=
begin
  split,
  { ext x, erw [mem_prod], simp [local_equiv.trans_source] },
  { rintros ⟨x, v⟩ hx,
    simp only [triv_change, local_triv', local_equiv.symm, true_and, prod_mk_mem_set_prod_eq,
      local_equiv.trans_source, mem_inter_eq, and_true, mem_univ, prod.mk.inj_iff, mem_preimage,
      proj, local_equiv.coe_mk, eq_self_iff_true, local_equiv.coe_trans, bundle.proj] at hx ⊢,
    simp [Z.coord_change_comp, hx], }
end

/-- Topological structure on the total space of a topological bundle created from core, designed so
that all the local trivialization are continuous. -/
instance to_topological_space : topological_space (bundle.total_space Z.fiber) :=
topological_space.generate_from $ ⋃ (i : ι) (s : set (B × F)) (s_open : is_open s),
  {(Z.local_triv' i).source ∩ (Z.local_triv' i) ⁻¹' s}

lemma open_source' (i : ι) : is_open (Z.local_triv' i).source :=
begin
  apply topological_space.generate_open.basic,
  simp only [exists_prop, mem_Union, mem_singleton_iff],
  refine ⟨i, set.prod (Z.base_set i) univ, (Z.is_open_base_set i).prod is_open_univ, _⟩,
  ext p,
  simp only with mfld_simps
end

lemma open_target' (i : ι) : is_open (Z.local_triv' i).target :=
(Z.is_open_base_set i).prod is_open_univ

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
      is_open s ∧ t = (local_triv' Z j).source ∩ (local_triv' Z j) ⁻¹' s := ht,
    rw ts,
    simp only [local_equiv.right_inv, preimage_inter, local_equiv.left_inv],
    let e := Z.local_triv' i,
    let e' := Z.local_triv' j,
    let f := e.symm.trans e',
    have : is_open (f.source ∩ f ⁻¹' s),
    { rw [(Z.local_triv'_trans i j).source_inter_preimage_eq],
      exact (continuous_on_open_iff (Z.triv_change i j).open_source).1
        ((Z.triv_change i j).continuous_on) _ s_open },
    convert this using 1,
    dsimp [local_equiv.trans_source],
    rw [← preimage_comp, inter_assoc]
  end,
  to_local_equiv := Z.local_triv' i }

/- We will now state again the basic properties of the local trivializations, but without primes,
i.e., for the local homeomorphism instead of the local equiv. -/

@[simp, mfld_simps] lemma mem_local_triv_source (i : ι) (p : Z.total_space) :
  p ∈ (Z.local_triv i).source ↔ p.1 ∈ Z.base_set i :=
iff.rfl

@[simp, mfld_simps] lemma mem_local_triv_target (i : ι) (p : B × F) :
  p ∈ (Z.local_triv i).target ↔ p.1 ∈ Z.base_set i :=
by { erw [mem_prod], simp }

@[simp, mfld_simps] lemma local_triv_apply (i : ι) (p : Z.total_space) :
  (Z.local_triv i) p = ⟨p.1, Z.coord_change (Z.index_at p.1) i p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma local_triv_symm_fst (i : ι) (p : B × F) :
  (Z.local_triv i).symm p = ⟨p.1, Z.coord_change i (Z.index_at p.1) p.1 p.2⟩ := rfl

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
  to_local_homeomorph := Z.local_triv i }

/-- A topological fiber bundle constructed from core is indeed a topological fiber bundle. -/
protected theorem is_topological_fiber_bundle : is_topological_fiber_bundle F Z.proj :=
λx, ⟨Z.local_triv_ext (Z.index_at x), Z.mem_base_set_at x⟩

/-- The projection on the base of a topological bundle created from core is continuous -/
lemma continuous_proj : continuous Z.proj :=
Z.is_topological_fiber_bundle.continuous_proj

/-- The projection on the base of a topological bundle created from core is an open map -/
lemma is_open_map_proj : is_open_map Z.proj :=
Z.is_topological_fiber_bundle.is_open_map_proj

/-- Preferred local trivialization of a fiber bundle constructed from core, at a given point, as
a local homeomorphism -/
def local_triv_at (p : Z.total_space) :
  local_homeomorph Z.total_space (B × F) :=
Z.local_triv (Z.index_at (Z.proj p))

@[simp, mfld_simps] lemma mem_local_triv_at_source (p : Z.total_space) :
  p ∈ (Z.local_triv_at p).source :=
by simp [local_triv_at]

@[simp, mfld_simps] lemma local_triv_at_fst (p q : Z.total_space) :
  ((Z.local_triv_at p) q).1 = q.1 := rfl

@[simp, mfld_simps] lemma local_triv_at_symm_fst (p : Z.total_space) (q : B × F) :
  ((Z.local_triv_at p).symm q).1 = q.1 := rfl

/-- Preferred local trivialization of a fiber bundle constructed from core, at a given point, as
a bundle trivialization -/
def local_triv_at_ext (p : Z.total_space) : bundle_trivialization F Z.proj :=
Z.local_triv_ext (Z.index_at (Z.proj p))

@[simp, mfld_simps] lemma local_triv_at_ext_to_local_homeomorph (p : Z.total_space) :
  (Z.local_triv_at_ext p).to_local_homeomorph = Z.local_triv_at p := rfl

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
    mem_nhds_sets (Z.is_open_base_set (Z.index_at x)) (Z.mem_base_set_at x),
  apply ((Z.local_triv (Z.index_at x)).continuous_at_iff_continuous_at_comp_left _).2,
  { simp only [(∘)] with mfld_simps,
    apply continuous_at_id.prod,
    have : continuous_on (λ (y : B), v) (Z.base_set (Z.index_at x)) := continuous_on_const,
    apply (this.congr _).continuous_at A,
    assume y hy,
    simp only [h, hy] with mfld_simps },
  { exact A }
end

end topological_fiber_bundle_core
