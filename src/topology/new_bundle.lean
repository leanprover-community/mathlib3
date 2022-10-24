/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import data.bundle
import topology.algebra.order.basic
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

Similarly we implement the object `topological_fiber_prebundle` which allows to define a topological
fiber bundle from trivializations given as local equivalences with minimum additional properties.

## Main definitions

### Basic definitions

* `trivialization F p` : structure extending local homeomorphisms, defining a local
                  trivialization of a topological space `Z` with projection `p` and fiber `F`.

* `is_topological_fiber_bundle F p` : Prop saying that the map `p` between topological spaces is a
                  fiber bundle with fiber `F`.

* `is_trivial_topological_fiber_bundle F p` : Prop saying that the map `p : Z → B` between
  topological spaces is a trivial topological fiber bundle, i.e., there exists a homeomorphism
  `h : Z ≃ₜ B × F` such that `proj x = (h x).1`.

### Operations on bundles

We provide the following operations on `trivialization`s.

* `trivialization.comap`: given a local trivialization `e` of a fiber bundle `p : Z → B`, a
  continuous map `f : B' → B` and a point `b' : B'` such that `f b' ∈ e.base_set`,
  `e.comap f hf b' hb'` is a trivialization of the pullback bundle. The pullback bundle
  (a.k.a., the induced bundle) has total space `{(x, y) : B' × Z | f x = p y}`, and is given by
  `λ ⟨(x, y), h⟩, x`.

* `is_topological_fiber_bundle.comap`: if `p : Z → B` is a topological fiber bundle, then its
  pullback along a continuous map `f : B' → B` is a topological fiber bundle as well.

* `trivialization.comp_homeomorph`: given a local trivialization `e` of a fiber bundle
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
* `Z.local_triv i`: for `i : ι`, bundle trivialization above the set `Z.base_set i`, which is an
                    open set in `B`.

* `pretrivialization F proj` : trivialization as a local equivalence, mainly used when the
                                      topology on the total space has not yet been defined.
* `topological_fiber_prebundle F proj` : structure registering a cover of prebundle trivializations
  and requiring that the relative transition maps are local homeomorphisms.
* `topological_fiber_prebundle.total_space_topology a` : natural topology of the total space, making
  the prebundle into a bundle.

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
Fiber bundle, topological bundle, local trivialization, structure group
-/

variables {ι : Type*} {B : Type*} {F : Type*}

open topological_space filter set bundle
open_locale topological_space classical

/-! ### General definition of topological fiber bundles -/

section topological_fiber_bundle

variables (F) {Z : Type*} [topological_space B] [topological_space F] {proj : Z → B}

/-- This structure contains the information left for a local trivialization (which is implemented
below as `trivialization F proj`) if the total space has not been given a topology, but we
have a topology on both the fiber and the base space. Through the construction
`topological_fiber_prebundle F proj` it will be possible to promote a
`pretrivialization F proj` to a `trivialization F proj`. -/
@[ext, nolint has_nonempty_instance]
structure pretrivialization (proj : Z → B) extends local_equiv Z (B × F) :=
(open_target   : is_open target)
(base_set      : set B)
(open_base_set : is_open base_set)
(source_eq     : source = proj ⁻¹' base_set)
(target_eq     : target = base_set ×ˢ univ)
(proj_to_fun   : ∀ p ∈ source, (to_fun p).1 = proj p)

namespace pretrivialization

instance : has_coe_to_fun (pretrivialization F proj) (λ _, Z → (B × F)) := ⟨λ e, e.to_fun⟩

variables {F} (e : pretrivialization F proj) {x : Z}

@[simp, mfld_simps] lemma coe_coe : ⇑e.to_local_equiv = e := rfl
@[simp, mfld_simps] lemma coe_fst (ex : x ∈ e.source) : (e x).1 = proj x := e.proj_to_fun x ex
lemma mem_source : x ∈ e.source ↔ proj x ∈ e.base_set := by rw [e.source_eq, mem_preimage]
lemma coe_fst' (ex : proj x ∈ e.base_set) : (e x).1 = proj x := e.coe_fst (e.mem_source.2 ex)
protected lemma eq_on : eq_on (prod.fst ∘ e) proj e.source := λ x hx, e.coe_fst hx
lemma mk_proj_snd (ex : x ∈ e.source) : (proj x, (e x).2) = e x := prod.ext (e.coe_fst ex).symm rfl
lemma mk_proj_snd' (ex : proj x ∈ e.base_set) : (proj x, (e x).2) = e x :=
prod.ext (e.coe_fst' ex).symm rfl

/-- Composition of inverse and coercion from the subtype of the target. -/
def set_symm : e.target → Z := e.target.restrict e.to_local_equiv.symm

lemma mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.base_set :=
by rw [e.target_eq, prod_univ, mem_preimage]

lemma proj_symm_apply {x : B × F} (hx : x ∈ e.target) : proj (e.to_local_equiv.symm x) = x.1 :=
begin
  have := (e.coe_fst (e.to_local_equiv.map_target hx)).symm,
  rwa [← e.coe_coe, e.to_local_equiv.right_inv hx] at this
end

lemma proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) :
  proj (e.to_local_equiv.symm (b, x)) = b :=
e.proj_symm_apply (e.mem_target.2 hx)

lemma proj_surj_on_base_set [nonempty F] : set.surj_on proj e.source e.base_set :=
λ b hb, let ⟨y⟩ := ‹nonempty F› in ⟨e.to_local_equiv.symm (b, y),
  e.to_local_equiv.map_target $ e.mem_target.2 hb, e.proj_symm_apply' hb⟩

lemma apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.to_local_equiv.symm x) = x :=
e.to_local_equiv.right_inv hx

lemma apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) :
  e (e.to_local_equiv.symm (b, x)) = (b, x) :=
e.apply_symm_apply (e.mem_target.2 hx)

lemma symm_apply_apply {x : Z} (hx : x ∈ e.source) : e.to_local_equiv.symm (e x) = x :=
e.to_local_equiv.left_inv hx

@[simp, mfld_simps] lemma symm_apply_mk_proj {x : Z} (ex : x ∈ e.source) :
  e.to_local_equiv.symm (proj x, (e x).2) = x :=
by rw [← e.coe_fst ex, prod.mk.eta, ← e.coe_coe, e.to_local_equiv.left_inv ex]

@[simp, mfld_simps] lemma preimage_symm_proj_base_set :
  (e.to_local_equiv.symm ⁻¹' (proj ⁻¹' e.base_set)) ∩ e.target  = e.target :=
begin
  refine inter_eq_right_iff_subset.mpr (λ x hx, _),
  simp only [mem_preimage, local_equiv.inv_fun_as_coe, e.proj_symm_apply hx],
  exact e.mem_target.mp hx,
end

@[simp, mfld_simps] lemma preimage_symm_proj_inter (s : set B) :
  (e.to_local_equiv.symm ⁻¹' (proj ⁻¹' s)) ∩ e.base_set ×ˢ univ = (s ∩ e.base_set) ×ˢ univ :=
begin
  ext ⟨x, y⟩,
  suffices : x ∈ e.base_set → (proj (e.to_local_equiv.symm (x, y)) ∈ s ↔ x ∈ s),
    by simpa only [prod_mk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ, and.congr_left_iff],
  intro h,
  rw [e.proj_symm_apply' h]
end

lemma target_inter_preimage_symm_source_eq (e f : pretrivialization F proj) :
  f.target ∩ (f.to_local_equiv.symm) ⁻¹' e.source = (e.base_set ∩ f.base_set) ×ˢ univ :=
by rw [inter_comm, f.target_eq, e.source_eq, f.preimage_symm_proj_inter]

lemma trans_source (e f : pretrivialization F proj) :
  (f.to_local_equiv.symm.trans e.to_local_equiv).source = (e.base_set ∩ f.base_set) ×ˢ univ :=
by rw [local_equiv.trans_source, local_equiv.symm_source, e.target_inter_preimage_symm_source_eq]

lemma symm_trans_symm (e e' : pretrivialization F proj) :
  (e.to_local_equiv.symm.trans e'.to_local_equiv).symm =
  e'.to_local_equiv.symm.trans e.to_local_equiv :=
by rw [local_equiv.trans_symm_eq_symm_trans_symm, local_equiv.symm_symm]

lemma symm_trans_source_eq (e e' : pretrivialization F proj) :
  (e.to_local_equiv.symm.trans e'.to_local_equiv).source = (e.base_set ∩ e'.base_set) ×ˢ univ :=
by rw [local_equiv.trans_source, e'.source_eq, local_equiv.symm_source, e.target_eq, inter_comm,
  e.preimage_symm_proj_inter, inter_comm]

lemma symm_trans_target_eq (e e' : pretrivialization F proj) :
  (e.to_local_equiv.symm.trans e'.to_local_equiv).target = (e.base_set ∩ e'.base_set) ×ˢ univ :=
by rw [← local_equiv.symm_source, symm_trans_symm, symm_trans_source_eq, inter_comm]

end pretrivialization

variable [topological_space Z]

/--
A structure extending local homeomorphisms, defining a local trivialization of a projection
`proj : Z → B` with fiber `F`, as a local homeomorphism between `Z` and `B × F` defined between two
sets of the form `proj ⁻¹' base_set` and `base_set × F`, acting trivially on the first coordinate.
-/
@[ext, nolint has_nonempty_instance]
structure trivialization (proj : Z → B) extends local_homeomorph Z (B × F) :=
(base_set      : set B)
(open_base_set : is_open base_set)
(source_eq     : source = proj ⁻¹' base_set)
(target_eq     : target = base_set ×ˢ univ)
(proj_to_fun   : ∀ p ∈ source, (to_local_homeomorph p).1 = proj p)

namespace trivialization

variables {F} (e : trivialization F proj) {x : Z}

/-- Natural identification as a `pretrivialization`. -/
def to_pretrivialization : pretrivialization F proj := { ..e }

instance : has_coe_to_fun (trivialization F proj) (λ _, Z → B × F) := ⟨λ e, e.to_fun⟩
instance : has_coe (trivialization F proj) (pretrivialization F proj) :=
⟨to_pretrivialization⟩

lemma to_pretrivialization_injective :
  function.injective (λ e : trivialization F proj, e.to_pretrivialization) :=
by { intros e e', rw [pretrivialization.ext_iff, trivialization.ext_iff,
  ← local_homeomorph.to_local_equiv_injective.eq_iff], exact id }

@[simp, mfld_simps] lemma coe_coe : ⇑e.to_local_homeomorph = e := rfl
@[simp, mfld_simps] lemma coe_fst (ex : x ∈ e.source) : (e x).1 = proj x := e.proj_to_fun x ex
protected lemma eq_on : eq_on (prod.fst ∘ e) proj e.source := λ x hx, e.coe_fst hx
lemma mem_source : x ∈ e.source ↔ proj x ∈ e.base_set := by rw [e.source_eq, mem_preimage]
lemma coe_fst' (ex : proj x ∈ e.base_set) : (e x).1 = proj x := e.coe_fst (e.mem_source.2 ex)
lemma mk_proj_snd (ex : x ∈ e.source) : (proj x, (e x).2) = e x := prod.ext (e.coe_fst ex).symm rfl
lemma mk_proj_snd' (ex : proj x ∈ e.base_set) : (proj x, (e x).2) = e x :=
prod.ext (e.coe_fst' ex).symm rfl

lemma source_inter_preimage_target_inter (s : set (B × F)) :
  e.source ∩ (e ⁻¹' (e.target ∩ s)) = e.source ∩ (e ⁻¹' s) :=
e.to_local_homeomorph.source_inter_preimage_target_inter s

@[simp, mfld_simps] lemma coe_mk (e : local_homeomorph Z (B × F)) (i j k l m) (x : Z) :
  (trivialization.mk e i j k l m : trivialization F proj) x = e x := rfl

lemma mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.base_set :=
e.to_pretrivialization.mem_target

lemma map_target {x : B × F} (hx : x ∈ e.target) : e.to_local_homeomorph.symm x ∈ e.source :=
e.to_local_homeomorph.map_target hx

lemma proj_symm_apply {x : B × F} (hx : x ∈ e.target) : proj (e.to_local_homeomorph.symm x) = x.1 :=
e.to_pretrivialization.proj_symm_apply hx

lemma proj_symm_apply' {b : B} {x : F}
  (hx : b ∈ e.base_set) : proj (e.to_local_homeomorph.symm (b, x)) = b :=
e.to_pretrivialization.proj_symm_apply' hx

lemma proj_surj_on_base_set [nonempty F] : set.surj_on proj e.source e.base_set :=
e.to_pretrivialization.proj_surj_on_base_set

lemma apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.to_local_homeomorph.symm x) = x :=
e.to_local_homeomorph.right_inv hx

lemma apply_symm_apply'
  {b : B} {x : F} (hx : b ∈ e.base_set) : e (e.to_local_homeomorph.symm (b, x)) = (b, x) :=
e.to_pretrivialization.apply_symm_apply' hx

@[simp, mfld_simps] lemma symm_apply_mk_proj (ex : x ∈ e.source) :
  e.to_local_homeomorph.symm (proj x, (e x).2) = x :=
e.to_pretrivialization.symm_apply_mk_proj ex

lemma symm_trans_source_eq (e e' : trivialization F proj) :
  (e.to_local_equiv.symm.trans e'.to_local_equiv).source = (e.base_set ∩ e'.base_set) ×ˢ univ :=
pretrivialization.symm_trans_source_eq e.to_pretrivialization e'

lemma symm_trans_target_eq (e e' : trivialization F proj) :
  (e.to_local_equiv.symm.trans e'.to_local_equiv).target = (e.base_set ∩ e'.base_set) ×ˢ univ :=
pretrivialization.symm_trans_target_eq e.to_pretrivialization e'

lemma coe_fst_eventually_eq_proj (ex : x ∈ e.source) : prod.fst ∘ e =ᶠ[𝓝 x] proj  :=
mem_nhds_iff.2 ⟨e.source, λ y hy, e.coe_fst hy, e.open_source, ex⟩

lemma coe_fst_eventually_eq_proj' (ex : proj x ∈ e.base_set) : prod.fst ∘ e =ᶠ[𝓝 x] proj :=
e.coe_fst_eventually_eq_proj (e.mem_source.2 ex)

lemma map_proj_nhds (ex : x ∈ e.source) : map proj (𝓝 x) = 𝓝 (proj x) :=
by rw [← e.coe_fst ex, ← map_congr (e.coe_fst_eventually_eq_proj ex), ← map_map, ← e.coe_coe,
  e.to_local_homeomorph.map_nhds_eq ex, map_fst_nhds]

lemma preimage_subset_source {s : set B} (hb : s ⊆ e.base_set) : proj ⁻¹' s ⊆ e.source :=
λ p hp, e.mem_source.mpr (hb hp)

lemma image_preimage_eq_prod_univ {s : set B} (hb : s ⊆ e.base_set) :
  e '' (proj ⁻¹' s) = s ×ˢ univ :=
subset.antisymm (image_subset_iff.mpr (λ p hp,
  ⟨(e.proj_to_fun p (e.preimage_subset_source hb hp)).symm ▸ hp, trivial⟩)) (λ p hp,
  let hp' : p ∈ e.target := e.mem_target.mpr (hb hp.1) in
  ⟨e.inv_fun p, mem_preimage.mpr ((e.proj_symm_apply hp').symm ▸ hp.1), e.apply_symm_apply hp'⟩)

/-- The preimage of a subset of the base set is homeomorphic to the product with the fiber. -/
def preimage_homeomorph {s : set B} (hb : s ⊆ e.base_set) : proj ⁻¹' s ≃ₜ s × F :=
(e.to_local_homeomorph.homeomorph_of_image_subset_source (e.preimage_subset_source hb)
  (e.image_preimage_eq_prod_univ hb)).trans
  ((homeomorph.set.prod s univ).trans ((homeomorph.refl s).prod_congr (homeomorph.set.univ F)))

@[simp] lemma preimage_homeomorph_apply {s : set B} (hb : s ⊆ e.base_set) (p : proj ⁻¹' s) :
  e.preimage_homeomorph hb p = (⟨proj p, p.2⟩, (e p).2) :=
prod.ext (subtype.ext (e.proj_to_fun p (e.mem_source.mpr (hb p.2)))) rfl

@[simp] lemma preimage_homeomorph_symm_apply {s : set B} (hb : s ⊆ e.base_set) (p : s × F) :
  (e.preimage_homeomorph hb).symm p = ⟨e.symm (p.1, p.2), ((e.preimage_homeomorph hb).symm p).2⟩ :=
rfl

/-- The source is homeomorphic to the product of the base set with the fiber. -/
def source_homeomorph_base_set_prod : e.source ≃ₜ e.base_set × F :=
(homeomorph.set_congr e.source_eq).trans (e.preimage_homeomorph subset_rfl)

@[simp] lemma source_homeomorph_base_set_prod_apply (p : e.source) :
  e.source_homeomorph_base_set_prod p = (⟨proj p, e.mem_source.mp p.2⟩, (e p).2) :=
e.preimage_homeomorph_apply subset_rfl ⟨p, e.mem_source.mp p.2⟩

@[simp] lemma source_homeomorph_base_set_prod_symm_apply (p : e.base_set × F) :
  e.source_homeomorph_base_set_prod.symm p =
    ⟨e.symm (p.1, p.2), (e.source_homeomorph_base_set_prod.symm p).2⟩ :=
rfl

/-- Each fiber of a trivialization is homeomorphic to the specified fiber. -/
def preimage_singleton_homeomorph {b : B} (hb : b ∈ e.base_set) : proj ⁻¹' {b} ≃ₜ F :=
(e.preimage_homeomorph (set.singleton_subset_iff.mpr hb)).trans (((homeomorph.homeomorph_of_unique
  ({b} : set B) punit).prod_congr (homeomorph.refl F)).trans (homeomorph.punit_prod F))

@[simp] lemma preimage_singleton_homeomorph_apply {b : B} (hb : b ∈ e.base_set)
  (p : proj ⁻¹' {b}) : e.preimage_singleton_homeomorph hb p = (e p).2 :=
rfl

@[simp] lemma preimage_singleton_homeomorph_symm_apply {b : B} (hb : b ∈ e.base_set) (p : F) :
  (e.preimage_singleton_homeomorph hb).symm p =
    ⟨e.symm (b, p), by rw [mem_preimage, e.proj_symm_apply' hb, mem_singleton_iff]⟩ :=
rfl

/-- In the domain of a bundle trivialization, the projection is continuous-/
lemma continuous_at_proj (ex : x ∈ e.source) : continuous_at proj x :=
(e.map_proj_nhds ex).le

/-- Composition of a `trivialization` and a `homeomorph`. -/
def comp_homeomorph {Z' : Type*} [topological_space Z'] (h : Z' ≃ₜ Z) :
  trivialization F (proj ∘ h) :=
{ to_local_homeomorph := h.to_local_homeomorph.trans e.to_local_homeomorph,
  base_set := e.base_set,
  open_base_set := e.open_base_set,
  source_eq := by simp [e.source_eq, preimage_preimage],
  target_eq := by simp [e.target_eq],
  proj_to_fun := λ p hp,
    have hp : h p ∈ e.source, by simpa using hp,
    by simp [hp] }

/-- Read off the continuity of a function `f : Z → X` at `z : Z` by transferring via a
trivialization of `Z` containing `z`. -/
lemma continuous_at_of_comp_right {X : Type*} [topological_space X] {f : Z → X} {z : Z}
  (e : trivialization F proj) (he : proj z ∈ e.base_set)
  (hf : continuous_at (f ∘ e.to_local_equiv.symm) (e z)) :
  continuous_at f z :=
begin
  have hez : z ∈ e.to_local_equiv.symm.target,
  { rw [local_equiv.symm_target, e.mem_source],
    exact he },
  rwa [e.to_local_homeomorph.symm.continuous_at_iff_continuous_at_comp_right hez,
   local_homeomorph.symm_symm]
end

/-- Read off the continuity of a function `f : X → Z` at `x : X` by transferring via a
trivialization of `Z` containing `f x`. -/
lemma continuous_at_of_comp_left {X : Type*} [topological_space X] {f : X → Z} {x : X}
  (e : trivialization F proj) (hf_proj : continuous_at (proj ∘ f) x) (he : proj (f x) ∈ e.base_set)
  (hf : continuous_at (e ∘ f) x) :
  continuous_at f x :=
begin
  rw e.to_local_homeomorph.continuous_at_iff_continuous_at_comp_left,
  { exact hf },
  rw [e.source_eq, ← preimage_comp],
  exact hf_proj.preimage_mem_nhds (e.open_base_set.mem_nhds he),
end

end trivialization

variables (E : B → Type*) [topological_space (total_space E)] [∀ b, topological_space (E b)]

class fiber_bundle :=
(total_space_mk_inducing [] : ∀ (b : B), inducing (@total_space_mk B E b))
(trivialization_atlas [] : set (trivialization F (total_space.proj : total_space E → B)))
(trivialization_at [] : B → trivialization F (total_space.proj : total_space E → B))
(mem_base_set_trivialization_at [] : ∀ b : B, b ∈ (trivialization_at b).base_set)
(trivialization_mem_atlas [] : ∀ b : B, trivialization_at b ∈ trivialization_atlas)

export fiber_bundle

variables {F E} [fiber_bundle F E]

@[class] def mem_trivialization_atlas (e : trivialization F (@total_space.proj B E)) : Prop :=
e ∈ trivialization_atlas F E

namespace fiber_bundle

variables (F)
lemma map_proj_nhds (x : total_space E) : map (@total_space.proj B E) (𝓝 x) = 𝓝 (total_space.proj x) :=
(trivialization_at F E (total_space.proj x)).map_proj_nhds $
  (trivialization_at F E (total_space.proj x)).mem_source.2 $
  mem_base_set_trivialization_at F E (total_space.proj x)

variables (E)
/-- The projection from a topological fiber bundle to its base is continuous. -/
@[continuity] lemma continuous_proj : continuous (@total_space.proj B E) :=
continuous_iff_continuous_at.2 $ λ x, (map_proj_nhds F x).le

-- /-- The projection from a topological fiber bundle to its base is an open map. -/
-- lemma is_topological_fiber_bundle.is_open_map_proj (h : is_topological_fiber_bundle F proj) :
--   is_open_map proj :=
-- is_open_map.of_nhds_le $ λ x, (h.map_proj_nhds x).ge

-- /-- The projection from a topological fiber bundle with a nonempty fiber to its base is a surjective
-- map. -/
-- lemma is_topological_fiber_bundle.surjective_proj [nonempty F]
--   (h : is_topological_fiber_bundle F proj) :
--   function.surjective proj :=
-- λ b, let ⟨e, eb⟩ := h b, ⟨x, _, hx⟩ := e.proj_surj_on_base_set eb in ⟨x, hx⟩

-- /-- The projection from a topological fiber bundle with a nonempty fiber to its base is a quotient
-- map. -/
-- lemma is_topological_fiber_bundle.quotient_map_proj [nonempty F]
--   (h : is_topological_fiber_bundle F proj) :
--   quotient_map proj :=
-- h.is_open_map_proj.to_quotient_map h.continuous_proj h.surjective_proj

-- /-- The first projection in a product is a trivial topological fiber bundle. -/
-- lemma is_trivial_topological_fiber_bundle_fst :
--   is_trivial_topological_fiber_bundle F (prod.fst : B × F → B) :=
-- ⟨homeomorph.refl _, λ x, rfl⟩

-- /-- The first projection in a product is a topological fiber bundle. -/
-- lemma is_topological_fiber_bundle_fst : is_topological_fiber_bundle F (prod.fst : B × F → B) :=
-- is_trivial_topological_fiber_bundle_fst.is_topological_fiber_bundle

-- /-- The second projection in a product is a trivial topological fiber bundle. -/
-- lemma is_trivial_topological_fiber_bundle_snd :
--   is_trivial_topological_fiber_bundle F (prod.snd : F × B → B) :=
-- ⟨homeomorph.prod_comm _ _, λ x, rfl⟩

-- /-- The second projection in a product is a topological fiber bundle. -/
-- lemma is_topological_fiber_bundle_snd : is_topological_fiber_bundle F (prod.snd : F × B → B) :=
-- is_trivial_topological_fiber_bundle_snd.is_topological_fiber_bundle

-- lemma is_topological_fiber_bundle.comp_homeomorph {Z' : Type*} [topological_space Z']
--   (e : is_topological_fiber_bundle F proj) (h : Z' ≃ₜ Z) :
--   is_topological_fiber_bundle F (proj ∘ h) :=
-- λ x, let ⟨e, he⟩ := e x in
-- ⟨e.comp_homeomorph h, by simpa [topological_fiber_bundle.trivialization.comp_homeomorph] using he⟩


lemma continuous_total_space_mk (x : B) : continuous (@total_space_mk B E x) :=
(total_space_mk_inducing F E x).continuous

end fiber_bundle


namespace bundle
instance [I : topological_space F] : ∀ x : B, topological_space (trivial B F x) := λ x, I

instance [t₁ : topological_space B] [t₂ : topological_space F] :
  topological_space (total_space (trivial B F)) :=
induced total_space.proj t₁ ⊓ induced (trivial.proj_snd B F) t₂

namespace trivial

variables (B F)

/-- Local trivialization for trivial bundle. -/
def trivialization : trivialization F (@total_space.proj B (bundle.trivial B F)) :=
{ to_fun := λ x, (x.fst, x.snd),
  inv_fun := λ y, ⟨y.fst, y.snd⟩,
  source := univ,
  target := univ,
  map_source' := λ x h, mem_univ (x.fst, x.snd),
  map_target' := λ y h,  mem_univ ⟨y.fst, y.snd⟩,
  left_inv' := λ x h, sigma.eq rfl rfl,
  right_inv' := λ x h, prod.ext rfl rfl,
  open_source := is_open_univ,
  open_target := is_open_univ,
  continuous_to_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [prod.topological_space, induced_inf, induced_compose], exact le_rfl, },
  continuous_inv_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [bundle.total_space.topological_space, induced_inf, induced_compose],
    exact le_rfl, },
  base_set := univ,
  open_base_set := is_open_univ,
  source_eq := rfl,
  target_eq := by simp only [univ_prod_univ],
  proj_to_fun := λ y hy, rfl }

@[simp]
lemma trivialization_source : (trivialization B F).source = univ := rfl

@[simp]
lemma trivialization_target : (trivialization B F).target = univ := rfl

instance : fiber_bundle F (bundle.trivial B F) :=
{ trivialization_atlas := {trivialization B F},
  trivialization_at := λ x, trivialization B F,
  mem_base_set_trivialization_at := mem_univ,
  trivialization_mem_atlas := λ x, mem_singleton _,
  total_space_mk_inducing := λ b, ⟨begin
    have : (λ (x : trivial B F b), x) = @id F, by { ext x, refl },
    simp only [total_space.topological_space, induced_inf, induced_compose, function.comp,
      total_space.proj, induced_const, top_inf_eq, trivial.proj_snd, id.def,
      trivial.topological_space, this, induced_id],
  end⟩ }

-- instance : mem_trivialization_atlas (trivialization B F) := ⟨mem_singleton _⟩
variables {B F}
lemma eq_trivialization (e : _root_.trivialization F (@total_space.proj B (bundle.trivial B F)))
  [he : mem_trivialization_atlas e] : e = trivialization B F :=
mem_singleton_iff.mp he

end trivial

end bundle

end topological_fiber_bundle
