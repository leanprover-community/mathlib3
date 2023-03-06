/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import topology.order
import topology.nhds_set

/-!
# Specific classes of maps between topological spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file introduces the following properties of a map `f : X → Y` between topological spaces:

* `is_open_map f` means the image of an open set under `f` is open.
* `is_closed_map f` means the image of a closed set under `f` is closed.

(Open and closed maps need not be continuous.)

* `inducing f` means the topology on `X` is the one induced via `f` from the topology on `Y`.
  These behave like embeddings except they need not be injective. Instead, points of `X` which
  are identified by `f` are also inseparable in the topology on `X`.
* `embedding f` means `f` is inducing and also injective. Equivalently, `f` identifies `X` with
  a subspace of `Y`.
* `open_embedding f` means `f` is an embedding with open image, so it identifies `X` with an
  open subspace of `Y`. Equivalently, `f` is an embedding and an open map.
* `closed_embedding f` similarly means `f` is an embedding with closed image, so it identifies
  `X` with a closed subspace of `Y`. Equivalently, `f` is an embedding and a closed map.

* `quotient_map f` is the dual condition to `embedding f`: `f` is surjective and the topology
  on `Y` is the one coinduced via `f` from the topology on `X`. Equivalently, `f` identifies
  `Y` with a quotient of `X`. Quotient maps are also sometimes known as identification maps.

## References

* <https://en.wikipedia.org/wiki/Open_and_closed_maps>
* <https://en.wikipedia.org/wiki/Embedding#General_topology>
* <https://en.wikipedia.org/wiki/Quotient_space_(topology)#Quotient_map>

## Tags

open map, closed map, embedding, quotient map, identification map

-/

open set filter function
open_locale topology filter

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section inducing

/-- A function `f : α → β` between topological spaces is inducing if the topology on `α` is induced
by the topology on `β` through `f`, meaning that a set `s : set α` is open iff it is the preimage
under `f` of some open set `t : set β`. -/
@[mk_iff]
structure inducing [tα : topological_space α] [tβ : topological_space β] (f : α → β) : Prop :=
(induced : tα = tβ.induced f)

variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

lemma inducing_id : inducing (@id α) :=
⟨induced_id.symm⟩

protected lemma inducing.comp {g : β → γ} {f : α → β} (hg : inducing g) (hf : inducing f) :
  inducing (g ∘ f) :=
⟨by rw [hf.induced, hg.induced, induced_compose]⟩

lemma inducing_of_inducing_compose {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g)
  (hgf : inducing (g ∘ f)) : inducing f :=
⟨le_antisymm
    (by rwa ← continuous_iff_le_induced)
    (by { rw [hgf.induced, ← continuous_iff_le_induced], apply hg.comp continuous_induced_dom })⟩

lemma inducing_iff_nhds {f : α → β} : inducing f ↔ ∀ a, 𝓝 a = comap f (𝓝 (f a)) :=
(inducing_iff _).trans (induced_iff_nhds_eq f)

lemma inducing.nhds_eq_comap {f : α → β} (hf : inducing f) :
  ∀ (a : α), 𝓝 a = comap f (𝓝 $ f a) :=
inducing_iff_nhds.1 hf

lemma inducing.nhds_set_eq_comap {f : α → β} (hf : inducing f) (s : set α) :
  𝓝ˢ s = comap f (𝓝ˢ (f '' s)) :=
by simp only [nhds_set, Sup_image, comap_supr, hf.nhds_eq_comap, supr_image]

lemma inducing.map_nhds_eq {f : α → β} (hf : inducing f) (a : α) :
  (𝓝 a).map f = 𝓝[range f] (f a) :=
hf.induced.symm ▸ map_nhds_induced_eq a

lemma inducing.map_nhds_of_mem {f : α → β} (hf : inducing f) (a : α) (h : range f ∈ 𝓝 (f a)) :
  (𝓝 a).map f = 𝓝 (f a) :=
hf.induced.symm ▸ map_nhds_induced_of_mem h

lemma inducing.image_mem_nhds_within {f : α → β} (hf : inducing f) {a : α} {s : set α}
  (hs : s ∈ 𝓝 a) : f '' s ∈ 𝓝[range f] (f a) :=
hf.map_nhds_eq a ▸ image_mem_map hs

lemma inducing.tendsto_nhds_iff {ι : Type*}
  {f : ι → β} {g : β → γ} {a : filter ι} {b : β} (hg : inducing g) :
  tendsto f a (𝓝 b) ↔ tendsto (g ∘ f) a (𝓝 (g b)) :=
by rw [hg.nhds_eq_comap, tendsto_comap_iff]

lemma inducing.continuous_at_iff {f : α → β} {g : β → γ} (hg : inducing g) {x : α} :
  continuous_at f x ↔ continuous_at (g ∘ f) x :=
by simp_rw [continuous_at, inducing.tendsto_nhds_iff hg]

lemma inducing.continuous_iff {f : α → β} {g : β → γ} (hg : inducing g) :
  continuous f ↔ continuous (g ∘ f) :=
by simp_rw [continuous_iff_continuous_at, hg.continuous_at_iff]

lemma inducing.continuous_at_iff' {f : α → β} {g : β → γ} (hf : inducing f) {x : α}
  (h : range f ∈ 𝓝 (f x)) : continuous_at (g ∘ f) x ↔ continuous_at g (f x) :=
by { simp_rw [continuous_at, filter.tendsto, ← hf.map_nhds_of_mem _ h, filter.map_map] }

protected lemma inducing.continuous {f : α → β} (hf : inducing f) : continuous f :=
hf.continuous_iff.mp continuous_id

protected lemma inducing.inducing_iff {f : α → β} {g : β → γ} (hg : inducing g) :
  inducing f ↔ inducing (g ∘ f) :=
begin
  refine ⟨λ h, hg.comp h, λ hgf, inducing_of_inducing_compose _ hg.continuous hgf⟩,
  rw hg.continuous_iff,
  exact hgf.continuous
end

lemma inducing.closure_eq_preimage_closure_image {f : α → β} (hf : inducing f) (s : set α) :
  closure s = f ⁻¹' closure (f '' s) :=
by { ext x, rw [set.mem_preimage, ← closure_induced, hf.induced] }

lemma inducing.is_closed_iff {f : α → β} (hf : inducing f) {s : set α} :
  is_closed s ↔ ∃ t, is_closed t ∧ f ⁻¹' t = s :=
by rw [hf.induced, is_closed_induced_iff]

lemma inducing.is_closed_iff' {f : α → β} (hf : inducing f) {s : set α} :
  is_closed s ↔ ∀ x, f x ∈ closure (f '' s) → x ∈ s :=
by rw [hf.induced, is_closed_induced_iff']

lemma inducing.is_closed_preimage {f : α → β} (h : inducing f) (s : set β) (hs : is_closed s) :
  is_closed (f ⁻¹' s) :=
(inducing.is_closed_iff h).mpr ⟨s, hs, rfl⟩

lemma inducing.is_open_iff {f : α → β} (hf : inducing f) {s : set α} :
  is_open s ↔ ∃ t, is_open t ∧ f ⁻¹' t = s :=
by rw [hf.induced, is_open_induced_iff]

lemma inducing.dense_iff {f : α → β} (hf : inducing f) {s : set α} :
  dense s ↔ ∀ x, f x ∈ closure (f '' s) :=
by simp only [dense, hf.closure_eq_preimage_closure_image, mem_preimage]

end inducing

section embedding

/-- A function between topological spaces is an embedding if it is injective,
  and for all `s : set α`, `s` is open iff it is the preimage of an open set. -/
@[mk_iff] structure embedding [tα : topological_space α] [tβ : topological_space β] (f : α → β)
  extends inducing f : Prop :=
(inj : injective f)

lemma function.injective.embedding_induced [t : topological_space β]
  {f : α → β} (hf : injective f) :
  @_root_.embedding α β (t.induced f) t f :=
{ induced := rfl,
  inj := hf }

variables [topological_space α] [topological_space β] [topological_space γ]

lemma embedding.mk' (f : α → β) (inj : injective f)
  (induced : ∀ a, comap f (𝓝 (f a)) = 𝓝 a) : embedding f :=
⟨inducing_iff_nhds.2 (λ a, (induced a).symm), inj⟩

lemma embedding_id : embedding (@id α) :=
⟨inducing_id, assume a₁ a₂ h, h⟩

lemma embedding.comp {g : β → γ} {f : α → β} (hg : embedding g) (hf : embedding f) :
  embedding (g ∘ f) :=
{ inj:= assume a₁ a₂ h, hf.inj $ hg.inj h,
  ..hg.to_inducing.comp hf.to_inducing }

lemma embedding_of_embedding_compose {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g)
  (hgf : embedding (g ∘ f)) : embedding f :=
{ induced := (inducing_of_inducing_compose hf hg hgf.to_inducing).induced,
  inj := assume a₁ a₂ h, hgf.inj $ by simp [h, (∘)] }

protected lemma function.left_inverse.embedding {f : α → β} {g : β → α}
  (h : left_inverse f g) (hf : continuous f) (hg : continuous g) :
  embedding g :=
embedding_of_embedding_compose hg hf $ h.comp_eq_id.symm ▸ embedding_id

lemma embedding.map_nhds_eq {f : α → β} (hf : embedding f) (a : α) :
  (𝓝 a).map f = 𝓝[range f] (f a) :=
hf.1.map_nhds_eq a

lemma embedding.map_nhds_of_mem {f : α → β}
  (hf : embedding f) (a : α) (h : range f ∈ 𝓝 (f a)) : (𝓝 a).map f = 𝓝 (f a) :=
hf.1.map_nhds_of_mem a h

lemma embedding.tendsto_nhds_iff {ι : Type*}
  {f : ι → β} {g : β → γ} {a : filter ι} {b : β} (hg : embedding g) :
  tendsto f a (𝓝 b) ↔ tendsto (g ∘ f) a (𝓝 (g b)) :=
hg.to_inducing.tendsto_nhds_iff

lemma embedding.continuous_iff {f : α → β} {g : β → γ} (hg : embedding g) :
  continuous f ↔ continuous (g ∘ f) :=
inducing.continuous_iff hg.1

lemma embedding.continuous {f : α → β} (hf : embedding f) : continuous f :=
inducing.continuous hf.1

lemma embedding.closure_eq_preimage_closure_image {e : α → β} (he : embedding e) (s : set α) :
  closure s = e ⁻¹' closure (e '' s) :=
he.1.closure_eq_preimage_closure_image s

/-- The topology induced under an inclusion `f : X → Y` from the discrete topological space `Y`
is the discrete topology on `X`. -/
lemma embedding.discrete_topology {X Y : Type*} [topological_space X] [tY : topological_space Y]
  [discrete_topology Y] {f : X → Y} (hf : embedding f) : discrete_topology X :=
discrete_topology_iff_nhds.2 $ λ x, by rw [hf.nhds_eq_comap, nhds_discrete, comap_pure,
  ← image_singleton, hf.inj.preimage_image, principal_singleton]

end embedding

/-- A function between topological spaces is a quotient map if it is surjective,
  and for all `s : set β`, `s` is open iff its preimage is an open set. -/
def quotient_map {α : Type*} {β : Type*} [tα : topological_space α] [tβ : topological_space β]
  (f : α → β) : Prop :=
surjective f ∧ tβ = tα.coinduced f

lemma quotient_map_iff {α β : Type*} [topological_space α] [topological_space β] {f : α → β} :
  quotient_map f ↔ surjective f ∧ ∀ s : set β, is_open s ↔ is_open (f ⁻¹' s) :=
and_congr iff.rfl topological_space_eq_iff

namespace quotient_map

variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]
  {g : β → γ} {f : α → β}

protected lemma id : quotient_map (@id α) :=
⟨assume a, ⟨a, rfl⟩, coinduced_id.symm⟩

protected lemma comp (hg : quotient_map g) (hf : quotient_map f) :
  quotient_map (g ∘ f) :=
⟨hg.left.comp hf.left, by rw [hg.right, hf.right, coinduced_compose]⟩

protected lemma of_quotient_map_compose (hf : continuous f) (hg : continuous g)
  (hgf : quotient_map (g ∘ f)) : quotient_map g :=
⟨hgf.1.of_comp,
  le_antisymm
    (by { rw [hgf.right, ← continuous_iff_coinduced_le], apply continuous_coinduced_rng.comp hf })
    (by rwa ← continuous_iff_coinduced_le)⟩

lemma of_inverse {g : β → α} (hf : continuous f) (hg : continuous g) (h : left_inverse g f) :
  quotient_map g :=
quotient_map.of_quotient_map_compose hf hg $ h.comp_eq_id.symm ▸ quotient_map.id

protected lemma continuous_iff (hf : quotient_map f) :
  continuous g ↔ continuous (g ∘ f) :=
by rw [continuous_iff_coinduced_le, continuous_iff_coinduced_le, hf.right, coinduced_compose]

protected lemma continuous (hf : quotient_map f) : continuous f :=
hf.continuous_iff.mp continuous_id

protected lemma surjective (hf : quotient_map f) : surjective f := hf.1

protected lemma is_open_preimage (hf : quotient_map f) {s : set β} :
  is_open (f ⁻¹' s) ↔ is_open s :=
((quotient_map_iff.1 hf).2 s).symm

protected lemma is_closed_preimage (hf : quotient_map f) {s : set β} :
  is_closed (f ⁻¹' s) ↔ is_closed s :=
by simp only [← is_open_compl_iff, ← preimage_compl, hf.is_open_preimage]

end quotient_map

/-- A map `f : α → β` is said to be an *open map*, if the image of any open `U : set α`
is open in `β`. -/
def is_open_map [topological_space α] [topological_space β] (f : α → β) :=
∀ U : set α, is_open U → is_open (f '' U)

namespace is_open_map
variables [topological_space α] [topological_space β] [topological_space γ] {f : α → β}

protected lemma id : is_open_map (@id α) := assume s hs, by rwa [image_id]

protected lemma comp
  {g : β → γ} {f : α → β} (hg : is_open_map g) (hf : is_open_map f) : is_open_map (g ∘ f) :=
by intros s hs; rw [image_comp]; exact hg _ (hf _ hs)

lemma is_open_range (hf : is_open_map f) : is_open (range f) :=
by { rw ← image_univ, exact hf _ is_open_univ }

lemma image_mem_nhds (hf : is_open_map f) {x : α} {s : set α} (hx : s ∈ 𝓝 x) :
  f '' s ∈ 𝓝 (f x) :=
let ⟨t, hts, ht, hxt⟩ := mem_nhds_iff.1 hx in
mem_of_superset (is_open.mem_nhds (hf t ht) (mem_image_of_mem _ hxt)) (image_subset _ hts)

lemma range_mem_nhds (hf : is_open_map f) (x : α) : range f ∈ 𝓝 (f x) :=
hf.is_open_range.mem_nhds $ mem_range_self _

lemma maps_to_interior (hf : is_open_map f) {s : set α} {t : set β} (h : maps_to f s t) :
  maps_to f (interior s) (interior t) :=
maps_to'.2 $ interior_maximal (h.mono interior_subset subset.rfl).image_subset
  (hf _ is_open_interior)

lemma image_interior_subset (hf : is_open_map f) (s : set α) :
  f '' interior s ⊆ interior (f '' s) :=
(hf.maps_to_interior (maps_to_image f s)).image_subset

lemma nhds_le (hf : is_open_map f) (a : α) : 𝓝 (f a) ≤ (𝓝 a).map f :=
le_map $ λ s, hf.image_mem_nhds

lemma of_nhds_le (hf : ∀ a, 𝓝 (f a) ≤ map f (𝓝 a)) : is_open_map f :=
λ s hs, is_open_iff_mem_nhds.2 $ λ b ⟨a, has, hab⟩,
  hab ▸ hf _ (image_mem_map $ is_open.mem_nhds hs has)

lemma of_sections {f : α → β}
  (h : ∀ x, ∃ g : β → α, continuous_at g (f x) ∧ g (f x) = x ∧ right_inverse g f) :
  is_open_map f :=
of_nhds_le $ λ x, let ⟨g, hgc, hgx, hgf⟩ := h x in
calc 𝓝 (f x) = map f (map g (𝓝 (f x))) : by rw [map_map, hgf.comp_eq_id, map_id]
... ≤ map f (𝓝 (g (f x))) : map_mono hgc
... = map f (𝓝 x) : by rw hgx

lemma of_inverse {f : α → β} {f' : β → α}
  (h : continuous f') (l_inv : left_inverse f f') (r_inv : right_inverse f f') :
  is_open_map f :=
of_sections $ λ x, ⟨f', h.continuous_at, r_inv _, l_inv⟩

/-- A continuous surjective open map is a quotient map. -/
lemma to_quotient_map {f : α → β}
  (open_map : is_open_map f) (cont : continuous f) (surj : surjective f) :
  quotient_map f :=
quotient_map_iff.2 ⟨surj, λ s, ⟨λ h, h.preimage cont, λ h, surj.image_preimage s ▸ open_map _ h⟩⟩

lemma interior_preimage_subset_preimage_interior (hf : is_open_map f) {s : set β} :
  interior (f⁻¹' s) ⊆ f⁻¹' (interior s) :=
hf.maps_to_interior (maps_to_preimage _ _)

lemma preimage_interior_eq_interior_preimage (hf₁ : is_open_map f) (hf₂ : continuous f)
  (s : set β) :
  f⁻¹' (interior s) = interior (f⁻¹' s) :=
subset.antisymm
  (preimage_interior_subset_interior_preimage hf₂)
  (interior_preimage_subset_preimage_interior hf₁)

lemma preimage_closure_subset_closure_preimage (hf : is_open_map f) {s : set β} :
  f ⁻¹' (closure s) ⊆ closure (f ⁻¹' s) :=
begin
  rw ← compl_subset_compl,
  simp only [← interior_compl, ← preimage_compl, hf.interior_preimage_subset_preimage_interior]
end

lemma preimage_closure_eq_closure_preimage (hf : is_open_map f) (hfc : continuous f) (s : set β) :
  f ⁻¹' (closure s) = closure (f ⁻¹' s) :=
hf.preimage_closure_subset_closure_preimage.antisymm (hfc.closure_preimage_subset s)

lemma preimage_frontier_subset_frontier_preimage (hf : is_open_map f) {s : set β} :
  f ⁻¹' (frontier s) ⊆ frontier (f ⁻¹' s) :=
by simpa only [frontier_eq_closure_inter_closure, preimage_inter]
  using inter_subset_inter hf.preimage_closure_subset_closure_preimage
    hf.preimage_closure_subset_closure_preimage

lemma preimage_frontier_eq_frontier_preimage (hf : is_open_map f) (hfc : continuous f) (s : set β) :
  f ⁻¹' (frontier s) = frontier (f ⁻¹' s) :=
by simp only [frontier_eq_closure_inter_closure, preimage_inter, preimage_compl,
  hf.preimage_closure_eq_closure_preimage hfc]

end is_open_map

lemma is_open_map_iff_nhds_le [topological_space α] [topological_space β] {f : α → β} :
  is_open_map f ↔ ∀(a:α), 𝓝 (f a) ≤ (𝓝 a).map f :=
⟨λ hf, hf.nhds_le, is_open_map.of_nhds_le⟩

lemma is_open_map_iff_interior [topological_space α] [topological_space β] {f : α → β} :
  is_open_map f ↔ ∀ s, f '' (interior s) ⊆ interior (f '' s) :=
⟨is_open_map.image_interior_subset, λ hs u hu, subset_interior_iff_is_open.mp $
  calc f '' u = f '' (interior u) : by rw hu.interior_eq
          ... ⊆ interior (f '' u) : hs u⟩

/-- An inducing map with an open range is an open map. -/
protected lemma inducing.is_open_map [topological_space α] [topological_space β] {f : α → β}
  (hi : inducing f) (ho : is_open (range f)) :
  is_open_map f :=
is_open_map.of_nhds_le $ λ x, (hi.map_nhds_of_mem _ $ is_open.mem_nhds ho $ mem_range_self _).ge

section is_closed_map
variables [topological_space α] [topological_space β]

/-- A map `f : α → β` is said to be a *closed map*, if the image of any closed `U : set α`
is closed in `β`. -/
def is_closed_map (f : α → β) := ∀ U : set α, is_closed U → is_closed (f '' U)

end is_closed_map

namespace is_closed_map

variables [topological_space α] [topological_space β] [topological_space γ]
open function

protected lemma id : is_closed_map (@id α) := assume s hs, by rwa image_id

protected lemma comp {g : β → γ} {f : α → β} (hg : is_closed_map g) (hf : is_closed_map f) :
  is_closed_map (g ∘ f) :=
by { intros s hs, rw image_comp, exact hg _ (hf _ hs) }

lemma closure_image_subset {f : α → β} (hf : is_closed_map f) (s : set α) :
  closure (f '' s) ⊆ f '' closure s :=
closure_minimal (image_subset _ subset_closure) (hf _ is_closed_closure)

lemma of_inverse {f : α → β} {f' : β → α}
  (h : continuous f') (l_inv : left_inverse f f') (r_inv : right_inverse f f') :
  is_closed_map f :=
assume s hs,
have f' ⁻¹' s = f '' s, by ext x; simp [mem_image_iff_of_inverse r_inv l_inv],
this ▸ hs.preimage h

lemma of_nonempty {f : α → β} (h : ∀ s, is_closed s → s.nonempty → is_closed (f '' s)) :
  is_closed_map f :=
begin
  intros s hs, cases eq_empty_or_nonempty s with h2s h2s,
  { simp_rw [h2s, image_empty, is_closed_empty] },
  { exact h s hs h2s }
end

lemma closed_range {f : α → β} (hf : is_closed_map f) : is_closed (range f) :=
@image_univ _ _ f ▸ hf _ is_closed_univ

end is_closed_map

lemma inducing.is_closed_map [topological_space α] [topological_space β]
  {f : α → β} (hf : inducing f) (h : is_closed (range f)) : is_closed_map f :=
begin
  intros s hs,
  rcases hf.is_closed_iff.1 hs with ⟨t, ht, rfl⟩,
  rw image_preimage_eq_inter_range,
  exact ht.inter h
end

lemma is_closed_map_iff_closure_image [topological_space α] [topological_space β] {f : α → β} :
  is_closed_map f ↔ ∀ s, closure (f '' s) ⊆ f '' closure s :=
⟨is_closed_map.closure_image_subset, λ hs c hc, is_closed_of_closure_subset $
  calc closure (f '' c) ⊆ f '' (closure c) : hs c
                    ... = f '' c : by rw hc.closure_eq⟩

section open_embedding
variables [topological_space α] [topological_space β] [topological_space γ]

/-- An open embedding is an embedding with open image. -/
@[mk_iff]
structure open_embedding (f : α → β) extends _root_.embedding f : Prop :=
(open_range : is_open $ range f)

lemma open_embedding.is_open_map {f : α → β} (hf : open_embedding f) : is_open_map f :=
hf.to_embedding.to_inducing.is_open_map hf.open_range

lemma open_embedding.map_nhds_eq {f : α → β} (hf : open_embedding f) (a : α) :
  map f (𝓝 a) = 𝓝 (f a) :=
hf.to_embedding.map_nhds_of_mem _ $ hf.open_range.mem_nhds $ mem_range_self _

lemma open_embedding.open_iff_image_open {f : α → β} (hf : open_embedding f)
  {s : set α} : is_open s ↔ is_open (f '' s) :=
⟨hf.is_open_map s,
 λ h, begin
   convert ← h.preimage hf.to_embedding.continuous,
   apply preimage_image_eq _ hf.inj
 end⟩

lemma open_embedding.tendsto_nhds_iff {ι : Type*}
  {f : ι → β} {g : β → γ} {a : filter ι} {b : β} (hg : open_embedding g) :
  tendsto f a (𝓝 b) ↔ tendsto (g ∘ f) a (𝓝 (g b)) :=
hg.to_embedding.tendsto_nhds_iff

lemma open_embedding.continuous {f : α → β} (hf : open_embedding f) : continuous f :=
hf.to_embedding.continuous

lemma open_embedding.open_iff_preimage_open {f : α → β} (hf : open_embedding f)
  {s : set β} (hs : s ⊆ range f) : is_open s ↔ is_open (f ⁻¹' s) :=
begin
  convert ←hf.open_iff_image_open.symm,
  rwa [image_preimage_eq_inter_range, inter_eq_self_of_subset_left]
end

lemma open_embedding_of_embedding_open {f : α → β} (h₁ : embedding f)
  (h₂ : is_open_map f) : open_embedding f :=
⟨h₁, h₂.is_open_range⟩

lemma open_embedding_iff_embedding_open {f : α → β} :
  open_embedding f ↔ embedding f ∧ is_open_map f :=
⟨λ h, ⟨h.1, h.is_open_map⟩, λ h, open_embedding_of_embedding_open h.1 h.2⟩

lemma open_embedding_of_continuous_injective_open {f : α → β} (h₁ : continuous f)
  (h₂ : injective f) (h₃ : is_open_map f) : open_embedding f :=
begin
  simp only [open_embedding_iff_embedding_open, embedding_iff, inducing_iff_nhds, *, and_true],
  exact λ a, le_antisymm (h₁.tendsto _).le_comap
    (@comap_map _ _ (𝓝 a) _ h₂ ▸ comap_mono (h₃.nhds_le _))
end

lemma open_embedding_iff_continuous_injective_open {f : α → β} :
  open_embedding f ↔ continuous f ∧ injective f ∧ is_open_map f :=
⟨λ h, ⟨h.continuous, h.inj, h.is_open_map⟩,
  λ h, open_embedding_of_continuous_injective_open h.1 h.2.1 h.2.2⟩

lemma open_embedding_id : open_embedding (@id α) :=
⟨embedding_id, is_open_map.id.is_open_range⟩

lemma open_embedding.comp {g : β → γ} {f : α → β}
  (hg : open_embedding g) (hf : open_embedding f) : open_embedding (g ∘ f) :=
⟨hg.1.comp hf.1, (hg.is_open_map.comp hf.is_open_map).is_open_range⟩

lemma open_embedding.is_open_map_iff {g : β → γ} {f : α → β} (hg : open_embedding g) :
  is_open_map f ↔ is_open_map (g ∘ f) :=
by simp only [is_open_map_iff_nhds_le, ← @map_map _ _ _ _ f g, ← hg.map_nhds_eq,
  map_le_map_iff hg.inj]

lemma open_embedding.of_comp_iff (f : α → β) {g : β → γ} (hg : open_embedding g) :
  open_embedding (g ∘ f) ↔ open_embedding f :=
by simp only [open_embedding_iff_continuous_injective_open, ← hg.is_open_map_iff,
  ← hg.1.continuous_iff, hg.inj.of_comp_iff]

lemma open_embedding.of_comp (f : α → β) {g : β → γ} (hg : open_embedding g)
  (h : open_embedding (g ∘ f)) : open_embedding f :=
(open_embedding.of_comp_iff f hg).1 h

end open_embedding

section closed_embedding
variables [topological_space α] [topological_space β] [topological_space γ]

/-- A closed embedding is an embedding with closed image. -/
@[mk_iff]
structure closed_embedding (f : α → β) extends _root_.embedding f : Prop :=
(closed_range : is_closed $ range f)

variables {f : α → β}

lemma closed_embedding.tendsto_nhds_iff {ι : Type*}
  {g : ι → α} {a : filter ι} {b : α} (hf : closed_embedding f) :
  tendsto g a (𝓝 b) ↔ tendsto (f ∘ g) a (𝓝 (f b)) :=
hf.to_embedding.tendsto_nhds_iff

lemma closed_embedding.continuous (hf : closed_embedding f) : continuous f :=
hf.to_embedding.continuous

lemma closed_embedding.is_closed_map (hf : closed_embedding f) : is_closed_map f :=
hf.to_embedding.to_inducing.is_closed_map hf.closed_range

lemma closed_embedding.closed_iff_image_closed (hf : closed_embedding f)
  {s : set α} : is_closed s ↔ is_closed (f '' s) :=
⟨hf.is_closed_map s,
 λ h, begin
   convert ←continuous_iff_is_closed.mp hf.continuous _ h,
   apply preimage_image_eq _ hf.inj
 end⟩

lemma closed_embedding.closed_iff_preimage_closed (hf : closed_embedding f)
  {s : set β} (hs : s ⊆ range f) : is_closed s ↔ is_closed (f ⁻¹' s) :=
begin
  convert ←hf.closed_iff_image_closed.symm,
  rwa [image_preimage_eq_inter_range, inter_eq_self_of_subset_left]
end

lemma closed_embedding_of_embedding_closed (h₁ : embedding f)
  (h₂ : is_closed_map f) : closed_embedding f :=
⟨h₁, by convert h₂ univ is_closed_univ; simp⟩

lemma closed_embedding_of_continuous_injective_closed (h₁ : continuous f)
  (h₂ : injective f) (h₃ : is_closed_map f) : closed_embedding f :=
begin
  refine closed_embedding_of_embedding_closed ⟨⟨_⟩, h₂⟩ h₃,
  apply le_antisymm (continuous_iff_le_induced.mp h₁) _,
  intro s',
  change is_open _ ≤ is_open _,
  rw [←is_closed_compl_iff, ←is_closed_compl_iff],
  generalize : s'ᶜ = s,
  rw is_closed_induced_iff,
  refine λ hs, ⟨f '' s, h₃ s hs, _⟩,
  rw preimage_image_eq _ h₂
end

lemma closed_embedding_id : closed_embedding (@id α) :=
⟨embedding_id, by convert is_closed_univ; apply range_id⟩

lemma closed_embedding.comp {g : β → γ} {f : α → β}
  (hg : closed_embedding g) (hf : closed_embedding f) : closed_embedding (g ∘ f) :=
⟨hg.to_embedding.comp hf.to_embedding, show is_closed (range (g ∘ f)),
 by rw [range_comp, ←hg.closed_iff_image_closed]; exact hf.closed_range⟩

lemma closed_embedding.closure_image_eq {f : α → β} (hf : closed_embedding f) (s : set α) :
  closure (f '' s) = f '' closure s :=
(hf.is_closed_map.closure_image_subset _).antisymm
  (image_closure_subset_closure_image hf.continuous)

end closed_embedding
