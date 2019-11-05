/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import topology.order

/-!
# Specific classes of maps between topological spaces

This file introduces the following properties of a map `f : X → Y` between topological spaces:

* `is_open_map f` means the image of an open set under `f` is open.
* `is_closed_map f` means the image of a closed set under `f` is closed.

(Open and closed maps need not be continuous.)

* `inducing f` means the topology on `X` is the one induced via `f` from the topology on `Y`.
  These behave like embeddings except they need not be injective. Instead, points of `X` which
  are identified by `f` are also indistinguishable in the topology on `X`.
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

* https://en.wikipedia.org/wiki/Open_and_closed_maps
* https://en.wikipedia.org/wiki/Embedding#General_topology
* https://en.wikipedia.org/wiki/Quotient_space_(topology)#Quotient_map

## Tags

open map, closed map, embedding, quotient map, identification map

-/

open set filter lattice

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section inducing
structure inducing [tα : topological_space α] [tβ : topological_space β] (f : α → β) : Prop :=
(induced : tα = tβ.induced f)

variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

lemma inducing_id : inducing (@id α) :=
⟨induced_id.symm⟩

lemma inducing.comp {f : α → β} {g : β → γ} (hg : inducing g) (hf : inducing f) :
  inducing (g ∘ f) :=
⟨by rw [hf.induced, hg.induced, induced_compose]⟩

lemma inducing_of_inducing_compose {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g)
  (hgf : inducing (g ∘ f)) : inducing f :=
⟨le_antisymm
    (by rwa ← continuous_iff_le_induced)
    (by { rw [hgf.induced, ← continuous_iff_le_induced], apply hg.comp continuous_induced_dom })⟩

lemma inducing_open {f : α → β} {s : set α}
  (hf : inducing f) (h : is_open (range f)) (hs : is_open s) : is_open (f '' s) :=
let ⟨t, ht, h_eq⟩ := by rw [hf.induced] at hs; exact hs in
have is_open (t ∩ range f), from is_open_inter ht h,
h_eq ▸ by rwa [image_preimage_eq_inter_range]

lemma inducing_is_closed {f : α → β} {s : set α}
  (hf : inducing f) (h : is_closed (range f)) (hs : is_closed s) : is_closed (f '' s) :=
let ⟨t, ht, h_eq⟩ := by rw [hf.induced, is_closed_induced_iff] at hs; exact hs in
have is_closed (t ∩ range f), from is_closed_inter ht h,
h_eq.symm ▸ by rwa [image_preimage_eq_inter_range]

lemma inducing.nhds_eq_comap {f : α → β} (hf : inducing f) :
  ∀ (a : α), nhds a = comap f (nhds $ f a) :=
(induced_iff_nhds_eq f).1 hf.induced

lemma inducing.map_nhds_eq {f : α → β} (hf : inducing f) (a : α) (h : range f ∈ nhds (f a)) :
  (nhds a).map f = nhds (f a) :=
hf.induced.symm ▸ map_nhds_induced_eq h

lemma inducing.tendsto_nhds_iff {ι : Type*}
  {f : ι → β} {g : β → γ} {a : filter ι} {b : β} (hg : inducing g) :
  tendsto f a (nhds b) ↔ tendsto (g ∘ f) a (nhds (g b)) :=
by rw [tendsto, tendsto, hg.induced, nhds_induced, ← map_le_iff_le_comap, filter.map_map]

lemma inducing.continuous_iff {f : α → β} {g : β → γ} (hg : inducing g) :
  continuous f ↔ continuous (g ∘ f) :=
by simp [continuous_iff_continuous_at, continuous_at, inducing.tendsto_nhds_iff hg]

lemma inducing.continuous {f : α → β} (hf : inducing f) : continuous f :=
hf.continuous_iff.mp continuous_id
end inducing
section embedding

/-- A function between topological spaces is an embedding if it is injective,
  and for all `s : set α`, `s` is open iff it is the preimage of an open set. -/
structure embedding [tα : topological_space α] [tβ : topological_space β] (f : α → β)
  extends inducing f : Prop :=
(inj : function.injective f)

variables [topological_space α] [topological_space β] [topological_space γ]

lemma embedding.mk' (f : α → β) (inj : function.injective f)
  (induced : ∀a, comap f (nhds (f a)) = nhds a) : embedding f :=
⟨⟨(induced_iff_nhds_eq f).2 (λ a, (induced a).symm)⟩, inj⟩

lemma embedding_id : embedding (@id α) :=
⟨inducing_id, assume a₁ a₂ h, h⟩

lemma embedding.comp {f : α → β} {g : β → γ} (hg : embedding g) (hf : embedding f) :
  embedding (g ∘ f) :=
{ inj:= assume a₁ a₂ h, hf.inj $ hg.inj h,
  ..hg.to_inducing.comp hf.to_inducing }

lemma embedding_of_embedding_compose {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g)
  (hgf : embedding (g ∘ f)) : embedding f :=
{ induced := (inducing_of_inducing_compose hf hg hgf.to_inducing).induced,
  inj := assume a₁ a₂ h, hgf.inj $ by simp [h, (∘)] }

lemma embedding_open {f : α → β} {s : set α}
  (hf : embedding f) (h : is_open (range f)) (hs : is_open s) : is_open (f '' s) :=
inducing_open hf.1 h hs

lemma embedding_is_closed {f : α → β} {s : set α}
  (hf : embedding f) (h : is_closed (range f)) (hs : is_closed s) : is_closed (f '' s) :=
inducing_is_closed hf.1 h hs

lemma embedding.map_nhds_eq {f : α → β}
  (hf : embedding f) (a : α) (h : range f ∈ nhds (f a)) : (nhds a).map f = nhds (f a) :=
inducing.map_nhds_eq hf.1 a h

lemma embedding.tendsto_nhds_iff {ι : Type*}
  {f : ι → β} {g : β → γ} {a : filter ι} {b : β} (hg : embedding g) :
  tendsto f a (nhds b) ↔ tendsto (g ∘ f) a (nhds (g b)) :=
by rw [tendsto, tendsto, hg.induced, nhds_induced, ← map_le_iff_le_comap, filter.map_map]

lemma embedding.continuous_iff {f : α → β} {g : β → γ} (hg : embedding g) :
  continuous f ↔ continuous (g ∘ f) :=
inducing.continuous_iff hg.1

lemma embedding.continuous {f : α → β} (hf : embedding f) : continuous f :=
inducing.continuous hf.1

lemma embedding.closure_eq_preimage_closure_image {e : α → β} (he : embedding e) (s : set α) :
  closure s = e ⁻¹' closure (e '' s) :=
by { ext x, rw [set.mem_preimage, ← closure_induced he.inj, he.induced] }

end embedding


/-- A function between topological spaces is a quotient map if it is surjective,
  and for all `s : set β`, `s` is open iff its preimage is an open set. -/
def quotient_map {α : Type*} {β : Type*} [tα : topological_space α] [tβ : topological_space β] (f : α → β) : Prop :=
function.surjective f ∧ tβ = tα.coinduced f

namespace quotient_map
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

protected lemma id : quotient_map (@id α) :=
⟨assume a, ⟨a, rfl⟩, coinduced_id.symm⟩

protected lemma comp {f : α → β} {g : β → γ} (hf : quotient_map f) (hg : quotient_map g) :
  quotient_map (g ∘ f) :=
⟨function.surjective_comp hg.left hf.left, by rw [hg.right, hf.right, coinduced_compose]⟩

protected lemma of_quotient_map_compose {f : α → β} {g : β → γ}
  (hf : continuous f) (hg : continuous g)
  (hgf : quotient_map (g ∘ f)) : quotient_map g :=
⟨assume b, let ⟨a, h⟩ := hgf.left b in ⟨f a, h⟩,
  le_antisymm
    (by rw [hgf.right, ← continuous_iff_coinduced_le];
        apply continuous_coinduced_rng.comp hf)
    (by rwa ← continuous_iff_coinduced_le)⟩

protected lemma continuous_iff {f : α → β} {g : β → γ} (hf : quotient_map f) :
  continuous g ↔ continuous (g ∘ f) :=
by rw [continuous_iff_coinduced_le, continuous_iff_coinduced_le, hf.right, coinduced_compose]

protected lemma continuous {f : α → β} (hf : quotient_map f) : continuous f :=
hf.continuous_iff.mp continuous_id

end quotient_map

section is_open_map
variables [topological_space α] [topological_space β]

def is_open_map (f : α → β) := ∀ U : set α, is_open U → is_open (f '' U)

lemma is_open_map_iff_nhds_le (f : α → β) : is_open_map f ↔ ∀(a:α), nhds (f a) ≤ (nhds a).map f :=
begin
  split,
  { assume h a s hs,
    rcases mem_nhds_sets_iff.1 hs with ⟨t, hts, ht, hat⟩,
    exact filter.mem_sets_of_superset
      (mem_nhds_sets (h t ht) (mem_image_of_mem _ hat))
      (image_subset_iff.2 hts) },
  { refine assume h s hs, is_open_iff_mem_nhds.2 _,
    rintros b ⟨a, ha, rfl⟩,
    exact h _ (filter.image_mem_map $ mem_nhds_sets hs ha) }
end

end is_open_map

namespace is_open_map
variables [topological_space α] [topological_space β] [topological_space γ]
open function

protected lemma id : is_open_map (@id α) := assume s hs, by rwa [image_id]

protected lemma comp
  {f : α → β} {g : β → γ} (hf : is_open_map f) (hg : is_open_map g) : is_open_map (g ∘ f) :=
by intros s hs; rw [image_comp]; exact hg _ (hf _ hs)

lemma of_inverse {f : α → β} {f' : β → α}
  (h : continuous f') (l_inv : left_inverse f f') (r_inv : right_inverse f f') :
  is_open_map f :=
assume s hs,
have f' ⁻¹' s = f '' s, by ext x; simp [mem_image_iff_of_inverse r_inv l_inv],
this ▸ h s hs

lemma to_quotient_map {f : α → β}
  (open_map : is_open_map f) (cont : continuous f) (surj : function.surjective f) :
  quotient_map f :=
⟨ surj,
  begin
    ext s,
    show is_open s ↔ is_open (f ⁻¹' s),
    split,
    { exact cont s },
    { assume h,
      rw ← @image_preimage_eq _ _ _ s surj,
      exact open_map _ h }
  end⟩

end is_open_map

section is_closed_map
variables [topological_space α] [topological_space β]

def is_closed_map (f : α → β) := ∀ U : set α, is_closed U → is_closed (f '' U)

end is_closed_map

namespace is_closed_map

variables [topological_space α] [topological_space β] [topological_space γ]
open function

protected lemma id : is_closed_map (@id α) := assume s hs, by rwa image_id

protected lemma comp {f : α → β} {g : β → γ} (hf : is_closed_map f) (hg : is_closed_map g) :
  is_closed_map (g ∘ f) :=
by { intros s hs, rw image_comp, exact hg _ (hf _ hs) }

lemma of_inverse {f : α → β} {f' : β → α}
  (h : continuous f') (l_inv : left_inverse f f') (r_inv : right_inverse f f') :
  is_closed_map f :=
assume s hs,
have f' ⁻¹' s = f '' s, by ext x; simp [mem_image_iff_of_inverse r_inv l_inv],
this ▸ continuous_iff_is_closed.mp h s hs

end is_closed_map

section open_embedding
variables [topological_space α] [topological_space β] [topological_space γ]

/-- An open embedding is an embedding with open image. -/
structure open_embedding (f : α → β) extends embedding f : Prop :=
(open_range : is_open $ range f)

lemma open_embedding.open_iff_image_open {f : α → β} (hf : open_embedding f)
  {s : set α} : is_open s ↔ is_open (f '' s) :=
⟨embedding_open hf.to_embedding hf.open_range,
 λ h, begin
   convert ←hf.to_embedding.continuous _ h,
   apply preimage_image_eq _ hf.inj
 end⟩

lemma open_embedding.is_open_map {f : α → β} (hf : open_embedding f) : is_open_map f :=
λ s, hf.open_iff_image_open.mp

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
⟨h₁, by convert h₂ univ is_open_univ; simp⟩

lemma open_embedding_of_continuous_injective_open {f : α → β} (h₁ : continuous f)
  (h₂ : function.injective f) (h₃ : is_open_map f) : open_embedding f :=
begin
  refine open_embedding_of_embedding_open ⟨⟨_⟩, h₂⟩ h₃,
  apply le_antisymm (continuous_iff_le_induced.mp h₁) _,
  intro s,
  change is_open _ ≤ is_open _,
  rw is_open_induced_iff,
  refine λ hs, ⟨f '' s, h₃ s hs, _⟩,
  rw preimage_image_eq _ h₂
end

lemma open_embedding_id : open_embedding (@id α) :=
⟨embedding_id, by convert is_open_univ; apply range_id⟩

lemma open_embedding.comp {f : α → β} {g : β → γ}
  (hg : open_embedding g) (hf : open_embedding f) : open_embedding (g ∘ f) :=
⟨hg.1.comp hf.1, show is_open (range (g ∘ f)),
 by rw [range_comp, ←hg.open_iff_image_open]; exact hf.2⟩

end open_embedding

section closed_embedding
variables [topological_space α] [topological_space β] [topological_space γ]

/-- A closed embedding is an embedding with closed image. -/
structure closed_embedding (f : α → β) extends embedding f : Prop :=
(closed_range : is_closed $ range f)

variables {f : α → β}

lemma closed_embedding.continuous (hf : closed_embedding f) : continuous f :=
hf.to_embedding.continuous

lemma closed_embedding.closed_iff_image_closed (hf : closed_embedding f)
  {s : set α} : is_closed s ↔ is_closed (f '' s) :=
⟨embedding_is_closed hf.to_embedding hf.closed_range,
 λ h, begin
   convert ←continuous_iff_is_closed.mp hf.continuous _ h,
   apply preimage_image_eq _ hf.inj
 end⟩

lemma closed_embedding.is_closed_map (hf : closed_embedding f) : is_closed_map f :=
λ s, hf.closed_iff_image_closed.mp

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
  (h₂ : function.injective f) (h₃ : is_closed_map f) : closed_embedding f :=
begin
  refine closed_embedding_of_embedding_closed ⟨⟨_⟩, h₂⟩ h₃,
  apply le_antisymm (continuous_iff_le_induced.mp h₁) _,
  intro s',
  change is_open _ ≤ is_open _,
  rw [←is_closed_compl_iff, ←is_closed_compl_iff],
  generalize : -s' = s,
  rw is_closed_induced_iff,
  refine λ hs, ⟨f '' s, h₃ s hs, _⟩,
  rw preimage_image_eq _ h₂
end

lemma closed_embedding_id : closed_embedding (@id α) :=
⟨embedding_id, by convert is_closed_univ; apply range_id⟩

lemma closed_embedding.comp {f : α → β} {g : β → γ}
  (hg : closed_embedding g) (hf : closed_embedding f) : closed_embedding (g ∘ f) :=
⟨hg.to_embedding.comp hf.to_embedding, show is_closed (range (g ∘ f)),
 by rw [range_comp, ←hg.closed_iff_image_closed]; exact hf.closed_range⟩

end closed_embedding
