/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton

Type of continuous maps and the compact-open topology on them.
-/
import topology.subset_properties
import topology.continuous_function.basic
import topology.homeomorph
import tactic.tidy

/-!
# The compact-open topology

In this file, we define the compact-open topology on the set of continuous maps between two
topological spaces.

## Main definitions

* `compact_open` is the compact-open topology on `C(α, β)`. It is declared as an instance.
* `ev` is the evaluation map `C(α, β) × α → β`. It is continuous as long as `α` is locally compact.
* `coev` is the coevaluation map `β → C(α, β × α)`. It is always continuous.
* `continuous_map.curry` is the currying map `C(α × β, γ) → C(α, C(β, γ))`. This map always exists
  and it is continuous as long as `α × β` is locally compact.
* `continuous_map.uncurry` is the uncurrying map `C(α, C(β, γ)) → C(α × β, γ)`. For this map to
  exist, we need `β` to be locally compact. If `α` is also locally compact, then this map is
  continuous.
* `homeomorph.curry` combines the currying and uncurrying operations into a homeomorphism
  `C(α × β, γ) ≃ₜ C(α, C(β, γ))`. This homeomorphism exists if `α` and `β` are locally compact.


## Tags

compact-open, curry, function space
-/

open set
open_locale topological_space

namespace continuous_map

section compact_open
variables {α : Type*} {β : Type*} {γ : Type*}
variables [topological_space α] [topological_space β] [topological_space γ]

def compact_open.gen (s : set α) (u : set β) : set C(α,β) := {f | f '' s ⊆ u}

-- The compact-open topology on the space of continuous maps α → β.
instance compact_open : topological_space C(α, β) :=
topological_space.generate_from
  {m | ∃ (s : set α) (hs : is_compact s) (u : set β) (hu : is_open u), m = compact_open.gen s u}

private lemma is_open_gen {s : set α} (hs : is_compact s) {u : set β} (hu : is_open u) :
  is_open (compact_open.gen s u) :=
topological_space.generate_open.basic _ (by dsimp [mem_set_of_eq]; tauto)

section functorial

variables {g : β → γ} (hg : continuous g)

def induced (f : C(α, β)) : C(α, γ) := ⟨g ∘ f, hg.comp f.continuous⟩

private lemma preimage_gen {s : set α} (hs : is_compact s) {u : set γ} (hu : is_open u) :
  continuous_map.induced hg ⁻¹' (compact_open.gen s u) = compact_open.gen s (g ⁻¹' u) :=
begin
  ext ⟨f, _⟩,
  change g ∘ f '' s ⊆ u ↔ f '' s ⊆ g ⁻¹' u,
  rw [image_comp, image_subset_iff]
end

/-- C(α, -) is a functor. -/
lemma continuous_induced : continuous (continuous_map.induced hg : C(α, β) → C(α, γ)) :=
continuous_generated_from $ assume m ⟨s, hs, u, hu, hm⟩,
  by rw [hm, preimage_gen hg hs hu]; exact is_open_gen hs (hu.preimage hg)

end functorial

section ev

variables (α β)
def ev (p : C(α, β) × α) : β := p.1 p.2

variables {α β}
-- The evaluation map C(α, β) × α → β is continuous if α is locally compact.
lemma continuous_ev [locally_compact_space α] : continuous (ev α β) :=
continuous_iff_continuous_at.mpr $ assume ⟨f, x⟩ n hn,
  let ⟨v, vn, vo, fxv⟩ := mem_nhds_iff.mp hn in
  have v ∈ 𝓝 (f x), from is_open.mem_nhds vo fxv,
  let ⟨s, hs, sv, sc⟩ :=
    locally_compact_space.local_compact_nhds x (f ⁻¹' v)
      (f.continuous.tendsto x this) in
  let ⟨u, us, uo, xu⟩ := mem_nhds_iff.mp hs in
  show (ev α β) ⁻¹' n ∈ 𝓝 (f, x), from
  let w := set.prod (compact_open.gen s v) u in
  have w ⊆ ev α β ⁻¹' n, from assume ⟨f', x'⟩ ⟨hf', hx'⟩, calc
    f' x' ∈ f' '' s  : mem_image_of_mem f' (us hx')
    ...       ⊆ v            : hf'
    ...       ⊆ n            : vn,
  have is_open w, from (is_open_gen sc vo).prod uo,
  have (f, x) ∈ w, from ⟨image_subset_iff.mpr sv, xu⟩,
  mem_nhds_iff.mpr ⟨w, by assumption, by assumption, by assumption⟩

end ev

section Inf_induced

/-- The compact-open topology on `C(α, β)` is equal to the infimum of the compact-open topologies
on `C(s, β)` for `s` a compact subset of `α`.  The key point of the proof is that the union of the
compact subsets of `α` is equal to the union of compact subsets of the compact subsets of `α`. -/
lemma compact_open_eq_Inf_induced :
  (continuous_map.compact_open : topological_space C(α, β))
  = ⨅ (s : set α) (hs : is_compact s),
    topological_space.induced (continuous_map.restrict s) continuous_map.compact_open :=
begin
  simp only [← generate_from_Union, induced_generate_from_eq, continuous_map.compact_open],
  congr' 1,
  ext m,
  rw mem_bUnion_iff',
  split,
  { rintros ⟨s, hs, u, hu, rfl⟩,
    refine ⟨s, hs, compact_open.gen univ u, _⟩,
    refine ⟨⟨univ, is_compact_iff_is_compact_univ.mp hs, u, hu, rfl⟩, _⟩,
    ext f,
    simp only [compact_open.gen, mem_set_of_eq, mem_preimage, continuous_map.coe_restrict],
    rw image_comp f (coe : s → α),
    simp },
  { rintros ⟨s, hs, sb, ⟨s', hs', u, hu, rfl⟩, rfl⟩,
    refine ⟨coe '' s', hs'.image continuous_subtype_coe, u, hu, _⟩,
    ext f,
    simp only [compact_open.gen, coe_restrict, mem_set_of_eq, preimage_set_of_eq,
      image_subset_iff],
    rw preimage_comp },
end

lemma nhds_compact_open_eq_Inf_nhds_induced (f : C(α, β)) :
  𝓝 f = ⨅ s (hs : is_compact s), (𝓝 (f.restrict s)).comap (continuous_map.restrict s) :=
by { rw [compact_open_eq_Inf_induced], simp [nhds_infi, nhds_induced] }

lemma tendsto_compact_open_iff_forall {ι : Type*} {l : filter ι} (F : ι → C(α, β)) (f : C(α, β)) :
  filter.tendsto F l (nhds f)
  ↔ ∀ s (hs : is_compact s), filter.tendsto (λ i, (F i).restrict s) l (𝓝 (f.restrict s)) :=
by { rw [compact_open_eq_Inf_induced], simp [nhds_infi, nhds_induced, filter.tendsto_comap_iff] }

end Inf_induced

section coev

variables (α β)
def coev (b : β) : C(α, β × α) := ⟨λ a, (b, a), continuous.prod_mk continuous_const continuous_id⟩

variables {α β}
lemma image_coev {y : β} (s : set α) : (coev α β y) '' s = set.prod {y} s := by tidy

-- The coevaluation map β → C(α, β × α) is continuous (always).
lemma continuous_coev : continuous (coev α β) :=
continuous_generated_from $ begin
  rintros _ ⟨s, sc, u, uo, rfl⟩,
  rw is_open_iff_forall_mem_open,
  intros y hy,
  change (coev α β y) '' s ⊆ u at hy,
  rw image_coev s at hy,
  rcases generalized_tube_lemma is_compact_singleton sc uo hy
    with ⟨v, w, vo, wo, yv, sw, vwu⟩,
  refine ⟨v, _, vo, singleton_subset_iff.mp yv⟩,
  intros y' hy',
  change (coev α β y') '' s ⊆ u,
  rw image_coev s,
  exact subset.trans (prod_mono (singleton_subset_iff.mpr hy') sw) vwu
end

end coev

section curry

/-- Auxiliary definition, see `continuous_map.curry` and `homeomorph.curry`. -/
def curry' (f : C(α × β, γ)) (a : α) : C(β, γ) := ⟨function.curry f a⟩

/-- If a map `α × β → γ` is continuous, then its curried form `α → C(β, γ)` is continuous. -/
lemma continuous_curry' (f : C(α × β, γ)) : continuous (curry' f) :=
have hf : curry' f = continuous_map.induced f.continuous_to_fun ∘ coev _ _, by { ext, refl },
hf ▸ continuous.comp (continuous_induced f.continuous_to_fun) continuous_coev

/-- To show continuity of a map `α → C(β, γ)`, it suffices to show that its uncurried form
    `α × β → γ` is continuous. -/
lemma continuous_of_continuous_uncurry (f : α → C(β, γ))
  (h : continuous (function.uncurry (λ x y, f x y))) : continuous f :=
by { convert continuous_curry' ⟨_, h⟩, ext, refl }

/-- The curried form of a continuous map `α × β → γ` as a continuous map `α → C(β, γ)`.
    If `a × β` is locally compact, this is continuous. If `α` and `β` are both locally
    compact, then this is a homeomorphism, see `homeomorph.curry`. -/
def curry (f : C(α × β, γ)) : C(α, C(β, γ)) :=
⟨_, continuous_curry' f⟩

/-- The currying process is a continuous map between function spaces. -/
lemma continuous_curry [locally_compact_space (α × β)] :
  continuous (curry : C(α × β, γ) → C(α, C(β, γ))) :=
begin
  apply continuous_of_continuous_uncurry,
  apply continuous_of_continuous_uncurry,
  rw ←homeomorph.comp_continuous_iff' (homeomorph.prod_assoc _ _ _).symm,
  convert continuous_ev;
  tidy
end

@[simp]
lemma curry_apply (f : C(α × β, γ)) (a : α) (b : β) : f.curry a b = f (a, b) := rfl

/-- The uncurried form of a continuous map `α → C(β, γ)` is a continuous map `α × β → γ`. -/
lemma continuous_uncurry_of_continuous [locally_compact_space β] (f : C(α, C(β, γ))) :
  continuous (function.uncurry (λ x y, f x y)) :=
have hf : function.uncurry (λ x y, f x y) = ev β γ ∘ prod.map f id, by { ext, refl },
hf ▸ continuous.comp continuous_ev $ continuous.prod_map f.2 id.2

/-- The uncurried form of a continuous map `α → C(β, γ)` as a continuous map `α × β → γ` (if `β` is
    locally compact). If `α` is also locally compact, then this is a homeomorphism between the two
    function spaces, see `homeomorph.curry`. -/
def uncurry [locally_compact_space β] (f : C(α, C(β, γ))) : C(α × β, γ) :=
⟨_, continuous_uncurry_of_continuous f⟩

/-- The uncurrying process is a continuous map between function spaces. -/
lemma continuous_uncurry [locally_compact_space α] [locally_compact_space β] :
  continuous (uncurry : C(α, C(β, γ)) → C(α × β, γ)) :=
begin
  apply continuous_of_continuous_uncurry,
  rw ←homeomorph.comp_continuous_iff' (homeomorph.prod_assoc _ _ _),
  apply continuous.comp continuous_ev (continuous.prod_map continuous_ev id.2);
  apply_instance
end

/-- The family of constant maps: `β → C(α, β)` as a continuous map. -/
def const' : C(β, C(α, β)) := curry ⟨prod.fst, continuous_fst⟩

@[simp] lemma coe_const' : (const' : β → C(α, β)) = const := rfl

lemma continuous_const' : continuous (const : β → C(α, β)) := const'.continuous

end curry

end compact_open

end continuous_map

open continuous_map

namespace homeomorph
variables {α : Type*} {β : Type*} {γ : Type*}
variables [topological_space α] [topological_space β] [topological_space γ]

/-- Currying as a homeomorphism between the function spaces `C(α × β, γ)` and `C(α, C(β, γ))`. -/
def curry [locally_compact_space α] [locally_compact_space β] : C(α × β, γ) ≃ₜ C(α, C(β, γ)) :=
⟨⟨curry, uncurry, by tidy, by tidy⟩, continuous_curry, continuous_uncurry⟩

/-- If `α` has a single element, then `β` is homeomorphic to `C(α, β)`. -/
def continuous_map_of_unique [unique α] : β ≃ₜ C(α, β) :=
{ to_fun := continuous_map.induced continuous_fst ∘ coev α β,
  inv_fun := ev α β ∘ (λ f, (f, default α)),
  left_inv := λ a, rfl,
  right_inv := λ f, by { ext, rw unique.eq_default x, refl },
  continuous_to_fun := continuous.comp (continuous_induced _) continuous_coev,
  continuous_inv_fun :=
    continuous.comp continuous_ev (continuous.prod_mk continuous_id continuous_const) }

@[simp] lemma continuous_map_of_unique_apply [unique α] (b : β) (a : α) :
  continuous_map_of_unique b a = b :=
rfl

@[simp] lemma continuous_map_of_unique_symm_apply [unique α] (f : C(α, β)) :
  continuous_map_of_unique.symm f = f (default α) :=
rfl

end homeomorph
