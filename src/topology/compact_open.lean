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

variables (β)
def uniform_on.gen (s : set α) : set (set C(α, β)) :=
{m | ∃ (u : set β) (hu : is_open u), m = compact_open.gen s u}

def uniform_on (s : set α) : topological_space C(α, β) :=
topological_space.generate_from (uniform_on.gen β s)
variables {β}

private lemma is_open_gen' (s : set α) {u : set β} (hu : is_open u) :
  (uniform_on β s).is_open (compact_open.gen s u) :=
topological_space.generate_open.basic _ (by dsimp [mem_set_of_eq]; tauto)

lemma bzz :
  {m | ∃ (s : set α) (hs : is_compact s) (u : set β) (hu : is_open u), m = compact_open.gen s u}
  = ⋃ (s : set α) (hs : is_compact s), uniform_on.gen β s :=
begin
  ext m,
  simp [uniform_on.gen],
end

-- The compact-open topology on the space of continuous maps α → β.
instance compact_open : topological_space C(α, β) :=
topological_space.generate_from
  {m | ∃ (s : set α) (hs : is_compact s) (u : set β) (hu : is_open u), m = compact_open.gen s u}

lemma foo (s : set α) (hs : is_compact s) : (⨅ (hs : is_compact s), uniform_on β s) = uniform_on β s :=
by simp [hs]

lemma foo' (s : set α) (hs : ¬ (is_compact s)) :  (⨅ (hs : is_compact s), uniform_on β s) = ⊤ :=
by simp [hs]

lemma compact_open_eq : (continuous_map.compact_open : topological_space C(α, β))
  = ⨅ (s : set α) (hs : is_compact s), uniform_on β s :=
begin

  -- transitivity ⨅ (s : set α), topological_space.generate_from (set_of (⨅ (hs : is_compact s)))
  -- rw ← generate_from_Union,
  rw continuous_map.compact_open,
  rw bzz,
  simp only [uniform_on],
  -- rw ← generate_from_Inter_of_generate_from_eq_self,
  simp only [← generate_from_Union],
  -- simp only [foo₃],

  transitivity topological_space.generate_from
    (⋃ (s : set α),
      {s' | (topological_space.generate_from (⋃ (hs : is_compact s), uniform_on.gen β s)).is_open s'}),

  simp only [generate_from_set_of_is_open, foo₃],
  -- simp only [← generate_from_Union],
  -- congr' 2,
  -- -- congr' 1,
  -- ext s,
  -- rw mem_set_of_eq,


  -- rw Union_set_of,
  -- simp only [generate_from_set_of_is_open],
  -- let T := topological_space C(α, β),
  -- haveI : complete_lattice T := tmp_complete_lattice,
  -- let l : set (set C(α, β)) → T := topological_space.generate_from,
  -- let u : T → set (set C(α, β)) := λ t, {s | t.is_open s},
  -- have gc : galois_insertion l u,
  -- have : @galois_insertion _ _ _ _ _ _ := gi_generate_from C(α, β),
  -- let gc : galois_connection
  -- rw continuous_map.compact_open,
  -- change _ = topological_space.generate_from _, --(topological_space.generate_from _),
  rw bzz,
  simp [uniform_on],
  change _ = topological_space.generate_from
    (⋃ y : set α, set_of (topological_space.is_open (topological_space.generate_from _))),
  simp [set_of],
  transitivity topological_space.generate_from
    (topological_space.generate_from
    (⋃ (y : set α),
      (⋃ (b : topological_space C(α, β))
      (x : is_compact y ∧ topological_space.generate_from (uniform_on.gen β y) = b), b.is_open))).is_open,
  rw galois_insertion.l_u_eq (gi_generate_from _),


  change _ = topological_space.generate_from (topological_space.is_open _),
  let F : topological_space C(α, β) → set (set C(α, β)) := λ t, {s | t.is_open s},
  have gi : galois_insertion topological_space.generate_from F,
  convert gi_generate_from C(α, β),
  change _ = gi.l _,
  have : ∀ y : set α, topological_space.generate_from (⨅ h : is_compact y, {s | (f i).is_open s}) = ⨅ i, (f i) :=

  have := @galois_insertion.l_infi_u  (set (set C(α, β))) (topological_space C(α, β)) topological_space.generate_from _, -- (gi_generate_from C(α, β)),
  dsimp [set_of],
  congr' 1,
  ext s,
  simp,
  split,
  { rintros ⟨u, hu, v, hv, rfl⟩,
    use u,
    convert is_open_gen' u hv,
    exact infi_pos hu },
  { --intros h,
    rintros ⟨u, h⟩,
    by_cases hu : is_compact u,
    { rw foo u hu at h,
      -- intros h,
      refine ⟨u, hu, _⟩,

       },
    rw foo' u hu at h,
    use ∅,
    simp,
    have : s = ∅ ∨ s = set.univ := sorry,
    rcases this with rfl | rfl,
    use ∅,
    simp,
    sorry,
    use set.univ,
    simp,
    sorry,
    -- have : (uniform_on β u).is_open s,
    -- { convert h,
    --   simp [hu] },
    -- refine ⟨u, hu, _⟩,


  }
end

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
