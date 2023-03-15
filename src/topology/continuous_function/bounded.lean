/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth
-/
import analysis.normed.order.lattice
import analysis.normed_space.operator_norm
import analysis.normed_space.star.basic
import data.real.sqrt
import topology.continuous_function.algebra
import topology.metric_space.equicontinuity

/-!
# Bounded continuous functions

The type of bounded continuous functions taking values in a metric space, with
the uniform distance.

-/

noncomputable theory
open_locale topology classical nnreal uniformity uniform_convergence

open set filter metric function

universes u v w
variables {F : Type*} {α : Type u} {β : Type v} {γ : Type w}

/-- `α →ᵇ β` is the type of bounded continuous functions `α → β` from a topological space to a
metric space.

When possible, instead of parametrizing results over `(f : α →ᵇ β)`,
you should parametrize over `(F : Type*) [bounded_continuous_map_class F α β] (f : F)`.

When you extend this structure, make sure to extend `bounded_continuous_map_class`. -/
structure bounded_continuous_function (α : Type u) (β : Type v)
  [topological_space α] [pseudo_metric_space β] extends continuous_map α β :
  Type (max u v) :=
(map_bounded' : ∃ C, ∀ x y, dist (to_fun x) (to_fun y) ≤ C)

localized "infixr (name := bounded_continuous_function)
  ` →ᵇ `:25 := bounded_continuous_function" in bounded_continuous_function

section
set_option old_structure_cmd true

/-- `bounded_continuous_map_class F α β` states that `F` is a type of bounded continuous maps.

You should also extend this typeclass when you extend `bounded_continuous_function`. -/
class bounded_continuous_map_class (F α β : Type*) [topological_space α] [pseudo_metric_space β]
  extends continuous_map_class F α β :=
(map_bounded (f : F) : ∃ C, ∀ x y, dist (f x) (f y) ≤ C)

end

export bounded_continuous_map_class (map_bounded)

namespace bounded_continuous_function
section basics
variables [topological_space α] [pseudo_metric_space β] [pseudo_metric_space γ]
variables {f g : α →ᵇ β} {x : α} {C : ℝ}

instance : bounded_continuous_map_class (α →ᵇ β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_continuous := λ f, f.continuous_to_fun,
  map_bounded := λ f, f.map_bounded' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (α →ᵇ β) (λ _, α → β) := fun_like.has_coe_to_fun

instance [bounded_continuous_map_class F α β] : has_coe_t F (α →ᵇ β) :=
⟨λ f, { to_fun := f, continuous_to_fun := map_continuous f, map_bounded' := map_bounded f }⟩

@[simp] lemma coe_to_continuous_fun (f : α →ᵇ β) : (f.to_continuous_map : α → β) = f := rfl

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : α →ᵇ β) : α → β := h

initialize_simps_projections bounded_continuous_function (to_continuous_map_to_fun → apply)

protected lemma bounded (f : α →ᵇ β) : ∃C, ∀ x y : α, dist (f x) (f y) ≤ C := f.map_bounded'
protected lemma continuous (f : α →ᵇ β) : continuous f := f.to_continuous_map.continuous

@[ext] lemma ext (h : ∀ x, f x = g x) : f = g := fun_like.ext _ _ h

lemma bounded_range (f : α →ᵇ β) : bounded (range f) :=
bounded_range_iff.2 f.bounded

lemma bounded_image (f : α →ᵇ β) (s : set α) : bounded (f '' s) :=
f.bounded_range.mono $ image_subset_range _ _

lemma eq_of_empty [is_empty α] (f g : α →ᵇ β) : f = g :=
ext $ is_empty.elim ‹_›

/-- A continuous function with an explicit bound is a bounded continuous function. -/
def mk_of_bound (f : C(α, β)) (C : ℝ) (h : ∀ x y : α, dist (f x) (f y) ≤ C) : α →ᵇ β :=
⟨f, ⟨C, h⟩⟩

@[simp] lemma mk_of_bound_coe {f} {C} {h} : (mk_of_bound f C h : α → β) = (f : α → β) :=
rfl

/-- A continuous function on a compact space is automatically a bounded continuous function. -/
def mk_of_compact [compact_space α] (f : C(α, β)) : α →ᵇ β :=
⟨f, bounded_range_iff.1 (is_compact_range f.continuous).bounded⟩

@[simp] lemma mk_of_compact_apply [compact_space α] (f : C(α, β)) (a : α) :
  mk_of_compact f a = f a :=
rfl

/-- If a function is bounded on a discrete space, it is automatically continuous,
and therefore gives rise to an element of the type of bounded continuous functions -/
@[simps] def mk_of_discrete [discrete_topology α] (f : α → β)
  (C : ℝ) (h : ∀ x y : α, dist (f x) (f y) ≤ C) : α →ᵇ β :=
⟨⟨f, continuous_of_discrete_topology⟩, ⟨C, h⟩⟩

/-- The uniform distance between two bounded continuous functions -/
instance : has_dist (α →ᵇ β) :=
⟨λf g, Inf {C | 0 ≤ C ∧ ∀ x : α, dist (f x) (g x) ≤ C}⟩

lemma dist_eq : dist f g = Inf {C | 0 ≤ C ∧ ∀ x : α, dist (f x) (g x) ≤ C} := rfl

lemma dist_set_exists : ∃ C, 0 ≤ C ∧ ∀ x : α, dist (f x) (g x) ≤ C :=
begin
  rcases f.bounded_range.union g.bounded_range with ⟨C, hC⟩,
  refine ⟨max 0 C, le_max_left _ _, λ x, (hC _ _ _ _).trans (le_max_right _ _)⟩;
    [left, right]; apply mem_range_self
end

/-- The pointwise distance is controlled by the distance between functions, by definition. -/
lemma dist_coe_le_dist (x : α) : dist (f x) (g x) ≤ dist f g :=
le_cInf dist_set_exists $ λb hb, hb.2 x

/- This lemma will be needed in the proof of the metric space instance, but it will become
useless afterwards as it will be superseded by the general result that the distance is nonnegative
in metric spaces. -/
private lemma dist_nonneg' : 0 ≤ dist f g :=
le_cInf dist_set_exists (λ C, and.left)

/-- The distance between two functions is controlled by the supremum of the pointwise distances -/
lemma dist_le (C0 : (0 : ℝ) ≤ C) : dist f g ≤ C ↔ ∀x:α, dist (f x) (g x) ≤ C :=
⟨λ h x, le_trans (dist_coe_le_dist x) h, λ H, cInf_le ⟨0, λ C, and.left⟩ ⟨C0, H⟩⟩

lemma dist_le_iff_of_nonempty [nonempty α] :
  dist f g ≤ C ↔ ∀ x, dist (f x) (g x) ≤ C :=
⟨λ h x, le_trans (dist_coe_le_dist x) h,
 λ w, (dist_le (le_trans dist_nonneg (w (nonempty.some ‹_›)))).mpr w⟩

lemma dist_lt_of_nonempty_compact [nonempty α] [compact_space α]
  (w : ∀x:α, dist (f x) (g x) < C) : dist f g < C :=
begin
  have c : continuous (λ x, dist (f x) (g x)), { continuity, },
  obtain ⟨x, -, le⟩ :=
    is_compact.exists_forall_ge is_compact_univ set.univ_nonempty (continuous.continuous_on c),
  exact lt_of_le_of_lt (dist_le_iff_of_nonempty.mpr (λ y, le y trivial)) (w x),
end

lemma dist_lt_iff_of_compact [compact_space α] (C0 : (0 : ℝ) < C) :
  dist f g < C ↔ ∀x:α, dist (f x) (g x) < C :=
begin
  fsplit,
  { intros w x,
    exact lt_of_le_of_lt (dist_coe_le_dist x) w, },
  { by_cases h : nonempty α,
    { resetI,
      exact dist_lt_of_nonempty_compact, },
    { rintro -,
      convert C0,
      apply le_antisymm _ dist_nonneg',
      rw [dist_eq],
      exact cInf_le ⟨0, λ C, and.left⟩ ⟨le_rfl, λ x, false.elim (h (nonempty.intro x))⟩, }, },
end

lemma dist_lt_iff_of_nonempty_compact [nonempty α] [compact_space α] :
  dist f g < C ↔ ∀x:α, dist (f x) (g x) < C :=
⟨λ w x, lt_of_le_of_lt (dist_coe_le_dist x) w, dist_lt_of_nonempty_compact⟩

/-- The type of bounded continuous functions, with the uniform distance, is a pseudometric space. -/
instance : pseudo_metric_space (α →ᵇ β) :=
{ dist_self := λ f, le_antisymm ((dist_le le_rfl).2 $ λ x, by simp) dist_nonneg',
  dist_comm := λ f g, by simp [dist_eq, dist_comm],
  dist_triangle := λ f g h,
    (dist_le (add_nonneg dist_nonneg' dist_nonneg')).2 $ λ x,
      le_trans (dist_triangle _ _ _) (add_le_add (dist_coe_le_dist _) (dist_coe_le_dist _)) }

/-- The type of bounded continuous functions, with the uniform distance, is a metric space. -/
instance {α β} [topological_space α] [metric_space β] : metric_space (α →ᵇ β) :=
{ eq_of_dist_eq_zero := λ f g hfg, by ext x; exact
    eq_of_dist_eq_zero (le_antisymm (hfg ▸ dist_coe_le_dist _) dist_nonneg) }

lemma nndist_eq : nndist f g = Inf {C | ∀ x : α, nndist (f x) (g x) ≤ C} :=
subtype.ext $ dist_eq.trans $ begin
  rw [nnreal.coe_Inf, nnreal.coe_image],
  simp_rw [mem_set_of_eq, ←nnreal.coe_le_coe, subtype.coe_mk, exists_prop, coe_nndist],
end

lemma nndist_set_exists : ∃ C, ∀ x : α, nndist (f x) (g x) ≤ C :=
subtype.exists.mpr $ dist_set_exists.imp $ λ a ⟨ha, h⟩, ⟨ha, h⟩

lemma nndist_coe_le_nndist (x : α) : nndist (f x) (g x) ≤ nndist f g :=
dist_coe_le_dist x

/-- On an empty space, bounded continuous functions are at distance 0 -/
lemma dist_zero_of_empty [is_empty α] : dist f g = 0 :=
by rw [(ext is_empty_elim : f = g), dist_self]

lemma dist_eq_supr : dist f g = ⨆ x : α, dist (f x) (g x) :=
begin
  casesI is_empty_or_nonempty α, { rw [supr_of_empty', real.Sup_empty, dist_zero_of_empty] },
  refine (dist_le_iff_of_nonempty.mpr $ le_csupr _).antisymm (csupr_le dist_coe_le_dist),
  exact dist_set_exists.imp (λ C hC, forall_range_iff.2 hC.2)
end

lemma nndist_eq_supr : nndist f g = ⨆ x : α, nndist (f x) (g x) :=
subtype.ext $ dist_eq_supr.trans $ by simp_rw [nnreal.coe_supr, coe_nndist]

lemma tendsto_iff_tendsto_uniformly {ι : Type*} {F : ι → (α →ᵇ β)} {f : α →ᵇ β} {l : filter ι} :
  tendsto F l (𝓝 f) ↔ tendsto_uniformly (λ i, F i) f l :=
iff.intro
  (λ h, tendsto_uniformly_iff.2
    (λ ε ε0, (metric.tendsto_nhds.mp h ε ε0).mp (eventually_of_forall $
    λ n hn x, lt_of_le_of_lt (dist_coe_le_dist x) (dist_comm (F n) f ▸ hn))))
  (λ h, metric.tendsto_nhds.mpr $ λ ε ε_pos,
    (h _ (dist_mem_uniformity $ half_pos ε_pos)).mp (eventually_of_forall $
    λ n hn, lt_of_le_of_lt ((dist_le (half_pos ε_pos).le).mpr $
    λ x, dist_comm (f x) (F n x) ▸ le_of_lt (hn x)) (half_lt_self ε_pos)))

/-- The topology on `α →ᵇ β` is exactly the topology induced by the natural map to `α →ᵤ β`. -/
lemma inducing_coe_fn : inducing (uniform_fun.of_fun ∘ coe_fn : (α →ᵇ β) → (α →ᵤ β)) :=
begin
  rw inducing_iff_nhds,
  refine λ f, eq_of_forall_le_iff (λ l, _),
  rw [← tendsto_iff_comap, ← tendsto_id', tendsto_iff_tendsto_uniformly,
      uniform_fun.tendsto_iff_tendsto_uniformly],
  refl
end

-- TODO: upgrade to a `uniform_embedding`
lemma embedding_coe_fn : embedding (uniform_fun.of_fun ∘ coe_fn : (α →ᵇ β) → (α →ᵤ β)) :=
⟨inducing_coe_fn, λ f g h, ext $ λ x, congr_fun h x⟩

variables (α) {β}

/-- Constant as a continuous bounded function. -/
@[simps {fully_applied := ff}] def const (b : β) : α →ᵇ β :=
⟨continuous_map.const α b, 0, by simp [le_rfl]⟩

variable {α}

lemma const_apply' (a : α) (b : β) : (const α b : α → β) a = b := rfl

/-- If the target space is inhabited, so is the space of bounded continuous functions -/
instance [inhabited β] : inhabited (α →ᵇ β) := ⟨const α default⟩

lemma lipschitz_evalx (x : α) : lipschitz_with 1 (λ f : α →ᵇ β, f x) :=
lipschitz_with.mk_one $ λ f g, dist_coe_le_dist x

theorem uniform_continuous_coe : @uniform_continuous (α →ᵇ β) (α → β) _ _ coe_fn :=
uniform_continuous_pi.2 $ λ x, (lipschitz_evalx x).uniform_continuous

lemma continuous_coe : continuous (λ (f : α →ᵇ β) x, f x) :=
uniform_continuous.continuous uniform_continuous_coe

/-- When `x` is fixed, `(f : α →ᵇ β) ↦ f x` is continuous -/
@[continuity] theorem continuous_eval_const {x : α} : continuous (λ f : α →ᵇ β, f x) :=
(continuous_apply x).comp continuous_coe

/-- The evaluation map is continuous, as a joint function of `u` and `x` -/
@[continuity] theorem continuous_eval : continuous (λ p : (α →ᵇ β) × α, p.1 p.2) :=
continuous_prod_of_continuous_lipschitz _ 1 (λ f, f.continuous) $ lipschitz_evalx

/-- Bounded continuous functions taking values in a complete space form a complete space. -/
instance [complete_space β] : complete_space (α →ᵇ β) :=
complete_of_cauchy_seq_tendsto $ λ (f : ℕ → α →ᵇ β) (hf : cauchy_seq f),
begin
  /- We have to show that `f n` converges to a bounded continuous function.
  For this, we prove pointwise convergence to define the limit, then check
  it is a continuous bounded function, and then check the norm convergence. -/
  rcases cauchy_seq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩,
  have f_bdd := λx n m N hn hm, le_trans (dist_coe_le_dist x) (b_bound n m N hn hm),
  have fx_cau : ∀x, cauchy_seq (λn, f n x) :=
    λx, cauchy_seq_iff_le_tendsto_0.2 ⟨b, b0, f_bdd x, b_lim⟩,
  choose F hF using λx, cauchy_seq_tendsto_of_complete (fx_cau x),
  /- F : α → β,  hF : ∀ (x : α), tendsto (λ (n : ℕ), f n x) at_top (𝓝 (F x))
  `F` is the desired limit function. Check that it is uniformly approximated by `f N` -/
  have fF_bdd : ∀x N, dist (f N x) (F x) ≤ b N :=
    λ x N, le_of_tendsto (tendsto_const_nhds.dist (hF x))
      (filter.eventually_at_top.2 ⟨N, λn hn, f_bdd x N n N (le_refl N) hn⟩),
  refine ⟨⟨⟨F, _⟩, _⟩, _⟩,
  { /- Check that `F` is continuous, as a uniform limit of continuous functions -/
    have : tendsto_uniformly (λn x, f n x) F at_top,
    { refine metric.tendsto_uniformly_iff.2 (λ ε ε0, _),
      refine ((tendsto_order.1 b_lim).2 ε ε0).mono (λ n hn x, _),
      rw dist_comm,
      exact lt_of_le_of_lt (fF_bdd x n) hn },
    exact this.continuous (eventually_of_forall $ λ N, (f N).continuous) },
  { /- Check that `F` is bounded -/
    rcases (f 0).bounded with ⟨C, hC⟩,
    refine ⟨C + (b 0 + b 0), λ x y, _⟩,
    calc dist (F x) (F y) ≤ dist (f 0 x) (f 0 y) + (dist (f 0 x) (F x) + dist (f 0 y) (F y)) :
      dist_triangle4_left _ _ _ _
                      ... ≤ C + (b 0 + b 0) : by mono* },
  { /- Check that `F` is close to `f N` in distance terms -/
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (λ _, dist_nonneg) _ b_lim),
    exact λ N, (dist_le (b0 _)).2 (λx, fF_bdd x N) }
end

/-- Composition of a bounded continuous function and a continuous function. -/
def comp_continuous {δ : Type*} [topological_space δ] (f : α →ᵇ β) (g : C(δ, α)) : δ →ᵇ β :=
{ to_continuous_map := f.1.comp g,
  map_bounded' := f.map_bounded'.imp (λ C hC x y, hC _ _) }

@[simp] lemma coe_comp_continuous {δ : Type*} [topological_space δ] (f : α →ᵇ β) (g : C(δ, α)) :
  coe_fn (f.comp_continuous g) = f ∘ g := rfl

@[simp] lemma comp_continuous_apply {δ : Type*} [topological_space δ]
  (f : α →ᵇ β) (g : C(δ, α)) (x : δ) : f.comp_continuous g x = f (g x) :=
rfl

lemma lipschitz_comp_continuous {δ : Type*} [topological_space δ] (g : C(δ, α)) :
  lipschitz_with 1 (λ f : α →ᵇ β, f.comp_continuous g) :=
lipschitz_with.mk_one $ λ f₁ f₂, (dist_le dist_nonneg).2 $ λ x, dist_coe_le_dist (g x)

lemma continuous_comp_continuous {δ : Type*} [topological_space δ] (g : C(δ, α)) :
  continuous (λ f : α →ᵇ β, f.comp_continuous g) :=
(lipschitz_comp_continuous g).continuous

/-- Restrict a bounded continuous function to a set. -/
def restrict (f : α →ᵇ β) (s : set α) : s →ᵇ β :=
f.comp_continuous $ (continuous_map.id _).restrict s

@[simp] lemma coe_restrict (f : α →ᵇ β) (s : set α) : coe_fn (f.restrict s) = f ∘ coe := rfl

@[simp] lemma restrict_apply (f : α →ᵇ β) (s : set α) (x : s) : f.restrict s x = f x := rfl

/-- Composition (in the target) of a bounded continuous function with a Lipschitz map again
gives a bounded continuous function -/
def comp (G : β → γ) {C : ℝ≥0} (H : lipschitz_with C G)
  (f : α →ᵇ β) : α →ᵇ γ :=
⟨⟨λx, G (f x), H.continuous.comp f.continuous⟩,
  let ⟨D, hD⟩ := f.bounded in
  ⟨max C 0 * D, λ x y, calc
    dist (G (f x)) (G (f y)) ≤ C * dist (f x) (f y) : H.dist_le_mul _ _
    ... ≤ max C 0 * dist (f x) (f y) : mul_le_mul_of_nonneg_right (le_max_left C 0) dist_nonneg
    ... ≤ max C 0 * D : mul_le_mul_of_nonneg_left (hD _ _) (le_max_right C 0)⟩⟩

/-- The composition operator (in the target) with a Lipschitz map is Lipschitz -/
lemma lipschitz_comp {G : β → γ} {C : ℝ≥0} (H : lipschitz_with C G) :
  lipschitz_with C (comp G H : (α →ᵇ β) → α →ᵇ γ) :=
lipschitz_with.of_dist_le_mul $ λ f g,
(dist_le (mul_nonneg C.2 dist_nonneg)).2 $ λ x,
calc dist (G (f x)) (G (g x)) ≤ C * dist (f x) (g x) : H.dist_le_mul _ _
  ... ≤ C * dist f g : mul_le_mul_of_nonneg_left (dist_coe_le_dist _) C.2

/-- The composition operator (in the target) with a Lipschitz map is uniformly continuous -/
lemma uniform_continuous_comp {G : β → γ} {C : ℝ≥0} (H : lipschitz_with C G) :
  uniform_continuous (comp G H : (α →ᵇ β) → α →ᵇ γ) :=
(lipschitz_comp H).uniform_continuous

/-- The composition operator (in the target) with a Lipschitz map is continuous -/
lemma continuous_comp {G : β → γ} {C : ℝ≥0} (H : lipschitz_with C G) :
  continuous (comp G H : (α →ᵇ β) → α →ᵇ γ) :=
(lipschitz_comp H).continuous

/-- Restriction (in the target) of a bounded continuous function taking values in a subset -/
def cod_restrict (s : set β) (f : α →ᵇ β) (H : ∀x, f x ∈ s) : α →ᵇ s :=
⟨⟨s.cod_restrict f H, f.continuous.subtype_mk _⟩, f.bounded⟩

section extend

variables {δ : Type*} [topological_space δ] [discrete_topology δ]

/-- A version of `function.extend` for bounded continuous maps. We assume that the domain has
discrete topology, so we only need to verify boundedness. -/
def extend (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) : δ →ᵇ β :=
{ to_fun := extend f g h,
  continuous_to_fun := continuous_of_discrete_topology,
  map_bounded' :=
    begin
      rw [← bounded_range_iff, range_extend f.injective, metric.bounded_union],
      exact ⟨g.bounded_range, h.bounded_image _⟩
    end }

@[simp] lemma extend_apply (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) (x : α) :
  extend f g h (f x) = g x :=
f.injective.extend_apply _ _ _

@[simp] lemma extend_comp (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) : extend f g h ∘ f = g :=
extend_comp f.injective _ _

lemma extend_apply' {f : α ↪ δ} {x : δ} (hx : x ∉ range f) (g : α →ᵇ β) (h : δ →ᵇ β) :
  extend f g h x = h x :=
extend_apply' _ _ _ hx

lemma extend_of_empty [is_empty α] (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) :
  extend f g h = h :=
fun_like.coe_injective $ function.extend_of_empty f g h

@[simp] lemma dist_extend_extend (f : α ↪ δ) (g₁ g₂ : α →ᵇ β) (h₁ h₂ : δ →ᵇ β) :
  dist (g₁.extend f h₁) (g₂.extend f h₂) =
    max (dist g₁ g₂) (dist (h₁.restrict (range f)ᶜ) (h₂.restrict (range f)ᶜ)) :=
begin
  refine le_antisymm ((dist_le $ le_max_iff.2 $ or.inl dist_nonneg).2 $ λ x, _) (max_le _ _),
  { rcases em (∃ y, f y = x) with (⟨x, rfl⟩|hx),
    { simp only [extend_apply],
      exact (dist_coe_le_dist x).trans (le_max_left _ _) },
    { simp only [extend_apply' hx],
      lift x to ((range f)ᶜ : set δ) using hx,
      calc dist (h₁ x) (h₂ x) = dist (h₁.restrict (range f)ᶜ x) (h₂.restrict (range f)ᶜ x) : rfl
      ... ≤ dist (h₁.restrict (range f)ᶜ) (h₂.restrict (range f)ᶜ) : dist_coe_le_dist x
      ... ≤ _ : le_max_right _ _ } },
  { refine (dist_le dist_nonneg).2 (λ x, _),
    rw [← extend_apply f g₁ h₁, ← extend_apply f g₂ h₂],
    exact dist_coe_le_dist _ },
  { refine (dist_le dist_nonneg).2 (λ x, _),
    calc dist (h₁ x) (h₂ x) = dist (extend f g₁ h₁ x) (extend f g₂ h₂ x) :
      by rw [extend_apply' x.coe_prop, extend_apply' x.coe_prop]
    ... ≤ _ : dist_coe_le_dist _ }
end

lemma isometry_extend (f : α ↪ δ) (h : δ →ᵇ β) :
  isometry (λ g : α →ᵇ β, extend f g h) :=
isometry.of_dist_eq $ λ g₁ g₂, by simp [dist_nonneg]

end extend

end basics

section arzela_ascoli
variables [topological_space α] [compact_space α] [pseudo_metric_space β]
variables {f g : α →ᵇ β} {x : α} {C : ℝ}

/- Arzela-Ascoli theorem asserts that, on a compact space, a set of functions sharing
a common modulus of continuity and taking values in a compact set forms a compact
subset for the topology of uniform convergence. In this section, we prove this theorem
and several useful variations around it. -/

/-- First version, with pointwise equicontinuity and range in a compact space -/
theorem arzela_ascoli₁ [compact_space β]
  (A : set (α →ᵇ β))
  (closed : is_closed A)
  (H : equicontinuous (coe_fn : A → α → β)) :
  is_compact A :=
begin
  simp_rw [equicontinuous, metric.equicontinuous_at_iff_pair] at H,
  refine is_compact_of_totally_bounded_is_closed _ closed,
  refine totally_bounded_of_finite_discretization (λ ε ε0, _),
  rcases exists_between ε0 with ⟨ε₁, ε₁0, εε₁⟩,
  let ε₂ := ε₁/2/2,
  /- We have to find a finite discretization of `u`, i.e., finite information
  that is sufficient to reconstruct `u` up to ε. This information will be
  provided by the values of `u` on a sufficiently dense set tα,
  slightly translated to fit in a finite ε₂-dense set tβ in the image. Such
  sets exist by compactness of the source and range. Then, to check that these
  data determine the function up to ε, one uses the control on the modulus of
  continuity to extend the closeness on tα to closeness everywhere. -/
  have ε₂0 : ε₂ > 0 := half_pos (half_pos ε₁0),
  have : ∀x:α, ∃U, x ∈ U ∧ is_open U ∧ ∀ (y z ∈ U) {f : α →ᵇ β},
    f ∈ A → dist (f y) (f z) < ε₂ := λ x,
      let ⟨U, nhdsU, hU⟩ := H x _ ε₂0,
          ⟨V, VU, openV, xV⟩ := _root_.mem_nhds_iff.1 nhdsU in
      ⟨V, xV, openV, λy hy z hz f hf, hU y (VU hy) z (VU hz) ⟨f, hf⟩⟩,
  choose U hU using this,
  /- For all x, the set hU x is an open set containing x on which the elements of A
  fluctuate by at most ε₂.
  We extract finitely many of these sets that cover the whole space, by compactness -/
  rcases is_compact_univ.elim_finite_subcover_image
    (λx _, (hU x).2.1) (λx hx, mem_bUnion (mem_univ _) (hU x).1)
    with ⟨tα, _, ⟨_⟩, htα⟩,
  /- tα : set α, htα : univ ⊆ ⋃x ∈ tα, U x -/
  rcases @finite_cover_balls_of_compact β _ _ is_compact_univ _ ε₂0
    with ⟨tβ, _, ⟨_⟩, htβ⟩, resetI,
  /- tβ : set β, htβ : univ ⊆ ⋃y ∈ tβ, ball y ε₂ -/
  /- Associate to every point `y` in the space a nearby point `F y` in tβ -/
  choose F hF using λy, show ∃z∈tβ, dist y z < ε₂, by simpa using htβ (mem_univ y),
  /- F : β → β, hF : ∀ (y : β), F y ∈ tβ ∧ dist y (F y) < ε₂ -/

  /- Associate to every function a discrete approximation, mapping each point in `tα`
  to a point in `tβ` close to its true image by the function. -/
  refine ⟨tα → tβ, by apply_instance, λ f a, ⟨F (f a), (hF (f a)).1⟩, _⟩,
  rintro ⟨f, hf⟩ ⟨g, hg⟩ f_eq_g,
  /- If two functions have the same approximation, then they are within distance ε -/
  refine lt_of_le_of_lt ((dist_le $ le_of_lt ε₁0).2 (λ x, _)) εε₁,
  obtain ⟨x', x'tα, hx'⟩ : ∃x' ∈ tα, x ∈ U x' := mem_Union₂.1 (htα (mem_univ x)),
  calc dist (f x) (g x)
      ≤ dist (f x) (f x') + dist (g x) (g x') + dist (f x') (g x') : dist_triangle4_right _ _ _ _
  ... ≤ ε₂ + ε₂ + ε₁/2 : le_of_lt (add_lt_add (add_lt_add _ _) _)
  ... = ε₁ : by rw [add_halves, add_halves],
  { exact (hU x').2.2 _ hx' _ ((hU x').1) hf },
  { exact (hU x').2.2 _ hx' _ ((hU x').1) hg },
  { have F_f_g : F (f x') = F (g x') :=
      (congr_arg (λ f:tα → tβ, (f ⟨x', x'tα⟩ : β)) f_eq_g : _),
    calc dist (f x') (g x')
          ≤ dist (f x') (F (f x')) + dist (g x') (F (f x')) : dist_triangle_right _ _ _
      ... = dist (f x') (F (f x')) + dist (g x') (F (g x')) : by rw F_f_g
      ... < ε₂ + ε₂ : add_lt_add (hF (f x')).2 (hF (g x')).2
      ... = ε₁/2 : add_halves _ }
end

/-- Second version, with pointwise equicontinuity and range in a compact subset -/
theorem arzela_ascoli₂
  (s : set β) (hs : is_compact s)
  (A : set (α →ᵇ β))
  (closed : is_closed A)
  (in_s : ∀(f : α →ᵇ β) (x : α), f ∈ A → f x ∈ s)
  (H : equicontinuous (coe_fn : A → α → β)) :
  is_compact A :=
/- This version is deduced from the previous one by restricting to the compact type in the target,
using compactness there and then lifting everything to the original space. -/
begin
  have M : lipschitz_with 1 coe := lipschitz_with.subtype_coe s,
  let F : (α →ᵇ s) → α →ᵇ β := comp coe M,
  refine is_compact_of_is_closed_subset
    ((_ : is_compact (F ⁻¹' A)).image (continuous_comp M)) closed (λ f hf, _),
  { haveI : compact_space s := is_compact_iff_compact_space.1 hs,
    refine arzela_ascoli₁ _ (continuous_iff_is_closed.1 (continuous_comp M) _ closed) _,
    rw uniform_embedding_subtype_coe.to_uniform_inducing.equicontinuous_iff,
    exact H.comp (A.restrict_preimage F) },
  { let g := cod_restrict s f (λx, in_s f x hf),
    rw [show f = F g, by ext; refl] at hf ⊢,
    exact ⟨g, hf, rfl⟩ }
end

/-- Third (main) version, with pointwise equicontinuity and range in a compact subset, but
without closedness. The closure is then compact -/
theorem arzela_ascoli [t2_space β]
  (s : set β) (hs : is_compact s)
  (A : set (α →ᵇ β))
  (in_s : ∀(f : α →ᵇ β) (x : α), f ∈ A → f x ∈ s)
  (H : equicontinuous (coe_fn : A → α → β)) :
  is_compact (closure A) :=
/- This version is deduced from the previous one by checking that the closure of A, in
addition to being closed, still satisfies the properties of compact range and equicontinuity -/
arzela_ascoli₂ s hs (closure A) is_closed_closure
  (λ f x hf, (mem_of_closed' hs.is_closed).2 $ λ ε ε0,
    let ⟨g, gA, dist_fg⟩ := metric.mem_closure_iff.1 hf ε ε0 in
    ⟨g x, in_s g x gA, lt_of_le_of_lt (dist_coe_le_dist _) dist_fg⟩)
  (H.closure' continuous_coe)

end arzela_ascoli

section has_one

variables [topological_space α] [pseudo_metric_space β] [has_one β]

@[to_additive] instance : has_one (α →ᵇ β) := ⟨const α 1⟩

@[simp, to_additive] lemma coe_one : ((1 : α →ᵇ β) : α → β) = 1 := rfl

@[simp, to_additive]
lemma mk_of_compact_one [compact_space α] : mk_of_compact (1 : C(α, β)) = 1 := rfl

@[to_additive] lemma forall_coe_one_iff_one (f : α →ᵇ β) : (∀ x, f x = 1) ↔ f = 1 :=
(@fun_like.ext_iff _ _ _ _ f 1).symm

@[simp, to_additive] lemma one_comp_continuous [topological_space γ] (f : C(γ, α)) :
  (1 : α →ᵇ β).comp_continuous f = 1 := rfl

end has_one

section has_lipschitz_add
/- In this section, if `β` is an `add_monoid` whose addition operation is Lipschitz, then we show
that the space of bounded continuous functions from `α` to `β` inherits a topological `add_monoid`
structure, by using pointwise operations and checking that they are compatible with the uniform
distance.

Implementation note: The material in this section could have been written for `has_lipschitz_mul`
and transported by `@[to_additive]`.  We choose not to do this because this causes a few lemma
names (for example, `coe_mul`) to conflict with later lemma names for normed rings; this is only a
trivial inconvenience, but in any case there are no obvious applications of the multiplicative
version. -/

variables [topological_space α] [pseudo_metric_space β] [add_monoid β]
variables [has_lipschitz_add β]
variables (f g : α →ᵇ β) {x : α} {C : ℝ}

/-- The pointwise sum of two bounded continuous functions is again bounded continuous. -/
instance : has_add (α →ᵇ β) :=
{ add := λ f g,
  bounded_continuous_function.mk_of_bound (f.to_continuous_map + g.to_continuous_map)
    (↑(has_lipschitz_add.C β) * max (classical.some f.bounded) (classical.some g.bounded))
    begin
      intros x y,
      refine le_trans (lipschitz_with_lipschitz_const_add ⟨f x, g x⟩ ⟨f y, g y⟩) _,
      rw prod.dist_eq,
      refine mul_le_mul_of_nonneg_left _ (has_lipschitz_add.C β).coe_nonneg,
      apply max_le_max,
      exact classical.some_spec f.bounded x y,
      exact classical.some_spec g.bounded x y,
    end }

@[simp] lemma coe_add : ⇑(f + g) = f + g := rfl
lemma add_apply : (f + g) x = f x + g x := rfl

@[simp] lemma mk_of_compact_add [compact_space α] (f g : C(α, β)) :
  mk_of_compact (f + g) = mk_of_compact f + mk_of_compact g := rfl

lemma add_comp_continuous [topological_space γ] (h : C(γ, α)) :
  (g + f).comp_continuous h = g.comp_continuous h + f.comp_continuous h := rfl

@[simp] lemma coe_nsmul_rec : ∀ n, ⇑(nsmul_rec n f) = n • f
| 0 := by rw [nsmul_rec, zero_smul, coe_zero]
| (n + 1) := by rw [nsmul_rec, succ_nsmul, coe_add, coe_nsmul_rec]

instance has_nat_scalar : has_smul ℕ (α →ᵇ β) :=
{ smul := λ n f,
  { to_continuous_map := n • f.to_continuous_map,
    map_bounded' := by simpa [coe_nsmul_rec] using (nsmul_rec n f).map_bounded' } }

@[simp] lemma coe_nsmul (r : ℕ) (f : α →ᵇ β) : ⇑(r • f) = r • f := rfl
@[simp] lemma nsmul_apply (r : ℕ) (f : α →ᵇ β) (v : α) : (r • f) v = r • f v := rfl

instance : add_monoid (α →ᵇ β) :=
fun_like.coe_injective.add_monoid _ coe_zero coe_add (λ _ _, coe_nsmul _ _)

instance : has_lipschitz_add (α →ᵇ β) :=
{ lipschitz_add := ⟨has_lipschitz_add.C β, begin
    have C_nonneg := (has_lipschitz_add.C β).coe_nonneg,
    rw lipschitz_with_iff_dist_le_mul,
    rintros ⟨f₁, g₁⟩ ⟨f₂, g₂⟩,
    rw dist_le (mul_nonneg C_nonneg dist_nonneg),
    intros x,
    refine le_trans (lipschitz_with_lipschitz_const_add ⟨f₁ x, g₁ x⟩ ⟨f₂ x, g₂ x⟩) _,
    refine mul_le_mul_of_nonneg_left _ C_nonneg,
    apply max_le_max; exact dist_coe_le_dist x,
  end⟩ }

/-- Coercion of a `normed_add_group_hom` is an `add_monoid_hom`. Similar to
`add_monoid_hom.coe_fn`. -/
@[simps] def coe_fn_add_hom : (α →ᵇ β) →+ (α → β) :=
{ to_fun := coe_fn, map_zero' := coe_zero, map_add' := coe_add }

variables (α β)

/-- The additive map forgetting that a bounded continuous function is bounded.
-/
@[simps] def to_continuous_map_add_hom : (α →ᵇ β) →+ C(α, β) :=
{ to_fun := to_continuous_map,
  map_zero' := by { ext, simp, },
  map_add' := by { intros, ext, simp, }, }

end has_lipschitz_add

section comm_has_lipschitz_add

variables [topological_space α] [pseudo_metric_space β] [add_comm_monoid β] [has_lipschitz_add β]

@[to_additive] instance : add_comm_monoid (α →ᵇ β) :=
{ add_comm      := assume f g, by ext; simp [add_comm],
  .. bounded_continuous_function.add_monoid }

open_locale big_operators

@[simp] lemma coe_sum {ι : Type*} (s : finset ι) (f : ι → (α →ᵇ β)) :
  ⇑(∑ i in s, f i) = (∑ i in s, (f i : α → β)) :=
(@coe_fn_add_hom α β _ _ _ _).map_sum f s

lemma sum_apply {ι : Type*} (s : finset ι) (f : ι → (α →ᵇ β)) (a : α) :
  (∑ i in s, f i) a = (∑ i in s, f i a) :=
by simp

end comm_has_lipschitz_add

section normed_add_comm_group
/- In this section, if β is a normed group, then we show that the space of bounded
continuous functions from α to β inherits a normed group structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

variables [topological_space α] [seminormed_add_comm_group β]
variables (f g : α →ᵇ β) {x : α} {C : ℝ}

instance : has_norm (α →ᵇ β) := ⟨λu, dist u 0⟩

lemma norm_def : ‖f‖ = dist f 0 := rfl

/-- The norm of a bounded continuous function is the supremum of `‖f x‖`.
We use `Inf` to ensure that the definition works if `α` has no elements. -/
lemma norm_eq (f : α →ᵇ β) :
  ‖f‖ = Inf {C : ℝ | 0 ≤ C ∧ ∀ (x : α), ‖f x‖ ≤ C} :=
by simp [norm_def, bounded_continuous_function.dist_eq]

/-- When the domain is non-empty, we do not need the `0 ≤ C` condition in the formula for ‖f‖ as an
`Inf`. -/
lemma norm_eq_of_nonempty [h : nonempty α] : ‖f‖ = Inf {C : ℝ | ∀ (x : α), ‖f x‖ ≤ C} :=
begin
  unfreezingI { obtain ⟨a⟩ := h, },
  rw norm_eq,
  congr,
  ext,
  simp only [and_iff_right_iff_imp],
  exact λ h', le_trans (norm_nonneg (f a)) (h' a),
end

@[simp] lemma norm_eq_zero_of_empty [h : is_empty α] : ‖f‖ = 0 :=
dist_zero_of_empty

lemma norm_coe_le_norm (x : α) : ‖f x‖ ≤ ‖f‖ := calc
  ‖f x‖ = dist (f x) ((0 : α →ᵇ β) x) : by simp [dist_zero_right]
  ... ≤ ‖f‖ : dist_coe_le_dist _

lemma dist_le_two_norm' {f : γ → β} {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x y : γ) :
  dist (f x) (f y) ≤ 2 * C :=
calc dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ : dist_le_norm_add_norm _ _
                  ... ≤ C + C         : add_le_add (hC x) (hC y)
                  ... = 2 * C         : (two_mul _).symm

/-- Distance between the images of any two points is at most twice the norm of the function. -/
lemma dist_le_two_norm (x y : α) : dist (f x) (f y) ≤ 2 * ‖f‖ :=
dist_le_two_norm' f.norm_coe_le_norm x y

variable {f}

/-- The norm of a function is controlled by the supremum of the pointwise norms -/
lemma norm_le (C0 : (0 : ℝ) ≤ C) : ‖f‖ ≤ C ↔ ∀x:α, ‖f x‖ ≤ C :=
by simpa using @dist_le _ _ _ _ f 0 _ C0

lemma norm_le_of_nonempty [nonempty α]
  {f : α →ᵇ β} {M : ℝ} : ‖f‖ ≤ M ↔ ∀ x, ‖f x‖ ≤ M :=
begin
  simp_rw [norm_def, ←dist_zero_right],
  exact dist_le_iff_of_nonempty,
end

lemma norm_lt_iff_of_compact [compact_space α]
  {f : α →ᵇ β} {M : ℝ} (M0 : 0 < M) : ‖f‖ < M ↔ ∀ x, ‖f x‖ < M :=
begin
  simp_rw [norm_def, ←dist_zero_right],
  exact dist_lt_iff_of_compact M0,
end

lemma norm_lt_iff_of_nonempty_compact [nonempty α] [compact_space α]
  {f : α →ᵇ β} {M : ℝ} : ‖f‖ < M ↔ ∀ x, ‖f x‖ < M :=
begin
  simp_rw [norm_def, ←dist_zero_right],
  exact dist_lt_iff_of_nonempty_compact,
end

variable (f)

/-- Norm of `const α b` is less than or equal to `‖b‖`. If `α` is nonempty,
then it is equal to `‖b‖`. -/
lemma norm_const_le (b : β) : ‖const α b‖ ≤ ‖b‖ :=
(norm_le (norm_nonneg b)).2 $ λ x, le_rfl

@[simp] lemma norm_const_eq [h : nonempty α] (b : β) : ‖const α b‖ = ‖b‖ :=
le_antisymm (norm_const_le b) $ h.elim $ λ x, (const α b).norm_coe_le_norm x

/-- Constructing a bounded continuous function from a uniformly bounded continuous
function taking values in a normed group. -/
def of_normed_add_comm_group {α : Type u} {β : Type v} [topological_space α]
  [seminormed_add_comm_group β] (f : α → β) (Hf : continuous f) (C : ℝ) (H : ∀x, ‖f x‖ ≤ C) :
  α →ᵇ β :=
⟨⟨λn, f n, Hf⟩, ⟨_, dist_le_two_norm' H⟩⟩

@[simp] lemma coe_of_normed_add_comm_group
  {α : Type u} {β : Type v} [topological_space α] [seminormed_add_comm_group β]
  (f : α → β) (Hf : continuous f) (C : ℝ) (H : ∀x, ‖f x‖ ≤ C) :
  (of_normed_add_comm_group f Hf C H : α → β) = f := rfl

lemma norm_of_normed_add_comm_group_le {f : α → β} (hfc : continuous f) {C : ℝ} (hC : 0 ≤ C)
  (hfC : ∀ x, ‖f x‖ ≤ C) : ‖of_normed_add_comm_group f hfc C hfC‖ ≤ C :=
(norm_le hC).2 hfC

/-- Constructing a bounded continuous function from a uniformly bounded
function on a discrete space, taking values in a normed group -/
def of_normed_add_comm_group_discrete {α : Type u} {β : Type v}
  [topological_space α] [discrete_topology α] [seminormed_add_comm_group β]
  (f : α  → β) (C : ℝ) (H : ∀x, norm (f x) ≤ C) : α →ᵇ β :=
of_normed_add_comm_group f continuous_of_discrete_topology C H

@[simp] lemma coe_of_normed_add_comm_group_discrete {α : Type u} {β : Type v} [topological_space α]
  [discrete_topology α] [seminormed_add_comm_group β] (f : α → β) (C : ℝ) (H : ∀x, ‖f x‖ ≤ C) :
  (of_normed_add_comm_group_discrete f C H : α → β) = f := rfl

/-- Taking the pointwise norm of a bounded continuous function with values in a
`seminormed_add_comm_group` yields a bounded continuous function with values in ℝ. -/
def norm_comp : α →ᵇ ℝ :=
f.comp norm lipschitz_with_one_norm

@[simp] lemma coe_norm_comp : (f.norm_comp : α → ℝ) = norm ∘ f := rfl

@[simp] lemma norm_norm_comp : ‖f.norm_comp‖ = ‖f‖ :=
by simp only [norm_eq, coe_norm_comp, norm_norm]

lemma bdd_above_range_norm_comp : bdd_above $ set.range $ norm ∘ f :=
(real.bounded_iff_bdd_below_bdd_above.mp $ @bounded_range _ _ _ _ f.norm_comp).2

lemma norm_eq_supr_norm : ‖f‖ = ⨆ x : α, ‖f x‖ :=
by simp_rw [norm_def, dist_eq_supr, coe_zero, pi.zero_apply, dist_zero_right]

/-- If `‖(1 : β)‖ = 1`, then `‖(1 : α →ᵇ β)‖ = 1` if `α` is nonempty. -/
instance [nonempty α] [has_one β] [norm_one_class β] : norm_one_class (α →ᵇ β) :=
{ norm_one := by simp only [norm_eq_supr_norm, coe_one, pi.one_apply, norm_one, csupr_const] }

/-- The pointwise opposite of a bounded continuous function is again bounded continuous. -/
instance : has_neg (α →ᵇ β) :=
⟨λf, of_normed_add_comm_group (-f) f.continuous.neg ‖f‖ $ λ x,
  trans_rel_right _ (norm_neg _) (f.norm_coe_le_norm x)⟩

/-- The pointwise difference of two bounded continuous functions is again bounded continuous. -/
instance : has_sub (α →ᵇ β) :=
⟨λf g, of_normed_add_comm_group (f - g) (f.continuous.sub g.continuous) (‖f‖ + ‖g‖) $ λ x,
  by { simp only [sub_eq_add_neg],
       exact le_trans (norm_add_le _ _) (add_le_add (f.norm_coe_le_norm x) $
         trans_rel_right _ (norm_neg _) (g.norm_coe_le_norm x)) }⟩

@[simp] lemma coe_neg : ⇑(-f) = -f := rfl
lemma neg_apply : (-f) x = -f x := rfl

@[simp] lemma coe_sub : ⇑(f - g) = f - g := rfl
lemma sub_apply : (f - g) x = f x - g x := rfl

@[simp] lemma mk_of_compact_neg [compact_space α] (f : C(α, β)) :
  mk_of_compact (-f) = -mk_of_compact f := rfl

@[simp] lemma mk_of_compact_sub [compact_space α] (f g : C(α, β)) :
  mk_of_compact (f - g) = mk_of_compact f - mk_of_compact g := rfl

@[simp] lemma coe_zsmul_rec : ∀ z, ⇑(zsmul_rec z f) = z • f
| (int.of_nat n) := by rw [zsmul_rec, int.of_nat_eq_coe, coe_nsmul_rec, coe_nat_zsmul]
| -[1+ n] := by rw [zsmul_rec, zsmul_neg_succ_of_nat, coe_neg, coe_nsmul_rec]

instance has_int_scalar : has_smul ℤ (α →ᵇ β) :=
{ smul := λ n f,
  { to_continuous_map := n • f.to_continuous_map,
    map_bounded' := by simpa using (zsmul_rec n f).map_bounded' } }

@[simp] lemma coe_zsmul (r : ℤ) (f : α →ᵇ β) : ⇑(r • f) = r • f := rfl
@[simp] lemma zsmul_apply (r : ℤ) (f : α →ᵇ β) (v : α) : (r • f) v = r • f v := rfl

instance : add_comm_group (α →ᵇ β) :=
fun_like.coe_injective.add_comm_group _ coe_zero coe_add coe_neg coe_sub (λ _ _, coe_nsmul _ _)
  (λ _ _, coe_zsmul _ _)

instance : seminormed_add_comm_group (α →ᵇ β) :=
{ dist_eq := λ f g, by simp only [norm_eq, dist_eq, dist_eq_norm, sub_apply] }

instance {α β} [topological_space α] [normed_add_comm_group β] : normed_add_comm_group (α →ᵇ β) :=
{ ..bounded_continuous_function.seminormed_add_comm_group }

lemma nnnorm_def : ‖f‖₊ = nndist f 0 := rfl

lemma nnnorm_coe_le_nnnorm (x : α) : ‖f x‖₊ ≤ ‖f‖₊ := norm_coe_le_norm _ _

lemma nndist_le_two_nnnorm (x y : α) : nndist (f x) (f y) ≤ 2 * ‖f‖₊ := dist_le_two_norm _ _ _

/-- The nnnorm of a function is controlled by the supremum of the pointwise nnnorms -/
lemma nnnorm_le (C : ℝ≥0) : ‖f‖₊ ≤ C ↔ ∀x:α, ‖f x‖₊ ≤ C :=
norm_le C.prop

lemma nnnorm_const_le (b : β) : ‖const α b‖₊ ≤ ‖b‖₊ :=
norm_const_le _

@[simp] lemma nnnorm_const_eq [h : nonempty α] (b : β) : ‖const α b‖₊ = ‖b‖₊ :=
subtype.ext $ norm_const_eq _

lemma nnnorm_eq_supr_nnnorm : ‖f‖₊ = ⨆ x : α, ‖f x‖₊ :=
subtype.ext $ (norm_eq_supr_norm f).trans $ by simp_rw [nnreal.coe_supr, coe_nnnorm]

lemma abs_diff_coe_le_dist : ‖f x - g x‖ ≤ dist f g :=
by { rw dist_eq_norm, exact (f - g).norm_coe_le_norm x }

lemma coe_le_coe_add_dist {f g : α →ᵇ ℝ} : f x ≤ g x + dist f g :=
sub_le_iff_le_add'.1 $ (abs_le.1 $ @dist_coe_le_dist _ _ _ _ f g x).2

lemma norm_comp_continuous_le [topological_space γ] (f : α →ᵇ β) (g : C(γ, α)) :
  ‖f.comp_continuous g‖ ≤ ‖f‖ :=
((lipschitz_comp_continuous g).dist_le_mul f 0).trans $
  by rw [nnreal.coe_one, one_mul, dist_zero_right]

end normed_add_comm_group

section has_bounded_smul
/-!
### `has_bounded_smul` (in particular, topological module) structure

In this section, if `β` is a metric space and a `𝕜`-module whose addition and scalar multiplication
are compatible with the metric structure, then we show that the space of bounded continuous
functions from `α` to `β` inherits a so-called `has_bounded_smul` structure (in particular, a
`has_continuous_mul` structure, which is the mathlib formulation of being a topological module), by
using pointwise operations and checking that they are compatible with the uniform distance. -/

variables {𝕜 : Type*} [pseudo_metric_space 𝕜] [topological_space α] [pseudo_metric_space β]

section has_smul
variables [has_zero 𝕜] [has_zero β] [has_smul 𝕜 β] [has_bounded_smul 𝕜 β]

instance : has_smul 𝕜 (α →ᵇ β) :=
{ smul := λ c f,
  { to_continuous_map := c • f.to_continuous_map,
    map_bounded' := let ⟨b, hb⟩ := f.bounded in ⟨dist c 0 * b, λ x y, begin
      refine (dist_smul_pair c (f x) (f y)).trans _,
      refine mul_le_mul_of_nonneg_left _ dist_nonneg,
      exact hb x y
    end⟩ } }

@[simp] lemma coe_smul (c : 𝕜) (f : α →ᵇ β) : ⇑(c • f) = λ x, c • (f x) := rfl
lemma smul_apply (c : 𝕜) (f : α →ᵇ β) (x : α) : (c • f) x = c • f x := rfl

instance [has_smul 𝕜ᵐᵒᵖ β] [is_central_scalar 𝕜 β] : is_central_scalar 𝕜 (α →ᵇ β) :=
{ op_smul_eq_smul := λ _ _, ext $ λ _, op_smul_eq_smul _ _ }

instance : has_bounded_smul 𝕜 (α →ᵇ β) :=
{ dist_smul_pair' := λ c f₁ f₂, begin
    rw dist_le (mul_nonneg dist_nonneg dist_nonneg),
    intros x,
    refine (dist_smul_pair c (f₁ x) (f₂ x)).trans _,
    exact mul_le_mul_of_nonneg_left (dist_coe_le_dist x) dist_nonneg
  end,
  dist_pair_smul' := λ c₁ c₂ f, begin
    rw dist_le (mul_nonneg dist_nonneg dist_nonneg),
    intros x,
    refine (dist_pair_smul c₁ c₂ (f x)).trans _,
    convert mul_le_mul_of_nonneg_left (dist_coe_le_dist x) dist_nonneg,
    simp
  end }

end has_smul

section mul_action
variables [monoid_with_zero 𝕜] [has_zero β] [mul_action 𝕜 β] [has_bounded_smul 𝕜 β]

instance : mul_action 𝕜 (α →ᵇ β) := fun_like.coe_injective.mul_action _ coe_smul

end mul_action

section distrib_mul_action
variables [monoid_with_zero 𝕜] [add_monoid β] [distrib_mul_action 𝕜 β] [has_bounded_smul 𝕜 β]
variables [has_lipschitz_add β]

instance : distrib_mul_action 𝕜 (α →ᵇ β) :=
function.injective.distrib_mul_action ⟨_, coe_zero, coe_add⟩ fun_like.coe_injective coe_smul

end distrib_mul_action

section module
variables [semiring 𝕜] [add_comm_monoid β] [module 𝕜 β] [has_bounded_smul 𝕜 β]
variables {f g : α →ᵇ β} {x : α} {C : ℝ}

variables [has_lipschitz_add β]

instance : module 𝕜 (α →ᵇ β) :=
function.injective.module _ ⟨_, coe_zero, coe_add⟩ fun_like.coe_injective coe_smul

variables (𝕜)
/-- The evaluation at a point, as a continuous linear map from `α →ᵇ β` to `β`. -/
def eval_clm (x : α) : (α →ᵇ β) →L[𝕜] β :=
{ to_fun := λ f, f x,
  map_add' := λ f g, add_apply _ _,
  map_smul' := λ c f, smul_apply _ _ _ }

@[simp] lemma eval_clm_apply (x : α) (f : α →ᵇ β) :
  eval_clm 𝕜 x f = f x := rfl

variables (α β)

/-- The linear map forgetting that a bounded continuous function is bounded. -/
@[simps]
def to_continuous_map_linear_map : (α →ᵇ β) →ₗ[𝕜] C(α, β) :=
{ to_fun := to_continuous_map,
  map_smul' := λ f g, rfl,
  map_add' := λ c f, rfl }

end module

end has_bounded_smul

section normed_space
/-!
### Normed space structure

In this section, if `β` is a normed space, then we show that the space of bounded
continuous functions from `α` to `β` inherits a normed space structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

variables {𝕜 : Type*}
variables [topological_space α] [seminormed_add_comm_group β]
variables {f g : α →ᵇ β} {x : α} {C : ℝ}

instance [normed_field 𝕜] [normed_space 𝕜 β] : normed_space 𝕜 (α →ᵇ β) := ⟨λ c f, begin
  refine norm_of_normed_add_comm_group_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _,
  exact (λ x, trans_rel_right _ (norm_smul _ _)
    (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _))) end⟩

variables [nontrivially_normed_field 𝕜] [normed_space 𝕜 β]
variables [seminormed_add_comm_group γ] [normed_space 𝕜 γ]

variables (α)
-- TODO does this work in the `has_bounded_smul` setting, too?
/--
Postcomposition of bounded continuous functions into a normed module by a continuous linear map is
a continuous linear map.
Upgraded version of `continuous_linear_map.comp_left_continuous`, similar to
`linear_map.comp_left`. -/
protected def _root_.continuous_linear_map.comp_left_continuous_bounded (g : β →L[𝕜] γ) :
  (α →ᵇ β) →L[𝕜] (α →ᵇ γ) :=
linear_map.mk_continuous
  { to_fun := λ f, of_normed_add_comm_group
      (g ∘ f)
      (g.continuous.comp f.continuous)
      (‖g‖ * ‖f‖)
      (λ x, (g.le_op_norm_of_le (f.norm_coe_le_norm x))),
    map_add' := λ f g, by ext; simp,
    map_smul' := λ c f, by ext; simp }
  ‖g‖
  (λ f, norm_of_normed_add_comm_group_le _ (mul_nonneg (norm_nonneg g) (norm_nonneg f)) _)

@[simp] lemma _root_.continuous_linear_map.comp_left_continuous_bounded_apply (g : β →L[𝕜] γ)
  (f : α →ᵇ β) (x : α) :
  (g.comp_left_continuous_bounded α f) x = g (f x) :=
rfl

end normed_space

section normed_ring
/-!
### Normed ring structure

In this section, if `R` is a normed ring, then we show that the space of bounded
continuous functions from `α` to `R` inherits a normed ring structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

variables [topological_space α] {R : Type*}

section non_unital

section semi_normed
variables [non_unital_semi_normed_ring R]

instance : has_mul (α →ᵇ R) :=
{ mul := λ f g, of_normed_add_comm_group (f * g) (f.continuous.mul g.continuous) (‖f‖ * ‖g‖) $ λ x,
    le_trans (norm_mul_le (f x) (g x)) $
      mul_le_mul (f.norm_coe_le_norm x) (g.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _) }

@[simp] lemma coe_mul (f g : α →ᵇ R) : ⇑(f * g) = f * g := rfl
lemma mul_apply (f g : α →ᵇ R) (x : α) : (f * g) x = f x * g x := rfl

instance : non_unital_ring (α →ᵇ R) :=
fun_like.coe_injective.non_unital_ring _ coe_zero coe_add coe_mul coe_neg coe_sub
  (λ _ _, coe_nsmul _ _) (λ _ _, coe_zsmul _ _)

instance : non_unital_semi_normed_ring (α →ᵇ R) :=
{ norm_mul := λ f g, norm_of_normed_add_comm_group_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _,
  .. bounded_continuous_function.seminormed_add_comm_group }

end semi_normed

instance [non_unital_normed_ring R] : non_unital_normed_ring (α →ᵇ R) :=
{ .. bounded_continuous_function.non_unital_semi_normed_ring,
  .. bounded_continuous_function.normed_add_comm_group }

end non_unital

section semi_normed

variables [semi_normed_ring R]

@[simp] lemma coe_npow_rec (f : α →ᵇ R) : ∀ n, ⇑(npow_rec n f) = f ^ n
| 0 := by rw [npow_rec, pow_zero, coe_one]
| (n + 1) := by rw [npow_rec, pow_succ, coe_mul, coe_npow_rec]

instance has_nat_pow : has_pow (α →ᵇ R) ℕ :=
{ pow := λ f n,
  { to_continuous_map := f.to_continuous_map ^ n,
    map_bounded' := by simpa [coe_npow_rec] using (npow_rec n f).map_bounded' } }

@[simp] lemma coe_pow (n : ℕ) (f : α →ᵇ R) : ⇑(f ^ n) = f ^ n := rfl
@[simp] lemma pow_apply (n : ℕ) (f : α →ᵇ R) (v : α) : (f ^ n) v = f v ^ n := rfl

instance : has_nat_cast (α →ᵇ R) :=
⟨λ n, bounded_continuous_function.const _ n⟩

@[simp, norm_cast] lemma coe_nat_cast (n : ℕ) : ((n : α →ᵇ R) : α → R) = n := rfl

instance : has_int_cast (α →ᵇ R) :=
⟨λ n, bounded_continuous_function.const _ n⟩

@[simp, norm_cast] lemma coe_int_cast (n : ℤ) : ((n : α →ᵇ R) : α → R) = n := rfl

instance : ring (α →ᵇ R) :=
fun_like.coe_injective.ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub
  (λ _ _, coe_nsmul _ _)
  (λ _ _, coe_zsmul _ _)
  (λ _ _, coe_pow _ _)
  coe_nat_cast
  coe_int_cast

instance : semi_normed_ring (α →ᵇ R) :=
{ ..bounded_continuous_function.non_unital_semi_normed_ring }

end semi_normed

instance [normed_ring R] : normed_ring (α →ᵇ R) :=
{ ..bounded_continuous_function.non_unital_normed_ring }

end normed_ring

section normed_comm_ring
/-!
### Normed commutative ring structure

In this section, if `R` is a normed commutative ring, then we show that the space of bounded
continuous functions from `α` to `R` inherits a normed commutative ring structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

variables [topological_space α] {R : Type*}

instance [semi_normed_comm_ring R] : comm_ring (α →ᵇ R) :=
{ mul_comm := λ f₁ f₂, ext $ λ x, mul_comm _ _,
  .. bounded_continuous_function.ring }

instance [semi_normed_comm_ring R] : semi_normed_comm_ring (α →ᵇ R) :=
{ ..bounded_continuous_function.comm_ring, ..bounded_continuous_function.seminormed_add_comm_group }

instance [normed_comm_ring R] : normed_comm_ring (α →ᵇ R) :=
{ .. bounded_continuous_function.comm_ring, .. bounded_continuous_function.normed_add_comm_group }

end normed_comm_ring

section normed_algebra
/-!
### Normed algebra structure

In this section, if `γ` is a normed algebra, then we show that the space of bounded
continuous functions from `α` to `γ` inherits a normed algebra structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

variables {𝕜 : Type*} [normed_field 𝕜]
variables [topological_space α] [seminormed_add_comm_group β] [normed_space 𝕜 β]
variables [normed_ring γ] [normed_algebra 𝕜 γ]
variables {f g : α →ᵇ γ} {x : α} {c : 𝕜}

/-- `bounded_continuous_function.const` as a `ring_hom`. -/
def C : 𝕜 →+* (α →ᵇ γ) :=
{ to_fun    := λ (c : 𝕜), const α ((algebra_map 𝕜 γ) c),
  map_one'  := ext $ λ x, (algebra_map 𝕜 γ).map_one,
  map_mul'  := λ c₁ c₂, ext $ λ x, (algebra_map 𝕜 γ).map_mul _ _,
  map_zero' := ext $ λ x, (algebra_map 𝕜 γ).map_zero,
  map_add'  := λ c₁ c₂, ext $ λ x, (algebra_map 𝕜 γ).map_add _ _ }

instance : algebra 𝕜 (α →ᵇ γ) :=
{ to_ring_hom := C,
  commutes' := λ c f, ext $ λ x, algebra.commutes' _ _,
  smul_def' := λ c f, ext $ λ x, algebra.smul_def' _ _,
  ..bounded_continuous_function.module,
  ..bounded_continuous_function.ring }

@[simp] lemma algebra_map_apply (k : 𝕜) (a : α) :
  algebra_map 𝕜 (α →ᵇ γ) k a = k • 1 :=
by { rw algebra.algebra_map_eq_smul_one, refl, }

instance : normed_algebra 𝕜 (α →ᵇ γ) :=
{ ..bounded_continuous_function.normed_space }

/-!
### Structure as normed module over scalar functions

If `β` is a normed `𝕜`-space, then we show that the space of bounded continuous
functions from `α` to `β` is naturally a module over the algebra of bounded continuous
functions from `α` to `𝕜`. -/

instance has_smul' : has_smul (α →ᵇ 𝕜) (α →ᵇ β) :=
⟨λ (f : α →ᵇ 𝕜) (g : α →ᵇ β), of_normed_add_comm_group (λ x, (f x) • (g x))
(f.continuous.smul g.continuous) (‖f‖ * ‖g‖) (λ x, calc
  ‖f x • g x‖ ≤ ‖f x‖ * ‖g x‖ : normed_space.norm_smul_le _ _
  ... ≤ ‖f‖ * ‖g‖ : mul_le_mul (f.norm_coe_le_norm _) (g.norm_coe_le_norm _) (norm_nonneg _)
    (norm_nonneg _)) ⟩

instance module' : module (α →ᵇ 𝕜) (α →ᵇ β) :=
module.of_core $
{ smul     := (•),
  smul_add := λ c f₁ f₂, ext $ λ x, smul_add _ _ _,
  add_smul := λ c₁ c₂ f, ext $ λ x, add_smul _ _ _,
  mul_smul := λ c₁ c₂ f, ext $ λ x, mul_smul _ _ _,
  one_smul := λ f, ext $ λ x, one_smul 𝕜 (f x) }

lemma norm_smul_le (f : α →ᵇ 𝕜) (g : α →ᵇ β) : ‖f • g‖ ≤ ‖f‖ * ‖g‖ :=
norm_of_normed_add_comm_group_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _

/- TODO: When `normed_module` has been added to `normed_space.basic`, the above facts
show that the space of bounded continuous functions from `α` to `β` is naturally a normed
module over the algebra of bounded continuous functions from `α` to `𝕜`. -/

end normed_algebra

lemma nnreal.upper_bound {α : Type*} [topological_space α]
  (f : α →ᵇ ℝ≥0) (x : α) : f x ≤ nndist f 0 :=
begin
  have key : nndist (f x) ((0 : α →ᵇ ℝ≥0) x) ≤ nndist f 0,
  { exact @dist_coe_le_dist α ℝ≥0 _ _ f 0 x, },
  simp only [coe_zero, pi.zero_apply] at key,
  rwa nnreal.nndist_zero_eq_val' (f x) at key,
end

/-!
### Star structures

In this section, if `β` is a normed ⋆-group, then so is the space of bounded
continuous functions from `α` to `β`, by using the star operation pointwise.

If `𝕜` is normed field and a ⋆-ring over which `β` is a normed algebra and a
star module, then the space of bounded continuous functions from `α` to `β`
is a star module.

If `β` is a ⋆-ring in addition to being a normed ⋆-group, then `α →ᵇ β`
inherits a ⋆-ring structure.

In summary, if `β` is a C⋆-algebra over `𝕜`, then so is  `α →ᵇ β`; note that
completeness is guaranteed when `β` is complete (see
`bounded_continuous_function.complete`). -/

section normed_add_comm_group

variables {𝕜 : Type*} [normed_field 𝕜] [star_ring 𝕜] [topological_space α]
  [seminormed_add_comm_group β] [star_add_monoid β] [normed_star_group β]
variables [normed_space 𝕜 β] [star_module 𝕜 β]

instance : star_add_monoid (α →ᵇ β) :=
{ star            := λ f, f.comp star star_normed_add_group_hom.lipschitz,
  star_involutive := λ f, ext $ λ x, star_star (f x),
  star_add        := λ f g, ext $ λ x, star_add (f x) (g x) }

/-- The right-hand side of this equality can be parsed `star ∘ ⇑f` because of the
instance `pi.has_star`. Upon inspecting the goal, one sees `⊢ ⇑(star f) = star ⇑f`.-/
@[simp] lemma coe_star (f : α →ᵇ β) : ⇑(star f) = star f := rfl

@[simp] lemma star_apply (f : α →ᵇ β) (x : α) : star f x = star (f x) := rfl

instance : normed_star_group (α →ᵇ β) :=
{ norm_star := λ f, by simp only [norm_eq, star_apply, norm_star] }

instance : star_module 𝕜 (α →ᵇ β) :=
{ star_smul := λ k f, ext $ λ x, star_smul k (f x) }

end normed_add_comm_group

section cstar_ring

variables [topological_space α]
variables [non_unital_normed_ring β] [star_ring β]

instance [normed_star_group β] : star_ring (α →ᵇ β) :=
{ star_mul := λ f g, ext $ λ x, star_mul (f x) (g x),
  ..bounded_continuous_function.star_add_monoid }

variable [cstar_ring β]

instance : cstar_ring (α →ᵇ β) :=
{ norm_star_mul_self :=
  begin
    intro f,
    refine le_antisymm _ _,
    { rw [←sq, norm_le (sq_nonneg _)],
      dsimp [star_apply],
      intro x,
      rw [cstar_ring.norm_star_mul_self, ←sq],
      refine sq_le_sq' _ _,
      { linarith [norm_nonneg (f x), norm_nonneg f] },
      { exact norm_coe_le_norm f x }, },
    { rw [←sq, ←real.le_sqrt (norm_nonneg _) (norm_nonneg _), norm_le (real.sqrt_nonneg _)],
      intro x,
      rw [real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq, ←cstar_ring.norm_star_mul_self],
      exact norm_coe_le_norm (star f * f) x }
  end }

end cstar_ring

section normed_lattice_ordered_group

variables [topological_space α] [normed_lattice_add_comm_group β]

instance : partial_order (α →ᵇ β) := partial_order.lift (λ f, f.to_fun) (by tidy)

/--
Continuous normed lattice group valued functions form a meet-semilattice
-/
instance : semilattice_inf (α →ᵇ β) :=
{ inf := λ f g,
  { to_fun := λ t, f t ⊓ g t,
    continuous_to_fun := f.continuous.inf g.continuous,
    map_bounded' := begin
      obtain ⟨C₁, hf⟩ := f.bounded,
      obtain ⟨C₂, hg⟩ := g.bounded,
      refine ⟨C₁ + C₂, λ x y, _⟩,
      simp_rw normed_add_comm_group.dist_eq at hf hg ⊢,
      exact (norm_inf_sub_inf_le_add_norm _ _ _ _).trans (add_le_add (hf _ _) (hg _ _)),
    end },
  inf_le_left := λ f g, continuous_map.le_def.mpr (λ _, inf_le_left),
  inf_le_right := λ f g, continuous_map.le_def.mpr (λ _, inf_le_right),
  le_inf := λ f g₁ g₂ w₁ w₂, continuous_map.le_def.mpr (λ _, le_inf (continuous_map.le_def.mp w₁ _)
    (continuous_map.le_def.mp w₂ _)),
  ..bounded_continuous_function.partial_order }

instance : semilattice_sup (α →ᵇ β) :=
{ sup := λ f g,
  { to_fun := λ t, f t ⊔ g t,
    continuous_to_fun := f.continuous.sup g.continuous,
    map_bounded' := begin
      obtain ⟨C₁, hf⟩ := f.bounded,
      obtain ⟨C₂, hg⟩ := g.bounded,
      refine ⟨C₁ + C₂, λ x y, _⟩,
      simp_rw normed_add_comm_group.dist_eq at hf hg ⊢,
      exact (norm_sup_sub_sup_le_add_norm _ _ _ _).trans (add_le_add (hf _ _) (hg _ _)),
    end },
  le_sup_left := λ f g, continuous_map.le_def.mpr (λ _, le_sup_left),
  le_sup_right := λ f g, continuous_map.le_def.mpr (λ _, le_sup_right),
  sup_le := λ f g₁ g₂ w₁ w₂, continuous_map.le_def.mpr (λ _, sup_le (continuous_map.le_def.mp w₁ _)
    (continuous_map.le_def.mp w₂ _)),
  ..bounded_continuous_function.partial_order }

instance  : lattice (α →ᵇ β) :=
{ .. bounded_continuous_function.semilattice_sup, .. bounded_continuous_function.semilattice_inf }

@[simp] lemma coe_fn_sup (f g : α →ᵇ β) : ⇑(f ⊔ g) = f ⊔ g := rfl

@[simp] lemma coe_fn_abs (f : α →ᵇ β) : ⇑|f| = |f| := rfl

instance : normed_lattice_add_comm_group (α →ᵇ β) :=
{ add_le_add_left := begin
    intros f g h₁ h t,
    simp only [coe_to_continuous_fun, pi.add_apply, add_le_add_iff_left, coe_add,
      continuous_map.to_fun_eq_coe],
    exact h₁ _,
  end,
  solid :=
  begin
    intros f g h,
    have i1: ∀ t, ‖f t‖ ≤ ‖g t‖ := λ t, solid (h t),
    rw norm_le (norm_nonneg _),
    exact λ t, (i1 t).trans (norm_coe_le_norm g t),
  end,
  ..bounded_continuous_function.lattice, ..bounded_continuous_function.seminormed_add_comm_group }

end normed_lattice_ordered_group

section nonnegative_part

variables [topological_space α]

/-- The nonnegative part of a bounded continuous `ℝ`-valued function as a bounded
continuous `ℝ≥0`-valued function. -/
def nnreal_part (f : α →ᵇ ℝ) : α →ᵇ ℝ≥0 :=
bounded_continuous_function.comp _
  (show lipschitz_with 1 real.to_nnreal, from lipschitz_with_pos) f

@[simp] lemma nnreal_part_coe_fun_eq (f : α →ᵇ ℝ) : ⇑(f.nnreal_part) = real.to_nnreal ∘ ⇑f := rfl

/-- The absolute value of a bounded continuous `ℝ`-valued function as a bounded
continuous `ℝ≥0`-valued function. -/
def nnnorm (f : α →ᵇ ℝ) : α →ᵇ ℝ≥0 :=
bounded_continuous_function.comp _
  (show lipschitz_with 1 (λ (x : ℝ), ‖x‖₊), from lipschitz_with_one_norm) f

@[simp] lemma nnnorm_coe_fun_eq (f : α →ᵇ ℝ) : ⇑(f.nnnorm) = has_nnnorm.nnnorm ∘ ⇑f := rfl

/-- Decompose a bounded continuous function to its positive and negative parts. -/
lemma self_eq_nnreal_part_sub_nnreal_part_neg (f : α →ᵇ ℝ) :
  ⇑f = coe ∘ f.nnreal_part - coe ∘ (-f).nnreal_part :=
by { funext x, dsimp, simp only [max_zero_sub_max_neg_zero_eq_self], }

/-- Express the absolute value of a bounded continuous function in terms of its
positive and negative parts. -/
lemma abs_self_eq_nnreal_part_add_nnreal_part_neg (f : α →ᵇ ℝ) :
  abs ∘ ⇑f = coe ∘ f.nnreal_part + coe ∘ (-f).nnreal_part :=
by { funext x, dsimp, simp only [max_zero_add_max_neg_zero_eq_abs_self], }

end nonnegative_part

end bounded_continuous_function
