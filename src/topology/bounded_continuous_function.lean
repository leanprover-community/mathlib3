/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro

Type of bounded continuous functions taking values in a metric space, with
the uniform distance.
 -/

import analysis.normed_space.basic topology.metric_space.lipschitz

noncomputable theory
local attribute [instance] classical.decidable_inhabited classical.prop_decidable
open_locale topological_space

open set lattice filter metric

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

/-- A locally uniform limit of continuous functions is continuous -/
lemma continuous_of_locally_uniform_limit_of_continuous [topological_space α] [metric_space β]
  {F : ℕ → α → β} {f : α → β}
  (L : ∀x:α, ∃s ∈ 𝓝 x, ∀ε>(0:ℝ), ∃n, ∀y∈s, dist (F n y) (f y) ≤ ε)
  (C : ∀ n, continuous (F n)) : continuous f :=
continuous_iff'.2 $ λ x ε ε0, begin
  rcases L x with ⟨r, rx, hr⟩,
  rcases hr (ε/2/2) (half_pos $ half_pos ε0) with ⟨n, hn⟩,
  rcases continuous_iff'.1 (C n) x (ε/2) (half_pos ε0) with ⟨s, sx, hs⟩,
  refine ⟨_, (𝓝 x).inter_sets rx sx, _⟩,
  rintro y ⟨yr, ys⟩,
  calc dist (f y) (f x)
        ≤ dist (F n y) (F n x) + (dist (F n y) (f y) + dist (F n x) (f x)) : dist_triangle4_left _ _ _ _
    ... < ε/2 + (ε/2/2 + ε/2/2) :
      add_lt_add_of_lt_of_le (hs _ ys) (add_le_add (hn _ yr) (hn _ (mem_of_nhds rx)))
    ... = ε : by rw [add_halves, add_halves]
end

/-- A uniform limit of continuous functions is continuous -/
lemma continuous_of_uniform_limit_of_continuous [topological_space α] {β : Type v} [metric_space β]
  {F : ℕ → α → β} {f : α → β} (L : ∀ε>(0:ℝ), ∃N, ∀y, dist (F N y) (f y) ≤ ε) :
  (∀ n, continuous (F n)) → continuous f :=
continuous_of_locally_uniform_limit_of_continuous $ λx,
  ⟨univ, by simpa [filter.univ_mem_sets] using L⟩

/-- The type of bounded continuous functions from a topological space to a metric space -/
def bounded_continuous_function (α : Type u) (β : Type v) [topological_space α] [metric_space β] : Type (max u v) :=
{f : α → β // continuous f ∧ ∃C, ∀x y:α, dist (f x) (f y) ≤ C}

local infixr ` →ᵇ `:25 := bounded_continuous_function

namespace bounded_continuous_function
section basics
variables [topological_space α] [metric_space β] [metric_space γ]
variables {f g : α →ᵇ β} {x : α} {C : ℝ}

instance : has_coe_to_fun (α →ᵇ β) :=  ⟨_, subtype.val⟩

lemma bounded_range : bounded (range f) :=
bounded_range_iff.2 f.2.2

/-- If a function is continuous on a compact space, it is automatically bounded,
and therefore gives rise to an element of the type of bounded continuous functions -/
def mk_of_compact [compact_space α] (f : α → β) (hf : continuous f) : α →ᵇ β :=
⟨f, hf, bounded_range_iff.1 $ bounded_of_compact $ compact_range hf⟩

/-- If a function is bounded on a discrete space, it is automatically continuous,
and therefore gives rise to an element of the type of bounded continuous functions -/
def mk_of_discrete [discrete_topology α] (f : α → β) (hf : ∃C, ∀x y, dist (f x) (f y) ≤ C) :
  α →ᵇ β :=
⟨f, continuous_of_discrete_topology, hf⟩

/-- The uniform distance between two bounded continuous functions -/
instance : has_dist (α →ᵇ β) :=
⟨λf g, Inf {C | C ≥ 0 ∧ ∀ x : α, dist (f x) (g x) ≤ C}⟩

lemma dist_eq : dist f g = Inf {C | C ≥ 0 ∧ ∀ x : α, dist (f x) (g x) ≤ C} := rfl

lemma dist_set_exists : ∃ C, C ≥ 0 ∧ ∀ x : α, dist (f x) (g x) ≤ C :=
begin
  refine if h : nonempty α then _ else ⟨0, le_refl _, λ x, h.elim ⟨x⟩⟩,
  cases h with x,
  rcases f.2 with ⟨_, Cf, hCf⟩, /- hCf : ∀ (x y : α), dist (f.val x) (f.val y) ≤ Cf -/
  rcases g.2 with ⟨_, Cg, hCg⟩, /- hCg : ∀ (x y : α), dist (g.val x) (g.val y) ≤ Cg -/
  let C := max 0 (dist (f x) (g x) + (Cf + Cg)),
  exact ⟨C, le_max_left _ _, λ y, calc
    dist (f y) (g y) ≤ dist (f x) (g x) + (dist (f x) (f y) + dist (g x) (g y)) : dist_triangle4_left _ _ _ _
                ... ≤ dist (f x) (g x) + (Cf + Cg) : add_le_add_left (add_le_add (hCf _ _) (hCg _ _)) _
                ... ≤ C : le_max_right _ _⟩
end

/-- The pointwise distance is controlled by the distance between functions, by definition -/
lemma dist_coe_le_dist (x : α) : dist (f x) (g x) ≤ dist f g :=
le_cInf dist_set_exists $ λb hb, hb.2 x

@[ext] lemma ext (H : ∀x, f x = g x) : f = g :=
subtype.eq $ by ext; apply H

/- This lemma will be needed in the proof of the metric space instance, but it will become
useless afterwards as it will be superceded by the general result that the distance is nonnegative
is metric spaces. -/
private lemma dist_nonneg' : 0 ≤ dist f g :=
le_cInf dist_set_exists (λ C, and.left)

/-- The distance between two functions is controlled by the supremum of the pointwise distances -/
lemma dist_le (C0 : (0 : ℝ) ≤ C) : dist f g ≤ C ↔ ∀x:α, dist (f x) (g x) ≤ C :=
⟨λ h x, le_trans (dist_coe_le_dist x) h, λ H, cInf_le ⟨0, λ C, and.left⟩ ⟨C0, H⟩⟩

/-- On an empty space, bounded continuous functions are at distance 0 -/
lemma dist_zero_of_empty (e : ¬ nonempty α) : dist f g = 0 :=
le_antisymm ((dist_le (le_refl _)).2 $ λ x, e.elim ⟨x⟩) dist_nonneg'

/-- The type of bounded continuous functions, with the uniform distance, is a metric space. -/
instance : metric_space (α →ᵇ β) :=
{ dist_self := λ f, le_antisymm ((dist_le (le_refl _)).2 $ λ x, by simp) dist_nonneg',
  eq_of_dist_eq_zero := λ f g hfg, by ext x; exact
    eq_of_dist_eq_zero (le_antisymm (hfg ▸ dist_coe_le_dist _) dist_nonneg),
  dist_comm := λ f g, by simp [dist_eq, dist_comm],
  dist_triangle := λ f g h,
    (dist_le (add_nonneg dist_nonneg' dist_nonneg')).2 $ λ x,
      le_trans (dist_triangle _ _ _) (add_le_add (dist_coe_le_dist _) (dist_coe_le_dist _)) }

def const (b : β) : α →ᵇ β := ⟨λx, b, continuous_const, 0, by simp [le_refl]⟩

/-- If the target space is inhabited, so is the space of bounded continuous functions -/
instance [inhabited β] : inhabited (α →ᵇ β) := ⟨const (default β)⟩

/-- The evaluation map is continuous, as a joint function of `u` and `x` -/
theorem continuous_eval : continuous (λ p : (α →ᵇ β) × α, p.1 p.2) :=
continuous_iff'.2 $ λ ⟨f, x⟩ ε ε0,
/- use the continuity of `f` to find a neighborhood of `x` where it varies at most by ε/2 -/
let ⟨s, sx, Hs⟩ := continuous_iff'.1 f.2.1 x (ε/2) (half_pos ε0) in
/- s : set α, sx : s ∈ 𝓝 x, Hs : ∀ (b : α), b ∈ s → dist (f.val b) (f.val x) < ε / 2 -/
⟨set.prod (ball f (ε/2)) s, prod_mem_nhds_sets (ball_mem_nhds _ (half_pos ε0)) sx,
λ ⟨g, y⟩ ⟨hg, hy⟩, calc dist (g y) (f x)
      ≤ dist (g y) (f y) + dist (f y) (f x) : dist_triangle _ _ _
  ... < ε/2 + ε/2 : add_lt_add (lt_of_le_of_lt (dist_coe_le_dist _) hg) (Hs _ hy)
  ... = ε : add_halves _⟩

/-- In particular, when `x` is fixed, `f → f x` is continuous -/
theorem continuous_evalx {x : α} : continuous (λ f : α →ᵇ β, f x) :=
continuous_eval.comp (continuous_id.prod_mk continuous_const)

/-- When `f` is fixed, `x → f x` is also continuous, by definition -/
theorem continuous_evalf {f : α →ᵇ β} : continuous f := f.2.1

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
    λ x N, le_of_tendsto (by simp)
      (tendsto_dist tendsto_const_nhds (hF x))
      (filter.mem_at_top_sets.2 ⟨N, λn hn, f_bdd x N n N (le_refl N) hn⟩),
  refine ⟨⟨F, _, _⟩, _⟩,
  { /- Check that `F` is continuous -/
    refine continuous_of_uniform_limit_of_continuous (λ ε ε0, _) (λN, (f N).2.1),
    rcases metric.tendsto_at_top.1 b_lim ε ε0 with ⟨N, hN⟩,
    exact ⟨N, λy, calc
      dist (f N y) (F y) ≤ b N : fF_bdd y N
      ... ≤ dist (b N) 0 : begin simp, show b N ≤ abs(b N), from le_abs_self _ end
      ... ≤ ε : le_of_lt (hN N (le_refl N))⟩ },
  { /- Check that `F` is bounded -/
    rcases (f 0).2.2 with ⟨C, hC⟩,
    exact ⟨C + (b 0 + b 0), λ x y, calc
      dist (F x) (F y) ≤ dist (f 0 x) (f 0 y) + (dist (f 0 x) (F x) + dist (f 0 y) (F y)) : dist_triangle4_left _ _ _ _
         ... ≤ C + (b 0 + b 0) : add_le_add (hC x y) (add_le_add (fF_bdd x 0) (fF_bdd y 0))⟩ },
  { /- Check that `F` is close to `f N` in distance terms -/
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (λ _, dist_nonneg) _ b_lim),
    exact λ N, (dist_le (b0 _)).2 (λx, fF_bdd x N) }
end

/-- Composition (in the target) of a bounded continuous function with a Lipschitz map again
gives a bounded continuous function -/
def comp (G : β → γ) {C : nnreal} (H : lipschitz_with C G)
  (f : α →ᵇ β) : α →ᵇ γ :=
⟨λx, G (f x), H.to_continuous.comp f.2.1,
  let ⟨D, hD⟩ := f.2.2 in
  ⟨max C 0 * D, λ x y, calc
    dist (G (f x)) (G (f y)) ≤ C * dist (f x) (f y) : H _ _
    ... ≤ max C 0 * dist (f x) (f y) : mul_le_mul_of_nonneg_right (le_max_left C 0) dist_nonneg
    ... ≤ max C 0 * D : mul_le_mul_of_nonneg_left (hD _ _) (le_max_right C 0)⟩⟩

/-- The composition operator (in the target) with a Lipschitz map is Lipschitz -/
lemma lipschitz_comp {G : β → γ} {C : nnreal} (H : lipschitz_with C G) :
  lipschitz_with C (comp G H : (α →ᵇ β) → α →ᵇ γ) :=
λ f g,
(dist_le (mul_nonneg C.2 dist_nonneg)).2 $ λ x,
calc dist (G (f x)) (G (g x)) ≤ C * dist (f x) (g x) : H _ _
  ... ≤ C * dist f g : mul_le_mul_of_nonneg_left (dist_coe_le_dist _) C.2

/-- The composition operator (in the target) with a Lipschitz map is uniformly continuous -/
lemma uniform_continuous_comp {G : β → γ} {C : nnreal} (H : lipschitz_with C G) :
  uniform_continuous (comp G H : (α →ᵇ β) → α →ᵇ γ) :=
(lipschitz_comp H).to_uniform_continuous

/-- The composition operator (in the target) with a Lipschitz map is continuous -/
lemma continuous_comp {G : β → γ} {C : nnreal} (H : lipschitz_with C G) :
  continuous (comp G H : (α →ᵇ β) → α →ᵇ γ) :=
(lipschitz_comp H).to_continuous

/-- Restriction (in the target) of a bounded continuous function taking values in a subset -/
def cod_restrict (s : set β) (f : α →ᵇ β) (H : ∀x, f x ∈ s) : α →ᵇ s :=
⟨λx, ⟨f x, H x⟩, continuous_subtype_mk _ f.2.1, f.2.2⟩

end basics

section arzela_ascoli
variables [topological_space α] [compact_space α] [metric_space β]
variables {f g : α →ᵇ β} {x : α} {C : ℝ}

/- Arzela-Ascoli theorem asserts that, on a compact space, a set of functions sharing
a common modulus of continuity and taking values in a compact set forms a compact
subset for the topology of uniform convergence. In this section, we prove this theorem
and several useful variations around it. -/

/-- First version, with pointwise equicontinuity and range in a compact space -/
theorem arzela_ascoli₁ [compact_space β]
  (A : set (α →ᵇ β))
  (closed : is_closed A)
  (H : ∀ (x:α) (ε > 0), ∃U ∈ 𝓝 x, ∀ (y z ∈ U) (f : α →ᵇ β),
    f ∈ A → dist (f y) (f z) < ε) :
  compact A :=
begin
  refine compact_of_totally_bounded_is_closed _ closed,
  refine totally_bounded_of_finite_discretization (λ ε ε0, _),
  rcases dense ε0 with ⟨ε₁, ε₁0, εε₁⟩,
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
          ⟨V, VU, openV, xV⟩ := mem_nhds_sets_iff.1 nhdsU in
      ⟨V, xV, openV, λy z hy hz f hf, hU y z (VU hy) (VU hz) f hf⟩,
  choose U hU using this,
  /- For all x, the set hU x is an open set containing x on which the elements of A
  fluctuate by at most ε₂.
  We extract finitely many of these sets that cover the whole space, by compactness -/
  rcases compact_univ.elim_finite_subcover_image
    (λx _, (hU x).2.1) (λx hx, mem_bUnion (mem_univ _) (hU x).1)
    with ⟨tα, _, ⟨_⟩, htα⟩,
  /- tα : set α, htα : univ ⊆ ⋃x ∈ tα, U x -/
  rcases @finite_cover_balls_of_compact β _ _ compact_univ _ ε₂0
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
  obtain ⟨x', x'tα, hx'⟩ : ∃x' ∈ tα, x ∈ U x' := mem_bUnion_iff.1 (htα (mem_univ x)),
  refine calc dist (f x) (g x)
      ≤ dist (f x) (f x') + dist (g x) (g x') + dist (f x') (g x') : dist_triangle4_right _ _ _ _
  ... ≤ ε₂ + ε₂ + ε₁/2 : le_of_lt (add_lt_add (add_lt_add _ _) _)
  ... = ε₁ : by rw [add_halves, add_halves],
  { exact (hU x').2.2 _ _ hx' ((hU x').1) hf },
  { exact (hU x').2.2 _ _ hx' ((hU x').1) hg },
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
  (s : set β) (hs : compact s)
  (A : set (α →ᵇ β))
  (closed : is_closed A)
  (in_s : ∀(f : α →ᵇ β) (x : α), f ∈ A → f x ∈ s)
  (H : ∀(x:α) (ε > 0), ∃U ∈ 𝓝 x, ∀ (y z ∈ U) (f : α →ᵇ β),
    f ∈ A → dist (f y) (f z) < ε) :
  compact A :=
/- This version is deduced from the previous one by restricting to the compact type in the target,
using compactness there and then lifting everything to the original space. -/
begin
  have M : lipschitz_with 1 coe := lipschitz_with.subtype_coe s,
  let F : (α →ᵇ s) → α →ᵇ β := comp coe M,
  refine compact_of_is_closed_subset
    ((_ : compact (F ⁻¹' A)).image (continuous_comp M)) closed (λ f hf, _),
  { haveI : compact_space s := compact_iff_compact_space.1 hs,
    refine arzela_ascoli₁ _ (continuous_iff_is_closed.1 (continuous_comp M) _ closed)
      (λ x ε ε0, bex.imp_right (λ U U_nhds hU y z hy hz f hf, _) (H x ε ε0)),
    calc dist (f y) (f z) = dist (F f y) (F f z) : rfl
                        ... < ε : hU y z hy hz (F f) hf },
  { let g := cod_restrict s f (λx, in_s f x hf),
    rw [show f = F g, by ext; refl] at hf ⊢,
    exact ⟨g, hf, rfl⟩ }
end

/-- Third (main) version, with pointwise equicontinuity and range in a compact subset, but
without closedness. The closure is then compact -/
theorem arzela_ascoli
  (s : set β) (hs : compact s)
  (A : set (α →ᵇ β))
  (in_s : ∀(f : α →ᵇ β) (x : α), f ∈ A → f x ∈ s)
  (H : ∀(x:α) (ε > 0), ∃U ∈ 𝓝 x, ∀ (y z ∈ U) (f : α →ᵇ β),
    f ∈ A → dist (f y) (f z) < ε) :
  compact (closure A) :=
/- This version is deduced from the previous one by checking that the closure of A, in
addition to being closed, still satisfies the properties of compact range and equicontinuity -/
arzela_ascoli₂ s hs (closure A) is_closed_closure
  (λ f x hf, (mem_of_closed' (closed_of_compact _ hs)).2 $ λ ε ε0,
    let ⟨g, gA, dist_fg⟩ := mem_closure_iff'.1 hf ε ε0 in
    ⟨g x, in_s g x gA, lt_of_le_of_lt (dist_coe_le_dist _) dist_fg⟩)
  (λ x ε ε0, show ∃ U ∈ 𝓝 x,
      ∀ y z ∈ U, ∀ (f : α →ᵇ β), f ∈ closure A → dist (f y) (f z) < ε,
    begin
      refine bex.imp_right (λ U U_set hU y z hy hz f hf, _) (H x (ε/2) (half_pos ε0)),
      rcases mem_closure_iff'.1 hf (ε/2/2) (half_pos (half_pos ε0)) with ⟨g, gA, dist_fg⟩,
      replace dist_fg := λ x, lt_of_le_of_lt (dist_coe_le_dist x) dist_fg,
      calc dist (f y) (f z) ≤ dist (f y) (g y) + dist (f z) (g z) + dist (g y) (g z) : dist_triangle4_right _ _ _ _
          ... < ε/2/2 + ε/2/2 + ε/2 :
            add_lt_add (add_lt_add (dist_fg y) (dist_fg z)) (hU y z hy hz g gA)
          ... = ε : by rw [add_halves, add_halves]
    end)

/- To apply the previous theorems, one needs to check the equicontinuity. An important
instance is when the source space is a metric space, and there is a fixed modulus of continuity
for all the functions in the set A -/

lemma equicontinuous_of_continuity_modulus {α : Type u} [metric_space α]
  (b : ℝ → ℝ) (b_lim : tendsto b (𝓝 0) (𝓝 0))
  (A : set (α →ᵇ β))
  (H : ∀(x y:α) (f : α →ᵇ β), f ∈ A → dist (f x) (f y) ≤ b (dist x y))
  (x:α) (ε : ℝ) (ε0 : ε > 0) : ∃U ∈ 𝓝 x, ∀ (y z ∈ U) (f : α →ᵇ β),
    f ∈ A → dist (f y) (f z) < ε :=
begin
  rcases tendsto_nhds_nhds.1 b_lim ε ε0 with ⟨δ, δ0, hδ⟩,
  refine ⟨ball x (δ/2), ball_mem_nhds x (half_pos δ0), λ y z hy hz f hf, _⟩,
  have : dist y z < δ := calc
    dist y z ≤ dist y x + dist z x : dist_triangle_right _ _ _
    ... < δ/2 + δ/2 : add_lt_add hy hz
    ... = δ : add_halves _,
  calc
    dist (f y) (f z) ≤ b (dist y z) : H y z f hf
    ... ≤ abs (b (dist y z)) : le_abs_self _
    ... = dist (b (dist y z)) 0 : by simp [real.dist_eq]
    ... < ε : hδ (by simpa [real.dist_eq] using this),
end

end arzela_ascoli

section normed_group
/- In this section, if β is a normed group, then we show that the space of bounded
continuous functions from α to β inherits a normed group structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

variables [topological_space α] [normed_group β]
variables {f g : α →ᵇ β} {x : α} {C : ℝ}

instance : has_zero (α →ᵇ β) := ⟨const 0⟩

@[simp] lemma coe_zero : (0 : α →ᵇ β) x = 0 := rfl

instance : has_norm (α →ᵇ β) := ⟨λu, dist u 0⟩

lemma norm_def : ∥f∥ = dist f 0 := rfl

lemma norm_coe_le_norm (x : α) : ∥f x∥ ≤ ∥f∥ := calc
  ∥f x∥ = dist (f x) ((0 : α →ᵇ β) x) : by simp [dist_zero_right]
  ... ≤ ∥f∥ : dist_coe_le_dist _

/-- Distance between the images of any two points is at most twice the norm of the function. -/
lemma dist_le_two_norm (x y : α) : dist (f x) (f y) ≤ 2 * ∥f∥ := calc
  dist (f x) (f y) ≤ ∥f x∥ + ∥f y∥ : dist_le_norm_add_norm _ _
               ... ≤ ∥f∥ + ∥f∥     : add_le_add (norm_coe_le_norm x) (norm_coe_le_norm y)
               ... = 2 * ∥f∥      : (two_mul _).symm

/-- The norm of a function is controlled by the supremum of the pointwise norms -/
lemma norm_le (C0 : (0 : ℝ) ≤ C) : ∥f∥ ≤ C ↔ ∀x:α, ∥f x∥ ≤ C :=
by simpa only [coe_zero, dist_zero_right] using @dist_le _ _ _ _ f 0 _ C0

/-- The pointwise sum of two bounded continuous functions is again bounded continuous. -/
instance : has_add (α →ᵇ β) :=
⟨λf g, ⟨λx, f x + g x, f.2.1.add g.2.1,
  let ⟨_, fM, hf⟩ := f.2 in let ⟨_, gM, hg⟩ := g.2 in
  ⟨fM + gM, λ x y, dist_add_add_le_of_le (hf _ _) (hg _ _)⟩⟩⟩

/-- The pointwise opposite of a bounded continuous function is again bounded continuous. -/
instance : has_neg (α →ᵇ β) :=
⟨λf, ⟨λx, -f x, f.2.1.neg, by simpa only [dist_neg_neg] using f.2.2⟩⟩

@[simp] lemma coe_add : (f + g) x = f x + g x := rfl
@[simp] lemma coe_neg : (-f) x = - (f x) := rfl
lemma forall_coe_zero_iff_zero : (∀x, f x = 0) ↔ f = 0 :=
⟨@ext _ _ _ _ f 0, by rintro rfl _; refl⟩

instance : add_comm_group (α →ᵇ β) :=
{ add_assoc    := assume f g h, by ext; simp,
  zero_add     := assume f, by ext; simp,
  add_zero     := assume f, by ext; simp,
  add_left_neg := assume f, by ext; simp,
  add_comm     := assume f g, by ext; simp,
  ..bounded_continuous_function.has_add,
  ..bounded_continuous_function.has_neg,
  ..bounded_continuous_function.has_zero }

@[simp] lemma coe_diff : (f - g) x = f x - g x := rfl

instance : normed_group (α →ᵇ β) :=
normed_group.of_add_dist (λ _, rfl) $ λ f g h,
(dist_le dist_nonneg).2 $ λ x,
le_trans (by rw [dist_eq_norm, dist_eq_norm, coe_add, coe_add,
  add_sub_add_right_eq_sub]) (dist_coe_le_dist x)

lemma abs_diff_coe_le_dist : norm (f x - g x) ≤ dist f g :=
by rw normed_group.dist_eq; exact @norm_coe_le_norm _ _ _ _ (f-g) x

lemma coe_le_coe_add_dist {f g : α →ᵇ ℝ} : f x ≤ g x + dist f g :=
sub_le_iff_le_add'.1 $ (abs_le.1 $ @dist_coe_le_dist _ _ _ _ f g x).2

/-- Constructing a bounded continuous function from a uniformly bounded continuous
function taking values in a normed group. -/
def of_normed_group {α : Type u} {β : Type v} [topological_space α] [normed_group β]
  (f : α  → β) (C : ℝ) (H : ∀x, norm (f x) ≤ C) (Hf : continuous f) : α →ᵇ β :=
⟨λn, f n, ⟨Hf, ⟨C + C, λ m n,
  calc dist (f m) (f n) ≤ dist (f m) 0 + dist (f n) 0 : dist_triangle_right _ _ _
       ... = norm (f m) + norm (f n) : by simp
       ... ≤ C + C : add_le_add (H m) (H n)⟩⟩⟩

/-- Constructing a bounded continuous function from a uniformly bounded
function on a discrete space, taking values in a normed group -/
def of_normed_group_discrete {α : Type u} {β : Type v}
  [topological_space α] [discrete_topology α] [normed_group β]
  (f : α  → β) (C : ℝ) (H : ∀x, norm (f x) ≤ C) : α →ᵇ β :=
of_normed_group f C H continuous_of_discrete_topology

end normed_group
end bounded_continuous_function
