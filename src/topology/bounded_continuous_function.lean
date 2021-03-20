/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth
-/
import analysis.normed_space.linear_isometry
import topology.algebra.continuous_functions
import tactic.equiv_rw

/-!
# Bounded continuous functions

The type of bounded continuous functions taking values in a metric space, with
the uniform distance.

-/

noncomputable theory
open_locale topological_space classical nnreal

open set filter metric

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

/-- The type of bounded continuous functions from a topological space to a metric space -/
structure bounded_continuous_function
  (α : Type u) (β : Type v) [topological_space α] [metric_space β] extends continuous_map α β :
  Type (max u v) :=
(bounded' : ∃C, ∀x y:α, dist (to_fun x) (to_fun y) ≤ C)

localized "infixr ` →ᵇ `:25 := bounded_continuous_function" in bounded_continuous_function

namespace bounded_continuous_function
section basics
variables [topological_space α] [metric_space β] [metric_space γ]
variables {f g : α →ᵇ β} {x : α} {C : ℝ}

instance : has_coe_to_fun (α →ᵇ β) :=  ⟨_, λ f, f.to_fun⟩

protected lemma bounded (f : α →ᵇ β) : ∃C, ∀ x y : α, dist (f x) (f y) ≤ C := f.bounded'
@[continuity]
protected lemma continuous (f : α →ᵇ β) : continuous f := f.to_continuous_map.continuous

@[ext] lemma ext (H : ∀x, f x = g x) : f = g :=
by { cases f, cases g, congr, ext, exact H x, }

lemma ext_iff : f = g ↔ ∀ x, f x = g x :=
⟨λ h, λ x, h ▸ rfl, ext⟩

lemma bounded_range : bounded (range f) :=
bounded_range_iff.2 f.bounded

/-- A continuous function with an explicit bound is a bounded continuous function. -/
def mk_of_bound (f : C(α, β)) (C : ℝ) (h : ∀ x y : α, dist (f x) (f y) ≤ C) : α →ᵇ β :=
⟨f, ⟨C, h⟩⟩

@[simp] lemma mk_of_bound_coe {f} {C} {h} : (mk_of_bound f C h : α → β) = (f : α → β) :=
rfl

/-- A continuous function on a compact space is automatically a bounded continuous function. -/
def mk_of_compact [compact_space α] (f : C(α, β)) : α →ᵇ β :=
⟨f, bounded_range_iff.1 $ bounded_of_compact $ compact_range f.continuous⟩

@[simp] lemma mk_of_compact_apply [compact_space α] (f : C(α, β)) (a : α) :
  mk_of_compact f a = f a :=
rfl

/-- If a function is bounded on a discrete space, it is automatically continuous,
and therefore gives rise to an element of the type of bounded continuous functions -/
def mk_of_discrete [discrete_topology α] (f : α → β)
  (C : ℝ) (h :  ∀ x y : α, dist (f x) (f y) ≤ C) : α →ᵇ β :=
⟨⟨f, continuous_of_discrete_topology⟩, ⟨C, h⟩⟩

@[simp] lemma mk_of_discrete_apply
  [discrete_topology α] (f : α → β) (C) (h) (a : α) :
  mk_of_discrete f C h a = f a :=
rfl

section
variables (α β)
/--
The map forgetting that a bounded continuous function is bounded.
-/
def forget_boundedness : (α →ᵇ β) → C(α, β) :=
λ f, f.1

@[simp] lemma forget_boundedness_coe (f : α →ᵇ β) : (forget_boundedness α β f : α → β) = f :=
rfl

/--
When `α` is compact, the bounded continuous maps `α →ᵇ 𝕜` are
equivalent to `C(α, 𝕜)`.
-/
@[simps]
def equiv_continuous_map_of_compact [compact_space α] : (α →ᵇ β) ≃ C(α, β) :=
⟨forget_boundedness α β, mk_of_compact, λ f, by { ext, refl, }, λ f, by { ext, refl, }⟩

end

/-- The uniform distance between two bounded continuous functions -/
instance : has_dist (α →ᵇ β) :=
⟨λf g, Inf {C | 0 ≤ C ∧ ∀ x : α, dist (f x) (g x) ≤ C}⟩

lemma dist_eq : dist f g = Inf {C | 0 ≤ C ∧ ∀ x : α, dist (f x) (g x) ≤ C} := rfl

lemma dist_set_exists : ∃ C, 0 ≤ C ∧ ∀ x : α, dist (f x) (g x) ≤ C :=
begin
  refine if h : nonempty α then _ else ⟨0, le_refl _, λ x, h.elim ⟨x⟩⟩,
  cases h with x,
  rcases f.bounded with ⟨Cf, hCf : ∀ x y, dist (f x) (f y) ≤ Cf⟩,
  rcases g.bounded with ⟨Cg, hCg : ∀ x y, dist (g x) (g y) ≤ Cg⟩,
  let C := max 0 (dist (f x) (g x) + (Cf + Cg)),
  refine ⟨C, le_max_left _ _, λ y, _⟩,
  calc dist (f y) (g y) ≤ dist (f x) (g x) + (dist (f x) (f y) + dist (g x) (g y)) :
    dist_triangle4_left _ _ _ _
                    ... ≤ dist (f x) (g x) + (Cf + Cg) : by mono*
                    ... ≤ C : le_max_right _ _
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

lemma dist_le_of_nonempty [nonempty α] :
  dist f g ≤ C ↔ ∀ x, dist (f x) (g x) ≤ C :=
⟨λ h x, le_trans (dist_coe_le_dist x) h,
 λ w, (dist_le (le_trans dist_nonneg (w (nonempty.some ‹_›)))).mpr w⟩

lemma dist_lt_of_compact_aux [nonempty α] [compact_space α]
  (w : ∀x:α, dist (f x) (g x) < C) : dist f g < C :=
begin
  have c : continuous (λ x, dist (f x) (g x)), { continuity, },
  obtain ⟨x, -, le⟩ :=
    is_compact.exists_forall_ge compact_univ set.univ_nonempty (continuous.continuous_on c),
  exact lt_of_le_of_lt (dist_le_of_nonempty.mpr (λ y, le y trivial)) (w x),
end

lemma dist_lt_of_compact [compact_space α] (C0 : (0 : ℝ) < C) :
  dist f g < C ↔ ∀x:α, dist (f x) (g x) < C :=
begin
  fsplit,
  { intros w x,
    exact lt_of_le_of_lt (dist_coe_le_dist x) w, },
  { by_cases h : nonempty α,
    { resetI,
      exact dist_lt_of_compact_aux, },
    { rintro -,
      convert C0,
      apply le_antisymm _ dist_nonneg',
      rw [dist_eq],
      exact cInf_le ⟨0, λ C, and.left⟩ ⟨le_refl _, λ x, false.elim (h (nonempty.intro x))⟩, }, },
end

lemma dist_lt_of_nonempty_compact [nonempty α] [compact_space α] :
  dist f g < C ↔ ∀x:α, dist (f x) (g x) < C :=
⟨λ w x, lt_of_le_of_lt (dist_coe_le_dist x) w, dist_lt_of_compact_aux⟩

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

instance [compact_space α] : metric_space C(α,β) :=
metric_space.induced
  (equiv_continuous_map_of_compact α β).symm
  (equiv_continuous_map_of_compact α β).symm.injective
  (by apply_instance)

variables (α β)
/--
When `α` is compact, and `β` is a metric space, the bounded continuous maps `α →ᵇ β` are
isometric to `C(α, β)`.
-/
@[simps]
def isometric_continuous_map_of_compact [compact_space α] :
  (α →ᵇ β) ≃ᵢ C(α, β) :=
{ isometry_to_fun := λ x y, rfl,
  to_equiv := equiv_continuous_map_of_compact α β }

variable {β}

/-- Constant as a continuous bounded function. -/
def const (b : β) : α →ᵇ β := ⟨continuous_map.const b, 0, by simp [le_refl]⟩

variable {α}

@[simp] lemma coe_const (b : β) : ⇑(const α b) = function.const α b := rfl
lemma const_apply (a : α) (b : β) : (const α b : α → β) a = b := rfl

/-- If the target space is inhabited, so is the space of bounded continuous functions -/
instance [inhabited β] : inhabited (α →ᵇ β) := ⟨const α (default β)⟩

/-- The evaluation map is continuous, as a joint function of `u` and `x` -/
theorem continuous_eval : continuous (λ p : (α →ᵇ β) × α, p.1 p.2) :=
continuous_iff'.2 $ λ ⟨f, x⟩ ε ε0,
/- use the continuity of `f` to find a neighborhood of `x` where it varies at most by ε/2 -/
have Hs : _ := continuous_iff'.1 f.continuous x (ε/2) (half_pos ε0),
mem_sets_of_superset (prod_mem_nhds_sets (ball_mem_nhds _ (half_pos ε0)) Hs) $
λ ⟨g, y⟩ ⟨hg, hy⟩, calc dist (g y) (f x)
      ≤ dist (g y) (f y) + dist (f y) (f x) : dist_triangle _ _ _
  ... < ε/2 + ε/2 : add_lt_add (lt_of_le_of_lt (dist_coe_le_dist _) hg) hy
  ... = ε : add_halves _

/-- In particular, when `x` is fixed, `f → f x` is continuous -/
theorem continuous_evalx {x : α} : continuous (λ f : α →ᵇ β, f x) :=
continuous_eval.comp (continuous_id.prod_mk continuous_const)

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
    exact this.continuous (λN, (f N).continuous) },
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
⟨⟨s.cod_restrict f H, continuous_subtype_mk _ f.continuous⟩, f.bounded⟩

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
  is_compact A :=
begin
  refine compact_of_totally_bounded_is_closed _ closed,
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
  (s : set β) (hs : is_compact s)
  (A : set (α →ᵇ β))
  (closed : is_closed A)
  (in_s : ∀(f : α →ᵇ β) (x : α), f ∈ A → f x ∈ s)
  (H : ∀(x:α) (ε > 0), ∃U ∈ 𝓝 x, ∀ (y z ∈ U) (f : α →ᵇ β),
    f ∈ A → dist (f y) (f z) < ε) :
  is_compact A :=
/- This version is deduced from the previous one by restricting to the compact type in the target,
using compactness there and then lifting everything to the original space. -/
begin
  have M : lipschitz_with 1 coe := lipschitz_with.subtype_coe s,
  let F : (α →ᵇ s) → α →ᵇ β := comp coe M,
  refine compact_of_is_closed_subset
    ((_ : is_compact (F ⁻¹' A)).image (continuous_comp M)) closed (λ f hf, _),
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
  (s : set β) (hs : is_compact s)
  (A : set (α →ᵇ β))
  (in_s : ∀(f : α →ᵇ β) (x : α), f ∈ A → f x ∈ s)
  (H : ∀(x:α) (ε > 0), ∃U ∈ 𝓝 x, ∀ (y z ∈ U) (f : α →ᵇ β),
    f ∈ A → dist (f y) (f z) < ε) :
  is_compact (closure A) :=
/- This version is deduced from the previous one by checking that the closure of A, in
addition to being closed, still satisfies the properties of compact range and equicontinuity -/
arzela_ascoli₂ s hs (closure A) is_closed_closure
  (λ f x hf, (mem_of_closed' hs.is_closed).2 $ λ ε ε0,
    let ⟨g, gA, dist_fg⟩ := metric.mem_closure_iff.1 hf ε ε0 in
    ⟨g x, in_s g x gA, lt_of_le_of_lt (dist_coe_le_dist _) dist_fg⟩)
  (λ x ε ε0, show ∃ U ∈ 𝓝 x,
      ∀ y z ∈ U, ∀ (f : α →ᵇ β), f ∈ closure A → dist (f y) (f z) < ε,
    begin
      refine bex.imp_right (λ U U_set hU y z hy hz f hf, _) (H x (ε/2) (half_pos ε0)),
      rcases metric.mem_closure_iff.1 hf (ε/2/2) (half_pos (half_pos ε0)) with ⟨g, gA, dist_fg⟩,
      replace dist_fg := λ x, lt_of_le_of_lt (dist_coe_le_dist x) dist_fg,
      calc dist (f y) (f z) ≤ dist (f y) (g y) + dist (f z) (g z) + dist (g y) (g z) :
        dist_triangle4_right _ _ _ _
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
  (x:α) (ε : ℝ) (ε0 : 0 < ε) : ∃U ∈ 𝓝 x, ∀ (y z ∈ U) (f : α →ᵇ β),
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
variables (f g : α →ᵇ β) {x : α} {C : ℝ}

instance : has_zero (α →ᵇ β) := ⟨const α 0⟩

@[simp] lemma coe_zero : ((0 : α →ᵇ β) : α → β) = 0 := rfl

instance : has_norm (α →ᵇ β) := ⟨λu, dist u 0⟩

lemma norm_def : ∥f∥ = dist f 0 := rfl

/-- The norm of a bounded continuous function is the supremum of `∥f x∥`.
We use `Inf` to ensure that the definition works if `α` has no elements. -/
lemma norm_eq (f : α →ᵇ β) :
  ∥f∥ = Inf {C : ℝ | 0 ≤ C ∧ ∀ (x : α), ∥f x∥ ≤ C} :=
by simp [norm_def, bounded_continuous_function.dist_eq]

lemma norm_coe_le_norm (x : α) : ∥f x∥ ≤ ∥f∥ := calc
  ∥f x∥ = dist (f x) ((0 : α →ᵇ β) x) : by simp [dist_zero_right]
  ... ≤ ∥f∥ : dist_coe_le_dist _

lemma dist_le_two_norm' {f : γ → β} {C : ℝ} (hC : ∀ x, ∥f x∥ ≤ C) (x y : γ) :
  dist (f x) (f y) ≤ 2 * C :=
calc dist (f x) (f y) ≤ ∥f x∥ + ∥f y∥ : dist_le_norm_add_norm _ _
                  ... ≤ C + C         : add_le_add (hC x) (hC y)
                  ... = 2 * C         : (two_mul _).symm

/-- Distance between the images of any two points is at most twice the norm of the function. -/
lemma dist_le_two_norm (x y : α) : dist (f x) (f y) ≤ 2 * ∥f∥ :=
dist_le_two_norm' f.norm_coe_le_norm x y

variable {f}

/-- The norm of a function is controlled by the supremum of the pointwise norms -/
lemma norm_le (C0 : (0 : ℝ) ≤ C) : ∥f∥ ≤ C ↔ ∀x:α, ∥f x∥ ≤ C :=
by simpa using @dist_le _ _ _ _ f 0 _ C0

lemma norm_le_of_nonempty [nonempty α]
  {f : α →ᵇ β} {M : ℝ} : ∥f∥ ≤ M ↔ ∀ x, ∥f x∥ ≤ M :=
⟨λ w x, le_trans (norm_coe_le_norm f x) w,
  λ w, (norm_le (le_trans (norm_nonneg _) (w (nonempty.some ‹_›)))).mpr w⟩

lemma norm_lt_of_compact [nonempty α] [compact_space α]
  {f : α →ᵇ β} {M : ℝ} : ∥f∥ < M ↔ ∀ x, ∥f x∥ < M :=
begin
  fsplit,
  { intros w x,
    exact lt_of_le_of_lt (norm_coe_le_norm f x) w, },
  { intro w,
    have c : continuous (λ x, ∥f x∥), { continuity, },
    obtain ⟨x, -, le⟩ :=
      is_compact.exists_forall_ge compact_univ set.univ_nonempty (continuous.continuous_on c),
    exact lt_of_le_of_lt (norm_le_of_nonempty.mpr (λ y, le y trivial)) (w x), },
end

variable (f)

/-- Norm of `const α b` is less than or equal to `∥b∥`. If `α` is nonempty,
then it is equal to `∥b∥`. -/
lemma norm_const_le (b : β) : ∥const α b∥ ≤ ∥b∥ :=
(norm_le (norm_nonneg b)).2 $ λ x, le_refl _

@[simp] lemma norm_const_eq [h : nonempty α] (b : β) : ∥const α b∥ = ∥b∥ :=
le_antisymm (norm_const_le b) $ h.elim $ λ x, (const α b).norm_coe_le_norm x

/-- Constructing a bounded continuous function from a uniformly bounded continuous
function taking values in a normed group. -/
def of_normed_group {α : Type u} {β : Type v} [topological_space α] [normed_group β]
  (f : α  → β) (Hf : continuous f) (C : ℝ) (H : ∀x, ∥f x∥ ≤ C) : α →ᵇ β :=
⟨⟨λn, f n, Hf⟩, ⟨_, dist_le_two_norm' H⟩⟩

lemma norm_of_normed_group_le {f : α → β} (hfc : continuous f) {C : ℝ} (hC : 0 ≤ C)
  (hfC : ∀ x, ∥f x∥ ≤ C) : ∥of_normed_group f hfc C hfC∥ ≤ C :=
(norm_le hC).2 hfC

/-- Constructing a bounded continuous function from a uniformly bounded
function on a discrete space, taking values in a normed group -/
def of_normed_group_discrete {α : Type u} {β : Type v}
  [topological_space α] [discrete_topology α] [normed_group β]
  (f : α  → β) (C : ℝ) (H : ∀x, norm (f x) ≤ C) : α →ᵇ β :=
of_normed_group f continuous_of_discrete_topology C H

/-- The pointwise sum of two bounded continuous functions is again bounded continuous. -/
instance : has_add (α →ᵇ β) :=
⟨λf g, of_normed_group (f + g) (f.continuous.add g.continuous) (∥f∥ + ∥g∥) $ λ x,
  le_trans (norm_add_le _ _) (add_le_add (f.norm_coe_le_norm x) (g.norm_coe_le_norm x))⟩

/-- The pointwise opposite of a bounded continuous function is again bounded continuous. -/
instance : has_neg (α →ᵇ β) :=
⟨λf, of_normed_group (-f) f.continuous.neg ∥f∥ $ λ x,
  trans_rel_right _ (norm_neg _) (f.norm_coe_le_norm x)⟩

/-- The pointwise difference of two bounded continuous functions is again bounded continuous. -/
instance : has_sub (α →ᵇ β) :=
⟨λf g, of_normed_group (f - g) (f.continuous.sub g.continuous) (∥f∥ + ∥g∥) $ λ x,
  by { simp only [sub_eq_add_neg],
       exact le_trans (norm_add_le _ _) (add_le_add (f.norm_coe_le_norm x) $
         trans_rel_right _ (norm_neg _) (g.norm_coe_le_norm x)) }⟩

@[simp] lemma coe_add : ⇑(f + g) = λ x, f x + g x := rfl
lemma add_apply : (f + g) x = f x + g x := rfl
@[simp] lemma coe_neg : ⇑(-f) = λ x, - f x := rfl
lemma neg_apply : (-f) x = -f x := rfl

lemma forall_coe_zero_iff_zero : (∀x, f x = 0) ↔ f = 0 :=
(@ext_iff _ _ _ _ f 0).symm

instance : add_comm_group (α →ᵇ β) :=
{ add_assoc      := assume f g h, by ext; simp [add_assoc],
  zero_add       := assume f, by ext; simp,
  add_zero       := assume f, by ext; simp,
  add_left_neg   := assume f, by ext; simp,
  add_comm       := assume f g, by ext; simp [add_comm],
  sub_eq_add_neg := assume f g, by { ext, apply sub_eq_add_neg },
  ..bounded_continuous_function.has_add,
  ..bounded_continuous_function.has_neg,
  ..bounded_continuous_function.has_sub,
  ..bounded_continuous_function.has_zero }

@[simp] lemma coe_sub : ⇑(f - g) = λ x, f x - g x := rfl
lemma sub_apply : (f - g) x = f x - g x := rfl

/-- Coercion of a `normed_group_hom` is an `add_monoid_hom`. Similar to `add_monoid_hom.coe_fn` -/
@[simps]
def coe_fn_add_hom : (α →ᵇ β) →+ (α → β) :=
{ to_fun := coe_fn, map_zero' := coe_zero, map_add' := coe_add}

open_locale big_operators
@[simp] lemma coe_sum {ι : Type*} (s : finset ι) (f : ι → (α →ᵇ β)) :
  ⇑(∑ i in s, f i) = (∑ i in s, (f i : α → β)) :=
(@coe_fn_add_hom α β _ _).map_sum f s

lemma sum_apply {ι : Type*} (s : finset ι) (f : ι → (α →ᵇ β)) (a : α) :
  (∑ i in s, f i) a = (∑ i in s, f i a) :=
by simp

instance : normed_group (α →ᵇ β) :=
{ dist_eq := λ f g, by simp only [norm_eq, dist_eq, dist_eq_norm, sub_apply] }

lemma abs_diff_coe_le_dist : ∥f x - g x∥ ≤ dist f g :=
by { rw dist_eq_norm, exact (f - g).norm_coe_le_norm x }

lemma coe_le_coe_add_dist {f g : α →ᵇ ℝ} : f x ≤ g x + dist f g :=
sub_le_iff_le_add'.1 $ (abs_le.1 $ @dist_coe_le_dist _ _ _ _ f g x).2

variables (α β)

/--
The additive map forgetting that a bounded continuous function is bounded.
-/
@[simps]
def forget_boundedness_add_hom : (α →ᵇ β) →+ C(α, β) :=
{ to_fun := forget_boundedness α β,
  map_zero' := by { ext, simp, },
  map_add' := by { intros, ext, simp, }, }

section compact_space
variables [compact_space α]

section

/--
When `α` is compact, the bounded continuous maps `α →ᵇ 𝕜` are
additively equivalent to `C(α, 𝕜)`.
-/
@[simps]
def add_equiv_continuous_map_of_compact : (α →ᵇ β) ≃+ C(α, β) :=
{ ..forget_boundedness_add_hom α β,
  ..equiv_continuous_map_of_compact α β, }

@[simp]
lemma add_equiv_continuous_map_of_compact_to_equiv :
  (add_equiv_continuous_map_of_compact α β).to_equiv = equiv_continuous_map_of_compact α β :=
rfl

end

-- TODO at some point we will need lemmas characterising this norm!
-- At the moment the only way to reason about it is to transfer `f : C(α,β)` back to `α →ᵇ β`.
instance : has_norm C(α,β) :=
{ norm := λ x, dist x 0 }

instance : normed_group C(α,β) :=
{ dist_eq := λ x y,
  begin
    change dist x y = dist (x-y) 0,
     -- it would be nice if `equiv_rw` could rewrite in multiple places at once
    equiv_rw (equiv_continuous_map_of_compact α β).symm at x,
    equiv_rw (equiv_continuous_map_of_compact α β).symm at y,
    have p : dist x y = dist (x-y) 0, { rw dist_eq_norm, rw dist_zero_right, },
    convert p,
    exact ((add_equiv_continuous_map_of_compact α β).map_sub _ _).symm,
  end, }

end compact_space

end normed_group

section normed_space
/-!
### Normed space structure

In this section, if `β` is a normed space, then we show that the space of bounded
continuous functions from `α` to `β` inherits a normed space structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

variables {𝕜 : Type*} [normed_field 𝕜]
variables [topological_space α] [normed_group β] [normed_space 𝕜 β]
variables {f g : α →ᵇ β} {x : α} {C : ℝ}

instance : has_scalar 𝕜 (α →ᵇ β) :=
⟨λ c f, of_normed_group (c • f) (continuous_const.smul f.continuous) (∥c∥ * ∥f∥) $ λ x,
  trans_rel_right _ (norm_smul _ _)
    (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _))⟩

@[simp] lemma coe_smul (c : 𝕜) (f : α →ᵇ β) : ⇑(c • f) = λ x, c • (f x) := rfl
lemma smul_apply (c : 𝕜) (f : α →ᵇ β) (x : α) : (c • f) x = c • f x := rfl

instance : semimodule 𝕜 (α →ᵇ β) :=
semimodule.of_core $
{ smul     := (•),
  smul_add := λ c f g, ext $ λ x, smul_add c (f x) (g x),
  add_smul := λ c₁ c₂ f, ext $ λ x, add_smul c₁ c₂ (f x),
  mul_smul := λ c₁ c₂ f, ext $ λ x, mul_smul c₁ c₂ (f x),
  one_smul := λ f, ext $ λ x, one_smul 𝕜 (f x) }

instance : normed_space 𝕜 (α →ᵇ β) := ⟨λ c f, norm_of_normed_group_le _
  (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _⟩

instance [compact_space α] : normed_space 𝕜 C(α,β) :=
{ norm_smul_le := λ c f,
  begin
    equiv_rw (equiv_continuous_map_of_compact α β).symm at f,
    exact le_of_eq (norm_smul c f),
  end }

end normed_space

section normed_ring
/-!
### Normed ring structure

In this section, if `R` is a normed ring, then we show that the space of bounded
continuous functions from `α` to `R` inherits a normed ring structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

variables [topological_space α] {R : Type*} [normed_ring R]

instance : ring (α →ᵇ R) :=
{ one := const α 1,
  mul := λ f g, of_normed_group (f * g) (f.continuous.mul g.continuous) (∥f∥ * ∥g∥) $ λ x,
    le_trans (normed_ring.norm_mul (f x) (g x)) $
      mul_le_mul (f.norm_coe_le_norm x) (g.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _),
  one_mul := λ f, ext $ λ x, one_mul (f x),
  mul_one := λ f, ext $ λ x, mul_one (f x),
  mul_assoc := λ f₁ f₂ f₃, ext $ λ x, mul_assoc _ _ _,
  left_distrib := λ f₁ f₂ f₃, ext $ λ x, left_distrib _ _ _,
  right_distrib := λ f₁ f₂ f₃, ext $ λ x, right_distrib _ _ _,
  .. bounded_continuous_function.add_comm_group }

instance : normed_ring (α →ᵇ R) :=
{ norm_mul := λ f g, norm_of_normed_group_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _,
  .. bounded_continuous_function.normed_group }

instance [compact_space α] : normed_ring C(α,R) :=
{ norm_mul := λ f g,
  begin
    equiv_rw (equiv_continuous_map_of_compact α R).symm at f,
    equiv_rw (equiv_continuous_map_of_compact α R).symm at g,
    exact norm_mul_le f g,
  end,
  ..(infer_instance : normed_group C(α,R)) }

end normed_ring

section normed_comm_ring
/-!
### Normed commutative ring structure

In this section, if `R` is a normed commutative ring, then we show that the space of bounded
continuous functions from `α` to `R` inherits a normed commutative ring structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

variables [topological_space α] {R : Type*} [normed_comm_ring R]

instance : comm_ring (α →ᵇ R) :=
{ mul_comm := λ f₁ f₂, ext $ λ x, mul_comm _ _,
  .. bounded_continuous_function.ring }

instance : normed_comm_ring (α →ᵇ R) :=
{ .. bounded_continuous_function.comm_ring, .. bounded_continuous_function.normed_group }

end normed_comm_ring

section normed_algebra
/-!
### Normed algebra structure

In this section, if `γ` is a normed algebra, then we show that the space of bounded
continuous functions from `α` to `γ` inherits a normed algebra structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

variables {𝕜 : Type*} [normed_field 𝕜]
variables [topological_space α] [normed_group β] [normed_space 𝕜 β]
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
  ..bounded_continuous_function.semimodule,
  ..bounded_continuous_function.ring }

@[simp] lemma algebra_map_apply (k : 𝕜) (a : α) :
  algebra_map 𝕜 (α →ᵇ γ) k a = k • 1 :=
by { rw algebra.algebra_map_eq_smul_one, refl, }

instance [nonempty α] : normed_algebra 𝕜 (α →ᵇ γ) :=
{ norm_algebra_map_eq := λ c, begin
    calc ∥ (algebra_map 𝕜 (α →ᵇ γ)).to_fun c∥ = ∥(algebra_map 𝕜 γ) c∥ : _
    ... = ∥c∥ : norm_algebra_map_eq _ _,
    apply norm_const_eq ((algebra_map 𝕜 γ) c), assumption,
  end,
  ..bounded_continuous_function.algebra }

instance [nonempty α] [compact_space α] : normed_algebra 𝕜 C(α, γ) :=
{ norm_algebra_map_eq := λ c, (norm_algebra_map_eq (α →ᵇ γ) c : _), }

/-!
### Structure as normed module over scalar functions

If `β` is a normed `𝕜`-space, then we show that the space of bounded continuous
functions from `α` to `β` is naturally a module over the algebra of bounded continuous
functions from `α` to `𝕜`. -/

instance has_scalar' : has_scalar (α →ᵇ 𝕜) (α →ᵇ β) :=
⟨λ (f : α →ᵇ 𝕜) (g : α →ᵇ β), of_normed_group (λ x, (f x) • (g x))
(f.continuous.smul g.continuous) (∥f∥ * ∥g∥) (λ x, calc
  ∥f x • g x∥ ≤ ∥f x∥ * ∥g x∥ : normed_space.norm_smul_le _ _
  ... ≤ ∥f∥ * ∥g∥ : mul_le_mul (f.norm_coe_le_norm _) (g.norm_coe_le_norm _) (norm_nonneg _)
    (norm_nonneg _)) ⟩

instance module' : module (α →ᵇ 𝕜) (α →ᵇ β) :=
semimodule.of_core $
{ smul     := (•),
  smul_add := λ c f₁ f₂, ext $ λ x, smul_add _ _ _,
  add_smul := λ c₁ c₂ f, ext $ λ x, add_smul _ _ _,
  mul_smul := λ c₁ c₂ f, ext $ λ x, mul_smul _ _ _,
  one_smul := λ f, ext $ λ x, one_smul 𝕜 (f x) }

lemma norm_smul_le (f : α →ᵇ 𝕜) (g : α →ᵇ β) : ∥f • g∥ ≤ ∥f∥ * ∥g∥ :=
norm_of_normed_group_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _

/- TODO: When `normed_module` has been added to `normed_space.basic`, the above facts
show that the space of bounded continuous functions from `α` to `β` is naturally a normed
module over the algebra of bounded continuous functions from `α` to `𝕜`. -/

variables (α 𝕜)

/--
When `α` is compact and `𝕜` is a normed field,
the `𝕜`-algebra of bounded continuous maps `α →ᵇ 𝕜` is
`𝕜`-linearly isometric to `C(α, 𝕜)`.
-/
def linear_isometry_continuous_map_of_compact [compact_space α] :
  (α →ᵇ 𝕜) ≃ₗᵢ[𝕜] C(α, 𝕜) :=
{ map_smul' := λ c f, by { ext, simp, },
  norm_map' := λ f, rfl,
  ..add_equiv_continuous_map_of_compact α 𝕜 }

@[simp]
lemma isometric_continuous_map_of_compact_to_isometric [compact_space α] :
  (linear_isometry_continuous_map_of_compact α 𝕜).to_isometric =
    isometric_continuous_map_of_compact α 𝕜 :=
rfl

@[simp]
lemma linear_isometry_continuous_map_of_compact_to_add_equiv [compact_space α] :
  (linear_isometry_continuous_map_of_compact α 𝕜).to_linear_equiv.to_add_equiv =
    add_equiv_continuous_map_of_compact α 𝕜 :=
rfl

@[simp]
lemma linear_isometry_continuous_map_of_compact_to_equiv [compact_space α] :
  (linear_isometry_continuous_map_of_compact α 𝕜).to_linear_equiv.to_equiv =
    equiv_continuous_map_of_compact α 𝕜 :=
rfl

end normed_algebra

end bounded_continuous_function
