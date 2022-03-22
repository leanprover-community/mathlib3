/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import topology.continuous_function.bounded

/-!
# Continuous functions vanishing at infinity

The type of continuous functions vanishing at infinity. When the domain is compact
`C(α, β) ≃ (α →C₀ β)` via the identity map. When the codomain is a metric space, every continuous
map which vanishes at infinity is a bounded continuous function. When the domain is a locally
compact space, this type has nice properties.
-/
universes u v w

variables {F : Type*} {α : Type u} {β : Type v} {γ : Type w} [topological_space α]

open_locale bounded_continuous_function topological_space
open filter metric

section preliminaries
--- these results need to be moved to appropriate places

@[simp]
lemma filter.cocompact_eq_bot [compact_space α] : cocompact α = ⊥ :=
has_basis_cocompact.eq_bot_iff.mpr ⟨set.univ, compact_univ, set.compl_univ⟩

end preliminaries

/-- `α →C₀ β)` is the type of continuous functions `α → β` which vanish at infinity from a
topological space to a metric space with a zero element.

When possible, instead of parametrizing results over `(f : α →C₀ β)`,
you should parametrize over `(F : Type*) [zero_at_infty_continuous_map_class F α β] (f : F)`.

When you extend this structure, make sure to extend `zero_at_infty_continuous_map_class`. -/
structure zero_at_infty_continuous_map (α : Type u) (β : Type v)
  [topological_space α] [has_zero β] [topological_space β] extends continuous_map α β :
  Type (max u v) :=
(zero_at_infty' : tendsto to_fun (cocompact α) (𝓝 0))

localized "notation  α ` →C₀ ` β := zero_at_infty_continuous_map α β" in zero_at_infty

/-- `zero_at_infty_continuous_map_class F α β` states that `F` is a type of continuous maps which
vanish at infinity.

You should also extend this typeclass when you extend `zero_at_infty_continuous_map`. -/
class zero_at_infty_continuous_map_class (F α β : Type*) [topological_space α] [has_zero β]
  [topological_space β] extends continuous_map_class F α β :=
(zero_at_infty (f : F) : tendsto f (cocompact α) (𝓝 0))

export zero_at_infty_continuous_map_class (zero_at_infty)

namespace zero_at_infty_continuous_map

section basics

variables [topological_space β] [has_zero β] [zero_at_infty_continuous_map_class F α β]

instance : zero_at_infty_continuous_map_class (α →C₀ β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_continuous := λ f, f.continuous_to_fun,
  zero_at_infty := λ f, f.zero_at_infty' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (α →C₀ β) (λ _, α → β) := fun_like.has_coe_to_fun

instance : has_coe_t F (α →C₀ β) :=
⟨λ f, { to_fun := f, continuous_to_fun := map_continuous f, zero_at_infty' := zero_at_infty f }⟩

@[simp] lemma coe_to_continuous_fun (f : α →C₀ β) : (f.to_continuous_map : α → β) = f := rfl


@[ext] lemma ext {f g : α →C₀ β} (h : ∀ x, f x = g x) : f = g := fun_like.ext _ _ h

/-- Copy of a `zero_at_infinity_continuous_map` with a new `to_fun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : α →C₀ β) (f' : α → β) (h : f' = f) : α →C₀ β :=
{ to_fun := f',
  continuous_to_fun := by { rw h, exact f.continuous_to_fun },
  zero_at_infty' := by { simp_rw h, exact f.zero_at_infty' } }

lemma eq_of_empty [is_empty α] (f g : α →C₀ β) : f = g :=
ext $ is_empty.elim ‹_›

/-- A continuous function on a compact space is automatically a continuous function vanishing at
infitnity. -/
@[simps]
def continuous_map.lift_zero_at_infty [compact_space α] : C(α, β) ≃ (α →C₀ β) :=
{ to_fun := λ f, { to_fun := f, continuous_to_fun := f.continuous, zero_at_infty' := by simp },
  inv_fun := λ f, f,
  left_inv := λ f, by { ext, refl },
  right_inv := λ f, by { ext, refl } }

/-- A continuous function on a compact space is automatically a continuous function vanishing at
infitnity. This is not an instance to avoid type class loops. -/
def zero_at_infty_continuous_map_class.of_compact {G : Type*} [continuous_map_class G α β]
  [compact_space α] : zero_at_infty_continuous_map_class G α β :=
{ coe := λ g, g,
  coe_injective' := λ f g h, fun_like.coe_fn_eq.mp h,
  map_continuous := map_continuous,
  zero_at_infty := by simp }

end basics

section algebraic_structure

variables [topological_space β] (x : α)

instance [has_zero β] : has_zero (α →C₀ β) := ⟨⟨0, tendsto_const_nhds⟩⟩

instance [has_zero β] : inhabited (α →C₀ β) := ⟨0⟩

@[simp] lemma coe_zero [has_zero β] : ⇑(0 : α →C₀ β) = 0 := rfl
lemma zero_apply [has_zero β] : (0 : α →C₀ β) x = 0 := rfl

instance [mul_zero_class β] [has_continuous_mul β] : has_mul (α →C₀ β) :=
⟨λ f g, ⟨f * g, by simpa only [mul_zero] using ((zero_at_infty f).mul (zero_at_infty g) :
  tendsto (λ x : α, f x * g x) (cocompact α) (𝓝 (0 * 0)))⟩⟩

@[simp] lemma coe_mul [mul_zero_class β] [has_continuous_mul β] (f g : α →C₀ β) :
  ⇑(f * g) = f * g := rfl
lemma mul_apply [mul_zero_class β] [has_continuous_mul β] (f g : α →C₀ β) :
  (f * g) x = f x * g x := rfl

instance [mul_zero_class β] [has_continuous_mul β] : mul_zero_class (α →C₀ β) :=
fun_like.coe_injective.mul_zero_class _ coe_zero coe_mul

instance [semigroup_with_zero β] [has_continuous_mul β] : semigroup_with_zero (α →C₀ β) :=
fun_like.coe_injective.semigroup_with_zero _ coe_zero coe_mul

instance [add_zero_class β] [has_continuous_add β] : has_add (α →C₀ β) :=
⟨λ f g, ⟨f + g, by simpa only [add_zero] using ((zero_at_infty f).add (zero_at_infty g) :
  tendsto (λ x : α, f x + g x) (cocompact α) (𝓝 (0 + 0)))⟩⟩

@[simp] lemma coe_add [add_zero_class β] [has_continuous_add β] (f g : α →C₀ β) :
  ⇑(f + g) = f + g := rfl
lemma add_apply [add_zero_class β] [has_continuous_add β] (f g : α →C₀ β) :
  (f + g) x = f x + g x := rfl

instance [add_zero_class β] [has_continuous_add β] : add_zero_class (α →C₀ β) :=
fun_like.coe_injective.add_zero_class _ coe_zero coe_add

section add_monoid

variables [add_monoid β] [has_continuous_add β] (f g : α →C₀ β)

@[simp] lemma coe_nsmul_rec : ∀ n, ⇑(nsmul_rec n f) = n • f
| 0 := by rw [nsmul_rec, zero_smul, coe_zero]
| (n + 1) := by rw [nsmul_rec, succ_nsmul, coe_add, coe_nsmul_rec]

instance has_nat_scalar : has_scalar ℕ (α →C₀ β) :=
⟨λ n f, ⟨n • f, by simpa [coe_nsmul_rec] using (nsmul_rec n f).zero_at_infty'⟩⟩

@[simp] lemma coe_nsmul (r : ℕ) (f : α →C₀ β) : ⇑(r • f) = r • f := rfl
@[simp] lemma nsmul_apply (r : ℕ) (f : α →C₀ β) (v : α) : (r • f) v = r • f v := rfl

instance : add_monoid (α →C₀ β) :=
fun_like.coe_injective.add_monoid _ coe_zero coe_add (λ _ _, coe_nsmul _ _)

end add_monoid

instance [add_comm_monoid β] [has_continuous_add β] : add_comm_monoid (α →C₀ β) :=
fun_like.coe_injective.add_comm_monoid _ coe_zero coe_add (λ _ _, coe_nsmul _ _)

section add_group

variables [add_group β] [topological_add_group β] (f g : α →C₀ β)

instance : has_neg (α →C₀ β) :=
⟨λ f, ⟨-f, by simpa only [neg_zero] using (zero_at_infty f : tendsto f (cocompact α) (𝓝 0)).neg⟩⟩

@[simp] lemma coe_neg : ⇑(-f) = -f := rfl
lemma neg_apply : (-f) x = -f x := rfl

instance : has_sub (α →C₀ β) :=
⟨λ f g, ⟨f - g,
begin
  rw sub_eq_add_neg,
  simpa only [add_zero] using ((zero_at_infty f).add (zero_at_infty (-g)) :
    tendsto (λ x, f x + (-g) x) (cocompact α) (𝓝 (0 + 0))),
end⟩⟩

@[simp] lemma coe_sub : ⇑(f - g) = f - g := rfl
lemma sub_apply : (f - g) x = f x - g x := rfl

@[simp] lemma coe_zsmul_rec : ∀ z, ⇑(zsmul_rec z f) = z • f
| (int.of_nat n) := by rw [zsmul_rec, int.of_nat_eq_coe, coe_nsmul_rec, coe_nat_zsmul]
| -[1+ n] := by rw [zsmul_rec, zsmul_neg_succ_of_nat, coe_neg, coe_nsmul_rec]

instance has_int_scalar : has_scalar ℤ (α →C₀ β) :=
⟨λ n f, ⟨n • f, by simpa using (zsmul_rec n f).zero_at_infty'⟩⟩

@[simp] lemma coe_zsmul (r : ℤ) (f : α →C₀ β) : ⇑(r • f) = r • f := rfl
@[simp] lemma zsmul_apply (r : ℤ) (f : α →C₀ β) (v : α) : (r • f) v = r • f v := rfl

instance [add_group β] [topological_add_group β] : add_group (α →C₀ β) :=
fun_like.coe_injective.add_group _ coe_zero coe_add coe_neg coe_sub (λ _ _, coe_nsmul _ _)
  (λ _ _, coe_zsmul _ _)

end add_group

instance [add_comm_group β] [topological_add_group β] : add_comm_group (α →C₀ β) :=
fun_like.coe_injective.add_comm_group _ coe_zero coe_add coe_neg coe_sub (λ _ _, coe_nsmul _ _)
  (λ _ _, coe_zsmul _ _)

instance [has_zero β] {R : Type*} [has_zero R] [smul_with_zero R β]
  [has_continuous_const_smul R β] : has_scalar R (α →C₀ β) :=
⟨λ r f, ⟨r • f, by simpa [smul_zero] using
  (zero_at_infty f : tendsto f (cocompact α) (𝓝 0)).const_smul r⟩⟩

@[simp] lemma coe_smul [has_zero β] {R : Type*} [has_zero R] [smul_with_zero R β]
  [has_continuous_const_smul R β] (r : R) (f : α →C₀ β) : ⇑(r • f) = r • f := rfl

lemma smul_apply [has_zero β] {R : Type*} [has_zero R] [smul_with_zero R β]
  [has_continuous_const_smul R β] (r : R) (f : α →C₀ β) (x : α) : (r • f) x = r • f x := rfl

instance [has_zero β] {R : Type*} [has_zero R] [smul_with_zero R β]
  [has_continuous_const_smul R β] : smul_with_zero R (α →C₀ β) :=
function.injective.smul_with_zero ⟨_, coe_zero⟩ fun_like.coe_injective coe_smul

instance [has_zero β] {R : Type*} [monoid_with_zero R] [mul_action_with_zero R β]
  [has_continuous_const_smul R β] : mul_action_with_zero R (α →C₀ β) :=
function.injective.mul_action_with_zero ⟨_, coe_zero⟩ fun_like.coe_injective coe_smul

instance [add_comm_monoid β] [has_continuous_add β] {R : Type*} [comm_semiring R] [module R β]
  [has_continuous_const_smul R β] : module R (α →C₀ β) :=
function.injective.module R ⟨_, coe_zero, coe_add⟩ fun_like.coe_injective coe_smul

-- this needs to be switched to `topological_semiring β`
instance [non_unital_semiring β] [has_continuous_add β] [has_continuous_mul β] :
  non_unital_semiring (α →C₀ β) :=
fun_like.coe_injective.non_unital_semiring _ coe_zero coe_add coe_mul (λ _ _, coe_nsmul _ _)

-- This has to wait for the `topological_ring` refactor.
instance [non_unital_ring β] : -- [topological_ring β] :
  non_unital_ring (α →C₀ β) :=
sorry

end algebraic_structure

section metric

open metric set

variables [metric_space β] [has_zero β] [zero_at_infty_continuous_map_class F α β]

protected lemma bounded (f : F) : ∃ C, ∀ x y : α, dist ((f : α → β) x) (f y) ≤ C :=
begin
  obtain ⟨K : set α, hK₁, hK₂⟩ := mem_cocompact.mp (tendsto_def.mp (zero_at_infty (f : F)) _
    (closed_ball_mem_nhds (0 : β) zero_lt_one)),
  obtain ⟨C, hC⟩ := (hK₁.image (map_continuous f)).bounded.subset_ball (0 : β),
  refine ⟨max C 1 + max C 1, (λ x y, _)⟩,
  have : ∀ x, f x ∈ closed_ball (0 : β) (max C 1),
  { intro x,
    by_cases hx : x ∈ K,
    { exact (mem_closed_ball.mp $ hC ⟨x, hx, rfl⟩).trans (le_max_left _ _) },
    { exact (mem_closed_ball.mp $ mem_preimage.mp (hK₂ hx)).trans (le_max_right _ _) } },
  exact (dist_triangle (f x) 0 (f y)).trans
    (add_le_add (mem_closed_ball.mp $ this x) (mem_closed_ball'.mp $ this y)),
end

lemma bounded_range (f : α →C₀ β) : bounded (range f) :=
bounded_range_iff.2 f.bounded

lemma bounded_image (f : α →C₀ β) (s : set α) : bounded (f '' s) :=
f.bounded_range.mono $ image_subset_range _ _

@[priority 100]
instance : bounded_continuous_map_class F α β :=
{ coe := λ f, f,
  coe_injective' := λ f g h, fun_like.coe_fn_eq.mp h,
  map_continuous := λ f, map_continuous f,
  map_bounded := λ f, zero_at_infty_continuous_map.bounded f }

/-- Construct a bounded continuous function from a continuous function vanshing at infinity. -/
@[simps]
def to_bounded_continuous_function (f : α →C₀ β) : α →ᵇ β :=
⟨f, map_bounded f⟩

lemma _root_.function.injective.to_bounded_continuous_function :
  function.injective (to_bounded_continuous_function : (α →C₀ β) → α →ᵇ β) :=
λ f g h, by { ext, simpa only using fun_like.congr_fun h x, }

-- how can we get the dist from this injective?

variables {C : ℝ} {f g : α →C₀ β}

/-- The uniform distance between two bounded continuous functions -/
noncomputable instance : has_dist (α →C₀ β) :=
⟨λ f g, Inf {C | 0 ≤ C ∧ ∀ x : α, dist (f x) (g x) ≤ C}⟩

lemma dist_eq : dist f g = Inf {C | 0 ≤ C ∧ ∀ x : α, dist (f x) (g x) ≤ C} := rfl

lemma dist_set_exists : ∃ C, 0 ≤ C ∧ ∀ x : α, dist (f x) (g x) ≤ C :=
begin
  rcases f.bounded_range.union g.bounded_range with ⟨C, hC⟩,
  refine ⟨max 0 C, le_max_left _ _, λ x, (hC _ _ _ _).trans (le_max_right _ _)⟩;
    [left, right]; apply mem_range_self
end

/-- The pointwise distance is controlled by the distance between functions, by definition. -/
lemma dist_coe_le_dist (x : α) : dist (f x) (g x) ≤ dist f g :=
le_cInf dist_set_exists $ λ b hb, hb.2 x

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
  (w : ∀ x : α, dist (f x) (g x) < C) : dist f g < C :=
begin
  have c : continuous (λ x, dist (f x) (g x)), { continuity, },
  obtain ⟨x, -, le⟩ :=
    is_compact.exists_forall_ge compact_univ set.univ_nonempty (continuous.continuous_on c),
  exact lt_of_le_of_lt (dist_le_iff_of_nonempty.mpr (λ y, le y trivial)) (w x),
end

lemma dist_lt_iff_of_compact [compact_space α] (C0 : (0 : ℝ) < C) :
  dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C :=
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
  dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C :=
⟨λ w x, lt_of_le_of_lt (dist_coe_le_dist x) w, dist_lt_of_nonempty_compact⟩

/-- The type of bounded continuous functions, with the uniform distance, is a metric space. -/
noncomputable instance : metric_space (α →C₀ β) :=
{ dist_self := λ f, le_antisymm ((dist_le le_rfl).2 $ λ x, by simp) dist_nonneg',
  eq_of_dist_eq_zero := λ f g hfg, by ext x; exact
    eq_of_dist_eq_zero (le_antisymm (hfg ▸ dist_coe_le_dist _) dist_nonneg),
  dist_comm := λ f g, by simp [dist_eq, dist_comm],
  dist_triangle := λ f g h,
    (dist_le (add_nonneg dist_nonneg' dist_nonneg')).2 $ λ x,
      le_trans (dist_triangle _ _ _) (add_le_add (dist_coe_le_dist _) (dist_coe_le_dist _)) }

/-- On an empty space, bounded continuous functions are at distance 0 -/
lemma dist_zero_of_empty [is_empty α] : dist f g = 0 :=
dist_eq_zero.2 (eq_of_empty f g)

lemma dist_eq_supr : dist f g = ⨆ x : α, dist (f x) (g x) :=
begin
  casesI is_empty_or_nonempty α, { rw [supr_of_empty', real.Sup_empty, dist_zero_of_empty] },
  refine (dist_le_iff_of_nonempty.mpr $ le_csupr _).antisymm (csupr_le dist_coe_le_dist),
  exact dist_set_exists.imp (λ C hC, forall_range_iff.2 hC.2)
end

lemma lipschitz_evalx (x : α) : lipschitz_with 1 (λ f : α →C₀ β, f x) :=
lipschitz_with.mk_one $ λ f g, dist_coe_le_dist x

theorem uniform_continuous_coe : @uniform_continuous (α →C₀ β) (α → β) _ _ coe_fn :=
uniform_continuous_pi.2 $ λ x, (lipschitz_evalx x).uniform_continuous

lemma continuous_coe : continuous (λ (f : α →C₀ β) x, f x) :=
uniform_continuous.continuous uniform_continuous_coe

/-- When `x` is fixed, `(f : α →C₀ β) ↦ f x` is continuous -/
@[continuity] theorem continuous_evalx {x : α} : continuous (λ f : α →C₀ β, f x) :=
(continuous_apply x).comp continuous_coe

/-- The evaluation map is continuous, as a joint function of `u` and `x` -/
@[continuity] theorem continuous_eval : continuous (λ p : (α →C₀ β) × α, p.1 p.2) :=
continuous_prod_of_continuous_lipschitz _ 1 (λ f, map_continuous f) $ lipschitz_evalx

/-- Continuous functions vanishing at infinity taking values in a complete space form a
complete space. -/
instance [complete_space β] : complete_space (α →C₀ β) :=
complete_of_cauchy_seq_tendsto $ λ (f : ℕ → (α →C₀ β)) (hf : cauchy_seq f),
begin
  /- We have to show that `f n` converges to a continuous function vanishing at infinity
  For this, we prove pointwise convergence to define the limit, then check it is a
  continuous function vanishing at infinity, and then check the metric convergence. -/
  rcases cauchy_seq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩,
  have f_bdd := λ x n m N hn hm, le_trans (dist_coe_le_dist x) (b_bound n m N hn hm),
  have fx_cau : ∀ x, cauchy_seq (λn, f n x) :=
    λ x, cauchy_seq_iff_le_tendsto_0.2 ⟨b, b0, f_bdd x, b_lim⟩,
  choose F hF using λ x, cauchy_seq_tendsto_of_complete (fx_cau x),
  /- F : α → β,  hF : ∀ (x : α), tendsto (λ (n : ℕ), f n x) at_top (𝓝 (F x))
  `F` is the desired limit function. Check that it is uniformly approximated by `f N` -/
  have fF_bdd : ∀ x N, dist (f N x) (F x) ≤ b N :=
    λ x N, le_of_tendsto (tendsto_const_nhds.dist (hF x))
      (filter.eventually_at_top.2 ⟨N, λ n hn, f_bdd x N n N (le_refl N) hn⟩),
  refine ⟨⟨⟨F, _⟩, _⟩, _⟩,
  { /- Check that `F` is continuous, as a uniform limit of continuous functions -/
    have : tendsto_uniformly (λ n x, f n x) F at_top,
    { refine metric.tendsto_uniformly_iff.2 (λ ε ε0, _),
      refine ((tendsto_order.1 b_lim).2 ε ε0).mono (λ n hn x, _),
      rw dist_comm,
      exact lt_of_le_of_lt (fF_bdd x n) hn },
    exact this.continuous (eventually_of_forall $ λ N, map_continuous (f N)) },
  { /- Check that `F` vanishes at infinity. -/
    refine metric.tendsto_nhds.mpr (λ ε hε, eventually_iff.mpr $ mem_cocompact.mpr _),
    rcases metric.tendsto_at_top.1 b_lim (ε / 2) (half_pos hε) with ⟨N, hN⟩,
    obtain ⟨t : set α, ht, htε⟩ := (mem_cocompact.mp $ eventually_iff.1 $
      metric.tendsto_nhds.mp (f N).zero_at_infty' (ε / 2) (half_pos hε)),
    refine ⟨t, ht, λ x hx, _⟩,
    calc dist (F x) 0 ≤ dist (f N x) (F x) + dist (f N x) 0 : dist_triangle_left _ _ _
    ...               < |b N| + ε / 2
                      : add_lt_add_of_le_of_lt ((fF_bdd x N).trans (le_abs_self (b N))) (htε hx)
    ...               < ε / 2 + ε / 2
                      : add_lt_add_right (real.dist_0_eq_abs (b N) ▸ (hN N (le_refl N))) _
    ...               = ε : add_halves ε },
  { /- Check that `F` is close to `f N` in distance terms -/
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (λ _, dist_nonneg) _ b_lim),
    exact λ N, (dist_le (b0 _)).2 (λx, fF_bdd x N) }
end

end metric

end zero_at_infty_continuous_map
