/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The Fréchet derivative.

Let `E` and `F` be normed spaces, and `f : E → F`. Then

  `has_fderiv_at_within f f' x s`

says that the function `f' : E → F` is a bounded linear map and `f` has derivative `f'` at
`x`, where the domain of interest is restricted to `s`. We also have

  `has_fderiv_at f f' x := has_fderiv_at_within f f' x univ`

The derivative is defined in terms of the `is_o` relation, but also characterized in terms of
the `tendsto` relation.
-/
import topology.basic topology.sequences topology.opens
import analysis.normed_space.bounded_linear_maps analysis.asymptotics tactic.abel

open filter asymptotics

section

variables (K : Type*) [normed_field K]
variables {E : Type*} [normed_space K E]
variables {F : Type*} [normed_space K F]
variables {G : Type*} [normed_space K G]
include K

def has_fderiv_at_filter (f : E → F) (f' : E → F) (x : E) (L : filter E) :=
is_bounded_linear_map K f' ∧
  is_o (λ x', f x' - f x - f' (x' - x)) (λ x', x' - x) L

def has_fderiv_at_within (f : E → F) (f' : E → F) (x : E) (s : set E) :=
has_fderiv_at_filter K f f' x (nhds_within x s)

def has_fderiv_at (f : E → F) (f' : E → F) (x : E) :=
has_fderiv_at_filter K f f' x (nhds x)

variables {K}

theorem has_fderiv_at_filter.is_o {f : E → F} {f' : E → F} {x L}
  (h : has_fderiv_at_filter K f f' x L) :
  is_o (λ x', f x' - f x - f' (x' - x)) (λ x', x' - x) L :=
h.right

theorem has_fderiv_at.is_o {f : E → F} {f' : E → F} {x : E} (h : has_fderiv_at K f f' x) :
  is_o (λ x', f x' - f x - f' (x' - x)) (λ x', x' - x) (nhds x) :=
h.is_o

theorem has_fderiv_at_filter_iff_tendsto {f : E → F} {f' : E → F} {x : E} {L : filter E} :
  has_fderiv_at_filter K f f' x L ↔
    is_bounded_linear_map K f' ∧
      tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - f' (x' - x)∥) L (nhds 0) :=
and.congr_right_iff.mpr $
  assume bf' : is_bounded_linear_map K f',
  have f'0 : f' 0 = 0 := (bf'.to_linear_map _).map_zero,
  have h : ∀ x', ∥x' - x∥ = 0 → ∥f x' - f x - f' (x' - x)∥ = 0, from
    assume x' hx',
    have x' = x, from eq_of_sub_eq_zero ((norm_eq_zero _).mp hx'),
    by rw this; simp [f'0],
  begin
    rw [←is_o_norm_left, ←is_o_norm_right, is_o_iff_tendsto h],
    exact tendsto.congr'r (λ x', mul_comm _ _)
  end

theorem has_fderiv_at_within_iff_tendsto {f : E → F} {f' : E → F} {x : E} {s : set E} :
  has_fderiv_at_within K f f' x s ↔
    is_bounded_linear_map K f' ∧
      tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - f' (x' - x)∥) (nhds_within x s) (nhds 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_fderiv_at_iff_tendsto {f : E → F} {f' : E → F} {x : E} :
  has_fderiv_at K f f' x ↔
    is_bounded_linear_map K f' ∧
      tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - f' (x' - x)∥) (nhds x) (nhds 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_fderiv_at_filter.mono {f : E → F} {f' : E → F} {x : E} {L₁ L₂ : filter E}
  (hst : L₁ ≤ L₂) : has_fderiv_at_filter K f f' x L₂ → has_fderiv_at_filter K f f' x L₁ :=
and.imp_right (is_o.mono hst)

theorem has_fderiv_at_within.mono {f : E → F} {f' : E → F} {x : E} {s t : set E}
  (hst : s ⊆ t) : has_fderiv_at_within K f f' x t → has_fderiv_at_within K f f' x s :=
has_fderiv_at_filter.mono (nhds_within_mono _ hst)

theorem has_fderiv_at_filter_of_has_fderiv_at {f : E → F} {f' : E → F} {x : E}
  {L : filter E} (hL : L ≤ nhds x) (h : has_fderiv_at K f f' x) : has_fderiv_at_filter K f f' x L :=
h.mono hL

theorem has_fderiv_at_within_of_has_fderiv_at {f : E → F} {f' : E → F} {x : E} {s : set E} :
  has_fderiv_at K f f' x → has_fderiv_at_within K f f' x s :=
has_fderiv_at_filter_of_has_fderiv_at lattice.inf_le_left

theorem has_fderiv_at_filter_congr' {f₀ f₁ : E → F} {f₀' f₁' : E → F} {x : E} {L : filter E}
  (hx : f₀ x = f₁ x) (h₀ : {x | f₀ x = f₁ x} ∈ L) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_filter K f₀ f₀' x L ↔ has_fderiv_at_filter K f₁ f₁' x L :=
by rw (funext h₁ : f₀' = f₁'); exact
and_congr_right (λ _, is_o_congr
  (by filter_upwards [h₀] λ x' (h:_=_), by simp [h, hx])
  (univ_mem_sets' $ λ _, rfl))

theorem has_fderiv_at_filter_congr {f₀ f₁ : E → F} {f₀' f₁' : E → F} {x : E} {L : filter E}
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_filter K f₀ f₀' x L ↔ has_fderiv_at_filter K f₁ f₁' x L :=
has_fderiv_at_filter_congr' (h₀ _) (univ_mem_sets' h₀) h₁

theorem has_fderiv_at_filter.congr {f₀ f₁ : E → F} {f₀' f₁' : E → F} {x : E} {L : filter E}
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_filter K f₀ f₀' x L → has_fderiv_at_filter K f₁ f₁' x L :=
(has_fderiv_at_filter_congr h₀ h₁).1

theorem has_fderiv_at_within_congr {f₀ f₁ : E → F} {f₀' f₁' : E → F} {x : E} {s : set E}
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_within K f₀ f₀' x s ↔ has_fderiv_at_within K f₁ f₁' x s :=
has_fderiv_at_filter_congr h₀ h₁

theorem has_fderiv_at_within.congr {f₀ f₁ : E → F} {f₀' f₁' : E → F} {x : E} {s : set E}
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_within K f₀ f₀' x s → has_fderiv_at_within K f₁ f₁' x s :=
(has_fderiv_at_within_congr h₀ h₁).1

theorem has_fderiv_at_congr {f₀ f₁ : E → F} {f₀' f₁' : E → F} {x : E}
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at K f₀ f₀' x ↔ has_fderiv_at K f₁ f₁' x :=
has_fderiv_at_filter_congr h₀ h₁

theorem has_fderiv_at.congr {f₀ f₁ : E → F} {f₀' f₁' : E → F} {x : E}
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at K f₀ f₀' x → has_fderiv_at K f₁ f₁' x :=
(has_fderiv_at_congr h₀ h₁).1

theorem has_fderiv_at_filter_id (x : E) (L : filter E) : has_fderiv_at_filter K id id x L :=
⟨is_bounded_linear_map.id, (is_o_zero _ _).congr_left (by simp)⟩

theorem has_fderiv_at_within_id (x : E) (s : set E) : has_fderiv_at_within K id id x s :=
has_fderiv_at_filter_id _ _

theorem has_fderiv_at_id (x : E) : has_fderiv_at K id id x :=
has_fderiv_at_filter_id _ _

theorem has_fderiv_at_filter_const (c : F) (x : E) (L : filter E) :
  has_fderiv_at_filter K (λ x, c) (λ y, 0) x L :=
⟨is_bounded_linear_map.zero, (is_o_zero _ _).congr_left (by simp)⟩

theorem has_fderiv_at_within_const (c : F) (x : E) (s : set E) :
  has_fderiv_at_within K (λ x, c) (λ y, 0) x s :=
has_fderiv_at_filter_const _ _ _

theorem has_fderiv_at_const (c : F) (x : E) :
  has_fderiv_at K (λ x, c) (λ y, 0) x :=
has_fderiv_at_filter_const _ _ _

set_option class.instance_max_depth 43

theorem has_fderiv_at_filter_smul {f : E → F} {f' : E → F} {x : E} {L : filter E}
    (c : K) (h : has_fderiv_at_filter K f f' x L) :
  has_fderiv_at_filter K (λ x, c • f x) (λ x, c • f' x) x L :=
⟨is_bounded_linear_map.smul c h.left,
  (is_o_const_smul_left h.right c).congr_left $
  λ x, by simp [smul_neg, smul_add]⟩

theorem has_fderiv_at_within_smul {f : E → F} {f' : E → F} {x : E} {s : set E}
    (c : K) : has_fderiv_at_within K f f' x s →
  has_fderiv_at_within K (λ x, c • f x) (λ x, c • f' x) x s :=
has_fderiv_at_filter_smul _

theorem has_fderiv_at_smul {f : E → F} {f' : E → F} {x : E}
    (c : K) : has_fderiv_at K f f' x →
  has_fderiv_at K (λ x, c • f x) (λ x, c • f' x) x :=
has_fderiv_at_filter_smul _

theorem has_fderiv_at_filter_add {f g : E → F} {f' g' : E → F} {x : E} {L : filter E}
  (hf : has_fderiv_at_filter K f f' x L) (hg : has_fderiv_at_filter K g g' x L) :
  has_fderiv_at_filter K (λ x, f x + g x) (λ x, f' x + g' x) x L :=
⟨is_bounded_linear_map.add hf.left hg.left,
  (hf.right.add hg.right).congr_left (by simp)⟩

theorem has_fderiv_at_within_add {f g : E → F} {f' g' : E → F} {x : E} {s : set E} :
  has_fderiv_at_within K f f' x s → has_fderiv_at_within K g g' x s →
  has_fderiv_at_within K (λ x, f x + g x) (λ x, f' x + g' x) x s :=
has_fderiv_at_filter_add

theorem has_fderiv_at_add {f g : E → F} {f' g' : E → F} {x : E} :
  has_fderiv_at K f f' x → has_fderiv_at K g g' x →
  has_fderiv_at K (λ x, f x + g x) (λ x, f' x + g' x) x :=
has_fderiv_at_filter_add

theorem has_fderiv_at_filter_neg {f : E → F} {f' : E → F} {x : E} {L : filter E}
  (h : has_fderiv_at_filter K f f' x L) :
  has_fderiv_at_filter K (λ x, -f x) (λ x, -f' x) x L :=
(has_fderiv_at_filter_smul (-1 : K) h).congr (by simp) (by simp)

theorem has_fderiv_at_within_neg {f : E → F} {f' : E → F} {x : E} {s : set E} :
  has_fderiv_at_within K f f' x s → has_fderiv_at_within K (λ x, -f x) (λ x, -f' x) x s :=
has_fderiv_at_filter_neg

theorem has_fderiv_at_neg {f : E → F} {f' : E → F} {x : E} :
  has_fderiv_at K f f' x → has_fderiv_at K (λ x, -f x) (λ x, -f' x) x :=
has_fderiv_at_filter_neg

theorem has_fderiv_at_filter_sub {f g : E → F} {f' g' : E → F} {x : E} {L : filter E}
  (hf : has_fderiv_at_filter K f f' x L) (hg : has_fderiv_at_filter K g g' x L) :
  has_fderiv_at_filter K (λ x, f x - g x) (λ x, f' x - g' x) x L :=
has_fderiv_at_filter_add hf (has_fderiv_at_filter_neg hg)

theorem has_fderiv_at_within_sub {f g : E → F} {f' g' : E → F} {x : E} {s : set E} :
  has_fderiv_at_within K f f' x s → has_fderiv_at_within K g g' x s →
  has_fderiv_at_within K (λ x, f x - g x) (λ x, f' x - g' x) x s :=
has_fderiv_at_filter_sub

theorem has_fderiv_at_sub {f g : E → F} {f' g' : E → F} {x : E} :
  has_fderiv_at K f f' x → has_fderiv_at K g g' x →
  has_fderiv_at K (λ x, f x - g x) (λ x, f' x - g' x) x :=
has_fderiv_at_filter_sub

theorem has_fderiv_at_filter.is_O_sub {f : E → F} {f' : E → F} {x : E} {L : filter E}
  (h : has_fderiv_at_filter K f f' x L) : is_O (λ x', f x' - f x) (λ x', x' - x) L :=
h.2.to_is_O.congr_of_sub.2 (h.1.is_O_sub _ _)

theorem has_fderiv_at_filter.tendsto_nhds {f : E → F} {f' : E → F} {x : E} {L : filter E}
  (hL : L ≤ nhds x) (h : has_fderiv_at_filter K f f' x L) : tendsto f L (nhds (f x)) :=
begin
  have : tendsto (λ x', f x' - f x) L (nhds 0),
  { refine h.is_O_sub.trans_tendsto (tendsto_le_left hL _),
    rw ← sub_self x, exact tendsto_sub tendsto_id tendsto_const_nhds },
  have := tendsto_add this tendsto_const_nhds,
  rw zero_add (f x) at this,
  exact this.congr (by simp)
end

theorem has_fderiv_at_within.continuous_at_within {f : E → F} {f' : E → F} {x : E} {s : set E} :
  has_fderiv_at_within K f f' x s → continuous_at_within f x s :=
has_fderiv_at_filter.tendsto_nhds lattice.inf_le_left

theorem has_fderiv_at.continuous_at {f : E → F} {f' : E → F} {x : E} :
  has_fderiv_at K f f' x → continuous_at f x :=
has_fderiv_at_filter.tendsto_nhds (le_refl _)

theorem has_fderiv_at_filter.comp {g g' : F → G} {f f' : E → F} {L : filter E} {x : E}
  (hf : has_fderiv_at_filter K f f' x L)
  (hg : has_fderiv_at_filter K g g' (f x) (L.map f)) :
  has_fderiv_at_filter K (g ∘ f) (g' ∘ f') x L :=
⟨hg.1.comp hf.1, begin
  have eq₁ := (hg.1.is_O_comp _).trans_is_o hf.2,
  have eq₂ := ((hg.2.comp f).mono le_comap_map).trans_is_O hf.is_O_sub,
  refine eq₂.tri (eq₁.congr_left (λ x', _)),
  rw [show g' (_-_) = g' _ - g' _, from (hg.1.to_linear_map _).map_sub _ _]
end⟩

/- A readable version of the previous theorem, a general form of the chain rule. -/

example {g g' : F → G} {f f' : E → F} {L : filter E} {x : E}
  (hf : has_fderiv_at_filter K f f' x L)
  (hg : has_fderiv_at_filter K g g' (f x) (L.map f)) :
  has_fderiv_at_filter K (g ∘ f) (g' ∘ f') x L :=
⟨hg.1.comp hf.1,
begin
  have : is_o (λ x', g (f x') - g (f x) - g' (f x' - f x)) (λ x', f x' - f x) L,
    from (hg.2.comp f).mono le_comap_map,
  have eq₁ : is_o (λ x', g (f x') - g (f x) - g' (f x' - f x)) (λ x', x' - x) L,
    from this.trans_is_O hf.is_O_sub,
  have eq₂ : is_o (λ x', f x' - f x - f' (x' - x)) (λ x', x' - x) L,
    from hf.2,
  have : is_O (λ x', g' (f x' - f x - f' (x' - x))) (λ x', f x' - f x - f' (x' - x)) L,
    from hg.1.is_O_comp _,
  have : is_o (λ x', g' (f x' - f x - f' (x' - x))) (λ x', x' - x) L,
    from this.trans_is_o eq₂,
  have eq₃ : is_o (λ x', g' (f x' - f x) - (g' (f' (x' - x)))) (λ x', x' - x) L,
    by { refine this.congr_left (λ x', _),
         rw [show g' (_-_) = g' _ - g' _, from (hg.1.to_linear_map _).map_sub _ _] },
  exact eq₁.tri eq₃
end⟩

theorem has_fderiv_at_within.comp {g g' : F → G} {f f' : E → F} {s : set E} {x : E}
  (hf : has_fderiv_at_within K f f' x s)
  (hg : has_fderiv_at_within K g g' (f x) (f '' s)) :
  has_fderiv_at_within K (g ∘ f) (g' ∘ f') x s :=
hf.comp (has_fderiv_at_filter.mono
  hf.continuous_at_within.tendsto_nhds_within_image hg)

/-- The chain rule. -/
theorem has_fderiv_at.comp {g g' : F → G} {f f' : E → F} {x : E}
  (hf : has_fderiv_at K f f' x) (hg : has_fderiv_at K g g' (f x)) :
  has_fderiv_at K (g ∘ f) (g' ∘ f') x :=
hf.comp (hg.mono hf.continuous_at)

end

section

variables (K : Type*) [nondiscrete_normed_field K]
variables {E : Type*} [normed_space K E]
variables {F : Type*} [normed_space K F]

open topological_space

set_option class.instance_max_depth 55

/-- The differential of a map at a point along a filter is unique, given that filter is coarser than the
 neighbourhood filter of the point.-/
lemma fderiv_at_filter_unique (f : E → F) (x₀ : E) {L : filter E} (h : nhds x₀ ≤ L) {A₁ A₂ : E → F} :
  has_fderiv_at_filter K f A₁ x₀ L → has_fderiv_at_filter K f A₂ x₀ L → A₁ = A₂ :=

assume ⟨⟨A₁_linear, A₁_bounded₁⟩, (eq₁ : is_o (λ x, f x - f x₀ - A₁ (x - x₀)) (λ x, x - x₀) L)⟩
  ⟨⟨A₂_linear₂, A₂_bounded⟩, (eq₂ : is_o (λ x, f x - f x₀ - A₂ (x - x₀)) (λ x, x - x₀) L)⟩,

-- To prove that A₁ = A₂, substract eq₁ and eq₂. After some calculation this implies
-- that for ∀ v ∈ E, lim_{n→∞} A₂ v - A₁ v = 0. We first show that this implies the claim
-- using the uniqueness of limits in normed spaces.
suffices ∀ v : E, tendsto (λ n : ℕ, A₂ v - A₁ v) at_top (nhds 0),
begin
  ext v, symmetry,
  rw [←sub_eq_zero_iff_eq], symmetry,
  exact tendsto_nhds_unique at_top_ne_bot (this v) tendsto_const_nhds
end,

assume v,

-- substract the equations eq₁ and eq₂ showing that A₁ and A₂ are differential
have is_o (λ x, A₂ (x - x₀) - A₁ (x - x₀)) (λ x, x - x₀) L, by simpa using eq₁.sub eq₂,

-- pick ξ ≠ 0, ∥ξ∥ < 1 and plugin in the sequence ξ^n + x₀, replace filter by at_top
let ⟨ξ, _, _⟩ := exists_norm_lt_one K in
have is_o (λ n, A₂ (ξ^n • v) - A₁ (ξ^n • v)) (λ n, ξ^n • v) (comap ((λ n, x₀ + ξ^n • v)) (nhds x₀)),
  by simpa [function.comp] using ((this.comp (λ (n : ℕ), ξ^n • v + x₀)).mono (comap_mono h)),

-- refine the filter to at_top
have at_top_is_finer : at_top ≤ comap (λ (n : ℕ), (ξ^n) • v + x₀) (nhds x₀),
begin
  rw ←tendsto_iff_comap,
  have : continuous (λ c : K, c • v + x₀) := continuous_add
    (continuous_smul continuous_id continuous_const) continuous_const,
  simpa only [zero_add, zero_smul, function.comp] using
    ‹continuous (λ c : K, c • v + x₀)›.to_sequentially_continuous (λ n, ξ^n)
      (tendsto_pow_at_top_nhds_0_of_lt_1_normed_field ‹∥ξ∥ < 1›)
end,

-- and use monotonicity of little o
have is_o (λ n : ℕ, A₂ (ξ^n • v) - A₁ (ξ^n • v)) (λ n, ξ^n • v) at_top,
  from is_o.mono at_top_is_finer (by simpa using this),

-- the ξ^n factor cancels
have is_o (λ (x : ℕ), A₂ v - A₁ v) (λ (x : ℕ), v) at_top,
  by simpa [‹is_linear_map K A₁›.smul, ‹is_linear_map K A₂›.smul,
            smul_add, smul_smul, inv_mul_cancel ((λ n, pow_ne_zero n ((norm_pos_iff ξ).mp ‹0 < ∥ξ∥›)) _), one_smul] using
     @is_o_smul _ _ _ _ _ _ _ (λ n : ℕ, (ξ^n)⁻¹) _ _ _ this,

show tendsto (λ (n : ℕ), A₂ v - A₁ v) at_top (nhds 0),
  from is_o_one_iff.mp (this.trans_is_O (is_O_const_one v _) : is_o _ (λ n, (1:K)) _)

theorem fderiv_at_unique (f : E → F) (x₀ : E) {A₁ A₂ : E → F} :
  has_fderiv_at K f A₁ x₀ → has_fderiv_at K f A₂ x₀ → A₁ = A₂ :=
assume H₁ H₂, fderiv_at_filter_unique K f x₀ (le_refl (nhds x₀)) H₁ H₂

theorem fderiv_at_within_open_unique (f : E → F) (U : opens E) (x₀ : U) {A₁ A₂ : E → F} :
  has_fderiv_at_within K f A₁ x₀ U → has_fderiv_at_within K f A₂ x₀ U → A₁ = A₂ :=
assume H₁ H₂, fderiv_at_filter_unique K f x₀ (le_of_eq $ eq.symm (nhds_within_eq_of_open x₀.2 U.2)) H₁ H₂

end

/-
In the special case of a normed space over the reals, we can use scalar multiplication in the
`tendsto` characterization of the Fréchet derivative.
-/

section

variables {E : Type*} [normed_space ℝ E]
variables {F : Type*} [normed_space ℝ F]
variables {G : Type*} [normed_space ℝ G]

set_option class.instance_max_depth 34

theorem has_fderiv_at_filter_real_equiv {f : E → F} {f' : E → F} {x : E} {L : filter E}
    (bf' : is_bounded_linear_map ℝ f') :
  tendsto (λ x' : E, ∥x' - x∥⁻¹ * ∥f x' - f x - f' (x' - x)∥) L (nhds 0) ↔
  tendsto (λ x' : E, ∥x' - x∥⁻¹ • (f x' - f x - f' (x' - x))) L (nhds 0) :=
begin
  have f'0 : f' 0 = 0 := (bf'.to_linear_map _).map_zero,
  symmetry, rw [tendsto_iff_norm_tendsto_zero], refine tendsto.congr'r (λ x', _),
  have : ∥x' + -x∥⁻¹ ≥ 0, from inv_nonneg.mpr (norm_nonneg _),
  simp [norm_smul, real.norm_eq_abs, abs_of_nonneg this]
end

end
