/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Continuous linear functions -- functions between normed vector spaces which are bounded and linear.
-/
import algebra.field
import analysis.normed_space.operator_norm

noncomputable theory
local attribute [instance] classical.prop_decidable

local notation f ` →_{`:50 a `} `:0 b := filter.tendsto f (nhds a) (nhds b)

open filter (tendsto)
open metric

variables {k : Type*} [normed_field k]
variables {E : Type*} [normed_space k E]
variables {F : Type*} [normed_space k F]
variables {G : Type*} [normed_space k G]

structure is_bounded_linear_map (k : Type*) [normed_field k] {E : Type*}
  [normed_space k E] {F : Type*} [normed_space k F] (f : E → F)
  extends is_linear_map k f : Prop :=
(bound : ∃ M > 0, ∀ x : E, ∥ f x ∥ ≤ M * ∥ x ∥)

lemma is_linear_map.with_bound
  {f : E → F} (hf : is_linear_map k f) (M : ℝ) (h : ∀ x : E, ∥ f x ∥ ≤ M * ∥ x ∥) :
  is_bounded_linear_map k f :=
⟨ hf, classical.by_cases
  (assume : M ≤ 0, ⟨1, zero_lt_one, assume x,
    le_trans (h x) $ mul_le_mul_of_nonneg_right (le_trans this zero_le_one) (norm_nonneg x)⟩)
  (assume : ¬ M ≤ 0, ⟨M, lt_of_not_ge this, h⟩)⟩

/-- A bounded linear map satisfies `is_bounded_linear_map` -/
lemma bounded_linear_map.is_bounded_linear_map (f : E →L[k] F) : is_bounded_linear_map k f := {..f}

namespace is_bounded_linear_map

def to_linear_map (f : E → F) (h : is_bounded_linear_map k f) : E →ₗ[k] F :=
(is_linear_map.mk' _ h.to_is_linear_map)

/-- Construct a bounded linear map from is_bounded_linear_map -/
def to_bounded_linear_map {f : E → F} (hf : is_bounded_linear_map k f) : E →L[k] F :=
{ bound := hf.bound, ..is_bounded_linear_map.to_linear_map f hf }

lemma zero : is_bounded_linear_map k (λ (x:E), (0:F)) :=
(0 : E →ₗ F).is_linear.with_bound 0 $ by simp [le_refl]

lemma id : is_bounded_linear_map k (λ (x:E), x) :=
linear_map.id.is_linear.with_bound 1 $ by simp [le_refl]

set_option class.instance_max_depth 43
variables { f g : E → F }

lemma smul (c : k) (hf : is_bounded_linear_map k f) :
  is_bounded_linear_map k (λ e, c • f e) :=
let ⟨hlf, M, hMp, hM⟩ := hf in
(c • hlf.mk' f).is_linear.with_bound (∥c∥ * M) $ assume x,
  calc ∥c • f x∥ = ∥c∥ * ∥f x∥ : norm_smul c (f x)
  ... ≤ ∥c∥ * (M * ∥x∥)        : mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  ... = (∥c∥ * M) * ∥x∥        : (mul_assoc _ _ _).symm

lemma neg (hf : is_bounded_linear_map k f) :
  is_bounded_linear_map k (λ e, -f e) :=
begin
  rw show (λ e, -f e) = (λ e, (-1 : k) • f e), { funext, simp },
  exact smul (-1) hf
end

lemma add (hf : is_bounded_linear_map k f) (hg : is_bounded_linear_map k g) :
  is_bounded_linear_map k (λ e, f e + g e) :=
let ⟨hlf, Mf, hMfp, hMf⟩ := hf in
let ⟨hlg, Mg, hMgp, hMg⟩ := hg in
(hlf.mk' _ + hlg.mk' _).is_linear.with_bound (Mf + Mg) $ assume x,
  calc ∥f x + g x∥ ≤ ∥f x∥ + ∥g x∥ : norm_triangle _ _
  ... ≤ Mf * ∥x∥ + Mg * ∥x∥        : add_le_add (hMf x) (hMg x)
  ... ≤ (Mf + Mg) * ∥x∥            : by rw add_mul

lemma sub (hf : is_bounded_linear_map k f) (hg : is_bounded_linear_map k g) :
  is_bounded_linear_map k (λ e, f e - g e) := add hf (neg hg)

lemma comp {g : F → G}
  (hg : is_bounded_linear_map k g) (hf : is_bounded_linear_map k f) :
  is_bounded_linear_map k (g ∘ f) :=
let ⟨hlg, Mg, hMgp, hMg⟩ := hg in
let ⟨hlf, Mf, hMfp, hMf⟩ := hf in
((hlg.mk' _).comp (hlf.mk' _)).is_linear.with_bound (Mg * Mf) $ assume x,
  calc ∥g (f x)∥ ≤ Mg * ∥f x∥ : hMg _
    ... ≤ Mg * (Mf * ∥x∥) : mul_le_mul_of_nonneg_left (hMf _) (le_of_lt hMgp)
    ... = Mg * Mf * ∥x∥   : (mul_assoc _ _ _).symm

lemma tendsto (x : E) (hf : is_bounded_linear_map k f) : f →_{x} (f x) :=
let ⟨hf, M, hMp, hM⟩ := hf in
tendsto_iff_norm_tendsto_zero.2 $
  squeeze_zero (assume e, norm_nonneg _)
    (assume e,
      calc ∥f e - f x∥ = ∥hf.mk' f (e - x)∥ : by rw (hf.mk' _).map_sub e x; refl
                   ... ≤ M * ∥e - x∥        : hM (e - x))
    (suffices (λ (e : E), M * ∥e - x∥) →_{x} (M * 0), by simpa,
      tendsto_mul tendsto_const_nhds (lim_norm _))

lemma continuous (hf : is_bounded_linear_map k f) : continuous f :=
continuous_iff_continuous_at.2 $ λ _, hf.tendsto _

lemma lim_zero_bounded_linear_map (hf : is_bounded_linear_map k f) :
  (f →_{0} 0) :=
(hf.1.mk' _).map_zero ▸ continuous_iff_continuous_at.1 hf.continuous 0

section
open asymptotics filter

theorem is_O_id {f : E → F} (h : is_bounded_linear_map k f) (l : filter E) :
  is_O f (λ x, x) l :=
let ⟨M, hMp, hM⟩ := h.bound in
⟨M, hMp, mem_sets_of_superset univ_mem_sets (λ x _, hM x)⟩

theorem is_O_comp {g : F → G} (hg : is_bounded_linear_map k g)
  {f : E → F} (l : filter E) : is_O (λ x', g (f x')) f l :=
((hg.is_O_id ⊤).comp _).mono (map_le_iff_le_comap.mp lattice.le_top)

theorem is_O_sub {f : E → F} (h : is_bounded_linear_map k f)
  (l : filter E) (x : E) : is_O (λ x', f (x' - x)) (λ x', x' - x) l :=
is_O_comp h l

end

end is_bounded_linear_map

set_option class.instance_max_depth 60

lemma is_bounded_linear_map_prod_iso :
  is_bounded_linear_map k (λ(p : (E →L[k] F) × (E →L[k] G)),
                            (bounded_linear_map.prod p.1 p.2 : (E →L[k] (F × G)))) :=
begin
  refine is_linear_map.with_bound ⟨λu v, rfl, λc u, rfl⟩ 1 (λp, _),
  simp only [norm, one_mul],
  refine bounded_linear_map.op_norm_le_bound _ (le_trans (norm_nonneg _) (le_max_left _ _)) (λu, _),
  simp only [norm, bounded_linear_map.prod, max_le_iff],
  split,
  { calc ∥p.1 u∥ ≤ ∥p.1∥ * ∥u∥ : bounded_linear_map.le_op_norm _ _
    ... ≤ max (∥p.1∥) (∥p.2∥) * ∥u∥ :
      mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _) },
  { calc ∥p.2 u∥ ≤ ∥p.2∥ * ∥u∥ : bounded_linear_map.le_op_norm _ _
    ... ≤ max (∥p.1∥) (∥p.2∥) * ∥u∥ :
      mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _) }
end

lemma bounded_linear_map.is_bounded_linear_map_comp_left (g : bounded_linear_map k F G) :
  is_bounded_linear_map k (λ(f : E →L[k] F), bounded_linear_map.comp g f) :=
begin
  refine is_linear_map.with_bound ⟨λu v, _, λc u, _⟩
    (∥g∥) (λu, bounded_linear_map.op_norm_comp_le _ _),
  { ext x,
    change g ((u+v) x) = g (u x) + g (v x),
    have : (u+v) x = u x + v x := rfl,
    rw [this, g.map_add] },
  { ext x,
    change g ((c • u) x) = c • g (u x),
    have : (c • u) x = c • u x := rfl,
    rw [this, bounded_linear_map.map_smul] }
end

lemma bounded_linear_map.is_bounded_linear_map_comp_right (f : bounded_linear_map k E F) :
  is_bounded_linear_map k (λ(g : F →L[k] G), bounded_linear_map.comp g f) :=
begin
  refine is_linear_map.with_bound ⟨λu v, rfl, λc u, rfl⟩ (∥f∥) (λg, _),
  rw mul_comm,
  exact bounded_linear_map.op_norm_comp_le _ _
end

/-- A continuous linear map between normed spaces is bounded when the field is nondiscrete.
The continuity ensures boundedness on a ball of some radius δ. The nondiscreteness is then
used to rescale any element into an element of norm in [δ/C, δ], whose image has a controlled norm.
The norm control for the original element follows by rescaling. -/
theorem is_linear_map.bounded_of_continuous_at {k : Type*} [nondiscrete_normed_field k]
  {E : Type*} [normed_space k E] {F : Type*} [normed_space k F] {f : E → F} {x₀ : E}
  (lin : is_linear_map k f) (cont : continuous_at f x₀) : is_bounded_linear_map k f :=
begin
  rcases tendsto_nhds_nhds.1 cont 1 zero_lt_one with ⟨ε, ε_pos, hε⟩,
  let δ := ε/2,
  have δ_pos : δ > 0 := half_pos ε_pos,
  have H : ∀{a}, ∥a∥ ≤ δ → ∥f a∥ ≤ 1,
  { assume a ha,
    have : dist (f (x₀+a)) (f x₀) ≤ 1,
    { apply le_of_lt (hε _),
      have : dist x₀ (x₀ + a) = ∥a∥, by { rw dist_eq_norm, simp },
      rw [dist_comm, this],
      exact lt_of_le_of_lt ha (half_lt_self ε_pos) },
    simpa [dist_eq_norm, lin.add] using this },
  rcases exists_one_lt_norm k with ⟨c, hc⟩,
  refine lin.with_bound (δ⁻¹ * ∥c∥) (λx, _),
  by_cases h : x = 0,
  { simp only [h, lin.map_zero, norm_zero, mul_zero] },
  { rcases rescale_to_shell hc δ_pos h with ⟨d, hd, dxle, ledx, dinv⟩,
    calc ∥f x∥
      = ∥f ((d⁻¹ * d) • x)∥ : by rwa [inv_mul_cancel, one_smul]
      ... = ∥d∥⁻¹ * ∥f (d • x)∥ :
        by rw [mul_smul, lin.smul, norm_smul, norm_inv]
      ... ≤ ∥d∥⁻¹ * 1 :
        mul_le_mul_of_nonneg_left (H dxle) (by { rw ← norm_inv, exact norm_nonneg _ })
      ... ≤ δ⁻¹ * ∥c∥ * ∥x∥ : by { rw mul_one, exact dinv } }
end


section bilinear_map

variable (k)

structure is_bounded_bilinear_map (f : E × F → G) : Prop :=
(add_left   : ∀(x₁ x₂ : E) (y : F), f (x₁ + x₂, y) = f (x₁, y) + f (x₂, y))
(smul_left  : ∀(c : k) (x : E) (y : F), f (c • x, y) = c • f (x,y))
(add_right  : ∀(x : E) (y₁ y₂ : F), f (x, y₁ + y₂) = f (x, y₁) + f (x, y₂))
(smul_right : ∀(c : k) (x : E) (y : F), f (x, c • y) = c • f (x,y))
(bound      : ∃C>0, ∀(x : E) (y : F), ∥f (x, y)∥ ≤ C * ∥x∥ * ∥y∥)

variable {k}
variable {f : E × F → G}

lemma is_bounded_bilinear_map.map_sub_left (h : is_bounded_bilinear_map k f) {x y : E} {z : F} :
  f (x - y, z) = f (x, z) -  f(y, z) :=
calc f (x - y, z) = f (x + (-1 : k) • y, z) : by simp
... = f (x, z) + (-1 : k) • f (y, z) : by simp only [h.add_left, h.smul_left]
... = f (x, z) - f (y, z) : by simp

lemma is_bounded_bilinear_map.map_sub_right (h : is_bounded_bilinear_map k f) {x : E} {y z : F} :
  f (x, y - z) = f (x, y) - f (x, z) :=
calc f (x, y - z) = f (x, y + (-1 : k) • z) : by simp
... = f (x, y) + (-1 : k) • f (x, z) : by simp only [h.add_right, h.smul_right]
... = f (x, y) - f (x, z) : by simp

lemma is_bounded_bilinear_map_smul :
  is_bounded_bilinear_map k (λ (p : k × E), p.1 • p.2) :=
{ add_left   := add_smul,
  smul_left  := λc x y, by simp [smul_smul],
  add_right  := smul_add,
  smul_right := λc x y, by simp [smul_smul, mul_comm],
  bound      := ⟨1, zero_lt_one, λx y, by simp [norm_smul]⟩ }

lemma is_bounded_bilinear_map_mul :
  is_bounded_bilinear_map k (λ (p : k × k), p.1 * p.2) :=
is_bounded_bilinear_map_smul

lemma is_bounded_bilinear_map_comp :
  is_bounded_bilinear_map k (λ(p : (E →L[k] F) × (F →L[k] G)), p.2.comp p.1) :=
{ add_left := λx₁ x₂ y, begin
      ext z,
      change y (x₁ z + x₂ z) = y (x₁ z) + y (x₂ z),
      rw y.map_add
    end,
  smul_left := λc x y, begin
      ext z,
      change y (c • (x z)) = c • y (x z),
      rw bounded_linear_map.map_smul
    end,
  add_right := λx y₁ y₂, rfl,
  smul_right := λc x y, rfl,
  bound := ⟨1, zero_lt_one, λx y, calc
    ∥bounded_linear_map.comp ((x, y).snd) ((x, y).fst)∥
      ≤ ∥y∥ * ∥x∥ : bounded_linear_map.op_norm_comp_le _ _
    ... = 1 * ∥x∥ * ∥ y∥ : by ring ⟩ }

/-- Definition of the derivative of a bilinear map `f`, given at a point `p` by
`q ↦ f(p.1, q.2) + f(q.1, p.2)` as in the standard formula for the derivative of a product.
We define this function here a bounded linear map from `E × F` to `G`. The fact that this
is indeed the derivative of `f` is proved in `is_bounded_bilinear_map.has_fderiv_at` in
`deriv.lean`-/
def is_bounded_bilinear_map.deriv (h : is_bounded_bilinear_map k f) (p : E × F) : (E × F) →L[k] G :=
{ to_fun := λq, f (p.1, q.2) + f (q.1, p.2),
  add := λq₁ q₂, begin
    change f (p.1, q₁.2 + q₂.2) + f (q₁.1 + q₂.1, p.2) =
      f (p.1, q₁.2) + f (q₁.1, p.2) + (f (p.1, q₂.2) + f (q₂.1, p.2)),
    simp [h.add_left, h.add_right]
  end,
  smul := λc q, begin
    change f (p.1, c • q.2) + f (c • q.1, p.2) = c • (f (p.1, q.2) + f (q.1, p.2)),
    simp [h.smul_left, h.smul_right, smul_add]
  end,
  bound := begin
    rcases h.bound with ⟨C, Cpos, hC⟩,
    refine exists_pos_bound_of_bound (C * ∥p.1∥ + C * ∥p.2∥) (λq, _),
    calc ∥f (p.1, q.2) + f (q.1, p.2)∥
      ≤ ∥f (p.1, q.2)∥ + ∥f (q.1, p.2)∥ : norm_triangle _ _
    ... ≤ C * ∥p.1∥ * ∥q.2∥ + C * ∥q.1∥ * ∥p.2∥ : add_le_add (hC _ _) (hC _ _)
    ... ≤ C * ∥p.1∥ * ∥q∥ + C * ∥q∥ * ∥p.2∥ : begin
       apply add_le_add,
       exact mul_le_mul_of_nonneg_left (le_max_right _ _) (mul_nonneg (le_of_lt Cpos) (norm_nonneg _)),
       apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
       exact mul_le_mul_of_nonneg_left (le_max_left _ _) (le_of_lt Cpos),
    end
    ... = (C * ∥p.1∥ + C * ∥p.2∥) * ∥q∥ : by ring
  end }

/-- Given a bounded bilinear map `f`, the map associating to a point `p` the derivative of `f` at
`p` is itself a bounded linear map. -/
lemma is_bounded_bilinear_map.is_bounded_linear_map_deriv (h : is_bounded_bilinear_map k f) :
  is_bounded_linear_map k (λp : E × F, h.deriv p) :=
begin
  rcases h.bound with ⟨C, Cpos, hC⟩,
  refine is_linear_map.with_bound ⟨λp₁ p₂, _, λc p, _⟩ (C + C) (λp, _),
  { ext q,
    change f (p₁.1 + p₂.1, q.2) + f (q.1, p₁.2 + p₂.2) =
      (f (p₁.1, q.2) + f (q.1, p₁.2)) + ((f (p₂.1, q.2) + f (q.1, p₂.2))),
    simp [h.add_left, h.add_right] },
  { ext q,
    change f (c • p.1, q.2) + f (q.1, c • p.2) = c • (f (p.1, q.2) + f (q.1, p.2)),
    simp [h.smul_left, h.smul_right, smul_add] },
  { dunfold is_bounded_bilinear_map.deriv,
    refine bounded_linear_map.op_norm_le_bound _
      (mul_nonneg (add_nonneg (le_of_lt Cpos) (le_of_lt Cpos)) (norm_nonneg _)) (λq, _),
    calc ∥f (p.1, q.2) + f (q.1, p.2)∥
      ≤ ∥f (p.1, q.2)∥ + ∥f (q.1, p.2)∥ : norm_triangle _ _
    ... ≤ C * ∥p.1∥ * ∥q.2∥ + C * ∥q.1∥ * ∥p.2∥ : add_le_add (hC _ _) (hC _ _)
    ... ≤ C * ∥p∥ * ∥q∥ + C * ∥q∥ * ∥p∥ : by apply_rules [add_le_add, mul_le_mul, norm_nonneg,
      le_of_lt Cpos, le_refl, le_max_left, le_max_right, mul_nonneg, norm_nonneg, norm_nonneg,
      norm_nonneg]
    ... = (C + C) * ∥p∥ * ∥q∥ : by ring },
end

end bilinear_map
