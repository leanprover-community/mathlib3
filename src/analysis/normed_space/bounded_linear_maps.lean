/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Continuous linear functions -- functions between normed vector spaces which are bounded and linear.
-/
import algebra.field
import ring_theory.algebra
import analysis.normed_space.basic
import ..asymptotics

@[simp] lemma mul_inv_eq' {α} [discrete_field α] (a b : α) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
classical.by_cases (assume : a = 0, by simp [this]) $ assume ha,
classical.by_cases (assume : b = 0, by simp [this]) $ assume hb,
mul_inv_eq hb ha

noncomputable theory
local attribute [instance] classical.prop_decidable
set_option class.instance_max_depth 43

local notation f ` →_{`:50 a `} `:0 b := filter.tendsto f (nhds a) (nhds b)

open filter (tendsto)
open metric

structure bounded_linear_map (k : Type*) [normed_field k]
  (E : Type*) [normed_space k E] (F : Type*) [normed_space k F]
  extends linear_map k E F :=
(bounded : ∃ M, ∀ x : E, ∥to_fun x∥ ≤ M * ∥x∥)

notation β ` →L[`:25 α `] ` γ := bounded_linear_map α β γ

variables {k : Type*} [normed_field k]
variables {E : Type*} [normed_space k E]
variables {F : Type*} [normed_space k F]
variables {G : Type*} [normed_space k G]

namespace bounded_linear_map

instance : has_coe (E →L[k] F) (E →ₗ[k] F) := ⟨to_linear_map⟩

instance : has_coe_to_fun (E →L[k] F) := ⟨_, λ f, f.to_fun⟩

@[extensionality] theorem ext {f g : E →L[k] F} (h : ∀ x, f x = g x) : f = g :=
  by cases f; cases g; congr' 1; ext x; apply h

theorem ext_iff {f g : E →L[k] F} : f = g ↔ ∀ x, f x = g x :=
  ⟨λ h x, by rintro; rw h, ext⟩

variables (f g : E →L[k] F) (c : k) (u v : E)

@[simp] lemma map_zero : f 0 = 0 := linear_map.map_zero _
@[simp] lemma map_add  : f (u + v) = f u + f v :=
  by erw linear_map.map_add; refl

@[simp] lemma map_sub  : f (u - v) = f u - f v :=
  by erw linear_map.map_sub; refl

@[simp] lemma map_smul : f (c • u) = c • f u :=
  by erw linear_map.map_smul; refl

@[simp] lemma map_neg  : f (-u) = - (f u) :=
  by erw linear_map.map_neg; refl


lemma has_pos_bound : ∃ M > 0, ∀ x, ∥f x∥ ≤ M * ∥x∥ :=
  let ⟨M, hf⟩ := f.bounded in
  ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left 1 _), λ _, le_trans
  (hf _) (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))⟩

lemma ratio_has_pos_bound : ∃ M > 0, ∀ x, ∥f x∥ / ∥x∥ ≤ M :=
  let ⟨M, hMp, hMb⟩ := has_pos_bound f in ⟨M, hMp,
  λ x, or.elim (lt_or_eq_of_le (norm_nonneg x))
  (λ hlt, div_le_of_le_mul hlt (by rw mul_comm; exact hMb x))
  (λ heq, by rw [←heq, div_zero]; exact le_of_lt hMp)⟩

def of_linear_map_of_bounded {f : E →ₗ[k] F}
  (h : ∃ M, ∀ x, ∥f x∥ ≤ M * ∥x∥) : E →L[k] F := ⟨f, h⟩

/-- the zero map is bounded.     -/
def zero : E →L[k] F := ⟨0, 0, λ x, by rw zero_mul; exact le_of_eq norm_zero⟩
/-- the identity map is bounded. -/
def id   : E →L[k] E := ⟨linear_map.id, 1, λ x, le_of_eq (one_mul _).symm⟩

/-- the composition of two bounded linear maps is bounded. -/
def comp (g : F →L[k] G) (f : E →L[k] F) : E →L[k] G :=
  ⟨linear_map.comp g.to_linear_map f.to_linear_map,
  let ⟨Mg, hMgp, hMgb⟩ := has_pos_bound g in
  let ⟨Mf, _, hMfb⟩ := has_pos_bound f in ⟨Mg * Mf, λ x, by rw mul_assoc;
  exact le_trans (hMgb _) ((mul_le_mul_left hMgp).2 (hMfb _))⟩⟩

instance : has_zero (E →L[k] F) := ⟨zero⟩
instance : has_one (bounded_linear_map k E E) := ⟨id⟩

instance : has_mul (bounded_linear_map k E E) := ⟨comp⟩

instance : has_add (E →L[k] F) :=
  ⟨λ f g, ⟨f + g, let ⟨Mg, hMg⟩ := g.bounded in
  let ⟨Mf, hMf⟩ := f.bounded in ⟨Mf + Mg, λ x,
  calc _ ≤ ∥f x∥ + ∥g x∥       : norm_triangle _ _
...      ≤ Mf * ∥x∥ + Mg * ∥x∥ : add_le_add (hMf _) (hMg _)
...      = (Mf + Mg) * ∥x∥     : (add_mul _ _ _).symm ⟩⟩⟩

instance : has_scalar k (E →L[k] F) :=
  ⟨λ c f, ⟨c • f, let ⟨M, hM⟩ := f.bounded in ⟨∥c∥ * M,
  λ x, by rw mul_assoc; exact (norm_smul c (f x)).symm ▸
  (mul_le_mul_of_nonneg_left (hM x) (norm_nonneg c))⟩⟩⟩

instance : has_neg (E →L[k] F) := ⟨λ f, (-1 : k) • f⟩
instance : has_sub (E →L[k] F) := ⟨λ f g, f + (-g)⟩

@[simp] lemma zero_apply : (0 : E →L[k] F) u = 0 := linear_map.zero_apply _
@[simp] lemma id_apply   : (1 : E →L[k] E) u = u := linear_map.id_apply _

@[simp] lemma add_apply  : (f + g) u = f u + g u := linear_map.add_apply _ _ _
@[simp] lemma smul_apply : (c • f) u = c • (f u) := linear_map.smul_apply _ _ _
@[simp] lemma neg_apply  : (-f) u = - (f u) :=
  by erw [smul_apply, neg_smul, one_smul]

instance to_add_comm_group : add_comm_group (E →L[k] F) := {
  add       := (+),
  add_assoc := λ _ _ _, ext $ λ _, add_assoc _ _ _,
  add_comm  := λ _ _, ext $ λ _, add_comm _ _,
  zero      := 0,
  add_zero  := λ _, ext $ λ _, add_zero _,
  zero_add  := λ _, ext $ λ _, zero_add _,
  neg       := λ f, -f,
  add_left_neg := λ f, ext $ λ x, have t: (-1 : k) • f x + f x = 0, from
    by rw neg_one_smul; exact add_left_neg _, t
}

instance : vector_space k (E →L[k] F) := {
  smul_zero := λ _, ext $ λ _, smul_zero _,
  zero_smul := λ _, ext $ λ _, zero_smul _ _,
  one_smul  := λ _, ext $ λ _, one_smul _ _,
  mul_smul  := λ _ _ _, ext $ λ _, mul_smul _ _ _,
  add_smul  := λ _ _ _, ext $ λ _, add_smul _ _ _,
  smul_add  := λ _ _ _, ext $ λ _, smul_add _ _ _
}

instance : ring (E →L[k] E) := {
  mul := (*),
  one := 1,
  mul_one := λ _, ext $ λ _, rfl,
  one_mul := λ _, ext $ λ _, rfl,
  mul_assoc := λ _ _ _, ext $ λ _, rfl,
  left_distrib := λ _ _ _, ext $ λ _, map_add _ _ _,
  right_distrib := λ _ _ _, ext $ λ _, linear_map.add_apply _ _ _,

  .. bounded_linear_map.to_add_comm_group
}

instance : is_ring_hom (λ c : k, c • (1 : E →L[k] E)) := {
  map_one := one_smul _ _,
  map_add := λ _ _, ext $ λ _, add_smul _ _ _,
  map_mul := λ _ _, ext $ λ _, mul_smul _ _ _,
}

instance : algebra k (E →L[k] E) := {
  to_fun    := λ c, c • 1,
  smul_def' := λ _ _, rfl,
  commutes' := λ _ _, ext $ λ _, map_smul _ _ _,
}

/-- bounded linear maps are continuous. -/
lemma tendsto (x : E): f →_{x} (f x) :=
  tendsto_iff_norm_tendsto_zero.2 $ let ⟨M, hf⟩ := f.bounded in
  (squeeze_zero (λ _, norm_nonneg _)
  (λ t, by rw ←map_sub; exact hf _ : ∀ t, ∥f t - f x∥ ≤ M * ∥t - x∥)
  ((mul_zero M) ▸ (tendsto_mul tendsto_const_nhds (lim_norm _))))

protected theorem continuous : continuous f :=
  continuous_iff_continuous_at.2 (tendsto f)

-- asymptotic properties of bounded linear maps
section
  open asymptotics filter
  variable l : filter E

  theorem is_O_id : is_O f (λ x, x) l :=
  let ⟨M, Mp, hM⟩ := f.has_pos_bound in
  ⟨M, Mp, sets_of_superset _ univ_mem_sets $ λ x _, hM x⟩

  theorem is_O_comp (f : F →L[k] G) {g : E → F} : is_O (f ∘ g) g l :=
    ((f.is_O_id _).comp _).mono (map_le_iff_le_comap.1 lattice.le_top)

  theorem is_O_sub (x : E) : is_O (λ x', f (x' - x)) (λ x', x' - x) l :=
    is_O_comp _ _
end

end bounded_linear_map


-- deriv.lean is dependent on `is_bounded_linear_map`
-- and has not yet been refactored.

structure is_bounded_linear_map (k : Type*)
  [normed_field k] {E : Type*} [normed_space k E] {F : Type*} [normed_space k F] (L : E → F)
  extends is_linear_map k L : Prop :=
(bound : ∃ M, M > 0 ∧ ∀ x : E, ∥ L x ∥ ≤ M * ∥ x ∥)

include k

lemma is_linear_map.with_bound
  {L : E → F} (hf : is_linear_map k L) (M : ℝ) (h : ∀ x : E, ∥ L x ∥ ≤ M * ∥ x ∥) :
  is_bounded_linear_map k L :=
⟨ hf, classical.by_cases
  (assume : M ≤ 0, ⟨1, zero_lt_one, assume x,
    le_trans (h x) $ mul_le_mul_of_nonneg_right (le_trans this zero_le_one) (norm_nonneg x)⟩)
  (assume : ¬ M ≤ 0, ⟨M, lt_of_not_ge this, h⟩)⟩

namespace is_bounded_linear_map

def to_linear_map (f : E → F) (h : is_bounded_linear_map k f) : E →ₗ[k] F :=
(is_linear_map.mk' _ h.to_is_linear_map)

lemma zero : is_bounded_linear_map k (λ (x:E), (0:F)) :=
(0 : E →ₗ F).is_linear.with_bound 0 $ by simp [le_refl]

lemma id : is_bounded_linear_map k (λ (x:E), x) :=
linear_map.id.is_linear.with_bound 1 $ by simp [le_refl]

set_option class.instance_max_depth 43
lemma smul {f : E → F} (c : k) : is_bounded_linear_map k f → is_bounded_linear_map k (λ e, c • f e)
| ⟨hf, ⟨M, hM, h⟩⟩ := (c • hf.mk' f).is_linear.with_bound (∥c∥ * M) $ assume x,
  calc ∥c • f x∥ = ∥c∥ * ∥f x∥ : norm_smul c (f x)
    ... ≤ ∥c∥ * (M * ∥x∥) : mul_le_mul_of_nonneg_left (h x) (norm_nonneg c)
    ... = (∥c∥ * M) * ∥x∥ : (mul_assoc _ _ _).symm

lemma neg {f : E → F} (hf : is_bounded_linear_map k f) : is_bounded_linear_map k (λ e, -f e) :=
begin
  rw show (λ e, -f e) = (λ e, (-1 : k) • f e), { funext, simp },
  exact smul (-1) hf
end

lemma add {f : E → F} {g : E → F} :
  is_bounded_linear_map k f → is_bounded_linear_map k g → is_bounded_linear_map k (λ e, f e + g e)
| ⟨hlf, Mf, hMf, hf⟩  ⟨hlg, Mg, hMg, hg⟩ := (hlf.mk' _ + hlg.mk' _).is_linear.with_bound (Mf + Mg) $ assume x,
  calc ∥f x + g x∥ ≤ ∥f x∥ + ∥g x∥ : norm_triangle _ _
    ... ≤ Mf * ∥x∥ + Mg * ∥x∥ : add_le_add (hf x) (hg x)
    ... ≤ (Mf + Mg) * ∥x∥ : by rw add_mul

lemma sub {f : E → F} {g : E → F} (hf : is_bounded_linear_map k f) (hg : is_bounded_linear_map k g) :
  is_bounded_linear_map k (λ e, f e - g e) := add hf (neg hg)

lemma comp {f : E → F} {g : F → G} :
  is_bounded_linear_map k g → is_bounded_linear_map k f → is_bounded_linear_map k (g ∘ f)
| ⟨hlg, Mg, hMg, hg⟩ ⟨hlf, Mf, hMf, hf⟩ := ((hlg.mk' _).comp (hlf.mk' _)).is_linear.with_bound (Mg * Mf) $ assume x,
  calc ∥g (f x)∥ ≤ Mg * ∥f x∥ : hg _
    ... ≤ Mg * (Mf * ∥x∥) : mul_le_mul_of_nonneg_left (hf _) (le_of_lt hMg)
    ... = Mg * Mf * ∥x∥ : (mul_assoc _ _ _).symm

lemma tendsto {L : E → F} (x : E) : is_bounded_linear_map k L → L →_{x} (L x)
| ⟨hL, M, hM, h_ineq⟩ := tendsto_iff_norm_tendsto_zero.2 $
  squeeze_zero (assume e, norm_nonneg _)
    (assume e, calc ∥L e - L x∥ = ∥hL.mk' L (e - x)∥ : by rw (hL.mk' _).map_sub e x; refl
      ... ≤ M*∥e-x∥ : h_ineq (e-x))
    (suffices (λ (e : E), M * ∥e - x∥) →_{x} (M * 0), by simpa,
      tendsto_mul tendsto_const_nhds (lim_norm _))

lemma continuous {L : E → F} (hL : is_bounded_linear_map k L) : continuous L :=
continuous_iff_continuous_at.2 $ assume x, hL.tendsto x

lemma lim_zero_bounded_linear_map {L : E → F} (H : is_bounded_linear_map k L) : (L →_{0} 0) :=
(H.1.mk' _).map_zero ▸ continuous_iff_continuous_at.1 H.continuous 0

section
open asymptotics filter

theorem is_O_id {L : E → F} (h : is_bounded_linear_map k L) (l : filter E) :
  is_O L (λ x, x) l :=
let ⟨M, Mpos, hM⟩ := h.bound in
⟨M, Mpos, mem_sets_of_superset univ_mem_sets (λ x _, hM x)⟩

theorem is_O_comp {L : F → G} (h : is_bounded_linear_map k L)
  {f : E → F} (l : filter E) : is_O (λ x', L (f x')) f l :=
((h.is_O_id ⊤).comp _).mono (map_le_iff_le_comap.mp lattice.le_top)

theorem is_O_sub {L : E → F} (h : is_bounded_linear_map k L) (l : filter E) (x : E) :
  is_O (λ x', L (x' - x)) (λ x', x' - x) l :=
is_O_comp h l

end

end is_bounded_linear_map

set_option class.instance_max_depth 34

-- Next lemma is stated for real normed space but it would work as soon as the base field is an extension of ℝ
lemma bounded_continuous_linear_map
  {E : Type*} [normed_space ℝ E] {F : Type*} [normed_space ℝ F] {L : E → F}
  (lin : is_linear_map ℝ L) (cont : continuous L) : is_bounded_linear_map ℝ L :=
let ⟨δ, δ_pos, hδ⟩ := exists_delta_of_continuous cont zero_lt_one 0 in
have HL0 : L 0 = 0, from (lin.mk' _).map_zero,
have H : ∀{a}, ∥a∥ ≤ δ → ∥L a∥ < 1, by simpa only [HL0, dist_zero_right] using hδ,
lin.with_bound (δ⁻¹) $ assume x,
classical.by_cases (assume : x = 0, by simp only [this, HL0, norm_zero, mul_zero]) $
assume h : x ≠ 0,
let p := ∥x∥ * δ⁻¹, q := p⁻¹ in
have p_inv : p⁻¹ = δ*∥x∥⁻¹, by simp,

have norm_x_pos : ∥x∥ > 0 := (norm_pos_iff x).2 h,
have norm_x : ∥x∥ ≠ 0 := mt (norm_eq_zero x).1 h,

have p_pos : p > 0 := mul_pos norm_x_pos (inv_pos δ_pos),
have p0 : _ := ne_of_gt p_pos,
have q_pos : q > 0 := inv_pos p_pos,
have q0 : _ := ne_of_gt q_pos,

have ∥p⁻¹ • x∥ = δ := calc
  ∥p⁻¹ • x∥ = abs p⁻¹ * ∥x∥ : by rw norm_smul; refl
  ... = p⁻¹ * ∥x∥ : by rw [abs_of_nonneg $ le_of_lt q_pos]
  ... = δ : by simp [mul_assoc, inv_mul_cancel norm_x],

calc ∥L x∥ = (p * q) * ∥L x∥ : begin dsimp [q], rw [mul_inv_cancel p0, one_mul] end
  ... = p * ∥L (q • x)∥ : by simp [lin.smul, norm_smul, real.norm_eq_abs, abs_of_pos q_pos, mul_assoc]
  ... ≤ p * 1 : mul_le_mul_of_nonneg_left (le_of_lt $ H $ le_of_eq $ this) (le_of_lt p_pos)
  ... = δ⁻¹ * ∥x∥ : by rw [mul_one, mul_comm]
