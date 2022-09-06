/-
Copyright (c) 2022 Filippo A. E. Nuccio Mortarino Majno di Capriglio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import topology.compact_open
import topology.homotopy.path

universes u v

noncomputable theory

open_locale unit_interval

namespace unit_interval

/- first simplify the most advanced proofs, then check
  whether these preliminary lemmas are still necessary. -/
@[simp] lemma univ_eq_ge_zero {θ : ℝ} (h : θ ≤ 0): {s : I | θ ≤ (s : ℝ)} = set.univ :=
set.eq_univ_iff_forall.2 $ λ _, h.trans (nonneg _)

@[simp] lemma univ_eq_le_one {θ : ℝ} (h : 1 ≤ θ) : {s : I | (s : ℝ) ≤ θ} = set.univ :=
set.eq_univ_iff_forall.2 $ λ _, (le_one _).trans h

lemma mem_closure_iff {θ : ℝ} {t : I} : t ∈ closure {s : I | (s : ℝ) ≤ θ} ↔ (t : ℝ) ≤ θ :=
by {rw [(is_closed_le continuous_induced_dom continuous_const).closure_eq, set.mem_set_of_eq],
  apply_instance}

lemma not_mem_interior {θ : ℝ} {t : I} : t ∉ interior {s : I | (s : ℝ) ≤ θ} → θ ≤ t :=
begin
  -- For `θ = 1` the set `{s : ↥I | (s : ℝ) ≤ θ}` is the whole `I`, whose interior (in the induced
  -- topology) is `I` again, and `t ∉ interior I = I` is always false, whereas `1 ≤ t` is true for
  -- `t = 1`. So we split the proof in the cases `1 ≤ θ` and `θ < 1`.
  by_cases h_θ_1 : 1 ≤ θ,
  { rw [univ_eq_le_one h_θ_1, interior_univ],
    tauto/-to be replaced-/ },
  intro h,
  by_cases h_θ_0 : 0 ≤ θ,
  { let θI : I := ⟨θ, set.mem_Icc.mpr ⟨h_θ_0, le_of_lt $ lt_of_not_ge h_θ_1⟩⟩,
    have : {s : ↥I | (s : ℝ) ≤ θ} = set.Iic θI := rfl,
    have H_ne : (set.Ioi θI).nonempty := ⟨1, _⟩,
    simpa only [this, interior_Iic' H_ne, ← set.Iio_def, set.mem_set_of_eq, not_lt,
      ← subtype.coe_le_coe] using h,
    simpa only [set.mem_Ioi, ← subtype.coe_lt_coe, subtype.coe_mk, set.Icc.coe_one] using
      lt_of_not_ge h_θ_1, },
  { exact le_of_lt (lt_of_lt_of_le (lt_of_not_ge h_θ_0) t.2.1) },
end

lemma mem_frontier {θ : ℝ} {t : I} : t ∈ frontier (λ i : I, (i : ℝ) ≤ θ) → (t : ℝ) = θ :=
λ ⟨hl, hr⟩, by simp only [le_antisymm (not_mem_interior hr) (mem_closure_iff.mp hl)]

lemma one_add_pos {t : I} : 0 < (1 + t : ℝ) := add_pos_of_pos_of_nonneg zero_lt_one $ nonneg _

end unit_interval

namespace path

open continuous_map path

variables {X : Type u} [topological_space X]

instance {x y : X} : has_coe (path x y) C(I, X) := ⟨λ γ, γ.1⟩

instance {x y : X} : topological_space (path x y) :=
topological_space.induced (coe : _ → C(I, X)) continuous_map.compact_open

lemma continuous_eval {x y : X} : continuous (λ p : path x y × I, p.1 p.2) :=
continuous_eval'.comp $ continuous_induced_dom.prod_map continuous_id

@[continuity] lemma _root_.continuous.path_eval {x y : X} {Y} [topological_space Y]
  {f : Y → path x y} {g : Y → I} (hf : continuous f) (hg : continuous g) :
  continuous (λ y, f y (g y)) := continuous.comp continuous_eval (hf.prod_mk hg)

section

variables {Y : Type v} [topological_space Y] {x y : X} {g : Y → path x y}

@[simp, continuity]
lemma continuous_to_path_of_to_C (h : continuous (↑g : Y → C(I,X))) : continuous g :=
continuous_induced_rng.mpr h

@[simp, continuity]
lemma continuous_to_path_of_continuous_uncurry
  (h : continuous (λ p : Y × I, g p.1 p.2)) : continuous g :=
continuous_induced_rng.mpr $ continuous_of_continuous_uncurry ↑g h

end

lemma continuous_trans {x y z : X} : continuous (λ ρ : path x y × path y z, ρ.1.trans ρ.2) :=
begin
  apply continuous_to_path_of_continuous_uncurry,
  apply continuous.piecewise,
  { rintro ⟨p, t⟩ h,
    change _ ∈ frontier (prod.snd ⁻¹' {s : I | (s : ℝ) ≤ 1 / 2}) at h,
    simp only [← set.univ_prod, frontier_prod_eq, frontier_univ, closure_univ, set.empty_prod,
      set.union_empty, set.prod_mk_mem_set_prod_eq, set.mem_univ, true_and] at h,
    simp only [unit_interval.mem_frontier h, set.right_mem_Icc, zero_le_one, one_div,
      mul_inv_cancel_of_invertible, extend_extends, set.Icc.mk_one, path.target,
      set.left_mem_Icc, sub_self, set.Icc.mk_zero, path.source] },
  all_goals { refine continuous.path_extend
    ((continuous.comp _ $ continuous_fst.comp continuous_fst).path_eval continuous_snd) _ },
  exacts [continuous_fst, by continuity, continuous_snd, by continuity],
end

end path

open path continuous_map set.Icc

class H_space (X : Type u) [topological_space X] :=
(Hmul : C(X × X, X))
(e : X)
(Hmul_e_e : Hmul (e, e) = e)
(left_Hmul_e : (continuous_map.id X).homotopy_rel
  (Hmul.comp $ (const X e).prod_mk $ continuous_map.id X) {e})
(right_Hmul_e : (continuous_map.id X).homotopy_rel
  (Hmul.comp $ (continuous_map.id X).prod_mk $ const X e) {e})

@[reducible] def H_space.Hmul' (X : Type u) [topological_space X] [H_space X] (x y : X) :=
H_space.Hmul (x, y)
infix ` ∧ₕ `:65 := H_space.Hmul'

namespace H_space

section topological_group_H_space

@[to_additive] instance topological_group (G : Type u) [topological_space G] [group G]
  [topological_group G] : H_space G :=
{ Hmul := ⟨function.uncurry has_mul.mul, continuous_mul⟩,
  e := 1,
  Hmul_e_e := one_mul 1,
  left_Hmul_e := (homotopy_rel.refl _ _).cast (by {ext1, apply one_mul}) rfl,
  right_Hmul_e := (homotopy_rel.refl _ _).cast (by {ext1, apply mul_one}) rfl }

lemma Hmul_e {G : Type u} [topological_space G] [group G] [topological_group G] :
  (1 : G) = H_space.e := rfl

end topological_group_H_space

section path_space_H_space

open unit_interval path

variables {X : Type u} [topological_space X]

notation ` Ω(` x `)` := path x x

/- `Q_right` is analogous to the function `Q` defined on p. 475 of Serre's `Homologie`
  `singulière des espaces fibrés` that helps proving continuity of `delayed_refl_right`.-/
def Q_right (p : I × I) : I := set.proj_Icc 0 1 zero_le_one (2 * p.1 / (1 + p.2))

lemma continuous_Q_right : continuous Q_right :=
continuous_proj_Icc.comp $ continuous.div (by continuity) (by continuity) (λ x, one_add_pos.ne')

lemma Q_right_zero_left (θ : I) : Q_right (0, θ) = 0 :=
set.proj_Icc_of_le_left _ $ by simp only [coe_zero, mul_zero, zero_div]

lemma Q_right_one_left (θ : I) : Q_right (1, θ) = 1 :=
set.proj_Icc_of_right_le _ $ (le_div_iff one_add_pos).2 $
  by { dsimp only, rw [coe_one, one_mul, mul_one], apply add_le_add_left (le_one _) }

lemma Q_right_zero_right (t : I) : (Q_right (t, 0) : ℝ) = if (t : ℝ) ≤ 1 / 2 then 2 * t else 1 :=
begin
  simp only [Q_right, coe_zero, add_zero, div_one],
  split_ifs,
  { rw set.proj_Icc_of_mem _ ((mul_pos_mem_iff zero_lt_two).2 _), exacts [rfl, ⟨t.2.1, h⟩] },
  { rw (set.proj_Icc_eq_right _).2, { refl }, { linarith }, { exact zero_lt_one } },
end

lemma Q_right_one_right (t : I) : Q_right (t, 1) = t :=
eq.trans (by {rw Q_right, congr, apply mul_div_cancel_left, exact two_ne_zero}) $
  set.proj_Icc_coe zero_le_one _

variables {x y : X}

/- This is the function analogous to the one on p. 475 of Serre's *Homologie singulière des espaces
  fibrés*, defining a homotopy from the product path `e ∧ γ` to `γ`.-/
def delayed_refl_right (θ : I) (γ : path x y) : path x y :=
{ to_fun := λ t, γ (Q_right (t, θ)),
  continuous_to_fun := γ.continuous.comp (continuous_Q_right.comp $ continuous.prod.mk_left θ),
  source' := by { dsimp only, rw [Q_right_zero_left, γ.source] },
  target' := by { dsimp only, rw [Q_right_one_left, γ.target] } }

lemma continuous_delayed_refl_right {x : X} :
  continuous (λ p : I × path x y, delayed_refl_right p.1 p.2) :=
continuous_to_path_of_continuous_uncurry $ (continuous_snd.comp continuous_fst).path_eval
  (continuous_Q_right.comp $ continuous_snd.prod_mk $ continuous_fst.comp continuous_fst)

def delayed_refl_left {x : X} (θ : I) (γ : path x y) : path x y :=
(delayed_refl_right (unit_interval.symm θ) γ.symm).symm

lemma delayed_refl_right_zero (γ : path x y) : delayed_refl_right 0 γ = γ.trans (path.refl y) :=
begin
  ext t,
  simp only [delayed_refl_right,
    trans_apply, refl_extend, path.coe_mk, function.comp_app, refl_apply],
  split_ifs, swap, conv_rhs { rw ← γ.target },
  all_goals { apply congr_arg γ, ext1, rw Q_right_zero_right },
  exacts [if_neg h, if_pos h],
end

lemma delayed_refl_right_one (γ : path x y) : delayed_refl_right 1 γ = γ :=
by { ext t, exact congr_arg γ (Q_right_one_right t) }

lemma delayed_refl_right_e (θ : I) : delayed_refl_right θ (refl x) = refl x := rfl

instance loop_space_is_H_space (x : X) : H_space Ω(x) :=
{ Hmul := ⟨λ ρ, ρ.1.trans ρ.2, continuous_trans⟩,
  e := refl x,
  Hmul_e_e := refl_trans_refl,
  left_Hmul_e := sorry,
  right_Hmul_e := homotopy_rel.symm
  { to_homotopy := ⟨⟨λ p, delayed_refl_right p.1 p.2, continuous_delayed_refl_right⟩,
      delayed_refl_right_zero, delayed_refl_right_one⟩,
    prop' := begin
      rintros t _ (rfl : _ = _),
      simp only [continuous_map.coe_mk, delayed_refl_right_e],
      exact ⟨refl_trans_refl.symm, rfl⟩,
    end } }

end path_space_H_space

end H_space
