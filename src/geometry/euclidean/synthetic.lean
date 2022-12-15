/-
Copyright (c) 2022 André Hernandez-Espiet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : André Hernandez-Espiet
-/

import data.real.basic
import data.set.finite
import data.matrix.basic
import data.real.sqrt

/-!
# Synthetic Geometry, Euclid's Elements Book I using Avigad Axioms
In this file we ...

## Main definitions
* `incidence_geometry` : class containing axioms...

## Main results
* `pythagorean_theorem` : The Pythagorean theorem
## Tags
synthetic geometry, Euclid elements
-/

universes u1 u2 u3
class incidence_geometry :=
(point : Type u1)
(line : Type u2)
(circle : Type u3)

(online : point → line → Prop)
(sameside : point → point → line → Prop)
(B : point → point → point → Prop) -- Betweenness
(oncircle : point → circle → Prop)
(in_circ : point → circle → Prop)
(cen_circ : point → circle → Prop)
(lines_inter : line → line → Prop)
(line_circle_inter : line → circle → Prop)
(circles_inter : circle → circle → Prop)
(length : point → point → real)
(angle : point → point → point → real)
(rightangle : real)
(area : point → point → point → real)

(more_pts : ∀ (S : set point), S.finite → ∃ (a : point), a ∉ S)
(pt_B_of_ne : ∀ {b c : point}, b ≠ c → ∃ (a : point), B b a c) -- old (P3)
(pt_extension_of_ne : ∀ {b c : point}, b ≠ c → ∃ (a : point), B b c a)
(diffside_of_not_online : ∀ {L : line}, ∀ {b : point}, ¬online b L →
  ∃ (a : point), ¬online a L ∧ ¬sameside a b L)
(line_of_pts : ∀ (a b : point), ∃ (L :line), online a L ∧ online b L) -- old (LB_of_line_circle_inter)
(circle_of_ne : ∀ {a b : point}, a ≠ b → ∃ (α : circle),  oncircle b α ∧ cen_circ a α)
(pt_of_lines_inter : ∀ {L M : line}, lines_inter L M →
  ∃ (a : point), online a L ∧ online a M)
(pts_of_line_circle_inter : ∀ {L : line}, ∀ {α : circle}, line_circle_inter L α →
  ∃ (a b : point),  a ≠ b ∧ online a L ∧ online b L ∧ oncircle a α ∧ oncircle b α )
(pt_oncircle_of_inside_outside : ∀ {b c : point}, ∀ {α : circle},
  ¬oncircle c α →in_circ b α → ¬in_circ c α →
  ∃ (a : point), B b a c ∧ oncircle a α )
(pt_oncircle_of_inside_ne : ∀ {b c : point}, ∀ {α : circle}, b ≠ c →in_circ b α →
  ∃ (a : point), B a b c ∧ oncircle a α )
(pts_of_circles_inter : ∀ {α β : circle}, circles_inter α β →
  ∃ (a b : point), a≠ b∧ oncircle a α ∧ oncircle a β ∧ oncircle b α ∧ oncircle b β )
(pt_sameside_of_circles_inter : ∀ {b c d : point}, ∀ {L : line}, ∀ {α β : circle},
  online c L → online d L →¬online b L  → cen_circ c α → cen_circ d β →circles_inter α β
  →  ∃ (a : point), sameside a b L∧ oncircle a α ∧  oncircle a β )
(line_unique_of_pts : ∀ {a b : point}, ∀ {L M : line}, a ≠ b → online a L → online b L →
  online a M → online b M → L = M)
(center_circle_unique : ∀ {a b : point}, ∀ {α : circle}, cen_circ a α → cen_circ b α →
  a = b)
(inside_circle_of_center : ∀ {a : point}, ∀ {α : circle}, cen_circ a α → in_circ a α)
(not_oncircle_of_inside : ∀ {a : point}, ∀ {α : circle}, in_circ a α → ¬oncircle a α)
(B_symm : ∀ {a b c : point}, B a b c → B c b a )
(ne_12_of_B : ∀ {a b c : point}, B a b c → a ≠ b )
(ne_13_of_B : ∀ {a b c : point}, B a b c → a ≠ c)
(ne_23_of_B : ∀ {a b c : point}, B a b c → b ≠ c )
(not_B_of_B : ∀ {a b c : point}, B a b c → ¬B b a c)
(online_3_of_B : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → online b L → online c L)
(online_2_of_B : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → online c L → online b L)
(B124_of_B134_B123 : ∀ {a b c d : point}, B a b c → B a d b → B a d c)
(B124_of_B123_B234 : ∀ {a b c d : point}, B a b c → B b c d → B a b d)
(B_of_three_online_ne : ∀ {a b c : point}, ∀ {L : line}, a ≠ b → a ≠ c → b ≠ c → online a L →
  online b L → online c L →  B a b c ∨ B b a c ∨ B a c b)
(not_B324_of_B123_B124 : ∀ {a b c d : point}, B a b c → B a b d → ¬B c b d)
(sameside_rfl_of_not_online : ∀ {a : point}, ∀ {L : line}, ¬online a L → sameside a a L)
(sameside_symm : ∀ {a b : point}, ∀ {L : line}, sameside a b L → sameside b a L)
(not_online_of_sameside : ∀ {a b : point}, ∀ {L : line}, sameside a b L → ¬online a L)
(sameside_trans : ∀ {a b c : point}, ∀ {L : line}, sameside a b L → sameside a c L → sameside b c L)
(sameside_or_of_diffside : ∀ {a b c : point}, ∀ {L : line}, ¬online a L → ¬online b L → ¬online c L →
  ¬sameside a b L → sameside a c L ∨ sameside b c L)
(sameside12_of_B123_sameside13 : ∀ {a b c : point}, ∀ {L : line}, B a b c → sameside a c L → sameside a b L)
(sameside23_of_B123_online1_not_online2 : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → ¬online b L → sameside b c L)
(not_sameside13_of_B123_online2 : ∀ {a b c : point}, ∀ {L : line}, B a b c → online b L → ¬sameside a c L)
(B_of_online_inter : ∀ {a b c : point}, ∀ {L M : line}, a ≠ b → b≠ c → a≠ c→ M≠ L → online a M → online b M → online c M →
  online b L →  ¬sameside a c L → B a b c)
(not_sameside_of_sameside_sameside : ∀ {a b c d : point}, ∀ {L M N : line}, online a L → online a M → online a N → online b L →
  online c M → online d N → sameside c d L → sameside b c N → ¬sameside b d M)
(sameside_of_sameside_not_sameside : ∀ {a b c d : point}, ∀ {L M N : line}, a≠ b → online a L → online a M → online a N → online b L →
  online c M → online d N → ¬online d M → sameside c d L → ¬sameside b d M →
  sameside b c N)
(B_of_line_circle_inter : ∀ {a b c : point}, ∀ {L : line}, ∀ {α : circle },b ≠ c → online a L → online b L → online c L
  → oncircle b α → oncircle c α → in_circ a α →   B b a c)
(not_sameside_of_circle_inter : ∀ {a b c d : point}, ∀ {L : line}, ∀ {α β : circle},  c ≠ d→ α ≠ β →  online a L
  → online b L  → oncircle c α → oncircle c β → oncircle d α → oncircle d β → cen_circ a α → cen_circ b β →
  circles_inter α β → ¬sameside c d L)
(lines_inter_of_not_sameside : ∀ {a b : point}, ∀ {L M : line}, online a M → online b M → ¬sameside a b L →
  lines_inter L M)
(line_circle_inter_of_not_sameside : ∀ {a b : point}, ∀ {L : line}, ∀ {α : circle},¬sameside a b L → oncircle a α ∨ in_circ a α→
 oncircle b α ∨ in_circ b α  →  line_circle_inter L α)
(line_circle_inter_of_inside_online : ∀ {a : point}, ∀ {L : line}, ∀ {α : circle}, online a L → in_circ a α →  line_circle_inter L α)
(circles_inter_of_inside_oncircle : ∀ {a b : point}, ∀ {α β : circle}, oncircle b α → oncircle a β → in_circ a α →  in_circ b β →
  circles_inter α β)
(length_eq_zero_iff : ∀ {a b : point}, length a b = 0 ↔ a = b)
(length_symm : ∀ (a b : point), length a b = length b a)
(angle_symm : ∀ (a b c : point), angle a b c = angle c b a) -- *** Discuss further ***
(angle_nonneg : ∀ (a b c : point), 0 ≤ angle a b c)
(length_nonneg : ∀ (a b : point), 0 ≤ length a b)
(degenerate_area : ∀ (a b : point), area a a b = 0)
(area_invariant : ∀ (a b c : point), area a b c = area c a b ∧ area a b c = area a c b)
(area_eq_of_SSS : ∀ {a b c a1 b1 c1 : point}, length a b = length a1 b1 → length b c = length b1 c1 →
  length c a = length c1 a1 → area a b c = area a1 b1 c1)
(length_sum_of_B : ∀ {a b c : point}, B a b c → length a b + length b c = length a c)
(oncircle_iff_length_eq : ∀ {a b c : point}, ∀ {α : circle},  oncircle b α → cen_circ a α →
  (length a b = length a c ↔ oncircle c α))
(incircle_iff_length_lt : ∀ {a b c : point}, ∀ {α : circle}, oncircle b α → cen_circ a α →
  (length a c < length a b ↔ in_circ c α))
(angle_zero_iff_online : ∀ {a b c : point}, ∀ {L : line}, a ≠ b → a ≠ c → online a L → online b L →
  (online c L ∧ ¬B b a c ↔ angle b a c = 0))--better reformulation?
(angle_add_iff_sameside : ∀ {a b c d : point}, ∀ {L M : line}, a ≠ b → a ≠ c → online a L → online b L → online a M
  → online c M → ¬online d M → ¬online d L → L ≠ M →
  (angle b a c = angle b a d + angle d a c ↔ sameside b d M ∧ sameside c d L))
(angle_eq_iff_rightangle : ∀ {a b c d : point}, ∀ {L : line}, online a L → online b L → ¬online d L → B a c b →
  (angle a c d = angle d c b ↔ angle a c d = rightangle))
(angle_extension : ∀ {a b c a1 b1 c1 : point}, ∀ {L M : line}, b ≠ a → b1 ≠ a → c ≠ a → c1 ≠ a → online a L → online b L → online b1 L →
  online a M → online c M → online c1 M →  ¬B b a b1 → ¬B c a c1 → angle b a c = angle b1 a1 c1)
(unparallel_postulate : ∀ {a b c d : point}, ∀ {L M N : line},b ≠ c → online a L → online b L → online b M → online c M →
  online c N → online d N →  sameside a d M → angle a b c + angle b c d < 2 * rightangle →
  ∃ (e : point), online e L ∧ online e N ∧ sameside e a M)
(area_zero_iff_online : ∀ {a b c : point}, ∀ {L : line},a ≠ b → online a L → online b L →
  (area a b c = 0 ↔ online c L))
(area_add_iff_B : ∀ {a b c d : point}, ∀ {L : line}, a ≠ b → b ≠ c → c ≠ a → online a L → online b L →
  online c L → ¬online d L → (B a c b ↔ area a c d + area d c b = area a d b))
(SAS_iff_SSS : ∀ {a b c d e f : point}, length a b = length d e → length a c = length d f →
  (angle b a c = angle e d f ↔ length b c = length e f)) --Euclid Prop 4,8

open incidence_geometry

----------------------

noncomputable theory

-- instantiation of axioms in ℝ × ℝ

instance incidence_geometry_ℝ_ℝ : incidence_geometry :=
{ point := fin 2 → ℝ,
  line := {L : fin 3 → ℝ // (L 0 > 0 ∧ (L 0)^2 + (L 1)^2 = 1) ∨ (L 0 = 0 ∧ L 1 = 1)},
  --{L : fin 3 → ℝ // L 0 = 1 ∨ (L 0 = 0 ∧ L 1 = 1)}, -- (x,y) is on line a x + b y = c
  circle := (fin 2 → ℝ) × {r : ℝ // 0 < r},
  online := λ a L, (L.1 0) * (a 0) + (L.1 1) * (a 1) - (L.1 2) = 0,
  sameside := λ a b L, 0 <
    ((L.1 0) * (a 0) + (L.1 1) * (a 1) - (L.1 2)) * ((L.1 0) * (b 0) + (L.1 1) * (b 1) - (L.1 2)),
  B := λ a b c, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ ∃ (μ : ℝ), 0 < μ ∧ (c - b) = μ • (b - a),
  oncircle := λ a α, (a 0 - α.1 0)^2 + (a 1 - α.1 1)^2 - (α.2.1)^2 = 0,
  in_circ := λ a α, (a 0 - α.1 0)^2 + (a 1 - α.1 1)^2 - (α.2.1)^2 < 0,
  cen_circ := λ a α, a = α.1,
  lines_inter := λ L M, L.1 0 * M.1 1 - L.1 1 * M.1 0 ≠ 0,
  line_circle_inter := λ L α, 0 < (α.2.1)^2 - (L.1 0 * α.1 0 + L.1 1 * α.1 1 - L.1 2)^2,
  circles_inter := sorry,
  length := sorry,
  angle := sorry,
  rightangle := sorry,
  area := sorry,
  more_pts := sorry,
  pt_B_of_ne := sorry,
  pt_extension_of_ne := sorry,
  diffside_of_not_online := sorry,
  line_of_pts := sorry,
  circle_of_ne := sorry,
  pt_of_lines_inter :=
  begin
    rintros ⟨L, hL⟩ ⟨M, hM⟩ inter,
    use ![(L 2 * M 1 - L 1 * M 2) / (L 0 * M 1 - L 1 * M 0),
      (L 0 * M 2 - L 2 * M 0) / (L 0 * M 1 - L 1 * M 0)],
    split; field_simp; ring,
  end,
  pts_of_line_circle_inter :=
  begin
    rintros ⟨L, hL⟩ ⟨c, ⟨r, r_pos⟩⟩ inter,
    simp only at inter,
    by_cases hL0 : L 0 = 0 ∨ L 1 = 0,
    { cases hL0 with hL0 hL0;
      rw hL0 at hL;
      simp only [gt_iff_lt, lt_self_iff_false, false_and, eq_self_iff_true, true_and, false_or,
        zero_pow', ne.def, bit0_eq_zero, nat.one_ne_zero, not_false_iff, add_zero, sq_eq_one_iff,
        zero_ne_one, and_false, or_false] at hL,
      { rw [hL0, hL] at inter,
        simp only [zero_mul, one_mul, zero_add] at inter,
        use ![c 0 + real.sqrt (r^2 - (c 1 - L 2)^2), L 2],
        use ![c 0 - real.sqrt (r^2 - (c 1 - L 2)^2), L 2],
        refine ⟨_, _, _, _, _⟩,
        { intros hh,
          have := congr_fun hh 0,
          simp only [matrix.cons_val_zero] at this,
          have sqrt_eq : real.sqrt (r ^ 2 - (c 1 - L 2) ^ 2) = 0,
          { have := sub_eq_zero.mpr this,
            simp only [add_sub_sub_cancel, add_self_eq_zero] at this,
            exact this, },
          have : 0 ≤ (r ^ 2 - (c 1 - L 2) ^ 2) := by linarith,
          have : r ^ 2 - (c 1 - L 2) ^ 2 = 0 := (real.sqrt_eq_zero this).mp sqrt_eq,
          linarith, },
        { simp only [matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons, hL0, hL],
          ring, },
        { simp only [matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons, hL0, hL],
          ring, },
        { simp only [matrix.cons_val_zero, add_tsub_cancel_left, matrix.cons_val_one,
            matrix.head_cons],
          rw @real.sq_sqrt (r ^ 2 - (c 1 - L 2) ^ 2) (by linarith),
          ring, },
        { simp only [matrix.cons_val_zero, sub_sub_cancel_left, neg_sq, matrix.cons_val_one,
            matrix.head_cons],
          rw @real.sq_sqrt (r ^ 2 - (c 1 - L 2) ^ 2) (by linarith),
          ring, }, },
      { have hL : L 0 = 1,
        { cases hL.2 with hh hh,
          { exact hh, },
          { exfalso,
            linarith, }, },
        rw [hL0, hL] at inter,
        simp only [one_mul, zero_mul, add_zero] at inter,
        use ![L 2, c 1 + real.sqrt (r^2 - (c 0 - L 2)^2)],
        use ![L 2, c 1 - real.sqrt (r^2 - (c 0 - L 2)^2)],
        refine ⟨_, _, _, _, _⟩,
        { intros hh,
          have := congr_fun hh 1,
          simp only [matrix.cons_val_one, matrix.head_cons] at this,
          have sqrt_eq : real.sqrt (r ^ 2 - (c 0 - L 2) ^ 2) = 0,
          { have := sub_eq_zero.mpr this,
            simp only [add_sub_sub_cancel, add_self_eq_zero] at this,
            exact this, },
          have : 0 ≤ (r ^ 2 - (c 0 - L 2) ^ 2) := by linarith,
          have : r ^ 2 - (c 0 - L 2) ^ 2 = 0 := (real.sqrt_eq_zero this).mp sqrt_eq,
          linarith, },
        { simp only [matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons, hL0, hL],
          ring, },
        { simp only [matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons, hL0, hL],
          ring, },
        { simp only [matrix.cons_val_zero, add_tsub_cancel_left, matrix.cons_val_one,
            matrix.head_cons],
          rw @real.sq_sqrt (r ^ 2 - (c 0 - L 2) ^ 2) (by linarith),
          ring, },
        { simp only [matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons,
            sub_sub_cancel_left, neg_sq],
          rw @real.sq_sqrt (r ^ 2 - (c 0 - L 2) ^ 2) (by linarith),
          ring, }, }, },
    { push_neg at hL0,
      simp only [hL0.1, gt_iff_lt, false_and, or_false] at hL,
      have L0_sq : L 0 ^ 2 = 1 - L 1 ^ 2,
        { apply sub_eq_zero.mp,
          rw [←sub_add, ←hL.2],
          ring, },
      have := hL0.2,
      let discr := real.sqrt((L 1)^2 * (r^2 - (L 0 * c 0 + L 1 * c 1 - L 2)^2)),
      have discr_ge_zero : 0 ≤ (L 1)^2 * (r^2 - (L 0 * c 0 + L 1 * c 1 - L 2)^2) :=
        mul_nonneg (sq_nonneg _) (le_of_lt inter),
      have discr_nonzero : discr ≠ 0,
      { intros hh,
        dsimp [discr] at hh,
        cases mul_eq_zero.mp
          ((@real.sqrt_eq_zero (L 1 ^ 2 * (r ^ 2 - (L 0 * c 0 + L 1 * c 1 - L 2) ^ 2))
            discr_ge_zero).mp hh) with hh hh,
        { rw sq_eq_zero_iff at hh,
          exact hL0.2 hh, },
        { rw hh at inter,
          exact (lt_self_iff_false _).mp inter, }, },
      have discr_sq : discr ^ 2 = (L 1)^2 * (r^2 - (L 0 * c 0 + L 1 * c 1 - L 2)^2) :=
        real.sq_sqrt discr_ge_zero,
/- MATHEMATICA CODE:
solns = (({x, y} /. Solve[ L[0] x + L[1] y == L[2] && (x - c[0])^2 + (y - c[1])^2 == r^2 , {x, y}]
  // Simplify) /. L[0]^2 + L[1]^2 -> 1) // Simplify;
TeXForm /@ solns[[1]]
TeXForm /@ solns[[2]]
-/
      use ![c 0 * (L 1)^2 - c 1 * L 0 * L 1 + L 0 * L 2 + discr,
        (c 1 * L 1 * (L 0)^2 - c 0 * (L 1)^2 * L 0 + (L 1)^2 * L 2 - L 0 * discr) / (L 1)],
      use ![c 0 * (L 1)^2 - c 1 * L 0 * L 1 + L 0 * L 2 - discr,
        (c 1 * L 1 * (L 0)^2 - c 0 * (L 1)^2 * L 0 + (L 1)^2 * L 2 + L 0 * discr) / (L 1)],
      refine ⟨_, _, _, _, _⟩,
      { intros hh,
        have := congr_fun hh 0,
        simp only [matrix.cons_val_zero] at this,
        have : discr = 0,
        { have := sub_eq_zero.mpr this,
          simp only [add_sub_sub_cancel, add_self_eq_zero] at this,
          exact this, },
        exact discr_nonzero this, },
      { simp only [matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons],
        field_simp,
        ring_nf,
        rw L0_sq,
        ring, },
      { simp only [matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons],
        field_simp,
        ring_nf,
        rw L0_sq,
        ring, },
      {
        simp only [matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons],
        field_simp,
        ring,
        rw L0_sq,
        ring,
        rw discr_sq,
        ring,
      },
    },

  end,
  pt_oncircle_of_inside_outside := sorry,
  pt_oncircle_of_inside_ne := sorry,
  pts_of_circles_inter := sorry,
  pt_sameside_of_circles_inter := sorry,
  line_unique_of_pts := sorry,
  center_circle_unique := sorry,
  inside_circle_of_center := sorry,
  not_oncircle_of_inside := sorry,
  B_symm := sorry,
  ne_12_of_B := sorry,
  ne_13_of_B := sorry,
  ne_23_of_B := sorry,
  not_B_of_B := sorry,
  online_3_of_B := sorry,
  online_2_of_B := sorry,
  B124_of_B134_B123 := sorry,
  B124_of_B123_B234 := sorry,
  B_of_three_online_ne := sorry,
  not_B324_of_B123_B124 := sorry,
  sameside_rfl_of_not_online := sorry,
  sameside_symm := sorry,
  not_online_of_sameside := sorry,
  sameside_trans := sorry,
  sameside_or_of_diffside := sorry,
  sameside12_of_B123_sameside13 := sorry,
  sameside23_of_B123_online1_not_online2 := sorry,
  not_sameside13_of_B123_online2 := sorry,
  B_of_online_inter := sorry,
  not_sameside_of_sameside_sameside := sorry,
  sameside_of_sameside_not_sameside := sorry,
  B_of_line_circle_inter := sorry,
  not_sameside_of_circle_inter := sorry,
  lines_inter_of_not_sameside := sorry,
  line_circle_inter_of_not_sameside := sorry,
  line_circle_inter_of_inside_online := sorry,
  circles_inter_of_inside_oncircle := sorry,
  length_eq_zero_iff := sorry,
  length_symm := sorry,
  angle_symm := sorry,
  angle_nonneg := sorry,
  length_nonneg := sorry,
  degenerate_area := sorry,
  area_invariant := sorry,
  area_eq_of_SSS := sorry,
  length_sum_of_B := sorry,
  oncircle_iff_length_eq := sorry,
  incircle_iff_length_lt := sorry,
  angle_zero_iff_online := sorry,
  angle_add_iff_sameside := sorry,
  angle_eq_iff_rightangle := sorry,
  angle_extension := sorry,
  unparallel_postulate := sorry,
  area_zero_iff_online := sorry,
  area_add_iff_B := sorry,
  SAS_iff_SSS := sorry }
/-
{ point := ℝ × ℝ, -- p = (x, y)
  line := { ![a,b,c]  :ℝ × ℝ × ℝ ∣  a = 1 ∨ (a=0 ∧ b=1)}, -- a x + b y = c ↔ (a, b, c)
  circle := (ℝ × ℝ) × (ℝ × ℝ), -- center and point on circle
  online := λ p L, L.1 * p.1 + L.2.1 * p.2 = L.2.2,
  sameside := λ p1 p2 L, L.1 * p1.1 + L.2.1 * p1.2 - L.2.2 ≠ 0 ∧
    L.1 * p2.1 + L.2.1 * p2.2 - L.2.2 ≠ 0 ∧ ∃ (μ : ℝ),
    0 < μ ∧ (L.1 * p1.1 + L.2.1 * p1.2 - L.2.2) = μ * (L.1 * p2.1 + L.2.1 * p2.2 - L.2.2),
  B := λ p1 p2 p3, p1 ≠ p2 ∧ p2 ≠ p3 ∧ ∃ (μ : ℝ), 0 < μ ∧ (p3 - p2) = μ • (p2-p1),
  oncircle := λ p ⟨c, b⟩, -- p is a point, c is the center, b is a point on the circle
   (c.1^2 - b.1^2) + (c.2^2 - b.2^2) = (c.1^2 - p.1^2) + (c.2^2 - p.2^2),
  in_circ := λ p ⟨c, b⟩, -- p is a point, c is the center, b is a point on the circle
   (c.1^2 - p.1^2) + (c.2^2 - p.2^2) < (c.1^2 - b.1^2) + (c.2^2 - b.2^2),
  cen_circ := λ p ⟨c, b⟩, p = c,
  lines_inter := λ L1 L2,
    ¬∃ (μ : ℝ), L1 = μ • L2 ∧ ¬∃ (μ : ℝ), (L1.1, L1.2.1) = μ • (L2.1, L2.2.1),
  line_circle_inter := sorry,
  circles_inter := sorry,
  length := sorry,
  angle := sorry,
  rightangle := sorry,
  area := sorry,
  more_pts := sorry,
  pt_B_of_ne := begin
    intros p1 p2 p1_ne_p2,
    use ((1:ℝ) / 2) • (p1+p2),
    split,
    { intro h,
      have hh := congr_arg (λ p : ℝ×ℝ, (2:ℝ) • p) h,
      simp only [one_div, smul_inv_smul₀, ne.def, bit0_eq_zero, one_ne_zero, not_false_iff] at hh,
      rw (two_smul ℝ p1) at hh,
      exact p1_ne_p2 ((add_right_inj p1).mp hh), },
    split,
    { sorry, },
    refine ⟨1, by norm_num, _⟩,
    field_simp,
    simp,
    sorry,
  end,
  pt_extension_of_ne := sorry,
  diffside_of_not_online := sorry,
  line_of_pts := sorry,
  circle_of_ne := sorry,
  pt_of_lines_inter := sorry,
  pts_of_line_circle_inter := sorry,
  pt_oncircle_of_inside_outside := sorry,
  pt_oncircle_of_inside_ne := sorry,
  pts_of_circles_inter := sorry,
  pt_sameside_of_circles_inter := sorry,
  line_unique_of_pts := sorry,
  center_circle_unique := sorry,
  inside_circle_of_center := sorry,
  not_oncircle_of_inside := sorry,
  B_symm := sorry,
  ne_12_of_B := sorry,
  ne_13_of_B := sorry,
  ne_23_of_B := sorry,
  not_B_of_B := sorry,
  online_3_of_B := sorry,
  online_2_of_B := sorry,
  B124_of_B134_B123 := sorry,
  B124_of_B123_B234 := sorry,
  B_of_three_online_ne := sorry,
  not_B324_of_B123_B124 := sorry,
  sameside_rfl_of_not_online := sorry,
  sameside_symm := sorry,
  not_online_of_sameside := sorry,
  sameside_trans := sorry,
  sameside_or_of_diffside := sorry,
  sameside12_of_B123_sameside13 := sorry,
  sameside23_of_B123_online1_not_online2 := sorry,
  not_sameside13_of_B123_online2 := sorry,
  B_of_online_inter := sorry,
  not_sameside_of_sameside_sameside := sorry,
  sameside_of_sameside_not_sameside := sorry,
  B_of_line_circle_inter := sorry,
  not_sameside_of_circle_inter := sorry,
  lines_inter_of_not_sameside := sorry,
  line_circle_inter_of_not_sameside := sorry,
  line_circle_inter_of_inside_online := sorry,
  circles_inter_of_inside_oncircle := sorry,
  length_eq_zero_iff := sorry,
  length_symm := sorry,
  angle_symm := sorry,
  angle_nonneg := sorry,
  length_nonneg := sorry,
  degenerate_area := sorry,
  area_invariant := sorry,
  area_eq_of_SSS := sorry,
  length_sum_of_B := sorry,
  oncircle_iff_length_eq := sorry,
  incircle_iff_length_lt := sorry,
  angle_zero_iff_online := sorry,
  angle_add_iff_sameside := sorry,
  angle_eq_iff_rightangle := sorry,
  angle_extension := sorry,
  unparallel_postulate := sorry,
  area_zero_iff_online := sorry,
  area_add_iff_B := sorry,
  SAS_iff_SSS := sorry }

---------------------- -/
variables[i: incidence_geometry] {a b c d e f g h j k l m n: i.point} {L M N O P Q: i.line}

-------------------------------------------------- API --------------------------------------------'
--local notation `|`x`|` := abs x

theorem len_symm_of_len {a b : point} {r:ℝ }(abcd : length a b = r) : length b a = r :=
  by rwa length_symm a b at abcd
theorem len_symm2_of_len {a b c d : point} (abcd : length a b = length c d) : length b a = length d c :=
  (len_symm_of_len (len_symm_of_len abcd).symm).symm
theorem angle_symm_of_angle {a b c : point} {r:ℝ } (ang : angle a b c = r) :
  angle c b a = r := by rwa angle_symm a b c at ang
theorem angle_symm2_of_angle {a b c d e f : point} (ab : a ≠ b) (ac : a ≠ c) (de : d ≠ e) (df : d ≠ f)
  (ang : angle a b c = angle d e f) : angle c b a = angle f e d :=
  (angle_symm_of_angle ) (angle_symm_of_angle ang.symm).symm

/-
convenient to have the ≠ there since they always get used
-/

theorem line_of_B {a b c : point} (Babc : B a b c) :
  ∃ (L : line), online a L ∧ online b L ∧ online c L ∧ a ≠ b ∧ b ≠ c ∧ c ≠ a :=
begin
  rcases line_of_pts a b with ⟨L, aL, bL⟩,
  refine ⟨L, aL, bL, online_3_of_B Babc aL bL, (ne_12_of_B Babc), (ne_23_of_B Babc), (ne_13_of_B Babc).symm⟩,
end

theorem not_B_symm {a b c : point} (Babc : ¬B a b c) : ¬B c b a := λ Bcba, Babc (B_symm Bcba)

theorem Bbcd_or_Bbdc_of_Babc_Babd {a b c d : point} (cd : c ≠ d) (Babc : B a b c) (Babd : B a b d) :
  B b c d ∨ B b d c :=
begin
  rcases line_of_B Babc with ⟨L, aL, bL, cL, -, bc, -⟩,
  cases B_of_three_online_ne  bc (ne_23_of_B Babd) cd bL cL (online_3_of_B Babd aL bL),
  left, assumption, cases h, exfalso, exact (not_B324_of_B123_B124 Babc Babd) h, right, exact h, --again
end

theorem Bbcd_of_Babc_Bacd {a b c d : point} (Babc : B a b c) (Bacd : B a c d) : B b c d :=
begin
  rcases line_of_B Babc with ⟨L, aL, bL, cL, -,bc,ca⟩,
  have bd : b ≠ d,
  { intro bd,
    rw bd at Babc,
    exact (not_B_of_B (B_symm Babc)) (B_symm Bacd), },
  have := B_of_three_online_ne  bc bd (ne_23_of_B Bacd) bL cL (online_3_of_B Bacd aL cL),
  cases this, exact this,
  exfalso, cases this,
  have Bdba := B124_of_B134_B123 (B_symm Bacd) (B_symm this),
  cases Bbcd_or_Bbdc_of_Babc_Babd ca.symm Bdba (B_symm this) with Bet,
  exact (not_B_of_B Bet) Babc,
  exact (not_B_of_B h) (B_symm Babc),
  exact (not_B_of_B (B_symm (B124_of_B134_B123 Babc (B_symm (B124_of_B123_B234 this (B_symm Bacd)))))) (B_symm Bacd),
end

theorem neq_of_online_offline (aL : online a L) (bL : ¬online b L) :   a ≠ b :=
begin
  intro ab, rw ab at aL, exact bL aL,
end

theorem neq_of_sameside (bL: online b L) (acL: sameside a c L) : a ≠ b :=
(neq_of_online_offline bL (not_online_of_sameside acL)).symm

theorem neq_of_sameside' (bL: online b L) (acL: sameside c a L) : a ≠ b :=
(neq_of_online_offline bL (not_online_of_sameside (sameside_symm acL))).symm

theorem neq_of_bet (eL: online e L) (gL: online g L) (cL: ¬ online c L) (Bet: B e h g) : h≠ c:=
begin
  exact  neq_of_online_offline (online_2_of_B Bet eL gL) cL,
end

meta def neq: tactic unit :=
do
tactic.assumption
<|>`[solve_by_elim [neq_of_online_offline]]
<|> `[solve_by_elim [neq_of_sameside]]
<|> `[solve_by_elim [neq_of_sameside']]
<|> `[solve_by_elim [neq_of_bet] { max_depth := 5 }]

meta def btw: tactic unit :=
do
tactic.assumption
<|>`[solve_by_elim [B_symm]]
<|> `[solve_by_elim [ne_12_of_B]]
<|> `[solve_by_elim [ne_13_of_B]]
<|> `[solve_by_elim [ne_23_of_B]]
<|> `[solve_by_elim [not_B_of_B]]
<|> `[solve_by_elim [B124_of_B134_B123]]
<|> `[solve_by_elim [B124_of_B123_B234]]
<|> `[solve_by_elim [B_of_three_online_ne] ]
<|> `[solve_by_elim [B_of_online_inter] ]
<|> `[solve_by_elim [not_B324_of_B123_B124] {max_depth := 5}]
<|> `[solve_by_elim [not_B_symm] ]

theorem lines_neq_of_online_offline {a : point} {L M : line} (aL : online a L) (aM : ¬online a M) : L ≠ M
  := λ LM, aM (by rwa LM at aL)

theorem angle_pos_of_not_colinear {a b c : point} {L : line} (ab : a ≠ b) (aL : online a L) (bL : online b L)
  (cL : ¬online c L) : 0 < angle b a c :=
begin --can be simplified to one line probably
  by_contra, push_neg at h, exact cL ((angle_zero_iff_online ab (neq_of_online_offline aL cL) aL bL).mpr (by linarith [angle_nonneg b a c])).1,
end

theorem angles_add_of_sameside {a b c d : point} {L M : line} (ab : a ≠ b) (ac : a ≠ c) (aL : online a L)
  (bL : online b L) (aM : online a M) (cM : online c M) (bdM : sameside b d M)
  (cdL : sameside c d L) :
  angle b a c = angle b a d + angle d a c ∧ angle b a d < angle b a c ∧ angle d a c < angle b a c
  ∧ 0 < angle b a d ∧ 0 < angle d a c :=
begin
  have angsplit := (angle_add_iff_sameside ab ac aL bL aM cM (not_online_of_sameside (sameside_symm bdM)) (not_online_of_sameside (sameside_symm cdL))
    (λ LM, (not_online_of_sameside cdL) (by rwa ← LM at cM))).mpr ⟨bdM, cdL⟩,
  rcases line_of_pts a d with ⟨N, aN, dN⟩,
  have ang1 := angle_pos_of_not_colinear ab aL bL (not_online_of_sameside (sameside_symm cdL)),
  have ang2 := angle_pos_of_not_colinear (neq_of_sameside' aL cdL).symm aN dN (λ cN, (not_online_of_sameside (sameside_symm bdM))
    (by rwa ← (line_unique_of_pts ac aM cM aN cN) at dN)),
  exact ⟨angsplit, by linarith, by linarith, ang1, ang2⟩,
end

theorem angle_extension_of_B { b1 : point} (ac : a ≠ c) (Babb1 : B a b b1) : angle b a c = angle b1 a c :=
begin
  rcases line_of_pts a b with ⟨L, aL, bL⟩, rcases line_of_pts a c with ⟨M, aM, cM⟩,
  refine angle_extension ((ne_12_of_B Babb1).symm) ((ne_13_of_B Babb1).symm) ac.symm
    ac.symm aL bL (online_3_of_B Babb1 aL bL) aM cM cM  (not_B_of_B Babb1) (λ Bcac, (ne_13_of_B Bcac) rfl),
end

theorem angle_extension_of_ss {a b c b1 : point} {L M : line} (ac : a ≠ c) (bb1 : b ≠ b1) (aL : online a L)
  (cL : online c L) (aM : online a M) (bM : online b M) (b1M : online b1 M)
  (bb1L : sameside b b1 L) : angle b a c = angle b1 a c :=
begin
  cases B_of_three_online_ne (neq_of_sameside aL bb1L).symm (neq_of_sameside' aL bb1L).symm bb1 aM bM b1M ,
  exact angle_extension_of_B ac h, cases h, exfalso, exact (not_sameside13_of_B123_online2 h) aL bb1L, exact (angle_extension_of_B ac h).symm,
end

theorem area_add_iff_B_mp {a b c d : point} {L : line} (aL : online a L) (bL : online b L)
  (cL : online c L) (dL : ¬online d L) (Bacb : B a c b) : area a c d + area d c b = area a d b
  := (area_add_iff_B (ne_13_of_B Bacb) (ne_23_of_B Bacb).symm ((ne_12_of_B Bacb).symm) aL bL cL dL).mp Bacb

theorem sss {a b c d e f : point} (lab : length a b = length d e) (lbc : length b c = length e f)
  (lac : length a c = length d f)
  : angle a b c = angle d e f ∧ angle b a c = angle e d f ∧ angle a c b = angle d f e
  := ⟨(SAS_iff_SSS (len_symm2_of_len lab) lbc).2 lac, (SAS_iff_SSS lab lac).2 lbc, (SAS_iff_SSS (len_symm2_of_len lac) (len_symm2_of_len lbc)).2 lab⟩

theorem sas {a b c d e f : point} (ab : length a b = length d e) (ac : length a c = length d f)
  (Abac : angle b a c = angle e d f)
  : length b c = length e f ∧ angle a b c = angle d e f ∧ angle a c b = angle d f e
  := ⟨(SAS_iff_SSS ab ac).1 Abac, (sss ab ((SAS_iff_SSS ab ac).1 Abac) ac).1, (sss ab ((SAS_iff_SSS ab ac).1 Abac) ac).2.2⟩ --Euclid I.4

lemma len_pos_of_nq {a b : point} (hab : a ≠ b) : 0 < length a b
  := (ne.symm (not_imp_not.2 length_eq_zero_iff.1 hab)).le_iff_lt.mp (length_nonneg a b)

lemma nq_of_len_pos {a b : point} (length : 0 < length a b) : a ≠ b
  := (not_congr (length_eq_zero_iff)).1 (ne_of_gt length)

lemma B_of_length_leq {a b c : point} {L : line} (ab : a ≠ b) (bc : b ≠ c) (ac : a ≠ c) (aL : online a L)
  (bL : online b L) (cL : online c L) (length : length a b + length b c ≤ length a c) : B a b c :=
begin
  cases B_of_three_online_ne ab ac bc aL bL cL, assumption, cases h,
  linarith [length_sum_of_B h, length_symm a b, len_pos_of_nq ab], linarith [length_sum_of_B h, length_symm c b, len_pos_of_nq bc],
end

theorem nq_of_nq_len {a b c : point} (ac : a ≠ c) (length : length a b = length b c) : a ≠ b
  := λ ab, by linarith [len_pos_of_nq (ne_of_eq_of_ne (eq.symm ab) ac), length_eq_zero_iff.mpr ab]

theorem nq_of_cen_circ {a b : point} {α β : circle} (acen : cen_circ a α) (bcen : cen_circ b β)
  (ab : a ≠ b) : α ≠ β :=
begin
  intro albet, rw albet at acen,
  have := center_circle_unique acen bcen,
  exact ab this,
end

def iseqtri (a b c : point) : Prop :=
  length a b = length a c  ∧ length b c = length b a ∧ length c a = length c b ∧ a ≠ b ∧ b ≠ c ∧ c ≠ a

def diffside (a b : point) (L : line) : Prop := ¬online a L ∧ ¬online b L ∧ ¬sameside a b L

theorem difsym {a b : point} {L : line} (nss : ¬sameside a b L) : ¬sameside b a L
  := λ nss2, nss (sameside_symm nss2)

theorem sameside_of_diffside_diffside {a b c : point} {L : line} (dsab : diffside a b L) (dsac : diffside a c L) :
  sameside b c L :=(or_iff_right dsac.2.2).mp
  (sameside_or_of_diffside dsab.1 dsab.2.1 dsac.2.1 dsab.2.2)

theorem difsamedif {a b c : point} {L : line} (ssab : sameside a b L) (dsac : diffside a c L) :
  diffside b c L :=
begin
  by_contra,
  unfold diffside at h,
  push_neg at h,
  exact dsac.2.2 (sameside_trans (sameside_symm ssab) (h (not_online_of_sameside (sameside_symm ssab)) dsac.2.1)),
end

theorem difneq {a b : point} {L : line} (dsab : diffside a b L) : a ≠ b :=
begin
  intro ab,
  rw ab at dsab,
  unfold diffside at dsab,
  have := sameside_rfl_of_not_online dsab.1,
  exact dsab.2.2 this,
end

theorem angeasy {a b c : point} {d : ℝ} (ab : a ≠ b) (ac : a ≠ c) (ang : d ≠ angle a b c) :
  d ≠ angle c b a := by rwa (angle_symm a b c) at ang

def para (M N : line) : Prop :=  (∀  (e : point), ¬online e M ∨ ¬online e N)

theorem para_symm {M N : line} (par: para M N) : para N M:= λ a, or.swap (par a)

theorem online_of_online_para {a : point} {M N: line}(aM: online a M)(par: para M N): ¬ online a N:=
begin
  cases par a,exfalso,exact h aM,exact h,
end

theorem online_of_online_para' {a : point} {M N: line}(aN: online a N)(par: para M N): ¬ online a M:=
begin
  cases par a,exact h,exfalso,exact h aN,
end

theorem sameside_of_online_online_para {a b : point} {M N: line} (aM: online a M) (bM: online b M)(par: para M N):
sameside a b N:=
begin
   by_contra abN, rcases pt_of_lines_inter (lines_inter_of_not_sameside aM bM abN) with ⟨z,zN,zM⟩,
    cases par z, exact h zM, exact h zN,
end

theorem sameside_of_online_online_para' {a b : point} {M N: line} (aM: online a N) (bM: online b N)(par: para M N):
sameside a b M:=
begin
   by_contra abN, rcases pt_of_lines_inter (lines_inter_of_not_sameside aM bM abN) with ⟨z,zN,zM⟩,
    cases par z, exact h zN, exact h zM,
end

theorem circint_of_lt_lt {a b c d : point} {α β : circle} (acen : cen_circ a α)
  (bcen : cen_circ b β) (ccirc : oncircle c α) (dcirc : oncircle d β)
  (cenbig : |length a c - length b d| < length a b)
  (censmall : length a b < length a c + length b d) :
  circles_inter α β :=
begin
  have := abs_lt.mp cenbig,
  have ab : a ≠ b := mt length_eq_zero_iff.mpr (by linarith : length a b ≠ 0),
  rcases line_of_pts a b with ⟨L, aL, bL⟩,
  rcases pts_of_line_circle_inter (line_circle_inter_of_inside_online aL
    (inside_circle_of_center acen)) with ⟨c1, c2,c1c2, c1L, c2L, c1circ, c2circ⟩,
  rcases pts_of_line_circle_inter (line_circle_inter_of_inside_online bL
    (inside_circle_of_center bcen)) with ⟨d1, d2,d1d2, d1L, d2L, d1circ, d2circ⟩,
  have Bc1ac2 := B_of_line_circle_inter c1c2 aL c1L c2L c1circ c2circ
    (inside_circle_of_center acen),
  have Bd1bd2 := B_of_line_circle_inter d1d2 bL d1L d2L d1circ d2circ
    (inside_circle_of_center bcen),
  have clen1 := (oncircle_iff_length_eq ccirc acen).mpr c1circ,
  have clen2 := (oncircle_iff_length_eq ccirc acen).mpr c2circ,
  have dlen1 := (oncircle_iff_length_eq dcirc bcen).mpr d1circ,
  have dlen2 := (oncircle_iff_length_eq dcirc bcen).mpr d2circ,
  have cin : in_circ c1 β ∨ in_circ c2 β,
  { by_contra out, push_neg at out,
    have ineq2 := mt (incircle_iff_length_lt d2circ bcen).mp out.1, push_neg at ineq2,
    have ineq4 := mt (incircle_iff_length_lt d2circ bcen).mp out.2, push_neg at ineq4,
    have bc1 : b ≠ c1 := nq_of_len_pos (by linarith [len_pos_of_nq (ab)] :
      0 < length b c1),
    have bc2 : b ≠ c2 := nq_of_len_pos (by linarith [len_pos_of_nq (ne_23_of_B Bd1bd2)] :
      0 < length b c2),
    cases B_of_three_online_ne (ne_23_of_B Bc1ac2) ab bc2.symm aL c2L bL  with Bac2b Bet,
    linarith [length_sum_of_B Bac2b, length_symm b c2],
    cases Bet with Bc2ab Babc2,
    cases Bbcd_or_Bbdc_of_Babc_Babd bc1.symm (B_symm Bc1ac2) Bc2ab with Bac1b Babc1,
    linarith [length_sum_of_B Bac1b, length_symm b c1],
    linarith [length_sum_of_B Babc1],
    linarith [length_sum_of_B Babc2], },
  have din : in_circ d1 α ∨ in_circ d2 α,
  { by_contra out, push_neg at out,
    have := mt (incircle_iff_length_lt c2circ acen).mp out.1, push_neg at this,
    have := mt (incircle_iff_length_lt c2circ acen).mp out.2, push_neg at this,
    have ad1 : a ≠ d1 := nq_of_len_pos (by linarith [len_pos_of_nq (ne_23_of_B Bc1ac2)] :
      0 < length a d1),
    have ad2 : a ≠ d2 := nq_of_len_pos (by linarith [len_pos_of_nq (ne_23_of_B Bc1ac2)] :
      0 < length a d2),
    cases B_of_three_online_ne ab ad1 ((ne_12_of_B Bd1bd2).symm) aL bL d1L  with Babd1 Bet,
    cases Bbcd_or_Bbdc_of_Babc_Babd ad2 (B_symm Babd1) Bd1bd2 with Bbad2 Bbd2a,
    linarith [length_symm a b, length_sum_of_B Bbad2],
    linarith [length_symm d2 a, length_symm a b, length_sum_of_B Bbd2a],
    cases Bet with Bbad1 Bad1b,
    linarith [length_symm a b, length_sum_of_B Bbad1],
    linarith [length_symm d1 b, length_sum_of_B Bad1b], },
  cases cin with c1bet c2bet,
  cases din with d1alp d2alp,
  exact circles_inter_of_inside_oncircle c1circ d1circ d1alp c1bet,
  exact circles_inter_of_inside_oncircle c1circ d2circ d2alp c1bet,
  cases din with d1alp d2alp,
  exact circles_inter_of_inside_oncircle c2circ d1circ d1alp c2bet,
  exact circles_inter_of_inside_oncircle c2circ d2circ d2alp c2bet,
end

theorem quadiag {a b c d : point} {L M N : line} (ab : a ≠ b) (cd : c ≠ d) (aL : online a L)
  (bL : online b L) (cM : online c M) (dM : online d M) (bN : online b N) (dN : online d N)
  (abM : sameside a b M) (cdL : sameside c d L) (acN : sameside a c N) :
  ∃ (e : point) (O P : line), online a O ∧ online d O ∧ online b P ∧ online c P ∧  online e O ∧
  online e P ∧ B b e c ∧ B d e a ∧ ¬online c O ∧ ¬online b O ∧ ¬online d P ∧ ¬online a P :=
begin
  rcases line_of_pts a d with ⟨O, aO, dO⟩,
  rcases line_of_pts c b with ⟨P, cP, bP⟩,
  rcases line_of_pts a c with ⟨K, aK, cK⟩,
  have OP : O ≠ P := λ OP, (not_online_of_sameside cdL (by rwa ←(line_unique_of_pts ab aL bL (by rwa OP at aO) bP) at cP)),
  have bcO := not_sameside_of_sameside_sameside dN dO dM bN aO cM acN (sameside_symm abM),
  rcases pt_of_lines_inter (lines_inter_of_not_sameside  bP cP bcO) with ⟨e, eO, eP⟩,
  have be : b ≠ e := λ be, (not_online_of_sameside (sameside_symm cdL)) (by rwa ←(line_unique_of_pts ab aL bL aO (by rwa ← be at eO)) at dO),
  have ce : c ≠ e := λ ce, (not_online_of_sameside abM) (by rwa line_unique_of_pts cd cM dM (by rwa ← ce at eO) dO),
  have de : d ≠ e := λ de, (not_online_of_sameside (sameside_symm abM)) (by rwa ← line_unique_of_pts cd cM dM cP (by rwa ← de at eP) at bP),
  have ae : a ≠ e := λ ae, (not_online_of_sameside cdL) (by rwa ← (line_unique_of_pts ab aL bL (by rwa ← ae at eP) bP) at cP),
  have cO := λ cO, OP (line_unique_of_pts ce cO eO cP eP),
  have bO := λ bO, OP (line_unique_of_pts be bO eO bP eP),
  have dP := λ dP, OP (line_unique_of_pts de dO eO dP eP),
  have aP := λ aP, OP (line_unique_of_pts ae aO eO aP eP),
  have daP := not_sameside_of_sameside_sameside cK cP cM aK bP dM (sameside_of_sameside_not_sameside ab aL aO aK bL dO cK cO (sameside_symm cdL) bcO ) abM,
  have Bbec := B_of_online_inter be ce.symm (neq_of_sameside bL cdL).symm OP.symm bP eP cP eO  bcO,
  have Bdea := B_of_online_inter de ae.symm (neq_of_sameside dM abM).symm OP dO eO aO eP (difsym daP),
  refine ⟨e, O, P, aO, dO, bP, cP, eO, eP, Bbec, Bdea, cO, bO, dP, aP⟩,
end

theorem quadarea_comm {a b c d : point} {L M N : line} (ab : a ≠ b) (cd : c ≠ d) (aL : online a L)
  (bL : online b L) (cM : online c M) (dM : online d M) (bN : online b N) (dN : online d N)
  (abM : sameside a b M) (cdL : sameside c d L) (acN : sameside a c N) :
  area d b a + area d c a = area b d c + area b a c :=
begin
  rcases quadiag ab cd aL bL cM dM bN dN abM cdL acN with
    ⟨e, O, P, aO, dO, bP, cP, eO, eP, Bbec, Bdea, cO, bO, dP, aP⟩,
  linarith [area_add_iff_B_mp dO aO eO cO Bdea, area_add_iff_B_mp dO aO eO bO Bdea, area_add_iff_B_mp bP cP eP aP Bbec,
    area_add_iff_B_mp bP cP eP dP Bbec, area_invariant a e c, area_invariant c a e, area_invariant b e d, area_invariant d b e],
end

theorem quad_add_of_quad_quad {a b c d e f : point} {L M N : line} (aL : online a L) (cL : online c L)
  (dM : online d M) (fM : online f M) (cN : online c N) (fN : online f N) (Babc : B a b c)
  (Bdef : B d e f) (acM : sameside a c M) (dfL : sameside d f L) (adN : sameside a d N) :
  area a b e + area d e a + area e b c + area e f c = area d a f + area f c a :=
begin
  rcases quadiag (ne_13_of_B Babc) (ne_23_of_B Bdef) aL cL (online_2_of_B Bdef dM fM) fM cN fN acM
    (sameside_trans (sameside12_of_B123_sameside13 Bdef dfL) dfL) (sameside_symm (sameside_trans (sameside_symm (sameside23_of_B123_online1_not_online2 (B_symm Bdef) fN (λ eN, (not_online_of_sameside (sameside_symm acM))
    (by rwa (line_unique_of_pts (ne_23_of_B Bdef) eN fN (online_2_of_B Bdef dM fM) fM) at cN)))) (sameside_symm adN))) with
    ⟨h, O, P, aO, fO, cP, eP, hO, hP, Bche, Bfha, eO, cO, fP, aP⟩,
  linarith [area_add_iff_B_mp aL cL (online_2_of_B Babc aL cL) (not_online_of_sameside (sameside_symm (sameside12_of_B123_sameside13 Bdef dfL))) Babc, area_add_iff_B_mp eP cP
    (online_2_of_B Bche cP eP) aP (B_symm Bche), area_add_iff_B_mp eP cP (online_2_of_B Bche cP eP) fP (B_symm Bche),
    area_add_iff_B_mp fO aO (online_2_of_B Bfha fO aO) cO Bfha, area_add_iff_B_mp fO aO (online_2_of_B Bfha fO aO) eO Bfha,
    area_add_iff_B_mp dM fM (online_2_of_B Bdef dM fM) (not_online_of_sameside acM) Bdef, area_invariant e a c, area_invariant e c a, area_invariant f e a, area_invariant a f e,
    area_invariant f h e, area_invariant e f h, area_invariant c h a, area_invariant a c h],
end

#exit

def square (a b d e: point) : Prop :=
a≠ b ∧ a≠ e ∧ length a b = length d e ∧ length a b = length a d ∧ length a b = length b e ∧
angle d a b = angle a b e ∧ angle d a b = angle a d e ∧ angle d a b = angle d e b

def square_strong (a b d e : point) (L M N O : line) : Prop :=
online a M ∧ online d M ∧ online b O ∧ online e O ∧
online a L ∧ online b L ∧ online d N ∧ online e N ∧
length a b = length d e ∧ length a b = length a d ∧
  length a b = length b e ∧ angle d a b = rightangle ∧ angle a b e = rightangle ∧
  angle a d e = rightangle ∧ angle d e b = rightangle ∧ para M O ∧ para L N

lemma online_1_1_of_square {a b d e : point} {L M N O : line}  (sq: square_strong a b d e L M N O) : online a L := sq.2.2.2.2.1
lemma online_1_2_of_square {a b d e : point} {L M N O : line}  (sq: square_strong a b d e L M N O) : online a M := sq.1
lemma online_2_1_of_square {a b d e : point} {L M N O : line}  (sq: square_strong a b d e L M N O) : online b L := sq.2.2.2.2.2.1
lemma online_2_4_of_square {a b d e : point} {L M N O : line}  (sq: square_strong a b d e L M N O) : online b O := sq.2.2.1
lemma online_3_2_of_square {a b d e : point} {L M N O : line}  (sq: square_strong a b d e L M N O) : online d M := sq.2.1
lemma online_3_3_of_square {a b d e : point} {L M N O : line}  (sq: square_strong a b d e L M N O) : online d N := sq.2.2.2.2.2.2.1
lemma online_4_4_of_square {a b d e : point} {L M N O : line}  (sq: square_strong a b d e L M N O) : online e O := sq.2.2.2.1
lemma online_4_3_of_square {a b d e : point} {L M N O : line}  (sq: square_strong a b d e L M N O) : online e N := sq.2.2.2.2.2.2.2.1
lemma para_2_4_of_square {a b d e : point} {L M N O : line}  (sq: square_strong a b d e L M N O) : para M O := sq.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma para_1_3_of_square {a b d e : point} {L M N O : line}  (sq: square_strong a b d e L M N O) : para L N := sq.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2


-------------------------------------------------- API --------------------------------------------

lemma makeeqtriaux {a b c : point} (hab : a ≠ b) (h1 : length a b = length a c)
  (h2 : length b c = length b a) : b ≠ c ∧ c ≠ a := ⟨λ bc, hab (length_eq_zero_iff.mp (by linarith [length_eq_zero_iff.mpr bc])).symm,
  λ ca, hab (length_eq_zero_iff.mp (by linarith [length_eq_zero_iff.mpr ca.symm]))⟩

theorem iseqtri_of_ne {a b : point} (hab : a ≠ b) : ∃ (c : point), iseqtri a b c := --Euclid 1.1
begin
  rcases circle_of_ne hab with ⟨α, bcirc, acen⟩,
  rcases circle_of_ne (ne.symm hab) with ⟨β, acirc, bcen⟩,
  rcases pts_of_circles_inter (circles_inter_of_inside_oncircle bcirc acirc (inside_circle_of_center acen) (inside_circle_of_center bcen)) with ⟨c,-, -, cona, conb, -, -⟩,
  have abeqac := (oncircle_iff_length_eq bcirc acen).2 cona,
  have bceqba := (oncircle_iff_length_eq conb bcen).mpr acirc,
  have caeqcb : length c a = length c b :=
    len_symm_of_len ((rfl.congr (eq.symm (len_symm2_of_len bceqba))).mp (eq.symm abeqac)),
  refine ⟨c, abeqac, bceqba, caeqcb, hab, makeeqtriaux hab abeqac bceqba⟩,
end

theorem iseqtri_iseqtri_ne_of_ne {a b : point} (hab : a ≠ b) : ∃ (c d : point), ∃ (L : line), iseqtri a b c ∧
  iseqtri a b d ∧ online a L ∧ online b L ∧ ¬sameside c d L ∧ c ≠ d := --Euclid 1.1
begin
  rcases line_of_pts a b with ⟨L, aL, bL⟩,
  rcases circle_of_ne hab with ⟨α, bcirc, acen⟩,
  rcases circle_of_ne (ne.symm hab) with ⟨β, acirc, bcen⟩,
  rcases pts_of_circles_inter (circles_inter_of_inside_oncircle bcirc acirc (inside_circle_of_center acen) (inside_circle_of_center bcen)) with ⟨c, d, cd,cona, conb, dona, donb⟩,
  have nss := not_sameside_of_circle_inter cd (nq_of_cen_circ acen bcen hab) aL bL cona conb dona donb acen bcen
    (circles_inter_of_inside_oncircle bcirc acirc (inside_circle_of_center acen) (inside_circle_of_center bcen)),
  have abeqac := (oncircle_iff_length_eq bcirc acen).2 cona,
  have abeqad := (oncircle_iff_length_eq bcirc acen).2 dona,
  have bceqba := (oncircle_iff_length_eq conb bcen).mpr acirc,
  have bdeqba := (oncircle_iff_length_eq donb bcen).mpr acirc,
  have caeqcb := len_symm_of_len ((rfl.congr (eq.symm (len_symm2_of_len bceqba))).mp (eq.symm abeqac)),
  have daeqdb := len_symm_of_len ((rfl.congr (eq.symm (len_symm2_of_len bdeqba))).mp (eq.symm abeqad)),
  refine ⟨c, d, L, ⟨abeqac, bceqba, caeqcb, hab, makeeqtriaux hab abeqac bceqba⟩,
    ⟨abeqad, bdeqba, daeqdb, hab, makeeqtriaux hab abeqad bdeqba⟩, aL, bL, nss, cd⟩,
end

theorem iseqtri_iseqtri_diffside_of_ne {a b : point} (hab : a ≠ b) : ∃ (c d : point), ∃ (L : line), iseqtri a b c ∧
  iseqtri a b d ∧ online a L ∧ online b L ∧ diffside c d L := --Euclid 1.1
begin
  rcases line_of_pts a b with ⟨L, aL, bL⟩,
  rcases circle_of_ne hab with ⟨α, bcirc, acen⟩,
  rcases circle_of_ne (ne.symm hab) with ⟨β, acirc, bcen⟩,
  rcases pts_of_circles_inter (circles_inter_of_inside_oncircle bcirc acirc (inside_circle_of_center acen) (inside_circle_of_center bcen)) with ⟨c, d, cd, cona, conb, dona, donb⟩,
  have nss := not_sameside_of_circle_inter cd (nq_of_cen_circ acen bcen hab) aL bL cona conb dona donb acen bcen
  (circles_inter_of_inside_oncircle bcirc acirc (inside_circle_of_center acen) (inside_circle_of_center bcen)),

  have abeqac := (oncircle_iff_length_eq bcirc acen).2 cona,
  have abeqad := (oncircle_iff_length_eq bcirc acen).2 dona,
  have bceqba := (oncircle_iff_length_eq conb bcen).mpr acirc,
  have bdeqba := (oncircle_iff_length_eq donb bcen).mpr acirc,
  have caeqcb := len_symm_of_len ((rfl.congr (eq.symm (len_symm2_of_len bceqba))).mp (eq.symm abeqac)),
  have daeqdb := len_symm_of_len ((rfl.congr (eq.symm (len_symm2_of_len bdeqba))).mp (eq.symm abeqad)),
  have key : diffside c d L,
  { split, intro cL,
    have := len_pos_of_nq hab,
    have := len_pos_of_nq hab.symm,
    have this1 : a ≠ c,
    { intro ac,
      have := length_eq_zero_iff.2 ac,
      linarith, },
    have : b ≠ c,
    { intro bc,
      have := length_eq_zero_iff.2 bc,
      linarith, },
    cases B_of_three_online_ne hab this1 this aL bL cL ,
    { linarith[length_symm a b, length_sum_of_B h], },
    cases h,
    { linarith[length_sum_of_B h,length_symm a b], },
    have := length_sum_of_B h,
    linarith [len_symm2_of_len bceqba],
    --same for d
    split, intro dL,
    have := len_pos_of_nq hab,
    have := len_pos_of_nq hab.symm,
    have this1 : a ≠ d,
    { intro ad,
      have := length_eq_zero_iff.2 ad,
      linarith, },
    have : b ≠ d,
    { intro bd,
      have := length_eq_zero_iff.2 bd,
      linarith, },
    cases B_of_three_online_ne hab this1 this aL bL dL ,
    { linarith[length_symm a b, length_sum_of_B h], },
    cases h,
    { linarith[length_sum_of_B h,length_symm a b], },
    have := length_sum_of_B h,
    linarith [len_symm2_of_len bdeqba],
    exact nss, },
  refine ⟨c, d, L, ⟨abeqac, bceqba, caeqcb, hab, makeeqtriaux hab abeqac bceqba⟩,
    ⟨abeqad, bdeqba, daeqdb, hab, makeeqtriaux hab abeqad bdeqba⟩, aL, bL, key⟩,
end

theorem same_length_of_ne {a b c : point} {L : line} (hbc : b ≠ c) (aL : online a L) : ∃ (d : point),
  online d L ∧ length a d = length b c := --Euclid 1.2,3 (generalizations and corrollaries)
begin
    by_cases hab : a = b,
    { rcases circle_of_ne hbc with ⟨α, ccirc, bcen⟩,
      rcases pts_of_line_circle_inter (line_circle_inter_of_inside_online (by rwa hab at aL) (inside_circle_of_center bcen)) with
        ⟨d, -,-, dL, -, dalpha, -⟩,
      refine ⟨d, dL, by rwa hab; linarith [(oncircle_iff_length_eq dalpha bcen).mpr ccirc]⟩, },
    rcases iseqtri_of_ne hab with ⟨d, len1, len2, len3, hab, hbd, hda⟩,
    rcases line_of_pts d a with ⟨M, dM, aM⟩,
    rcases line_of_pts b d with ⟨N, dN, bN⟩,
    rcases circle_of_ne hbc with ⟨α, ccirc, bcen⟩,
    rcases pt_oncircle_of_inside_ne hbd (inside_circle_of_center bcen)  with ⟨g, Bgbd,gcirc⟩,
    have hyp : length d g = length b a + length b g := by linarith [length_sum_of_B (B_symm Bgbd), length_symm d b],
    have hyp2 : length d a < length d g,
    { by_contra  h, -- by_contra and then push_neg?
      exact ((ne_12_of_B Bgbd).symm) (length_eq_zero_iff.mp (by linarith [length_nonneg b g, len_symm2_of_len len3, length_symm a d])), },
    rcases circle_of_ne ((ne_13_of_B Bgbd).symm) with ⟨β, gcirc2, dcen⟩,
    rcases pt_oncircle_of_inside_ne hda.symm ((incircle_iff_length_lt gcirc2 dcen).1 hyp2)  with ⟨f, Bfad,fcirc⟩,
    have key : length b c = length f a := by linarith [length_sum_of_B Bfad, (oncircle_iff_length_eq fcirc dcen).2 gcirc2, length_symm d f,
      len_symm2_of_len len3, (oncircle_iff_length_eq ccirc bcen).2 gcirc],
    rcases circle_of_ne ((ne_12_of_B Bfad).symm) with ⟨γ, fcirc3, acen2⟩,
    rcases pts_of_line_circle_inter (line_circle_inter_of_inside_online aL (inside_circle_of_center acen2)) with ⟨h, -,-, hL, -, hcirc, -⟩,
    refine ⟨h, hL, by linarith [length_symm a f, (oncircle_iff_length_eq fcirc3 acen2).2 hcirc]⟩,
end

theorem same_length_B_of_ne {a b c : point} (hab : a ≠ b) (hbc : b ≠ c) :
  ∃ (p : point), B a b p ∧ length b p = length c b :=
begin
  rcases line_of_pts a b with ⟨L, aL, bL⟩,
  rcases circle_of_ne hbc with ⟨α, ccirc, bcirc⟩,
  rcases pt_oncircle_of_inside_ne hab.symm (inside_circle_of_center bcirc) with ⟨p, Bpba, pcirc⟩ ,
  refine ⟨p, B_symm Bpba, by rwa [length_symm c b, ((oncircle_iff_length_eq pcirc bcirc).2 ccirc)]⟩,
end

theorem same_length_B_of_ne_four {a b c d : point} (hab : a ≠ b) (hcd : c ≠ d) :
  ∃ (p : point), B a b p ∧ length b p = length c d :=
begin
  rcases line_of_pts a b with ⟨L, aL, bL⟩,
  rcases same_length_of_ne hcd bL with ⟨p1, p1L, len⟩,
  by_cases b = p1, { exfalso, refine hcd (length_eq_zero_iff.mp (eq.trans (length_eq_zero_iff.mpr h).symm len).symm), },
  by_cases hap1 : a = p1,
  { rcases circle_of_ne (ne.symm hab) with ⟨α, acirc, bcen⟩,
    rcases pts_of_line_circle_inter (line_circle_inter_of_inside_online bL (inside_circle_of_center bcen)) with ⟨e, f, hef,eL, fL, ecirc, fcirc⟩ ,
    by_cases hyp : a = e,
    { use f, split,
      { -- refine later
        exact B_of_line_circle_inter (λ haf, hef (eq.trans hyp.symm haf)) bL aL fL acirc fcirc (inside_circle_of_center bcen)  , },--again
      rw ← hap1 at len,
      linarith [(oncircle_iff_length_eq acirc bcen).2 fcirc], },
    refine ⟨e, B_of_line_circle_inter hyp bL aL eL acirc ecirc (inside_circle_of_center bcen) , _⟩,
    rw ← ((oncircle_iff_length_eq acirc bcen).2 ecirc),
    rwa ← hap1 at len, }, --again
    rcases same_length_B_of_ne hab h with ⟨p, hypp⟩,
  refine ⟨p, hypp.1, by linarith [hypp.2, length_symm b p1]⟩,
end

theorem same_length_B_of_ne_le {a b c d : point} (cd : c ≠ d) (big : length c d < length a b) :
  ∃ (p : point), B a p b ∧ length a p = length c d := --can use for I.11
begin
  rcases line_of_pts a b with ⟨L, aL, bL⟩,
  rcases pt_extension_of_ne (nq_of_len_pos (by linarith [length_nonneg c d]) : a ≠ b).symm with ⟨q, Bbaq⟩,
  by_cases ad : a = d,
  { by_cases ac : a = c, { exfalso, rw [← ac, ← ad] at cd, exact cd rfl, },
    rcases circle_of_ne ac with ⟨α, ccirc, acen⟩,
    rw ← ad at big,
    have noin := mt (incircle_iff_length_lt ccirc acen).mpr (by linarith [length_symm a c] : ¬(length a b < length a c)),
    have := mt (oncircle_iff_length_eq ccirc acen).mpr ((by linarith [length_symm a c]) : length a c ≠ length a b),
    rcases pt_oncircle_of_inside_outside this (inside_circle_of_center acen) noin with ⟨p,Bapb , pcirc⟩,
    have := (oncircle_iff_length_eq ccirc acen).mpr pcirc,
    rw ← ad, --optimize?
    refine ⟨p, Bapb, by linarith [length_symm a c]⟩, },
  rcases same_length_B_of_ne (ne_23_of_B Bbaq).symm ad with ⟨p, Bqap, len⟩,
  by_cases a = c,
  have bp : b ≠ p, { intro bp, rw [bp, h.symm] at big, linarith [length_symm a d], },
  rw [h.symm, (len_symm_of_len len.symm)] at big,
  cases (B_of_three_online_ne ((ne_12_of_B Bbaq).symm) (ne_23_of_B Bqap) bp aL bL (online_3_of_B Bqap (online_3_of_B Bbaq bL aL) aL) ),
  --- **** BAD don't use auto-generated `h_1`
  linarith [length_sum_of_B h_1, len_pos_of_nq (ne_23_of_B h_1)],
  cases h_1,
  exfalso,
  exact not_B324_of_B123_B124 Bbaq h_1 Bqap, --exfalso + exact?
  refine ⟨p, h_1, _⟩,symmetry,
   rw [len_symm_of_len],symmetry, rwa h.symm,
  rcases same_length_B_of_ne_four (ne_23_of_B Bbaq).symm cd with ⟨p, Bqap, len⟩, --same as above but with a ≠ c
  have bp : b ≠ p, { intro bp, rw bp at big, linarith, }, --again
  cases B_of_three_online_ne ((ne_12_of_B Bbaq).symm) (ne_23_of_B Bqap) bp aL bL (online_3_of_B Bqap (online_3_of_B Bbaq bL aL) aL) ,
  linarith [length_sum_of_B h_1, len_pos_of_nq (ne_23_of_B h_1)], cases h_1, exfalso,
  exact not_B324_of_B123_B124 Bbaq h_1 Bqap,
  refine ⟨p, h_1, len⟩,
end

--- Euclid I.5 (part 1)
theorem eq_angle_of_eq_length {a b c : point} (ab : a ≠ b) (bc : b ≠ c) (labac : length a b = length a c) :
  angle a b c = angle a c b  := (sas labac labac.symm (angle_symm b a c)).2.2.symm

theorem isosidelem {a b c : point} {L : line} (ab : a ≠ b) (bc : b ≠ c) (ca : c ≠ a)
  (aL : online a L) (bL : online b L) (ang : angle a b c = angle a c b) (Bbac : ¬B b a c) :
  ¬online c L :=
begin
  intro cL,
  cases B_of_three_online_ne ab ca.symm bc aL bL cL  with hyp,
  { have := not_imp_not.2 (angle_zero_iff_online ab.symm bc bL aL).2,
    push_neg at this, -- any way to push_neg without extra line?
    exact (this (iff_of_true cL hyp).mp) (by linarith [((angle_zero_iff_online ca bc.symm cL aL).1
      ⟨bL, not_B_symm (not_B_of_B (B_symm hyp))⟩)]), },
  cases h,
  exact ab (false.rec (a = b) (Bbac h)),
  have := not_imp_not.2 (angle_zero_iff_online ca bc.symm cL aL).2, push_neg at this,
  exact (this (iff_of_true bL h).mp) (by linarith [(angle_zero_iff_online ab.symm bc bL aL).1
    ⟨cL, not_B_symm (not_B_of_B (B_symm h))⟩]),
end

--Euclid I.6
theorem isoside {a b c : point} (Bbac : ¬B b a c) (ab : a ≠ b) (bc : b ≠ c) (ca : c ≠ a)
  (ang : angle a b c = angle a c b) : length a b = length a c :=
begin
  wlog h : (length a c ≤ length a b) using [b c, c b],
  { exact le_total (length a c) (length a b), },
  by_cases h_1 : length a c = length a b, exact h_1.symm,
  rcases same_length_B_of_ne_le ca.symm (by linarith [(ne.le_iff_lt h_1).mp h, length_symm a b] : length a c < length b a) with
    ⟨d, Bbda, bdac⟩,
  have dbcacb : angle a c b = angle d b c := by linarith [angle_extension_of_B bc Bbda],
  have eq := sas (len_symm_of_len bdac.symm) (length_symm c b) dbcacb,
  rcases line_of_B Bbda with ⟨L, bL, dL, aL, bd, da, ab⟩,
  have asplit := (area_add_iff_B ab.symm da.symm bd.symm bL aL dL (isosidelem ab bc ca aL bL ang Bbac)).1
    Bbda,
  have key : area b c a + area d a c = area b c a :=
    by linarith [area_eq_of_SSS (len_symm_of_len bdac.symm) eq.1 (length_symm b c),
    (area_invariant c a b).1, (area_invariant d a c).1],
  exfalso,
  exact (isosidelem ab bc ca aL bL ang Bbac) ((area_zero_iff_online da dL aL).1 (by linarith)),
  exact (this (not_B_symm Bbac) ca.symm bc.symm ab.symm ang.symm).symm,
end

--Euclid I.10
theorem bisline {a b : point} (ab : a ≠ b) : ∃ (d : point), B a d b ∧ length a d = length d b :=
begin
  rcases iseqtri_iseqtri_ne_of_ne ab with ⟨c, e, L, ⟨labac, lbcba, lcacb, ab, bc, ca⟩,
    ⟨labae, lbeba, lcaeb, ab, be, ea⟩, aL, bL, nss, ce⟩,
  rcases line_of_pts c e with ⟨M, cM, eM⟩,
  rcases pt_of_lines_inter (lines_inter_of_not_sameside cM eM nss) with ⟨d, dL, dM⟩,
  have cd : c ≠ d,
  { intro cd,
    rw ← cd at dL,
    cases B_of_three_online_ne ab ca.symm bc aL bL dL ,
    linarith [length_sum_of_B h, len_symm2_of_len lcacb,  length_symm a b, len_pos_of_nq ab],
    cases h,
    linarith [length_sum_of_B h, len_pos_of_nq ca.symm],
    linarith [length_sum_of_B h, len_pos_of_nq bc.symm], },
  have ed : e ≠ d,
  { intro ed,
    rw ← ed at dL,
    cases B_of_three_online_ne ab ea.symm be aL bL dL ,
    linarith [length_sum_of_B h, len_symm2_of_len lcacb, length_symm a b, len_pos_of_nq ab],
    cases h,
    linarith [length_sum_of_B h, len_pos_of_nq ca.symm],
    linarith [length_sum_of_B h, len_pos_of_nq be.symm], },
  have LM : L ≠ M,
  { intro LM,
    rw ← LM at cM,
    cases B_of_three_online_ne ab ca.symm bc aL bL cM ,
    linarith [len_symm2_of_len lcacb, length_symm a b, len_pos_of_nq ab, length_sum_of_B h],
    cases h,
    linarith [length_sum_of_B h, len_pos_of_nq ca.symm],
    linarith [length_sum_of_B h, len_pos_of_nq bc.symm], }, --proof
  have extang1 := (angle_extension_of_B ca (B_of_online_inter cd ed.symm ce LM.symm cM dM eM dL  nss)),
  have extang2 := angle_extension_of_B bc.symm (B_of_online_inter cd ed.symm ce LM.symm cM dM eM dL nss),
  have bis := angle_symm2_of_angle ca.symm ea.symm bc be (sss (by linarith : length c a = length c b)
    (by linarith [length_symm a e, length_symm b e] : length a e = length b e) rfl).2.1,
  have adbsplit := len_symm_of_len (sas (rfl : length c d = length c d) (by linarith : length c a = length c b)
    (by linarith)).1,
  use d,
  split,
  { cases B_of_three_online_ne ab (nq_of_nq_len ab adbsplit) (nq_of_nq_len ab.symm (len_symm2_of_len adbsplit).symm) aL bL dL  with
      Babd Bet,
    { exfalso, linarith [length_sum_of_B Babd, length_symm b d, len_pos_of_nq ab], },
    { cases Bet with Bbad,
      { exfalso, linarith [length_sum_of_B Bbad, length_symm b d, len_pos_of_nq ab.symm], },
      exact Bet, }, },
  exact adbsplit,
end

theorem bisangiso {a b c : point} {L M : line} (ab : a ≠ b) (ac : a ≠ c) (LM : L ≠ M)
  (aL : online a L) (bL : online b L) (aM : online a M) (cM : online c M)
  (abeqac : length a b = length a c) : ∃ (d : point), angle b a d = angle c a d ∧ sameside d b M ∧
  sameside d c L ∧ B b d c :=
begin
  -- *** FIX THIS ***
  have : ∀ a b c : point, ∀ L M : line, a ≠ b → a ≠ c → L ≠ M → online a L → online a M →
    online b L → online c M → b ≠ c := λ a b c L M ab ac LM aL aM bL cM bc,
     LM (line_unique_of_pts ab aL bL aM (by rwa bc.symm at cM)),
  rcases bisline (this _ _ _ _ _ ab ac LM aL aM bL cM) with ⟨d, Bbdc, len⟩,
  rcases line_of_B Bbdc with ⟨N, bN, dN, cN, bd, dc, - ⟩,
  have dM : ¬online d M := λ dM, LM (line_unique_of_pts ab aL bL aM (by rwa (line_unique_of_pts dc.symm cN dN cM dM) at bN)),
  have dL : ¬online d L := λ dL, LM (line_unique_of_pts ac aL (by rwa (line_unique_of_pts bd bN dN bL dL) at cN) aM cM),
  refine ⟨d, (sss abeqac (len_symm_of_len len.symm).symm rfl).2.1, sameside23_of_B123_online1_not_online2 (B_symm Bbdc) cM dM, sameside23_of_B123_online1_not_online2 Bbdc bL dL, by btw⟩ ,
end

--Euclid I.9
theorem bisang {a b c : point} {L M : line} (ab : a ≠ b) (ac : a ≠ c) (LM : L ≠ M)
  (aL : online a L) (bL : online b L) (aM : online a M) (cM : online c M) :
  ∃ (d : point), angle b a d = angle c a d ∧ sameside d b M ∧ sameside d c L :=
begin
  rcases same_length_B_of_ne_four ab ac with ⟨d, Babd, bdac⟩,
  rcases same_length_B_of_ne_four ac ab with ⟨e, Bace, ceab⟩,
  have length : length a d = length a e := by linarith [length_sum_of_B Babd, length_sum_of_B Bace],
  have key := bisangiso (ne_13_of_B Babd) (ne_13_of_B Bace) LM aL (online_3_of_B Babd aL bL) aM
    (online_3_of_B Bace aM cM) length,
  rcases key with ⟨f, ang, ss1, ss2, Bdfe⟩,
  rcases line_of_B Bdfe with ⟨N, dN, fN, eN, -, -, -⟩,
  have af : a ≠ f := λ af, LM ((rfl.congr (eq.symm (line_unique_of_pts (ne_13_of_B Babd) aL (online_3_of_B Babd aL bL)
    (by rwa af.symm at fN) dN))).mp (line_unique_of_pts (ne_13_of_B Bace) aM (online_3_of_B Bace aM cM)
    (by rwa af.symm at fN) eN)).symm,
  refine ⟨f, by linarith [angle_extension_of_B af Babd, angle_extension_of_B af Bace], sameside_trans (sameside_symm ss1) (sameside_symm (sameside23_of_B123_online1_not_online2 Babd aM
    (λ bM, LM (line_unique_of_pts ab aL bL aM bM)))), sameside_trans (sameside_symm ss2) (sameside_symm (sameside23_of_B123_online1_not_online2 Bace aL (λ cL,
    LM (line_unique_of_pts ac aL cL aM cM))))⟩,
end

--Euclid I.11
theorem perpline {a b c : point} (Babc : B a b c) :
  ∃ (d : point), angle a b d = rightangle ∧ angle c b d = rightangle :=
begin
  rcases same_length_B_of_ne_four ((ne_12_of_B Babc).symm) (ne_23_of_B Babc) with ⟨e, Bbae, len1⟩,
  rcases same_length_B_of_ne_four (ne_23_of_B Babc) (ne_12_of_B Bbae) with ⟨f, Bbcf, len2⟩,
  rcases iseqtri_iseqtri_diffside_of_ne ((ne_13_of_B (B124_of_B123_B234 (B_symm Bbae) (B124_of_B123_B234 Babc Bbcf)))) with
    ⟨d, d1, L, ⟨len1, len2, len3, nq⟩, other, eL, fL, dL, d1L, nss⟩,
  have bd := (neq_of_online_offline (online_3_of_B (B_symm Bbae) eL (online_2_of_B (B124_of_B123_B234 (B_symm Bbae) (B124_of_B123_B234 Babc Bbcf)) eL fL)) dL),
  have := angle_symm_of_angle  (angle_extension_of_B bd Bbcf).symm,
  have := angle_symm_of_angle (angle_extension_of_B bd Bbae).symm,
  have := angle_symm_of_angle (angle_extension_of_B bd Bbcf),
  have len4 : length e b = length f b := by apply len_symm2_of_len; linarith [length_sum_of_B Bbcf, length_sum_of_B Bbae], --proof
  have key := (angle_eq_iff_rightangle (online_2_of_B (B124_of_B123_B234 (B_symm Bbae) (B124_of_B123_B234 Babc Bbcf)) eL fL)
  (online_2_of_B (B124_of_B123_B234 (B_symm Bbcf) (B124_of_B123_B234 (B_symm Babc)
    Bbae)) fL eL) dL Babc).1 (by linarith [(angle_extension_of_B bd Bbcf), (sss len3 len4 rfl).2.2]),
  refine ⟨d, key, by linarith [(sss len3 len4 rfl).2.2]⟩,
end

--Euclid I.11
theorem perplinecor {a b c p : point} {O : line} (aO : online a O) (cO : online c O)
  (pO : ¬online p O) (Babc : B a b c) :
  ∃ (d : point), angle a b d = rightangle ∧ angle c b d = rightangle ∧ sameside d p O :=
begin
  rcases same_length_B_of_ne_four ((ne_12_of_B Babc).symm) (ne_23_of_B Babc) with ⟨e, Bbae, len1⟩,
  rcases same_length_B_of_ne_four (ne_23_of_B Babc) (ne_12_of_B Bbae) with ⟨f, Bbcf, len2⟩,
  rcases iseqtri_iseqtri_diffside_of_ne ((ne_13_of_B (B124_of_B123_B234 (B_symm Bbae) (B124_of_B123_B234 Babc Bbcf)))) with ⟨d, d1, L,
    ⟨len1, len2, len3, nq⟩, ⟨len4, len5, len6, nq1⟩, eL, fL, ds⟩,
  have bd := (neq_of_online_offline (online_3_of_B (B_symm Bbae) eL (online_2_of_B (B124_of_B123_B234 (B_symm Bbae) (B124_of_B123_B234 Babc Bbcf)) eL fL)) ds.1),
  have bd1 := (neq_of_online_offline (online_3_of_B (B_symm Bbae) eL (online_2_of_B (B124_of_B123_B234 (B_symm Bbae) (B124_of_B123_B234 Babc Bbcf)) eL fL)) ds.2.1),
  have := angle_symm_of_angle (angle_extension_of_B bd Bbcf).symm,
  have := angle_symm_of_angle (angle_extension_of_B bd Bbae).symm,
  have := angle_symm_of_angle (angle_extension_of_B bd Bbcf),
  have := angle_symm_of_angle (angle_extension_of_B bd1 Bbcf).symm,
  have := angle_symm_of_angle (angle_extension_of_B bd1 Bbae).symm,
  have := angle_symm_of_angle (angle_extension_of_B bd1 Bbcf),
  have len4 : length e b = length f b := by apply len_symm2_of_len; linarith [length_sum_of_B Bbcf, length_sum_of_B Bbae], --proof
  by_cases sameside d p O,
  { have key := (angle_eq_iff_rightangle (online_2_of_B (B124_of_B123_B234 (B_symm Bbae) (B124_of_B123_B234 Babc Bbcf)) eL fL) (online_2_of_B (B124_of_B123_B234 (B_symm Bbcf) (B124_of_B123_B234 (B_symm Babc)      Bbae)) fL eL) ds.1 Babc).1 (by linarith [angle_extension_of_B bd Bbcf, (sss len3 len4 rfl).2.2]),
    refine ⟨d, key, by linarith [(sss len3 len4 rfl).2.2], h⟩, },
  have OL := line_unique_of_pts (ne_13_of_B Babc) aO cO (online_2_of_B (B124_of_B123_B234 (B_symm Bbae) (B124_of_B123_B234 Babc Bbcf)) eL fL)
    (online_2_of_B (B124_of_B123_B234 (B_symm Bbcf) (B124_of_B123_B234 (B_symm Babc) Bbae)) fL eL),
  rw OL at h,
  rw OL at pO,
  rw OL, --anything better here? *** YES
  have key := (angle_eq_iff_rightangle (online_2_of_B (B124_of_B123_B234 (B_symm Bbae) (B124_of_B123_B234 Babc Bbcf))
    eL fL)
    (online_2_of_B (B124_of_B123_B234 (B_symm Bbcf) (B124_of_B123_B234 (B_symm Babc) Bbae)) fL eL) ds.2.1 Babc).1 (by linarith [angle_extension_of_B bd1 Bbcf, (sss len6 len4 rfl).2.2]),
  refine ⟨d1, key, by linarith [(sss len6 len4 rfl).2.2], sameside_of_diffside_diffside ds ⟨ds.1, pO, h⟩⟩,
end

--Euclid I.12
theorem perppointnon { c : point} {O : line} (cO : ¬online c O) : ∃ (e h g : point), online e O ∧
  online h O ∧ online g O ∧ B e h g ∧ angle c h e = rightangle ∧ angle c h g = rightangle :=
begin
  rcases diffside_of_not_online cO with ⟨d, dO, dcO⟩,
  rcases circle_of_ne (λ cd, (by rwa cd at dcO : ¬sameside d d O) (sameside_rfl_of_not_online dO) : c ≠ d) with ⟨α, dcirc, ccen⟩,
  rcases pts_of_line_circle_inter (line_circle_inter_of_not_sameside dcO (by left; exact dcirc) (by right; exact (inside_circle_of_center ccen))) with
    ⟨e, g,eg, eO, gO, ecirc, gcirc⟩,
  rcases bisline eg with ⟨h, Behg, len⟩,
  have := (sss ((oncircle_iff_length_eq ecirc ccen).mpr gcirc) (len_symm_of_len len.symm).symm rfl).2.2,
  have := angle_symm c h e,
  have := (angle_eq_iff_rightangle eO gO cO Behg).mp (by linarith),
  refine ⟨e, h, g, eO, (online_2_of_B Behg eO gO), gO, Behg, by linarith, by linarith⟩,
end

--Euclid I.13
theorem flatsumright {a b c d : point} {L : line} (dL : online d L) (cL : online c L)
  (aL : ¬online a L) (Bdbc : B d b c) : angle a b c + angle a b d = 2 * rightangle :=
begin
  --have := bet_nq2 dL cL aL Bdbc,
  have ab : a≠ b:= (neq_of_bet dL cL aL Bdbc).symm,
  rcases line_of_pts a b with ⟨N, aN, bN⟩,
  by_cases (angle a b c = angle a b d),
  { linarith [(angle_eq_iff_rightangle dL cL aL Bdbc).mp ((angle_symm_of_angle h.symm)), (angle_symm_of_angle  h.symm)], },
  rcases perplinecor cL dL aL (B_symm Bdbc) with ⟨e, a1, a2, eaL⟩,
  have eb := (neq_of_online_offline (online_2_of_B Bdbc dL cL) (not_online_of_sameside eaL)).symm,
  rcases line_of_pts e b with ⟨M, eM, bM⟩,
  have ra : angle e b c = angle e b d := by linarith [angle_symm c b e, angle_symm d b e],
  have aM : ¬online a M,
  { intro aM,
    have ae : a ≠ e := λ ae, (by rwa ae at h : (¬(angle e b c = angle e b d))) ra,
    cases B_of_three_online_ne (neq_of_online_offline (online_2_of_B Bdbc dL cL) aL).symm ae eb.symm aM bM eM ,
    --- *** BAD don't use `h_1`
    { exact (not_sameside13_of_B123_online2 h_1 (online_2_of_B Bdbc dL cL)) (sameside_symm eaL), },
    cases h_1,
    exact (by rwa [angle_extension_of_B (ne_23_of_B Bdbc) h_1,
      angle_extension_of_B ((ne_12_of_B Bdbc).symm) h_1] at h : (¬(angle e b c = angle e b d))) ra,
    exact (by rwa [←(angle_extension_of_B (ne_23_of_B Bdbc) (B_symm h_1)),
      ←(angle_extension_of_B ((ne_12_of_B Bdbc).symm) (B_symm h_1))] at h : (¬(angle e b c = angle e b d))) ra, },
  wlog acM : (sameside a c M) using [c d, d c],
  { by_cases h1 : sameside a c M,
    { left, assumption, },
    right,
    have cM : ¬online c M := λ cM, (not_online_of_sameside eaL)
      (by rwa (line_unique_of_pts (ne_23_of_B Bdbc) bM cM (online_2_of_B Bdbc dL cL) cL) at eM),
    have dM : ¬online d M := λ dM, (not_online_of_sameside eaL)
      (by rwa (line_unique_of_pts ((ne_12_of_B Bdbc).symm) bM dM (online_2_of_B Bdbc dL cL) dL) at eM),
    exact sameside_of_diffside_diffside ⟨cM, aM, difsym h1⟩ ⟨cM, dM, difsym (not_sameside13_of_B123_online2 Bdbc bM)⟩, },
    --end of proof of wlog; not worth it?
  { have splitcbe := (angle_add_iff_sameside (ne_23_of_B Bdbc) eb.symm (online_2_of_B Bdbc dL cL) cL bM eM  aM aL (λ LM, (not_online_of_sameside eaL)
      (by rwa ← LM at eM))).mpr ⟨sameside_symm acM, eaL⟩,
    have eNL : ¬online e N ∧ ¬online e L := ⟨(λ eN, (by rwa (line_unique_of_pts eb eM bM eN bN) at aM :
      ¬online a N) aN), (λ eL, (not_online_of_sameside eaL) eL)⟩,
    have deN : sameside d e N,
    { have cN : ¬online c N := λ cN,
        aL (by rwa (line_unique_of_pts (ne_23_of_B Bdbc) bN cN (online_2_of_B Bdbc dL cL) cL) at aN),
      have dN : ¬online d N  := λ dN,
        aL (by rwa (line_unique_of_pts ((ne_12_of_B Bdbc).symm) bN dN (online_2_of_B Bdbc dL cL) dL) at aN),
      exact sameside_symm (sameside_of_diffside_diffside ⟨cN, eNL.1, difsym (not_sameside_of_sameside_sameside bM bN (online_2_of_B Bdbc dL cL) eM aN cL acM eaL)⟩
        ⟨cN, dN, difsym (not_sameside13_of_B123_online2 Bdbc bN)⟩), },
    have splitabd := (angle_add_iff_sameside ab.symm ((ne_12_of_B Bdbc).symm) bN aN (online_2_of_B Bdbc dL cL) dL  eNL.2 eNL.1
      (λ NL, aL (by rwa NL at aN))).mpr ⟨sameside_symm eaL, deN⟩,
    have flipcbe := angle_symm c b e,
    have flipabc := angle_symm a b c,
    linarith [(angle_eq_iff_rightangle dL cL eNL.2 Bdbc).mp (by linarith)], },
  linarith [this cL dL (B_symm Bdbc) (λ hh, h hh.symm) a2 a1 ra.symm],
end

-- Euclid I.14
theorem rightimpflat {a b c d : point} {N : line} (ab : a ≠ b) (aN : online a N) (bN : online b N)
  (cdN : diffside c d N) (ang : angle a b c + angle a b d = 2 * rightangle) : B c b d :=
begin
  have cd := difneq cdN, --API and degenerate cases
  have bd : b ≠ d := λ bd, cdN.2.1 (by rwa bd at bN),
  rcases same_length_B_of_ne (neq_of_online_offline bN cdN.1).symm (neq_of_online_offline bN cdN.1) with ⟨e, Bcbe, len⟩,
  rcases line_of_pts b c with ⟨M, bM, cM⟩,
  have eM := online_3_of_B Bcbe cM bM,
  have eN : ¬online e N := λ eN, cdN.1 (online_3_of_B (B_symm Bcbe) eN bN),
  have edN := sameside_of_diffside_diffside ⟨cdN.1, eN, difsym (not_sameside13_of_B123_online2 (B_symm Bcbe) bN)⟩ cdN,
  rcases line_of_pts b d with ⟨L, bL, dL⟩,
  have LN : L ≠ N := λ LN, cdN.2.1 (by rwa LN at dL),
  by_cases eL : online e L,
  { exact B_of_online_inter  (neq_of_online_offline bN cdN.1).symm bd cd LN (online_3_of_B (B_symm Bcbe) eL bL) bL dL bN  cdN.2.2, },
  have dM : ¬online d M := λ dM, eL (by rwa (line_unique_of_pts bd bM dM bL dL) at eM),
  have ae : a ≠ e := λ ae, eN (by rwa ae at aN),
  by_cases ed : e = d, { rwa ed at Bcbe, },
  have ang1 := flatsumright cM eM (λ aM, cdN.1 (by rwa ← (line_unique_of_pts ab aN bN aM bM) at cM)) Bcbe, --beginning of proof
  by_cases eaL : sameside e a L,
  { have split := (angle_add_iff_sameside bd ab.symm bL dL bN aN eN eL LN).mpr ⟨sameside_symm edN, sameside_symm eaL⟩,
    have dM := ((angle_zero_iff_online (ne_23_of_B Bcbe) bd bM eM).mpr (by linarith [angle_symm a b e,
      angle_symm a b d, angle_symm d b e])).1,
    exact B_of_online_inter  (by show_term{btw}) bd cd ((λ NM, eN (by rwa NM at eM)) : M≠ N) cM bM dM bN  cdN.2.2 },
  have adM := sameside_of_sameside_not_sameside ab.symm bN bL bM aN dL eM eL (sameside_symm edN) (difsym eaL),
  have split := (angle_add_iff_sameside ab.symm (ne_23_of_B Bcbe) bN aN bM eM dM (not_online_of_sameside (sameside_symm edN))
    (λ NM, eN (by rwa ← NM at eM))).mpr ⟨adM, edN⟩,
  have dM := ((angle_zero_iff_online (ne_23_of_B Bcbe) bd bM eM).mpr (by linarith [angle_symm a b e,
    angle_symm a b d, angle_symm d b e])).1,
  exact B_of_online_inter (by show_term{btw}) bd cd (((λ NM, eN (by rwa NM at eM)) : M≠ N)) cM bM dM bN  cdN.2.2,
end

--Euclid I.15
theorem vertang {a b c d e : point} {L : line} (cL : online c L) (dL : online d L)
  (aL : ¬online a L) (Bced : B c e d) (Baeb : B a e b) : angle b e c = angle d e a :=
begin
  rcases line_of_B Baeb with ⟨N, aN, eN, bN, -,nq,-⟩,
  have dN : ¬online d N := λ dN,
    ((by rwa (line_unique_of_pts (ne_23_of_B Bced) (online_2_of_B Bced cL dL) dL eN dN) at aL) : ¬online a N) aN,
  have bL : ¬online b L := λ bL,
    (by rwa line_unique_of_pts nq (online_2_of_B Bced cL dL) bL eN bN at aL : ¬online a N) aN,
  have := flatsumright cL dL bL Bced,
  have := flatsumright aN bN dN Baeb,
  linarith [angle_symm a e d, angle_symm b e d],
end

--Euclid I.16 (Elliptic geometry fails)
theorem extang {a b c d : point} {L : line} (aL : ¬online a L) (bL : online b L) (dL : online d L)
  (Bbcd : B b c d) : angle b a c < angle a c d :=
begin
  have cL := online_2_of_B Bbcd bL dL,
  have ca := neq_of_online_offline cL aL,
  have ba := neq_of_online_offline bL aL,
  rcases bisline ca with ⟨e, Bcea, len⟩,
  have be : b ≠ e := λ be, aL (online_3_of_B Bcea cL (by rwa be at bL)),
  rcases same_length_B_of_ne be be.symm with ⟨f, Bbef, len2⟩,
  have cf : c ≠ f := λ cf, aL (online_3_of_B Bcea cL (online_2_of_B Bbef bL (by rwa cf at cL))),
  have afL := sameside_trans (sameside23_of_B123_online1_not_online2 Bcea cL (λ eL, aL ((online_3_of_B Bcea) cL eL)))
    (sameside23_of_B123_online1_not_online2 Bbef bL (λ eL, aL ((online_3_of_B Bcea) cL eL))),
  rcases line_of_B Bbef with ⟨M, bM, eM, fM, -⟩,
  have cM : ¬online c M := λ cM,
    ((by rwa ← (line_unique_of_pts (ne_12_of_B Bbcd) bM cM bL cL) at aL) : ¬online a M) (online_3_of_B Bcea cM eM),
  have ang := vertang bM fM cM Bbef Bcea,
  have ang2 := (sas (len_symm_of_len len2.symm).symm (len_symm_of_len len) (by linarith [angle_symm b e a])).2.2,
  rcases line_of_B Bcea with ⟨N, cN, eN, aN, -,-,nq⟩,
  have fN : ¬online f N := λ fN,
    aL (by rwa (line_unique_of_pts (ne_12_of_B Bbcd) (online_3_of_B (B_symm Bbef) fN eN) cN bL cL) at aN),
  have bN : ¬online b N := λ bN, fN (online_3_of_B Bbef bN eN),
  have dfN := sameside_symm (sameside_of_diffside_diffside ⟨bN, fN, not_sameside13_of_B123_online2 Bbef eN⟩ ⟨bN, (λ dN, bN (online_3_of_B (B_symm Bbcd) dN cN)),
    not_sameside13_of_B123_online2 Bbcd cN⟩),
  have NL : N ≠ L := λ NL, bN (by rwa ←NL at bL), --start of pf below, API above
  have splitang := (angle_add_iff_sameside nq.symm (ne_23_of_B Bbcd) cN aN cL dL (not_online_of_sameside (sameside_symm afL))
    (not_online_of_sameside (sameside_symm dfN)) NL).mpr ⟨afL, dfN⟩,
  rcases line_of_pts c f with ⟨P, cP, fP⟩,
  have geq := lt_of_le_of_ne (angle_nonneg f c d) (ne_comm.mp (mt (angle_zero_iff_online cf (ne_23_of_B Bbcd) cP fP).mpr _)),--better way to deal with or?
  have geq2 := lt_of_le_of_ne (angle_nonneg b a c) (angeasy ca ((ne_12_of_B Bbcd).symm)
    (ne_comm.mp (mt (angle_zero_iff_online ca.symm ba.symm aN cN).mpr _))),
  linarith [angle_symm c a b, angle_extension_of_B ba.symm (B_symm Bcea), angle_extension_of_B cf Bcea],
  exact λ bN, NL (line_unique_of_pts (ne_12_of_B Bbcd) bN.1 cN bL cL),
  exact λ dP, not_online_of_sameside (sameside_symm (by rwa ←(line_unique_of_pts (ne_23_of_B Bbcd) cP dP.1 cL dL) at afL)) fP,
end

--Euclid I.16 (Elliptic geometry fails)
theorem extangcor {a b c d : point} {L : line} (aL : ¬online a L) (bL : online b L)
  (dL : online d L) (Bbcd : B b c d) : angle a b c < angle a c d :=
begin
  rcases same_length_B_of_ne (neq_of_online_offline (online_2_of_B Bbcd bL dL) aL).symm (neq_of_online_offline (online_2_of_B Bbcd bL dL) aL) with ⟨g, Bacg, len3⟩,
  have gb : g ≠ b := λ gb, aL (online_3_of_B (B_symm Bacg) (by rwa ← gb at bL) (online_2_of_B Bbcd bL dL)),
  have := angle_symm2_of_angle (ne_23_of_B Bacg).symm gb (ne_23_of_B Bbcd).symm (neq_of_online_offline dL aL)
    (vertang bL dL aL Bbcd Bacg),
  rcases line_of_B Bacg with ⟨N, aN, cN, gN, nq⟩,
  linarith [extang (λ bN, aL (by rwa line_unique_of_pts (ne_12_of_B Bbcd) bN cN bL (online_2_of_B Bbcd bL dL) at aN)) aN gN Bacg],
end

 --Euclid I.18
 theorem sidebigang {a b c : point} {L : line} (bc : b ≠ c) (bL : online b L) (cL : online c L)
  (aL : ¬online a L) (length : length a b < length a c) : angle b c a < angle a b c :=
begin
  rcases same_length_B_of_ne_le (neq_of_online_offline bL aL).symm length with ⟨d, Badc, len2⟩,
  rcases line_of_B Badc with ⟨M, aM, dM, cM, nq0,nq1,nq2⟩,
  have ang := extangcor (λ bM, aL (by rwa line_unique_of_pts bc bM cM bL cL at aM)) cM aM (B_symm Badc),
  have db : d ≠ b := neq_of_online_offline dM (λ bM, aL (by rwa line_unique_of_pts bc bM cM bL cL at aM)),
  have LM : L ≠ M := λ LM, aL (by rwa LM.symm at aM),
  rcases line_of_pts b a with ⟨N, bN, aN⟩,
  have adL : sameside a d L, {by_contra adL, exact not_B_symm (not_B_of_B (B_symm Badc))
    (B_of_online_inter nq2.symm nq1.symm (ne_12_of_B Badc) LM.symm aM cM dM cL  adL), },
  rcases line_of_pts d b with ⟨P, dP, bP⟩,
  have aP : ¬online a P := λ aP, LM (line_unique_of_pts bc bL cL (by rwa (line_unique_of_pts nq0 aP dP aM dM) at bP) cM),
  have cdN := sameside_of_sameside_not_sameside bc bL bP bN cL dP aN aP (sameside_symm adL) (not_sameside13_of_B123_online2 (B_symm Badc) dP),
  have splitang := (angle_add_iff_sameside bc (neq_of_online_offline bL aL) bL cL bN aN (not_online_of_sameside (sameside_symm cdN)) (not_online_of_sameside (sameside_symm adL))
    (λ LN, aL (by rwa ← LN at aN))).mpr ⟨cdN, adL⟩,
  have := eq_angle_of_eq_length (ne_12_of_B Badc) db len2,
  linarith [angle_symm c b a, angle_symm d b a, angle_symm a d b, (angle_nonneg c b d),
    angle_extension_of_B bc.symm (B_symm Badc), angle_symm b c d, angle_symm b c a],
end

--Euclid I.19 -- Probably can be turned into one line
theorem angbigside {a b c : point} {L : line} (bc : b ≠ c) (bL : online b L) (cL : online c L)
  (aL : ¬online a L) (ang : angle b c a < angle a b c) : length a b < length a c :=
begin
  by_cases len : length a b = length a c,
  { linarith [angle_symm b c a, eq_angle_of_eq_length (neq_of_online_offline bL aL).symm bc len], },
  by_cases len2 : length a c < length a b,
  { linarith [sidebigang bc.symm cL bL aL len2, angle_symm c b a, angle_symm b c a], },
  push_neg at len2,
  exact (ne.le_iff_lt len).mp len2,
end

--Euclid I.20
theorem triineq {a b c : point} {L : line} (ab : a ≠ b) (aL : online a L) (bL : online b L)
  (cL : ¬online c L) : length b c < length a b + length a c :=
begin
  have bc := neq_of_online_offline bL cL,
  rcases same_length_B_of_ne ab.symm (neq_of_online_offline aL cL) with ⟨d, Bbad, len⟩,
  have dc := neq_of_online_offline (online_3_of_B Bbad bL aL) cL,
  have ang := eq_angle_of_eq_length (ne_23_of_B Bbad) dc (len_symm_of_len len.symm).symm,
  rcases line_of_pts b c with ⟨M, bM, cM⟩,
  rcases line_of_pts d c with ⟨N, dN, cN⟩,
  have aN : ¬online a N := λ aN,
    cL (by rwa ← (line_unique_of_pts (ne_23_of_B Bbad) aL (online_3_of_B Bbad bL aL) aN dN) at cN),
  have adM := sameside23_of_B123_online1_not_online2 Bbad bM (λ aM, cL (by rwa (line_unique_of_pts ab aM bM aL bL) at cM)),
  have abN := sameside23_of_B123_online1_not_online2 (B_symm Bbad) dN aN,
  have angsplit := angles_add_of_sameside dc.symm bc.symm cN dN cM bM (sameside_symm adM) (sameside_symm (sameside23_of_B123_online1_not_online2 (B_symm Bbad) dN aN)),
  have bigside := angbigside dc.symm cN dN (not_online_of_sameside (sameside_symm abN)) (by linarith [angle_extension_of_B dc (B_symm Bbad),
    angle_symm d c b, angle_symm d c a, angle_symm c d b]),
  linarith [length_symm b a, length_symm c a, length_sum_of_B Bbad],
end

--Euclid I.20
theorem triineqcor {a b c : point} {L : line} (ab : a ≠ b) (aL : online a L) (bL : online b L)
  (cL : ¬online c L) : length b c < length a b + length a c ∧ length a c < length a b + length b c ∧
  length a b < length a c + length b c :=
begin
  rcases line_of_pts b c with ⟨M, bM, cM⟩,
  rcases line_of_pts a c with ⟨N, aN, cN⟩,
  have aM : ¬online a M := λ aM, cL (by rwa ← (line_unique_of_pts ab aL bL aM bM) at cM),
  have bN : ¬online b N := λ bN, cL (by rwa (line_unique_of_pts ab aN bN aL bL) at cN),
  exact ⟨triineq ab aL bL cL, by linarith [length_symm a b, length_symm a c, triineq (neq_of_online_offline bL cL) bM cM aM],
    by linarith [length_symm a c, length_symm b c, triineq (neq_of_online_offline aL cL).symm cN aN bN]⟩,
end

--Euclid I.22
theorem trimake {a1 a2 b1 b2 c1 c2 d f g : point} {L : line} (dL : online d L) (fL : online f L)
  (gL : ¬online g L) (ab : length c1 c2 < length a1 a2 + length b1 b2)
  (bc : length a1 a2 < length b1 b2 + length c1 c2) (ac : length b1 b2  < length a1 a2 + length c1 c2)
  (len : length d f = length a1 a2) :
  ∃ (k : point), length d k = length b1 b2 ∧ length f k = length c1 c2 ∧ sameside g k L :=
begin
  have df : d ≠ f := nq_of_len_pos (by linarith),
  have b1b2 : b1 ≠ b2,
  { intro b1b2, rw b1b2 at ab; rw b1b2 at bc, linarith [length_eq_zero_iff.mpr (rfl : b2 = b2)], },--????
  have c1c2 : c1 ≠ c2,
  { intro c1c2, rw c1c2 at ac; rw c1c2 at bc, linarith [length_eq_zero_iff.mpr (rfl : c2 = c2)], },
  rcases same_length_B_of_ne_four df.symm b1b2 with ⟨k1, Bfdk1, lenb⟩,
  rcases same_length_B_of_ne_four df c1c2 with ⟨k2, Bdfk2, lenc⟩,
  rcases circle_of_ne (ne_23_of_B Bdfk2) with ⟨α, k2circ, fcen⟩,
  rcases circle_of_ne (ne_23_of_B Bfdk1) with ⟨β, k1circ, dcen⟩,
  rcases pt_sameside_of_circles_inter fL dL gL fcen dcen (circint_of_lt_lt fcen dcen k2circ k1circ _ (by linarith [length_symm d f])) with
    ⟨k, kgL,kalph, kbet⟩,
  refine ⟨k, by linarith [(oncircle_iff_length_eq k1circ dcen).mpr kbet], by linarith [(oncircle_iff_length_eq k2circ fcen).mpr kalph],
    sameside_symm kgL⟩,
  apply abs_lt.mpr,
  exact ⟨by linarith [length_symm f d], by linarith [length_symm f d]⟩,
  exact ordered_add_comm_monoid.to_covariant_class_left ℝ,
  exact covariant_swap_add_le_of_covariant_add_le ℝ, --why do we have to do this?
end

--Euclid I.23
theorem angcopy {a b c d e h : point} {L M : line} (ab : a ≠ b) (ce : c ≠ e) (cL : online c L)
  (eL : online e L) (dL : ¬online d L) (aM : online a M) (bM : online b M) (hM : ¬online h M) :
  ∃ (f : point), angle b a f = angle e c d ∧ sameside f h M :=
begin
  rcases same_length_B_of_ne_four ce ab with ⟨e1, Bcee1, len⟩,
  rcases same_length_B_of_ne_four ab ce with ⟨b1, Babb1, len2⟩,
  have ineqs := triineqcor (ne_13_of_B Bcee1) cL (online_3_of_B Bcee1 cL eL) dL,
  have l3 : length a b1 = length c e1 := by linarith [length_sum_of_B Bcee1, length_sum_of_B Babb1],
  rcases trimake aM (online_3_of_B Babb1 aM bM) hM ineqs.1 ineqs.2.2 ineqs.2.1 l3 with ⟨f, l1, l2, hfM⟩,
  refine ⟨f, by linarith [(sss l3 l2 l1).2.1, angle_extension_of_B (neq_of_online_offline cL dL) Bcee1,
    angle_extension_of_B (neq_of_online_offline aM (not_online_of_sameside (sameside_symm hfM))) Babb1], sameside_symm hfM⟩,
end

--Euclid I.26 part 1
theorem asa {a b c d e f : point} {L : line} (ef : e ≠ f) (eL : online e L) (fL : online f L)
  (dL : ¬online d L) (side : length b c = length e f) (ang1 : angle c b a = angle f e d)
  (ang2 : angle a c b = angle d f e) :
  length a b = length d e ∧ length a c = length d f ∧ angle b a c = angle e d f :=
begin
  have bc : b ≠ c := λ bc, by linarith [len_pos_of_nq ef, length_eq_zero_iff.mpr bc],
  rcases line_of_pts b c with ⟨M, bM, cM⟩,
  by_cases len : length a b = length d e,
  { have congr := sas side (len_symm2_of_len len) ang1,
    exact ⟨len, len_symm2_of_len congr.1, congr.2.2⟩, },
  by_cases len1 : length d e < length a b,
  { exfalso,
    rcases same_length_B_of_ne_le (neq_of_online_offline eL dL).symm (by linarith [length_symm a b] : length d e < length b a) with
      ⟨g, Bbga, len2⟩,
    have ac : a ≠ c, --why was this so hard to do?
    { intro ac,
      have := mt (angle_zero_iff_online bc (ne_13_of_B Bbga) bM cM).mp (by linarith [angle_pos_of_not_colinear ef eL fL dL]),
      push_neg at this,
      by_cases online a M,
      exact (ne_13_of_B (this h)).symm ac,
      exact (neq_of_online_offline cM h).symm ac, },
    have aext := angle_extension_of_B bc Bbga,
    have := angle_symm c b a,
    have gc : g ≠ c,--can be oneliner
    { intro gc,
      rw gc at *,
      linarith [len_pos_of_nq (neq_of_online_offline fL dL), length_eq_zero_iff.mpr (rfl : c = c), (sas side (len_symm_of_len len2.symm).symm
        (by linarith)).1], },
    have := angle_symm c b g,
    have sasc := sas side (len_symm_of_len len2.symm).symm (by linarith),
    rcases line_of_pts a c with ⟨N, aN, cN⟩,
    have gM : ¬online g M,--oneliner?
    { intro gM,
      have := (area_zero_iff_online bc bM cM).mpr gM,
      exact (mt (area_zero_iff_online ef eL fL).mp dL) (by rwa (area_eq_of_SSS side sasc.1 (len_symm_of_len len2)) at this), },
    rcases line_of_B Bbga with ⟨O, bO, gO, aO, -,nq,-⟩,
    have gN : ¬online g N := λ gN, (lines_neq_of_online_offline gN gM) (line_unique_of_pts bc (by rwa (line_unique_of_pts nq gO aO gN aN) at
      bO : online b N) cN bM cM),
    have key := angles_add_of_sameside ac.symm bc.symm cN aN cM bM (sameside_symm (sameside23_of_B123_online1_not_online2 Bbga bM gM))
      (sameside_symm (sameside23_of_B123_online1_not_online2 (B_symm Bbga) aN gN)),
    linarith [angle_symm e f d, angle_symm g c b], },
  have ab : a ≠ b,--oneliner?
  { intro ab,
    rw ← ab at *,
    linarith [angle_symm e f d, angle_pos_of_not_colinear ef.symm fL eL dL, (angle_zero_iff_online bc.symm bc.symm cM bM).mp
      ⟨bM, (λ Bcac, (ne_13_of_B Bcac) rfl)⟩], },
  push_neg at len1,
  rcases same_length_B_of_ne_le ab (by linarith [((ne.le_iff_lt len).mp len1), length_symm d e] : length a b < length e d) with
    ⟨g, Begd, len2⟩,
  have := angle_extension_of_B ef Begd,
  have := angle_symm f e d,
  rcases line_of_pts e d with ⟨M, eM, dM⟩,
  rcases line_of_pts f d with ⟨N, fN, dN⟩,
  have gL : ¬online g L := λ gL, dL (online_3_of_B Begd eL gL),
  have sasc := sas side (len_symm_of_len len2.symm) (by linarith [angle_symm f e g]),
  have gN : ¬online g N,--oneliner?
  { intro gN,
    have := line_unique_of_pts (ne_23_of_B Begd) gN dN (online_2_of_B Begd eM dM) dM,
    exact (lines_neq_of_online_offline gN gL) (line_unique_of_pts ef eL fL (by rwa ← this at eM : online e N) fN).symm, },
  have key := angles_add_of_sameside (neq_of_online_offline fL dL) ef.symm fN dN fL eL (sameside_symm (sameside23_of_B123_online1_not_online2 Begd eL gL))
    (sameside_symm (sameside23_of_B123_online1_not_online2 (B_symm Begd) dN gN)),
  linarith [angle_symm b c a, angle_symm e f g],
end

--Euclid I.27
theorem angeqpar {a e f d : point} {L M N : line} (ae : a ≠ e) (ef : e ≠ f) (fd : f ≠ d)
  (aM : online a M) (eM : online e M) (fN : online f N) (dN : online d N)
  (eL : online e L) (fL : online f L) (ang : angle a e f = angle e f d) (adL : diffside a d L) :
  para M N :=
begin
  intro g,
  by_contra gMN,
  push_neg at gMN,
  have ML : M ≠ L := λ ML, adL.1 (by rwa ML at aM),
  have NL : N ≠ L := λ NL, adL.2.1 (by rwa NL at dN),
  have eN : ¬online e N := λ eN, NL (line_unique_of_pts ef eN fN eL fL),
  have fM : ¬online f M := λ fM, ML (line_unique_of_pts ef eM fM eL fL),
  have gL : ¬online g L := λ gL, ML (line_unique_of_pts (neq_of_online_offline gMN.2 eN) gMN.1 eM gL eL),
  have dg : d ≠ g,
  { intro dg,
    rw dg at *,
    linarith [angle_symm a e f, angle_symm e f g, extang fM gMN.1 aM
    (B_symm (B_of_online_inter  ae (neq_of_online_offline eL gL) (difneq adL) ML aM eM gMN.1 eL adL.2.2))], },
  have ag : a ≠ g,
  { intro ag,
    rw ag at *,
    linarith [extang eN gMN.2 dN (B_symm (B_of_online_inter fd.symm (neq_of_online_offline fL gL) dg NL dN fN gMN.2 fL
    (difsym adL.2.2)))], },
  cases sameside_or_of_diffside adL.2.1 adL.1 gL (difsym adL.2.2) with dgL agL,
  { by_cases Bfdg : B f d g,
    { have Baeg := B_of_online_inter ae (neq_of_online_offline gMN.2 eN).symm ag ML aM eM gMN.1 eL
        (difsym (difsamedif dgL ⟨adL.2.1, adL.1, difsym adL.2.2⟩).2.2),
      have ang1 := extang fM gMN.1 (online_3_of_B (B_symm Baeg) gMN.1 eM) (B_symm Baeg),
      linarith [angle_extension_of_B (neq_of_online_offline eM fM).symm Bfdg, angle_symm d f e, angle_symm f e a], },
    by_cases Bfgd : B f g d,
    { have Baeg := B_of_online_inter ae (neq_of_online_offline gMN.2 eN).symm ag ML aM eM gMN.1 eL (difsym (difsamedif dgL
        ⟨adL.2.1, adL.1, difsym adL.2.2⟩).2.2),
      have ang1 := extang fM gMN.1 (online_3_of_B (B_symm Baeg) gMN.1 eM) (B_symm Baeg),
      linarith [angle_symm a e f, angle_symm e f g, angle_symm d f e,
        angle_extension_of_B ef.symm Bfgd], },
    cases B_of_three_online_ne fd (neq_of_online_offline fL gL) dg fN dN gMN.2 ,
    exact Bfdg h,
    cases h with Bdfg,
    exact (not_sameside13_of_B123_online2 Bdfg fL) dgL,
    exact Bfgd h, },
  by_cases Beag : B e a g,
  { have ang1 := extang eN gMN.2 dN (B_symm (B_of_online_inter fd.symm (neq_of_online_offline fL gL) dg NL dN fN gMN.2 fL
      (difsym (difsamedif agL adL).2.2))),
    linarith [angle_extension_of_B ef Beag], },
  by_cases Bega : B e g a,
  { have ang1 := extang eN gMN.2 dN (B_symm (B_of_online_inter fd.symm (neq_of_online_offline fL gL) dg NL dN fN gMN.2 fL
      (difsym (difsamedif agL adL).2.2))),
    linarith [angle_extension_of_B ef Bega], },
  cases B_of_three_online_ne ae.symm (neq_of_online_offline eL gL) ag eM aM gMN.1 ,
  exact Beag h,
  cases h with Baeg,
  exact (not_sameside13_of_B123_online2 Baeg eL) agL,
  exact Bega h,
end

--Euclid I.29
theorem parapost {a b d e g h : point} {L M N : line} (dh : d ≠ h) (aM: online a M) (gM: online g M)
  (dN: online d N)(hL : online h L) (hN: online h N)
  (gL : online g L) (par : para M N) (Bagb : B a g b) (Begh : B e g h)
  (bdL : sameside b d L) : angle a g h = angle g h d ∧ angle e g b = angle g h d ∧
  angle b g h + angle g h d = 2 * rightangle :=
begin
  rcases same_length_B_of_ne dh dh.symm with ⟨c, Bdhc, len⟩,
  have hM : ¬online h M, { cases par h, exact h_1, exfalso, exact h_1 hN, },--better way?
  have gN : ¬online g N, { cases par g, exfalso, exact h_1 gM, exact h_1 },--better way?
  have acL : sameside a c L := sameside_of_diffside_diffside (difsamedif bdL ⟨not_online_of_sameside bdL, λ aL, (not_online_of_sameside bdL) (online_3_of_B Bagb aL gL),
    difsym (not_sameside13_of_B123_online2 Bagb gL)⟩) ⟨(not_online_of_sameside (sameside_symm bdL)), λ cL, (not_online_of_sameside (sameside_symm bdL)) (online_3_of_B (B_symm Bdhc) cL hL),
    not_sameside13_of_B123_online2 Bdhc hL⟩,
  have := angle_symm h g b,
  have := angle_symm h g a,
  have := flatsumright aM (online_3_of_B Bagb aM gM) hM Bagb,
  have := flatsumright dN (online_3_of_B Bdhc dN hN) gN Bdhc,
  have key1 : angle a g h = angle g h d,
  { by_contra ang,
    by_cases ang1 : angle g h d < angle a g h, --anything better than the casework?
    { rcases unparallel_postulate (neq_of_online_offline gM hM) (online_3_of_B Bagb aM gM) gM gL hL hN dN bdL
        (by linarith) with ⟨e, eM, eN, junk⟩, -- *** `junk` can be replaced by `-`?
      cases par e,
      exact h_1 eM,
      exact h_1 eN, },
    push_neg at ang1,
    have ang2 : angle a g h < angle g h d := (ne.le_iff_lt ang).mp ang1,--anything better?
    rcases unparallel_postulate (neq_of_online_offline gM hM) aM gM gL hL hN (online_3_of_B Bdhc dN hN) acL
      (by linarith) with ⟨e, eM, eN, junk⟩,
    cases par e, exact h_1 eM, exact h_1 eN, },
  exact ⟨key1, by linarith [vertang hL (online_3_of_B (B_symm Begh) hL gL) (not_online_of_sameside bdL) (B_symm Begh) (B_symm Bagb)],
    by linarith⟩,
end

--Euclid I.29
theorem parapostcor {a d g h : point} {L M N : line} (dh : d ≠ h) (aM: online a M) (gM: online g M)
(hN: online h N) (dN: online d N) (hL : online h L)
  (gL : online g L) (par : para M N) (adL : diffside a d L) : angle a g h = angle g h d :=
begin
  have hg : h ≠ g,
  { intro hg, rw hg at *, cases par g, exact h_1 gM, exact h_1 hN, },
  rcases same_length_B_of_ne (neq_of_online_offline gL adL.1).symm (neq_of_online_offline gL adL.1) with ⟨b, Bagb, junk⟩,
  rcases same_length_B_of_ne hg hg.symm with ⟨e, Bhge, junk⟩,
  exact (parapost dh aM gM dN hL hN gL par Bagb (B_symm Bhge)
    (sameside_of_diffside_diffside ⟨adL.1, (λ bL, adL.1 (online_3_of_B (B_symm Bagb) bL gL)), not_sameside13_of_B123_online2 Bagb gL⟩ adL)).1,
end

--Euclid I.29
theorem parapostcor2 {b g h d : point} {L M N : line} (dh : d ≠ h) (bM: online b M) (gM: online g M)
(hN: online h N) (dN: online d N) (hL : online h L)
  (gL : online g L) (par : para M N) (bdL : sameside b d L) : angle b g h + angle g h d = 2 * rightangle  :=
begin
  have hg : h ≠ g,
  { intro hg, rw hg at *, cases par g, exact h_1 gM, exact h_1 hN, },
  rcases same_length_B_of_ne (neq_of_online_offline gL (not_online_of_sameside bdL)).symm (neq_of_online_offline gL (not_online_of_sameside bdL)) with ⟨a, Bbga, -⟩,
  rcases same_length_B_of_ne hg hg.symm with ⟨e, Bhge, -⟩,
  exact (parapost dh (online_3_of_B Bbga bM gM) gM dN hL hN gL par (B_symm Bbga) (B_symm Bhge)
    bdL).2.2,
end

--Euclid I.31
theorem drawpar {a b c : point} {L : line} (bc : b ≠ c) (bL : online b L) (cL : online c L)
  (aL : ¬online a L) : ∃ (e : point), ∃ (N : line),online e N ∧ online a N ∧ online b L ∧ online c L∧  para N L :=
begin
  rcases pt_B_of_ne bc with ⟨d, Bbdc⟩,
  have dL := online_2_of_B Bbdc bL cL,
  rcases line_of_pts d a with ⟨M, dM, aM⟩,
  have bM : ¬online b M := λ bM, (lines_neq_of_online_offline aM aL) (line_unique_of_pts bc bM (online_3_of_B Bbdc bM dM) bL cL),
  rcases angcopy (neq_of_online_offline dL aL).symm (ne_23_of_B Bbdc) dL cL aL aM dM bM with ⟨e, ang, ebM⟩,
  have ae : a ≠ e := λ ae, (not_online_of_sameside ebM) (by rwa ae at aM),
  rcases line_of_pts a e with ⟨N, aN, eN⟩,
  refine ⟨e, N,eN, aN, bL , cL,angeqpar ae.symm (neq_of_online_offline dL aL).symm (ne_23_of_B Bbdc) eN aN dL cL aM dM
    (by linarith [angle_symm e a d, angle_symm a d c]) (difsamedif (sameside_symm ebM)
    ⟨bM, (λ cM, bM (online_3_of_B (B_symm Bbdc) cM dM)), not_sameside13_of_B123_online2 Bbdc dM⟩)⟩,
end

theorem parasianar {a b c d : point} {L M N K : line} (aL: online a L) (bL: online b L)
 (cM: online c M) (dM: online d M) (aK: online a K) (cK: online c K) (bN: online b N) (dN: online d N)
 (par1 : para L M) (par2 : para K N) :
  length a b = length c d ∧ angle c a b = angle b d c ∧ area c a b = area b d c :=
begin
  have ab : a ≠ b := neq_of_online_offline aK (online_of_online_para' bN par2),
  have cd : c ≠ d := neq_of_online_offline cK (online_of_online_para' dN par2),
  have cb : c ≠ b := neq_of_online_offline cM (online_of_online_para bL par1),
  have ca : c ≠ a := neq_of_online_offline cM (online_of_online_para aL par1),
  rcases line_of_pts c b with ⟨O, cO, bO⟩,
  have adO := not_sameside_of_sameside_sameside bL bO bN aL cO dN
    (sameside_of_online_online_para' cM dM par1) (sameside_of_online_online_para aK cK par2),
  have aO : ¬online a O,
  { intro aO, have := line_unique_of_pts ab aL bL aO bO, rw this at par1, cases par1 c,
    exact h cO, exact h cM, },
  have dO : ¬online d O,
  { intro dO, have := line_unique_of_pts cd cO dO cM dM, rw this at *, cases par1 b,
    exact h bL, exact h bO, },
    have ang1:= parapostcor cd.symm aL bL cM dM cO bO par1 ⟨aO, dO, adO⟩,
  have ang2 := parapostcor ca.symm dN bN cK aK cO bO (para_symm par2) ⟨dO, aO, difsym adO⟩,
  have key := asa cb cO bO aO (length_symm b c) (by linarith [angle_symm c b d] : angle c b d = angle b c a)
    (by linarith [angle_symm d c b]),
  exact ⟨by linarith [length_symm c d], key.2.2.symm, (area_eq_of_SSS (len_symm2_of_len key.1) key.2.1 (length_symm c b)).symm⟩,
end

--Euclid I.35
theorem parallelarea1 {a b c d e f : point} {L M K N O P : line}
 (aL: online a L) (dL: online d L) (bM: online b M) (cM: online c M)
 (eL: online e L) (fL: online f L)
 (aK: online a K) (bK: online b K) (dN: online d N) (cN: online c N)
 (bO: online b O) (eO: online e O) (cP: online c P) (fP: online f P)
 (par1 : para L M)
  (par2 : para M L) (par3 : para K N) (par4 : para O P) (Baed : B a e d) :
  area b a d + area d b c = area c f e + area e c b :=
begin
  have ad := neq_of_online_offline aK (online_of_online_para' dN par3),
  have bc := neq_of_online_offline bK (online_of_online_para' cN par3),
  have eP := online_of_online_para eO par4,
  have dfM := sameside_of_online_online_para dL fL par1,
  have edM := sameside_of_online_online_para eL dL par1,
  have := parasianar aL dL bM cM aK bK dN cN par1 par3,
  have := parasianar bM cM eL fL bO eO cP fP par2 par4,
  by_cases af : a = f,
  { rw ← af at *,
    have := quadarea_comm ad bc aL dL bM cM dN cN (sameside_of_online_online_para aL dL par1)
      (sameside_of_online_online_para bM cM par2) (sameside_of_online_online_para aK bK par3),
    have := quadarea_comm (neq_of_online_offline eO (online_of_online_para' fP par4)) bc eL aL bM
      cM fP cP (sameside_of_online_online_para eL aL par1) (sameside_of_online_online_para' bM cM par1)
      (sameside_of_online_online_para eO bO par4),
    have := area_eq_of_SSS (by linarith : length a d = length e a) (parasianar aK bK dN cN aL dL bM cM par3 par1).1.symm
      (parasianar bO eO cP fP bM cM eL fL par4 par2).1.symm,
    linarith [area_invariant d c b, area_invariant d a b, area_invariant b d a, area_invariant c b e, area_invariant c b a, area_invariant c d a, area_invariant a c d, area_invariant a e b,
      area_invariant a b e],
  },
  by_cases df : d = f,
  { rw ← df at *,
    have NP := line_unique_of_pts (neq_of_online_offline dL (online_of_online_para' cM par1)) dN cN
      fP cP, rw ← NP at *, exfalso,
      cases B_of_three_online_ne (ne_12_of_B Baed) ad (ne_23_of_B Baed) aL eL dL ,

    linarith [length_sum_of_B h, len_pos_of_nq (ne_12_of_B Baed)],
    cases h,
    linarith [length_sum_of_B h, len_pos_of_nq (ne_12_of_B h)],
    have abN := sameside_of_online_online_para aK bK par3,
    exact (difsamedif abN ⟨not_online_of_sameside abN, eP, not_sameside13_of_B123_online2 h dN⟩).2.2
      (sameside_of_online_online_para bO eO par4),
   },
  have Bedf : B e d f,
  { cases B_of_three_online_ne (ne_23_of_B Baed) (neq_of_online_offline fP eP).symm df eL dL fL ,
    exact h,
    exfalso,
    cases h with Bdef Befd,
    { cases or.swap (Bbcd_or_Bbdc_of_Babc_Babd af (B_symm Baed) Bdef) with Befa Beaf,
      linarith [length_sum_of_B Befa, length_sum_of_B Baed, length_symm e a, len_pos_of_nq af, length_symm a f, len_pos_of_nq (ne_23_of_B Baed)],
      by_cases bfN : sameside b f N,
      { have dbP := difsym (not_sameside_of_sameside_sameside cM cP cN bM fP dN (sameside_symm dfM) bfN),
        have deP := sameside_symm (sameside23_of_B123_online1_not_online2 (B_symm Bdef) fP eP),
        exact (difsamedif deP ⟨(λ dP, eP (online_2_of_B (B_symm Bdef) fP dP)),
          online_of_online_para bO par4, dbP⟩).2.2 (sameside_symm (sameside_of_online_online_para bO eO par4)),
      },
      refine bfN (sameside_symm (sameside_trans (sameside23_of_B123_online1_not_online2
      (B_symm (B124_of_B123_B234 (B_symm Beaf) Baed)) dN (online_of_online_para aK par3))
        (sameside_of_online_online_para aK bK par3))),
    },
    linarith [length_sum_of_B Befd, length_sum_of_B Baed, len_pos_of_nq (ne_12_of_B Baed), len_pos_of_nq df, length_symm d f],
  },
  have := area_add_iff_B_mp aL dL eL (online_of_online_para' bM par1) Baed,
  have ebN := sameside_trans (sameside_symm (sameside23_of_B123_online1_not_online2 (B_symm Baed) dN (λ eN, (online_of_online_para aK par3)
    (online_3_of_B (B_symm Baed) dN eN)))) (sameside_of_online_online_para aK bK par3),
  have := quadarea_comm (ne_23_of_B Baed) bc eL dL bM cM dN cN edM (sameside_of_online_online_para' bM cM par1) ebN,
  have := parasianar aK bK dN cN aL dL bM cM par3 par1,
  have := length_sum_of_B Baed,
  have := length_sum_of_B Bedf,
  have := area_eq_of_SSS (by linarith : length a e = length d f).symm  (len_symm2_of_len (parasianar bO eO cP fP bM cM eL fL par4 par2).1.symm)
    (len_symm2_of_len (parasianar aK bK dN cN aL dL bM cM par3 par1).1).symm,
  have := area_add_iff_B_mp eL fL dL (online_of_online_para' cM par1) Bedf,
  linarith [area_invariant b a d, area_invariant b d a, area_invariant d c b, area_invariant d e b, area_invariant b d e, area_invariant e d c, area_invariant c e d, area_invariant d f c,
    area_invariant c f e, area_invariant c b e],
end

--Euclid I.35
theorem parallelarea2 {a b c d e f : point} {L M K N O P : line}
 (aL: online a L) (dL: online d L) (bM: online b M) (cM: online c M)
 (eL: online e L) (fL: online f L)
 (aK: online a K) (bK: online b K) (dN: online d N) (cN: online c N)
 (bO: online b O) (eO: online e O) (cP: online c P) (fP: online f P)
 (par1 : para L M)
  (par2 : para M L) (par3 : para K N) (par4 : para O P) (Bade : B a d e) :
  area b a d + area d b c = area c f e + area e c b :=
begin
    have ab := neq_of_online_offline aL (online_of_online_para' bM par1),
    have ad := neq_of_online_offline aK (online_of_online_para' dN par3),
    have eP := online_of_online_para eO par4,
    have bc := neq_of_online_offline bK (online_of_online_para' cN par3),
    have dc := neq_of_online_offline dL (online_of_online_para' cM par1),
    have ef := neq_of_online_offline eO (online_of_online_para' fP par4),
    have dfM := sameside_of_online_online_para dL fL par1,
    have := parasianar aL dL bM cM aK bK dN cN par1 par3,
    have := parasianar bM cM eL fL bO eO cP fP par2 par4,
    have bN:= online_of_online_para bK par3,
  by_cases af : a = f,
  { rw ← af at *,
     have := quadarea_comm ad bc aL dL bM cM dN cN (sameside_of_online_online_para aL dL par1)
      (sameside_of_online_online_para bM cM par2) (sameside_of_online_online_para aK bK par3),
    have := quadarea_comm (neq_of_online_offline eO (online_of_online_para' fP par4)) bc eL aL bM
      cM fP cP (sameside_of_online_online_para eL aL par1) (sameside_of_online_online_para' bM cM par1)
      (sameside_of_online_online_para eO bO par4),
    have := area_eq_of_SSS (by linarith : length a d = length e a) (parasianar aK bK dN cN aL dL bM cM par3 par1).1.symm
      (parasianar bO eO cP fP bM cM eL fL par4 par2).1.symm,
    linarith [area_invariant d c b, area_invariant d a b, area_invariant b d a, area_invariant c b e, area_invariant c b a, area_invariant c d a, area_invariant a c d, area_invariant a e b,
      area_invariant a b e],
  },
  by_cases df : d = f,
  { rw ← df at *, have NP := line_unique_of_pts (neq_of_online_offline dL (online_of_online_para' cM par1)) dN cN fP cP, rw ← NP at *,
    { exfalso,
    cases B_of_three_online_ne (ne_13_of_B Bade) ad (ne_23_of_B Bade).symm aL eL dL ,
      linarith [length_sum_of_B h, len_pos_of_nq (ne_13_of_B Bade)], cases h, linarith [length_sum_of_B h, len_pos_of_nq
        (ne_13_of_B Bade).symm],
         have abN := sameside_of_online_online_para aK bK par3,
         refine (difsamedif abN ⟨not_online_of_sameside abN, eP, not_sameside13_of_B123_online2 h dN⟩).2.2
      (sameside_of_online_online_para bO eO par4),
    },
  },
  have Bdef : B d e f,
  { cases B_of_three_online_ne (ne_23_of_B Bade) df ef dL eL fL ,
    exact h,
    exfalso,
    cases h with Bedf Bdfe,
    { by_cases bfN : sameside b f N,
      { have dP : ¬online d P := λ dP, eP (online_3_of_B (B_symm Bedf) fP dP),
        have dbP := difsym (not_sameside_of_sameside_sameside cM cP cN bM
          fP dN (sameside_symm dfM) bfN),
        exact (difsamedif (sameside23_of_B123_online1_not_online2 (B_symm Bedf) fP dP) ⟨dP, (online_of_online_para bO par4), dbP⟩).2.2
          (sameside_symm (sameside_of_online_online_para bO eO par4)),
      },
      cases Bbcd_or_Bbdc_of_Babc_Babd af (B_symm Bade) Bedf with Bdaf Bdfa,
      linarith [length_sum_of_B Bdaf, length_sum_of_B Bedf, len_pos_of_nq (ne_23_of_B Bade).symm, len_pos_of_nq af, length_symm a d],
      have fN := λ fN, (online_of_online_para aK par3) (online_3_of_B Bdfa dN fN),
      refine (difsamedif (sameside_symm (sameside_of_online_online_para aK bK par3)) ⟨bN, fN, bfN⟩).2.2
        (sameside_symm (sameside23_of_B123_online1_not_online2 Bdfa dN fN)),
    },
    have Bfda := Bbcd_of_Babc_Bacd (B_symm Bdfe) (B_symm Bade),
    by_cases bfN : sameside b f N,
    exact (not_sameside13_of_B123_online2 Bfda dN) (sameside_symm (sameside_trans (sameside_symm (sameside_of_online_online_para aK bK par3)) bfN)),
      have fN := λ fN, (online_of_online_para aK par3) (online_3_of_B Bfda fN dN),
    exact (not_sameside13_of_B123_online2 Bdfe fP) (sameside_trans (sameside_of_sameside_not_sameside
      bc.symm cM cN cP bM dN fP fN dfM bfN) (sameside_of_online_online_para bO eO par4)),
  },
  have dO := λ dO, (online_of_online_para' fP par4) (online_3_of_B Bdef dO eO),
  have eN := λ eN, (online_of_online_para aK par3) (online_3_of_B (B_symm Bade) eN dN),
  have cdO := (difsamedif (sameside_symm (sameside_of_online_online_para' cP fP par4))
    ⟨(online_of_online_para' fP par4), dO, difsym (not_sameside13_of_B123_online2 Bdef eO)⟩).2.2,
    have beN := (difsamedif (sameside_of_online_online_para aK bK par3) ⟨(online_of_online_para aK par3), eN,
    (not_sameside13_of_B123_online2 Bade dN)⟩).2.2,
  have beN := (difsamedif (sameside_of_online_online_para aK bK par3) ⟨(online_of_online_para aK par3), eN,
    (not_sameside13_of_B123_online2 Bade dN)⟩).2.2,
  rcases pt_of_lines_inter (lines_inter_of_not_sameside bO eO beN) with ⟨g, gN, gO⟩,
  have Bbge := B_of_online_inter (neq_of_online_offline gN bN).symm
    (neq_of_online_offline gN eN) (neq_of_online_offline bM (online_of_online_para' eL par2))
    (lines_neq_of_online_offline eO eN) bO gO eO gN  beN,
  have Bcgd := B_of_online_inter  (neq_of_online_offline gO (online_of_online_para' cP par4)).symm
  (neq_of_online_offline gO dO) dc.symm (lines_neq_of_online_offline eO eN).symm
    cN gN dN gO  cdO,
  have := parasianar aK bK dN cN aL dL bM cM par3 par1,
  have := length_sum_of_B Bade,
  have := length_sum_of_B Bdef,
  have := area_eq_of_SSS (by linarith : length a e = length d f).symm  (len_symm2_of_len (parasianar bO eO cP fP bM cM eL fL par4 par2).1.symm)
    (len_symm2_of_len (parasianar aK bK dN cN aL dL bM cM par3 par1).1).symm,
  have := area_add_iff_B_mp bO eO gO dO Bbge,
  have := area_add_iff_B_mp bO eO gO (λ cO, dO (online_3_of_B Bcgd cO gO)) Bbge,
  have := area_add_iff_B_mp cN dN gN (λ bN, eN (online_3_of_B Bbge bN gN)) Bcgd,
  have := area_add_iff_B_mp cN dN gN eN Bcgd,
  have := area_add_iff_B_mp aL eL dL (online_of_online_para' bM par1) Bade,
  have := area_add_iff_B_mp dL fL eL (online_of_online_para' cM par1) Bdef,
  linarith [area_invariant d c f, area_invariant c e f, area_invariant d e c, area_invariant c d e, area_invariant a b e, area_invariant a d b, area_invariant e g d, area_invariant d e g,
    area_invariant c b d, area_invariant d c b, area_invariant b g c, area_invariant c b g, area_invariant e c b, area_invariant b e c],
end

--Euclid I.35
theorem parallelarea3 {a b c d e f : point} {L M K N O P : line}
(aL: online a L) (dL: online d L) (bM: online b M) (cM: online c M)
 (eL: online e L) (fL: online f L)
 (aK: online a K) (bK: online b K) (dN: online d N) (cN: online c N)
 (bO: online b O) (eO: online e O) (cP: online c P) (fP: online f P)
(par1 : para L M)
  (par2 : para M L) (par3 : para K N) (par4 : para O P) (Bdae : B d a e) :
  area b a d + area d b c = area c f e + area e c b :=
begin
    have bc := neq_of_online_offline bK (online_of_online_para' cN par3),
    have ef := neq_of_online_offline eO (online_of_online_para' fP par4),
    have eP := online_of_online_para eO par4,
    have ad := neq_of_online_offline aK (online_of_online_para' dN par3),
    have := parasianar aL dL bM cM aK bK dN cN par1 par3,
    have := parasianar bM cM eL fL bO eO cP fP par2 par4,
  by_cases af : a = f,
  {
    rw ← af at *,
     have := quadarea_comm ad bc aL dL bM cM dN cN (sameside_of_online_online_para aL dL par1)
      (sameside_of_online_online_para bM cM par2) (sameside_of_online_online_para aK bK par3),
    have := quadarea_comm (neq_of_online_offline eO (online_of_online_para' fP par4)) bc eL aL bM
      cM fP cP (sameside_of_online_online_para eL aL par1) (sameside_of_online_online_para' bM cM par1)
      (sameside_of_online_online_para eO bO par4),
    have := area_eq_of_SSS (by linarith : length a d = length e a) (parasianar aK bK dN cN aL dL bM cM par3 par1).1.symm
      (parasianar bO eO cP fP bM cM eL fL par4 par2).1.symm,
    linarith [area_invariant d c b, area_invariant d a b, area_invariant b d a, area_invariant c b e, area_invariant c b a, area_invariant c d a, area_invariant a c d, area_invariant a e b,
      area_invariant a b e],
  },
  by_cases df : d = f,
  { rw ← df at *,
    have NP := line_unique_of_pts (neq_of_online_offline dL (online_of_online_para' cM par1)) dN cN fP cP, rw ← NP at *,
    exfalso,
    cases B_of_three_online_ne (ne_23_of_B Bdae) ad (ne_13_of_B Bdae).symm aL eL dL ,
    linarith [length_sum_of_B h, len_pos_of_nq (ne_23_of_B Bdae)],
    cases h,
    linarith [length_sum_of_B h, len_pos_of_nq (ne_23_of_B Bdae).symm],
    have abN := sameside_of_online_online_para aK bK par3,
    refine (difsamedif abN ⟨not_online_of_sameside abN, eP, not_sameside13_of_B123_online2 h dN⟩).2.2
      (sameside_of_online_online_para bO eO par4),
  },
  have key : B d f a ∨ B d a f,
  { by_contra key, push_neg at key,
    cases B_of_three_online_ne df (ne.symm ad) (ne.symm af) dL fL aL ,
    exact key.1 h,
    cases h,
    linarith [length_sum_of_B (B124_of_B123_B234 h Bdae), length_sum_of_B Bdae, length_symm a d, length_symm e f, len_pos_of_nq (ne_23_of_B Bdae),
      len_pos_of_nq (ne.symm df)],
    exact key.2 h,
  },
  cases key,
  have := parallelarea1 dL aL cM bM fL eL dN cN aK bK cP fP bO eO par1 par2 (para_symm par3) (para_symm par4) key,
  have := quadarea_comm (ne_13_of_B key).symm bc aL dL bM cM dN
    cN (sameside_of_online_online_para aL dL par1) (sameside_of_online_online_para' bM cM par1)
    (sameside_of_online_online_para aK bK par3),
  have := quadarea_comm ef bc eL fL bM cM fP cP
    (sameside_of_online_online_para' eL fL par2) (sameside_of_online_online_para' bM cM par1)
    (sameside_of_online_online_para' eO bO (para_symm par4)),
  linarith [area_invariant b a d, area_invariant d b a, area_invariant d b c, area_invariant c b e, area_invariant c b a, area_invariant b e f, area_invariant f b e, area_invariant f b c],
  have := parallelarea2 dL aL cM bM fL eL dN cN aK bK cP fP bO eO par1 par2 (para_symm par3) (para_symm par4) key,
  have := quadarea_comm (ad) bc aL dL bM cM dN
    cN (sameside_of_online_online_para aL dL par1) (sameside_of_online_online_para' bM cM par1)
    (sameside_of_online_online_para aK bK par3),
  have := quadarea_comm ef bc eL fL bM cM fP cP
    (sameside_of_online_online_para' eL fL par2) (sameside_of_online_online_para' bM cM par1)
    (sameside_of_online_online_para' eO bO (para_symm par4)),
  linarith [area_invariant b a d, area_invariant d b a, area_invariant d b c, area_invariant c b e, area_invariant c b a, area_invariant b e f, area_invariant f b e, area_invariant f b c],
end

theorem parallelarea {a b c d e f : point} {L M K N O P : line}
(aL: online a L) (dL: online d L) (bM: online b M) (cM: online c M)
 (eL: online e L) (fL: online f L)
 (aK: online a K) (bK: online b K) (dN: online d N) (cN: online c N)
 (bO: online b O) (eO: online e O) (cP: online c P) (fP: online f P)
(par1 : para L M)
  (par2 : para M L) (par3 : para K N) (par4 : para O P) :
  area b a d + area d b c = area c f e + area e c b :=
begin
    have ab := neq_of_online_offline aL (online_of_online_para' bM par1),
    have ad := neq_of_online_offline aK (online_of_online_para' dN par3),
    have eP := online_of_online_para eO par4,
    have bc := neq_of_online_offline bK (online_of_online_para' cN par3),
    have := parasianar aL dL bM cM aK bK dN cN par1 par3,
    have := parasianar bM cM eL fL bO eO cP fP par2 par4,
  by_cases af : a = f,
  {
   rw ← af at *,
     have := quadarea_comm ad bc aL dL bM cM dN cN (sameside_of_online_online_para aL dL par1)
      (sameside_of_online_online_para bM cM par2) (sameside_of_online_online_para aK bK par3),
    have := quadarea_comm (neq_of_online_offline eO (online_of_online_para' fP par4)) bc eL aL bM
      cM fP cP (sameside_of_online_online_para eL aL par1) (sameside_of_online_online_para' bM cM par1)
      (sameside_of_online_online_para eO bO par4),
    have := area_eq_of_SSS (by linarith : length a d = length e a) (parasianar aK bK dN cN aL dL bM cM par3 par1).1.symm
      (parasianar bO eO cP fP bM cM eL fL par4 par2).1.symm,
    linarith [area_invariant d c b, area_invariant d a b, area_invariant b d a, area_invariant c b e, area_invariant c b a, area_invariant c d a, area_invariant a c d, area_invariant a e b,
      area_invariant a b e],
  },
  by_cases ed : e = d, { rw ed at *, linarith, },
  by_cases df : d = f,
  {
    rw ← df at *, have NP := line_unique_of_pts (neq_of_online_offline dL (online_of_online_para' cM par1)) dN cN fP cP, rw ← NP at *,
    by_cases ae : a ≠ e,
    { exfalso,
      cases B_of_three_online_ne ae ad ed aL eL dL ,
      linarith [length_sum_of_B h, len_pos_of_nq ae],
      cases h,
      linarith [length_sum_of_B h, len_pos_of_nq ae.symm],
      have abN := sameside_of_online_online_para aK bK par3,
      refine (difsamedif abN ⟨not_online_of_sameside abN, eP, not_sameside13_of_B123_online2 h dN⟩).2.2
      (sameside_of_online_online_para bO eO par4),
    },
    push_neg at ae,
    rw ae at *,
    have := quadarea_comm ad bc eL fL bM cM fP cP
      (sameside_of_online_online_para aL dL par1)
      (sameside_of_online_online_para bM cM par2) (sameside_of_online_online_para aK bK par3),
    linarith [area_invariant c b e, area_invariant d c b, area_invariant b d e, area_invariant d e b],
  },
  by_cases ae : a = e,
  { exfalso,
    rw ← ae at *,
    have OK := line_unique_of_pts ab eO bO aK bK,
    rw OK at *,
    cases B_of_three_online_ne ad af df aL dL fL ,
    linarith [len_pos_of_nq df, length_sum_of_B h],
    cases h,
    exact (difsamedif (sameside_symm (sameside_of_online_online_para' cP fP par4)) ⟨(online_of_online_para' fP par4),
      (online_of_online_para' dN par3), difsym (not_sameside13_of_B123_online2 h aK)⟩).2.2 (sameside_symm (sameside_of_online_online_para' dN cN par3)),
    linarith [len_pos_of_nq df, length_symm d f, length_sum_of_B h],
  },
  cases B_of_three_online_ne ae ad ed aL eL dL ,
  exact parallelarea1 aL dL bM cM eL fL aK bK dN cN bO eO cP fP par1 par2 par3 par4 h,
  cases h,
  exact parallelarea3 aL dL bM cM eL fL aK bK dN cN bO eO cP fP par1 par2 par3 par4 (B_symm h),
  exact parallelarea2 aL dL bM cM eL fL aK bK dN cN bO eO cP fP par1 par2 par3 par4 h,
end

--Lemma for I.37
theorem parallelodraw {a d b c : point} {L M N : line} (ad : a ≠ d) (bc : b ≠ c) (aN : online a N) (cN : online c N)
  (aL: online a L) (dL: online d L) (bM: online b M) (cM: online c M)
  (par : para L M) (bdN : ¬sameside b d N) :
  ∃ (e : point) (P : line), online e P ∧ online b P ∧ online e L∧  para P N ∧ para L M ∧ B d a e :=
begin
  rcases line_of_pts a b with ⟨O, aO, bO⟩,
  have bN := λ bN, (online_of_online_para aL par) (by rwa (line_unique_of_pts bc bN cN bM cM) at aN),
  rcases same_length_B_of_ne_four ad.symm bc with ⟨e, Bdae, len⟩,
  have dcO := sameside_of_sameside_not_sameside ad aL aN aO dL cN bO bN (sameside_symm (sameside_of_online_online_para' bM cM par)) (difsym bdN),
  have deO := not_sameside13_of_B123_online2 Bdae aO,
  have dO := not_online_of_sameside dcO,
  have ecO := (difsamedif dcO ⟨dO, λ eO, dO (online_3_of_B (B_symm Bdae) eO aO), deO ⟩),
  have := parapostcor (ne_23_of_B Bdae).symm cM bM aL (online_3_of_B Bdae dL aL) aO bO (para_symm par) ecO,
  have eb := (neq_of_online_offline (online_3_of_B Bdae dL aL) (online_of_online_para' bM par)),
  have := sas len (length_symm a b) (by linarith [angle_symm e a b]),
  rcases line_of_pts e b with ⟨P, eP, bP⟩,
  have := angeqpar eb (neq_of_online_offline aN bN).symm (neq_of_online_offline aL (online_of_online_para' cM par))  eP
    bP aN cN bO aO (by linarith [angle_symm e b a]) ⟨ecO.2.1, ecO.1, difsym ecO.2.2⟩ ,
  refine ⟨e, P, eP,bP,(online_3_of_B Bdae dL aL),this, par, Bdae⟩,
end

--Euclid I.37
theorem triarea {a d b c : point} {L M : line}
(aL: online a L) (dL: online d L) (bM: online b M) (cM: online c M)
(par : para L M) :
  area a b c = area d b c :=
begin
  by_cases ad : a = d,
  rw ad,
  by_cases bc : b= c,
  rw bc,
  linarith [area_invariant a c c, area_invariant c a c, area_invariant d c c, area_invariant c d c, degenerate_area c a, degenerate_area c d],
  rcases line_of_pts a c with ⟨N, aN, cN⟩,
  rcases line_of_pts b d with ⟨Q, bQ, dQ⟩,
  rcases line_of_pts d c with ⟨K, dK, cK⟩,
  rcases line_of_pts a b with ⟨O, aO, bO⟩,
  have bN := λ bN, (online_of_online_para aL par) (by rwa (line_unique_of_pts bc bN cN bM cM) at aN),
  by_cases bdN : ¬sameside b d N,
  { rcases parallelodraw ad bc aN cN aL dL bM cM par bdN with ⟨e, P, eP, bP, eL, par1, par2, Bdae⟩,

    rcases parallelodraw (ne.symm ad) (ne.symm bc) dQ bQ dL aL cM bM par
      (difsym (not_sameside_of_sameside_sameside dL dQ dK aL bQ cK (sameside_of_online_online_para' bM cM par)
      (sameside_symm (sameside_of_sameside_not_sameside (λ cb, bc cb.symm) cM cN cK
      bM aN dK (λ dN, (online_of_online_para eP par1)
      (online_3_of_B Bdae dN aN)) (sameside_of_online_online_para aL dL par) bdN )))) with ⟨f, R,fR,cR,fL, par3, par4, Badf⟩,
    have := parallelarea eL aL bM cM dL fL eP bP aN cN bQ dQ cR fR par2 (para_symm par4) par1 (para_symm par3),
    have := parasianar eL aL bM cM eP bP aN cN par2 par1,
    have := parasianar fL dL cM bM fR cR dQ bQ par4 par3,
    linarith [area_invariant a c b, area_invariant d b c],
  },
  push_neg at bdN,
  rcases parallelodraw (ne.symm ad) bc dK cK dL aL bM cM par (not_sameside_of_sameside_sameside cM cK cN bM dK aN
    (sameside_symm (sameside_of_online_online_para aL dL par)) bdN) with ⟨e, P, eP, bP, eL, par1, par2, Bade⟩,
  rcases parallelodraw ad (ne.symm bc) aO bO aL dL cM bM par (difsym (not_sameside_of_sameside_sameside aL aO aN dL bO cN
    (sameside_of_online_online_para' bM cM par) (sameside_symm bdN))) with ⟨f, R,fR,cR,fL, par3, par4, Bdaf⟩,
  have := parallelarea eL dL bM cM aL fL eP bP dK cK bO aO cR fR par (para_symm par) par1 (para_symm par3),
  have := parasianar eL dL bM cM eP bP dK cK par2 par1,
  have := parasianar fL aL cM bM fR cR aO bO par4 par3,
  linarith [area_invariant a c b, area_invariant d b c],
end

--Euclid I.41
theorem paratri {a d b c e : point} {L M N K : line} (eL : online e L)
(aL: online a L) (dL: online d L) (bM: online b M) (cM: online c M)
(aN: online a N) (bN: online b N) (dK: online d K) (cK: online c K)
(par1 : para L M) (par2 : para N K) : area a d c + area a b c = 2 * area b e c :=
by linarith [parasianar dK cK aN bN dL aL cM bM (para_symm par2) par1,
triarea aL eL bM cM par1,  area_invariant a b c, area_invariant c a b, area_invariant e b c, area_invariant e c b]

theorem square_strong_of_square {a b c d : point} (sq: square a b c d) : ∃ L M N O, square_strong a b c d L M N O :=
begin
  unfold square at *,
  unfold square_strong at *,
  rcases line_of_pts a c with ⟨M,aM,cM ⟩ ,
  rcases line_of_pts b d with ⟨O,bO,dO⟩ ,
  rcases line_of_pts a b with ⟨ L,aL,bL⟩,
  rcases line_of_pts c d with ⟨ N,cN,dN⟩ ,
  rcases line_of_pts a d with ⟨X,aX,dX ⟩,
  have := sss (len_symm_of_len sq.2.2.1) (length_symm a d) (by linarith [length_symm a c]),
  have dc : d≠ c,
  {
    intro dc,
    rw dc at *,
    have:=  length_eq_zero_iff.mpr (by refl: c=c),
    rw this at sq,
    rw length_eq_zero_iff at sq,
    exact sq.1 sq.2.2.1,
  },
  have bd: b≠ d,
  {
    intro dc,
    rw dc at *,
    have:=  length_eq_zero_iff.mpr (by refl: d=d),
    rw this at sq,
    rw length_eq_zero_iff at sq,
    exact sq.1 sq.2.2.2.2.1,
  },
  have ac: a≠ c,
  {
    intro dc,
    rw dc at *,
    have:=  length_eq_zero_iff.mpr (by refl: c=c),
    rw this at sq,
    rw length_eq_zero_iff at sq,
    exact sq.1 sq.2.2.2.1,
  },
  have bcX: diffside b c X,
  {
    split,
    {
      intro bX,
      cases B_of_three_online_ne bd.symm sq.2.1.symm sq.1.symm dX bX aX with Bdba Bs,
    },
  },
  have lem:= angeqpar sq.1.symm sq.2.1 dc bL aL dN cN aX dX (angle_symm_of_angle this.1.symm).symm bcX,
  have lem2:= angeqpar bd sq.2.1.symm ac bO dO aM cM dX aX (angle_symm_of_angle this.2.2.symm).symm bcX,
  have := parapostcor2 ac bO dO cM aM cN dN lem2 (sameside_of_online_online_para bL aL lem),
  have := angle_symm b d c,
  have := angle_symm d c a,
  refine ⟨L,M,N,O,aM,cM,bO,dO,aL,bL,cN,dN,sq.2.2.1,sq.2.2.2.1,sq.2.2.2.2.1,by linarith, by linarith,
    by linarith,by linarith,para_symm lem2, lem ⟩,
end

#exit

--Euclid I.46
theorem drawsq {a b g : point} {L : line} (ab : a ≠ b)
  (aL : online a L) (bL : online b L)
  (gL : ¬online g L) : ∃ (d e : point), ∃ (M N O : line),
  square_strong a b d e L M N O ∧  ¬sameside d g L :=
begin
  rcases same_length_B_of_ne ab.symm ab with ⟨b1, Bbab1, len⟩,
  rcases perplinecor bL (online_3_of_B Bbab1 bL aL) gL Bbab1 with ⟨c, per, per2, cgL⟩,
  rcases same_length_B_of_ne (neq_of_online_offline aL (not_online_of_sameside cgL)).symm ab with ⟨d, Bcad, len1⟩,
  rcases same_length_B_of_ne (ne_23_of_B Bcad) (ne_23_of_B Bcad).symm with ⟨d1, Badd1, lend1⟩,
  rcases circle_of_ne (ne_23_of_B Bcad).symm with ⟨α, acirc, dcen⟩,
  rcases line_of_pts c d with ⟨M, cM, dM⟩,
  have gdL := difsamedif cgL ⟨not_online_of_sameside cgL, (λ dL, (not_online_of_sameside cgL) (online_3_of_B (B_symm Bcad) dL aL)), not_sameside13_of_B123_online2 Bcad aL⟩,
  rcases drawpar ab aL bL gdL.2.1 with ⟨e1, N,e1N,dN,-,-, par1⟩,
  have bM : ¬online b M,
  { intro bM, have := line_unique_of_pts ab aL bL (online_2_of_B Bcad cM dM) bM, rw ← this at cM; exact  (not_online_of_sameside cgL) cM, },
  have eex : ∃ (e : point), online e N ∧ sameside b e M ∧ oncircle e α ∧ d ≠ e,
  { rcases pts_of_line_circle_inter (line_circle_inter_of_inside_online dN (inside_circle_of_center dcen)) with ⟨e2, e3, e2e3,e2N, e3N, e2circ, e3circ⟩ ,
    have Be2de3 : B e2 d e3,
    { have same := (oncircle_iff_length_eq e2circ dcen).mpr e3circ,
      cases B_of_three_online_ne (λ e2d, (not_oncircle_of_inside (inside_circle_of_center dcen)) _)
      e2e3 (λ e3d, (not_oncircle_of_inside (inside_circle_of_center dcen)) (by rwa ← e3d at e3circ)) e2N dN e3N,
      exact h,
      cases h,
      have := length_sum_of_B h,
      linarith [len_pos_of_nq e2e3],
      have := length_sum_of_B h,
      linarith [len_pos_of_nq e2e3, len_symm2_of_len same],
      rwa e2d at e2circ,
      },
    by_cases beM : sameside b e2 M,
    { refine ⟨e2, e2N, beM, e2circ, by btw⟩, },
    have e2M : ¬online e2 M,
    { intro e2M,
      have := line_unique_of_pts (ne_12_of_B Be2de3) e2M dM e2N dN,
      rw this at *,
      exact (online_of_online_para' aL par1) (online_2_of_B Bcad cM dM), },
    have e3M := λ e3M, e2M (online_3_of_B (B_symm Be2de3) e3M dM),
    refine ⟨e3, e3N, sameside_of_diffside_diffside ⟨e2M, bM, difsym beM⟩ ⟨e2M, e3M, not_sameside13_of_B123_online2 Be2de3 dM⟩, e3circ,
      (ne_23_of_B Be2de3)⟩, },
  rcases eex with ⟨e, eN, beM, ecirc, de⟩,
  rcases line_of_pts e b with ⟨O, eO, bO⟩,
  rcases line_of_pts e a with ⟨P, eP, aP⟩,
  rcases same_length_B_of_ne de.symm de with ⟨e4, Bede4, lene4⟩,
  have bdP := not_sameside_of_sameside_sameside aL aP (online_2_of_B Bcad cM dM) bL eP dM (sameside_symm (sameside_of_online_online_para dN eN par1)) beM,
  have bP : ¬online b P,
  {
    intro bP,rw (line_unique_of_pts ab aL bL aP bP) at *,
    exact (online_of_online_para' eP par1) eN,
  },
  have dP : ¬online d P,
  { intro dP,
    have := line_unique_of_pts de dN eN dP eP,
    rw this at *,
    exact (online_of_online_para aL (para_symm par1)) aP,
  },
  have := (oncircle_iff_length_eq acirc dcen).mpr ecirc,
  have := parapostcor de  bL aL eN dN  eP aP (para_symm par1) ⟨bP, dP, bdP⟩,
  have := sas (length_symm a e) (len_symm2_of_len (by linarith [length_symm d a] : length d e = length b a)).symm
    (by linarith [angle_symm b a e]),
  have par2 := angeqpar (neq_of_online_offline eP bP).symm (neq_of_online_offline eN (online_of_online_para' aL par1)) (neq_of_online_offline aP dP)
     bO eO (online_2_of_B Bcad cM dM) dM eP aP (by linarith [angle_symm a e b]) ⟨bP, dP, bdP⟩,
  have := parapost (neq_of_online_offline eP bP).symm (online_3_of_B Badd1 (online_2_of_B Bcad cM dM) dM) dM bO eN eO  dN (para_symm par2) (B_symm Badd1) (B_symm Bede4)
    (sameside_of_online_online_para' aL bL par1),
  have := flatsumright cM dM bM Bcad,
  have := angle_symm b a d,
  have := angle_symm d e b,
  have := angle_symm a d e,
  have := parasianar aL bL dN eN (online_2_of_B Bcad cM dM) dM bO eO (para_symm par1) (para_symm par2)  ,
  refine ⟨d, e, M, N, O,⟨ online_2_of_B Bcad cM dM,dM,bO,eO,aL,bL,dN,eN, this.1,by linarith[length_symm a b],
  by linarith [length_symm e b, length_symm a b],by linarith,by linarith,by linarith,by linarith, para_symm par2, para_symm par1⟩, difsym gdL.2.2⟩,
end

--Euclid I.47
theorem pythagorasdraw {a b c : point} {N : line} (ab : a ≠ b) (aN : online a N) (bN : online b N)
  (cN : ¬online c N) : ∃ (f g h k d e : point) (L M O P Q R S T U V W : line),
  square_strong b a f g N W V U ∧ square_strong c a k h M R S T ∧ square_strong b c d e L Q P O ∧ ¬sameside f c N ∧
  ¬sameside k b M ∧ ¬sameside d a L :=
begin
  rcases line_of_pts a c with ⟨M, aM, cM⟩,
  rcases line_of_pts b c with ⟨L, bL, cL⟩,
  rcases drawsq ab.symm bN aN cN with ⟨f, g, W, V, U, sq1, fcN⟩,
  rcases drawsq (neq_of_online_offline aN cN).symm cM aM (λ bM, (lines_neq_of_online_offline cM cN) (line_unique_of_pts ab aM bM aN bN)) with
    ⟨k, h, R, S,T, sq2, hbM⟩,
  rcases drawsq (neq_of_online_offline bN cN) bL cL (λ aL, (lines_neq_of_online_offline cL cN) (line_unique_of_pts ab aL bL aN bN)) with
    ⟨d, e, Q, P, O, sq3, daL⟩,
  refine ⟨f, g, h, k, d, e, L, M, O, P, Q, R, S,T, U, V, W, sq1, sq2, sq3, fcN, hbM, daL⟩,
end

theorem pythlem0 {a b c d : point} {L : line} (bc : b ≠ c) (bd : b ≠ d) (bL : online b L)
  (cL : online c L) (dL : online d L) (aL : ¬online a L) (ang : angle a b c = rightangle) :
  angle a b d = rightangle :=
begin
  by_cases cd : c = d,
  rwa ← cd,
  cases B_of_three_online_ne bc bd cd bL cL dL ,
  have := angle_extension_of_B (neq_of_online_offline bL aL) h,
  have := angle_symm a b c,
  have := angle_symm a b d,
  linarith,
  cases h,
  have := flatsumright cL dL aL h,
  linarith,
  have := angle_extension_of_B (neq_of_online_offline bL aL) h,
  have := angle_symm a b c,
  have := angle_symm a b d,
  linarith,
end

--Euclid I.47/Generalization of I.13
theorem pythlem {a b c : point} {L : line} (bc : b ≠ c) (bL : online b L) (cL : online c L)
  (aL : ¬online a L) (ang : rightangle ≤ angle c a b) :
  ∃ (m : point), angle a m b = rightangle ∧ angle a m c = rightangle ∧ B b m c :=
begin
  rcases perppointnon aL with ⟨h, m, g, hL, mL, gL, Bhmg, ang1⟩,
  have mb : m ≠ b,
  { intro mb,
    rcases line_of_pts b a with ⟨M, bM, aM⟩,
    have cM : ¬online c M,
    { intro cM,
      exact (lines_neq_of_online_offline aM aL) (line_unique_of_pts bc bL cL bM cM).symm, },
    rw mb at *,
    rcases same_length_B_of_ne (neq_of_online_offline bL aL) (neq_of_online_offline bL aL).symm with ⟨a1, Bbaa1, junk⟩,
    have := flatsumright bM (online_3_of_B Bbaa1 bM aM) cM Bbaa1,
    have := extangcor cM bM (online_3_of_B Bbaa1 bM aM) Bbaa1,
    have := angle_symm c b a,
    by_cases gcM : sameside g c M,
    { by_cases gc : g = c,
      rw gc at *,
      linarith,
      have := angle_extension_of_ss (neq_of_online_offline bL aL) gc bM aM bL gL cL gcM,
      have := angle_symm a b g,
      linarith, },
    have hM : ¬online h M,
    { intro hM,
      exact (lines_neq_of_online_offline aM aL) (line_unique_of_pts ((ne_12_of_B Bhmg).symm) bL hL bM hM).symm, },
    have gM : ¬online g M,
    { intro gM,
      exact (lines_neq_of_online_offline aM aL) (line_unique_of_pts (ne_23_of_B Bhmg) bL gL bM gM).symm, },
    have hcM := sameside_symm (sameside_of_diffside_diffside ⟨gM, cM, gcM⟩ ⟨gM, hM, difsym (not_sameside13_of_B123_online2 Bhmg bM)⟩),
    by_cases hc : h = c,
    rw hc at *,
    linarith,
    have := angle_extension_of_ss (neq_of_online_offline bL aL) hc bM aM bL hL cL hcM,
    have := angle_symm a b h,
    linarith, },
  have mc : m ≠ c,
  { intro mc,
    rcases line_of_pts c a with ⟨M, cM, aM⟩,
    have bM : ¬online b M,
    { intro bM,
      exact (lines_neq_of_online_offline aM aL) (line_unique_of_pts bc bL cL bM cM).symm, },
    rw mc at *,
    rcases same_length_B_of_ne (neq_of_online_offline cL aL) (neq_of_online_offline cL aL).symm with ⟨a1, Bcaa1, junk⟩,
    have := flatsumright cM (online_3_of_B Bcaa1 cM aM) bM Bcaa1,
    have := extangcor bM cM (online_3_of_B Bcaa1 cM aM) Bcaa1,
    have := angle_symm b c a,
    have := angle_symm c a b,
    by_cases gbM : sameside g b M,
    { by_cases gb : g = b,
      rw gb at *,
      linarith,
      have := angle_extension_of_ss (neq_of_online_offline cL aL) gb cM aM cL gL bL gbM,
      have := angle_symm a c g,
      linarith, },
    have hM : ¬online h M,
    { intro hM,
      exact (lines_neq_of_online_offline aM aL) (line_unique_of_pts ((ne_12_of_B Bhmg).symm) cL hL cM hM).symm, },
    have gM : ¬online g M,
    { intro gM,
      exact (lines_neq_of_online_offline aM aL) (line_unique_of_pts (ne_23_of_B Bhmg) cL gL cM gM).symm, },
    have hbM := sameside_symm (sameside_of_diffside_diffside ⟨gM, bM, gbM⟩ ⟨gM, hM, difsym (not_sameside13_of_B123_online2 Bhmg cM)⟩),
    by_cases hb : h = b,
    rw hb at *,
    linarith,
    have := angle_extension_of_ss (neq_of_online_offline cL aL) hb cM aM cL hL bL hbM,
    have := angle_symm a c h,
    linarith, },
  have ang2 := pythlem0 (ne_23_of_B Bhmg) mb mL gL bL aL ang1.2,
  have ang3 := pythlem0 (ne_23_of_B Bhmg) mc mL gL cL aL ang1.2,
  cases B_of_three_online_ne mb mc bc mL bL cL  with Bmbc hs,
  exfalso,
  rcases same_length_B_of_ne (ne.symm mb) (mb) with ⟨m1, Bbmm1, junk⟩,
  have := flatsumright bL (online_3_of_B Bbmm1 bL mL) aL Bbmm1,
  have := extangcor aL bL (online_3_of_B Bbmm1 bL mL) Bbmm1,
  have := flatsumright mL cL aL Bmbc,
  rcases line_of_pts b a with ⟨M, bM, aM⟩,
  have cM := λ cM, (lines_neq_of_online_offline aM aL) (line_unique_of_pts bc bL cL bM cM).symm,
  rcases same_length_B_of_ne (neq_of_online_offline bL aL) (neq_of_online_offline bL aL).symm with ⟨a1, Bbaa1, junk⟩,
  have := flatsumright bM (online_3_of_B Bbaa1 bM aM) cM Bbaa1,
  have := extangcor cM bM (online_3_of_B Bbaa1 bM aM) Bbaa1,
  have := angle_symm c b a,
  linarith,
  cases hs.swap with Bmcb Bbmc,
  rcases same_length_B_of_ne (ne.symm mc) (mc) with ⟨m1, Bcmm1, junk⟩,
  have := flatsumright cL (online_3_of_B Bcmm1 cL mL) aL Bcmm1,
  have := extangcor aL cL (online_3_of_B Bcmm1 cL mL) Bcmm1,
  have := flatsumright mL bL aL Bmcb,
  rcases line_of_pts c a with ⟨M, cM, aM⟩,
  have bM := λ bM, (lines_neq_of_online_offline aM aL) (line_unique_of_pts bc.symm cL bL cM bM).symm,
  rcases same_length_B_of_ne (neq_of_online_offline cL aL) (neq_of_online_offline cL aL).symm with ⟨a1, Bcaa1, junk⟩,
  have := flatsumright cM (online_3_of_B Bcaa1 cM aM) bM Bcaa1,
  have := extangcor bM cM (online_3_of_B Bcaa1 cM aM) Bcaa1,
  have := angle_symm b c a,
  have := angle_symm b a c,
  linarith,
  refine ⟨m, ang2, ang3, Bbmc⟩,
end


--Euclid I.47
theorem pythagoras {a b c f g h k d e : point} {L M N O P Q R S T U V W : line} (bc : b ≠ c)
  (aL : ¬online a L) (ang : angle c a b = rightangle) (sq1 : square_strong b a f g N W V U)
  (sq2 : square_strong c a k h M R S T) (sq3 : square_strong b c d e L Q P O) (fcN : ¬sameside f c N)
  (kbM : ¬sameside k b M) (daL : ¬sameside d a L) :
  area d b e+ area e c b = area a b f + area a g f + area a h k + area a c k :=
begin
  unfold square_strong at sq3,
  unfold square_strong at sq2,
  unfold square_strong at sq1,
  have bL := online_1_1_of_square sq3,
  have cL := online_2_1_of_square sq3,
  have dP := online_3_3_of_square sq3,
  have eP := online_4_3_of_square sq3,
  have eO := online_4_4_of_square sq3,
  have sq3par1:= (para_1_3_of_square sq3),
  have sq2par1:= (para_1_3_of_square sq2),
  have sq1par1:= (para_1_3_of_square sq1),
  have sq3par2:= para_2_4_of_square sq3,
  have sq1par2:= para_2_4_of_square sq1,
  have sq2par2:= para_2_4_of_square sq2,
  have bP := (online_of_online_para bL sq3par1),
  have bN := online_1_1_of_square sq1,
  have aN := online_2_1_of_square sq1,
  have cM := online_1_1_of_square sq2,
  have aM := online_2_1_of_square sq2,
  have aU := online_2_4_of_square sq1,
  have gU := online_4_4_of_square sq1,
  have aT := online_2_4_of_square sq2,
  have hT := online_4_4_of_square sq2,
  have bW := online_1_2_of_square sq1,
  have fW := online_3_2_of_square sq1,
  have cR := online_1_2_of_square sq2,
  have kR := online_3_2_of_square sq2,
  have kS := online_3_3_of_square sq2,
  have fV := online_3_3_of_square sq1,
  have gV := online_4_3_of_square sq1,
  have hS := online_4_3_of_square sq2,
  have kM := (online_of_online_para kS (para_symm sq2par1)),
  have fN := (online_of_online_para fV (para_symm sq1par1)),
  have cP := (online_of_online_para cL  sq3par1),
  have ec := (neq_of_online_offline eP cP),
  have db := (neq_of_online_offline dP bP),
  have dL := (online_of_online_para dP  (para_symm sq3par1)),
  have eL := (online_of_online_para eP  (para_symm sq3par1)),
  have cd := neq_of_online_offline cL dL,
  have ca := (neq_of_online_offline cL aL),
  have ba := (neq_of_online_offline bL aL),
  have eQ := (online_of_online_para eO  (para_symm sq3par2)),
  have dQ := online_3_2_of_square sq3,
  have bQ := online_1_2_of_square sq3,
  have dO := (online_of_online_para dQ  sq3par2),
  have cO := online_2_4_of_square sq3,
  have de := neq_of_online_offline dQ eQ,
  have bf := neq_of_online_offline bN fN,
  have ck := neq_of_online_offline cM kM,
  rcases pythlem bc bL cL aL (by linarith) with ⟨m, ang1, ang2, Bbmc⟩,
  have mL := (online_2_of_B Bbmc bL cL),
  have ma := (neq_of_online_offline mL aL),
  have md := neq_of_online_offline mL dL,
  have me := neq_of_online_offline mL eL,
  rcases line_of_pts m a with ⟨X, mX, aX⟩,
  have mP := online_of_online_para mL sq3par1,
  have mQ : ¬online m Q,
  { intro mQ, have := line_unique_of_pts (ne_12_of_B Bbmc) bL mL bQ mQ, rw this at *, exact dL dQ, },
  have mO : ¬online m O,
  { intro mO, have := line_unique_of_pts (ne_12_of_B (B_symm Bbmc)) cL mL cO mO, rw this at *, exact eL eO, },
  have mcQ := sameside23_of_B123_online1_not_online2 Bbmc bQ mQ,
  have ceQ := sameside_of_online_online_para' cO eO  sq3par2,
  have meQ := sameside_symm (sameside_trans ceQ (sameside_symm mcQ)),
  have mbP := sameside_of_online_online_para mL bL sq3par1,
  have mbO := sameside23_of_B123_online1_not_online2 (B_symm Bbmc) cO mO,
  have bdO := sameside_of_online_online_para bQ dQ sq3par2,
  have mdO := sameside_symm (sameside_trans bdO (sameside_symm mbO)),
  have mcP := sameside_of_online_online_para mL cL sq3par1,
  rcases perppointnon mP with ⟨p1, l, p2, p1P, lP, p2P, Bp1lp2, angs⟩,
  have lm := neq_of_online_offline lP mP,
  rcases line_of_pts l m with ⟨X', lX', mX'⟩,
  have := angle_symm c b d,
  have dl : d ≠ l,
  { intro dl,
    rw ← dl at *,
    rcases same_length_B_of_ne (ne_12_of_B Bbmc).symm (ne_12_of_B Bbmc) with ⟨b1, Bmbb1, junk⟩,
    have := flatsumright mL (online_3_of_B Bmbb1 mL bL) dL Bmbb1,
    have := extangcor dL mL (online_3_of_B Bmbb1 mL bL) Bmbb1,
    have beX' := not_sameside_of_sameside_sameside dQ lX' dP bQ mX' eP meQ (sameside_symm mbP),
    have bX' : ¬online b X',
    { intro bX', have := line_unique_of_pts (ne_12_of_B Bmbb1) mL bL mX' bX', rw this at *, exact dL lX', },
    have eX' : ¬online e X',
    { intro eX', have := line_unique_of_pts (neq_of_online_offline dQ eQ) dP eP lX' eX', rw this at *, exact mP mX', },
    have := parapostcor (ne_12_of_B Bmbb1).symm eP dP mL bL mX' lX' (para_symm sq3par1)  ⟨eX', bX', difsym beX'⟩,
    have := pythlem0 (ne_12_of_B Bp1lp2).symm (neq_of_online_offline dQ eQ) dP p1P eP mP (by linarith),
    have := angle_extension_of_B db.symm Bbmc,
    have := angle_symm e d m,
    have := angle_symm m b d,
    have := angle_symm c b d,
    linarith, },
  have el : e ≠ l,
  { intro el,
    rw ← el at *,
    rcases same_length_B_of_ne (ne_12_of_B (B_symm Bbmc)).symm (ne_12_of_B (B_symm Bbmc)) with ⟨b1, Bmcc1, junk⟩,
    have := flatsumright mL (online_3_of_B Bmcc1 mL cL) eL Bmcc1,
    have := extangcor eL mL (online_3_of_B Bmcc1 mL cL) Bmcc1,
    have cdX' := not_sameside_of_sameside_sameside eO lX' eP cO mX' dP mdO (sameside_symm mcP),
    have cX' : ¬online c X',
    { intro cX', have := line_unique_of_pts (ne_12_of_B Bmcc1) mL cL mX' cX', rw this at *, exact eL lX', },
    have dX' : ¬online d X',
    { intro dX', have := line_unique_of_pts (neq_of_online_offline eO dO) eP dP lX' dX', rw this at *, exact mP mX', },
    have := parapostcor (ne_12_of_B Bmcc1).symm dP eP mL cL mX' lX' (para_symm sq3par1) ⟨dX', cX', difsym cdX'⟩,
    have := pythlem0 (ne_12_of_B Bp1lp2).symm (neq_of_online_offline eO dO) eP p1P dP mP (by linarith),
    have := angle_extension_of_B ec.symm (B_symm Bbmc),
    have := angle_symm d e m,
    have := angle_symm m c e,
    linarith, },
  have eX' : ¬online e X',
  { intro eX', have := line_unique_of_pts el eP lP eX' lX', rw this at *, exact mP mX', },
  have dX' : ¬online d X',
  { intro dX', have := line_unique_of_pts dl dP lP dX' lX', rw this at *, exact mP mX', },
  have := angle_symm d e c,
  have := angle_symm m l d,
  have := angle_symm m l e,
  have ang4 := pythlem0 (ne_12_of_B Bp1lp2).symm el.symm lP p1P eP mP angs.1,
  have ang3 := pythlem0 (ne_12_of_B Bp1lp2).symm dl.symm lP p1P dP mP angs.1,
  have ang5 := pythlem0 de dl dP eP lP bP (by linarith),
  have ang6 := pythlem0 de.symm el eP dP lP cP (by linarith),--sq3.2.2.2.2.2.2.1
  rcases same_length_B_of_ne lm.symm lm with ⟨l', Bmll', junk⟩,
  have := flatsumright mX' (online_3_of_B Bmll' mX' lX') dX' Bmll',
  have := flatsumright mX' (online_3_of_B Bmll' mX' lX') eX' Bmll',
  have ml'P := not_sameside13_of_B123_online2 Bmll' lP,
  have bl'P := difsamedif mbP ⟨mP, (λ l'P, mP (online_3_of_B (B_symm Bmll') l'P lP)), ml'P⟩,
  have cl'P := difsamedif mcP ⟨mP, (λ l'P, mP (online_3_of_B (B_symm Bmll') l'P lP)), ml'P⟩,
  have par2 := (angeqpar db.symm dl (ne_23_of_B Bmll')
    bQ dQ lX' (online_3_of_B Bmll' mX' lX') dP lP (by linarith) bl'P),
  have par3 :=  (angeqpar ec.symm el (ne_23_of_B Bmll')
    cO eO lX' (online_3_of_B Bmll' mX' lX') eP lP (by linarith) cl'P),
  have := parasianar bL mL dP lP bQ dQ mX' lX' sq3par1 par2,
  have := parasianar cL mL eP lP cO eO mX' lX' sq3par1 par3,
  have := length_sum_of_B Bbmc,
  have := parasianar  dP lP bL mL dQ bQ lX' mX' (para_symm sq3par1) par2,
  have := angle_symm b m a,
  have := angle_symm b m l,
  have Blma := rightimpflat (ne_12_of_B Bbmc) bL mL (difsamedif (sameside_of_online_online_para' dP lP sq3par1)
    ⟨dL, aL, daL⟩) (by linarith),
  have Bdle := B_of_length_leq dl el.symm de dP lP eP (by linarith [length_symm m c, length_symm e l]),
  have := (line_unique_of_pts ma mX aX mX' (online_3_of_B Blma lX' mX')),
  rw ← this at *,
  have cN : ¬online c N,
  { intro cN, have := line_unique_of_pts bc bL cL bN cN, rw this at *, exact aL aN, },
  have fgN := sameside_of_online_online_para' fV gV sq1par1,
  have UM : U = M,
  { have := rightimpflat ba bN aN (difsamedif fgN ⟨not_online_of_sameside fgN, cN, fcN⟩) (by linarith [angle_symm b a c]),
    exact line_unique_of_pts (ne_23_of_B this) aU (online_3_of_B this gU aU) aM cM, },
  have khM := sameside_of_online_online_para' kS hS sq2par1,
    have bM : ¬online b M, { intro bM, have := line_unique_of_pts bc bL cL bM cM, rw this at *, exact aL aM, },
  have TN : T = N,
  { have := rightimpflat ca cM aM (difsamedif khM ⟨not_online_of_sameside khM, bM, kbM⟩) (by linarith [angle_symm c a b]),
    exact line_unique_of_pts (ne_23_of_B this) aT (online_3_of_B this hT aT) aN bN, },
  rw TN at *,
  rw UM at *,
  have ang1 : angle a b d = angle f b c,
  { have caW := sameside_of_online_online_para' cM aM sq1par2,
    have faL := sameside_of_sameside_not_sameside bf bW bN bL fW aN cL cN (sameside_symm caW) fcN, --(sameside_symm caW) ⟨cN, not_online_of_sameside fgN, sameside_symm cN⟩,
    have := angles_add_of_sameside bf bc bW fW bL cL faL caW,
    have bdX := sameside_of_online_online_para bQ dQ par2,
    have amQ := sameside_of_online_online_para' aX mX par2,
    have dmN := sameside_of_sameside_not_sameside db.symm bQ bL bN dQ mL aN aL (sameside_symm amQ) daL,
    rcases quadiag db ma dQ bQ mX aX bN aN (sameside_symm bdX)
      (sameside_symm amQ) dmN with
      ⟨y,Y1,Y2, dY1, aY1, bY2, mY2,yY1,yY2, Bbym, Bayd, mY1, bY1, aY2, dY2⟩,
    have yQ : ¬online y Q,
    { intro yQ, have := line_unique_of_pts (ne_23_of_B Bayd) yY1 dY1 yQ dQ, rw this at *, exact bY1 bQ, },
    have yN : ¬online y N,
    { intro yN, have := line_unique_of_pts (ne_12_of_B Bayd) aY1 yY1 aN yN, rw this at *, exact bY1 bN, },
    have := angles_add_of_sameside ba db.symm bN aN bQ dQ
      (sameside_symm (sameside23_of_B123_online1_not_online2 (B_symm Bayd) dQ yQ))
      (sameside_symm (sameside23_of_B123_online1_not_online2 Bayd aN yN)),
    have := angle_extension_of_B ba (B124_of_B134_B123 Bbmc Bbym),
    have := angle_extension_of_B db.symm (B124_of_B134_B123 Bbmc Bbym),
    have := angle_symm a b y,
    have := angle_symm a b c,
    linarith, },
  have ang2 : angle a c e = angle k c b,
  {
    have baR := sameside_of_online_online_para' bN aN sq2par2,
    have kaL := sameside_of_sameside_not_sameside ck cR cM cL kR aM bL bM (sameside_symm baR) kbM , --(sameside_symm caW) ⟨cN, not_online_of_sameside fgN, sameside_symm cN⟩,
    have := angles_add_of_sameside ck bc.symm cR kR cL bL kaL baR,
    have eaL := difsamedif (sameside_symm (sameside_of_online_online_para' eP dP sq3par1)) ⟨dL, aL, daL⟩,
    have emM := sameside_of_sameside_not_sameside ec.symm cO cL cM eO mL aM aL (sameside_symm (sameside_of_online_online_para' aX mX par3)) eaL.2.2,
    rcases quadiag ec ma eO cO mX aX cM aM (sameside_symm (sameside_of_online_online_para cO eO par3))
      (sameside_symm (sameside_of_online_online_para' aX mX par3)) emM with
      ⟨y,Y1,Y2, eY1, aY1, cY2, mY2,yY1,yY2, Bcym, Baye, mY1, cY1, aY2, eY2⟩,
    have yO : ¬online y O,
    { intro yO, have := line_unique_of_pts (ne_23_of_B Baye) yY1 eY1 yO eO, rw this at *, exact cY1 cO, },
    have yM : ¬online y M,
    { intro yM, have := line_unique_of_pts (ne_12_of_B Baye) aY1 yY1 aM yM, rw this at *, exact cY1 cM, },
    have := angles_add_of_sameside ca ec.symm cM aM cO eO (sameside_symm (sameside23_of_B123_online1_not_online2 (B_symm Baye) eO yO)) (sameside_symm (sameside23_of_B123_online1_not_online2 Baye aM yM)),
    have := angle_extension_of_B ca (B124_of_B134_B123 (B_symm Bbmc) Bcym),
    have := angle_extension_of_B ec.symm (B124_of_B134_B123 (B_symm Bbmc) Bcym),
    have := angle_symm a c y,
    have := angle_symm a c b,
    linarith, },
  have := sas sq1.2.2.2.2.2.2.2.2.2.1 sq3.2.2.2.2.2.2.2.2.2.1.symm ang1,
  have := area_eq_of_SSS sq1.2.2.2.2.2.2.2.2.2.1 this.1 (len_symm2_of_len sq3.2.2.2.2.2.2.2.2.2.1.symm),
  have := sas sq2.2.2.2.2.2.2.2.2.2.1 (len_symm_of_len sq3.2.2.2.2.2.2.2.2.2.2.1).symm ang2,
  have := area_eq_of_SSS sq2.2.2.2.2.2.2.2.2.2.1 this.1 (len_symm_of_len sq3.2.2.2.2.2.2.2.2.2.2.1.symm),
  have := paratri cM aU gU bW fW aN bN gV fV (para_symm sq1par2) sq1par1,
  have := paratri bN aN hT cR kR aM cM hS kS (para_symm sq2par2) sq2par1,
  have := paratri aX mX lX' bQ dQ mL bL lP dP (para_symm par2) sq3par1,
  have := paratri aX mX lX' cO eO mL cL lP eP (para_symm par3) sq3par1,
  have := quad_add_of_quad_quad bL cL dP eP cO eO Bbmc Bdle (sameside_of_online_online_para bL cL sq3par1)
    (sameside_of_online_online_para' dP eP sq3par1) bdO,
  have := quadarea_comm (ne_12_of_B Bbmc) (ne_12_of_B Bdle) bL mL dP lP mX lX' (sameside_symm mbP)
    (sameside_of_online_online_para' dP lP sq3par1) (sameside_of_online_online_para bQ dQ par2),
  have := quadarea_comm (ne_12_of_B (B_symm Bbmc)) (ne_12_of_B (B_symm Bdle)) cL mL eP lP mX lX' (sameside_symm mcP)
    (sameside_of_online_online_para' eP lP sq3par1) (sameside_of_online_online_para cO eO par3),
  linarith [area_invariant b c f, area_invariant c b k, area_invariant l d b, area_invariant l b d, area_invariant l m b, area_invariant b l m],
end


--- AK playing around with Steiner-Lehmus Theorem

def colinear (a b c : point) : Prop := ∃ (L : line), online a L ∧ online b L ∧ online c L

-- API
lemma colinear_iff {a b c : point} :
  colinear a b c ↔ (∃ L, online a L ∧ online b L ∧ online c L) := by refl

lemma colinear_of_B {a b c : point} (Babc : B a b c) : colinear a b c :=
begin
  obtain ⟨L, aL, bL, cL, -⟩ := line_of_B Babc,
  exact ⟨L, aL, bL, cL⟩,
end

lemma colinear.symm_23 {a b c : point} (h : colinear a b c) : colinear a c b :=
begin
  obtain ⟨L, aL, bL, cL⟩ := h,
  exact ⟨L, aL, cL, bL⟩,
end

lemma colinear.perm {a b c : point} (h : colinear a b c) : colinear b c a :=
begin
  obtain ⟨L, aL, bL, cL⟩ := h,
  exact ⟨L, bL, cL, aL⟩,
end

lemma diffside_of_B_diffside {a b c : point} {L : line} (Babc : B a b c) (h : diffside a b L) :
  diffside a c L :=
begin
  obtain ⟨N, aN, bN, cN, a_ne_b, b_ne_c, c_ne_a⟩ := line_of_B Babc,
  have := lines_inter_of_not_sameside aN bN h.2.2,
  obtain ⟨d, dL, dN⟩ := pt_of_lines_inter this,

  sorry,
end

-- change axiom angle_symm ! There is symmetry whether they're equal or not...

lemma colinear_of_eq_12 (a b : point) : colinear a a b :=
begin
  obtain ⟨L, aL, bL⟩ := line_of_pts a b,
  exact ⟨L, aL, aL, bL⟩,
end

lemma colinear_of_eq_23 (a b : point) : colinear a b b :=
begin
  obtain ⟨L, aL, bL⟩ := line_of_pts a b,
  exact ⟨L, aL, bL, bL⟩,
end

lemma colinear_of_eq_13 (a b : point) : colinear a b a :=
begin
  obtain ⟨L, aL, bL⟩ := line_of_pts a b,
  exact ⟨L, aL, bL, aL⟩,
end

lemma ne_12_of_not_colinear {a b c : point} (h : ¬ colinear a b c) : a ≠ b :=
begin
  intros hab,
  rw hab at h,
  exact h (colinear_of_eq_12 b c),
end

lemma ne_23_of_not_colinear {a b c : point} (h : ¬ colinear a b c) : b ≠ c :=
begin
  intros hbc,
  rw hbc at h,
  exact h (colinear_of_eq_23 a c),
end

lemma ne_13_of_not_colinear {a b c : point} (h : ¬ colinear a b c) : a ≠ c :=
begin
  intros hac,
  rw hac at h,
  exact h (colinear_of_eq_13 c b),
end

lemma offline_of_not_colinear {a b c : point} {L : line} (habc : ¬ colinear a b c)
  (bL : online b L) (cL : online c L) : ¬ online a L :=
begin
  intros aL,
  have : colinear a b c,
  { rw colinear_iff,
    refine ⟨L, aL, bL, cL⟩, },
  exact habc this,
end

-- Proofs

theorem isosceles_of_equal_angles {a b c : point} (habc : ¬ colinear a b c)
  (h : angle a b c = angle a c b) : length a b = length a c :=
begin
  refine isoside _ (ne_12_of_not_colinear habc) (ne_23_of_not_colinear habc)
    (ne_13_of_not_colinear habc).symm h,
  intros Bbac,
  obtain ⟨L, bL, aL, cL, -⟩ := line_of_B Bbac,
  exact habc ⟨L, aL, bL, cL⟩,
end

lemma B_of_greater_angle {a b c d : point} {L : line} (habc : ¬ colinear a b c)
  (hbcd: colinear b c d) (aL : online a L) (bL : online b L) (cdL : sameside c d L)
  (h : angle b a c < angle b a d) : B b c d :=
begin
  have a_ne_c := ne_13_of_not_colinear habc,
  have a_ne_b := ne_12_of_not_colinear habc,
  have b_ne_c := ne_23_of_not_colinear habc,
  by_cases c_ne_d : c = d,
  { rw c_ne_d at *; linarith, },
  have dL := not_online_of_sameside (sameside_symm cdL),
  by_cases b_ne_d : b = d,
  { rw b_ne_d at *,
    exact false.rec _ (dL bL), },
  obtain ⟨M, bM, cM, dM⟩ := hbcd,
  cases B_of_three_online_ne b_ne_c b_ne_d c_ne_d bM cM dM  with Bbcd h₁,
  { exact Bbcd, },
  cases h₁ with Bcbd Bbdc,
  { exact false.rec _ (not_sameside13_of_B123_online2 Bcbd bL cdL), },
  have aM : ¬ online a M := λ hh, habc ⟨M, hh, bM, cM⟩,
  obtain ⟨N, aN, cN⟩ := line_of_pts  a c,
  have dN : ¬ online d N :=
    λ hh, habc ⟨N, aN, (by rwa ← (line_unique_of_pts c_ne_d cN hh cM dM) at bM), cN⟩,
  have LN : L ≠ N := λ hh, habc ⟨L, aL, bL, by rwa ← hh at cN⟩,
  have bdN : sameside b d N :=
    sameside_symm (sameside23_of_B123_online1_not_online2 (B_symm Bbdc) cN dN),
  have cdL : sameside c d L := sameside_symm (sameside23_of_B123_online1_not_online2 Bbdc bL dL),
  have : 0 ≤ angle d a c := angle_nonneg _ _ _,
  have := (angle_add_iff_sameside a_ne_b a_ne_c aL bL aN cN dN dL LN).mpr ⟨bdN, cdL⟩,
  linarith,
end

-- If a base angle is smaller, then its bisector is longer. Proof in Coxeter (by H.G. Forder)
lemma steiner_lehmus_prep {a b c y z : point} (habc : ¬ colinear a b c) (Bazb : B a z b)
  (Bayc : B a y c) (hb : angle a b y = angle y b c) (hc : angle a c z = angle z c b)
  (b_le_c : angle a b c < angle a c b) :
  length c z < length b y :=
begin
  have aby_lt_zca : angle a b y < angle z c a := sorry,
  have a_ne_b := ne_12_of_not_colinear habc,
  have a_ne_c := ne_13_of_not_colinear habc,
  have b_ne_c := ne_23_of_not_colinear habc,
  have b_ne_y : b ≠ y,
  { intros hby,
    rw ←hby at Bayc,
    exact habc (colinear_of_B Bayc), },
  have c_ne_z : c ≠ z,
  { intros hcz,
    rw ←hcz at Bazb,
    exact habc (colinear_of_B Bazb).symm_23, },
  obtain ⟨L, aL, bL⟩ := line_of_pts a b,
  have yL : ¬ online y L := sorry,
  obtain ⟨M, cM, zM⟩ := line_of_pts c z,
  have diffside_abM : diffside a b M := sorry,
  obtain ⟨N, bN, yN⟩ := line_of_pts b y,
  have L_ne_N : L ≠ N := sorry,
  have aM : ¬ online a M := sorry,
  have zL : online z L := sorry,
  have : ∃ u : point, B a u z ∧ angle u c z = angle u b y, -- draw half b at c
  {
    obtain ⟨f, hf⟩ := angcopy c_ne_z a_ne_b.symm bL aL yL cM zM aM,
    have a_ne_f : a ≠ f := sorry,
    have b_ne_f : b ≠ f := sorry,
    by_cases fL : online f L,
    {
      refine ⟨f, B_symm (B_of_greater_angle _ _ cM zM hf.2 _), _⟩,
      { sorry, }, -- not colinear c z f
      { refine ⟨L, zL, fL, aL⟩, },
      { convert aby_lt_zca using 1,
        exact hf.1, },
      { convert hf.1 using 1,
        { refine angle_symm _ _ _,
          { sorry, }, -- f ne c
          { sorry, }, -- f ne z
        },
        { refine angle_extension_of_ss b_ne_y _ bN yN bL fL aL _,
          { sorry, }, -- f ne a
          by_contra faN,
          have diffside_faN : diffside f a N := sorry,
          --have := lines_inter_of_not_sameside faN fL aL,
          have Babf := B_of_online_inter a_ne_b b_ne_f a_ne_f L_ne_N aL bL fL bN _,
          exact (diffside_of_B_diffside Babf diffside_abM).2.2 (sameside_symm hf.2),
          intros hh,
          exact diffside_faN.2.2 (sameside_symm hh), }, }, },
    ---------- STOPPED HERE!!
    sorry,
  },
  obtain ⟨u, Bauz, angle_ucz_uby⟩ := this,
  have : ∃ v : point, B u v b ∧ length b v = length c u, -- draw circle at b of radius cu
  {
    sorry,
  },
  obtain ⟨v, Buvb, bv_eq_uc⟩ := this,
  have : ∃ w, B b w y ∧ angle b v w = angle b u c, -- drop parallel from v to uc
  {
    sorry,
  },
  obtain ⟨w, Bbwy, angle_bcw_buc⟩ := this,
  have : length b w = length c z,
  {
    sorry,
  },
  calc length c z = length b w : this.symm
  ... < length b y : _,
  have := length_sum_of_B Bbwy,
  have := length_pos_iff_ne.mpr (ne_23_of_B Bbwy),
  linarith,
end

#exit

-- angle bisectors are equal → isosceles
theorem steiner_lehmus {a b c y z : point} (hbc : b ≠ c) (Bazb : B a z b) (Bayc : B a y c)
  (hb : angle a b y = angle y b c) (hc : angle a c z = angle z c b) (h : length b y = length c z) :
  length a b = length a c :=
begin
  suffices angle_bc : angle a b c = angle a c b,
  { exact isosceles_of_equal_angles (ne_13_of_B Bazb) (ne_13_of_B Bayc) hbc angle_bc, },
  by_contra b_ne_c,
  wlog b_le_c : angle a b c < angle a c b using [b c y z, c b z y],
  { exact ne.lt_or_lt b_ne_c, },
  { exact (steiner_lehmus_prep hbc Bazb Bayc hb hc b_le_c).ne h.symm, },
end
