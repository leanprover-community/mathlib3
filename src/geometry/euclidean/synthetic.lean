/-
Copyright (c) 2022 André Hernandez-Espiet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : André Hernandez-Espiet
-/

import data.real.basic
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
(inside_circle : point → circle → Prop)
(center_circle : point → circle → Prop)
(line_line_inter : line → line → Prop)
(line_circle_inter : line → circle → Prop)
(circle_circle_inter : circle → circle → Prop)
(dist : point → point → real)
(angle : point → point → point → real)
(rightangle : real)
(area : point → point → point → real)

--(P1 : ∀ (S: set point), ∃ (a : point), a∉ S) --Does not work for S= everything. What to do?
--(P2 : ∀ (L :  line), ∃ (a : point), online a L) -- NEVER USED
(pt_B_of_ne : ∀ {b c : point}, b ≠ c → ∃ (a : point), B b a c) -- old (P3)
(pt_extension_of_ne : ∀ {b c : point}, b ≠ c → ∃ (a : point), B b c a)
  -- (P4) not strictly necessary but doesn't cost moves
--(P5 : ∀ (L : line), ∀ (b : point), ¬online b L → ∃ (a : point), a ≠ b ∧ sameside a b L)
  -- (P5) NEVER USED
(opp_side_of_not_online : ∀ {L : line}, ∀ {b : point}, ¬online b L →
  ∃ (a : point), ¬online a L ∧ ¬sameside a b L)
--(P7 : ∀ (α : circle), ∃ (a : point), oncircle a α) -- NEVER USED!!
--(P8 : ∀ (α : circle), ∃ (a : point), inside_circle a α) -- NEVER USED!!
--(P9 : ∀ (α : circle), ∃ (a : point), ¬inside_circle a α ∧ ¬oncircle a α) -- NEVER USED!!

(line_of_ne : ∀ {a b : point}, a ≠ b → ∃ (L :line), online a L ∧ online b L) -- old (LC1)
(circle_of_ne : ∀ {a b : point}, a ≠ b → ∃ (α : circle), center_circle a α ∧ oncircle b α)
  -- old (LC2)

(pt_of_line_line_inter : ∀ {L M : line}, line_line_inter L M →
  ∃ (a : point), online a L ∧ online a M)
--(pt_of_line_circle_inter : ∀ {L : line}, ∀ {α : circle}, line_circle_inter L α →
--  ∃ (a : point), online a L ∧ oncircle a α)
   --pts_of_line_circle_inter Should be proven?
(pts_of_line_circle_inter : ∀ {L : line}, ∀ {α : circle}, line_circle_inter L α →
  ∃ (a b : point), online a L ∧ online b L ∧ oncircle a α ∧ oncircle b α ∧ a ≠ b)
(pt_oncircle_of_inside_outside : ∀ {b c : point}, ∀ {α : circle},
  inside_circle b α → ¬inside_circle c α → ¬oncircle c α →
  ∃ (a : point), oncircle a α ∧ B b a c)
(pt_oncircle_of_inside_ne : ∀ {b c : point}, ∀ {α : circle}, inside_circle b α → c ≠ b →
  ∃ (a : point), oncircle a α ∧ B a b c)
--pt_oncircle_of_inside_ne can be proven?
--(I6 : ∀ {α β : circle}, circle_circle_inter α β → ∃ (a : point), oncircle a α ∧ oncircle a β)
(pts_of_circle_circle_inter : ∀ {α β : circle}, circle_circle_inter α β →
  ∃ (a b : point), oncircle a α ∧ oncircle a β ∧ oncircle b α ∧ oncircle b β ∧ a ≠ b)
(pt_sameside_of_circle_circle_inter : ∀ {b c d : point}, ∀ {α β : circle}, ∀ {L : line},
  circle_circle_inter α β → center_circle c α → center_circle d β → online c L → online d L →
  ¬online b L → ∃ (a : point), oncircle a α ∧ oncircle a β ∧ sameside a b L)
--(I9 : ∀ {b c d : point}, ∀ {α β : circle}, ∀ {L : line}, circle_circle_inter α β → center_circle c α →
--  center_circle d β → online c L → online d L → ¬online b L →
--  ∃ (a : point), oncircle a α ∧ oncircle a β ∧ ¬sameside a b L ∧ ¬online a L) -- NEVER USED!!

(line_unique_of_pts : ∀ {a b : point}, ∀ {L M : line}, a ≠ b → online a L → online b L →
  online a M → online b M → L = M)
(center_circle_unique : ∀ {a b : point}, ∀ {α : circle}, center_circle a α → center_circle b α →
  a = b)
  --center_circle_unique should be proven?
(inside_circle_of_center : ∀ {a : point}, ∀ {α : circle}, center_circle a α → inside_circle a α)
(not_oncircle_of_inside : ∀ {a : point}, ∀ {α : circle}, inside_circle a α → ¬oncircle a α)

(B1 : ∀ {a b c : point}, B a b c → B c b a ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬B b a c)
  -- B1 slightly modified, hope no issue?
(B2 : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → online b L → online c L)
(B3 : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → online c L → online b L)
  -- B3 can be proven?
(B4 : ∀ {a b c d : point}, B a b c → B a d b → B a d c)
(B5 : ∀ {a b c d : point}, B a b c → B b c d → B a b d)
(B6 : ∀ {a b c : point}, ∀ {L : line}, online a L → online b L → online c L → a ≠ b → a ≠ c → b ≠ c
  → B a b c ∨ B b a c ∨ B a c b)
(B7 : ∀ {a b c d : point}, B a b c → B a b d → ¬B c b d)

(S1 : ∀ {a : point}, ∀ {L : line}, ¬online a L → sameside a a L)
(S2 : ∀ {a b : point}, ∀ {L : line}, sameside a b L → sameside b a L)
(S3 : ∀ {a b : point}, ∀ {L : line}, sameside a b L → ¬online a L)
(S4 : ∀ {a b c : point}, ∀ {L : line}, sameside a b L → sameside a c L → sameside b c L)
(S5 : ∀ {a b c : point}, ∀ {L : line}, ¬online a L → ¬online b L → ¬online c L→
  ¬sameside a b L → sameside a c L ∨ sameside b c L)

(Pa1 : ∀ {a b c : point}, ∀ {L : line}, B a b c → sameside a c L → sameside a b L)
(Pa2 : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → ¬online b L → sameside b c L)
(Pa3 : ∀ {a b c : point}, ∀ {L : line}, B a b c → online b L → ¬sameside a c L)
(Pa4 : ∀ {a b c : point}, ∀ {L M : line}, L ≠ M → a ≠ c → online a M → online b M → online c M →
  online b L → a ≠ b → c ≠ b → ¬sameside a c L → B a b c)

(T1 : ∀ {a b c d : point}, ∀ {L M N : line}, online a L → online a M → online a N → online b L →
  online c M → online d N → sameside c d L → sameside b c N → ¬sameside b d M)
(T2 : ∀ {a b c d : point}, ∀ {L M N : line}, online a L → online a M → online a N → online b L →
  online c M → online d N → sameside c d L → ¬sameside b d M → ¬online d M → b ≠ a →
  sameside b c N)
(T3 : ∀ (a b c d e : point), ∀ (L M N : line), online a L → online a M → online a N → online b L →
  online c M → online d N → sameside c d L → sameside b c N → sameside d e M → sameside c e N →
  sameside c e L) -- NEVER USED!!

(C1 : ∀ {a b c : point}, ∀ {L : line}, ∀ {α : circle }, online a L → online b L → online c L
  → inside_circle a α → oncircle b α → oncircle c α → b ≠ c → B b a c)
(C2 : ∀ (a b c : point), ∀ (α : circle), inside_circle a α ∨ oncircle a α → inside_circle b α ∨ oncircle b α →
  B a c b → inside_circle c α)
(C3 : ∀ (a b c : point), ∀ (α : circle), inside_circle a α ∨ oncircle a α → ¬inside_circle c α → B a c b →
  ¬inside_circle b α ∧ ¬oncircle b α) -- NEVER USED!!!
(C4 : ∀ {a b c d : point}, ∀ {α β : circle}, ∀ {L : line}, α ≠ β → c ≠ d→ circle_circle_inter α β →
  oncircle c α → oncircle c β → oncircle d α → oncircle d β → center_circle a α → center_circle b β → online a L
  → online b L → ¬sameside c d L)

(Int1 : ∀ {a b : point}, ∀ {L M : line}, ¬sameside a b L → online a M → online b M →
  line_line_inter L M)
(Int2 : ∀ {a b : point}, ∀ {L : line}, ∀ {α : circle}, inside_circle a α ∨ oncircle a α →
  inside_circle b α ∨ oncircle b α → ¬sameside a b L → line_circle_inter L α)
(Int3 : ∀ {a : point}, ∀ {L : line}, ∀ {α : circle}, inside_circle a α → online a L → line_circle_inter L α)
(Int4 : ∀ {a b : point}, ∀ {α β : circle}, oncircle a α → inside_circle b α ∨ oncircle b α → inside_circle a β →
  ¬inside_circle b β → ¬oncircle b β → circle_circle_inter α β) -- NEVER USED!!
(Int5 : ∀ {a b : point}, ∀ {α β : circle}, inside_circle a α → oncircle b α → inside_circle b β → oncircle a β →
  circle_circle_inter α β)

(M1 : ∀ {a b : point}, dist a b = 0 ↔ a = b)
(M2 : ∀ (a b : point), dist a b = dist b a)
(M3 : ∀ {a b c : point}, a ≠ b → a ≠ c → angle a b c = angle c b a)
(M4 : ∀ (a b c : point), angle a b c ≤ 2 * rightangle ∧ 0 ≤ angle a b c)
(M5 : ∀ (a b : point), 0 ≤ dist a b)
--(M6 : 0 < rightangle) I believe this can be deduced from M4 together with A1 (there exist nonzero angles)
(M6 : ∀ (a b : point), area a a b = 0)
(M7 : ∀ (a b c : point), 0 ≤ area a b c) -- NEVER USED!
(M8 : ∀ (a b c : point), area a b c = area c a b ∧ area a b c = area a c b)
(M9 : ∀ {a b c a1 b1 c1 : point}, dist a b = dist a1 b1 → dist b c = dist b1 c1 →
  dist c a = dist c1 a1 → angle a b c = angle a1 b1 c1 → angle b a c = angle b1 a1 c1 →
  angle a c b = angle a1 c1 b1 → area a b c = area a1 b1 c1)

(DS1 : ∀ {a b c : point}, B a b c → dist a b + dist b c = dist a c)
(DS2 : ∀ {a b c : point}, ∀ {α β : circle}, center_circle a α → center_circle a β → oncircle b α → oncircle c β
  → dist a b = dist a c → α = β) -- NEVER USED!
(DS3 : ∀ {a b c : point}, ∀ {α : circle}, center_circle a α → oncircle b α →
  (dist a b = dist a c ↔ oncircle c α))
(DS4 : ∀ {a b c : point}, ∀ {α : circle}, center_circle a α → oncircle b α →
  (dist a c < dist a b ↔ inside_circle c α))

(A1 : ∀ {a b c : point}, ∀ {L : line}, a ≠ b → a ≠ c → online a L → online b L →
  (online c L ∧ ¬B b a c ↔ angle b a c = 0))--better reformulation?
(A2 : ∀ {a b c d : point}, ∀ {L M : line}, online a L → online b L → online a M → online c M →
  a ≠ b → a ≠ c → ¬online d M → ¬online d L → L ≠ M →
  (angle b a c = angle b a d + angle d a c ↔ sameside b d M ∧ sameside c d L))
(A3 : ∀ {a b c d : point}, ∀ {L : line}, online a L → online b L → B a c b → ¬online d L →
  (angle a c d = angle d c b ↔ angle a c d = rightangle))
(A4 : ∀ {a b c a1 b1 c1 : point}, ∀ {L M : line}, online a L → online b L → online b1 L →
  online a M → online c M → online c1 M → b ≠ a → b1 ≠ a → c ≠ a → c1 ≠ a → ¬B b a b1 →
  ¬B c a c1 → angle b a c = angle b1 a1 c1)
(A5 : ∀ {a b c d : point}, ∀ {L M N : line}, online a L → online b L → online b M → online c M →
  online c N → online d N → b ≠ c → sameside a d M → angle a b c + angle b c d < 2 * rightangle →
  ∃ (e : point), online e L ∧ online e N ∧ sameside e a M)

(DA1 : ∀ {a b c : point}, ∀ {L : line}, online a L → online b L → a ≠ b →
  (area a b c = 0 ↔ online c L))
(DA2 : ∀ {a b c d : point}, ∀ {L : line}, a ≠ b → b ≠ c → c ≠ a → online a L → online b L →
  online c L → ¬online d L → (B a c b ↔ area a c d + area d c b = area a d b))

(S : ∀ {a b c d e f : point}, dist a b = dist d e → dist a c = dist d f →
  (angle b a c = angle e d f ↔ dist b c = dist e f)) --Euclid Prop 4,8

open incidence_geometry

----------------------

noncomputable theory

-- instantiation of axioms in ℝ × ℝ

instance incidence_geometry_ℝ_ℝ : incidence_geometry :=
{ point := ℝ × ℝ, -- p = (x, y)
  line := ℝ × ℝ × ℝ, -- a x + b y = c ↔ (a, b, c)
  circle := (ℝ × ℝ) × (ℝ × ℝ), -- center and point on circle
  online := λ p L, L.1 * p.1 + L.2.1 * p.2 = L.2.2,
  sameside := λ p1 p2 L, L.1 * p1.1 + L.2.1 * p1.2 - L.2.2 ≠ 0 ∧
  L.1 * p2.1 + L.2.1 * p2.2 - L.2.2 ≠ 0 ∧
  ∃ (μ : ℝ), 0 < μ ∧ (L.1 * p1.1 + L.2.1 * p1.2 - L.2.2) = μ * (L.1 * p2.1 + L.2.1 * p2.2 - L.2.2),
  B := λ p1 p2 p3, p1 ≠ p2 ∧ p2 ≠ p3 ∧ ∃ (μ : ℝ), 0 < μ ∧ (p3 - p2) = μ • (p2-p1),
  oncircle := λ p ⟨c, b⟩, -- p is a point, c is the center, b is a point on the circle
   (c.1^2 - b.1^2) + (c.2^2 - b.2^2) = (c.1^2 - p.1^2) + (c.2^2 - p.2^2),
  inside_circle := λ p ⟨c, b⟩, -- p is a point, c is the center, b is a point on the circle
   (c.1^2 - p.1^2) + (c.2^2 - p.2^2) < (c.1^2 - b.1^2) + (c.2^2 - b.2^2),
  center_circle := λ p ⟨c, b⟩, p = c,
  line_line_inter := λ L1 L2,
    ¬∃ (μ : ℝ), L1 = μ • L2 ∧ ¬∃ (μ : ℝ), (L1.1, L1.2.1) = μ • (L2.1, L2.2.1),
  line_circle_inter := sorry, -- messy...?
  circle_circle_inter := sorry, -- already have the conditions below
  dist := λ p1 p2, ((p1.1 - p2.1)^2 + (p2.1 - p2.2)^2).sqrt,
  angle := sorry, -- messy...?
  rightangle := sorry, -- slopes
  area := sorry, -- Heron's formula!
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
  opp_side_of_not_online := sorry,
  line_of_ne := sorry,
  circle_of_ne := sorry,
  pt_of_line_line_inter := sorry,
  pts_of_line_circle_inter := sorry,
  pt_oncircle_of_inside_outside := sorry,
  pt_oncircle_of_inside_ne := sorry,
  pts_of_circle_circle_inter := sorry,
  pt_sameside_of_circle_circle_inter := sorry,
  line_unique_of_pts := sorry,
  center_circle_unique := sorry,
  inside_circle_of_center := sorry,
  not_oncircle_of_inside := sorry,
  B1 := begin
    intros a b c Babc,
    obtain ⟨μ, hμ₁, hμ₂⟩ := Babc.2.2,
    split,
    { refine ⟨Babc.2.1.symm, Babc.1.symm, _⟩,
      use 1/μ,
      refine ⟨one_div_pos.mpr hμ₁, _⟩,
      convert (congr_arg (λ x : ℝ × ℝ, ((-1 : ℝ) / μ) • x) hμ₂).symm using 1,
      { rw [smul_smul, ← neg_sub a b, ← neg_one_smul _ (a-b), smul_smul],
        convert (one_smul _ (a-b)).symm,
        field_simp [hμ₁.ne.symm], },
      { rw [← neg_sub, ← neg_one_smul _ (c-b), smul_smul],
        apply congr_arg (λ x : ℝ, x • (c-b)),
        field_simp [hμ₁.ne.symm], }, },
    refine ⟨Babc.1, _⟩,
    split,
    { intros hac,
      rw hac at hμ₂,
      rw ← neg_sub b c at hμ₂,
      rw ← neg_one_smul ℝ (b-c) at hμ₂,
      have : b-c ≠ 0 := λ  hbc, Babc.2.1 (sub_eq_zero.mp hbc),
      have : -1 = μ,
      {
        sorry,
      },
      linarith,
    },
    refine ⟨Babc.2.1, _⟩,
    push_neg,
    intros _ _ μ' hμ' hμ'',
    have : μ' = -(1+μ),
    {
      sorry,
    },
    linarith,
  end,
  B2 := sorry,
  B3 := sorry,
  B4 := sorry,
  B5 := sorry,
  B6 := sorry,
  B7 := sorry,
  S1 := sorry,
  S2 := sorry,
  S3 := sorry,
  S4 := sorry,
  S5 := sorry,
  Pa1 := sorry,
  Pa2 := sorry,
  Pa3 := sorry,
  Pa4 := sorry,
  T1 := sorry,
  T2 := sorry,
  T3 := sorry,
  C1 := sorry,
  C2 := sorry,
  C3 := sorry,
  C4 := sorry,
  Int1 := sorry,
  Int2 := sorry,
  Int3 := sorry,
  Int4 := sorry,
  Int5 := sorry,
  M1 := sorry,
  M2 := sorry,
  M3 := sorry,
  M4 := sorry,
  M5 := sorry,
  M6 := sorry,
  M7 := sorry,
  M8 := sorry,
  M9 := sorry,
  DS1 := sorry,
  DS2 := sorry,
  DS3 := sorry,
  DS4 := sorry,
  A1 := sorry,
  A2 := sorry,
  A3 := sorry,
  A4 := sorry,
  A5 := sorry,
  DA1 := sorry,
  DA2 := sorry,
  S := sorry }

----------------------

#exit

variables[AxA: incidence_geometry]

include AxA
-------------------------------------------------- API --------------------------------------------'
local notation `|`x`|` := abs x

theorem flip1 {a b c d : point} (abcd : dist a b = dist c d) : dist b a = dist c d :=
  by rwa M2 a b at abcd
theorem flip2 {a b c d : point} (abcd : dist a b = dist c d) : dist a b = dist d c :=
  (flip1 abcd.symm).symm
theorem flipboth {a b c d : point} (abcd : dist a b = dist c d) : dist b a = dist d c :=
  flip2 (flip1 abcd)
theorem aflip1 {a b c d e f : point} (ab : a ≠ b) (ac : a ≠ c) (ang : angle a b c = angle d e f) :
  angle c b a = angle d e f := by rwa M3 ab ac at ang
theorem aflip2 {a b c d e f : point} (de : d ≠ e) (df : d ≠ f) (ang : angle a b c = angle d e f) :
  angle a b c = angle f e d := (aflip1 de df ang.symm).symm
theorem aflipboth {a b c d e f : point} (ab : a ≠ b) (ac : a ≠ c) (de : d ≠ e) (df : d ≠ f)
  (ang : angle a b c = angle d e f) : angle c b a = angle f e d :=
  (aflip2 de df) (aflip1 ab ac ang)

theorem Beasy (a b : point) : ¬B a b a ∧ ¬B a a b :=
  ⟨λ Baba, (B1 Baba).2.2.1 rfl, λ Baab, (B1 Baab).2.1 rfl⟩

theorem Beasy2 {a b c d e : point} {L : line} (bd : b ≠ d) (aL : online a L) (bL : online b L)
  (dL : ¬online d L) (Babc : B a b c) (Bade : B a d e) : b ≠ e :=
begin
  intro be, rw be.symm at Bade, exact dL (B3 Bade aL bL), --anything better?
end

theorem Beasy3 {a b c : point} (Babc : B a b c) :
  ∃ (L : line), online a L ∧ online b L ∧ online c L ∧ a ≠ b ∧ b ≠ c ∧ c ≠ a :=
begin
  rcases line_of_ne (B1 Babc).2.1 with ⟨L, aL, bL⟩,
  refine ⟨L, aL, bL, B2 Babc aL bL, (B1 Babc).2.1, (B1 Babc).2.2.2.1, (B1 Babc).2.2.1.symm⟩,
end

theorem Beasy4 {a b c : point} (Babc : ¬B a b c) : ¬B c b a := λ Bcba, Babc (B1 Bcba).1

theorem Beasy5 {a b c d : point} (cd : c ≠ d) (Babc : B a b c) (Babd : B a b d) :
  B b c d ∨ B b d c :=
begin
  rcases Beasy3 Babc with ⟨L, aL, bL, cL, ab, bc, ca⟩,
  cases B6 bL cL (B2 Babd aL bL) bc (B1 Babd).2.2.2.1 cd,
  left, assumption, cases h, exfalso, exact (B7 Babc Babd) h, right, exact h, --again
end

theorem Beasy6 {a b c d : point} (bc : b ≠ c) (Babd : B a b d) (Bacd : B a c d) :
  B a b c ∨ B a c b :=
begin
  rcases Beasy3 Babd with ⟨L, aL, bL, dL, nq⟩,
  cases B6 aL bL (B3 Bacd aL dL) nq.1 (B1 Bacd).2.1 bc, left, exact h, cases h, exfalso,
  exact (B1 (B5 (B1 h).1 Babd)).2.2.2.2 Bacd, right, exact h,
end

theorem Beasy7 {a b c d : point} (Babc : B a b c) (Bacd : B a c d) : B b c d :=
begin
  rcases Beasy3 Babc with ⟨L, aL, bL, cL, nq⟩,
  have bd : b ≠ d,
  { intro bd,
    rw bd at Babc,
    exact (B1 (B1 Babc).1).2.2.2.2 (B1 Bacd).1, },
  have := B6 bL cL (B2 Bacd aL cL) nq.2.1 bd (B1 Bacd).2.2.2.1,
  cases this, exact this,
  exfalso, cases this,
  have Bdba := B4 (B1 Bacd).1 (B1 this).1,
  cases Beasy5 nq.2.2.symm Bdba (B1 this).1 with Bet,
  exact (B1 Bet).2.2.2.2 Babc,
  exact (B1 h).2.2.2.2 (B1 Babc).1,
  exact (B1 (B1 (B4 Babc (B1 (B5 this (B1 Bacd).1)).1)).1).2.2.2.2 (B1 Bacd).1,
end

theorem Leasy {a b : point} {L : line} (aL : online a L) (bL : ¬online b L) : a ≠ b :=
begin
  intro ab, rw ab at aL, exact bL aL,
end

theorem Leasy2 {a b c : point} {L M : line} (ab : a ≠ b) (ac : a ≠ c) (LM : L ≠ M)
  (aL : online a L) (aM : online a M) (bL : online b L) (cM : online c M) : b ≠ c
   := λ bc, LM (line_unique_of_pts ab aL bL aM (by rwa bc.symm at cM))

theorem Leasy3 {a b c : point} {L M : line} (ab : a ≠ b) (aL : online a L) (bL : online b L)
  (cL : ¬online c L) (bM : online b M) (cM : online c M) : ¬online a M
   := λ aM, cL (by rwa ← (line_unique_of_pts ab aL bL aM bM) at cM)

theorem Leasy4 {a : point} {L M : line} (aL : online a L) (aM : ¬online a M) : L ≠ M
  := λ LM, aM (by rwa LM at aL)

theorem A1mprmod {a b c : point} {L : line} (ab : a ≠ b) (aL : online a L) (bL : online b L)
  (cL : ¬online c L) : 0 < angle b a c :=
begin --can be simplified to one line probably
  by_contra, push_neg at h, exact cL ((A1 ab (Leasy aL cL) aL bL).mpr (by linarith [M4 b a c])).1,
end

theorem A2mprmod {a b c d : point} {L M : line} (ab : a ≠ b) (ac : a ≠ c) (aL : online a L)
  (bL : online b L) (aM : online a M) (cM : online c M) (bdM : sameside b d M)
  (cdL : sameside c d L) :
  angle b a c = angle b a d + angle d a c ∧ angle b a d < angle b a c ∧ angle d a c < angle b a c
  ∧ 0 < angle b a d ∧ 0 < angle d a c :=
begin
  have angsplit := (A2 aL bL aM cM ab ac (S3 (S2 bdM)) (S3 (S2 cdL))
    (λ LM, (S3 cdL) (by rwa ← LM at cM))).mpr ⟨bdM, cdL⟩,
  rcases line_of_ne (Leasy aL (S3 (S2 cdL))) with ⟨N, aN, dN⟩,
  have ang1 := A1mprmod ab aL bL (S3 (S2 cdL)),
  have ang2 := A1mprmod (Leasy aL (S3 (S2 cdL))) aN dN (λ cN, (S3 (S2 bdM))
    (by rwa ← (line_unique_of_pts ac aM cM aN cN) at dN)),
  exact ⟨angsplit, by linarith, by linarith, ang1, ang2⟩,
end

theorem A4mod {a b c b1 c1 : point} (Babb1 : B a b b1) (Bacc1 : B a c c1) :
  angle b a c = angle b1 a c1 :=
begin
  rcases line_of_ne (B1 Babb1).2.1 with ⟨L, aL, bL⟩; rcases line_of_ne (B1 Bacc1).2.1 with ⟨M, aM, cM⟩,
  exact A4 aL bL (B2 Babb1 aL bL) aM cM (B2 Bacc1 aM cM) (B1 Babb1).2.1.symm (B1 Babb1).2.2.1.symm
  (B1 Bacc1).2.1.symm (B1 Bacc1).2.2.1.symm (B1 Babb1).2.2.2.2 (B1 Bacc1).2.2.2.2,
end

theorem A4mod1 {a b c b1 : point} (ac : a ≠ c) (Babb1 : B a b b1) : angle b a c = angle b1 a c :=
begin
  rcases line_of_ne (B1 Babb1).2.1 with ⟨L, aL, bL⟩, rcases line_of_ne ac with ⟨M, aM, cM⟩,
  exact A4 aL bL (B2 Babb1 aL bL) aM cM cM (B1 Babb1).2.1.symm (B1 Babb1).2.2.1.symm ac.symm
    ac.symm (B1 Babb1).2.2.2.2 (Beasy c a).1,
end

theorem A4mod2 {a b c b1 : point} {L M : line} (ac : a ≠ c) (bb1 : b ≠ b1) (aL : online a L)
  (cL : online c L) (aM : online a M) (bM : online b M) (b1M : online b1 M)
  (bb1L : sameside b b1 L) : angle b a c = angle b1 a c :=
begin
  cases B6 aM bM b1M (Leasy aL (S3 bb1L)) (Leasy aL (S3 (S2 bb1L))) bb1,
  exact A4mod1 ac h, cases h, exfalso, exact (Pa3 h) aL bb1L, exact (A4mod1 ac h).symm,
end

theorem DA2mpmod {a b c d : point} {L : line} (aL : online a L) (bL : online b L)
  (cL : online c L) (dL : ¬online d L) (Bacb : B a c b) : area a c d + area d c b = area a d b
  := (DA2 (B1 Bacb).2.2.1 (B1 Bacb).2.2.2.1.symm (B1 Bacb).2.1.symm aL bL cL dL).mp Bacb

theorem sss {a b c d e f : point} (lab : dist a b = dist d e) (lbc : dist b c = dist e f)
  (lac : dist a c = dist d f)
  : angle a b c = angle d e f ∧ angle b a c = angle e d f ∧ angle a c b = angle d f e
  := ⟨(S (flipboth lab) lbc).2 lac, (S lab lac).2 lbc, (S (flipboth lac) (flipboth lbc)).2 lab⟩

theorem sas {a b c d e f : point} (ab : dist a b = dist d e) (ac : dist a c = dist d f)
  (Abac : angle b a c = angle e d f)
  : dist b c = dist e f ∧ angle a b c = angle d e f ∧ angle a c b = angle d f e
  := ⟨(S ab ac).1 Abac, (sss ab ((S ab ac).1 Abac) ac).1, (sss ab ((S ab ac).1 Abac) ac).2.2⟩ --Euclid I.4

lemma nonzerolen {a b : point} (hab : a ≠ b) : 0 < dist a b
  := (ne.symm (not_imp_not.2 M1.1 hab)).le_iff_lt.mp (M5 a b)

lemma nonzerolenconv {a b : point} (len : 0 < dist a b) : a ≠ b
  := (not_congr (M1)).1 (ne_of_gt len)

lemma DS1rev {a b c : point} {L : line} (ab : a ≠ b) (bc : b ≠ c) (ac : a ≠ c) (aL : online a L)
  (bL : online b L) (cL : online c L) (len : dist a b + dist b c ≤ dist a c) : B a b c :=
begin
  cases B6 aL bL cL ab ac bc, assumption, cases h,
  linarith [DS1 h, M2 a b, nonzerolen ab], linarith [DS1 h, M2 c b, nonzerolen bc],
end

theorem Leneasy {a b c : point} (ac : a ≠ c) (len : dist a b = dist b c) : a ≠ b
  := λ ab, by linarith [nonzerolen (ne_of_eq_of_ne (eq.symm ab) ac), M1.mpr ab]

theorem ceneqon {a b : point} {α : circle} (acen : center_circle a α) (bcirc : oncircle b α) : a ≠ b :=
begin
  intro ab,
  have := not_oncircle_of_inside (inside_circle_of_center acen),
  rw ab at this,
  exact this bcirc,
end

theorem difcendifcirc {a b : point} {α β : circle} (acen : center_circle a α) (bcen : center_circle b β)
  (ab : a ≠ b) : α ≠ β :=
begin
  intro albet, rw albet at acen,
  have := center_circle_unique acen bcen,
  exact ab this,
end

def iseqtri (a b c : point) : Prop :=
  dist a b = dist a c  ∧ dist b c = dist b a ∧ dist c a = dist c b ∧ a ≠ b ∧ b ≠ c ∧ c ≠ a

def diffside (a b : point) (L : line) : Prop := ¬online a L ∧ ¬online b L ∧ ¬sameside a b L

theorem difsym {a b : point} {L : line} (nss : ¬sameside a b L) : ¬sameside b a L
  := λ nss2, nss (S2 nss2)

theorem difdifsame {a b c : point} {L : line} (dsab : diffside a b L) (dsac : diffside a c L) :
  sameside b c L :=
begin
  by_contra,
  have := S5 dsab.1 dsab.2.1 dsac.2.1 dsab.2.2,
  cases this,
  exact dsac.2.2 this,
  exact h this,
end

theorem difsamedif {a b c : point} {L : line} (ssab : sameside a b L) (dsac : diffside a c L) :
  diffside b c L :=
begin
  by_contra,
  unfold diffside at h,
  push_neg at h,
  exact dsac.2.2 (S4 (S2 ssab) (h (S3 (S2 ssab)) dsac.2.1)),
end

theorem difneq {a b : point} {L : line} (dsab : diffside a b L) : a ≠ b :=
begin
  intro ab,
  rw ab at dsab,
  unfold diffside at dsab,
  have := S1 dsab.1,
  exact dsab.2.2 this,
end

theorem angeasy {a b c : point} {d : ℝ} (ab : a ≠ b) (ac : a ≠ c) (ang : d ≠ angle a b c) :
  d ≠ angle c b a := by rwa (M3 ab ac) at ang

def para (a b c d : point) (M N : line) : Prop := online a M ∧ online b M ∧ online c N ∧ online d N
  ∧ (∀  (e : point), ¬online e M ∨ ¬online e N)

theorem paraeasy {a b c d e : point} {M N : line} (eN : online e N) (par : para a b c d M N) :
  para a b e d M N := ⟨par.1, par.2.1, eN, par.2.2.2.1, (λ g, par.2.2.2.2 g)⟩

theorem paraeasy1 {a b c d : point} {M N : line} (par : para a b c d M N) : para d c b a N M
  :=⟨par.2.2.2.1, par.2.2.1, par.2.1, par.1, (λ g, or.swap (par.2.2.2.2 g))⟩

theorem paraeasy2 {a b c d : point} {M N : line} (par : para a b c d M N) : M ≠ N ∧ ¬online a N ∧
  ¬online b N ∧ ¬online c M ∧ ¬online d M ∧ sameside a b N ∧ sameside c d M :=
begin
  have MN : M ≠ N, { intro MN, rw MN at par, cases par.2.2.2.2 a, exact h par.1, exact h par.1, },
  have aN : ¬online a N, { intro aN, cases par.2.2.2.2 a, exact h par.1, exact h aN, },
  have bN : ¬online b N, { intro bN, cases par.2.2.2.2 b, exact h par.2.1, exact h bN, },
  have cM : ¬online c M, { intro cM, cases par.2.2.2.2 c, exact h cM, exact h par.2.2.1, },
  have dM : ¬online d M, { intro dM, cases par.2.2.2.2 d, exact h dM, exact h par.2.2.2.1, },
  have abN : sameside a b N, { by_contra abN, rcases pt_of_line_line_inter (Int1 abN par.1 par.2.1) with ⟨z,zN,zM⟩,
    cases par.2.2.2.2 z, exact h zM, exact h zN, },
  have cdM : sameside c d M, { by_contra cdM, rcases pt_of_line_line_inter (Int1 cdM par.2.2.1 par.2.2.2.1) with
    ⟨z, zM, zN⟩, cases par.2.2.2.2 z, exact h zM, exact h zN, },
  exact ⟨MN, aN, bN, cM, dM, abN, cdM⟩,
end


theorem paraeasy3 {a b c d : point} {M N : line} (par : para a b c d M N) : para b a d c M N :=
  ⟨par.2.1, par.1, par.2.2.2.1, par.2.2.1, (λ e, par.2.2.2.2 e)⟩

theorem paraeasy4 {a b c d : point} {M N : line} (par : para a b c d M N) : para c d a b N M :=
  ⟨par.2.2.1, par.2.2.2.1, par.1, par.2.1, (λ e, or.swap (par.2.2.2.2 e))⟩

theorem paraeasy5 {a b c d : point} {M N : line} (par : para a b c d M N) : para a b d c M N :=
  ⟨par.1, par.2.1, par.2.2.2.1, par.2.2.1, (λ e, par.2.2.2.2 e)⟩

theorem paraeasy6 {a b c d : point} {M N : line} (par : para a b c d M N) : para b a c d M N :=
  ⟨par.2.1, par.1, par.2.2.1, par.2.2.2.1, (λ e, par.2.2.2.2 e)⟩


theorem circint {a b c d : point} {α β : circle} (acen : center_circle a α) (bcen : center_circle b β)
  (ccirc : oncircle c α) (dcirc : oncircle d β) (cenbig : |dist a c - dist b d| < dist a b)
  (censmall : dist a b < dist a c + dist b d) : circle_circle_inter α β :=
begin
  have := abs_lt.mp cenbig,
  have ab : a ≠ b := mt M1.mpr (by linarith : dist a b ≠ 0),
  rcases line_of_ne ab with ⟨L, aL, bL⟩,
  rcases pts_of_line_circle_inter (Int3 (inside_circle_of_center acen) aL) with ⟨c1, c2, c1L, c2L, c1circ, c2circ, c1c2⟩,
  rcases pts_of_line_circle_inter (Int3 (inside_circle_of_center bcen) bL) with ⟨d1, d2, d1L, d2L, d1circ, d2circ, d1d2⟩,
  have Bc1ac2 := C1 aL c1L c2L (inside_circle_of_center acen) c1circ c2circ c1c2,
  have Bd1bd2 := C1 bL d1L d2L (inside_circle_of_center bcen) d1circ d2circ d1d2,
  have clen1 := (DS3 acen ccirc).mpr c1circ,
  have clen2 := (DS3 acen ccirc).mpr c2circ,
  have dlen1 := (DS3 bcen dcirc).mpr d1circ,
  have dlen2 := (DS3 bcen dcirc).mpr d2circ,
  have cin : inside_circle c1 β ∨ inside_circle c2 β,
  { by_contra out, push_neg at out,
    have ineq2 := mt (DS4 bcen d2circ).mp out.1, push_neg at ineq2,
    have ineq4 := mt (DS4 bcen d2circ).mp out.2, push_neg at ineq4,
    have bc1 : b ≠ c1 := nonzerolenconv (by linarith [nonzerolen (B1 Bd1bd2).2.2.2.1] :
      0 < dist b c1),
    have bc2 : b ≠ c2 := nonzerolenconv (by linarith [nonzerolen (B1 Bd1bd2).2.2.2.1] :
      0 < dist b c2),
    cases B6 aL c2L bL (B1 Bc1ac2).2.2.2.1 ab bc2.symm with Bac2b Bet,
    linarith [DS1 Bac2b, M2 b c2],
    cases Bet with Bc2ab Babc2,
    cases Beasy5 bc1.symm (B1 Bc1ac2).1 Bc2ab with Bac1b Babc1,
    linarith [DS1 Bac1b, M2 b c1],
    linarith [DS1 Babc1],
    linarith [DS1 Babc2], },
  have din : inside_circle d1 α ∨ inside_circle d2 α,
  { by_contra out, push_neg at out,
    have := mt (DS4 acen c2circ).mp out.1, push_neg at this,
    have := mt (DS4 acen c2circ).mp out.2, push_neg at this,
    have ad1 : a ≠ d1 := nonzerolenconv (by linarith [nonzerolen (B1 Bc1ac2).2.2.2.1] :
      0 < dist a d1),
    have ad2 : a ≠ d2 := nonzerolenconv (by linarith [nonzerolen (B1 Bc1ac2).2.2.2.1] :
      0 < dist a d2),
    cases B6 aL bL d1L ab ad1 (B1 Bd1bd2).2.1.symm with Babd1 Bet,
    cases Beasy5 ad2 (B1 Babd1).1 Bd1bd2 with Bbad2 Bbd2a,
    linarith [M2 a b, DS1 Bbad2],
    linarith [M2 d2 a, M2 a b, DS1 Bbd2a],
    cases Bet with Bbad1 Bad1b,
    linarith [M2 a b, DS1 Bbad1],
    linarith [M2 d1 b, DS1 Bad1b], },
  cases cin with c1bet c2bet,
  cases din with d1alp d2alp,
  exact Int5 d1alp c1circ c1bet d1circ,
  exact Int5 d2alp c1circ c1bet d2circ,
  cases din with d1alp d2alp,
  exact Int5 d1alp c2circ c2bet d1circ,
  exact Int5 d2alp c2circ c2bet d2circ,
end

theorem quadiag {a b c d : point} {L M N : line} (ab : a ≠ b) (cd : c ≠ d) (aL : online a L)
  (bL : online b L) (cM : online c M) (dM : online d M) (bN : online b N) (dN : online d N)
  (abM : sameside a b M) (cdL : sameside c d L) (acN : sameside a c N) :
  ∃ (e : point) (O P : line), online a O ∧ online d O ∧ online b P ∧ online c P ∧  online e O ∧
  online e P ∧ B b e c ∧ B d e a ∧ ¬online c O ∧ ¬online b O ∧ ¬online d P ∧ ¬online a P :=
begin
  rcases line_of_ne (Leasy aL (S3 (S2 cdL))) with ⟨O, aO, dO⟩,
  rcases line_of_ne (Leasy cM (S3 (S2 abM))) with ⟨P, cP, bP⟩,
  rcases line_of_ne (Leasy aL (S3 cdL)) with ⟨K, aK, cK⟩,
  have OP : O ≠ P := λ OP, (S3 cdL (by rwa ←(line_unique_of_pts ab aL bL (by rwa OP at aO) bP) at cP)),
  have bcO := T1 dN dO dM bN aO cM acN (S2 abM),
  rcases pt_of_line_line_inter (Int1 bcO bP cP) with ⟨e, eO, eP⟩,
  have be : b ≠ e := λ be, (S3 (S2 cdL)) (by rwa ←(line_unique_of_pts ab aL bL aO (by rwa ← be at eO)) at dO),
  have ce : c ≠ e := λ ce, (S3 abM) (by rwa line_unique_of_pts cd cM dM (by rwa ← ce at eO) dO),
  have de : d ≠ e := λ de, (S3 (S2 abM)) (by rwa ← line_unique_of_pts cd cM dM cP (by rwa ← de at eP) at bP),
  have ae : a ≠ e := λ ae, (S3 cdL) (by rwa ← (line_unique_of_pts ab aL bL (by rwa ← ae at eP) bP) at cP),
  have cO := λ cO, OP (line_unique_of_pts ce cO eO cP eP),
  have bO := λ bO, OP (line_unique_of_pts be bO eO bP eP),
  have dP := λ dP, OP (line_unique_of_pts de dO eO dP eP),
  have aP := λ aP, OP (line_unique_of_pts ae aO eO aP eP),
  have daP := T1 cK cP cM aK bP dM (T2 aL aO aK bL dO cK (S2 cdL) bcO cO ab.symm) abM,
  have Bbec := Pa4 OP (Leasy bL (S3 cdL)) bP eP cP eO be ce bcO,
  have Bdea := Pa4 OP.symm (Leasy dM (S3 abM)) dO eO aO eP de ae (difsym daP),
  refine ⟨e, O, P, aO, dO, bP, cP, eO, eP, Bbec, Bdea, cO, bO, dP, aP⟩,
end

theorem quadarea {a b c d : point} {L M N : line} (ab : a ≠ b) (cd : c ≠ d) (aL : online a L)
  (bL : online b L) (cM : online c M) (dM : online d M) (bN : online b N) (dN : online d N)
  (abM : sameside a b M) (cdL : sameside c d L) (acN : sameside a c N) :
  area d b a + area d c a = area b d c + area b a c :=
begin
  rcases quadiag ab cd aL bL cM dM bN dN abM cdL acN with
    ⟨e, O, P, aO, dO, bP, cP, eO, eP, Bbec, Bdea, cO, bO, dP, aP⟩,
  linarith [DA2mpmod dO aO eO cO Bdea, DA2mpmod dO aO eO bO Bdea, DA2mpmod bP cP eP aP Bbec,
    DA2mpmod bP cP eP dP Bbec, M8 a e c, M8 c a e, M8 b e d, M8 d b e],
end

theorem quadarea1 {a b c d : point} {L M N : line} (ab : a ≠ b) (cd : c ≠ d) (aL : online a L)
  (bL : online b L) (cM : online c M) (dM : online d M) (bN : online b N) (dN : online d N)
  (abM : sameside a b M) (cdL : sameside c d L) (acN : ¬sameside a c N) :
  area b a d + area b c d = area a d c + area a b c :=
  --***** redundant?
begin
  rcases line_of_ne (Leasy aL (S3 (S2 cdL))) with ⟨O, aO, dO⟩,
  rcases line_of_ne (Leasy cM (S3 (S2 abM))) with ⟨P, cP, bP⟩,
  rcases line_of_ne (Leasy aL (S3 cdL)) with ⟨K, aK, cK⟩,
  have NK : N ≠ K := λ NK, (S3 (S2 cdL) (by rwa ←(line_unique_of_pts ab aL bL (by rwa NK.symm at aK) bN) at dN)),
  rcases pt_of_line_line_inter (Int1 acN aK cK) with ⟨e, eN, eK⟩,
  have be : b ≠ e := λ be, (S3 cdL) (by rwa ←(line_unique_of_pts ab aL bL aK (by rwa ← be at eK)) at cK),
  have ce : c ≠ e := λ ce, (S3 (S2 abM)) (by rwa line_unique_of_pts cd cM dM (by rwa ← ce at eN) dN),
  have de : d ≠ e := λ de, (S3 abM) (by rwa ← line_unique_of_pts cd.symm dM cM (by rwa ← de at eK) cK at aK),
  have ae : a ≠ e := λ ae, (S3 (S2 cdL)) (by rwa ←(line_unique_of_pts ab aL bL (by rwa ←  ae at eN) bN) at dN),
  have cN := λ cN, NK (line_unique_of_pts ce cN eN cK eK),
  have bK := λ bK, NK (line_unique_of_pts be bN eN bK eK),
  have dK := λ dK, NK (line_unique_of_pts de dN eN dK eK),
  have aN := λ aN, NK (line_unique_of_pts ae aN eN aK eK),
  have bdK := T1 aL aK aO bL cK dO cdL (S2 (T2 dM dN dO cM bN aO (S2 abM) (difsym acN) aN cd)),
  have Baec := Pa4 NK (Leasy aL (S3 cdL)) aK eK cK eN ae ce acN,
  have Bbed := Pa4 NK.symm (Leasy bL (S3 (S2 cdL))) bN eN dN eK be de bdK,
  linarith [DA2mpmod bN dN eN aN Bbed, DA2mpmod bN dN eN cN Bbed, DA2mpmod aK cK eK bK Baec,
    DA2mpmod aK cK eK dK Baec, M8 b e a, M8 a b e, M8 c e d, M8 d c e],
end

theorem quadext {a b c d e f : point} {L M N : line} (aL : online a L) (cL : online c L)
  (dM : online d M) (fM : online f M) (cN : online c N) (fN : online f N) (Babc : B a b c)
  (Bdef : B d e f) (acM : sameside a c M) (dfL : sameside d f L) (adN : sameside a d N) :
  area a b e + area d e a + area e b c + area e f c = area d a f + area f c a :=
begin
  rcases quadiag (B1 Babc).2.2.1 (B1 Bdef).2.2.2.1 aL cL (B3 Bdef dM fM) fM cN fN acM
    (S4 (Pa1 Bdef dfL) dfL) (S2 (S4 (S2 (Pa2 (B1 Bdef).1 fN (λ eN, (S3 (S2 acM))
    (by rwa (line_unique_of_pts (B1 Bdef).2.2.2.1 eN fN (B3 Bdef dM fM) fM) at cN)))) (S2 adN))) with
    ⟨h, O, P, aO, fO, cP, eP, hO, hP, Bche, Bfha, eO, cO, fP, aP⟩,
  linarith [DA2mpmod aL cL (B3 Babc aL cL) (S3 (S2 (Pa1 Bdef dfL))) Babc, DA2mpmod eP cP
    (B3 Bche cP eP) aP (B1 Bche).1, DA2mpmod eP cP (B3 Bche cP eP) fP (B1 Bche).1,
    DA2mpmod fO aO (B3 Bfha fO aO) cO Bfha, DA2mpmod fO aO (B3 Bfha fO aO) eO Bfha,
    DA2mpmod dM fM (B3 Bdef dM fM) (S3 acM) Bdef, M8 e a c, M8 e c a, M8 f e a, M8 a f e,
    M8 f h e, M8 e f h, M8 c h a, M8 a c h],
end

def square (a b d e : point) (L M N O : line) : Prop := dist a b = dist d e ∧ dist a b = dist a d ∧
  dist a b = dist b e ∧ angle d a b = rightangle ∧ angle a b e = rightangle ∧
  angle a d e = rightangle ∧ angle d e b = rightangle ∧ para a d b e M O ∧ para a b d e L N

-------------------------------------------------- API --------------------------------------------

lemma makeeqtriaux {a b c : point} (hab : a ≠ b) (h1 : dist a b = dist a c)
  (h2 : dist b c = dist b a) : b ≠ c ∧ c ≠ a := ⟨λ bc, hab (M1.mp (by linarith [M1.mpr bc])).symm,
  λ ca, hab (M1.mp (by linarith [M1.mpr ca.symm]))⟩

theorem makeeqtri {a b : point} (hab : a ≠ b) : ∃ (c : point), iseqtri a b c := --Euclid 1.1
begin
  rcases circle_of_ne hab with ⟨α, acen, bcirc⟩,
  rcases circle_of_ne (ne.symm hab) with ⟨β, bcen, acirc⟩,
  rcases pts_of_circle_circle_inter (Int5 (inside_circle_of_center acen) bcirc (inside_circle_of_center bcen) acirc) with ⟨c, -, cona, conb, -, -, -⟩,
  have abeqac := (DS3 acen bcirc).2 cona,
  have bceqba := (DS3 bcen conb).mpr acirc,
  have caeqcb : dist c a = dist c b :=
    flip1 ((rfl.congr (eq.symm (flipboth bceqba))).mp (eq.symm abeqac)),
  refine ⟨c, abeqac, bceqba, caeqcb, hab, makeeqtriaux hab abeqac bceqba⟩,
end

theorem makeeqtri1 {a b : point} (hab : a ≠ b) : ∃ (c d : point), iseqtri a b c ∧ iseqtri a b d ∧
  c ≠ d := --Euclid 1.1
begin
  rcases circle_of_ne hab with ⟨α, acen, bcirc⟩,
  rcases circle_of_ne (ne.symm hab) with ⟨β, bcen, acirc⟩,
  rcases pts_of_circle_circle_inter (Int5 (inside_circle_of_center acen) bcirc (inside_circle_of_center bcen) acirc) with ⟨c, d, cona, conb, dona, donb, cd⟩,
  have abeqac := (DS3 acen bcirc).2 cona,
  have abeqad := (DS3 acen bcirc).2 dona,
  have bceqba := (DS3 bcen conb).mpr acirc,
  have bdeqba := (DS3 bcen donb).mpr acirc,
  have caeqcb := flip1 ((rfl.congr (eq.symm (flipboth bceqba))).mp (eq.symm abeqac)),
  have daeqdb := flip1 ((rfl.congr (eq.symm (flipboth bdeqba))).mp (eq.symm abeqad)),
  refine ⟨c, d, ⟨abeqac, bceqba, caeqcb, hab, makeeqtriaux hab abeqac bceqba⟩,
    ⟨abeqad, bdeqba, daeqdb, hab, makeeqtriaux hab abeqad bdeqba⟩, cd⟩,
end

theorem makeeqtri2 {a b : point} (hab : a ≠ b) : ∃ (c d : point), ∃ (L : line), iseqtri a b c ∧
  iseqtri a b d ∧ online a L ∧ online b L ∧ ¬sameside c d L ∧ c ≠ d := --Euclid 1.1
begin
  rcases line_of_ne hab with ⟨L, aL, bL⟩,
  rcases circle_of_ne hab with ⟨α, acen, bcirc⟩,
  rcases circle_of_ne (ne.symm hab) with ⟨β, bcen, acirc⟩,
  rcases pts_of_circle_circle_inter (Int5 (inside_circle_of_center acen) bcirc (inside_circle_of_center bcen) acirc) with ⟨c, d, cona, conb, dona, donb, cd⟩,
  have nss := C4 (difcendifcirc acen bcen hab) cd (Int5 (inside_circle_of_center acen) bcirc (inside_circle_of_center bcen) acirc) cona conb
    dona donb acen bcen aL bL,
  have abeqac := (DS3 acen bcirc).2 cona,
  have abeqad := (DS3 acen bcirc).2 dona,
  have bceqba := (DS3 bcen conb).mpr acirc,
  have bdeqba := (DS3 bcen donb).mpr acirc,
  have caeqcb := flip1 ((rfl.congr (eq.symm (flipboth bceqba))).mp (eq.symm abeqac)),
  have daeqdb := flip1 ((rfl.congr (eq.symm (flipboth bdeqba))).mp (eq.symm abeqad)),
  refine ⟨c, d, L, ⟨abeqac, bceqba, caeqcb, hab, makeeqtriaux hab abeqac bceqba⟩,
    ⟨abeqad, bdeqba, daeqdb, hab, makeeqtriaux hab abeqad bdeqba⟩, aL, bL, nss, cd⟩,
end

theorem makeeqtri3 {a b : point} (hab : a ≠ b) : ∃ (c d : point), ∃ (L : line), iseqtri a b c ∧
  iseqtri a b d ∧ online a L ∧ online b L ∧ diffside c d L := --Euclid 1.1
begin
  rcases line_of_ne hab with ⟨L, aL, bL⟩,
  rcases circle_of_ne hab with ⟨α, acen, bcirc⟩,
  rcases circle_of_ne (ne.symm hab) with ⟨β, bcen, acirc⟩,
  rcases pts_of_circle_circle_inter (Int5 (inside_circle_of_center acen) bcirc (inside_circle_of_center bcen) acirc) with ⟨c, d, cona, conb, dona, donb, cd⟩,
  have nss := C4 (difcendifcirc acen bcen hab) cd (Int5 (inside_circle_of_center acen) bcirc (inside_circle_of_center bcen) acirc) cona conb
    dona donb acen bcen aL bL,
  have abeqac := (DS3 acen bcirc).2 cona,
  have abeqad := (DS3 acen bcirc).2 dona,
  have bceqba := (DS3 bcen conb).mpr acirc,
  have bdeqba := (DS3 bcen donb).mpr acirc,
  have caeqcb := flip1 ((rfl.congr (eq.symm (flipboth bceqba))).mp (eq.symm abeqac)),
  have daeqdb := flip1 ((rfl.congr (eq.symm (flipboth bdeqba))).mp (eq.symm abeqad)),
  have key : diffside c d L,
  { split, intro cL,
    have := nonzerolen hab,
    have := nonzerolen hab.symm,
    have this1 : a ≠ c,
    { intro ac,
      have := M1.2 ac,
      linarith, },
    have : b ≠ c,
    { intro bc,
      have := M1.2 bc,
      linarith, },
    cases B6 aL bL cL hab this1 this,
    { have := DS1 h,
      have := flip2 bceqba,
      linarith, },
    cases h,
    { have := DS1 h,
      have := flip1 abeqac,
      linarith, },
    have := DS1 h,
    linarith [flipboth bceqba],
    --same for d
    split, intro dL,
    have := nonzerolen hab,
    have := nonzerolen hab.symm,
    have this1 : a ≠ d,
    { intro ad,
      have := M1.2 ad,
      linarith, },
    have : b ≠ d,
    { intro bd,
      have := M1.2 bd,
      linarith, },
    cases B6 aL bL dL hab this1 this,
    { have := DS1 h,
      have := flip2 bceqba,
      linarith, },
    cases h,
    { have := DS1 h,
      have := flip1 abeqac,
      linarith, },
    have := DS1 h,
    linarith [flipboth bdeqba],
    exact nss, },
  refine ⟨c, d, L, ⟨abeqac, bceqba, caeqcb, hab, makeeqtriaux hab abeqac bceqba⟩,
    ⟨abeqad, bdeqba, daeqdb, hab, makeeqtriaux hab abeqad bdeqba⟩, aL, bL, key⟩,
end

theorem ex {a b c : point} {L : line} (hbc : b ≠ c) (aL : online a L) : ∃ (d : point),
  online d L ∧ dist a d = dist b c := --Euclid 1.2,3 (generalizations and corrollaries)
begin
    by_cases hab : a = b,
    { rcases circle_of_ne hbc with ⟨α, bcen, ccirc⟩,
      rcases pts_of_line_circle_inter (Int3 (inside_circle_of_center bcen) (by rwa hab at aL)) with
        ⟨d, -, dL, -, dalpha, -, -⟩,
      refine ⟨d, dL, by rwa hab; linarith [(DS3 bcen dalpha).mpr ccirc]⟩, },
    rcases makeeqtri hab with ⟨d, len1, len2, len3, hab, hbd, hda⟩,
    rcases line_of_ne hda with ⟨M, dM, aM⟩,
    rcases line_of_ne hbd.symm with ⟨N, dN, bN⟩,
    rcases circle_of_ne hbc with ⟨α, bcen, ccirc⟩,
    rcases pt_oncircle_of_inside_ne (inside_circle_of_center bcen) hbd.symm with ⟨g, gcirc, Bgbd⟩,
    have hyp : dist d g = dist b a + dist b g := by linarith [DS1 (B1 Bgbd).1, M2 d b],
    have hyp2 : dist d a < dist d g,
    { by_contra  h, -- by_contra and then push_neg?
      exact (ne.symm (B1 Bgbd).2.1) (M1.mp (by linarith [M5 b g, flipboth len3, M2 a d])), },
    rcases circle_of_ne (ne.symm(B1 Bgbd).2.2.1) with ⟨β, dcen, gcirc2⟩,
    rcases pt_oncircle_of_inside_ne ((DS4 dcen gcirc2).1 hyp2) hda with ⟨f, fcirc, Bfad⟩,
    have key : dist b c = dist f a := by linarith [DS1 Bfad, (DS3 dcen fcirc).2 gcirc2, M2 d f,
      flipboth len3, (DS3 bcen ccirc).2 gcirc],
    rcases circle_of_ne (ne.symm (B1 Bfad).2.1) with ⟨γ, acen2, fcirc3⟩,
    rcases pts_of_line_circle_inter (Int3 (inside_circle_of_center acen2) aL) with ⟨h, -, hL, -, hcirc, -, -⟩,
    refine ⟨h, hL, by linarith [M2 a f, (DS3 acen2 fcirc3).2 hcirc]⟩,
end

theorem excor {a b c : point} (hab : a ≠ b) (hbc : b ≠ c) :
  ∃ (p : point), B a b p ∧ dist b p = dist c b :=
begin
  rcases line_of_ne hab with ⟨L, aL, bL⟩,
  rcases circle_of_ne hbc with ⟨α, bcirc, ccirc⟩,
  rcases pt_oncircle_of_inside_ne (inside_circle_of_center bcirc) hab with ⟨p, pcirc, Bpba⟩,
  refine ⟨p, (B1 Bpba).1, by rwa [M2 c b, ((DS3 bcirc pcirc).2 ccirc)]⟩,
end

theorem excor2 {a b c d : point} (hab : a ≠ b) (hcd : c ≠ d) :
  ∃ (p : point), B a b p ∧ dist b p = dist c d :=
begin
  rcases line_of_ne hab with ⟨L, aL, bL⟩,
  rcases ex hcd bL with ⟨p1, p1L, len⟩,
  by_cases b = p1, { exfalso, refine hcd (M1.mp (eq.trans (M1.mpr h).symm len).symm), },
  by_cases hap1 : a = p1,
  { rcases circle_of_ne (ne.symm hab) with ⟨α, bcen, acirc⟩,
    rcases pts_of_line_circle_inter (Int3 (inside_circle_of_center bcen) bL) with ⟨e, f, eL, fL, ecirc, fcirc, hef⟩,
    by_cases hyp : a = e,
    { use f, split,
      { -- refine later
        exact C1 bL aL fL (inside_circle_of_center bcen) acirc fcirc (λ haf, hef (eq.trans hyp.symm haf)), },--again
      rw ← hap1 at len,
      linarith [(DS3 bcen acirc).2 fcirc], },
    refine ⟨e, C1 bL aL eL (inside_circle_of_center bcen) acirc ecirc hyp, _⟩,
    rw ← ((DS3 bcen acirc).2 ecirc),
    rwa ← hap1 at len, }, --again
    rcases excor hab h with ⟨p, hypp⟩,
  refine ⟨p, hypp.1, by linarith [hypp.2, flip1 len]⟩,
end

theorem excor3 {a b c d : point} (cd : c ≠ d) (big : dist c d < dist a b) :
  ∃ (p : point), B a p b ∧ dist a p = dist c d := --can use for I.11
begin
  rcases line_of_ne (nonzerolenconv (by linarith [M5 c d]) : a ≠ b) with ⟨L, aL, bL⟩,
  rcases pt_extension_of_ne (nonzerolenconv (by linarith [M5 c d]) : a ≠ b).symm with ⟨q, Bbaq⟩,
  by_cases ad : a = d,
  { by_cases ac : a = c, { exfalso, rw [← ac, ← ad] at cd, exact cd rfl, },
    rcases circle_of_ne ac with ⟨α, acen, ccirc⟩,
    rw ← ad at big,
    have noin := mt (DS4 acen ccirc).mpr (by linarith [M2 a c] : ¬(dist a b < dist a c)),
    have := mt (DS3 acen ccirc).mpr ((by linarith [M2 a c]) : dist a c ≠ dist a b),
    rcases pt_oncircle_of_inside_outside (inside_circle_of_center acen) noin this with ⟨p, pcirc, Bapb⟩,
    have := (DS3 acen ccirc).mpr pcirc,
    rw ← ad, --optimize?
    refine ⟨p, Bapb, by linarith [M2 a c]⟩, },
  rcases excor (B1 Bbaq).2.2.2.1.symm ad with ⟨p, Bqap, len⟩,
  by_cases a = c,
  have bp : b ≠ p, { intro bp, rw [bp, h.symm] at big, linarith [flip2 len], },
  rw [h.symm, (flip2 len).symm] at big,
  cases (B6 aL bL (B2 Bqap (B2 Bbaq bL aL) aL) (B1 Bbaq).2.1.symm (B1 Bqap).2.2.2.1 bp),
  --- **** BAD don't use auto-generated `h_1`
  linarith [DS1 h_1, nonzerolen (B1 h_1).2.2.2.1],
  cases h_1,
  exfalso,
  exact (B7 Bqap (B1 Bbaq).1) (B1 h_1).1, --exfalso + exact?
  refine ⟨p, h_1, by rwa [flip2, h.symm]⟩,
  rcases excor2 (B1 Bbaq).2.2.2.1.symm cd with ⟨p, Bqap, len⟩, --same as above but with a ≠ c
  have bp : b ≠ p, { intro bp, rw bp at big, linarith, }, --again
  cases B6 aL bL (B2 Bqap (B2 Bbaq bL aL) aL) (B1 Bbaq).2.1.symm (B1 Bqap).2.2.2.1 bp,
  linarith [DS1 h_1, nonzerolen (B1 h_1).2.2.2.1], cases h_1, exfalso,
  exact (B7 Bqap (B1 Bbaq).1) (B1 h_1).1,
  refine ⟨p, h_1, len⟩,
end

--- Euclid I.5 (part 1)
theorem isoangle {a b c : point} (ab : a ≠ b) (bc : b ≠ c) (labac : dist a b = dist a c) :
  angle a b c = angle a c b  := (sas labac labac.symm (M3 ab.symm bc)).2.2.symm

-- Euclid I.5 (part 2)
theorem isoangleext {a b c d e : point} {L : line} (bc : b ≠ c) (aL : online a L)
  (bL : online b L) (cL : ¬online c L) (Babd : B a b d) (Bace : B a c e)
  (labac : dist a b = dist a c) (ladae : dist a d = dist a e) : angle c b d = angle b c e :=
begin
  have key1 : angle d a c = angle e a b := by linarith [A4mod1 (B1 Babd).2.1 Bace,
    (aflip1 (B1 Babd).2.1.symm bc) (A4mod1 (B1 Bace).2.1 Babd)],
  rcases line_of_ne (B1 Bace).2.2.1 with ⟨M, aM, eM⟩,
  have bM : ¬online b M, { intro bM, rw (line_unique_of_pts (B1 Babd).2.1 aL bL aM bM) at cL,
    exact cL (B3 Bace aM eM), },--anything better here? (intro rw exact)
  have key2 := aflipboth (B1 Babd).2.2.1.symm (Beasy2 bc.symm aM (B3 Bace aM eM) bM Bace
    Babd).symm (B1 Bace).2.2.1.symm (Beasy2 bc aL bL cL Babd Bace).symm key1,
  exact (sss ((sas labac labac.symm (M3 (B1 Babd).2.1.symm bc)).1) (sas labac.symm ladae key2).1
    (by linarith [DS1 Babd, DS1 Bace])).2.1,
end

theorem isosidelem {a b c : point} {L : line} (ab : a ≠ b) (bc : b ≠ c) (ca : c ≠ a)
  (aL : online a L) (bL : online b L) (ang : angle a b c = angle a c b) (Bbac : ¬B b a c) :
  ¬online c L :=
begin
  intro cL,
  cases B6 aL bL cL ab ca.symm bc with hyp,
  { have := not_imp_not.2 (A1 ab.symm bc bL aL).2,
    push_neg at this, -- any way to push_neg without extra line?
    exact (this (iff_of_true cL hyp).mp) (by linarith [((A1 ca bc.symm cL aL).1
      ⟨bL, Beasy4 (B1 (B1 hyp).1).2.2.2.2⟩)]), },
  cases h,
  exact Bbac h,
  have := not_imp_not.2 (A1 ca bc.symm cL aL).2, push_neg at this,
  exact (this (iff_of_true bL h).mp) (by linarith [(A1 ab.symm bc bL aL).1
    ⟨cL, Beasy4 (B1 (B1 h).1).2.2.2.2⟩]),
end

--Euclid I.6
theorem isoside {a b c : point} (Bbac : ¬B b a c) (ab : a ≠ b) (bc : b ≠ c) (ca : c ≠ a)
  (ang : angle a b c = angle a c b) : dist a b = dist a c :=
begin
  wlog h : (dist a c ≤ dist a b) using [b c, c b],
  { exact le_total (dist a c) (dist a b), },
  by_cases h_1 : dist a c = dist a b, exact h_1.symm,
  rcases excor3 ca.symm (by linarith [(ne.le_iff_lt h_1).mp h, M2 a b] : dist a c < dist b a) with
    ⟨d, Bbda, bdac⟩,
  have dbcacb : angle a c b = angle d b c := by linarith [A4mod1 bc Bbda],
  have eq := sas (flip2 bdac).symm (M2 c b) dbcacb,
  rcases Beasy3 Bbda with ⟨L, bL, dL, aL, bd, da, ab⟩,
  have asplit := (DA2 ab.symm da.symm bd.symm bL aL dL (isosidelem ab bc ca aL bL ang Bbac)).1
    Bbda,
  have key : area b c a + area d a c = area b c a :=
    by linarith [M9 (flip2 bdac).symm eq.1 (M2 b c) eq.2.1 dbcacb eq.2.2,
    (M8 c a b).1, (M8 d a c).1],
  exfalso,
  exact (isosidelem ab bc ca aL bL ang Bbac) ((DA1 dL aL da).1 (by linarith)),
  exact (this (Beasy4 Bbac) ca.symm bc.symm ab.symm ang.symm).symm,
end

--Euclid I.10
theorem bisline {a b : point} (ab : a ≠ b) : ∃ (d : point), B a d b ∧ dist a d = dist d b :=
begin
  rcases makeeqtri2 ab with ⟨c, e, L, ⟨labac, lbcba, lcacb, ab, bc, ca⟩,
    ⟨labae, lbeba, lcaeb, ab, be, ea⟩, aL, bL, nss, ce⟩,
  rcases line_of_ne ce with ⟨M, cM, eM⟩,
  rcases pt_of_line_line_inter (Int1 nss cM eM) with ⟨d, dL, dM⟩,
  have cd : c ≠ d,
  { intro cd,
    rw ← cd at dL,
    cases B6 aL bL dL ab ca.symm bc,
    linarith [DS1 h, flipboth lcacb, flip2 lbcba, nonzerolen ab],
    cases h,
    linarith [DS1 h, nonzerolen ca.symm],
    linarith [DS1 h, nonzerolen bc.symm], },
  have ed : e ≠ d,
  { intro ed,
    rw ← ed at dL,
    cases B6 aL bL dL ab ea.symm be,
    linarith [DS1 h, flipboth lcacb, flip2 lbcba, nonzerolen ab],
    cases h,
    linarith [DS1 h, nonzerolen ca.symm],
    linarith [DS1 h, nonzerolen be.symm], },
  have LM : L ≠ M,
  { intro LM,
    rw ← LM at cM,
    cases B6 aL bL cM ab ca.symm bc,
    linarith [flipboth lcacb, flip2 lbcba, nonzerolen ab, DS1 h],
    cases h,
    linarith [DS1 h, nonzerolen ca.symm],
    linarith [DS1 h, nonzerolen bc.symm], }, --proof
  have extang1 := (A4mod1 ca (Pa4 LM ce cM dM eM dL cd ed nss)),
  have extang2 := A4mod1 bc.symm (Pa4 LM ce cM dM eM dL cd ed nss),
  have bis := aflipboth ca.symm ea.symm bc be (sss (by linarith : dist c a = dist c b)
    (by linarith [M2 a e, M2 b e] : dist a e = dist b e) rfl).2.1,
  have adbsplit := flip1 (sas (rfl : dist c d = dist c d) (by linarith : dist c a = dist c b)
    (by linarith)).1,
  use d,
  split,
  { cases B6 aL bL dL ab (Leneasy ab adbsplit) (Leneasy ab.symm (flipboth adbsplit).symm) with
      Babd Bet,
    { exfalso, linarith [DS1 Babd, M2 b d, nonzerolen ab], },
    { cases Bet with Bbad,
      { exfalso, linarith [DS1 Bbad, M2 b d, nonzerolen ab.symm], },
      exact Bet, }, },
  exact adbsplit,
end

theorem bisangiso {a b c : point} {L M : line} (ab : a ≠ b) (ac : a ≠ c) (LM : L ≠ M)
  (aL : online a L) (bL : online b L) (aM : online a M) (cM : online c M)
  (abeqac : dist a b = dist a c) : ∃ (d : point), angle b a d = angle c a d ∧ sameside d b M ∧
  sameside d c L ∧ B b d c :=
begin
  rcases bisline (Leasy2 ab ac LM aL aM bL cM) with ⟨d, Bbdc, len⟩,
  rcases Beasy3 Bbdc with ⟨N, bN, dN, cN, bd, dc, cb⟩,
  have dM : ¬online d M := λ dM, LM (line_unique_of_pts ab aL bL aM (by rwa (line_unique_of_pts dc.symm cN dN cM dM) at bN)),
  have dL : ¬online d L := λ dL, LM (line_unique_of_pts ac aL (by rwa (line_unique_of_pts bd bN dN bL dL) at cN) aM cM),
  refine ⟨d, (sss abeqac (flip2 len) rfl).2.1, Pa2 (B1 Bbdc).1 cM dM, Pa2 Bbdc bL dL, Bbdc⟩,
end

--Euclid I.9
theorem bisang {a b c : point} {L M : line} (ab : a ≠ b) (ac : a ≠ c) (LM : L ≠ M)
  (aL : online a L) (bL : online b L) (aM : online a M) (cM : online c M) :
  ∃ (d : point), angle b a d = angle c a d ∧ sameside d b M ∧ sameside d c L :=
begin
  rcases excor2 ab ac with ⟨d, Babd, bdac⟩,
  rcases excor2 ac ab with ⟨e, Bace, ceab⟩,
  have len : dist a d = dist a e := by linarith [DS1 Babd, DS1 Bace],
  have key := bisangiso (B1 Babd).2.2.1 (B1 Bace).2.2.1 LM aL (B2 Babd aL bL) aM
    (B2 Bace aM cM) len,
  rcases key with ⟨f, ang, ss1, ss2, Bdfe⟩,
  rcases Beasy3 Bdfe with ⟨N, dN, fN, eN, df, fe, ed⟩,
  have af : a ≠ f := λ af, LM ((rfl.congr (eq.symm (line_unique_of_pts (B1 Babd).2.2.1 aL (B2 Babd aL bL)
    (by rwa af.symm at fN) dN))).mp (line_unique_of_pts (B1 Bace).2.2.1 aM (B2 Bace aM cM)
    (by rwa af.symm at fN) eN)).symm,
  refine ⟨f, by linarith [A4mod1 af Babd, A4mod1 af Bace], S4 (S2 ss1) (S2 (Pa2 Babd aM
    (λ bM, LM (line_unique_of_pts ab aL bL aM bM)))), S4 (S2 ss2) (S2 (Pa2 Bace aL (λ cL,
    LM (line_unique_of_pts ac aL cL aM cM))))⟩,
end

--Euclid I.11
theorem perpline {a b c : point} (Babc : B a b c) :
  ∃ (d : point), angle a b d = rightangle ∧ angle c b d = rightangle :=
begin
  rcases excor2 (B1 Babc).2.1.symm (B1 Babc).2.2.2.1 with ⟨e, Bbae, len1⟩,
  rcases excor2 (B1 Babc).2.2.2.1 (B1 Babc).2.1.symm with ⟨f, Bbcf, len2⟩,
  rcases makeeqtri3 ((B1 (B5 (B1 Bbae).1 (B5 Babc Bbcf))).2.2.1) with
    ⟨d, d1, L, ⟨len1, len2, len3, nq⟩, other, eL, fL, dL, d1L, nss⟩,
  have bd := (Leasy (B2 (B1 Bbae).1 eL (B3 (B5 (B1 Bbae).1 (B5 Babc Bbcf)) eL fL)) dL),
  have := aflip2 (B1 Bbcf).2.2.1.symm nq.2.1 (A4mod1 bd Bbcf),
  have := aflip2 (B1 Bbae).2.2.1.symm nq.2.2.symm (A4mod1 bd Bbae),
  have := aflip1 (B1 Babc).2.2.2.1.symm
    (Leasy (B3 (B5 (B1 Bbcf).1 (B5 (B1 Babc).1 Bbae)) fL eL) dL) (A4mod1 bd Bbcf),
  have len4 : dist e b = dist f b := by apply flipboth; linarith [DS1 Bbcf, DS1 Bbae], --proof
  have key := (A3 (B3 (B5 (B1 Bbae).1 (B5 Babc Bbcf)) eL fL) (B3 (B5 (B1 Bbcf).1 (B5 (B1 Babc).1
    Bbae)) fL eL) Babc dL).1 (by linarith [(A4mod1 bd Bbcf), (sss len3 len4 rfl).2.2]),
  refine ⟨d, key, by linarith [(sss len3 len4 rfl).2.2]⟩,
end

--Euclid I.11
theorem perplinecor {a b c p : point} {O : line} (aO : online a O) (cO : online c O)
  (pO : ¬online p O) (Babc : B a b c) :
  ∃ (d : point), angle a b d = rightangle ∧ angle c b d = rightangle ∧ sameside d p O :=
begin
  rcases excor2 (B1 Babc).2.1.symm (B1 Babc).2.2.2.1 with ⟨e, Bbae, len1⟩,
  rcases excor2 (B1 Babc).2.2.2.1 (B1 Babc).2.1.symm with ⟨f, Bbcf, len2⟩,
  rcases makeeqtri3 ((B1 (B5 (B1 Bbae).1 (B5 Babc Bbcf))).2.2.1) with ⟨d, d1, L,
    ⟨len1, len2, len3, nq⟩, ⟨len4, len5, len6, nq1⟩, eL, fL, ds⟩,
  have bd := (Leasy (B2 (B1 Bbae).1 eL (B3 (B5 (B1 Bbae).1 (B5 Babc Bbcf)) eL fL)) ds.1),
  have bd1 := (Leasy (B2 (B1 Bbae).1 eL (B3 (B5 (B1 Bbae).1 (B5 Babc Bbcf)) eL fL)) ds.2.1),
  have := aflip2 (B1 Bbcf).2.2.1.symm nq.2.1 (A4mod1 bd Bbcf),
  have := aflip2 (B1 Bbae).2.2.1.symm nq.2.2.symm (A4mod1 bd Bbae),
  have := aflip1 (B1 Babc).2.2.2.1.symm
    (Leasy (B3 (B5 (B1 Bbcf).1 (B5 (B1 Babc).1 Bbae)) fL eL) ds.1) (A4mod1 bd Bbcf),
  have := aflip2 (B1 Bbcf).2.2.1.symm nq1.2.1 (A4mod1 bd1 Bbcf),
  have := aflip2 (B1 Bbae).2.2.1.symm nq1.2.2.symm (A4mod1 bd1 Bbae),
  have := aflip1 (B1 Babc).2.2.2.1.symm
    (Leasy (B3 (B5 (B1 Bbcf).1 (B5 (B1 Babc).1 Bbae)) fL eL) ds.2.1) (A4mod1 bd1 Bbcf),
  have len4 : dist e b = dist f b := by apply flipboth; linarith [DS1 Bbcf, DS1 Bbae], --proof
  by_cases sameside d p O,
  { have key := (A3 (B3 (B5 (B1 Bbae).1 (B5 Babc Bbcf)) eL fL) (B3 (B5 (B1 Bbcf).1 (B5 (B1 Babc).1
      Bbae)) fL eL) Babc ds.1).1 (by linarith [A4mod1 bd Bbcf, (sss len3 len4 rfl).2.2]),
    refine ⟨d, key, by linarith [(sss len3 len4 rfl).2.2], h⟩, },
  have OL := line_unique_of_pts (B1 Babc).2.2.1 aO cO (B3 (B5 (B1 Bbae).1 (B5 Babc Bbcf)) eL fL)
    (B3 (B5 (B1 Bbcf).1 (B5 (B1 Babc).1 Bbae)) fL eL),
  rw OL at h,
  rw OL at pO,
  rw OL, --anything better here? *** YES
  have key := (A3 (B3 (B5 (B1 Bbae).1 (B5 Babc Bbcf)) eL fL) (B3 (B5 (B1 Bbcf).1 (B5 (B1 Babc).1
    Bbae)) fL eL) Babc ds.2.1).1 (by linarith [A4mod1 bd1 Bbcf, (sss len6 len4 rfl).2.2]),
  refine ⟨d1, key, by linarith [(sss len6 len4 rfl).2.2], difdifsame ds ⟨ds.1, pO, h⟩⟩,
end

--Euclid I.12
theorem perppointnon { c : point} {O : line} (cO : ¬online c O) : ∃ (e h g : point), online e O ∧
  online h O ∧ online g O ∧ B e h g ∧ angle c h e = rightangle ∧ angle c h g = rightangle :=
begin
  rcases opp_side_of_not_online cO with ⟨d, dO, dcO⟩,
  rcases circle_of_ne (λ cd, (by rwa cd at dcO : ¬sameside d d O) (S1 dO) : c ≠ d) with ⟨α, ccen, dcirc⟩,
  rcases pts_of_line_circle_inter (Int2 (by right; exact dcirc) (by left; exact (inside_circle_of_center ccen)) dcO) with
    ⟨e, g, eO, gO, ecirc, gcirc, eg⟩,
  rcases bisline eg with ⟨h, Behg, len⟩,
  have := (sss ((DS3 ccen ecirc).mpr gcirc) (flip2 len) rfl).2.2,
  have := M3 (Leasy (B3 Behg eO gO) cO).symm (Leasy eO cO).symm,
  have := (A3 eO gO Behg cO).mp (by linarith),
  refine ⟨e, h, g, eO, (B3 Behg eO gO), gO, Behg, by linarith, by linarith⟩,
end

--Euclid I.13
theorem flatsumright {a b c d : point} {L : line} (dL : online d L) (cL : online c L)
  (aL : ¬online a L) (Bdbc : B d b c) : angle a b c + angle a b d = 2 * rightangle :=
begin
  have ab := (Leasy (B3 Bdbc dL cL) aL).symm,
  rcases line_of_ne ab with ⟨N, aN, bN⟩,
  by_cases (angle a b c = angle a b d),
  { linarith [(A3 dL cL Bdbc aL).mp ((aflip2 ab ((Leasy dL aL).symm) h).symm),
      (aflip2 ab ((Leasy dL aL).symm) h).symm], },
  rcases perplinecor cL dL aL (B1 Bdbc).1 with ⟨e, a1, a2, eaL⟩,
  have eb := (Leasy (B3 Bdbc dL cL) (S3 eaL)).symm,
  rcases line_of_ne eb with ⟨M, eM, bM⟩,
  have ra : angle e b c = angle e b d := by linarith [M3 (B1 Bdbc).2.2.2.1.symm
    (Leasy cL (S3 eaL)), M3 (B1 Bdbc).2.1 (Leasy dL (S3 eaL))],
  have aM : ¬online a M,
  { intro aM,
    have ae : a ≠ e := λ ae, (by rwa ae at h : (¬(angle e b c = angle e b d))) ra,
    cases B6 aM bM eM (Leasy (B3 Bdbc dL cL) aL).symm ae eb.symm,
    --- *** BAD don't use `h_1`
    { exact (Pa3 h_1 (B3 Bdbc dL cL)) (S2 eaL), },
    cases h_1,
    exact (by rwa [A4mod1 (B1 Bdbc).2.2.2.1 h_1,
      A4mod1 (B1 Bdbc).2.1.symm h_1] at h : (¬(angle e b c = angle e b d))) ra,
    exact (by rwa [←(A4mod1 (B1 Bdbc).2.2.2.1 (B1 h_1).1),
      ←(A4mod1 (B1 Bdbc).2.1.symm (B1 h_1).1)] at h : (¬(angle e b c = angle e b d))) ra, },
  wlog acM : (sameside a c M) using [c d, d c],
  { by_cases h1 : sameside a c M,
    { left, assumption, },
    right,
    have cM : ¬online c M := λ cM, (S3 eaL)
      (by rwa (line_unique_of_pts (B1 Bdbc).2.2.2.1 bM cM (B3 Bdbc dL cL) cL) at eM),
    have dM : ¬online d M := λ dM, (S3 eaL)
      (by rwa (line_unique_of_pts (B1 Bdbc).2.1.symm bM dM (B3 Bdbc dL cL) dL) at eM),
    exact difdifsame ⟨cM, aM, difsym h1⟩ ⟨cM, dM, difsym (Pa3 Bdbc bM)⟩, },
    --end of proof of wlog; not worth it?
  { have splitcbe := (A2 (B3 Bdbc dL cL) cL bM eM (B1 Bdbc).2.2.2.1 eb.symm aM aL (λ LM, (S3 eaL)
      (by rwa ← LM at eM))).mpr ⟨S2 acM, eaL⟩,
    have eNL : ¬online e N ∧ ¬online e L := ⟨(λ eN, (by rwa (line_unique_of_pts eb eM bM eN bN) at aM :
      ¬online a N) aN), (λ eL, (S3 eaL) eL)⟩,
    have deN : sameside d e N,
    { have cN : ¬online c N := λ cN,
        aL (by rwa (line_unique_of_pts (B1 Bdbc).2.2.2.1 bN cN (B3 Bdbc dL cL) cL) at aN),
      have dN : ¬online d N  := λ dN,
        aL (by rwa (line_unique_of_pts (B1 Bdbc).2.1.symm bN dN (B3 Bdbc dL cL) dL) at aN),
      exact S2 (difdifsame ⟨cN, eNL.1, difsym (T1 bM bN (B3 Bdbc dL cL) eM aN cL acM eaL)⟩
        ⟨cN, dN, difsym (Pa3 Bdbc bN)⟩), },
    have splitabd := (A2 bN aN (B3 Bdbc dL cL) dL ab.symm (B1 Bdbc).2.1.symm eNL.2 eNL.1
      (λ NL, aL (by rwa NL at aN))).mpr ⟨S2 eaL, deN⟩,
    have flipcbe := M3 (B1 Bdbc).2.2.2.1.symm (Leasy cL eNL.2),
    have flipabc := M3 ab (Leasy cL aL).symm,
    linarith [(A3 dL cL Bdbc eNL.2).mp (by linarith)], },
  linarith [this cL dL (B1 Bdbc).1 (λ hh, h hh.symm) a2 a1 ra.symm],
end

-- Euclid I.14
theorem rightimpflat {a b c d : point} {N : line} (ab : a ≠ b) (aN : online a N) (bN : online b N)
  (cdN : diffside c d N) (ang : angle a b c + angle a b d = 2 * rightangle) : B c b d :=
begin
  have cd := difneq cdN, --API and degenerate cases
  have bd : b ≠ d := λ bd, cdN.2.1 (by rwa bd at bN),
  rcases excor (Leasy bN cdN.1).symm (Leasy bN cdN.1) with ⟨e, Bcbe, len⟩,
  rcases line_of_ne (Leasy bN cdN.1) with ⟨M, bM, cM⟩,
  have eM := B2 Bcbe cM bM,
  have eN : ¬online e N := λ eN, cdN.1 (B2 (B1 Bcbe).1 eN bN),
  have edN := difdifsame ⟨cdN.1, eN, difsym (Pa3 (B1 Bcbe).1 bN)⟩ cdN,
  rcases line_of_ne bd with ⟨L, bL, dL⟩,
  have LN : L ≠ N := λ LN, cdN.2.1 (by rwa LN at dL),
  by_cases eL : online e L,
  { exact Pa4 LN.symm cd (B2 (B1 Bcbe).1 eL bL) bL dL bN (Leasy bN cdN.1).symm bd.symm cdN.2.2, },
  have dM : ¬online d M := λ dM, eL (by rwa (line_unique_of_pts bd bM dM bL dL) at eM),
  have ae : a ≠ e := λ ae, eN (by rwa ae at aN),
  by_cases ed : e = d, { rwa ed at Bcbe, },
  have ang1 := flatsumright cM eM (λ aM, cdN.1 (by rwa ← (line_unique_of_pts ab aN bN aM bM) at cM)) Bcbe, --beginning of proof
  by_cases eaL : sameside e a L,
  { have split := (A2 bL dL bN aN bd ab.symm eN eL LN).mpr ⟨S2 edN, S2 eaL⟩,
    have dM := ((A1 (B1 Bcbe).2.2.2.1 bd bM eM).mpr (by linarith [M3 ab ae,
      M3 ab (Leasy aN cdN.2.1), M3 bd.symm (ne.symm ed)])).1,
    exact Pa4 ((λ NM, eN (by rwa ←NM at eM)) : N ≠ M) cd cM bM dM bN (B1 Bcbe).2.1
      bd.symm cdN.2.2 },
  have adM := T2 bN bL bM aN dL eM (S2 edN) (difsym eaL) eL ab,
  have split := (A2 bN aN bM eM ab.symm (B1 Bcbe).2.2.2.1 dM (S3 (S2 edN))
    (λ NM, eN (by rwa ← NM at eM))).mpr ⟨adM, edN⟩,
  have dM := ((A1 (B1 Bcbe).2.2.2.1 bd bM eM).mpr (by linarith [M3 ab ae,
    M3 ab (Leasy aN cdN.2.1), M3 bd.symm (ne.symm ed)])).1,
  exact Pa4 (((λ NM, eN (by rwa ←NM at eM)) : N ≠ M)) cd cM bM dM bN (B1 Bcbe).2.1 bd.symm cdN.2.2,
end

--Euclid I.15
theorem vertang {a b c d e : point} {L : line} (cL : online c L) (dL : online d L)
  (aL : ¬online a L) (Bced : B c e d) (Baeb : B a e b) : angle b e c = angle d e a :=
begin
  rcases Beasy3 Baeb with ⟨N, aN, eN, bN, nq⟩,
  have dN : ¬online d N := λ dN,
    ((by rwa (line_unique_of_pts (B1 Bced).2.2.2.1 (B3 Bced cL dL) dL eN dN) at aL) : ¬online a N) aN,
  have bL : ¬online b L := λ bL,
    (by rwa line_unique_of_pts nq.2.1 (B3 Bced cL dL) bL eN bN at aL : ¬online a N) aN,
  have := flatsumright cL dL bL Bced,
  have := flatsumright aN bN dN Baeb,
  linarith [M3 nq.1 (Leasy dL aL).symm, M3 nq.2.1.symm (Leasy bN dN)],
end

--Euclid I.16 (Elliptic geometry fails)
theorem extang {a b c d : point} {L : line} (aL : ¬online a L) (bL : online b L) (dL : online d L)
  (Bbcd : B b c d) : angle b a c < angle a c d :=
begin
  have cL := B3 Bbcd bL dL,
  have ca := Leasy cL aL,
  have ba := Leasy bL aL,
  rcases bisline ca with ⟨e, Bcea, len⟩,
  have be : b ≠ e := λ be, aL (B2 Bcea cL (by rwa be at bL)),
  rcases excor be be.symm with ⟨f, Bbef, len2⟩,
  have cf : c ≠ f := λ cf, aL (B2 Bcea cL (B3 Bbef bL (by rwa cf at cL))),
  have afL := S4 (Pa2 Bcea cL (λ eL, aL ((B2 Bcea) cL eL)))
    (Pa2 Bbef bL (λ eL, aL ((B2 Bcea) cL eL))),
  rcases Beasy3 Bbef with ⟨M, bM, eM, fM, nq⟩,
  have cM : ¬online c M := λ cM,
    ((by rwa ← (line_unique_of_pts (B1 Bbcd).2.1 bM cM bL cL) at aL) : ¬online a M) (B2 Bcea cM eM),
  have ang := vertang bM fM cM Bbef Bcea,
  have ang2 := (sas (flip2 len2) (flip1 len) (by linarith [M3 be ba])).2.2,
  rcases Beasy3 Bcea with ⟨N, cN, eN, aN, nq1⟩,
  have fN : ¬online f N := λ fN,
    aL (by rwa (line_unique_of_pts (B1 Bbcd).2.1 (B2 (B1 Bbef).1 fN eN) cN bL cL) at aN),
  have bN : ¬online b N := λ bN, fN (B2 Bbef bN eN),
  have dfN := S2 (difdifsame ⟨bN, fN, Pa3 Bbef eN⟩ ⟨bN, (λ dN, bN (B2 (B1 Bbcd).1 dN cN)),
    Pa3 Bbcd cN⟩),
  have NL : N ≠ L := λ NL, bN (by rwa ←NL at bL), --start of pf below, API above
  have splitang := (A2 cN aN cL dL nq1.2.2.symm (B1 Bbcd).2.2.2.1 (S3 (S2 afL))
    (S3 (S2 dfN)) NL).mpr ⟨afL, dfN⟩,
  rcases line_of_ne cf with ⟨P, cP, fP⟩,
  have geq := lt_of_le_of_ne (M4 f c d).2 (ne_comm.mp (mt (A1 cf (B1 Bbcd).2.2.2.1 cP fP).mpr _)),--better way to deal with or?
  have geq2 := lt_of_le_of_ne (M4 b a c).2 (angeasy ca (B1 Bbcd).2.1.symm
    (ne_comm.mp (mt (A1 ca.symm ba.symm aN cN).mpr _))),
  linarith [M3 ca (B1 Bbcd).2.1.symm, A4mod1 ba.symm (B1 Bcea).1, A4mod1 cf Bcea],
  exact λ bN, NL (line_unique_of_pts (B1 Bbcd).2.1 bN.1 cN bL cL),
  exact λ dP, S3 (S2 (by rwa ←(line_unique_of_pts (B1 Bbcd).2.2.2.1 cP dP.1 cL dL) at afL)) fP,
end

--Euclid I.16 (Elliptic geometry fails)
theorem extangcor {a b c d : point} {L : line} (aL : ¬online a L) (bL : online b L)
  (dL : online d L) (Bbcd : B b c d) : angle a b c < angle a c d :=
begin
  rcases excor (Leasy (B3 Bbcd bL dL) aL).symm (Leasy (B3 Bbcd bL dL) aL) with ⟨g, Bacg, len3⟩,
  have gb : g ≠ b := λ gb, aL (B2 (B1 Bacg).1 (by rwa ← gb at bL) (B3 Bbcd bL dL)),
  have := aflipboth (B1 Bacg).2.2.2.1.symm gb (B1 Bbcd).2.2.2.1.symm (Leasy dL aL)
    (vertang bL dL aL Bbcd Bacg),
  rcases Beasy3 Bacg with ⟨N, aN, cN, gN, nq⟩,
  linarith [extang (λ bN, aL (by rwa line_unique_of_pts (B1 Bbcd).2.1 bN cN bL (B3 Bbcd bL dL) at aN)) aN gN Bacg],
end

 --Euclid I.18
 theorem sidebigang {a b c : point} {L : line} (bc : b ≠ c) (bL : online b L) (cL : online c L)
  (aL : ¬online a L) (len : dist a b < dist a c) : angle b c a < angle a b c :=
begin
  rcases excor3 (Leasy bL aL).symm len with ⟨d, Badc, len2⟩,
  rcases Beasy3 Badc with ⟨M, aM, dM, cM, nq⟩,
  have ang := extangcor (λ bM, aL (by rwa line_unique_of_pts bc bM cM bL cL at aM)) cM aM (B1 Badc).1,
  have db : d ≠ b := Leasy dM (λ bM, aL (by rwa line_unique_of_pts bc bM cM bL cL at aM)),
  have LM : L ≠ M := λ LM, aL (by rwa LM.symm at aM),
  rcases line_of_ne (Leasy bL aL) with ⟨N, bN, aN⟩,
  have adL : sameside a d L, {by_contra adL, exact Beasy4 (B1 (B1 Badc).1).2.2.2.2
    (Pa4 LM (B1 Badc).2.1 aM cM dM cL nq.2.2.symm nq.2.1 adL), },
  rcases line_of_ne db with ⟨P, dP, bP⟩,
  have aP : ¬online a P := λ aP, LM (line_unique_of_pts bc bL cL (by rwa (line_unique_of_pts nq.1 aP dP aM dM) at bP) cM),
  have cdN := T2 bL bP bN cL dP aN (S2 adL) (Pa3 (B1 Badc).1 dP) aP bc.symm,
  have splitang := (A2 bL cL bN aN bc (Leasy bL aL) (S3 (S2 cdN)) (S3 (S2 adL))
    (λ LN, aL (by rwa ← LN at aN))).mpr ⟨cdN, adL⟩,
  have := isoangle (B1 Badc).2.1 db len2,
  linarith [M3 bc.symm nq.2.2, M3 db nq.1.symm, M3 nq.1 (Leasy bL aL).symm, (M4 c b d).2,
    A4mod1 bc.symm (B1 Badc).1, M3 bc db.symm, M3 bc (Leasy bL aL)],
end

--Euclid I.19 -- Probably can be turned into one line
theorem angbigside {a b c : point} {L : line} (bc : b ≠ c) (bL : online b L) (cL : online c L)
  (aL : ¬online a L) (ang : angle b c a < angle a b c) : dist a b < dist a c :=
begin
  by_cases len : dist a b = dist a c,
  { linarith [M3 bc (Leasy bL aL), isoangle (Leasy bL aL).symm bc len], },
  by_cases len2 : dist a c < dist a b,
  { linarith [sidebigang bc.symm cL bL aL len2, M3 bc.symm (Leasy cL aL), M3 bc (Leasy bL aL)], },
  push_neg at len2,
  exact (ne.le_iff_lt len).mp len2,
end

--Euclid I.20
theorem triineq {a b c : point} {L : line} (ab : a ≠ b) (aL : online a L) (bL : online b L)
  (cL : ¬online c L) : dist b c < dist a b + dist a c :=
begin
  have bc := Leasy bL cL,
  rcases excor ab.symm (Leasy aL cL) with ⟨d, Bbad, len⟩,
  have dc := Leasy (B2 Bbad bL aL) cL,
  have ang := isoangle (B1 Bbad).2.2.2.1 dc (flip2 len),
  rcases line_of_ne (Leasy bL cL) with ⟨M, bM, cM⟩,
  rcases line_of_ne dc with ⟨N, dN, cN⟩,
  have aN : ¬online a N := λ aN,
    cL (by rwa ← (line_unique_of_pts (B1 Bbad).2.2.2.1 aL (B2 Bbad bL aL) aN dN) at cN),
  have adM := Pa2 Bbad bM (λ aM, cL (by rwa (line_unique_of_pts ab aM bM aL bL) at cM)),
  have abN := Pa2 (B1 Bbad).1 dN aN,
  have angsplit := A2mprmod dc.symm bc.symm cN dN cM bM (S2 adM) (S2 (Pa2 (B1 Bbad).1 dN aN)),
  have bigside := angbigside dc.symm cN dN (S3 (S2 abN)) (by linarith [A4mod1 dc (B1 Bbad).1,
    M3 dc (B1 Bbad).2.2.1.symm, M3 dc (B1 Bbad).2.2.2.1.symm, M3 dc.symm bc.symm]),
  linarith [M2 b a, M2 c a, DS1 Bbad],
end

--Euclid I.20
theorem triineqcor {a b c : point} {L : line} (ab : a ≠ b) (aL : online a L) (bL : online b L)
  (cL : ¬online c L) : dist b c < dist a b + dist a c ∧ dist a c < dist a b + dist b c ∧
  dist a b < dist a c + dist b c :=
begin
  rcases line_of_ne (Leasy bL cL) with ⟨M, bM, cM⟩,
  rcases line_of_ne (Leasy aL cL) with ⟨N, aN, cN⟩,
  have aM : ¬online a M := λ aM, cL (by rwa ← (line_unique_of_pts ab aL bL aM bM) at cM),
  have bN : ¬online b N := λ bN, cL (by rwa (line_unique_of_pts ab aN bN aL bL) at cN),
  exact ⟨triineq ab aL bL cL, by linarith [M2 a b, M2 a c, triineq (Leasy bL cL) bM cM aM],
    by linarith [M2 a c, M2 b c, triineq (Leasy aL cL).symm cN aN bN]⟩,
end

--Euclid I.22
theorem trimake {a1 a2 b1 b2 c1 c2 d f g : point} {L : line} (dL : online d L) (fL : online f L)
  (gL : ¬online g L) (ab : dist c1 c2 < dist a1 a2 + dist b1 b2)
  (bc : dist a1 a2 < dist b1 b2 + dist c1 c2) (ac : dist b1 b2  < dist a1 a2 + dist c1 c2)
  (len : dist d f = dist a1 a2) :
  ∃ (k : point), dist d k = dist b1 b2 ∧ dist f k = dist c1 c2 ∧ sameside g k L :=
begin
  have df : d ≠ f := nonzerolenconv (by linarith),
  have b1b2 : b1 ≠ b2,
  { intro b1b2, rw b1b2 at ab; rw b1b2 at bc, linarith [M1.mpr (rfl : b2 = b2)], },--????
  have c1c2 : c1 ≠ c2,
  { intro c1c2, rw c1c2 at ac; rw c1c2 at bc, linarith [M1.mpr (rfl : c2 = c2)], },
  rcases excor2 df.symm b1b2 with ⟨k1, Bfdk1, lenb⟩,
  rcases excor2 df c1c2 with ⟨k2, Bdfk2, lenc⟩,
  rcases circle_of_ne (B1 Bdfk2).2.2.2.1 with ⟨α, fcen, k2circ⟩,
  rcases circle_of_ne (B1 Bfdk1).2.2.2.1 with ⟨β, dcen, k1circ⟩,
  rcases pt_sameside_of_circle_circle_inter (circint fcen dcen k2circ k1circ _ (by linarith [M2 d f])) fcen dcen fL dL gL with
    ⟨k, kalph, kbet, kgL⟩,
  refine ⟨k, by linarith [(DS3 dcen k1circ).mpr kbet], by linarith [(DS3 fcen k2circ).mpr kalph],
    S2 kgL⟩,
  apply abs_lt.mpr,
  exact ⟨by linarith [M2 f d], by linarith [M2 f d]⟩,
  exact ordered_add_comm_monoid.to_covariant_class_left ℝ,
  exact covariant_swap_add_le_of_covariant_add_le ℝ, --why do we have to do this?
end

--Euclid I.23
theorem angcopy {a b c d e h : point} {L M : line} (ab : a ≠ b) (ce : c ≠ e) (cL : online c L)
  (eL : online e L) (dL : ¬online d L) (aM : online a M) (bM : online b M) (hM : ¬online h M) :
  ∃ (f : point), angle b a f = angle e c d ∧ sameside f h M :=
begin
  rcases excor2 ce ab with ⟨e1, Bcee1, len⟩,
  rcases excor2 ab ce with ⟨b1, Babb1, len2⟩,
  have ineqs := triineqcor (B1 Bcee1).2.2.1 cL (B2 Bcee1 cL eL) dL,
  have l3 : dist a b1 = dist c e1 := by linarith [DS1 Bcee1, DS1 Babb1],
  rcases trimake aM (B2 Babb1 aM bM) hM ineqs.1 ineqs.2.2 ineqs.2.1 l3 with ⟨f, l1, l2, hfM⟩,
  refine ⟨f, by linarith [(sss l3 l2 l1).2.1, A4mod1 (Leasy cL dL) Bcee1,
    A4mod1 (Leasy aM (S3 (S2 hfM))) Babb1], S2 hfM⟩,
end

--Euclid I.26 part 1
theorem asa {a b c d e f : point} {L : line} (ef : e ≠ f) (eL : online e L) (fL : online f L)
  (dL : ¬online d L) (side : dist b c = dist e f) (ang1 : angle c b a = angle f e d)
  (ang2 : angle a c b = angle d f e) :
  dist a b = dist d e ∧ dist a c = dist d f ∧ angle b a c = angle e d f :=
begin
  have bc : b ≠ c := λ bc, by linarith [nonzerolen ef, M1.mpr bc],
  rcases line_of_ne bc with ⟨M, bM, cM⟩,
  by_cases len : dist a b = dist d e,
  { have congr := sas side (flipboth len) ang1,
    exact ⟨len, flipboth congr.1, congr.2.2⟩, },
  by_cases len1 : dist d e < dist a b,
  { exfalso,
    rcases excor3 (Leasy eL dL).symm (by linarith [M2 a b] : dist d e < dist b a) with
      ⟨g, Bbga, len2⟩,
    have ac : a ≠ c, --why was this so hard to do?
    { intro ac,
      have := mt (A1 bc (B1 Bbga).2.2.1 bM cM).mp (by linarith [A1mprmod ef eL fL dL]),
      push_neg at this,
      by_cases online a M,
      exact (B1 (this h)).2.2.1.symm ac,
      exact (Leasy cM h).symm ac, },
    have aext := A4mod1 bc Bbga,
    have := M3 bc.symm ac.symm,
    have gc : g ≠ c,--can be oneliner
    { intro gc,
      rw gc at *,
      linarith [nonzerolen (Leasy fL dL), M1.mpr (rfl : c = c), (sas side (flip2 len2)
        (by linarith)).1], },
    have := M3 bc.symm gc.symm,
    have sasc := sas side (flip2 len2) (by linarith [M3 bc.symm gc.symm]),
    rcases line_of_ne ac with ⟨N, aN, cN⟩,
    have gM : ¬online g M,--oneliner?
    { intro gM,
      have := (DA1 bM cM bc).mpr gM,
      exact (mt (DA1 eL fL ef).mp dL) (by rwa (M9 side sasc.1 (flip1 len2) sasc.2.1
        (by linarith) sasc.2.2) at this), },
    rcases Beasy3 Bbga with ⟨O, bO, gO, aO, nq⟩,
    have gN : ¬online g N := λ gN, (Leasy4 gN gM) (line_unique_of_pts bc (by rwa (line_unique_of_pts nq.2.1 gO aO gN aN) at
      bO : online b N) cN bM cM),
    have key := A2mprmod ac.symm bc.symm cN aN cM bM (S2 (Pa2 Bbga bM gM))
      (S2 (Pa2 (B1 Bbga).1 aN gN)),
    linarith [M3 ef (Leasy eL dL), M3 gc (B1 Bbga).2.1.symm], },
  have ab : a ≠ b,--oneliner?
  { intro ab,
    rw ← ab at *,
    linarith [M3 ef (Leasy eL dL), A1mprmod ef.symm fL eL dL, (A1 bc.symm bc.symm cM bM).mp
      ⟨bM, (λ Bcac, (B1 Bcac).2.2.1 rfl)⟩], },
  push_neg at len1,
  rcases excor3 ab (by linarith [((ne.le_iff_lt len).mp len1), M2 d e] : dist a b < dist e d) with
    ⟨g, Begd, len2⟩,
  have := A4mod1 ef Begd,
  have := M3 ef.symm (Leasy fL dL),
  rcases line_of_ne (Leasy eL dL) with ⟨M, eM, dM⟩,
  rcases line_of_ne (Leasy fL dL) with ⟨N, fN, dN⟩,
  have gL : ¬online g L := λ gL, dL (B2 Begd eL gL),
  have sasc := sas side (flip2 len2).symm (by linarith [M3 ef.symm (Leasy fL gL)]),
  have gN : ¬online g N,--oneliner?
  { intro gN,
    have := line_unique_of_pts (B1 Begd).2.2.2.1 gN dN (B3 Begd eM dM) dM,
    exact (Leasy4 gN gL) (line_unique_of_pts ef eL fL (by rwa ← this at eM : online e N) fN).symm, },
  have key := A2mprmod (Leasy fL dL) ef.symm fN dN fL eL (S2 (Pa2 Begd eL gL))
    (S2 (Pa2 (B1 Begd).1 dN gN)),
  linarith [M3 bc ab.symm, M3 ef (B1 Begd).2.1],
end

--Euclid I.27
theorem angeqpar {a e f d : point} {L M N : line} (ae : a ≠ e) (ef : e ≠ f) (fd : f ≠ d)
  (MN : M ≠ N) (aM : online a M) (eM : online e M) (fN : online f N) (dN : online d N)
  (eL : online e L) (fL : online f L) (ang : angle a e f = angle e f d) (adL : diffside a d L) :
  para a e f d M N :=
begin
  refine ⟨aM, eM, fN, dN,_⟩,
  intro g,
  by_contra gMN,
  push_neg at gMN,
  have ML : M ≠ L := λ ML, adL.1 (by rwa ML at aM),
  have NL : N ≠ L := λ NL, adL.2.1 (by rwa NL at dN),
  have eN : ¬online e N := λ eN, NL (line_unique_of_pts ef eN fN eL fL),
  have fM : ¬online f M := λ fM, ML (line_unique_of_pts ef eM fM eL fL),
  have gL : ¬online g L := λ gL, ML (line_unique_of_pts (Leasy gMN.2 eN) gMN.1 eM gL eL),
  have dg : d ≠ g,
  { intro dg,
    rw dg at *,
    linarith [M3 ae (Leasy aM fM), M3 ef (Leasy dN eN).symm, extang fM gMN.1 aM (B1 (Pa4 ML.symm
      (difneq adL) aM eM gMN.1 eL ae (Leasy eL gL).symm adL.2.2)).1], },
  have ag : a ≠ g,
  { intro ag,
    rw ag at *,
    linarith [extang eN gMN.2 dN (B1 (Pa4 NL.symm dg dN fN gMN.2 fL fd.symm (Leasy fL gL).symm
    (difsym adL.2.2))).1], },
  cases S5 adL.2.1 adL.1 gL (difsym adL.2.2) with dgL agL,
  { by_cases Bfdg : B f d g,
    { have Baeg := Pa4 ML.symm ag aM eM gMN.1 eL ae (Leasy gMN.2 eN)
        (difsym (difsamedif dgL ⟨adL.2.1, adL.1, difsym adL.2.2⟩).2.2),
      have ang1 := extang fM gMN.1 (B2 (B1 Baeg).1 gMN.1 eM) (B1 Baeg).1,
      linarith [A4mod1 (Leasy eM fM).symm Bfdg, M3 (Leasy fL (S3 dgL)).symm (Leasy dN eN),
        M3 (Leasy eM fM).symm (Leasy (B2 (B1 Baeg).1 gMN.1 eM) fM).symm], },
    by_cases Bfgd : B f g d,
    { have Baeg := Pa4 ML.symm ag aM eM gMN.1 eL ae (Leasy gMN.2 eN) (difsym (difsamedif dgL
        ⟨adL.2.1, adL.1, difsym adL.2.2⟩).2.2),
      have ang1 := extang fM gMN.1 (B2 (B1 Baeg).1 gMN.1 eM) (B1 Baeg).1,
      linarith [M3 ae (Leasy aM fM), M3 ef (Leasy gMN.2 eN).symm, M3 fd.symm (Leasy dN eN),
        A4mod1 ef.symm Bfgd], },
    cases B6 fN dN gMN.2 fd (Leasy fL gL) dg,
    exact Bfdg h,
    cases h with Bdfg,
    exact (Pa3 Bdfg fL) dgL,
    exact Bfgd h, },
  by_cases Beag : B e a g,
  { have ang1 := extang eN gMN.2 dN (B1 (Pa4 NL.symm dg dN fN gMN.2 fL fd.symm (Leasy fL gL).symm
      (difsym (difsamedif agL adL).2.2))).1,
    linarith [A4mod1 ef Beag], },
  by_cases Bega : B e g a,
  { have ang1 := extang eN gMN.2 dN (B1 (Pa4 NL.symm dg dN fN gMN.2 fL fd.symm (Leasy fL gL).symm
      (difsym (difsamedif agL adL).2.2))).1,
    linarith [A4mod1 ef Bega], },
  cases B6 eM aM gMN.1 ae.symm (Leasy eL gL) ag,
  exact Beag h,
  cases h with Baeg,
  exact (Pa3 Baeg eL) agL,
  exact Bega h,
end

--Euclid I.29
theorem parapost {a b d e g h : point} {L M N : line} (dh : d ≠ h) (hL : online h L)
  (gL : online g L) (par : para a g h d M N) (Bagb : B a g b) (Begh : B e g h)
  (bdL : sameside b d L) : angle a g h = angle g h d ∧ angle e g b = angle g h d ∧
  angle b g h + angle g h d = 2 * rightangle :=
begin
  rcases excor dh dh.symm with ⟨c, Bdhc, len⟩,
  have hM : ¬online h M, { cases par.2.2.2.2 h, exact h_1, exfalso, exact h_1 par.2.2.1, },--better way?
  have gN : ¬online g N, { cases par.2.2.2.2 g, exfalso, exact h_1 par.2.1, exact h_1 },--better way?
  have acL : sameside a c L := difdifsame (difsamedif bdL ⟨S3 bdL, λ aL, (S3 bdL) (B2 Bagb aL gL),
    difsym (Pa3 Bagb gL)⟩) ⟨(S3 (S2 bdL)), λ cL, (S3 (S2 bdL)) (B2 (B1 Bdhc).1 cL hL),
    Pa3 Bdhc hL⟩,
  have := M3 (Leasy par.2.1 hM).symm (Leasy (B2 Bagb par.1 par.2.1) hM).symm,
  have := M3 (Leasy par.2.1 hM).symm (Leasy par.1 hM).symm,
  have := flatsumright (par.1) (B2 Bagb (par.1) (par.2.1)) hM Bagb,
  have := flatsumright par.2.2.2.1 (B2 Bdhc par.2.2.2.1 par.2.2.1) gN Bdhc,
  have key1 : angle a g h = angle g h d,
  { by_contra ang,
    by_cases ang1 : angle g h d < angle a g h, --anything better than the casework?
    { rcases A5 (B2 Bagb par.1 par.2.1) par.2.1 gL hL par.2.2.1 par.2.2.2.1 (Leasy par.2.1 hM) bdL
        (by linarith) with ⟨e, eM, eN, junk⟩, -- *** `junk` can be replaced by `-`?
      cases par.2.2.2.2 e,
      exact h_1 eM,
      exact h_1 eN, },
    push_neg at ang1,
    have ang2 : angle a g h < angle g h d := (ne.le_iff_lt ang).mp ang1,--anything better?
    rcases A5 par.1 par.2.1 gL hL par.2.2.1 (B2 Bdhc par.2.2.2.1 par.2.2.1) (Leasy par.2.1 hM) acL
      (by linarith) with ⟨e, eM, eN, junk⟩,
    cases par.2.2.2.2 e, exact h_1 eM, exact h_1 eN, },
  exact ⟨key1, by linarith [vertang hL (B2 (B1 Begh).1 hL gL) (S3 bdL) (B1 Begh).1 (B1 Bagb).1],
    by linarith⟩,
end

--Euclid I.29
theorem parapostcor {a d g h : point} {L M N : line} (dh : d ≠ h) (hL : online h L)
  (gL : online g L) (par : para a g h d M N) (adL : diffside a d L) : angle a g h = angle g h d :=
begin
  have hg : h ≠ g,
  { intro hg, rw hg at *, cases par.2.2.2.2 g, exact h_1 par.2.1, exact h_1 par.2.2.1, },
  rcases excor (Leasy gL adL.1).symm (Leasy gL adL.1) with ⟨b, Bagb, junk⟩,
  rcases excor hg hg.symm with ⟨e, Bhge, junk⟩,
  exact (parapost dh hL gL par Bagb (B1 Bhge).1
    (difdifsame ⟨adL.1, (λ bL, adL.1 (B2 (B1 Bagb).1 bL gL)), Pa3 Bagb gL⟩ adL)).1,
end

--Euclid I.31
theorem drawpar {a b c : point} {L : line} (bc : b ≠ c) (bL : online b L) (cL : online c L)
  (aL : ¬online a L) : ∃ (e : point), ∃ (N : line), para e a b c N L :=
begin
  rcases pt_B_of_ne bc with ⟨d, Bbdc⟩,
  have dL := B3 Bbdc bL cL,
  rcases line_of_ne (Leasy dL aL) with ⟨M, dM, aM⟩,
  have bM : ¬online b M := λ bM, (Leasy4 aM aL) (line_unique_of_pts bc bM (B2 Bbdc bM dM) bL cL),
  rcases angcopy (Leasy dL aL).symm (B1 Bbdc).2.2.2.1 dL cL aL aM dM bM with ⟨e, ang, ebM⟩,
  have ae : a ≠ e := λ ae, (S3 ebM) (by rwa ae at aM),
  rcases line_of_ne ae with ⟨N, aN, eN⟩,
  refine ⟨e, N, paraeasy bL (angeqpar ae.symm (Leasy dL aL).symm (B1 Bbdc).2.2.2.1
    (Leasy4 aN aL) eN aN dL cL aM dM (by linarith [M3 ae.symm (Leasy dM (S3 ebM)).symm,
    M3 (Leasy dL aL).symm (Leasy cL aL).symm]) (difsamedif (S2 ebM)
    ⟨bM, (λ cM, bM (B2 (B1 Bbdc).1 cM dM)), Pa3 Bbdc dM⟩))⟩,
end

-- Euclid I.34
theorem parasianar {a b c d : point} {L M N K : line} (par1 : para a b c d L M)
  (par2 : para a c b d K N) :
  dist a b = dist c d ∧ angle c a b = angle b d c ∧ area c a b = area b d c :=
begin
  have ab : a ≠ b := Leasy par2.1 (paraeasy2 par2).2.2.2.1,
  have cd : c ≠ d := Leasy par2.2.1 (paraeasy2 par2).2.2.2.2.1,
  have cb : c ≠ b := Leasy par1.2.2.1 (paraeasy2 par1).2.2.1,
  have ca : c ≠ a := Leasy par1.2.2.1 (paraeasy2 par1).2.1,
  rcases line_of_ne cb with ⟨O, cO, bO⟩,
  have adO := T1 par1.2.1 bO par2.2.2.1 par1.1 cO par2.2.2.2.1
    (paraeasy2 par1).2.2.2.2.2.2 (paraeasy2 par2).2.2.2.2.2.1,
  have aO : ¬online a O,
  { intro aO, have := line_unique_of_pts ab par1.1 par1.2.1 aO bO, rw this at par1, cases par1.2.2.2.2 c,
    exact h cO, exact h par1.2.2.1, },
  have dO : ¬online d O,
  { intro dO, have := line_unique_of_pts cd cO dO par1.2.2.1 par1.2.2.2.1, rw this at *, cases par1.2.2.2.2 b,
    exact h par1.2.1, exact h bO, },
  have ang1 := parapostcor cd.symm cO bO par1 ⟨aO, dO, adO⟩,
  have ang2 := parapostcor ca.symm cO bO (paraeasy1 par2) ⟨dO, aO, difsym adO⟩,
  have key := asa cb cO bO aO (M2 b c) (by linarith [M3 cb cd] : angle c b d = angle b c a)
    (by linarith [M3 cd.symm (Leasy bO dO).symm]),
  exact ⟨by linarith [M2 c d], key.2.2.symm, (M9 (flipboth key.1) key.2.1 (M2 c b) key.2.2
    (by linarith [M3 cb.symm ab.symm]) (by linarith [M3 cb ca])).symm⟩,
end

--Euclid I.35
theorem parallelarea1 {a b c d e f : point} {L M K N O P : line} (par1 : para a d b c L M)
  (par2 : para b c e f M L) (par3 : para a b d c K N) (par4 : para b e c f O P) (Baed : B a e d) :
  area b a d + area d b c = area c f e + area e c b :=
begin
  have ad := Leasy par3.1 (paraeasy2 par3).2.2.2.1,
  have bc := Leasy par3.2.1 (paraeasy2 par3).2.2.2.2.1,
  have eP := (paraeasy2 par4).2.2.1,
  have dfM := (paraeasy2 (paraeasy par1.2.1 par2)).2.2.2.2.2.2,
  have edM := S4 (S2 (paraeasy2 par2).2.2.2.2.2.2) (S2 dfM),
  have := parasianar par1 par3,
  have := parasianar par2 par4,
  by_cases af : a = f,
  { rw ← af at *,
    have := quadarea ad bc par1.1 par1.2.1 par1.2.2.1 par1.2.2.2.1 par3.2.2.1 par3.2.2.2.1
      (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par2).2.2.2.2.2.1 (paraeasy2 par3).2.2.2.2.2.1,
    have := quadarea (Leasy par4.2.1 (paraeasy2 par4).2.2.2.2.1) bc par2.2.2.1 par1.1 par1.2.2.1
      par1.2.2.2.1 par4.2.2.2.1 par4.2.2.1 (paraeasy2 par2).2.2.2.2.2.2
      (paraeasy2 par2).2.2.2.2.2.1 (S2 (paraeasy2 par4).2.2.2.2.2.1),
    have := sss (by linarith :dist a d = dist e a) (parasianar par3 par1).1.symm
      (flipboth (parasianar par4 par2).1).symm,
    have := M9 (by linarith :dist a d = dist e a) (parasianar par3 par1).1.symm
      (parasianar par4 par2).1.symm this.1 this.2.1 this.2.2,
    linarith [M8 d c b, M8 d a b, M8 b d a, M8 c b e, M8 c b a, M8 c d a, M8 a c d, M8 a e b,
      M8 a b e], },
  by_cases df : d = f,
  { rw ← df at *,
    have NP := line_unique_of_pts (Leasy par1.2.1 (paraeasy2 par1).2.2.2.2.1) par3.2.2.1 par3.2.2.2.1
      par4.2.2.2.1 par4.2.2.1, rw ← NP at *, exfalso, cases B6 par1.1 par2.2.2.1 par1.2.1
      (B1 Baed).2.1 ad (B1 Baed).2.2.2.1,
    linarith [DS1 h, nonzerolen (B1 Baed).2.1],
    cases h,
    linarith [DS1 h, nonzerolen (B1 Baed).2.1.symm],
    have abN := (paraeasy2 par3).2.2.2.2.2.1,
    exact (difsamedif abN ⟨S3 abN, (paraeasy2 par4).2.2.1, Pa3 h par3.2.2.1⟩).2.2
      (paraeasy2 par4).2.2.2.2.2.1, },
  have Bedf : B e d f,
  { cases B6 par2.2.2.1 par1.2.1 par2.2.2.2.1 (B1 Baed).2.2.2.1 (Leasy par4.2.2.2.1 eP).symm df,
    exact h,
    exfalso,
    cases h with Bdef Befd,
    { cases or.swap (Beasy5 af (B1 Baed).1 Bdef) with Befa Beaf,
      linarith [DS1 Befa, DS1 Baed, M2 e a, nonzerolen af, M2 a f, nonzerolen (B1 Baed).2.2.2.1],
      by_cases bfN : sameside b f N,
      { have dbP := difsym (T1 par1.2.2.2.1 par4.2.2.1 par3.2.2.2.1 par2.1  par4.2.2.2.1
          par3.2.2.1 (S2 dfM) bfN),
        have deP := S2 (Pa2 (B1 Bdef).1 par4.2.2.2.1 eP),
        exact (difsamedif deP ⟨(λ dP, eP (B3 (B1 Bdef).1 par4.2.2.2.1 dP)),
          (paraeasy2 par4).2.1, dbP⟩).2.2 (S2 (paraeasy2 par4).2.2.2.2.2.1), },
      exact bfN (S2 (S4 (Pa2 (B1 (B5 (B1 Beaf).1 Baed)).1 par3.2.2.1 (paraeasy2 par3).2.1)
        (paraeasy2 par3).2.2.2.2.2.1)), },
    linarith [DS1 Befd, DS1 Baed, nonzerolen (B1 Baed).2.1, nonzerolen df, M2 d f], },
  have := DA2mpmod par1.1 par1.2.1 par2.2.2.1 (paraeasy2 par1).2.2.2.1 Baed,
  have ebN := S4 (S2 (Pa2 (B1 Baed).1 par3.2.2.1 (λ eN, (paraeasy2 par3).2.1
    (B2 (B1 Baed).1 par3.2.2.1 eN)))) (paraeasy2 par3).2.2.2.2.2.1,
  have := quadarea (B1 Baed).2.2.2.1 bc par2.2.2.1 par1.2.1 par2.1 par2.2.1 par3.2.2.1
    par3.2.2.2.1 edM (paraeasy2 par2).2.2.2.2.2.1 ebN,
  have := parasianar par3 par1,
  have := DS1 Baed,
  have := DS1 Bedf,
  have := sss (by linarith : dist a e = dist d f).symm (flipboth (parasianar par4 par2).1).symm
    (parasianar par3 par1).1.symm,
  have := M9 (by linarith : dist a e = dist d f).symm  (flipboth (parasianar par4 par2).1.symm)
    (flipboth (parasianar par3 par1).1).symm this.1 this.2.1 this.2.2,
  have := DA2mpmod par2.2.2.1 par2.2.2.2.1 par1.2.1 (paraeasy2 par1).2.2.2.2.1 Bedf,
  linarith [M8 b a d, M8 b d a, M8 d c b, M8 d e b, M8 b d e, M8 e d c, M8 c e d, M8 d f c,
    M8 c f e, M8 c b e],
end

--Euclid I.35
theorem parallelarea2 {a b c d e f : point} {L M K N O P : line} (par1 : para a d b c L M)
  (par2 : para b c e f M L) (par3 : para a b d c K N) (par4 : para b e c f O P) (Bade : B a d e) :
  area b a d + area d b c = area c f e + area e c b :=
begin
  have ab := Leasy par1.1 (paraeasy2 par1).2.2.2.1,
  have ad := Leasy par3.1 (paraeasy2 par3).2.2.2.1,
  have bc := Leasy par3.2.1 (paraeasy2 par3).2.2.2.2.1,
  have dc := Leasy par1.2.1 (paraeasy2 par1).2.2.2.2.1,
  have ef := Leasy par4.2.1 (paraeasy2 par4).2.2.2.2.1,
  have dfM := (paraeasy2 (paraeasy par1.2.1 par2)).2.2.2.2.2.2,
  have := parasianar par1 par3,
  have := parasianar par2 par4,
  by_cases af : a = f,
  { rw ← af at *,
    have := quadarea ad bc par1.1 par1.2.1 par1.2.2.1 par1.2.2.2.1 par3.2.2.1 par3.2.2.2.1
      (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par2).2.2.2.2.2.1 (paraeasy2 par3).2.2.2.2.2.1,
    have := quadarea ef bc par2.2.2.1 par1.1 par1.2.2.1 par1.2.2.2.1 par4.2.2.2.1 par4.2.2.1
      (paraeasy2 par2).2.2.2.2.2.2 (paraeasy2 par2).2.2.2.2.2.1 (S2 (paraeasy2 par4).2.2.2.2.2.1),
    have := sss (by linarith :dist a d = dist e a) (parasianar par3 par1).1.symm (flipboth
      (parasianar par4 par2).1).symm,
    have := M9 (by linarith :dist a d = dist e a) (parasianar par3 par1).1.symm  (parasianar par4
      par2).1.symm this.1 this.2.1 this.2.2,
    linarith [M8 d c b, M8 d a b, M8 b d a, M8 c b e, M8 c b a, M8 c d a, M8 a c d, M8 a e b,
      M8 a b e], },
  by_cases df : d = f,
  { rw ← df at *, have NP := line_unique_of_pts dc par3.2.2.1 par3.2.2.2.1 par4.2.2.2.1 par4.2.2.1, rw ← NP at *,
    { exfalso, cases B6 par1.1 par2.2.2.1 par1.2.1 (B1 Bade).2.2.1 ad (B1 Bade).2.2.2.1.symm,
      linarith [DS1 h, nonzerolen (B1 Bade).2.2.1], cases h, linarith [DS1 h, nonzerolen
        (B1 Bade).2.2.1.symm],
      have abN := (paraeasy2 par3).2.2.2.2.2.1,
      exact (difsamedif abN ⟨S3 abN, (paraeasy2 par4).2.2.1, Pa3 h par3.2.2.1⟩).2.2
        (paraeasy2 par4).2.2.2.2.2.1, }, },
  have Bdef : B d e f,
  { cases B6 par1.2.1 par2.2.2.1 par2.2.2.2.1 (B1 Bade).2.2.2.1 df ef,
    exact h,
    exfalso,
    cases h with Bedf Bdfe,
    { by_cases bfN : sameside b f N,
      { have dP : ¬online d P := λ dP, (paraeasy2 par4).2.2.1 (B2 (B1 Bedf).1 par4.2.2.2.1 dP),
        have dbP := difsym (T1 par1.2.2.2.1 par4.2.2.1 par3.2.2.2.1 par2.1
          par4.2.2.2.1 par3.2.2.1 (S2 dfM) bfN),
        exact (difsamedif (Pa2 (B1 Bedf).1 par4.2.2.2.1 dP) ⟨dP, (paraeasy2 par4).2.1, dbP⟩).2.2
          (S2 (paraeasy2 par4).2.2.2.2.2.1), },
      cases Beasy5 af (B1 Bade).1 Bedf with Bdaf Bdfa,
      linarith [DS1 Bdaf, DS1 Bedf, nonzerolen (B1 Bade).2.2.2.1.symm, nonzerolen af, M2 a d],
      have fN := λ fN, (paraeasy2 par3).2.1 (B2 Bdfa par3.2.2.1 fN),
      exact (difsamedif (S2 (paraeasy2 par3).2.2.2.2.2.1) ⟨(paraeasy2 par3).2.2.1, fN, bfN⟩).2.2
        (S2 (Pa2 Bdfa par3.2.2.1 fN)), },
    have Bfda := Beasy7 (B1 Bdfe).1 (B1 Bade).1,
    by_cases bfN : sameside b f N,
    exact (Pa3 Bfda par3.2.2.1) (S2 (S4 (S2 (paraeasy2 par3).2.2.2.2.2.1) bfN)),
    have fN := λ fN, (paraeasy2 par3).2.1 (B2 Bfda fN par3.2.2.1),
    exact (Pa3 Bdfe par4.2.2.2.1) (S4 (T2 par1.2.2.2.1 par3.2.2.2.1 par4.2.2.1 par1.2.2.1
      par3.2.2.1 par4.2.2.2.1 dfM bfN fN bc) (paraeasy2 par4).2.2.2.2.2.1), },
  have dO := λ dO, (paraeasy2 par4).2.2.2.2.1 (B2 Bdef dO par4.2.1),
  have eN := λ eN, (paraeasy2 par3).2.1 (B2 (B1 Bade).1 eN par3.2.2.1),
  have cdO := (difsamedif (S2 (paraeasy2 par4).2.2.2.2.2.2)
    ⟨(paraeasy2 par4).2.2.2.2.1, dO, difsym (Pa3 Bdef par4.2.1)⟩).2.2,
  have beN := (difsamedif (paraeasy2 par3).2.2.2.2.2.1 ⟨(paraeasy2 par3).2.1, eN,
    (Pa3 Bade par3.2.2.1)⟩).2.2,
  rcases pt_of_line_line_inter (Int1 beN par4.1 par4.2.1) with ⟨g, gN, gO⟩,
  have Bbge := Pa4 (Leasy4 par4.2.1 eN).symm (Leasy par1.2.2.1 (paraeasy2 par2).2.2.2.1)
    par4.1 gO par4.2.1 gN (Leasy gN (paraeasy2 par3).2.2.1).symm (Leasy gN eN).symm beN,
  have Bcgd := Pa4 (Leasy4 par4.2.1 eN) dc.symm par3.2.2.2.1 gN par3.2.2.1 gO (Leasy gO
    (paraeasy2 par4).2.2.2.1).symm (Leasy gO dO).symm cdO,
  have := parasianar par3 par1,
  have := DS1 Bade,
  have := DS1 Bdef,
  have := sss (by linarith : dist a e = dist d f).symm (flipboth (parasianar par4 par2).1).symm
    (parasianar par3 par1).1.symm,
  have := M9 (by linarith : dist a e = dist d f).symm  (flipboth (parasianar par4 par2).1.symm)
    (flipboth (parasianar par3 par1).1).symm this.1 this.2.1 this.2.2,
  have := DA2mpmod par4.1 par4.2.1 gO dO Bbge,
  have := DA2mpmod par4.1 par4.2.1 gO (λ cO, dO (B2 Bcgd cO gO)) Bbge,
  have := DA2mpmod par3.2.2.2.1 par3.2.2.1 gN (λ bN, eN (B2 Bbge bN gN)) Bcgd,
  have := DA2mpmod par3.2.2.2.1 par3.2.2.1 gN eN Bcgd,
  have := DA2mpmod par1.1 par2.2.2.1 par1.2.1 (paraeasy2 par2).2.1 Bade,
  have := DA2mpmod par1.2.1 par2.2.2.2.1 par2.2.2.1 (paraeasy2 par2).2.2.1 Bdef,
  linarith [M8 d c f, M8 c e f, M8 d e c, M8 c d e, M8 a b e, M8 a d b, M8 e g d, M8 d e g,
    M8 c b d, M8 d c b, M8 b g c, M8 c b g, M8 e c b, M8 b e c],
end

--Euclid I.35
theorem parallelarea3 {a b c d e f : point} {L M K N O P : line} (par1 : para a d b c L M)
  (par2 : para b c e f M L) (par3 : para a b d c K N) (par4 : para b e c f O P) (Bdae : B d a e) :
  area b a d + area d b c = area c f e + area e c b :=
begin
  have bc := Leasy par3.2.1 (paraeasy2 par3).2.2.2.2.1,
  have ef := Leasy par4.2.1 (paraeasy2 par4).2.2.2.2.1,
  have := parasianar par1 par3,
  have := parasianar par2 par4,
  by_cases af : a = f,
  { rw ← af at *,
    have := quadarea (B1 Bdae).2.1.symm bc par1.1 par1.2.1 par1.2.2.1 par1.2.2.2.1 par3.2.2.1
      par3.2.2.2.1 (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par2).2.2.2.2.2.1
      (paraeasy2 par3).2.2.2.2.2.1,
    have := quadarea ef bc par2.2.2.1 par1.1 par1.2.2.1 par1.2.2.2.1 par4.2.2.2.1 par4.2.2.1
      (paraeasy2 par2).2.2.2.2.2.2 (paraeasy2 par2).2.2.2.2.2.1 (S2 (paraeasy2 par4).2.2.2.2.2.1),
    have := sss (by linarith :dist a d = dist e a) (parasianar par3 par1).1.symm (flipboth
      (parasianar par4 par2).1).symm,
    have := M9 (by linarith :dist a d = dist e a) (parasianar par3 par1).1.symm
      (parasianar par4 par2).1.symm this.1 this.2.1 this.2.2,
    linarith [M8 d c b, M8 d a b, M8 b d a, M8 c b e, M8 c b a, M8 c d a, M8 a c d, M8 a e b,
      M8 a b e], },
  by_cases df : d = f,
  { rw ← df at *,
    have NP := line_unique_of_pts (Leasy par1.2.1 (paraeasy2 par1).2.2.2.2.1) par3.2.2.1 par3.2.2.2.1 par4.2.2.2.1
      par4.2.2.1,
    rw ← NP at *,
    exfalso,
    cases B6 par1.1 par2.2.2.1 par1.2.1 (B1 Bdae).2.2.2.1 (B1 Bdae).2.1.symm (B1 Bdae).2.2.1.symm,
    linarith [DS1 h, nonzerolen (B1 Bdae).2.2.2.1],
    cases h,
    linarith [DS1 h, nonzerolen (B1 Bdae).2.2.2.1.symm],
    have abN := (paraeasy2 par3).2.2.2.2.2.1,
    exact (difsamedif abN ⟨S3 abN, (paraeasy2 par4).2.2.1, Pa3 h par3.2.2.1⟩).2.2
      (paraeasy2 par4).2.2.2.2.2.1, },
  have key : B d f a ∨ B d a f,
  { by_contra key, push_neg at key,
    cases B6 par1.2.1 par2.2.2.2.1 par1.1 df (B1 Bdae).2.1 (ne.symm af),
    exact key.1 h,
    cases h,
    linarith [DS1 (B5 h Bdae), DS1 Bdae, M2 a d, M2 e f, nonzerolen (B1 Bdae).2.2.2.1,
      nonzerolen (B1 h).2.1],
    exact key.2 h, },
  cases key,
  have := parallelarea1 (paraeasy3 par1) (paraeasy3 par2) (paraeasy4 par3) (paraeasy4 par4) key,
  have := quadarea (B1 key).2.2.1.symm bc par1.1 par1.2.1 par1.2.2.1 par1.2.2.2.1 par3.2.2.1
    par3.2.2.2.1 (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par1).2.2.2.2.2.2
    (paraeasy2 par3).2.2.2.2.2.1,
  have := quadarea ef bc par2.2.2.1 par2.2.2.2.1 par1.2.2.1 par1.2.2.2.1 par4.2.2.2.1 par4.2.2.1
    (paraeasy2 par2).2.2.2.2.2.2 (paraeasy2 par1).2.2.2.2.2.2 (S2 (paraeasy2 par4).2.2.2.2.2.1),
  linarith [M8 b a d, M8 d b a, M8 d b c, M8 c b e, M8 c b a, M8 b e f, M8 f b e, M8 f b c],
  have := parallelarea2 (paraeasy3 par1) (paraeasy3 par2) (paraeasy4 par3) (paraeasy4 par4) key,
  have := quadarea (B1 key).2.1.symm bc par1.1 par1.2.1 par1.2.2.1 par1.2.2.2.1 par3.2.2.1
    par3.2.2.2.1 (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par1).2.2.2.2.2.2
    (paraeasy2 par3).2.2.2.2.2.1,
  have := quadarea ef bc par2.2.2.1 par2.2.2.2.1 par1.2.2.1 par1.2.2.2.1 par4.2.2.2.1 par4.2.2.1
    (paraeasy2 par2).2.2.2.2.2.2 (paraeasy2 par1).2.2.2.2.2.2 (S2 (paraeasy2 par4).2.2.2.2.2.1),
  linarith [M8 b a d, M8 d b a, M8 d b c, M8 c b e, M8 c b a, M8 b e f, M8 f b e, M8 f b c],
end

--Euclid I.35
theorem parallelarea {a b c d e f : point} {L M K N O P : line} (par1 : para a d b c L M)
  (par2 : para b c e f M L) (par3 : para a b d c K N) (par4 : para b e c f O P) :
  area b a d + area d b c = area c f e + area e c b :=
begin
  have ab := Leasy par1.1 (paraeasy2 par1).2.2.2.1,
  have ad := Leasy par3.1 (paraeasy2 par3).2.2.2.1,
  have bc := Leasy par3.2.1 (paraeasy2 par3).2.2.2.2.1,
  have dc := Leasy par1.2.1 (paraeasy2 par1).2.2.2.2.1,
  have ef := Leasy par4.2.1 (paraeasy2 par4).2.2.2.2.1,
  have := parasianar par1 par3,
  have := parasianar par2 par4,
  by_cases af : a = f,
  { rw ← af at *,
    have := quadarea ad bc par1.1 par1.2.1 par1.2.2.1 par1.2.2.2.1 par3.2.2.1 par3.2.2.2.1
      (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par2).2.2.2.2.2.1 (paraeasy2 par3).2.2.2.2.2.1,
    have := quadarea ef bc par2.2.2.1 par1.1 par1.2.2.1 par1.2.2.2.1 par4.2.2.2.1 par4.2.2.1
      (paraeasy2 par2).2.2.2.2.2.2 (paraeasy2 par2).2.2.2.2.2.1 (S2 (paraeasy2 par4).2.2.2.2.2.1),
    have := sss (by linarith :dist a d = dist e a) (parasianar par3 par1).1.symm (flipboth
      (parasianar par4 par2).1).symm,
    have := M9 (by linarith :dist a d = dist e a) (parasianar par3 par1).1.symm
      (parasianar par4 par2).1.symm this.1 this.2.1 this.2.2,
    linarith [M8 d c b, M8 d a b, M8 b d a, M8 c b e, M8 c b a, M8 c d a, M8 a c d, M8 a e b,
      M8 a b e], },
  by_cases ed : e = d, { rw ed at *, linarith, },
  by_cases df : d = f,
  { rw ← df at *,
    have NP := line_unique_of_pts dc par3.2.2.1 par3.2.2.2.1 par4.2.2.2.1 par4.2.2.1,
    rw ← NP at *,
    by_cases ae : a ≠ e,
    { exfalso,
      cases B6 par1.1 par2.2.2.1 par1.2.1 ae ad ed,
      linarith [DS1 h, nonzerolen ae],
      cases h,
      linarith [DS1 h, nonzerolen ae.symm],
      have abN := (paraeasy2 par3).2.2.2.2.2.1,
      exact (difsamedif abN ⟨S3 abN, (paraeasy2 par4).2.2.1, Pa3 h par3.2.2.1⟩).2.2
        (paraeasy2 par4).2.2.2.2.2.1, },
    push_neg at ae,
    rw ae at *,
    have := quadarea ad bc par2.2.2.1 par2.2.2.2.1 par2.1 par2.2.1 par4.2.2.2.1 par4.2.2.1
      (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par2).2.2.2.2.2.1 (paraeasy2 par3).2.2.2.2.2.1,
    linarith [M8 c b e, M8 d c b, M8 b d e, M8 d e b], },
  by_cases ae : a = e,
  { exfalso,
    rw ← ae at *,
    have OK := line_unique_of_pts ab par4.2.1 par4.1 par3.1 par3.2.1,
    rw OK at *,
    cases B6 par1.1 par1.2.1 par2.2.2.2.1 ad af df,
    linarith [nonzerolen df, DS1 h],
    cases h,
    exact (difsamedif (S2 (paraeasy2 par4).2.2.2.2.2.2) ⟨(paraeasy2 par4).2.2.2.2.1,
      (paraeasy2 par3).2.2.2.1, difsym (Pa3 h par3.1)⟩).2.2 (S2 (paraeasy2 par3).2.2.2.2.2.2),
    linarith [nonzerolen df, M2 d f, DS1 h], },
  cases B6 par1.1 par2.2.2.1 par1.2.1 ae ad ed,
  exact parallelarea1 par1 par2 par3 par4 h,
  cases h,
  exact parallelarea3 par1 par2 par3 par4 (B1 h).1,
  exact parallelarea2 par1 par2 par3 par4 h,
end

--Lemma for I.37
theorem parallelodraw {a d b c : point} {L M N : line} (ad : a ≠ d) (bc : b ≠ c) (aN : online a N)
  (cN : online c N) (par : para a d b c L M) (bdN : ¬sameside b d N) :
  ∃ (e : point) (P : line), para e b a c P N ∧ para e a b c L M ∧ B d a e :=
begin
  rcases line_of_ne (Leasy par.1 (paraeasy2 par).2.2.2.1) with ⟨O, aO, bO⟩,
  have bN := λ bN, (paraeasy2 par).2.1 (by rwa (line_unique_of_pts bc bN cN par.2.2.1 par.2.2.2.1) at aN),
  rcases excor2 ad.symm bc with ⟨e, Bdae, len⟩,
  have dcO := T2 par.1 aN aO par.2.1 cN bO (S2 (paraeasy2 par).2.2.2.2.2.2) (difsym bdN) bN
    ad.symm,
  have deO := Pa3 Bdae aO,
  have dO := S3 dcO,
  have ecO := (difsamedif dcO ⟨dO, λ eO, dO (B2 (B1 Bdae).1 eO aO), deO⟩),
  have par2 := paraeasy5 (paraeasy (B2 Bdae par.2.1 par.1)
    (paraeasy5 (paraeasy4 (paraeasy5 par)))),
  have := parapostcor (B1 Bdae).2.2.2.1.symm aO bO (paraeasy5 (paraeasy (B2 Bdae par.2.1 par.1)
    (paraeasy5 (paraeasy4 (paraeasy5 par))))) ecO,
  have eb := (Leasy par2.2.2.2.1 (paraeasy2 par2).2.2.1),
  have := sas len (M2 a b) (by linarith [M3 (B1 Bdae).2.2.2.1.symm eb]),
  rcases line_of_ne eb with ⟨P, eP, bP⟩,
  have := angeqpar eb (Leasy aN bN).symm (Leasy par.1 (paraeasy2 par).2.2.2.2.1) (Leasy4 bP bN) eP
    bP aN cN bO aO (by linarith [M3 eb (B1 Bdae).2.2.2.1.symm]) ⟨ecO.2.1, ecO.1, difsym ecO.2.2⟩,
  refine ⟨e, P, this, paraeasy1 par2, Bdae⟩,
end

--Euclid I.37
theorem triarea {a d b c : point} {L M : line} (par : para a d b c L M) :
  area a b c = area d b c :=
begin
  by_cases ad : a = d,
  rw ad,
  by_cases bc : b= c,
  rw bc,
  linarith [M8 a c c, M8 c a c, M8 d c c, M8 c d c, M6 c a, M6 c d],
  rcases line_of_ne (Leasy par.1 (paraeasy2 par).2.2.2.2.1) with ⟨N, aN, cN⟩,
  rcases line_of_ne (Leasy par.2.2.1 (paraeasy2 par).2.2.1) with ⟨Q, bQ, dQ⟩,
  rcases line_of_ne (Leasy par.2.1 (paraeasy2 par).2.2.2.2.1) with ⟨K, dK, cK⟩,
  rcases line_of_ne (Leasy par.1 (paraeasy2 par).2.2.2.1) with ⟨O, aO, bO⟩,
  have bN := λ bN, (paraeasy2 par).2.1 (by rwa (line_unique_of_pts bc bN cN par.2.2.1 par.2.2.2.1) at aN),
  by_cases bdN : ¬sameside b d N,
  { rcases parallelodraw ad bc aN cN par bdN with ⟨e, P, par1, par2, Bdae⟩,
    rcases parallelodraw (ne.symm ad) (ne.symm bc) dQ bQ (paraeasy3 par)
      (difsym (T1 par.2.1 dQ dK par.1 bQ cK (paraeasy2 par).2.2.2.2.2.2 (S2 (T2 par.2.2.2.1 cN cK
      par.2.2.1 aN dK (paraeasy2 par).2.2.2.2.2.1 bdN (λ dN, (paraeasy2 par1).2.1
      (B2 Bdae dN aN)) bc)))) with ⟨f, R, par3, par4, Badf⟩,
    have := parallelarea par2 (paraeasy1 par4) par1 (paraeasy1 par3),
    have := parasianar par2 par1,
    have := parasianar par4 par3,
    linarith [M8 a c b, M8 d b c], },
  push_neg at bdN,
  rcases parallelodraw (ne.symm ad) bc dK cK (paraeasy6 par) (T1 par.2.2.2.1 cK cN par.2.2.1 dK aN
    (S2 (paraeasy2 par).2.2.2.2.2.1) bdN) with ⟨e, P, par1, par2, Bade⟩,
  rcases parallelodraw ad (ne.symm bc) aO bO (paraeasy5 par) (difsym (T1 par.1 aO aN par.2.1 bO cN
    (paraeasy2 par).2.2.2.2.2.2 (S2 bdN))) with ⟨f, R, par3, par4, Bdaf⟩,
  have := parallelarea par2 (paraeasy1 par4) par1 (paraeasy1 par3),
  have := parasianar par2 par1,
  have := parasianar par4 par3,
  linarith [M8 a c b, M8 d b c],
end

--Euclid I.41
theorem paratri {a d b c e : point} {L M N K : line} (eL : online e L) (par1 : para a d b c L M)
  (par2 : para a b d c N K) : area a d c + area a b c = 2 * area b e c :=
  by linarith [parasianar (paraeasy4 par2) (paraeasy3 par1), triarea (paraeasy1 (paraeasy eL
  (paraeasy1 par1))), M8 a b c, M8 c a b, M8 e b c, M8 e c b]

--Euclid I.46
theorem drawsq {a b g : point} {L : line} (ab : a ≠ b) (aL : online a L) (bL : online b L)
  (gL : ¬online g L) : ∃ (d e : point), ∃ (M N O : line),
  square a b d e L M N O ∧  ¬sameside d g L :=
begin
  rcases excor ab.symm ab with ⟨b1, Bbab1, len⟩,
  rcases perplinecor bL (B2 Bbab1 bL aL) gL Bbab1 with ⟨c, per, per2, cgL⟩,
  rcases excor (Leasy aL (S3 cgL)).symm ab with ⟨d, Bcad, len1⟩,
  rcases excor (B1 Bcad).2.2.2.1 (B1 Bcad).2.2.2.1.symm with ⟨d1, Badd1, lend1⟩,
  rcases circle_of_ne (B1 Bcad).2.2.2.1.symm with ⟨α, dcen, acirc⟩,
  rcases line_of_ne (B1 Bcad).2.2.1 with ⟨M, cM, dM⟩,
  have gdL := difsamedif cgL ⟨S3 cgL, (λ dL, (S3 cgL) (B2 (B1 Bcad).1 dL aL)), Pa3 Bcad aL⟩,
  rcases drawpar ab aL bL gdL.2.1 with ⟨e1, N, par1⟩,
  have bM : ¬online b M,-- := λ bM, (S3 cgL) (by rw (line_unique_of_pts ab aL bL (B3 Bcad cM dM) bM) at cM; exact cM),--why is this not a proof?
  { intro bM, have := line_unique_of_pts ab aL bL (B3 Bcad cM dM) bM, rw ← this at cM; exact  (S3 cgL) cM, },
  have eex : ∃ (e : point), online e N ∧ sameside b e M ∧ oncircle e α ∧ d ≠ e,
  { rcases pts_of_line_circle_inter (Int3 (inside_circle_of_center dcen) par1.2.1) with ⟨e2, e3, e2N, e3N, e2circ, e3circ, e2e3⟩,
    have Be2de3 : B e2 d e3,
    { have same := (DS3 dcen e2circ).mpr e3circ,
      cases B6 e2N par1.2.1 e3N (λ e2d, (not_oncircle_of_inside (inside_circle_of_center dcen)) (by rwa e2d at e2circ)) e2e3
        (λ e3d, (not_oncircle_of_inside (inside_circle_of_center dcen)) (by rwa ← e3d at e3circ)),
      --- *** BAD to use junk `h` autogenerated
      exact h,
      cases h,
      have := DS1 h,
      linarith [nonzerolen e2e3],
      have := DS1 h,
      linarith [nonzerolen e2e3, flipboth same], },
    by_cases beM : sameside b e2 M,
    { refine ⟨e2, e2N, beM, e2circ, (B1 Be2de3).2.1.symm⟩, },
    have e2M : ¬online e2 M,
    { intro e2M,
      have := line_unique_of_pts (B1 Be2de3).2.1 e2M dM e2N par1.2.1,
      rw this at *,
      exact (paraeasy2 par1).2.2.2.1 (B3 Bcad cM dM), },
    have e3M := λ e3M, e2M (B2 (B1 Be2de3).1 e3M dM),
    refine ⟨e3, e3N, difdifsame ⟨e2M, bM, difsym beM⟩ ⟨e2M, e3M, Pa3 Be2de3 dM⟩, e3circ,
      (B1 Be2de3).2.2.2.1⟩, },
  rcases eex with ⟨e, eN, beM, ecirc, de⟩,
  rcases line_of_ne (Leasy eN (paraeasy2 par1).2.2.2.2.1) with ⟨O, eO, bO⟩,
  rcases line_of_ne (Leasy eN (paraeasy2 par1).2.2.2.1) with ⟨P, eP, aP⟩,
  rcases excor de.symm de with ⟨e4, Bede4, lene4⟩,
  have par := paraeasy5 (paraeasy eN (paraeasy4 par1)),
  have bdP := T1 aL aP (B3 Bcad cM dM) bL eP dM (S2 (paraeasy2 par).2.2.2.2.2.2) beM,
  have bP : ¬online b P := λ bP, (paraeasy2 (by rwa (line_unique_of_pts ab aL bL aP bP) at par)).2.2.2.2.1 eP,--works here, seems like rwa something with par and thenn doing it on par is the problem. Why?
  have dP : ¬online d P,
  { intro dP,
    have := line_unique_of_pts de par.2.2.1 eN dP eP,
    rw this at *,
    exact (paraeasy2 (by rwa (line_unique_of_pts de par.2.2.1 eN dP eP) at par)).2.1 aP, },
  have := (DS3 dcen acirc).mpr ecirc,
  have := parapostcor de eP aP (paraeasy3 par) ⟨bP, dP, bdP⟩,
  have := sas (M2 a e) (flipboth (by linarith [M2 d a] : dist d e = dist b a)).symm
    (by linarith [M3 ab.symm (Leasy eP bP).symm]),
  have par2 := angeqpar (Leasy eP bP).symm (Leasy eN (paraeasy2 par1).2.2.2.1) (Leasy aP dP)
    (Leasy4 bO bM) bO eO (B3 Bcad cM dM) dM eP aP
    (by linarith [M3 (Leasy eN (paraeasy2 par1).2.2.2.1).symm ab]) ⟨bP, dP, bdP⟩,
  have := (paraeasy (B2 Badd1 (B3 Bcad cM dM) dM) par2),
  have par3 := paraeasy6 (paraeasy1 (paraeasy (B2 Badd1 (B3 Bcad cM dM) dM) par2)),
  have := parapost (Leasy eP bP).symm eN par1.2.1 par3 (B1 Badd1).1 (B1 Bede4).1
    (paraeasy2 par1).2.2.2.2.2.2,
  have := flatsumright cM dM bM Bcad,
  have := M3 ab.symm (Leasy dM bM).symm,
  have := M3 de (Leasy dM bM),
  have := M3 (B1 Bcad).2.2.2.1 (Leasy eN (paraeasy2 par1).2.2.2.1).symm,
  have := parasianar par (paraeasy4 par2),
  refine ⟨d, e, M, N, O,⟨this.1, by linarith [M2 d a], by linarith [M2 e b, M2 a b], by linarith,
    by linarith, by linarith, by linarith, paraeasy4 par2, par⟩, difsym gdL.2.2⟩,
end

--Euclid I.47
theorem pythagorasdraw {a b c : point} {N : line} (ab : a ≠ b) (aN : online a N) (bN : online b N)
  (cN : ¬online c N) : ∃ (f g h k d e : point) (L M O P Q R S T U V W : line),
  square b a f g N W V U ∧ square c a k h M R S T ∧ square b c d e L Q P O ∧ ¬sameside f c N ∧
  ¬sameside k b M ∧ ¬sameside d a L :=
begin
  rcases line_of_ne (Leasy aN cN) with ⟨M, aM, cM⟩,
  rcases line_of_ne (Leasy bN cN) with ⟨L, bL, cL⟩,
  rcases drawsq ab.symm bN aN cN with ⟨f, g, W, V, U, sq1, fcN⟩,
  rcases drawsq (Leasy aN cN).symm cM aM (λ bM, (Leasy4 cM cN) (line_unique_of_pts ab aM bM aN bN)) with
    ⟨k, h, R, S,T, sq2, hbM⟩,
  rcases drawsq (Leasy bN cN) bL cL (λ aL, (Leasy4 cL cN) (line_unique_of_pts ab aL bL aN bN)) with
    ⟨d, e, Q, P, O, sq3, daL⟩,
  refine ⟨f, g, h, k, d, e, L, M, O, P, Q, R, S,T, U, V, W, sq1, sq2, sq3, fcN, hbM, daL⟩,
end

theorem pythlem0 {a b c d : point} {L : line} (bc : b ≠ c) (bd : b ≠ d) (bL : online b L)
  (cL : online c L) (dL : online d L) (aL : ¬online a L) (ang : angle a b c = rightangle) :
  angle a b d = rightangle :=
begin
  by_cases cd : c = d,
  rwa ← cd,
  cases B6 bL cL dL bc bd cd,
  have := A4mod1 (Leasy bL aL) h,
  have := M3 (Leasy bL aL).symm (Leasy cL aL).symm,
  have := M3 (Leasy bL aL).symm (Leasy dL aL).symm,
  linarith,
  cases h,
  have := flatsumright cL dL aL h,
  linarith,
  have := A4mod1 (Leasy bL aL) h,
  have := M3 (Leasy bL aL).symm (Leasy cL aL).symm,
  have := M3 (Leasy bL aL).symm (Leasy dL aL).symm,
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
    rcases line_of_ne (Leasy bL aL) with ⟨M, bM, aM⟩,
    have cM : ¬online c M,
    { intro cM,
      exact (Leasy4 aM aL) (line_unique_of_pts bc bL cL bM cM).symm, },
    rw mb at *,
    rcases excor (Leasy bL aL) (Leasy bL aL).symm with ⟨a1, Bbaa1, junk⟩,
    have := flatsumright bM (B2 Bbaa1 bM aM) cM Bbaa1,
    have := extangcor cM bM (B2 Bbaa1 bM aM) Bbaa1,
    have := M3 bc.symm (Leasy cL aL),
    by_cases gcM : sameside g c M,
    { by_cases gc : g = c,
      rw gc at *,
      linarith,
      have := A4mod2 (Leasy bL aL) gc bM aM bL gL cL gcM,
      have := M3 (Leasy bL aL).symm (Leasy gL aL).symm,
      linarith, },
    have hM : ¬online h M,
    { intro hM,
      exact (Leasy4 aM aL) (line_unique_of_pts (B1 Bhmg).2.1.symm bL hL bM hM).symm, },
    have gM : ¬online g M,
    { intro gM,
      exact (Leasy4 aM aL) (line_unique_of_pts (B1 Bhmg).2.2.2.1 bL gL bM gM).symm, },
    have hcM := S2 (difdifsame ⟨gM, cM, gcM⟩ ⟨gM, hM, difsym (Pa3 Bhmg bM)⟩),
    by_cases hc : h = c,
    rw hc at *,
    linarith,
    have := A4mod2 (Leasy bL aL) hc bM aM bL hL cL hcM,
    have := M3 (Leasy bL aL).symm (Leasy hL aL).symm,
    linarith, },
  have mc : m ≠ c,
  { intro mc,
    rcases line_of_ne (Leasy cL aL) with ⟨M, cM, aM⟩,
    have bM : ¬online b M,
    { intro bM,
      exact (Leasy4 aM aL) (line_unique_of_pts bc bL cL bM cM).symm, },
    rw mc at *,
    rcases excor (Leasy cL aL) (Leasy cL aL).symm with ⟨a1, Bcaa1, junk⟩,
    have := flatsumright cM (B2 Bcaa1 cM aM) bM Bcaa1,
    have := extangcor bM cM (B2 Bcaa1 cM aM) Bcaa1,
    have := M3 bc (Leasy bL aL),
    have := M3 (Leasy cL aL) bc.symm,
    by_cases gbM : sameside g b M,
    { by_cases gb : g = b,
      rw gb at *,
      linarith,
      have := A4mod2 (Leasy cL aL) gb cM aM cL gL bL gbM,
      have := M3 (Leasy cL aL).symm (Leasy gL aL).symm,
      linarith, },
    have hM : ¬online h M,
    { intro hM,
      exact (Leasy4 aM aL) (line_unique_of_pts (B1 Bhmg).2.1.symm cL hL cM hM).symm, },
    have gM : ¬online g M,
    { intro gM,
      exact (Leasy4 aM aL) (line_unique_of_pts (B1 Bhmg).2.2.2.1 cL gL cM gM).symm, },
    have hbM := S2 (difdifsame ⟨gM, bM, gbM⟩ ⟨gM, hM, difsym (Pa3 Bhmg cM)⟩),
    by_cases hb : h = b,
    rw hb at *,
    linarith,
    have := A4mod2 (Leasy cL aL) hb cM aM cL hL bL hbM,
    have := M3 (Leasy cL aL).symm (Leasy hL aL).symm,
    linarith, },
  have ang2 := pythlem0 (B1 Bhmg).2.2.2.1 mb mL gL bL aL ang1.2,
  have ang3 := pythlem0 (B1 Bhmg).2.2.2.1 mc mL gL cL aL ang1.2,
  cases B6 mL bL cL mb mc bc with Bmbc hs,
  exfalso,
  rcases excor (B1 Bmbc).2.1.symm (B1 Bmbc).2.1 with ⟨m1, Bbmm1, junk⟩,
  have := flatsumright bL (B2 Bbmm1 bL mL) aL Bbmm1,
  have := extangcor aL bL (B2 Bbmm1 bL mL) Bbmm1,
  have := flatsumright mL cL aL Bmbc,
  rcases line_of_ne (Leasy bL aL) with ⟨M, bM, aM⟩,
  have cM := λ cM, (Leasy4 aM aL) (line_unique_of_pts bc bL cL bM cM).symm,
  rcases excor (Leasy bL aL) (Leasy bL aL).symm with ⟨a1, Bbaa1, junk⟩,
  have := flatsumright bM (B2 Bbaa1 bM aM) cM Bbaa1,
  have := extangcor cM bM (B2 Bbaa1 bM aM) Bbaa1,
  have := M3 bc.symm (Leasy cL aL),
  linarith,
  cases hs.swap with Bmcb Bbmc,
  rcases excor (B1 Bmcb).2.1.symm (B1 Bmcb).2.1 with ⟨m1, Bcmm1, junk⟩,
  have := flatsumright cL (B2 Bcmm1 cL mL) aL Bcmm1,
  have := extangcor aL cL (B2 Bcmm1 cL mL) Bcmm1,
  have := flatsumright mL bL aL Bmcb,
  rcases line_of_ne (Leasy cL aL) with ⟨M, cM, aM⟩,
  have bM := λ bM, (Leasy4 aM aL) (line_unique_of_pts bc.symm cL bL cM bM).symm,
  rcases excor (Leasy cL aL) (Leasy cL aL).symm with ⟨a1, Bcaa1, junk⟩,
  have := flatsumright cM (B2 Bcaa1 cM aM) bM Bcaa1,
  have := extangcor bM cM (B2 Bcaa1 cM aM) Bcaa1,
  have := M3 bc (Leasy bL aL),
  have := M3 (Leasy bL aL) bc,
  linarith,
  refine ⟨m, ang2, ang3, Bbmc⟩,
end

--Euclid I.47
theorem pythagoras {a b c f g h k d e : point} {L M N O P Q R S T U V W : line} (bc : b ≠ c)
  (aL : ¬online a L) (ang : angle c a b = rightangle) (sq1 : square b a f g N W V U)
  (sq2 : square c a k h M R S T) (sq3 : square b c d e L Q P O) (fcN : ¬sameside f c N)
  (kbM : ¬sameside k b M) (daL : ¬sameside d a L) :
  area d b e+ area e c b = area a b f + area a g f + area a h k + area a c k :=
begin
  unfold square at sq3,
  unfold square at sq2,
  unfold square at sq1,
  have bL := (sq3.2.2.2.2.2.2.2.2).1,
  have cL := (sq3.2.2.2.2.2.2.2.2).2.1,
  have dP := (sq3.2.2.2.2.2.2.2.2).2.2.1,
  have eP := (sq3.2.2.2.2.2.2.2.2).2.2.2.1,
  have bP := (paraeasy2 sq3.2.2.2.2.2.2.2.2).2.1,
  have bN := (sq1.2.2.2.2.2.2.2.2).1,
  have aN := (sq1.2.2.2.2.2.2.2.2).2.1,
  have cM := (sq2.2.2.2.2.2.2.2.2).1,
  have aM := (sq2.2.2.2.2.2.2.2.2).2.1,
  have aU := (sq1.2.2.2.2.2.2.2.1).2.2.1,
  have gU := (sq1.2.2.2.2.2.2.2.1).2.2.2.1,
  have aT := (sq2.2.2.2.2.2.2.2.1).2.2.1,
  have hT := (sq2.2.2.2.2.2.2.2.1).2.2.2.1,
  have bW := (sq1.2.2.2.2.2.2.2.1).1,
  have fW := (sq1.2.2.2.2.2.2.2.1).2.1,
  have cR := (sq2.2.2.2.2.2.2.2.1).1,
  have kR := (sq2.2.2.2.2.2.2.2.1).2.1,
  have kM := (paraeasy2 sq2.2.2.2.2.2.2.2.2).2.2.2.1,
  have fN := (paraeasy2 sq1.2.2.2.2.2.2.2.2).2.2.2.1,
  have cP := (paraeasy2 sq3.2.2.2.2.2.2.2.2).2.2.1,
  have ec := (Leasy eP cP),
  have db := (Leasy dP bP),
  have dL := (paraeasy2 sq3.2.2.2.2.2.2.2.2).2.2.2.1,
  have eL := (paraeasy2 sq3.2.2.2.2.2.2.2.2).2.2.2.2.1,
  have cd := Leasy cL dL,
  have ca := (Leasy cL aL),
  have ba := (Leasy bL aL),
  have eQ := (paraeasy2 (sq3.2.2.2.2.2.2.2.1)).2.2.2.2.1,
  have dQ := (sq3.2.2.2.2.2.2.2.1).2.1,
  have bQ := (sq3.2.2.2.2.2.2.2.1).1,
  have dO := (paraeasy2 (sq3.2.2.2.2.2.2.2.1)).2.2.1,
  have eO := (sq3.2.2.2.2.2.2.2.1).2.2.2.1,
  have cO := (sq3.2.2.2.2.2.2.2.1).2.2.1,
  have de := Leasy dQ eQ,
  have bf := Leasy bN fN,
  have ck := Leasy cM kM,
  rcases pythlem bc bL cL aL (by linarith) with ⟨m, ang1, ang2, Bbmc⟩,
  have mL := (B3 Bbmc bL cL),
  have ma := (Leasy mL aL),
  have md := Leasy mL dL,
  have me := Leasy mL eL,
  rcases line_of_ne ma with ⟨X, mX, aX⟩,
  have mP := (paraeasy2 (paraeasy mL (paraeasy1 (sq3.2.2.2.2.2.2.2.2)))).2.2.2.1,
  have mQ : ¬online m Q,
  { intro mQ, have := line_unique_of_pts (B1 Bbmc).2.1 bL mL bQ mQ, rw this at *, exact dL dQ, },
  have mO : ¬online m O,
  { intro mO, have := line_unique_of_pts (B1 (B1 Bbmc).1).2.1 cL mL cO mO, rw this at *, exact eL eO, },
  have mcQ := Pa2 Bbmc bQ mQ,
  have ceQ := (paraeasy2 sq3.2.2.2.2.2.2.2.1).2.2.2.2.2.2,
  have meQ := S2 (S4 ceQ (S2 mcQ)),
  have mbP := (paraeasy2 (paraeasy mL (paraeasy1 sq3.2.2.2.2.2.2.2.2))).2.2.2.2.2.2,
  have mbO := Pa2 (B1 Bbmc).1 cO mO,
  have bdO := (paraeasy2 sq3.2.2.2.2.2.2.2.1).2.2.2.2.2.1,
  have mdO := S2 (S4 bdO (S2 mbO)),
  have mcP := (paraeasy2 (paraeasy mL (paraeasy1 (paraeasy6 sq3.2.2.2.2.2.2.2.2)))).2.2.2.2.2.2,
  have par := (paraeasy mL (paraeasy1 sq3.2.2.2.2.2.2.2.2)),
  have par1 := paraeasy mL (paraeasy1 (paraeasy6 sq3.2.2.2.2.2.2.2.2)),
  rcases perppointnon mP with ⟨p1, l, p2, p1P, lP, p2P, Bp1lp2, angs⟩,
  have lm := Leasy lP mP,
  rcases line_of_ne lm with ⟨X', lX', mX'⟩,
  have := M3 bc.symm cd,
  have dl : d ≠ l,
  { intro dl, rw ← dl at *,
    rcases excor (B1 Bbmc).2.1.symm (B1 Bbmc).2.1 with ⟨b1, Bmbb1, junk⟩,
    have := flatsumright mL (B2 Bmbb1 mL bL) dL Bmbb1,
    have := extangcor dL mL (B2 Bmbb1 mL bL) Bmbb1,
    have beX' := T1 dQ lX' dP bQ mX' eP meQ (S2 mbP),
    have bX' : ¬online b X',
    { intro bX', have := line_unique_of_pts (B1 Bmbb1).2.1 mL bL mX' bX', rw this at *, exact dL lX', },
    have eX' : ¬online e X',
    { intro eX', have := line_unique_of_pts (Leasy dQ eQ) dP eP lX' eX', rw this at *, exact mP mX', },
    have := parapostcor (B1 Bmbb1).2.1.symm mX' lX' par ⟨eX', bX', difsym beX'⟩,
    have := pythlem0 (B1 Bp1lp2).2.1.symm (Leasy dQ eQ) dP p1P eP mP (by linarith),
    have := A4mod1 db.symm Bbmc,
    have := M3 de.symm (Leasy eP mP),
    have := M3 (B1 Bbmc).2.1.symm md,
    have := M3 bc.symm cd,
    linarith, },
  have el : e ≠ l,
  { intro el,
    rw ← el at *,
    rcases excor (B1 (B1 Bbmc).1).2.1.symm (B1 (B1 Bbmc).1).2.1 with ⟨b1, Bmcc1, junk⟩,
    have := flatsumright mL (B2 Bmcc1 mL cL) eL Bmcc1,
    have := extangcor eL mL (B2 Bmcc1 mL cL) Bmcc1,
    have cdX' := T1 eO lX' eP cO mX' dP mdO (S2 mcP),
    have cX' : ¬online c X',
    { intro cX', have := line_unique_of_pts (B1 Bmcc1).2.1 mL cL mX' cX', rw this at *, exact eL lX', },
    have dX' : ¬online d X',
    { intro dX', have := line_unique_of_pts (Leasy eO dO) eP dP lX' dX', rw this at *, exact mP mX', },
    have := parapostcor (B1 Bmcc1).2.1.symm mX' lX' (paraeasy6 par1) ⟨dX', cX', difsym cdX'⟩,
    have := pythlem0 (B1 Bp1lp2).2.1.symm (Leasy eO dO) eP p1P dP mP (by linarith),
    have := A4mod1 ec.symm (B1 Bbmc).1,
    have := M3 de (Leasy dP mP),
    have := M3 (B1 (B1 Bbmc).1).2.1.symm me,
    linarith, },
  have eX' : ¬online e X',
  { intro eX', have := line_unique_of_pts el eP lP eX' lX', rw this at *, exact mP mX', },
  have dX' : ¬online d X',
  { intro dX', have := line_unique_of_pts dl dP lP dX' lX', rw this at *, exact mP mX', },
  have := M3 de cd.symm,
  have := M3 lm.symm md,
  have := M3 lm.symm me,
  have ang4 := pythlem0 (B1 Bp1lp2).2.1.symm el.symm lP p1P eP mP angs.1,
  have ang3 := pythlem0 (B1 Bp1lp2).2.1.symm dl.symm lP p1P dP mP angs.1,
  have ang5 := pythlem0 de dl dP eP lP bP sq3.2.2.2.2.2.1,
  have ang6 := pythlem0 de.symm el eP dP lP cP (by linarith),--sq3.2.2.2.2.2.2.1
  rcases excor lm.symm lm with ⟨l', Bmll', junk⟩,
  have := flatsumright mX' (B2 Bmll' mX' lX') dX' Bmll',
  have := flatsumright mX' (B2 Bmll' mX' lX') eX' Bmll',
  have mbP := (paraeasy2 par).2.2.2.2.2.2,
  have mcP := (paraeasy2 par1).2.2.2.2.2.2,
  have ml'P := Pa3 Bmll' lP,
  have bl'P := difsamedif mbP ⟨mP, (λ l'P, mP (B2 (B1 Bmll').1 l'P lP)), ml'P⟩,
  have cl'P := difsamedif mcP ⟨mP, (λ l'P, mP (B2 (B1 Bmll').1 l'P lP)), ml'P⟩,
  have par2 := paraeasy mX' (paraeasy5 (angeqpar db.symm dl (B1 Bmll').2.2.2.1 (Leasy4 dQ dX')
    bQ dQ lX' (B2 Bmll' mX' lX') dP lP (by linarith) bl'P)),
  have par3 := paraeasy mX' (paraeasy5 (angeqpar ec.symm el (B1 Bmll').2.2.2.1 (Leasy4 eO eX')
    cO eO lX' (B2 Bmll' mX' lX') eP lP (by linarith) cl'P)),
  have par4 := paraeasy3 (paraeasy lP (paraeasy4 par)),
  have par5 := paraeasy5 (paraeasy lP (paraeasy1 par1)),
  have := parasianar par4 par2,
  have := parasianar par5 par3,
  have := DS1 Bbmc,
  have := parasianar (paraeasy4 par4) (paraeasy5 (paraeasy6 par2)),
  have := M3 (B1 Bbmc).2.1 ba,
  have := M3 (B1 Bbmc).2.1 (Leasy lP bP).symm,
  have Blma := rightimpflat (B1 Bbmc).2.1 bL mL (difsamedif (paraeasy2 par4).2.2.2.2.2.2
    ⟨dL, aL, daL⟩) (by linarith),
  have Bdle := DS1rev dl el.symm de dP lP eP (by linarith [M2 m c, M2 e l]),
  have := (line_unique_of_pts ma mX aX mX' (B2 Blma lX' mX')),
  rw ← this at *,
  have cN : ¬online c N,
  { intro cN, have := line_unique_of_pts bc bL cL bN cN, rw this at *, exact aL aN, },
  have fgN := (paraeasy2 sq1.2.2.2.2.2.2.2.2).2.2.2.2.2.2,
  have UM : U = M,
  { have := rightimpflat ba bN aN (difsamedif fgN ⟨S3 fgN, cN, fcN⟩) (by linarith [M3 ba bc]),
    exact line_unique_of_pts (B1 this).2.2.2.1 aU (B2 this gU aU) aM cM, },
    have khM := (paraeasy2 sq2.2.2.2.2.2.2.2.2).2.2.2.2.2.2, --hkM
    have bM : ¬online b M, { intro bM, have := line_unique_of_pts bc bL cL bM cM, rw this at *, exact aL aM, },
  have TN : T = N,
  { have := rightimpflat ca cM aM (difsamedif khM ⟨S3 khM, bM, kbM⟩) (by linarith [M3 ca bc.symm]),
    exact line_unique_of_pts (B1 this).2.2.2.1 aT (B2 this hT aT) aN bN, },
  rw TN at *,
  rw UM at *,
  have ang1 : angle a b d = angle f b c,
  { have par7 := paraeasy cM (paraeasy5 sq1.2.2.2.2.2.2.2.1),
    have caW := (paraeasy2 par7).2.2.2.2.2.2,
    have faL := T2 bW bN bL fW aN cL (S2 caW) fcN cN bf.symm, --(S2 caW) ⟨cN, S3 fgN, S2 cN⟩,
    have := A2mprmod bf bc bW fW bL cL faL caW,
    have par6 := paraeasy aX (paraeasy5 par2),
    have dmN := T2 bQ bL bN dQ mL aN (S2 (paraeasy2 par6).2.2.2.2.2.2) daL aL db,
    rcases quadiag db ma dQ bQ mX aX bN aN (S2 (paraeasy2 par6).2.2.2.2.2.1)
      (S2 (paraeasy2 par6).2.2.2.2.2.2) dmN with
      ⟨y,Y1,Y2, dY1, aY1, bY2, mY2,yY1,yY2, Bbym, Bayd, mY1, bY1, aY2, dY2⟩,
    have yQ : ¬online y Q,
    { intro yQ, have := line_unique_of_pts (B1 Bayd).2.2.2.1 yY1 dY1 yQ dQ, rw this at *, exact bY1 bQ, },
    have yN : ¬online y N,
    { intro yN, have := line_unique_of_pts (B1 Bayd).2.1 aY1 yY1 aN yN, rw this at *, exact bY1 bN, },
    have := A2mprmod ba db.symm bN aN bQ dQ (S2 (Pa2 (B1 Bayd).1 dQ yQ)) (S2 (Pa2 Bayd aN yN)),
    have := A4mod1 ba (B4 Bbmc Bbym),
    have := A4mod1 db.symm (B4 Bbmc Bbym),
    have := M3 ba.symm (B1 Bayd).2.1,
    have := M3 ba.symm ca.symm,
    linarith, },
  have ang2 : angle a c e = angle k c b,
  { have par8 := paraeasy bN (paraeasy5 sq2.2.2.2.2.2.2.2.1),
    have baR := (paraeasy2 par8).2.2.2.2.2.2,
    have kaL := T2 cR cM cL kR aM bL (S2 baR) kbM bM ck.symm, --(S2 caW) ⟨cN, S3 fgN, S2 cN⟩,
    have := A2mprmod ck bc.symm cR kR cL bL kaL baR,
    have par9 := paraeasy aX (paraeasy5 par3),
    have eaL := difsamedif (S2 (paraeasy2 par).2.2.2.2.2.1) ⟨dL, aL, daL⟩,
    have emM := T2 cO cL cM eO mL aM (S2 (paraeasy2 par9).2.2.2.2.2.2) eaL.2.2 aL ec,
    rcases quadiag ec ma eO cO mX aX cM aM (S2 (paraeasy2 par9).2.2.2.2.2.1)
      (S2 (paraeasy2 par9).2.2.2.2.2.2) emM with
      ⟨y,Y1,Y2, eY1, aY1, cY2, mY2,yY1,yY2, Bcym, Baye, mY1, cY1, aY2, eY2⟩,
    have yO : ¬online y O,
    { intro yO, have := line_unique_of_pts (B1 Baye).2.2.2.1 yY1 eY1 yO eO, rw this at *, exact cY1 cO, },
    have yM : ¬online y M,
    { intro yM, have := line_unique_of_pts (B1 Baye).2.1 aY1 yY1 aM yM, rw this at *, exact cY1 cM, },
    have := A2mprmod ca ec.symm cM aM cO eO (S2 (Pa2 (B1 Baye).1 eO yO)) (S2 (Pa2 Baye aM yM)),
    have := A4mod1 ca (B4 (B1 Bbmc).1 Bcym),
    have := A4mod1 ec.symm (B4 (B1 Bbmc).1 Bcym),
    have := M3 ca.symm (B1 Baye).2.1,
    have := M3 ca.symm ba.symm,
    linarith, },
  have := sas sq1.2.1 sq3.2.1.symm ang1,
  have := M9 sq1.2.1 this.1 (flipboth sq3.2.1.symm) this.2.1 ang1 this.2.2,
  have := sas sq2.2.1 (flip2 sq3.2.2.1.symm) ang2,
  have := M9 sq2.2.1 this.1 (flip1 sq3.2.2.1.symm) this.2.1 ang2 this.2.2,
  have := paratri cM (paraeasy4 sq1.2.2.2.2.2.2.2.1) (paraeasy3 sq1.2.2.2.2.2.2.2.2),
  have := paratri bN (paraeasy4 sq2.2.2.2.2.2.2.2.1) (paraeasy3 sq2.2.2.2.2.2.2.2.2),
  have := paratri aX (paraeasy4 par2) (paraeasy3 par4),
  have := paratri aX (paraeasy4 par3) (paraeasy3 par5),
  have := quadext bL cL dP eP cO eO Bbmc Bdle (paraeasy2 sq3.2.2.2.2.2.2.2.2).2.2.2.2.2.1
    (S2 (paraeasy2 par).2.2.2.2.2.1) bdO,
  have := quadarea (B1 Bbmc).2.1 (B1 Bdle).2.1 bL mL dP lP mX lX' (S2 mbP)
    (paraeasy2 par4).2.2.2.2.2.2 (paraeasy2 par2).2.2.2.2.2.1,
  have := quadarea (B1 (B1 Bbmc).1).2.1 (B1 (B1 Bdle).1).2.1 cL mL eP lP mX lX' (S2 mcP)
    (paraeasy2 par5).2.2.2.2.2.2 (paraeasy2 par3).2.2.2.2.2.1,
  linarith [M8 b c f, M8 c b k, M8 l d b, M8 l b d, M8 l m b, M8 b l m],
end
