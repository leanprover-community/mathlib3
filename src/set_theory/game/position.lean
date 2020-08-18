/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import set_theory.pgame

/-!
# Basic definitions about who has a winning stratergy

We define `G.p_position`, `G.n_position`, `G.l_position` and `G.r_position`
for a pgame `G`, which means the second, first, left and right players
have a winning stratergy respectivly.
These are defined by inequalities which can be unfolded with, `pgame.lt_def`
and `pgame.le_def`.
-/

namespace pgame

local infix ` ≈ ` := equiv

/-- The player who goes first loses -/
def p_position (G : pgame) : Prop := G ≤ 0 ∧ 0 ≤ G

/-- The player who goes first wins -/
def n_position (G : pgame) : Prop := 0 < G ∧ G < 0

/-- The left player can always win -/
def l_position (G : pgame) : Prop := 0 < G ∧ 0 ≤ G

/-- The right player can always win -/
def r_position (G : pgame) : Prop := G ≤ 0 ∧ G < 0

theorem zero_p_postition : p_position 0 := by tidy
theorem one_l_postition : l_position 1 :=
begin
    split,
    rw lt_def_le,
    tidy
end
theorem star_n_postition : n_position star := ⟨ zero_lt_star, star_lt_zero ⟩
theorem omega_l_postition : l_position omega :=
begin
  split,
    rw lt_def_le,
    left,
    use 0,
  tidy
end

lemma position_cases (G : pgame) : G.l_position ∨ G.r_position ∨ G.p_position ∨ G.n_position :=
begin
  classical,
  by_cases hpos : 0 < G;
  by_cases hneg : G < 0;
  { try { rw not_lt at hpos },
    try { rw not_lt at hneg },
    try { left, exact ⟨ hpos, hneg ⟩ },
    try { right, left, exact ⟨ hpos, hneg ⟩ },
    try { right, right, left, exact ⟨ hpos, hneg ⟩ },
    try { right, right, right, exact ⟨ hpos, hneg ⟩ } }
end

lemma p_position_is_zero {G : pgame} : G.p_position ↔ G ≈ 0 := by refl

lemma p_position_of_equiv {G H : pgame} (h : G ≈ H) : G.p_position → H.p_position :=
λ hGp, ⟨ le_of_equiv_of_le h.symm hGp.1, le_of_le_of_equiv hGp.2 h ⟩
lemma n_position_of_equiv {G H : pgame} (h : G ≈ H) : G.n_position → H.n_position :=
λ hGn, ⟨ lt_of_lt_of_equiv hGn.1 h, lt_of_equiv_of_lt h.symm hGn.2 ⟩
lemma l_position_of_equiv {G H : pgame} (h : G ≈ H) : G.l_position → H.l_position :=
λ hGl, ⟨ lt_of_lt_of_equiv hGl.1 h, le_of_le_of_equiv hGl.2 h ⟩
lemma r_position_of_equiv {G H : pgame} (h : G ≈ H) : G.r_position → H.r_position :=
λ hGr, ⟨ le_of_equiv_of_le h.symm hGr.1, lt_of_equiv_of_lt h.symm hGr.2 ⟩

lemma p_position_of_equiv_iff {G H : pgame} (h : G ≈ H) : G.p_position ↔ H.p_position :=
⟨ p_position_of_equiv h, p_position_of_equiv h.symm ⟩
lemma n_position_of_equiv_iff {G H : pgame} (h : G ≈ H) : G.n_position ↔ H.n_position :=
⟨ n_position_of_equiv h, n_position_of_equiv h.symm ⟩
lemma l_position_of_equiv_iff {G H : pgame} (h : G ≈ H) : G.l_position ↔ H.l_position :=
⟨ l_position_of_equiv h, l_position_of_equiv h.symm ⟩
lemma r_position_of_equiv_iff {G H : pgame} (h : G ≈ H) : G.r_position ↔ H.r_position :=
⟨ r_position_of_equiv h, r_position_of_equiv h.symm ⟩

end pgame
