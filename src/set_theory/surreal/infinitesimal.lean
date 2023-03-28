/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.surreal.dyadic

/-!
# Infinitesimal pre-games

We define the notions of infinitesimal, small, and dicotic pre-games, and prove some basic
results.

## Main definitions

- `pgame.infinitesimal`: a pre-game between `-2 ^ (-n)` and `2 ^ (-n)` for any `n : ℕ`.
- `pgame.small`: a pre-game between `-x` and `x` for any positive numeric `x`.
- `pgame.dicotic`: a pre-game where both players can move from any nonempty position.

## Todo

- Prove the analog of `pgame.infinitesimal_iff_forall_mem_Icc` for small games.
- Show that a dicotic pre-game is small.
- Define the pre-game `↑` (in set_theory/game/pgame) and show that it's dicotic.
- Show that infinitesimal and small games are closed under addition (and multiplication?)
-/

namespace pgame

/-- A pre-game is infinitesimal when it's between `-2 ^ (-n)` and `2 ^ (-n)` for any `n : ℕ`. -/
def infinitesimal (x : pgame) : Prop :=
∀ n, x ∈ set.Ioo (-pow_half n) (pow_half n)

theorem infinitesimal.neg {x} (hx : infinitesimal x) : infinitesimal (-x) :=
λ n, by simpa [and.comm, neg_lt_iff] using hx n

theorem infinitesimal_iff_forall_mem_Icc {x : pgame} :
  x.infinitesimal ↔ ∀ n, x ∈ set.Icc (-pow_half n) (pow_half n) :=
⟨λ h n, set.Ioo_subset_Icc_self (h n), λ h n, set.Icc_subset_Ioo
  (neg_lt_neg_iff.2 $ pow_half_succ_lt_pow_half n) (pow_half_succ_lt_pow_half n) $ h _⟩

/-- A pre-game is small when it's between `-x` and `x` for any positive numeric pre-game `x`. -/
def small (x : pgame) : Prop :=
∀ y, numeric y → 0 < y → x ∈ set.Ioo (-y) y

theorem small.infinitesimal {x} (h : small x) : infinitesimal x :=
λ n, h _ (numeric_pow_half n) (pow_half_pos n)

theorem zero_small : small 0 :=
λ y oy hy, ⟨neg_lt_zero_iff.2 hy, hy⟩

theorem zero_infinitesimal : infinitesimal 0 :=
zero_small.infinitesimal

theorem small.neg {x} (hx : small x) : small (-x) :=
λ n, by simpa [and.comm, neg_lt_iff] using hx n

/-- A pre-game is dicotic when both players can move from any nonempty position.
Equivalently, either none or both of its left and right move sets are empty, and all options are
also dicotic. -/
def dicotic_aux : pgame → Prop
| x := (is_empty x.left_moves ↔ is_empty x.right_moves) ∧
    (∀ i, dicotic_aux (x.move_left i)) ∧ ∀ j, dicotic_aux (x.move_right j)
using_well_founded { dec_tac := pgame_wf_tac }

lemma dicotic_aux_def {x : pgame} : x.dicotic_aux ↔
  (is_empty x.left_moves ↔ is_empty x.right_moves) ∧
  (∀ i, dicotic_aux (x.move_left i)) ∧ ∀ j, dicotic_aux (x.move_right j) :=
by rw dicotic_aux

/-- A typeclass on dicotic games. -/
class dicotic (x : pgame) : Prop := (out : dicotic_aux x)

lemma dicotic_iff_aux {x : pgame} : x.dicotic ↔ x.dicotic_aux :=
⟨λ h, h.1, λ h, ⟨h⟩⟩

lemma dicotic_def {x : pgame} : x.dicotic ↔
  (is_empty x.left_moves ↔ is_empty x.right_moves) ∧
  (∀ i, dicotic (x.move_left i)) ∧ ∀ j, dicotic (x.move_right j) :=
by simpa only [dicotic_iff_aux] using dicotic_aux_def

theorem is_empty_moves_iff {x : pgame} [h : x.dicotic] :
  is_empty x.left_moves ↔ is_empty x.right_moves :=
(dicotic_def.1 h).1

theorem nonempty_moves_iff {x : pgame} [h : x.dicotic] :
  nonempty x.left_moves ↔ nonempty x.right_moves :=
by { rw ←not_iff_not, simp [is_empty_moves_iff] }

instance move_left_dicotic {x : pgame} [h : x.dicotic] (i : x.left_moves) :
  (x.move_left i).dicotic :=
(dicotic_def.1 h).2.1 i

instance move_right_dicotic {x : pgame} [h : x.dicotic] (j : x.right_moves) :
  (x.move_right j).dicotic :=
(dicotic_def.1 h).2.2 j

@[priority 100] instance dicotic_of_is_empty_moves (x : pgame)
  [hl : is_empty x.left_moves] [hr : is_empty x.right_moves] : x.dicotic :=
begin
  rw dicotic_def,
  simp only [hl, hr, iff_self, true_and],
  exact ⟨is_empty_elim, is_empty_elim⟩
end

theorem zero_dicotic : dicotic 0 := by apply_instance

instance star_dicotic : star.dicotic :=
by { rw dicotic_def, simpa using zero_dicotic }

theorem dicotic_congr : ∀ {x y : pgame} (e : relabelling x y) [x.dicotic], y.dicotic
| x y ⟨L, R, hL, hR⟩ := begin
  introI h,
  refine dicotic_def.2 ⟨_, λ i, _, λ j, _⟩,
  { rw [←L.is_empty_congr, ←R.is_empty_congr, is_empty_moves_iff] },
  { rw ←L.apply_symm_apply i,
    exact dicotic_congr (hL _) },
  { rw ←R.apply_symm_apply j,
    exact dicotic_congr (hR _) }
end
using_well_founded { dec_tac := pgame_wf_tac }

instance dicotic_add : ∀ (x y : pgame) [x.dicotic] [y.dicotic], (x + y).dicotic
| x y := begin
  introsI hx hy,
  rw dicotic_def,
  simp only [left_moves_add, right_moves_add, is_empty_sum],
  rw [is_empty_moves_iff, is_empty_moves_iff],
  refine ⟨iff.rfl, _, _⟩,
  { intro i,
    apply left_moves_add_cases i;
    { intro j,
      simpa using dicotic_add _ _ } },
  { intro i,
    apply right_moves_add_cases i;
    { intro j,
      simpa using dicotic_add _ _ } }
end
using_well_founded { dec_tac := pgame_wf_tac }

instance dicotic_neg : ∀ (x : pgame) [x.dicotic], (-x).dicotic
| x := begin
  introI h,
  rw dicotic_def,
  simp only [left_moves_neg, right_moves_neg, move_left_neg', move_right_neg'],
  exact ⟨is_empty_moves_iff.symm, λ i, dicotic_neg _, λ j, dicotic_neg _⟩
end
using_well_founded { dec_tac := pgame_wf_tac }

end pgame
