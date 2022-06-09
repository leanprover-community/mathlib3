import set_theory.surreal.dyadic

namespace pgame

/-- A pre-game is infinitesimal when it's between `-2 ^ (-n)` and `2 ^ (-n)` for any `n : ℕ`. -/
def infinitesimal (x : pgame) : Prop :=
∀ n, x ∈ set.Ioo (-pow_half n) (pow_half n)

theorem infinitesimal_iff_forall_mem_Icc {x : pgame} :
  x.infinitesimal ↔ ∀ n, x ∈ set.Icc (-pow_half n) (pow_half n) :=
⟨λ h n, set.Ioo_subset_Icc_self (h n), λ h n, set.Icc_subset_Ioo
  (neg_lt_iff.2 $ pow_half_succ_lt_pow_half n) (pow_half_succ_lt_pow_half n) $ h _⟩

/-- A pre-game is strongly infinitesimal when it's between `-x` and `x` for any positive numeric
pre-game `x`. -/
def strong_infinitesimal (x : pgame) : Prop :=
∀ y, numeric y → 0 < y → x ∈ set.Ioo (-y) y

theorem strong_infinitesimal.infinitesimal {x} (h : strong_infinitesimal x) : infinitesimal x :=
λ n, h _ (numeric_pow_half n) (pow_half_pos n)

theorem zero_strong_infinitesimal : strong_infinitesimal 0 :=
λ y oy hy, ⟨neg_lt_zero_iff.2 hy, hy⟩

theorem zero_infinitesimal : infinitesimal 0 :=
zero_strong_infinitesimal.infinitesimal

/-- A pre-game is all-small when every position with left moves has right moves and viceversa.
Equivalently, either none or both of its left and right move sets are empty, and all options are
also all-small. -/
def all_small_aux : pgame → Prop
| x := (is_empty x.left_moves ↔ is_empty x.right_moves) ∧
    (∀ i, all_small_aux (x.move_left i)) ∧ ∀ j, all_small_aux (x.move_right j)
using_well_founded { dec_tac := pgame_wf_tac }

lemma all_small_aux_def {x : pgame} : x.all_small_aux ↔
  (is_empty x.left_moves ↔ is_empty x.right_moves) ∧
  (∀ i, all_small_aux (x.move_left i)) ∧ ∀ j, all_small_aux (x.move_right j) :=
by rw all_small_aux

/-- A typeclass on all-small games. -/
class all_small (x : pgame) : Prop := (out : all_small_aux x)

lemma all_small_iff_aux {x : pgame} : x.all_small ↔ x.all_small_aux :=
⟨λ h, h.1, λ h, ⟨h⟩⟩

lemma all_small_def {x : pgame} : x.all_small ↔
  (is_empty x.left_moves ↔ is_empty x.right_moves) ∧
  (∀ i, all_small (x.move_left i)) ∧ ∀ j, all_small (x.move_right j) :=
by simpa only [all_small_iff_aux] using all_small_aux_def

theorem is_empty_moves_iff {x : pgame} [h : x.all_small] :
  is_empty x.left_moves ↔ is_empty x.right_moves :=
(all_small_def.1 h).1

theorem nonempty_moves_iff {x : pgame} [h : x.all_small] :
  nonempty x.left_moves ↔ nonempty x.right_moves :=
by { rw ←not_iff_not, simp [is_empty_moves_iff] }

instance move_left_all_small {x : pgame} [h : x.all_small] (i : x.left_moves) :
  (x.move_left i).all_small :=
(all_small_def.1 h).2.1 i

instance move_right_all_small {x : pgame} [h : x.all_small] (j : x.right_moves) :
  (x.move_right j).all_small :=
(all_small_def.1 h).2.2 j

instance all_small_of_is_empty_moves (x : pgame)
  [hl : is_empty x.left_moves] [hr : is_empty x.right_moves] : x.all_small :=
begin
  rw all_small_def,
  simp only [hl, hr, iff_self, true_and],
  exact ⟨is_empty_elim, is_empty_elim⟩
end

theorem zero_all_small : all_small 0 := by apply_instance

instance star_all_small : star.all_small :=
by { rw all_small_def, simpa using zero_all_small }

theorem all_small_congr : ∀ {x y : pgame} (e : relabelling x y) [x.all_small], y.all_small
| x y ⟨L, R, hL, hR⟩ := begin
  introI h,
  refine all_small_def.2 ⟨_, _, _⟩,
  { rw [←L.is_empty_congr, ←R.is_empty_congr, is_empty_moves_iff] },
  { intro i,
    convert all_small_congr (hL (L.symm i)),
    rw equiv.apply_symm_apply },
  { exact λ j, all_small_congr (hR j) }
end
using_well_founded { dec_tac := pgame_wf_tac }

instance all_small_add : ∀ (x y : pgame) [x.all_small] [y.all_small], (x + y).all_small
| x y := begin
  introsI hx hy,
  rw all_small_def,
  simp only [left_moves_add, right_moves_add, is_empty_sum],
  rw [is_empty_moves_iff, is_empty_moves_iff],
  refine ⟨iff.rfl, _, _⟩,
  { intro i,
    apply left_moves_add_cases i;
    { intro j,
      simpa using all_small_add _ _ } },
  { intro i,
    apply right_moves_add_cases i;
    { intro j,
      simpa using all_small_add _ _ } }
end
using_well_founded { dec_tac := pgame_wf_tac }

instance all_small_neg : ∀ (x : pgame) [x.all_small], (-x).all_small
| x := begin
  introI h,
  rw all_small_def,
  simp only [left_moves_neg, right_moves_neg, move_left_neg', move_right_neg'],
  exact ⟨is_empty_moves_iff.symm, λ i, all_small_neg _, λ j, all_small_neg _⟩
end
using_well_founded { dec_tac := pgame_wf_tac }

end pgame
