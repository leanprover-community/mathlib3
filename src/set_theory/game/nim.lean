/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import set_theory.game.impartial
import set_theory.ordinal
import data.set
import logic.basic

universes u v

/-!
# Nim and the Sprague-Grundy theorem

This file contains the definition for nim for any ordinal `O`. In the game of `nim O₁` both players
may move to `nim O₂` for any `O₂ < O₁`.
We also define a Grundy value for an impartial game `G` and prove the Sprague-Grundy theorem, that
`G` is equivalent to `nim (Grundy_value G)`.

## Implementation details

The pen-and-paper definition of nim defines the possible moves of `nim O` to be `{ O' | O' < O}`.
However, this definition does not work for us because it would make the type of nim
`ordinal.{u} → pgame.{u + 1}`, which would make it impossible for us to state the Sprague-Grundy
theorem, since that requires the type of `nim` to be `ordinal.{u} → pgame.{u}`. For this reason, we
instead use `O.out.α` for the possible moves, which makes proofs significantly more messy and
tedious, but avoids the universe bump.

-/

/-- `ordinal.out` and `ordinal.type_out'` are required to make the definition of nim computable.
 `ordinal.out` performs the same job as `quotient.out` but is specific to ordinals. -/
def ordinal.out (o : ordinal) : Well_order :=
⟨o.out.α, λ x y, o.out.r x y, o.out.wo⟩

/-- This is the same as `ordinal.type_out` but defined to use `ordinal.out`. -/
theorem ordinal.type_out' : ∀ (o : ordinal), ordinal.type (ordinal.out o).r = o := ordinal.type_out

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
 take a positive number of stones from it on their turn. -/
def nim : ordinal → pgame
| O₁ := ⟨ O₁.out.α, O₁.out.α,
  λ O₂, have hwf : (ordinal.typein O₁.out.r O₂) < O₁,
    from begin nth_rewrite_rhs 0 ←ordinal.type_out' O₁, exact ordinal.typein_lt_type _ _ end,
    nim (ordinal.typein O₁.out.r O₂),
  λ O₂, have hwf : (ordinal.typein O₁.out.r O₂) < O₁,
    from begin nth_rewrite_rhs 0 ←ordinal.type_out' O₁, exact ordinal.typein_lt_type _ _ end,
    nim (ordinal.typein O₁.out.r O₂)⟩
using_well_founded { dec_tac := tactic.assumption }

namespace pgame

local infix ` ≈ ` := equiv

namespace nim

lemma nim_def (O : ordinal) : nim O = pgame.mk O.out.α O.out.α
  (λ O₂, nim (ordinal.typein O.out.r O₂))
  (λ O₂, nim (ordinal.typein O.out.r O₂)) :=
by rw nim

lemma nim_wf_lemma {O₁ : ordinal} (O₂ : O₁.out.α) : (ordinal.typein O₁.out.r O₂) < O₁ :=
begin
  nth_rewrite_rhs 0 ← ordinal.type_out O₁,
  exact ordinal.typein_lt_type _ _
end

instance nim_impartial : ∀ (O : ordinal), impartial (nim O)
| O :=
begin
  rw [impartial_def, nim_def, neg_def],
  split,
  split,
  { rw pgame.le_def,
    split,
    { intro i,
      let hwf : (ordinal.typein O.out.r i) < O := nim_wf_lemma i,
      exact or.inl ⟨i, (@impartial.neg_equiv_self _ $ nim_impartial $ ordinal.typein O.out.r i).1⟩ },
    { intro j,
      let hwf : (ordinal.typein O.out.r j) < O := nim_wf_lemma j,
      exact or.inr ⟨j, (@impartial.neg_equiv_self _ $ nim_impartial $ ordinal.typein O.out.r j).1⟩ } },
  { rw pgame.le_def,
    split,
    { intro i,
      let hwf : (ordinal.typein O.out.r i) < O := nim_wf_lemma i,
      exact or.inl ⟨i, (@impartial.neg_equiv_self _ $ nim_impartial $ ordinal.typein O.out.r i).2⟩ },
    { intro j,
      let hwf : (ordinal.typein O.out.r j) < O := nim_wf_lemma j,
      exact or.inr ⟨j, (@impartial.neg_equiv_self _ $ nim_impartial $ ordinal.typein O.out.r j).2⟩ } },
  split,
  { intro i,
    let hwf : (ordinal.typein O.out.r i) < O := nim_wf_lemma i,
    simpa using nim_impartial (ordinal.typein O.out.r i) },
  { intro j,
    let hwf : (ordinal.typein O.out.r j) < O := nim_wf_lemma j,
    simpa using nim_impartial (ordinal.typein O.out.r j) }
end
using_well_founded { dec_tac := tactic.assumption }

lemma zero_first_loses : (nim (0 : ordinal)).first_loses :=
begin
  rw [impartial.first_loses_symm, nim_def, le_def_lt],
  split,
  { rintro (i : (0 : ordinal).out.α),
    have h := ordinal.typein_lt_type _ i,
    rw ordinal.type_out at h,
    exact false.elim (not_le_of_lt h (ordinal.zero_le (ordinal.typein _ i))) },
  { tidy }
end

lemma non_zero_first_wins (O : ordinal) (hO : O ≠ 0) : (nim O).first_wins :=
begin
  rw [impartial.first_wins_symm, nim_def, lt_def_le],
  rw ←ordinal.pos_iff_ne_zero at hO,
  exact or.inr ⟨(ordinal.principal_seg_out hO).top, by simpa using zero_first_loses.1⟩
end

lemma sum_first_loses_iff_eq (O₁ O₂ : ordinal) : (nim O₁ + nim O₂).first_loses ↔ O₁ = O₂ :=
begin
  split,
  { contrapose,
    intro h,
    rw [impartial.not_first_loses],
    wlog h' : O₁ ≤ O₂ using [O₁ O₂, O₂ O₁],
    { exact ordinal.le_total O₁ O₂ },
    { have h : O₁ < O₂ := lt_of_le_of_ne h' h,
      rw [impartial.first_wins_symm', lt_def_le, nim_def O₂],
      refine or.inl ⟨(left_moves_add (nim O₁) _).symm (sum.inr _), _⟩,
      { exact (ordinal.principal_seg_out h).top },
      { simpa using (impartial.add_self (nim O₁)).2 } },
    { exact first_wins_of_equiv add_comm_equiv (this (ne.symm h)) } },
  { rintro rfl,
    exact impartial.add_self (nim O₁) }
end

lemma sum_first_wins_iff_neq (O₁ O₂ : ordinal) : (nim O₁ + nim O₂).first_wins ↔ O₁ ≠ O₂ :=
by rw [iff_not_comm, impartial.not_first_wins, sum_first_loses_iff_eq]

lemma equiv_iff_eq (O₁ O₂ : ordinal) : nim O₁ ≈ nim O₂ ↔ O₁ = O₂ :=
⟨λ h, (sum_first_loses_iff_eq _ _).1 $
  by rw [first_loses_of_equiv_iff (add_congr h (equiv_refl _)), sum_first_loses_iff_eq],
 by { rintro rfl, refl }⟩

end nim

/-- This definition will be used in the proof of the Sprague-Grundy theorem. It takes a function
  from some type to ordinals and returns a nonempty set of ordinals with empty intersection with
  the image of the function. It is guaranteed that the smallest ordinal not in the image will be
  in the set, i.e. we can use this to find the mex. -/
def nonmoves {α : Type u} (M : α → ordinal.{u}) : set ordinal.{u} :=
  { O : ordinal | ¬ ∃ a : α, M a = O }

lemma nonmoves_nonempty {α : Type u} (M : α → ordinal.{u}) : ∃ O : ordinal, O ∈ nonmoves M :=
begin
  classical,
  by_contra h,
  simp only [nonmoves, not_exists, not_forall, set.mem_set_of_eq, not_not] at h,

  have hle : cardinal.univ.{u (u+1)} ≤ cardinal.lift.{u (u+1)} (cardinal.mk α),
  { refine ⟨⟨λ ⟨O⟩, ⟨classical.some (h O)⟩, _⟩⟩,
    rintros ⟨O₁⟩ ⟨O₂⟩ heq,
    ext,
    refine eq.trans (classical.some_spec (h O₁)).symm _,
    injection heq with heq,
    rw heq,
    exact classical.some_spec (h O₂) },

  have hlt : cardinal.lift.{u (u+1)} (cardinal.mk α) < cardinal.univ.{u (u+1)} :=
    cardinal.lt_univ.2 ⟨cardinal.mk α, rfl⟩,

  cases hlt,
  contradiction
end

/-- The Grundy value of an impartial game, the ordinal which corresponds to the game of nim that the
 game is equivalent to -/
noncomputable def grundy_value : Π (G : pgame.{u}) [G.impartial], ordinal.{u}
| G := λ hG, by exactI
    ordinal.omin (nonmoves (λ i, grundy_value (G.move_left i))) (nonmoves_nonempty _)
using_well_founded { dec_tac := pgame_wf_tac }

lemma grundy_value_def (G : pgame) [G.impartial] :
grundy_value G = ordinal.omin (nonmoves (λ i, (grundy_value (G.move_left i))))
  (nonmoves_nonempty _) :=
by { rw grundy_value, refl }

/-- The Sprague-Grundy theorem which states that every impartial game is equivalent to a game of
 nim, namely the game of nim corresponding to the games Grundy value -/
theorem equiv_nim_grundy_value : ∀ (G : pgame.{u}) [G.impartial], by exactI G ≈ nim (grundy_value G)
| G :=
begin
  classical,
  introI hG,
  rw [impartial.equiv_iff_sum_first_loses, ←impartial.no_good_left_moves_iff_first_loses],
  intro i,
  equiv_rw left_moves_add G (nim (grundy_value G)) at i,
  cases i with i₁ i₂,
  { rw add_move_left_inl,
    apply first_wins_of_equiv
     (add_congr (equiv_nim_grundy_value (G.move_left i₁)).symm (equiv_refl _)),
    rw nim.sum_first_wins_iff_neq,
    intro heq,
    rw [eq_comm, grundy_value_def G] at heq,
    have h := ordinal.omin_mem
      (nonmoves (λ (i : G.left_moves), grundy_value (G.move_left i))) (nonmoves_nonempty _),
    rw heq at h,
    have hcontra : ∃ (i' : G.left_moves),
      (λ (i'' : G.left_moves), grundy_value (G.move_left i'')) i' = grundy_value (G.move_left i₁) :=
      ⟨i₁, rfl⟩,
    contradiction },
  { rw [add_move_left_inr, ←impartial.good_left_move_iff_first_wins],
    revert i₂,
    rw nim.nim_def,
    intro i₂,

    have h' : ∃ i : G.left_moves, (grundy_value (G.move_left i)) =
      ordinal.typein (quotient.out (grundy_value G)).r i₂,
    { have hlt : ordinal.typein (quotient.out (grundy_value G)).r i₂ <
        ordinal.type (quotient.out (grundy_value G)).r := ordinal.typein_lt_type _ _,
      rw ordinal.type_out at hlt,
      revert i₂ hlt,
      rw grundy_value_def,
      intros i₂ hlt,
      have hnotin : ordinal.typein (quotient.out (ordinal.omin
          (nonmoves (λ i, grundy_value (G.move_left i))) _)).r i₂ ∉
        (nonmoves (λ (i : G.left_moves), grundy_value (G.move_left i))),
      { intro hin,
        have hge := ordinal.omin_le hin,
        have hcontra := (le_not_le_of_lt hlt).2,
        contradiction },
      simpa [nonmoves] using hnotin },

    cases h' with i hi,
    use (left_moves_add _ _).symm (sum.inl i),
    rw [add_move_left_inl, move_left_mk],
    apply first_loses_of_equiv
      (add_congr (equiv_symm (equiv_nim_grundy_value (G.move_left i))) (equiv_refl _)),
    simpa only [hi] using impartial.add_self (nim (grundy_value (G.move_left i))) }
end
using_well_founded { dec_tac := pgame_wf_tac }

lemma equiv_nim_iff_grundy_value_eq {G : pgame.{u}} (hG : impartial G) (O : ordinal) :
  G ≈ nim O ↔ grundy_value G = O :=
⟨by { intro h, rw ←nim.equiv_iff_eq, exact equiv_trans (equiv_symm (equiv_nim_grundy_value G)) h },
 by { rintro rfl, exact equiv_nim_grundy_value G }⟩

lemma nim.grundy_value (O : ordinal.{u}) : grundy_value (nim O) = O :=
by rw ←equiv_nim_iff_grundy_value_eq

end pgame
