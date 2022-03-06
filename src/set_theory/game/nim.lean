/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel
-/
import data.nat.bitwise
import set_theory.game.impartial
import set_theory.ordinal_arithmetic

/-!
# Nim and the Sprague-Grundy theorem

This file contains the definition for nim for any ordinal `O`. In the game of `nim O₁` both players
may move to `nim O₂` for any `O₂ < O₁`.
We also define a Grundy value for an impartial game `G` and prove the Sprague-Grundy theorem, that
`G` is equivalent to `nim (grundy_value G)`.
Finally, we compute the sum of finite Grundy numbers: if `G` and `H` have Grundy values `n` and `m`,
where `n` and `m` are natural numbers, then `G + H` has the Grundy value `n xor m`.

## Implementation details

The pen-and-paper definition of nim defines the possible moves of `nim O` to be `{O' | O' < O}`.
However, this definition does not work for us because it would make the type of nim
`ordinal.{u} → pgame.{u + 1}`, which would make it impossible for us to state the Sprague-Grundy
theorem, since that requires the type of `nim` to be `ordinal.{u} → pgame.{u}`. For this reason, we
instead use `O.out.α` for the possible moves, which makes proofs significantly more messy and
tedious, but avoids the universe bump.

The lemma `nim_def` is somewhat prone to produce "motive is not type correct" errors. If you run
into this problem, you may find the lemmas `exists_ordinal_move_left_eq` and `exists_move_left_eq`
useful.

-/
universes u

/-- `ordinal.out'` has the sole purpose of making `nim` computable. It performs the same job as
  `quotient.out` but is specific to ordinals. -/
def ordinal.out' (o : ordinal) : Well_order :=
⟨o.out.α, (<), o.out.wo⟩

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
  take a positive number of stones from it on their turn. -/
def nim : ordinal → pgame
| O₁ := let f := λ O₂, have hwf : ordinal.typein O₁.out'.r O₂ < O₁ := ordinal.typein_lt_self O₂,
          nim (ordinal.typein O₁.out'.r O₂) in ⟨O₁.out'.α, O₁.out'.α, f, f⟩
using_well_founded { dec_tac := tactic.assumption }

namespace pgame

local infix ` ≈ ` := equiv

namespace nim

open ordinal

lemma nim_def (O : ordinal) : nim O = pgame.mk O.out.α O.out.α
  (λ O₂, nim (ordinal.typein (<) O₂))
  (λ O₂, nim (ordinal.typein (<) O₂)) :=
by { rw nim, refl }

instance nim_impartial : ∀ (O : ordinal), impartial (nim O)
| O :=
begin
  rw [impartial_def, nim_def, neg_def],
  split, split;
  rw pgame.le_def,
  all_goals { refine ⟨λ i, let hwf := ordinal.typein_lt_self i in _,
    λ j, let hwf := ordinal.typein_lt_self j in _⟩ },
  { exact or.inl ⟨i, (@impartial.neg_equiv_self _ $ nim_impartial $ typein (<) i).1⟩ },
  { exact or.inr ⟨j, (@impartial.neg_equiv_self _ $ nim_impartial $ typein (<) j).1⟩ },
  { exact or.inl ⟨i, (@impartial.neg_equiv_self _ $ nim_impartial $ typein (<) i).2⟩ },
  { exact or.inr ⟨j, (@impartial.neg_equiv_self _ $ nim_impartial $ typein (<) j).2⟩ },
  { exact nim_impartial (typein (<) i) },
  { exact nim_impartial (typein (<) j) }
end
using_well_founded { dec_tac := tactic.assumption }

lemma exists_ordinal_move_left_eq (O : ordinal) : ∀ i, ∃ O' < O, (nim O).move_left i = nim O' :=
by { rw nim_def, exact λ i, ⟨_, ⟨ordinal.typein_lt_self i, rfl⟩⟩ }

lemma exists_move_left_eq {O : ordinal} : ∀ O' < O, ∃ i, (nim O).move_left i = nim O' :=
by { rw nim_def, exact λ _ h, ⟨(ordinal.principal_seg_out h).top, by simp⟩ }

lemma zero_first_loses : (nim (0 : ordinal)).first_loses :=
begin
  rw [impartial.first_loses_symm, nim_def, le_def_lt],
  exact ⟨@is_empty_elim (0 : ordinal).out.α _ _, @is_empty_elim pempty _ _⟩
end

lemma non_zero_first_wins {O : ordinal} (hO : O ≠ 0) : (nim O).first_wins :=
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
(set.range M)ᶜ

lemma nonmoves_nonempty {α : Type u} (M : α → ordinal.{u}) : set.nonempty (nonmoves M) :=
⟨_, ordinal.lsub_nmem_range.{u u} M⟩

/-- The Grundy value of an impartial game, the ordinal which corresponds to the game of nim that the
 game is equivalent to -/
noncomputable def grundy_value : Π (G : pgame.{u}) [G.impartial], ordinal.{u}
| G := λ hG, by exactI Inf (nonmoves (λ i, grundy_value (G.move_left i)))
using_well_founded { dec_tac := pgame_wf_tac }

lemma grundy_value_def (G : pgame) [G.impartial] :
  grundy_value G = Inf (nonmoves (λ i, (grundy_value (G.move_left i)))) :=
by rw grundy_value

/-- The Sprague-Grundy theorem which states that every impartial game is equivalent to a game of
 nim, namely the game of nim corresponding to the games Grundy value -/
theorem equiv_nim_grundy_value : ∀ (G : pgame.{u}) [G.impartial], by exactI G ≈ nim (grundy_value G)
| G :=
begin
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
    have h := Inf_mem (nonmoves_nonempty _),
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
    { revert i₂,
      rw grundy_value_def,
      intros i₂,
      have hnotin : _ ∉ _ := λ hin, (le_not_le_of_lt (ordinal.typein_lt_self i₂)).2 (cInf_le' hin),
      simpa [nonmoves] using hnotin },

    cases h' with i hi,
    use (left_moves_add _ _).symm (sum.inl i),
    rw [add_move_left_inl, move_left_mk],
    apply first_loses_of_equiv
      (add_congr (equiv_symm (equiv_nim_grundy_value (G.move_left i))) (equiv_refl _)),
    simpa only [hi] using impartial.add_self (nim (grundy_value (G.move_left i))) }
end
using_well_founded { dec_tac := pgame_wf_tac }

lemma equiv_nim_iff_grundy_value_eq (G : pgame) [G.impartial] (O : ordinal) :
  G ≈ nim O ↔ grundy_value G = O :=
⟨by { intro h, rw ←nim.equiv_iff_eq, exact equiv_trans (equiv_symm (equiv_nim_grundy_value G)) h },
 by { rintro rfl, exact equiv_nim_grundy_value G }⟩

lemma nim.grundy_value (O : ordinal.{u}) : grundy_value (nim O) = O :=
by rw ←equiv_nim_iff_grundy_value_eq

lemma equiv_iff_grundy_value_eq (G H : pgame) [G.impartial] [H.impartial] :
  G ≈ H ↔ grundy_value G = grundy_value H :=
(equiv_congr_left.1 (equiv_nim_grundy_value H) _).trans $ equiv_nim_iff_grundy_value_eq _ _

lemma grundy_value_zero : grundy_value 0 = 0 :=
by rw [(equiv_iff_grundy_value_eq 0 (nim 0)).1 (equiv_symm nim.zero_first_loses), nim.grundy_value]

lemma equiv_zero_iff_grundy_value (G : pgame) [G.impartial] : G ≈ 0 ↔ grundy_value G = 0 :=
by rw [equiv_iff_grundy_value_eq, grundy_value_zero]

lemma grundy_value_nim_add_nim (n m : ℕ) : grundy_value (nim n + nim m) = nat.lxor n m :=
begin
  induction n using nat.strong_induction_on with n hn generalizing m,
  induction m using nat.strong_induction_on with m hm,
  rw [grundy_value_def],

  -- We want to show that `n xor m` is the smallest unreachable Grundy value. We will do this in two
  -- steps:
  -- h₀: `n xor m` is not a reachable grundy number.
  -- h₁: every Grundy number strictly smaller than `n xor m` is reachable.

  have h₀ : (nat.lxor n m : ordinal) ∈ nonmoves (λ i, grundy_value ((nim n + nim m).move_left i)),
  { -- To show that `n xor m` is unreachable, we show that every move produces a Grundy number
    -- different from `n xor m`.
    rw [nonmoves, set.mem_compl_eq, set.mem_range, not_exists],
    equiv_rw left_moves_add _ _,

    -- The move operates either on the left pile or on the right pile.
    rintro (a|a),

    all_goals
    { -- One of the piles is reduced to `k` stones, with `k < n` or `k < m`.
      obtain ⟨ok, ⟨hk, hk'⟩⟩ := nim.exists_ordinal_move_left_eq _ a,
      obtain ⟨k, rfl⟩ := ordinal.lt_omega.1 (lt_trans hk (ordinal.nat_lt_omega _)),
      replace hk := ordinal.nat_cast_lt.1 hk,

      -- Thus, the problem is reduced to computing the Grundy value of `nim n + nim k` or
      -- `nim k + nim m`, both of which can be dealt with using an inductive hypothesis.
      simp only [hk', add_move_left_inl, add_move_left_inr, id],
      rw hn _ hk <|> rw hm _ hk,

      -- But of course xor is injective, so if we change one of the arguments, we will not get the
      -- same value again.
      intro h,
      rw ordinal.nat_cast_inj at h,
      try { rw [nat.lxor_comm n k, nat.lxor_comm n m] at h },
      exact hk.ne (nat.lxor_left_inj h) } },

  have h₁ : ∀ (u : ordinal), u < nat.lxor n m →
    u ∉ nonmoves (λ i, grundy_value ((nim n + nim m).move_left i)),
  { -- Take any natural number `u` less than `n xor m`.
    intros ou hu,
    obtain ⟨u, rfl⟩ := ordinal.lt_omega.1 (lt_trans hu (ordinal.nat_lt_omega _)),
    replace hu := ordinal.nat_cast_lt.1 hu,

    -- Our goal is to produce a move that gives the Grundy value `u`.
    rw [nonmoves, set.mem_compl_eq, set.mem_range, not_not],

    -- By a lemma about xor, either `u xor m < n` or `u xor n < m`.
    have : nat.lxor u (nat.lxor n m) ≠ 0,
    { intro h, rw nat.lxor_eq_zero at h, linarith },
    rcases nat.lxor_trichotomy this with h|h|h,
    { linarith },

    -- Therefore, we can play the corresponding move, and by the inductive hypothesis the new state
    -- is `(u xor m) xor m = u` or `n xor (u xor n) = u` as required.
    { obtain ⟨i, hi⟩ := nim.exists_move_left_eq _ (ordinal.nat_cast_lt.2 h),
      refine ⟨(left_moves_add _ _).symm (sum.inl i), _⟩,
      simp only [hi, add_move_left_inl],
      rw [hn _ h, nat.lxor_assoc, nat.lxor_self, nat.lxor_zero] },
    { obtain ⟨i, hi⟩ := nim.exists_move_left_eq _ (ordinal.nat_cast_lt.2 h),
      refine ⟨(left_moves_add _ _).symm (sum.inr i), _⟩,
      simp only [hi, add_move_left_inr],
      rw [hm _ h, nat.lxor_comm, nat.lxor_assoc, nat.lxor_self, nat.lxor_zero] } },

  -- We are done!
  apply (cInf_le' h₀).antisymm,
  contrapose! h₁,
  exact ⟨_, ⟨h₁, Inf_mem (nonmoves_nonempty _)⟩⟩
end

lemma nim_add_nim_equiv {n m : ℕ} : nim n + nim m ≈ nim (nat.lxor n m) :=
by rw [equiv_nim_iff_grundy_value_eq, grundy_value_nim_add_nim]

lemma grundy_value_add (G H : pgame) [G.impartial] [H.impartial] {n m : ℕ} (hG : grundy_value G = n)
  (hH : grundy_value H = m) : grundy_value (G + H) = nat.lxor n m :=
begin
  rw [←nim.grundy_value (nat.lxor n m), ←equiv_iff_grundy_value_eq],
  refine equiv_trans _ nim_add_nim_equiv,
  convert add_congr (equiv_nim_grundy_value G) (equiv_nim_grundy_value H);
  simp only [hG, hH]
end

end pgame
