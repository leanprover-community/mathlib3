/-
Copyright (c) 2022 Jakub Kądziołka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakub Kądziołka
-/
import data.nat.fib.basic
import algebra.big_operators.order
import tactic.omega.main
import tactic.linarith

/-!
# Zeckendorf's Theorem

`nat.zeckendorf`: Each natural number can be written in exactly one way as a sum of distinct,
non-consecutive Fibonacci numbers.
-/

open_locale big_operators

namespace nat

/-- The set `S` contains the indices which have been chosen.
    For uniqueness, we need to exclude `fib 0` and `fib 1`,
    since `fib 0 = 0` and `fib 1 = fib 2 = 1`. -/
def is_zeckendorf_rep (S : finset ℕ) : Prop :=
  ∀ (n ∈ S), n ≥ 2 ∧ n + 1 ∉ S

/-- Every natural number lies between two Fibonacci numbers. -/
lemma fib_between (n : ℕ): ∃ k : ℕ, fib k ≤ n ∧ n < fib k.succ :=
begin
  induction n using nat.two_step_induction with n IHn IHnsucc,
  { use 0, simp },
  { use 2, simp },
  { obtain ⟨k, Hfibk_around_nsucc⟩ := IHnsucc,
    by_cases Hfib_ksucc : n.succ.succ = fib k.succ,
    { use k.succ,
      have k_not_0 : k ≠ 0,
      { assume H : k = 0,
        have bad := calc n.succ.succ = fib k.succ : Hfib_ksucc
                                 ... = fib 1      : by simp [H]
                                 ... = 1          : rfl,
        cases bad },
      split,
      show fib k.succ ≤ n.succ.succ, by simp [Hfib_ksucc],
      show n.succ.succ < fib k.succ.succ,
      { rw Hfib_ksucc, apply fib_lt_fib_succ, omega } },
    { use k, split; omega } }
end

lemma is_zeckendorf_rep.mono {S T : finset ℕ}
  (HzT : is_zeckendorf_rep T)
  (Hsubset : S ⊆ T): is_zeckendorf_rep S :=
begin
  assume (n : ℕ) (HnS : n ∈ S),
  obtain ⟨Hgt2, HnconsecT⟩ : n ≥ 2 ∧ n + 1 ∉ T := HzT n (Hsubset HnS),
  have HnconsecS : n + 1 ∉ S,
  { assume (HconsecS : n + 1 ∈ S),
    have HconsecT : n + 1 ∈ T := Hsubset HconsecS,
    contradiction },
  tauto
end

lemma is_zeckendorf_rep.insert
  (S : finset ℕ) (Hzeckendorf : is_zeckendorf_rep S)
  (n : ℕ) (Hle_n : ∀ i ∈ S, i ≤ n):
  is_zeckendorf_rep (insert (n + 2) S) :=
begin
  assume (i : ℕ) (Hi : i ∈ insert (n + 2) S),
  rw finset.mem_insert at Hi, cases Hi,
  /- Hi : i = n + 2 -/
  { rewrite Hi at *,
    have no_n_plus_3 : n + 3 ∉ S,
    { assume n_plus_3 : n + 3 ∈ S,
      have bad : n + 3 ≤ n := Hle_n (n + 3) n_plus_3,
      linarith },
    finish },
  /- Hi : i ∈ S -/
  { obtain ⟨ge2, nconsec⟩ : i ≥ 2 ∧ i + 1 ∉ S := Hzeckendorf i Hi,
    have not_new : i + 1 ≠ n + 2,
    { have le_n : i ≤ n := Hle_n i Hi, linarith },
    finish }
end

lemma zeckendorf_bound_base_case
  (S : finset ℕ) (Hzeckendorf : is_zeckendorf_rep S)
  (n : ℕ) (Hle_n : ∀ i ∈ S, i ≤ n)
  (Hlt2 : n < 2):
  S.sum fib < fib n.succ :=
begin
  suffices Hempty : S = ∅, by simp [Hempty, fib_pos],
  apply finset.eq_empty_of_forall_not_mem,
  assume (i : ℕ) (Hi : i ∈ S),
  have ge_2: i ≥ 2 := (Hzeckendorf i Hi).elim_left,
  have Hbad: i ≤ n := Hle_n i Hi,
  linarith
end

#find strict_mono

/-- If we use Fibonacci numbers with indexes less than `n`, the sum will be less than `fib n`. -/
lemma zeckendorf_bound
  (S : finset ℕ) (Hzeckendorf : is_zeckendorf_rep S)
  (n : ℕ) (Hle_n : ∀ i ∈ S, i ≤ n):
  S.sum fib < fib n.succ :=
begin
  induction n using nat.two_step_induction with n IHn IHnsucc generalizing S,
  { apply zeckendorf_bound_base_case; finish },
  { apply zeckendorf_bound_base_case; finish },
  /- Inductive case. Now we're bounded by n.succ.succ -/
  { by_cases (n.succ.succ ∈ S),
    /- Case 1: the bound is tight, i.e. `n.succ.succ ∈ S`. -/
    { let S' := S.erase n.succ.succ,
      have Hless_n_S' : ∀ i ∈ S', i ≤ n,
      { assume (i : ℕ) (Hi : i ∈ S'),
        obtain ⟨Hi_not_nsucc, Hi_in_S⟩: i ≠ n.succ.succ ∧ i ∈ S, by finish,
        have less_n_succ : i ≤ n.succ.succ := Hle_n i Hi_in_S,
        have Hi_not_n : i ≠ n.succ,
        { assume (H: i = n.succ),
          rw H at *,
          have Hno_nsucc : n.succ.succ ∉ S := (Hzeckendorf n.succ Hi_in_S).elim_right,
          contradiction },
        show i ≤ n, by omega },
      have Hzeckendorf' : is_zeckendorf_rep S',
        { apply is_zeckendorf_rep.mono Hzeckendorf, apply finset.erase_subset },
      have S_insert : S = insert n.succ.succ S', by rwa finset.insert_erase,
      have S'_no_nsucc : n.succ.succ ∉ S', by simp,
      have IH := IHn S' Hzeckendorf' Hless_n_S',
      calc ∑ k in S, fib k
          = fib (n + 2) + S'.sum fib : by rwa [S_insert, finset.sum_insert]
      ... < fib (n + 2) + fib (n + 1) : by simp [IHn S' Hzeckendorf' Hless_n_S']
      ... = fib (n + 3) : by simp [@fib_add_two (n + 1)]; ring },
    /- Case 2: the bound is not tight, i.e. `n.succ.succ ∉ S`. -/
    { calc ∑ k in S, fib k < fib (n + 2) : _
                       ... ≤ fib (n + 3) : by apply fib_mono; linarith,
      apply IHnsucc S Hzeckendorf,
      assume (i : ℕ) (Hi : i ∈ S),
      have less_n_succ : i ≤ n.succ.succ, from Hle_n i Hi,
      have not_n : i ≠ n.succ.succ, by finish,
      show i ≤ n.succ, by omega } }
end

theorem zeckendorf (n : ℕ): ∃! (S : finset ℕ), is_zeckendorf_rep S ∧ S.sum fib = n :=
begin
  induction n using nat.strong_induction_on with n IH,
  obtain ⟨i, Hless, Hmore⟩ : ∃ i, fib i ≤ n ∧ n < fib i.succ := fib_between n,
  rcases i with _|_|i,
  /- If i = 0, then n = 0. We handle this case separately. -/
  { simp at Hmore, have n0 : n = 0 := by assumption,
    rw n0 at *,
    use ∅, split,
    { tauto },
    { assume (S : finset ℕ) (H : is_zeckendorf_rep S ∧ S.sum fib = 0),
      by_contradiction Hnonempty,
      obtain ⟨m, Hm⟩ : ∃ m, m ∈ S := finset.nonempty.bex (finset.nonempty_of_ne_empty Hnonempty),
      suffices H : (0 : ℕ) > 0, cases H,
      have Hge2 : m ≥ 2 := (H.elim_left m Hm).elim_left,
      calc 0 = S.sum fib : by rw H.elim_right
      ...    ≥ fib m     : finset.single_le_sum (by intros; apply zero_le) Hm
      ...    > 0         : by apply fib_pos; linarith } },
  /- i = 1 is impossible, because the [fib i; fib i.succ) interval is empty. -/
  { finish },
  /- The general case -/
  let n' := n - fib i.succ.succ,
  have Hposfib : fib (i + 2) > 0 := by simp [fib_pos],
  have Hsmaller : n' < n := by linarith,
  obtain ⟨S', ⟨S'zeckendorf, S'sum⟩, S'unique⟩
    : ∃! (S' : finset ℕ), is_zeckendorf_rep S' ∧ S'.sum fib = n',
    from IH n' Hsmaller,
  let S := insert (i + 2) S',
  use S,
  have Hbounded : ∀ k ∈ S', k ≤ i,
  { assume (k : ℕ) (Hk : k ∈ S'),
    by_contradiction, have Hisucc : k ≥ i.succ := by omega,
    have HH :=
      calc n = n' + fib i.succ.succ         : by linarith
      ...    = S'.sum fib + fib i.succ.succ : by rw S'sum
      ...    ≥ fib k + fib i.succ.succ
                  : by simp; from finset.single_le_sum (by intros; apply zero_le) Hk
      ...    ≥ fib i.succ + fib i.succ.succ : by simp [fib_mono Hisucc]
      ...    = fib i.succ.succ.succ         : by simp [fib_add_two],
    linarith },
  have nmem_S' : i + 2 ∉ S',
  { assume Hi : i + 2 ∈ S',
    have Hle_i := Hbounded (i + 2) Hi,
    linarith },
  split, split,
  show is_zeckendorf_rep S,
  { apply is_zeckendorf_rep.insert; assumption },
  show S.sum fib = n,
  { calc S.sum fib = fib (i + 2) + S'.sum fib : by simp [nmem_S']
    ...            = fib (i + 2) + n'         : by rw S'sum
    ...            = n                        : by linarith },
  assume (S₂ : finset ℕ) (HS₂ : is_zeckendorf_rep S₂ ∧ S₂.sum fib = n),
  rcases HS₂ with ⟨S₂_rep, S₂_sum⟩,
  show S₂ = S,
  { have S₂_bounded : ∀ k ∈ S₂, k ≤ i + 2,
    { by_contra' Hbig_k,
      obtain ⟨k, k_mem, lt_k⟩ : ∃ k : ℕ, k ∈ S₂ ∧ i + 2 < k := Hbig_k,
      have H :=
        calc S₂.sum fib ≥ fib k       : finset.single_le_sum (by intros; apply zero_le) k_mem
        ...             ≥ fib (i + 3) : by apply fib_mono; omega
        ...             > n           : Hmore,
      linarith },
    have has_i_plus_2 : i + 2 ∈ S₂,
    { by_contradiction Hno_i_plus_2,
      have bounded_more : ∀ k ∈ S₂, k ≤ i + 1,
      { assume (k : ℕ) (Hk : k ∈ S₂),
        have not_i_plus_2 : k ≠ i + 2 := by finish,
        have bound : k ≤ i + 2 := S₂_bounded k Hk,
        omega },
      have H :=
        calc n = S₂.sum fib  : by rw S₂_sum
        ...    < fib (i + 2) : by apply zeckendorf_bound; assumption,
      linarith },
    let S₂' := S₂.erase (i + 2),
    have S₂'_rep : is_zeckendorf_rep S₂',
    { apply is_zeckendorf_rep.mono S₂_rep, apply finset.erase_subset },
    have H : S₂.sum fib = S₂'.sum fib + fib (i + 2) := by simp [finset.sum_erase_add, has_i_plus_2],
    have S₂'_sum : S₂'.sum fib = n' := by linarith,
    have S₂'_is_S' : S₂' = S' := by apply S'unique; tauto,
    show S₂ = S,
      calc S₂ = insert (i + 2) S₂' : by rwa finset.insert_erase
      ...     = insert (i + 2) S'  : by rw S₂'_is_S' }
end

end nat
