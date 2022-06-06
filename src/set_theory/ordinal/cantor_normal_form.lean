/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Violeta Hernández Palacios
-/

import set_theory.ordinal.arithmetic

/-!
# Cantor Normal Form

The Cantor normal form of an ordinal is generally defined as its base `ω` expansion, with its
non-zero exponents in decreasing order. Here, we more generally define a base `b` expansion
`ordinal.CNF` in this manner, for any `b ≥ 2`.

# Todo

- Add API for the coefficients of the Cantor normal form.
- Prove the basic results relating the CNF to the arithmetic operations on ordinals.
-/

noncomputable theory

universe u

namespace ordinal

variables {a b o : ordinal.{u}} {p : ordinal.{u} × ordinal.{u}}

/-- We don't make this the main definition, since having `o` as the last argument makes it much
harder for the definition to elaborate. -/
@[elab_as_eliminator] private noncomputable def CNF_rec_aux (hb : b ≠ 0) {C : ordinal → Sort*}
  (H0 : C 0) (H : ∀ a, a ≠ 0 → C (a % b ^ log b a) → C a) : ∀ o, C o
| o :=
  if ho : o = 0 then by rwa ho else
  have _, from mod_opow_log_lt_self hb ho,
  H o ho (CNF_rec_aux (o % b ^ log b o))
using_well_founded {dec_tac := `[assumption]}

/-- Inducts on the base `b` expansion of an ordinal. -/
@[elab_as_eliminator] noncomputable def CNF_rec (o) (hb : b ≠ 0) {C : ordinal → Sort*} (H0 : C 0)
  (H : ∀ a, a ≠ 0 → C (a % b ^ log b a) → C a) : C o :=
CNF_rec_aux hb H0 H o

@[simp] theorem CNF_rec_zero {C H0 H} (hb) : @CNF_rec b 0 hb C H0 H = H0 :=
by { rw [CNF_rec, CNF_rec_aux, dif_pos rfl], refl }

theorem CNF_rec_ne_zero {C H0 H} (hb ho) :
  @CNF_rec b o hb C H0 H = H o ho (@CNF_rec b _ hb C H0 H) :=
by { rw [CNF_rec, CNF_rec_aux, dif_neg ho], refl }

/-- The Cantor normal form of an ordinal `o` is the list of coefficients and exponents in the
    base-`b` expansion of `o`.

    We special-case `CNF 0 o = []`, `CNF b 0 = []`, and `CNF 1 o = [(0, o)]` for `o ≠ 0`.

    `CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)]` -/
@[pp_nodot] def CNF (b o : ordinal) : list (ordinal × ordinal) :=
if hb : b = 0 then [] else
CNF_rec o hb [] (λ a ha IH, (log b a, a / b ^ log b a) :: IH)

@[simp] theorem zero_CNF (o) : CNF 0 o = [] :=
dif_pos rfl

@[simp] theorem CNF_zero (b) : CNF b 0 = [] :=
if hb : b = 0 then dif_pos hb else (dif_neg hb).trans $ CNF_rec_zero _

/-- Recursive definition for the Cantor normal form. -/
theorem CNF_ne_zero (hb : b ≠ 0) (ho : o ≠ 0) :
  CNF b o = (log b o, o / b ^ log b o) :: CNF b (o % b ^ log b o) :=
by { unfold CNF, rw [dif_neg hb, dif_neg hb, CNF_rec_ne_zero hb ho] }

theorem one_CNF (ho : o ≠ 0) : CNF 1 o = [(0, o)] :=
by rw [CNF_ne_zero ordinal.one_ne_zero ho, log_of_not_one_lt_left (irrefl _), opow_zero, mod_one,
       CNF_zero, div_one]

theorem mem_one_CNF (hp : p ∈ CNF 1 o) : p = ⟨0, o⟩ :=
begin
  rcases eq_or_ne o 0 with rfl | ho,
  { rw CNF_zero at hp,
    exact hp.elim },
  { rwa [one_CNF ho, list.mem_singleton] at hp }
end

/-- Evaluating the Cantor normal form of an ordinal returns the ordinal. -/
theorem CNF_foldr (hb : b ≠ 0) (o) : (CNF b o).foldr (λ p r, b ^ p.1 * p.2 + r) 0 = o :=
CNF_rec o hb (by { rw CNF_zero, refl })
  (λ a ha IH, by rw [CNF_ne_zero hb ha, list.foldr_cons, IH, div_add_mod])

/-- Every term in the Cantor normal form of `o` is less or equal to `o`. -/
theorem le_self_of_mem_CNF : p ∈ CNF b o → b ^ p.1 * p.2 ≤ o :=
begin
  rcases eq_or_ne b 0 with rfl | hb, { simp },
  apply CNF_rec o hb, { simp },
  intros a ha H hp,
  have := CNF_foldr hb a,
  rw CNF_ne_zero hb ha at hp this,
  rcases hp with rfl | hp,
  { nth_rewrite_rhs 0 ←this,
    rw [list.foldr_cons, le_add_iff_nonneg_right],
    exact ordinal.zero_le _ },
  { exact (H hp).trans (mod_le a _) }
end

/-- Every coefficient in a Cantor normal form is positive. -/
theorem CNF_snd_pos : p ∈ CNF b o → 0 < p.2 :=
begin
  rcases eq_or_ne b 0 with rfl | hb, { simp },
  apply CNF_rec o hb, { simp },
  intros a ha H hp,
  rw CNF_ne_zero hb ha at hp,
  rcases hp with rfl | hp,
  { rw div_pos_iff (opow_ne_zero _ hb),
    apply opow_log_le_self,
    rwa ordinal.pos_iff_ne_zero },
  { exact H hp }
end

/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
theorem CNF_snd_lt (hb : b ≠ 1) : p ∈ CNF b o → p.2 < b :=
begin
  rcases eq_or_ne b 0 with rfl | hb', { simp },
  apply CNF_rec o hb', { simp },
  intros a ha H hp,
  rw CNF_ne_zero hb' ha at hp,
  rcases hp with rfl | hp,
  { rw [div_lt (opow_ne_zero _ hb'), ←opow_succ],
    apply lt_opow_succ_log_self (one_lt_iff.2 ⟨hb', hb⟩) },
  { exact H hp }
end

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `log b o`. -/
theorem CNF_fst_le_log (hp : p ∈ CNF b o) : p.1 ≤ log b o :=
begin
  cases lt_or_le 1 b with hb hb,
  { have := log_mono_right b ((le_mul_left _ (CNF_snd_pos hp)).trans (le_self_of_mem_CNF hp)),
    rwa log_opow hb at this },
  { rcases le_one_iff.1 hb with rfl | rfl,
    { rw zero_CNF at hp,
      exact hp.elim },
    { rw mem_one_CNF hp,
      apply ordinal.zero_le _ } }
end

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `o`. -/
theorem CNF_fst_le (hp : p ∈ CNF b o) : p.1 ≤ o :=
(CNF_fst_le_log hp).trans (log_le_self b o)

/-- The exponents of the Cantor normal form are decreasing. -/
theorem CNF_pairwise (b o) : (CNF b o).pairwise (λ p q : _ × _, q.1 < p.1) :=
begin
  rcases eq_or_ne b 0 with rfl | hb, { simp },
  rcases eq_or_ne b 1 with rfl | hb',
  { rcases eq_or_ne o 0 with rfl | ho, { simp },
    simp [one_CNF ho] },
  apply CNF_rec o hb, { simp },
  intros a ha H,
  rw [CNF_ne_zero hb ha, list.pairwise_cons],
  refine ⟨λ c hc, lt_of_le_of_lt (CNF_fst_le_log hc) _, H⟩,
  rw ←lt_opow_iff_log_lt (one_lt_iff.2 ⟨hb, hb'⟩),
  { exact mod_lt a (opow_ne_zero _ hb) },
  { rw ordinal.pos_iff_ne_zero,
    intro h,
    rwa [h, CNF_zero] at hc }
end

/-- The exponents of the Cantor normal form are decreasing. -/
theorem CNF_sorted (b o : ordinal) : ((CNF b o).map prod.fst).sorted (>) :=
by { rw [list.sorted, list.pairwise_map], exact CNF_pairwise b o }

end ordinal
