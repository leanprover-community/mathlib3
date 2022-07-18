/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import data.list.alist
import set_theory.ordinal.arithmetic

/-!
# Cantor normal form

The Cantor normal form of an ordinal is generally defined as its base `ω` expansion, with its
non-zero exponents in decreasing order. Here, we more generally define a base `b` expansion
`ordinal.CNF` in this manner, which is well-behaved for any `b ≥ 2`.

# Implementation notes

We implement `ordinal.CNF` as an association list, where keys are exponents and values are
coefficients. This is because this structure intrinsically reflects two key properties of the Cantor
normal form:

- It is ordered.
- It has finitely many entries.

We special-case `CNF 0 o = CNF 1 o = [(0, o)]` for `o ≠ 0`. This guarantees that various basic
theorems are unconditionally true:

- The exponents are decreasing.
- All coefficients are positive.
- The sum of `b ^ e * c` over the exponents and coefficients `(e, c)` is the original ordinal.

# Todo

- Add API for the coefficients of the Cantor normal form.
- Prove the basic results relating the CNF to the arithmetic operations on ordinals.
-/

noncomputable theory

universe u

open list order

namespace ordinal

/-- Inducts on the base `b` expansion of an ordinal. -/
@[pp_nodot, elab_as_eliminator] noncomputable def CNF_rec {C : ordinal → Sort*} (b : ordinal)
  (H0 : C 0) (H : ∀ o, 0 < o → C (o % b ^ log b o) → C o) : ∀ o, C o
| o := if ho : o = 0 then by rwa ho else
        let ho' := ordinal.pos_iff_ne_zero.2 ho, hwf := mod_opow_log_lt_self b ho' in
          H o ho' $ CNF_rec $ o % b ^ log b o
using_well_founded {dec_tac := `[assumption]}

@[simp] theorem CNF_rec_zero {C : ordinal → Sort*} (b : ordinal)
  (H0 : C 0) (H : ∀ o, 0 < o → C (o % b ^ log b o) → C o) : @CNF_rec C b H0 H 0 = H0 :=
by { rw [CNF_rec, dif_pos rfl], refl }

theorem CNF_rec_pos {o : ordinal} {C : ordinal → Sort*} (ho : 0 < o) (b : ordinal)
  (H0 : C 0) (H : ∀ o, 0 < o → C (o % b ^ log b o) → C o) :
  @CNF_rec C b H0 H o = H o ho (@CNF_rec C b H0 H _) :=
by rw [CNF_rec, dif_neg ho.ne']

/-- The Cantor normal form as an association list, without the proof that its keys are not
duplicate. See `CNF` for the Cantor normal form as an `alist`. -/
@[pp_nodot] def CNF_list (b o : ordinal) : list (sigma (λ x : ordinal, ordinal)) :=
CNF_rec b [] (λ o h0 l, ⟨log b o, o / b ^ log b o⟩ :: l) o

@[simp] theorem CNF_list_zero (b : ordinal) : CNF_list b 0 = [] := CNF_rec_zero _ _ _

/-- Recursive definition for the Cantor normal form. -/
theorem CNF_list_ne_zero {b o : ordinal} (ho : 0 < o) :
  CNF_list b o = ⟨log b o, o / b ^ log b o⟩ :: CNF_list b (o % b ^ log b o) :=
CNF_rec_pos ho _ _ _

theorem zero_CNF_list {o : ordinal} (ho : 0 < o) : CNF_list 0 o = [⟨0, o⟩] :=
by simp [CNF_list_ne_zero ho]

theorem one_CNF_list {o : ordinal} (ho : 0 < o) : CNF_list 1 o = [⟨0, o⟩] :=
by simp [CNF_list_ne_zero ho]

theorem CNF_list_of_le_one {b o : ordinal} (hb : b ≤ 1) (ho : 0 < o) : CNF_list b o = [⟨0, o⟩] :=
begin
  rcases le_one_iff.1 hb with rfl | rfl,
  { exact zero_CNF_list ho },
  { exact one_CNF_list ho }
end

theorem CNF_list_of_lt {b o : ordinal} (ho : 0 < o) (hb : o < b) : CNF_list b o = [⟨0, o⟩] :=
by simp [CNF_list_ne_zero ho, log_eq_zero hb]

theorem CNF_list_foldr (b o : ordinal) : (CNF_list b o).foldr (λ p r, b ^ p.1 * p.2 + r) 0 = o :=
CNF_rec b (by { rw CNF_list_zero, refl })
  (λ o ho IH, by rw [CNF_list_ne_zero ho, list.foldr_cons, IH, div_add_mod]) o

theorem le_log_of_mem_CNF_list {b o x : ordinal} : x ∈ (CNF_list b o).keys → x ≤ log b o :=
begin
  refine CNF_rec b _ (λ a ha H, _) o,
  { rw CNF_list_zero,
    exact false.elim },
  { rw [CNF_list_ne_zero ha, keys, map_cons, mem_cons_iff],
    rintro (rfl | h),
    { exact le_rfl },
    { exact (H h).trans (log_mono_right _ (mod_opow_log_lt_self b ha).le) } }
end

theorem le_right_of_mem_CNF_list {b o x : ordinal} (h : x ∈ (CNF_list b o).keys) : x ≤ o :=
(le_log_of_mem_CNF_list h).trans $ log_le_self _ _

theorem snd_pos_of_mem_CNF_list {b o : ordinal} {x : sigma _} : x ∈ CNF_list b o → 0 < x.2 :=
begin
  refine CNF_rec b _ _ o,
  { simp },
  { intros o ho IH,
    rcases eq_zero_or_pos b with rfl | hb,
    { rw [zero_CNF_list ho, mem_singleton],
      rintro rfl,
      exact ho },
    { rw CNF_list_ne_zero ho,
      rintro (rfl | h),
      { simp,
        rw div_pos,
        { exact opow_log_le_self _ ho },
        { exact (opow_pos _ hb).ne' } },
      { exact IH h } } }
end

theorem snd_lt_of_mem_CNF_list {b o : ordinal} (hb : 1 < b) {x : sigma _} :
  x ∈ CNF_list b o → x.2 < b :=
begin
  refine CNF_rec b _ (λ o ho IH, _) o,
  { simp },
  { rw CNF_list_ne_zero ho,
    rintro (rfl | h),
    { simpa using div_opow_log_lt o hb },
    { exact IH h } }
end

theorem CNF_list_keys_sorted (b o : ordinal) : (CNF_list b o).keys.sorted (>) :=
begin
  refine CNF_rec b _ (λ o ho IH, _) o,
  { simp },
  { cases le_or_lt b 1 with hb hb,
    { simp [CNF_list_of_le_one hb ho] },
    { cases lt_or_le o b with hob hbo,
      { simp [CNF_list_of_lt ho hob] },
      { rw [CNF_list_ne_zero ho, keys, map_cons, sorted_cons],
        exact ⟨λ a H, (le_log_of_mem_CNF_list H).trans_lt $
          log_mod_opow_log_lt_log_self hb ho hbo, IH⟩ } } }
end

theorem CNF_list_nodupkeys (b o : ordinal) : (CNF_list b o).nodupkeys :=
(CNF_list_keys_sorted b o).imp $ @ne_of_gt _ _

/-- The Cantor normal form of an ordinal `o` is the association list of exponents and coefficients
in the base-`b` expansion of `o`.

We special-case `CNF 0 o = CNF 1 o = [(0, o)]` for `o ≠ 0`. -/
@[pp_nodot] def CNF (b o : ordinal) : alist (λ x : ordinal, ordinal) := ⟨_, CNF_list_nodupkeys b o⟩

@[simp] theorem CNF_entries (b o : ordinal) : (CNF b o).entries = CNF_list b o := rfl

@[simp] theorem CNF_zero (b : ordinal) : CNF b 0 = ∅ := alist.ext $ CNF_list_zero b

theorem zero_CNF {o : ordinal} (ho : 0 < o) : CNF 0 o = alist.singleton 0 o :=
alist.ext $ zero_CNF_list ho

theorem one_CNF {o : ordinal} (ho : 0 < o) : CNF 1 o = alist.singleton 0 o :=
alist.ext $ one_CNF_list ho

theorem CNF_of_le_one {b o : ordinal} (hb : b ≤ 1) (ho : 0 < o) : CNF b o = alist.singleton 0 o :=
alist.ext $ CNF_list_of_le_one hb ho

theorem CNF_of_lt {b o : ordinal} (ho : 0 < o) (hb : o < b) : CNF b o = alist.singleton 0 o :=
alist.ext $ CNF_list_of_lt ho hb

theorem le_log_of_mem_CNF {b o x : ordinal} : x ∈ CNF b o → x ≤ log b o := le_log_of_mem_CNF_list

theorem le_right_of_mem_CNF {b o x : ordinal} : x ∈ CNF b o → x ≤ o := le_right_of_mem_CNF_list

/-- Evaluating the Cantor normal form of an ordinal returns the ordinal. -/
theorem CNF_foldr (b o : ordinal) : (CNF b o).foldr (λ x e c, b ^ e * c + x) 0 = o :=
CNF_list_foldr b o

/-- Every coefficient in a Cantor normal form is positive. -/
theorem pos_of_mem_CNF_lookup {b o x y : ordinal} (h : y ∈ (CNF b o).lookup x) : 0 < y :=
snd_pos_of_mem_CNF_list $ alist.mem_lookup_iff.1 h

/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
theorem lt_of_mem_CNF_lookup {b o x y : ordinal} (hb : 1 < b) (h : y ∈ (CNF b o).lookup x) :
  y < b := snd_lt_of_mem_CNF_list hb $ alist.mem_lookup_iff.1 h

end ordinal
