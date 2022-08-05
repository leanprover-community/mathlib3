/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import data.finsupp.basic
import set_theory.ordinal.arithmetic

/-!
# Cantor Normal Form

The Cantor normal form of an ordinal is generally defined as its base `ω` expansion, with its
non-zero exponents in decreasing order. Here, we more generally define a base `b` expansion
`ordinal.CNF` in this manner, which is well-behaved for any `b ≥ 2`.

# Implementation notes

We implement `ordinal.CNF` as an association list, where keys are exponents and values are
coefficients. This is because this structure intrinsically reflects two key properties of the Cantor
normal form:

- It is ordered.
- It has finitely many entries.

# Todo

- Add API for the coefficients of the Cantor normal form.
- Prove the basic results relating the CNF to the arithmetic operations on ordinals.
-/

noncomputable theory

universe u

open order list

namespace ordinal

-- Short-circuits typeclass inference so that `quotient.decidable_eq` isn't tried first.
instance : decidable_eq ordinal := classical.dec_eq _

/-! ### Recursion principle -/

/-- Inducts on the base `b` expansion of an ordinal. -/
@[elab_as_eliminator] noncomputable def CNF_rec (b : ordinal)
  {C : ordinal → Sort*} (H0 : C 0) (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : ∀ o, C o
| o :=
  if ho : o = 0 then by rwa ho else
    let hwf := mod_opow_log_lt_self b ho in H o ho (CNF_rec (o % b ^ log b o))
using_well_founded {dec_tac := `[assumption]}

@[simp] theorem CNF_rec_zero {C : ordinal → Sort*} (b : ordinal)
  (H0 : C 0) (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : @CNF_rec b C H0 H 0 = H0 :=
by { rw [CNF_rec, dif_pos rfl], refl }

theorem CNF_rec_pos (b : ordinal) {o : ordinal} {C : ordinal → Sort*} (ho : o ≠ 0)
  (H0 : C 0) (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) :
  @CNF_rec b C H0 H o = H o ho (@CNF_rec b C H0 H _) :=
by rw [CNF_rec, dif_neg ho]

/-! ### Cantor normal form as a list -/

/-- The Cantor normal form unbundled from the proof that there's no duplicate keys. See
`ordinal.CNF` for the bundled version. -/
@[pp_nodot] def CNF_list (b o : ordinal) : list (sigma (λ x : ordinal, ordinal)) :=
CNF_rec b [] (λ o ho IH, ⟨log b o, o / b ^ log b o⟩ :: IH) o

@[simp] theorem CNF_list_zero_right (b : ordinal) : CNF_list b 0 = [] := CNF_rec_zero b _ _

theorem CNF_list_ne_zero {b o : ordinal} (ho : o ≠ 0) :
  CNF_list b o = ⟨log b o, o / b ^ log b o⟩ :: CNF_list b (o % b ^ log b o) :=
CNF_rec_pos b ho _ _

theorem CNF_list_zero_left {o : ordinal} (ho : o ≠ 0) : CNF_list 0 o = [⟨0, o⟩] :=
by simp [CNF_list_ne_zero ho]

theorem CNF_list_one {o : ordinal} (ho : o ≠ 0) : CNF_list 1 o = [⟨0, o⟩] :=
by simp [CNF_list_ne_zero ho]

theorem CNF_list_of_le_one {b o : ordinal} (hb : b ≤ 1) (ho : o ≠ 0) : CNF_list b o = [⟨0, o⟩] :=
begin
  rcases le_one_iff.1 hb with rfl | rfl,
  { exact CNF_list_zero_left ho },
  { exact CNF_list_one ho }
end

theorem CNF_list_of_lt {b o : ordinal} (ho : o ≠ 0) (hb : o < b) : CNF_list b o = [⟨0, o⟩] :=
by simp [CNF_list_ne_zero ho, log_eq_zero hb]

theorem CNF_list_foldr (b o : ordinal) : (CNF_list b o).foldr (λ p r, b ^ p.1 * p.2 + r) 0 = o :=
CNF_rec b (by { rw CNF_list_zero_right, refl })
  (λ o ho IH, by rw [CNF_list_ne_zero ho, foldr_cons, IH, div_add_mod]) o

theorem le_log_of_mem_keys_CNF_list {b o x : ordinal} : x ∈ (CNF_list b o).keys → x ≤ log b o :=
begin
  refine CNF_rec b (by simp) (λ o ho IH hx, _) o,
  rw [CNF_list_ne_zero ho, keys_cons, mem_cons_iff] at hx,
  rcases hx with rfl | hx,
  { refl },
  { exact (IH hx).trans (log_mono_right b $ mod_le _ _) }
end

theorem le_self_of_mem_keys_CNF_list {b o x : ordinal} (h : x ∈ (CNF_list b o).keys) : x ≤ o :=
(le_log_of_mem_keys_CNF_list h).trans (log_le_self b o)

theorem CNF_list_keys_sorted (b o : ordinal) : (CNF_list b o).keys.sorted (>) :=
begin
  refine CNF_rec b (by simp) (λ o ho IH, _) o,
  cases lt_or_le o b with hob hbo,
  { rw CNF_list_of_lt ho hob,
    apply sorted_singleton },
  { rw [CNF_list_ne_zero ho, keys_cons, sorted_cons],
    refine ⟨λ x hx, _, IH⟩,
    cases le_or_lt b 1 with hb hb,
    { rcases le_one_iff.1 hb with rfl | rfl;
      simpa using hx },
    { exact (le_log_of_mem_keys_CNF_list hx).trans_lt (log_mod_opow_log_lt_log_self hb ho hbo) } }
end

theorem CNF_list_nodupkeys (b o : ordinal) : (CNF_list b o).nodupkeys :=
(CNF_list_keys_sorted b o).imp (λ x y, has_lt.lt.ne')

theorem pos_of_mem_lookup_CNF_list {b o x e : ordinal} : x ∈ (CNF_list b o).lookup e → 0 < x :=
begin
  rw mem_lookup_iff (CNF_list_nodupkeys b o),
  refine CNF_rec b (by simp) (λ o ho IH, _) o,
  rw [CNF_list_ne_zero ho, mem_cons_iff],
  rintro (h | h),
  { simp only [heq_iff_eq] at h,
    rcases h with ⟨rfl, rfl⟩,
    exact div_opow_log_pos b ho },
  { exact IH h }
end

theorem zero_not_mem_lookup_CNF_list (b o e : ordinal) : (0 : ordinal) ∉ (CNF_list b o).lookup e :=
λ h, (pos_of_mem_lookup_CNF_list h).false

theorem lt_of_mem_lookup_CNF_list {b o x e : ordinal} (hb : 1 < b) :
  x ∈ (CNF_list b o).lookup e → x < b :=
begin
  rw mem_lookup_iff (CNF_list_nodupkeys b o),
  refine CNF_rec b (by simp) (λ o ho IH, _) o,
  rw [CNF_list_ne_zero ho, mem_cons_iff],
  rintro (h | h),
  { simp only [heq_iff_eq] at h,
    rcases h with ⟨rfl, rfl⟩,
    exact div_opow_log_lt o hb },
  { exact IH h }
end

/-! ### Cantor normal form as an alist -/

/-- The Cantor normal form of an ordinal `o` is the association list of exponents and coefficients
in the base-`b` expansion of `o`, ordered by decreasing exponents.

We special-case `CNF 0 o = CNF 1 o = [(0, o)]` for `o ≠ 0`. -/
@[pp_nodot] def CNF (b o : ordinal.{u}) : alist (λ x : ordinal.{u}, ordinal.{u}) :=
⟨CNF_list b o, CNF_list_nodupkeys b o⟩

@[simp] theorem CNF_entries (b o : ordinal) : (CNF b o).entries = CNF_list b o := rfl

theorem mem_CNF_iff {b o x : ordinal} : x ∈ CNF b o ↔ x ∈ (CNF_list b o).keys := iff.rfl

@[simp] theorem CNF_zero_right (b : ordinal) : CNF b 0 = ∅ := alist.ext $ CNF_list_zero_right b

/-- Recursive definition for the Cantor normal form. -/
theorem CNF_ne_zero {b o : ordinal} (ho : o ≠ 0) :
  CNF b o = alist.insert (log b o) (o / b ^ log b o) (CNF b (o % b ^ log b o)) :=
by simp_rw [CNF, CNF_list_ne_zero ho, alist.mk_cons_eq_insert]

theorem CNF_zero_left {o : ordinal} (ho : o ≠ 0) : CNF 0 o = alist.singleton 0 o :=
alist.ext $ CNF_list_zero_left ho

theorem CNF_one {o : ordinal} (ho : o ≠ 0) : CNF 1 o = alist.singleton 0 o :=
alist.ext $ CNF_list_one ho

theorem CNF_of_le_one {b o : ordinal} (hb : b ≤ 1) (ho : o ≠ 0) : CNF b o = alist.singleton 0 o :=
alist.ext $ CNF_list_of_le_one hb ho

theorem CNF_of_lt {b o : ordinal} (ho : o ≠ 0) (hb : o < b) : CNF b o = alist.singleton 0 o :=
alist.ext $ CNF_list_of_lt ho hb

/-- Evaluating the Cantor normal form of an ordinal returns the ordinal. -/
theorem CNF_foldr (b o : ordinal) : (CNF b o).foldr (λ e c r, b ^ e * c + r) 0 = o :=
CNF_list_foldr b o

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `log b o`. -/
theorem le_log_of_mem_CNF {b o x : ordinal} : x ∈ CNF b o → x ≤ log b o :=
le_log_of_mem_keys_CNF_list

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `o`. -/
theorem le_self_of_mem_CNF {b o x : ordinal} : x ∈ CNF b o → x ≤ o :=
le_self_of_mem_keys_CNF_list

/-- The exponents of the Cantor normal form are decreasing. -/
theorem CNF_keys_sorted : ∀ b o, (CNF b o).keys.sorted (>) := CNF_list_keys_sorted

/-- Every coefficient in a Cantor normal form is positive. -/
theorem pos_of_mem_lookup_CNF {b o x e : ordinal} : x ∈ (CNF b o).lookup e → 0 < x :=
pos_of_mem_lookup_CNF_list

theorem zero_not_mem_lookup_CNF : ∀ b o e, (0 : ordinal) ∉ (CNF b o).lookup e :=
zero_not_mem_lookup_CNF_list

/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
theorem lt_of_mem_lookup_CNF {b o x e : ordinal} : 1 < b → x ∈ (CNF b o).lookup e → x < b :=
lt_of_mem_lookup_CNF_list

/-! ### Coefficients of the Cantor normal form -/

/-- The finitely supported function that outputs the coefficient for a given exponent in the base
`b` expansion of an ordinal `o`. -/
@[pp_nodot] def CNF_coeff (b o : ordinal) : ordinal →₀ ordinal := alist.lookup_finsupp $ CNF b o

theorem CNF_coeff_eq_zero_iff {b o e : ordinal} : CNF_coeff b o e = 0 ↔ e ∉ CNF b o :=
begin
  rw [CNF_coeff, alist.lookup_finsupp_eq_zero_iff],
  exact or_iff_left (zero_not_mem_lookup_CNF_list b o e)
end

theorem CNF_coeff_eq_iff_of_ne_zero {b o e x : ordinal} (hx : x ≠ 0) :
  CNF_coeff b o e = x ↔ x ∈ (CNF b o).lookup e :=
by rw [CNF_coeff, alist.lookup_finsupp_eq_iff_of_ne_zero hx]

@[simp] theorem CNF_coeff_zero_right (b : ordinal) : CNF_coeff b 0 = 0 :=
by simp [CNF_coeff]

@[simp] theorem CNF_coeff_zero_left (o : ordinal) : CNF_coeff 0 o = finsupp.single 0 o :=
begin
  rcases eq_or_ne o 0 with rfl | ho,
  { simp },
  { rw [CNF_coeff, CNF_zero_left ho, alist.singleton_lookup_finsupp] }
end

@[simp] theorem CNF_coeff_one (o : ordinal) : CNF_coeff 1 o = finsupp.single 0 o :=
begin
  rcases eq_or_ne o 0 with rfl | ho,
  { simp },
  { rw [CNF_coeff, CNF_one ho, alist.singleton_lookup_finsupp] }
end

@[simp] theorem CNF_coeff_log (b o : ordinal.{u}) : CNF_coeff b o (log b o) = o / b ^ log b o :=
begin
  rcases eq_or_ne o 0 with rfl | ho,
  { simp },
  { rw [CNF_coeff_eq_iff_of_ne_zero (div_opow_log_pos b ho).ne',
      @alist.mem_lookup_iff _ (λ _, ordinal.{u}), CNF_entries, CNF_list_ne_zero ho],
    apply mem_cons_self }
end

theorem CNF_coeff_of_log_lt {b o e : ordinal} (h : log b o < e) : CNF_coeff b o e = 0 :=
CNF_coeff_eq_zero_iff.2 $ λ h', (le_log_of_mem_CNF h').not_lt h

theorem CNF_coeff_of_lt_opow {b o e : ordinal.{u}} (h : o < b ^ e) : CNF_coeff b o e = 0 :=
begin
  rcases eq_or_ne o 0 with rfl | ho,
  { simp },
  { cases le_or_lt b 1 with hb hb,
    { rcases le_one_iff.1 hb with rfl | rfl,
      { rw zero_opow' at h,
        exact (ho $ lt_one_iff_zero.1 $ h.trans_le $ sub_le_self _ _).elim },
      { rw one_opow at h,
        exact (ho $ lt_one_iff_zero.1 h).elim } },
    { exact CNF_coeff_of_log_lt ((lt_opow_iff_log_lt hb ho).1 h) } },
end

theorem CNF_coeff_of_log_ne {b o e : ordinal} (h : log b o ≠ e) :
  CNF_coeff b o e = CNF_coeff b (o % b ^ log b o) e :=
begin
  rcases eq_or_ne o 0 with rfl | ho,
  { simp },
  { simp [CNF_coeff, CNF_ne_zero ho, h.symm] }
end

theorem CNF_coeff_eq_CNF_coeff_mod_opow_gt (b o : ordinal) {e f : ordinal} (hf : e < f) :
  CNF_coeff b o e = CNF_coeff b (o % b ^ f) e :=
begin
  cases lt_or_le o (b ^ e) with h h,
  { rw [CNF_coeff_of_lt_opow h, CNF_coeff_of_lt_opow ((mod_le o _).trans_lt h)] },
  { induction f using ordinal.induction with f IH,
    intros f IH hf,
    nth_rewrite_rhs 0 CNF_coeff_of_log_ne sorry },

end

theorem CNF_coeff_eq_div_mod (b o e : ordinal) : CNF_coeff b o e = o / b ^ e % b :=
begin
  refine CNF_rec b (by simp) (λ o ho IH, _) o,


end

theorem CNF_coeff_apply_zero {b : ordinal} (o : ordinal) (hb : b ≠ 1) : CNF_coeff b o 0 = o % b :=
begin

end

end ordinal
