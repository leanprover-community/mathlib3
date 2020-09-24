import data.real.basic
import data.set.finite
import tactic.omega

open set

section real

variables {a b : ℝ}

/--
This function is an injection from natrual number to open interval
-/

noncomputable def nat_to_Ioo {a b : ℝ} (h : a < b) : ℕ → Ioo a b := λ n,
⟨(b-a) / (n+2) + a,
⟨begin
  rw [lt_add_iff_pos_left], apply div_pos,
  { exact sub_pos.mpr h },
  { norm_cast, exact (n + 1).succ_pos }
end, begin
  rw [←sub_pos, ←gt_iff_lt],
  rw calc b - ((b - a) / (n+2) + a)
      = (b - a) - (b - a) / (n+2) : by ring
  ... = (b - a) * (1 - 1 / (n+2)) : by ring,
  apply mul_pos (sub_pos.mpr h),
  rw sub_pos, rw div_lt_iff; norm_cast; omega,
end⟩⟩

lemma infinite_Ioo (h : a < b) : infinite ↥(Ioo a b) :=
begin
  apply infinite.of_injective (nat_to_Ioo h),
  intros m n H,
  rw subtype.ext_iff_val at H,
  simp only [nat_to_Ioo, add_left_inj] at H,
  rw [div_eq_div_iff] at H,
  { replace H := mul_left_cancel' _ H,
    replace H := add_right_cancel H,
    norm_cast at H, exact H.symm,
    suffices : 0 < b - a, exact ne_of_gt this,
    exact sub_pos.mpr h },
  { norm_cast, omega },
  { norm_cast, omega }
end

lemma infinite_Icc (h : a < b) : infinite ↥(Icc a b) := @infinite.of_injective _ _ (infinite_Ioo h) (inclusion Ioo_subset_Icc_self) (inclusion_injective Ioo_subset_Icc_self)


end real
