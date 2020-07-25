import set_theory.cardinal

open cardinal

lemma two_element_type_exists: ∃ α : Type, mk α = 2 := begin
  use bool,
  simp
end

def two_element_type := classical.some two_element_type_exists

lemma A : mk two_element_type = 2 := classical.some_spec two_element_type_exists

namespace cardinal

@[simp] lemma bit0_ne_zero (a : cardinal) : ¬bit0 a = 0 ↔ ¬a = 0 :=
by simp [bit0]

@[simp] lemma bit1_ne_zero (a : cardinal) : ¬bit1 a = 0 :=
by simp [bit1]

@[simp] lemma zero_lt_bit0 (a : cardinal) : 0 < bit0 a ↔ 0 < a :=
by { rw ←not_iff_not, simp [bit0], }

@[simp] lemma zero_lt_bit1 (a : cardinal) : 0 < bit1 a :=
lt_of_lt_of_le zero_lt_one (le_add_left _ _)

@[simp] lemma one_le_bit0 (a : cardinal) : 1 ≤ bit0 a ↔ 0 < a :=
⟨λ h, (zero_lt_bit0 a).mp (lt_of_lt_of_le zero_lt_one h),
 λ h, le_trans (one_le_iff_pos.mpr h) (le_add_left a a)⟩

@[simp] lemma one_le_bit1 (a : cardinal) : 1 ≤ bit1 a :=
le_add_left _ _

-- The converse is rather more difficult!
lemma bit0_le_bit0 {a b : cardinal} (h : a ≤ b) : bit0 a ≤ bit0 b :=
calc a + a ≤ a + b : add_le_add_left a h
       ... ≤ b + b : add_le_add_right b h

-- The converse is rather more difficult!
lemma bit1_le_bit1 {a b : cardinal} (h : a ≤ b) : bit1 a ≤ bit1 b :=
calc a + a + 1 ≤ a + b + 1 : add_le_add_right 1 (add_le_add_left a h)
           ... ≤ b + b + 1 : add_le_add_right 1 (add_le_add_right b h)

lemma one_lt_two : (1 : cardinal) < 2 :=
-- This strategy works generally to prove inequalities between numerals in `cardinality`.
begin
  suffices : ((1 : ℕ) : cardinal) < ((2 : ℕ) : cardinal), simpa,
  norm_cast, simp,
end

@[simp] lemma one_lt_bit0 {a : cardinal} : 1 < bit0 a ↔ 0 < a :=
begin
  split,
  { intro h,
    by_contradiction p, simp at p, subst p,
    simp at h,
    exact lt_irrefl _ (lt_trans h zero_lt_one), },
  { exact λ h, lt_of_lt_of_le one_lt_two (bit0_le_bit0 (one_le_iff_pos.mpr h)), },
end

@[simp] lemma one_lt_bit1 (a : cardinal) : 1 < bit1 a ↔ 0 < a :=
begin
  split,
  { intro h,
    by_contradiction p, simp at p, subst p,
    simp at h,
    exact lt_irrefl _ h, },
  { intro h,
    apply lt_of_lt_of_le (one_lt_bit0.2 h),
    exact le_add_right _ _, }
end

attribute [simp] zero_lt_one

end cardinal

example : (1 : cardinal) < 6 := by simp

noncomputable def B : two_element_type :=
begin
  have nz : mk two_element_type ≠ 0 := by simp [A],
  have ne := ne_zero_iff_nonempty.1 nz,
  exact ne.some,
end


-- universes u

-- open_locale classical


-- lemma bar {α : Type*} : mk α = 0 ↔ (α → false) := sorry


-- -- @[simp] lemma foo (a : cardinal) : 1 < bit0 a ↔ 0 < a := sorry
-- @[simp] lemma cardinal.zero_lt_bit0 (a : cardinal.{u}) : 0 < bit0 a ↔ 0 < a :=
-- begin
--   rw ←not_iff_not,
--   simp [bit0],
-- end

-- attribute [simp] cardinal.zero_lt_one
