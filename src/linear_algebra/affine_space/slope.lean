import linear_algebra.affine_space.basic
import algebra.module.ordered

open affine_map

variables {k E PE : Type*}

section no_order

variables [field k] [add_comm_group E] [semimodule k E] [add_torsor E PE]

include E

def slope (f : k → PE) (a b : k) : E := (b - a)⁻¹ • (f b -ᵥ f a)

@[simp] lemma slope_same (f : k → PE) (a : k) : (slope f a a : E) = 0 :=
by rw [slope, sub_self, inv_zero, zero_smul]

lemma slope_symm (f : k → PE) (a b : k) : slope f a b = slope f b a :=
by rw [slope, slope, ← neg_vsub_eq_vsub_rev, smul_neg, ← neg_smul, neg_inv, neg_sub]

lemma slope_trans (f : k → PE) (a b c : k) :
  slope f a c = ((b - a) / (c - a)) • slope f a b + ((c - b) / (c - a)) • slope f b c :=
begin
  by_cases hab : a = b,
  { subst hab,
    rw [sub_self, zero_div, zero_smul, zero_add],
    by_cases hac : a = c,
    { simp [hac] },
    { rw [div_self (sub_ne_zero.2 $ ne.symm hac), one_smul] } },
  by_cases hbc : b = c, { subst hbc, simp [sub_ne_zero.2 (ne.symm hab)] },
  rw [add_comm],
  simp_rw [slope, div_eq_inv_mul, mul_smul, ← smul_add,
    smul_inv_smul' (sub_ne_zero.2 $ ne.symm hab), smul_inv_smul' (sub_ne_zero.2 $ ne.symm hbc),
    vsub_add_vsub_cancel],
end

lemma slope_eq_line_map (f : k → PE) (a b c : k) (h : a ≠ c) :
  slope f a c = line_map (slope f a b) (slope f b c) ((c - b) / (c - a)) :=
begin
  rw [slope_trans f a b c, line_map_apply, vadd_eq_add, vsub_eq_sub, smul_sub,
    sub_add_eq_add_sub, add_comm, add_sub_assoc, add_left_cancel_iff, eq_sub_iff_add_eq',
    ← add_smul, ← add_div, sub_add_sub_cancel, div_self, one_smul],
  exact sub_ne_zero.2 h.symm
end

lemma slope_of_line_map (f : k → PE) (a b r : k) :
  slope f a b = line_map (slope f b (line_map a b r)) (slope f a (line_map a b r)) r :=
begin
  obtain (rfl|hab) : a = b ∨ a ≠ b := classical.em _, { simp },
  rw [slope_symm _ a, slope_symm _ a],
  convert slope_eq_line_map f b (line_map a b r) a hab.symm using 2,
  rw [line_map_apply_ring, eq_div_iff (sub_ne_zero.2 hab), sub_mul, one_mul, mul_sub, ← sub_sub,
    sub_sub_cancel]
end

end no_order

section ordered_ring

variables [ordered_ring k] [ordered_add_comm_group E] [ordered_semimodule k E]

variables {a a' b b' : E} {r r' : k}

lemma line_map_mono_left (ha : a ≤ a') (hr : r ≤ 1) :
  line_map a b r ≤ line_map a' b r :=
begin
  simp only [line_map_apply_module],
  exact add_le_add_right (smul_le_smul_of_nonneg ha (sub_nonneg.2 hr)) _
end

lemma line_map_strict_mono_left (ha : a < a') (hr : r < 1) :
  line_map a b r < line_map a' b r :=
begin
  simp only [line_map_apply_module],
  exact add_lt_add_right (smul_lt_smul_of_pos ha (sub_pos.2 hr)) _
end

lemma line_map_mono_right (hb : b ≤ b') (hr : 0 ≤ r) :
  line_map a b r ≤ line_map a b' r :=
begin
  simp only [line_map_apply_module],
  exact add_le_add_left (smul_le_smul_of_nonneg hb hr) _
end

lemma line_map_strict_mono_right (hb : b < b') (hr : 0 < r) :
  line_map a b r < line_map a b' r :=
begin
  simp only [line_map_apply_module],
  exact add_lt_add_left (smul_lt_smul_of_pos hb hr) _
end

lemma line_map_mono_endpoints (ha : a ≤ a') (hb : b ≤ b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
  line_map a b r ≤ line_map a' b' r :=
(line_map_mono_left ha h₁).trans (line_map_mono_right hb h₀)

lemma line_map_strict_mono_endpoints (ha : a < a') (hb : b < b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
  line_map a b r < line_map a' b' r :=
begin
  rcases h₀.eq_or_lt with (rfl|h₀), { simpa },
  exact (line_map_mono_left ha.le h₁).trans_lt (line_map_strict_mono_right hb h₀)
end

lemma line_map_lt_line_map_iff_of_lt (h : r < r') :
  line_map a b r < line_map a b r' ↔ a < b :=
begin
  simp only [line_map_apply_module],
  rw [← lt_sub_iff_add_lt, add_sub_assoc, ← sub_lt_iff_lt_add', ← sub_smul, ← sub_smul,
    sub_sub_sub_cancel_left, smul_lt_smul_iff_of_pos (sub_pos.2 h)]
end

lemma left_lt_line_map_iff_lt (h : 0 < r) : a < line_map a b r ↔ a < b :=
iff.trans (by rw line_map_apply_zero) (line_map_lt_line_map_iff_of_lt h)

lemma line_map_lt_left_iff_lt (h : 0 < r) : line_map a b r < a ↔ b < a :=
@left_lt_line_map_iff_lt k (order_dual E) _ _ _ _ _ _ h

lemma line_map_lt_right_iff_lt (h : r < 1) : line_map a b r < b ↔ a < b :=
iff.trans (by rw line_map_apply_one) (line_map_lt_line_map_iff_of_lt h)

lemma right_lt_line_map_iff_lt (h : r < 1) : b < line_map a b r ↔ b < a :=
@line_map_lt_right_iff_lt k (order_dual E) _ _ _ _ _ _ h

end ordered_ring

section linear_ordered_field

variables [linear_ordered_field k] [ordered_add_comm_group E] [ordered_semimodule k E]

section

variables {a b : E} {r r' : k}

lemma line_map_le_line_map_iff_of_lt (h : r < r') :
  line_map a b r ≤ line_map a b r' ↔ a ≤ b :=
begin
  simp only [line_map_apply_module],
  rw [← le_sub_iff_add_le, add_sub_assoc, ← sub_le_iff_le_add', ← sub_smul, ← sub_smul,
    sub_sub_sub_cancel_left, smul_le_smul_iff_of_pos (sub_pos.2 h)]
end

lemma left_le_line_map_iff_le (h : 0 < r) : a ≤ line_map a b r ↔ a ≤ b :=
iff.trans (by rw line_map_apply_zero) (line_map_le_line_map_iff_of_lt h)

lemma line_map_le_left_iff_le (h : 0 < r) : line_map a b r ≤ a ↔ b ≤ a :=
@left_le_line_map_iff_le k (order_dual E) _ _ _ _ _ _ h

lemma line_map_le_right_iff_le (h : r < 1) : line_map a b r ≤ b ↔ a ≤ b :=
iff.trans (by rw line_map_apply_one) (line_map_le_line_map_iff_of_lt h)

lemma right_le_line_map_iff_le (h : r < 1) : b ≤ line_map a b r ↔ b ≤ a :=
@line_map_le_right_iff_le k (order_dual E) _ _ _ _ _ _ h

end

variables {f : k → E} {a b r : k}

lemma map_le_line_map_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
  f (line_map a b r) ≤ line_map (f a) (f b) r ↔ slope f a (line_map a b r) ≤ slope f a b :=
by simp_rw [line_map_apply, slope, vsub_eq_sub, vadd_eq_add, smul_eq_mul, add_sub_cancel, smul_sub,
  sub_le_iff_le_add, mul_inv_rev', mul_smul, ← smul_sub, ← smul_add, smul_smul, ← mul_inv_rev',
  smul_le_iff_of_pos (inv_pos.2 h), inv_inv', smul_smul,
  mul_inv_cancel_right' (right_ne_zero_of_mul h.ne'), smul_add,
  smul_inv_smul' (left_ne_zero_of_mul h.ne')]

lemma line_map_le_map_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
  line_map (f a) (f b) r ≤ f (line_map a b r) ↔ slope f a b ≤ slope f a (line_map a b r) :=
@map_le_line_map_iff_slope_le_slope_left k (order_dual E) _ _ _ f a b r h

lemma map_lt_line_map_iff_slope_lt_slope_left (h : 0 < r * (b - a)) :
  f (line_map a b r) < line_map (f a) (f b) r ↔ slope f a (line_map a b r) < slope f a b :=
lt_iff_lt_of_le_iff_le' (line_map_le_map_iff_slope_le_slope_left h)
  (map_le_line_map_iff_slope_le_slope_left h)

lemma line_map_lt_map_iff_slope_lt_slope_left (h : 0 < r * (b - a)) :
  line_map (f a) (f b) r < f (line_map a b r) ↔ slope f a b < slope f a (line_map a b r) :=
@map_lt_line_map_iff_slope_lt_slope_left k (order_dual E) _ _ _ f a b r h

lemma map_le_line_map_iff_slope_le_slope_right (h : (1 - r) * (b - a) < 0) :
  f (line_map a b r) ≤ line_map (f a) (f b) r ↔ slope f (line_map a b r) b ≤ slope f a b :=
begin
  rw [← neg_pos, neg_mul_eq_mul_neg, neg_sub] at h,
  rw [← line_map_apply_one_sub b, ← line_map_apply_one_sub (f b),
    map_le_line_map_iff_slope_le_slope_left h, slope_symm _ _ b, slope_symm _ _ b]
end

lemma line_map_le_map_iff_slope_le_slope_right (h : (1 - r) * (b - a) < 0) :
  line_map (f a) (f b) r ≤ f (line_map a b r) ↔ slope f a b ≤ slope f (line_map a b r) b :=
@map_le_line_map_iff_slope_le_slope_right k (order_dual E) _ _ _ f a b r h

lemma map_lt_line_map_iff_slope_lt_slope_right (h : (1 - r) * (b - a) < 0) :
  f (line_map a b r) < line_map (f a) (f b) r ↔ slope f (line_map a b r) b < slope f a b :=
lt_iff_lt_of_le_iff_le' (line_map_le_map_iff_slope_le_slope_right h)
  (map_le_line_map_iff_slope_le_slope_right h)

lemma line_map_lt_map_iff_slope_lt_slope_right (h : (1 - r) * (b - a) < 0) :
  line_map (f a) (f b) r < f (line_map a b r) ↔ slope f a b < slope f (line_map a b r) b :=
@map_lt_line_map_iff_slope_lt_slope_right k (order_dual E) _ _ _ f a b r h

lemma map_le_line_map_iff_slope_le_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
  f (line_map a b r) ≤ line_map (f a) (f b) r ↔
    slope f a (line_map a b r) ≤ slope f (line_map a b r) b :=
by rw [map_le_line_map_iff_slope_le_slope_left (mul_pos h₀ (sub_pos.2 hab)),
  slope_of_line_map f a b r, right_le_line_map_iff_le h₁, slope_symm _ b]

lemma line_map_le_map_iff_slope_le_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
  line_map (f a) (f b) r ≤ f (line_map a b r) ↔
    slope f (line_map a b r) b ≤ slope f a (line_map a b r) :=
@map_le_line_map_iff_slope_le_slope k (order_dual E) _ _ _ _ _ _ _ hab h₀ h₁

lemma map_lt_line_map_iff_slope_lt_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
  f (line_map a b r) < line_map (f a) (f b) r ↔
    slope f a (line_map a b r) < slope f (line_map a b r) b :=
lt_iff_lt_of_le_iff_le' (line_map_le_map_iff_slope_le_slope hab h₀ h₁)
  (map_le_line_map_iff_slope_le_slope hab h₀ h₁)

lemma line_map_lt_map_iff_slope_lt_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
  line_map (f a) (f b) r < f (line_map a b r) ↔
    slope f (line_map a b r) b < slope f a (line_map a b r) :=
@map_lt_line_map_iff_slope_lt_slope k (order_dual E) _ _ _ _ _ _ _ hab h₀ h₁

end linear_ordered_field

/-
/-- For a function `f` defined on a convex subset `D` of `ℝ`, if for any three points `x<y<z`
the slope of the secant line of `f` on `[x, y]` is less than or equal to the slope
of the secant line of `f` on `[x, z]`, then `f` is convex on `D`. This way of proving convexity
of a function is used in the proof of convexity of a function with a monotone derivative. -/
lemma convex_on_real_of_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ}
  (hf : ∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :
  convex_on s f :=

/-- For a function `f` defined on a subset `D` of `ℝ`, if `f` is convex on `D`, then for any three
points `x<y<z`, the slope of the secant line of `f` on `[x, y]` is less than or equal to the slope
of the secant line of `f` on `[x, z]`. -/
lemma convex_on.slope_mono_adjacent {s : set ℝ} {f : ℝ → ℝ} (hf : convex_on s f)
  {x y z : ℝ} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
  (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=

/-- For a function `f` defined on a convex subset `D` of `ℝ`, `f` is convex on `D` iff for any three
points `x<y<z` the slope of the secant line of `f` on `[x, y]` is less than or equal to the slope
of the secant line of `f` on `[x, z]`. -/
lemma convex_on_real_iff_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ} :
  convex_on s f ↔
  (∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :=
⟨convex_on.slope_mono_adjacent, convex_on_real_of_slope_mono_adjacent hs⟩

/-- For a function `f` defined on a convex subset `D` of `ℝ`, if for any three points `x<y<z`
the slope of the secant line of `f` on `[x, y]` is greater than or equal to the slope
of the secant line of `f` on `[x, z]`, then `f` is concave on `D`. -/
lemma concave_on_real_of_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ}
  (hf : ∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) : concave_on s f :=

/-- For a function `f` defined on a subset `D` of `ℝ`, if `f` is concave on `D`, then for any three
points `x<y<z`, the slope of the secant line of `f` on `[x, y]` is greater than or equal to the
slope of the secant line of `f` on `[x, z]`. -/
lemma concave_on.slope_mono_adjacent {s : set ℝ} {f : ℝ → ℝ} (hf : concave_on s f)
  {x y z : ℝ} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
  (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) :=


/-- For a function `f` defined on a convex subset `D` of `ℝ`, `f` is concave on `D` iff for any
three points `x<y<z` the slope of the secant line of `f` on `[x, y]` is greater than or equal to
the slope of the secant line of `f` on `[x, z]`. -/
lemma concave_on_real_iff_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ} :
  concave_on s f ↔
  (∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) :=
⟨concave_on.slope_mono_adjacent, concave_on_real_of_slope_mono_adjacent hs⟩
-/
