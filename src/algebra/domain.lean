import algebra.regular.basic

universes u v

variables {M : Type u} {N : Type v}

/-- A domain is a nontrivial ring with no zero divisors, i.e. satisfying
  the condition `a * b = 0 ↔ a = 0 ∨ b = 0`.

  This is implemented as a mixin for `ring α`.
  To obtain an integral domain use `[comm_ring α] [is_domain α]`. -/
class is_domain (M : Type u) [has_mul M] [has_zero M] extends nontrivial M : Prop :=
(regular_of_ne_zero : ∀ {c : M}, c ≠ 0 → is_regular c)

section

variables [has_mul M] [has_zero M] [is_domain M] {a b c : M}

lemma mul_left_cancel_of_ne_zero (hc : c ≠ 0) (h : c * a = c * b) : a = b :=
(is_domain.regular_of_ne_zero hc).left h

lemma mul_right_cancel_of_ne_zero (hc : c ≠ 0) (h : a * c = b * c) : a = b :=
(is_domain.regular_of_ne_zero hc).right h

lemma mul_left_cancel₀ (hc : c ≠ 0) (h : c * a = c * b) : a = b :=
(is_domain.regular_of_ne_zero hc).left h

lemma mul_right_cancel₀ (hc : c ≠ 0) (h : a * c = b * c) : a = b :=
(is_domain.regular_of_ne_zero hc).right h

lemma mul_left_injective₀ (hc : c ≠ 0) : function.injective ((*) c) :=
λ a b, mul_left_cancel₀ hc

lemma mul_right_injective₀ (hc : c ≠ 0) : function.injective (* c) :=
λ a b, mul_right_cancel₀ hc

end

namespace is_domain

@[priority 10] -- see Note [lower instance priority]
instance to_no_zero_divisors [mul_zero_class M] [is_domain M] :
  no_zero_divisors M :=
⟨λ a b h, or_iff_not_and_not.mpr $
  λ H, H.right $ mul_left_cancel_of_ne_zero H.left $ (mul_zero a).symm ▸ h⟩

-- -- @[priority 0] -- see Note [lower instance priority]
-- -- instance
-- def to_cancel_monoid_with_zero [monoid_with_zero M] [is_domain M] :
--   cancel_monoid_with_zero M :=
-- { mul_left_cancel_of_ne_zero := λ a b c, mul_left_cancel_of_ne_zero,
--   mul_right_cancel_of_ne_zero := λ a b c, mul_right_cancel_of_ne_zero,
--   .. (infer_instance : monoid_with_zero M) }

-- -- @[priority 0] -- see Note [lower instance priority]
-- -- instance
-- def to_cancel_comm_monoid_with_zero [comm_monoid_with_zero M] [is_domain M] :
--   cancel_comm_monoid_with_zero M :=
-- { .. (infer_instance : comm_monoid_with_zero M), .. is_domain.to_cancel_monoid_with_zero }

end is_domain

/-- Pullback an `is_domain` instance along an injective function. -/
protected theorem function.injective.is_domain
  {M S : Type*} [mul_zero_one_class M] [mul_zero_one_class S] [is_domain S]
  (f : M →*₀ S) (hf : function.injective f) :
  is_domain M :=
{ regular_of_ne_zero := λ x h,
  { left := λ y z (H : x * y = x * z),
      have f x * f y = f x * f z, by simp_rw [←map_mul, H],
      hf $ (mul_left_cancel_of_ne_zero $ (function.injective.ne_iff' hf f.map_zero).mpr h) this,
    right := λ y z (H : y * x = z * x),
      have f y * f x = f z * f x, by simp_rw [←map_mul, H],
      hf $ (mul_right_cancel_of_ne_zero $ (function.injective.ne_iff' hf f.map_zero).mpr h) this }
  .. pullback_nonzero f f.map_zero f.map_one }

/-- Pullback a `is_domain` instance along an injective function. -/
protected def function.injective.is_domain'
  [has_zero M] [has_mul M] [has_one M] [has_pow M ℕ] [monoid_with_zero N] [is_domain N]
  (f : M → N) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) :
  is_domain M :=
{ regular_of_ne_zero := λ c hc,
  { left := λ a b (H : c * a = c * b), hf $ mul_left_cancel₀ ((hf.ne_iff' zero).2 hc) $
    by erw [← mul, ← mul, H]; refl,
    right := λ a b (H : a * c = b * c), hf $ mul_right_cancel₀ ((hf.ne_iff' zero).2 hc) $
    by erw [← mul, ← mul, H]; refl },
  exists_pair_ne := by
  { refine ⟨0, 1, _⟩,
    apply hf.ne_iff.1,
    rw [zero, one],
    exact zero_ne_one } }

section

variables [mul_zero_class M] [is_domain M] {a b c : M}

/-- In a non-trivial integral domain, an element is regular iff it is non-zero. -/
lemma is_regular_iff_ne_zero {a : M} : is_regular a ↔ a ≠ 0 :=
⟨is_regular.ne_zero, is_domain.regular_of_ne_zero⟩

lemma mul_left_inj' (hc : c ≠ 0) : a * c = b * c ↔ a = b := ⟨mul_right_cancel₀ hc, λ h, h ▸ rfl⟩

lemma mul_right_inj' (ha : a ≠ 0) : a * b = a * c ↔ b = c := ⟨mul_left_cancel₀ ha, λ h, h ▸ rfl⟩

@[simp] lemma mul_eq_mul_right_iff : a * c = b * c ↔ a = b ∨ c = 0 :=
by by_cases hc : c = 0; [simp [hc], simp [mul_left_inj', hc]]

@[simp] lemma mul_eq_mul_left_iff : a * b = a * c ↔ b = c ∨ a = 0 :=
by by_cases ha : a = 0; [simp [ha], simp [mul_right_inj', ha]]

end

section monoid_with_zero
variables [monoid_with_zero M] [is_domain M] {a b c : M}

lemma mul_right_eq_self₀ : a * b = a ↔ b = 1 ∨ a = 0 :=
calc a * b = a ↔ a * b = a * 1 : by rw mul_one
     ...       ↔ b = 1 ∨ a = 0 : mul_eq_mul_left_iff

lemma mul_left_eq_self₀ : a * b = b ↔ a = 1 ∨ b = 0 :=
calc a * b = b ↔ a * b = 1 * b : by rw one_mul
     ...       ↔ a = 1 ∨ b = 0 : mul_eq_mul_right_iff

/-- An element of a `cancel_monoid_with_zero` fixed by right multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_right (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
classical.by_contradiction $ λ ha, h₁ $ mul_left_cancel₀ ha $ h₂.symm ▸ (mul_one a).symm

/-- An element of a `cancel_monoid_with_zero` fixed by left multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_left (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
classical.by_contradiction $ λ ha, h₁ $ mul_right_cancel₀ ha $ h₂.symm ▸ (one_mul a).symm

end monoid_with_zero

section group_with_zero
variables [group_with_zero M]

@[priority 10] -- see Note [lower instance priority]
instance group_with_zero.cancel_monoid_with_zero : is_domain M :=
{ regular_of_ne_zero := λ c hc,
  { left := λ a b (h : c * a = c * b),
    by rw [← inv_mul_cancel_left₀ hc a, h, inv_mul_cancel_left₀ hc b],
    right := λ a b (h : a * c = b * c),
    by rw [← mul_inv_cancel_right₀ hc a, h, mul_inv_cancel_right₀ hc b] } }

end group_with_zero

section
variables [comm_group_with_zero M] {a b c d : M}

@[field_simps] lemma div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
calc a / b = c / d ↔ a / b * (b * d) = c / d * (b * d) :
by rw [mul_left_inj' (mul_ne_zero hb hd)]
               ... ↔ a * d = c * b :
by rw [← mul_assoc, div_mul_cancel _ hb,
      ← mul_assoc, mul_right_comm, div_mul_cancel _ hd]

end

/-
\[cancel_monoid_with_zero (.+)\]
[monoid_with_zero $1] [is_domain $1]
-/
