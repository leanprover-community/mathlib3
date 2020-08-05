import algebra.group_with_zero

variables {α : Type*} {a b c : α}

section comm_monoid

variable [comm_monoid α]

instance comm_monoid_has_dvd : has_dvd α :=
has_dvd.mk (λ a b, ∃ c, b = a * c)

-- TODO: this used to not have c explicit, but that seems to be important
--       for use with tactics, similar to exist.intro
theorem dvd.intro (c : α) (h : a * c = b) : a ∣ b :=
exists.intro c h^.symm

alias dvd.intro ← dvd_of_mul_right_eq

theorem dvd.intro_left (c : α) (h : c * a = b) : a ∣ b :=
dvd.intro _ (begin rewrite mul_comm at h, apply h end)

alias dvd.intro_left ← dvd_of_mul_left_eq

theorem exists_eq_mul_right_of_dvd (h : a ∣ b) : ∃ c, b = a * c := h

theorem dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : ∀ c, b = a * c → P) : P :=
exists.elim H₁ H₂

theorem exists_eq_mul_left_of_dvd (h : a ∣ b) : ∃ c, b = c * a :=
dvd.elim h (assume c, assume H1 : b = a * c, exists.intro c (eq.trans H1 (mul_comm a c)))

theorem dvd.elim_left {P : Prop} (h₁ : a ∣ b) (h₂ : ∀ c, b = c * a → P) : P :=
exists.elim (exists_eq_mul_left_of_dvd h₁) (assume c, assume h₃ : b = c * a, h₂ c h₃)

@[refl, simp] theorem dvd_refl (a : α) : a ∣ a :=
dvd.intro 1 (by simp)

local attribute [simp] mul_assoc mul_comm mul_left_comm

@[trans] theorem dvd_trans (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
match h₁, h₂ with
| ⟨d, (h₃ : b = a * d)⟩, ⟨e, (h₄ : c = b * e)⟩ :=
  ⟨d * e, show c = a * (d * e), by simp [h₃, h₄]⟩
end

alias dvd_trans ← dvd.trans

@[simp] theorem one_dvd (a : α) : 1 ∣ a := dvd.intro a (by simp)

@[simp] theorem dvd_mul_right (a b : α) : a ∣ a * b := dvd.intro b rfl

@[simp] theorem dvd_mul_left (a b : α) : a ∣ b * a := dvd.intro b (by simp)

theorem dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c :=
dvd.elim h (λ d h', begin rw [h', mul_assoc], apply dvd_mul_right end)

theorem dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c * b :=
begin rw mul_comm, exact dvd_mul_of_dvd_left h _ end

theorem mul_dvd_mul : ∀ {a b c d : α}, a ∣ b → c ∣ d → a * c ∣ b * d
| a ._ c ._ ⟨e, rfl⟩ ⟨f, rfl⟩ := ⟨e * f, by simp⟩

theorem mul_dvd_mul_left (a : α) {b c : α} (h : b ∣ c) : a * b ∣ a * c :=
mul_dvd_mul (dvd_refl a) h

theorem mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c :=
mul_dvd_mul h (dvd_refl c)

theorem dvd_of_mul_right_dvd (h : a * b ∣ c) : a ∣ c :=
dvd.elim h (begin intros d h₁, rw [h₁, mul_assoc], apply dvd_mul_right end)

theorem dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c :=
dvd.elim h (λ d ceq, dvd.intro (a * d) (by simp [ceq]))

end comm_monoid

section comm_monoid_with_zero

variable [comm_monoid_with_zero α]

theorem eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0 :=
dvd.elim h (assume c, assume H' : a = 0 * c, eq.trans H' (zero_mul c))

/-- Given an element a of a commutative semiring, there exists another element whose product
    with zero equals a iff a equals zero. -/
@[simp] lemma zero_dvd_iff : 0 ∣ a ↔ a = 0 :=
⟨eq_zero_of_zero_dvd, λ h, by rw h⟩

@[simp] theorem dvd_zero (a : α) : a ∣ 0 := dvd.intro 0 (by simp)

end comm_monoid_with_zero
