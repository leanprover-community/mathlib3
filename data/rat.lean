/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Introduces the rational numbers as discrete, linear ordered field.
-/

/- linorder -/

section linear_order_cases_on
universes u v
variables {α : Type u} [decidable_linear_order α] {β : Sort v}

def linear_order_cases_on (a b : α) (h_eq : a = b → β) (h_lt : a < b → β) (h_gt : a > b → β) : β :=
if h₁ : a = b then h_eq h₁ else
  if h₂ : a < b then h_lt h₂ else h_gt ((lt_or_gt_of_ne h₁).resolve_left h₂)

variables {a b : α} {h_eq : a = b → β} {h_lt : a < b → β} {h_gt : a > b → β}

theorem linear_order_cases_on_eq (h : a = b) : linear_order_cases_on a b h_eq h_lt h_gt = h_eq h :=
dif_pos h

theorem linear_order_cases_on_lt (h : a < b) : linear_order_cases_on a b h_eq h_lt h_gt = h_lt h :=
eq.trans (dif_neg $ ne_of_lt h) $ dif_pos h

theorem linear_order_cases_on_gt (h : a > b) : linear_order_cases_on a b h_eq h_lt h_gt = h_gt h :=
eq.trans (dif_neg $ (ne_of_lt h).symm) (dif_neg $ not_lt_of_ge $ le_of_lt h)

end linear_order_cases_on

/- linorder ring -/

section ordered_ring
universes u
variables {α : Type u} [linear_ordered_ring α] {a b : α}

theorem mul_nonneg_iff_right_nonneg_of_pos (h : 0 < a) : 0 ≤ b * a ↔ 0 ≤ b :=
⟨assume : 0 ≤ b * a, nonneg_of_mul_nonneg_right this h, assume : 0 ≤ b, mul_nonneg this $ le_of_lt h⟩

end ordered_ring

/- auxiliary -/

theorem not_antimono {a b : Prop} (nb : ¬ b) (h : (a → b)) : ¬ a :=
assume ha, nb (h ha)

/- rational numbers -/

namespace rat

protected def num_denum := ℤ × {d:ℤ // d > 0}

protected def rel : rat.num_denum → rat.num_denum → Prop
| ⟨n₁, ⟨d₁, _⟩⟩ ⟨n₂, ⟨d₂, _⟩⟩ := n₁ * d₂ = n₂ * d₁

private lemma rel_trans : Π{p q r}, rat.rel p q → rat.rel q r → rat.rel p r
| ⟨n₁, ⟨d₁, _⟩⟩ ⟨n₂, ⟨d₂, _⟩⟩ ⟨n₃, ⟨d₃, _⟩⟩ :=
  assume (h₁ : n₁ * d₂ = n₂ * d₁),
  assume (h₂ : n₂ * d₃ = n₃ * d₂),
  show n₁ * d₃ = n₃ * d₁,
    from eq_of_mul_eq_mul_right (ne_of_lt ‹d₂ > 0›).symm (by cc)

instance setoid_rat.rel : setoid rat.num_denum :=
{r := rat.rel, iseqv :=
  ⟨assume ⟨_, ⟨_, _⟩⟩, rfl,
    assume  ⟨n₁, ⟨d₁, _⟩⟩ ⟨n₂, ⟨d₂, _⟩⟩ h, h.symm,
    assume a b c, rel_trans⟩}

@[simp] protected theorem rel_eq {n₁ d₁ n₂ d₂ : ℤ} { h₁ : d₁ > 0 } { h₂ : d₂ > 0 } :
  @setoid.r rat.num_denum _ (n₁, ⟨d₁, h₁⟩) (n₂, ⟨d₂, h₂⟩) = (n₁ * d₂ = n₂ * d₁) :=
rfl

end rat

def rat := quotient rat.setoid_rat.rel
notation `ℚ` := rat

namespace rat

protected def zero : ℚ := ⟦⟨0, ⟨1, zero_lt_one⟩⟩⟧

instance : has_zero ℚ := ⟨rat.zero⟩

protected def one : ℚ := ⟦⟨1, ⟨1, zero_lt_one⟩⟩⟧

instance : has_one ℚ := ⟨rat.one⟩

private def add' : rat.num_denum → rat.num_denum → ℚ
| ⟨n₁, ⟨d₁, h₁⟩⟩ ⟨n₂, ⟨d₂, h₂⟩⟩ := ⟦⟨n₁ * d₂ + n₂ * d₁, ⟨d₁ * d₂, mul_pos h₁ h₂⟩⟩⟧

protected def add : ℚ → ℚ → ℚ :=
quotient.lift₂ add' $ λ⟨n₁, ⟨d₁, h₁⟩⟩ ⟨n₂, ⟨d₂, h₂⟩⟩ ⟨n₃, ⟨d₃, h₃⟩⟩ ⟨n₄, ⟨d₄, h₄⟩⟩,
  assume (h₁ : n₁ * d₃ = n₃ * d₁) (h₂ : n₂ * d₄ = n₄ * d₂),
  quotient.sound $
  calc (n₁ * d₂ + n₂ * d₁) * (d₃ * d₄) =
          (n₁ * d₃) * d₂ * d₄ + (n₂ * d₄) * (d₁ * d₃) : by simp [mul_add, add_mul]
    ... = (n₃ * d₁) * d₂ * d₄ + (n₄ * d₂) * (d₁ * d₃) : by rw [h₁, h₂]
    ... = (n₃ * d₄ + n₄ * d₃) * (d₁ * d₂)             : by simp [mul_add, add_mul]

instance : has_add ℚ := ⟨rat.add⟩

private def neg' : rat.num_denum → ℚ
| ⟨n, d⟩ := ⟦⟨-n, d⟩⟧

protected def neg : ℚ → ℚ :=
  quotient.lift neg' $ λ⟨n₁, ⟨d₁, h₁⟩⟩ ⟨n₂, ⟨d₂, h₂⟩⟩,
  assume (h : n₁ * d₂ = n₂ * d₁),
  quotient.sound $ show (-n₁) * d₂ = (-n₂) * d₁,
    by simp [h]

instance : has_neg ℚ := ⟨rat.neg⟩

private def mul' : rat.num_denum → rat.num_denum → ℚ
| ⟨n₁, ⟨d₁, h₁⟩⟩ ⟨n₂, ⟨d₂, h₂⟩⟩ := ⟦⟨n₁ * n₂, ⟨d₁ * d₂, mul_pos h₁ h₂⟩⟩⟧

protected def mul : ℚ → ℚ → ℚ :=
quotient.lift₂ mul' $ λ⟨n₁, ⟨d₁, h₁⟩⟩ ⟨n₂, ⟨d₂, h₂⟩⟩ ⟨n₃, ⟨d₃, h₃⟩⟩ ⟨n₄, ⟨d₄, h₄⟩⟩,
  assume (h₁ : n₁ * d₃ = n₃ * d₁) (h₂ : n₂ * d₄ = n₄ * d₂),
  quotient.sound $
  calc (n₁ * n₂) * (d₃ * d₄) =
          (n₁ * d₃) * (n₂ * d₄) : by simp
    ... = (n₃ * d₁) * (n₄ * d₂) : by rw [h₁, h₂]
    ... = (n₃ * n₄) * (d₁ * d₂) : by simp

instance : has_mul ℚ := ⟨rat.mul⟩

private def inv' : rat.num_denum → ℚ
| ⟨n, ⟨d, h⟩⟩ := linear_order_cases_on n 0
  (assume : n = 0, 0)
  (assume : n < 0, ⟦⟨-d, ⟨-n, neg_pos_of_neg this⟩⟩⟧)
  (assume : n > 0, ⟦⟨d, ⟨n, this⟩⟩⟧)

private lemma inv'_zero : Π{d : {d:ℤ // d > 0}}, inv' ⟨0, d⟩ = 0
| ⟨d, p⟩ := linear_order_cases_on_eq rfl

private lemma inv'_pos {n d : ℤ} {h : d > 0} (p : n > 0) : inv' ⟨n, ⟨d, h⟩⟩ = ⟦⟨d, ⟨n, p⟩⟩⟧ :=
linear_order_cases_on_gt p

private lemma inv'_neg {n d : ℤ} {h : d > 0} (p : n < 0) : inv' ⟨n, ⟨d, h⟩⟩ = ⟦⟨- d, ⟨- n, neg_pos_of_neg p⟩⟩⟧ :=
linear_order_cases_on_lt p

protected def inv : ℚ → ℚ :=
quotient.lift inv' $ λ⟨n₁, ⟨d₁, h₁⟩⟩ ⟨n₂, ⟨d₂, h₂⟩⟩,
  assume h_eq : n₁ * d₂ = n₂ * d₁,
  linear_order_cases_on n₁ 0
    (assume : n₁ = 0,
      have n₂ * d₁ = 0,
        by simp [this] at h_eq; simp [h_eq],
      have n₂ = 0,
        from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right $ (ne_of_lt h₁).symm,
      by simp [this, ‹n₁ = 0›, inv'_zero])
    (assume : n₁ < 0,
      have n₂ * d₁ < 0,
        from h_eq ▸ mul_neg_of_neg_of_pos this ‹0 < d₂›,
      have n₂ < 0,
        from neg_of_mul_neg_right this $ le_of_lt ‹d₁ > 0›,
      begin
        rw [inv'_neg this, inv'_neg ‹n₁ < 0›],
        apply quotient.sound,
        simp [h_eq]
      end)
    (assume : n₁ > 0,
      have n₂ * d₁ > 0,
        from h_eq ▸ mul_pos this ‹0 < d₂›,
      have n₂ > 0,
        from pos_of_mul_pos_right this $ le_of_lt ‹d₁ > 0›,
      begin
        rw [inv'_pos this, inv'_pos ‹n₁ > 0›],
        apply quotient.sound,
        simp [h_eq]
      end)

instance : has_inv ℚ := ⟨rat.inv⟩

variables (a b c : ℚ)

protected theorem add_zero : a + 0 = a :=
quotient.induction_on a $ λ⟨n, ⟨d, h⟩⟩, quotient.sound $
  by simp [rat.rel]

protected theorem zero_add : 0 + a = a :=
quotient.induction_on a $ λ⟨n, ⟨d, h⟩⟩, quotient.sound $
  by simp [rat.rel]

protected theorem add_comm : a + b = b + a :=
quotient.induction_on₂ a b $ λ⟨n₁, ⟨d₁, h₁⟩⟩ ⟨n₂, ⟨d₂, h₂⟩⟩, quotient.sound $
  by simp [rat.rel]

protected theorem add_assoc : a + b + c = a + (b + c) :=
quotient.induction_on₃ a b c $ λ⟨n₁, ⟨d₁, h₁⟩⟩ ⟨n₂, ⟨d₂, h₂⟩⟩ ⟨n₃, ⟨d₃, h₃⟩⟩, quotient.sound $
  by simp [rat.rel, mul_add, add_mul]

protected theorem add_left_neg : -a + a = 0 :=
quotient.induction_on a $ λ⟨n, ⟨d, h⟩⟩, quotient.sound $
  by simp [rat.rel]

protected theorem mul_one : a * 1 = a :=
quotient.induction_on a $ λ⟨n, ⟨d, h⟩⟩, quotient.sound $
  by simp [rat.rel]

protected theorem one_mul : 1 * a = a :=
quotient.induction_on a $ λ⟨n, ⟨d, h⟩⟩, quotient.sound $
  by simp [rat.rel]

protected theorem mul_comm : a * b = b * a :=
quotient.induction_on₂ a b $ λ⟨n₁, ⟨d₁, h₁⟩⟩ ⟨n₂, ⟨d₂, h₂⟩⟩, quotient.sound $
  by simp [rat.rel]

protected theorem mul_assoc : a * b * c = a * (b * c) :=
quotient.induction_on₃ a b c $ λ⟨n₁, ⟨d₁, h₁⟩⟩ ⟨n₂, ⟨d₂, h₂⟩⟩ ⟨n₃, ⟨d₃, h₃⟩⟩, quotient.sound $
  by simp [rat.rel]

protected theorem add_mul : (a + b) * c = a * c + b * c :=
quotient.induction_on₃ a b c $ λ⟨n₁, ⟨d₁, h₁⟩⟩ ⟨n₂, ⟨d₂, h₂⟩⟩ ⟨n₃, ⟨d₃, h₃⟩⟩, quotient.sound $
  by simp [rat.rel, mul_add, add_mul]

protected theorem mul_add : a * (b + c) = a * b + a * c :=
quotient.induction_on₃ a b c $ λ⟨n₁, ⟨d₁, h₁⟩⟩ ⟨n₂, ⟨d₂, h₂⟩⟩ ⟨n₃, ⟨d₃, h₃⟩⟩, quotient.sound $
  by simp [rat.rel, mul_add, add_mul]

private lemma rat_eq_zero : ∀{a : rat.num_denum}, ⟦a⟧ = (0:ℚ) → a.1 = 0
| ⟨n, ⟨d, h⟩⟩ eq_0 :=
  have n * 1 = 0 * d, from quotient.exact eq_0,
  begin simp at this, assumption end

private lemma eq_zero_of_rat_eq_zero : ∀{a : rat.num_denum}, a.1 = 0 → ⟦a⟧ = (0:ℚ)
| ⟨n, ⟨d, h⟩⟩ (_ : n = 0) := begin simp [‹n = 0›], apply quotient.sound, simp [rat.rel] end

private lemma rat_eq_zero_iff {a : rat.num_denum} : ⟦a⟧ = (0:ℚ) ↔ a.1 = 0 :=
⟨rat_eq_zero, eq_zero_of_rat_eq_zero⟩

protected theorem zero_ne_one : 0 ≠ (1:ℚ) :=
assume h, zero_ne_one (rat_eq_zero h.symm).symm

protected theorem mul_inv_cancel : a ≠ 0 → a * a⁻¹ = 1 :=
quotient.induction_on a $ λ⟨n, ⟨d, h⟩⟩ neq0,
let a : rat.num_denum := ⟨n, ⟨d, h⟩⟩ in
linear_order_cases_on n 0
  (assume : n = 0, by rw [this, @eq_zero_of_rat_eq_zero ⟨0, ⟨d, h⟩⟩ rfl] at neq0; contradiction)
  (assume : n < 0,
    have @has_inv.inv rat _ ⟦a⟧ = ⟦⟨-d, ⟨-n, neg_pos_of_neg this⟩⟩⟧,
      from @inv'_neg n d h _,
    begin simp [this], apply quotient.sound, simp [rat.rel] end)
  (assume : n > 0,
    have @has_inv.inv rat _ ⟦a⟧ = ⟦⟨d, ⟨n, this⟩⟩⟧,
      from @inv'_pos n d h _,
    begin simp [this], apply quotient.sound, simp [rat.rel] end)

protected theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
eq.trans (rat.mul_comm _ _) (rat.mul_inv_cancel _ h)

instance decidable_eq_rat.rel : Π{a b : rat.num_denum}, decidable (rat.rel a b)
| ⟨n₁, ⟨d₁, h₁⟩⟩ ⟨n₂, ⟨d₂, h₂⟩⟩ := show decidable (n₁ * d₂ = n₂ * d₁), by apply_instance

instance decidable_eq_rat : decidable_eq ℚ :=
by dunfold rat; apply_instance

instance field_rat : discrete_field ℚ :=
{ zero             := rat.zero,
  add              := rat.add,
  neg              := rat.neg,
  one              := rat.one,
  mul              := rat.mul,
  inv              := rat.inv,
  zero_add         := rat.zero_add,
  add_zero         := rat.add_zero,
  add_comm         := rat.add_comm,
  add_assoc        := rat.add_assoc,
  add_left_neg     := rat.add_left_neg,
  mul_one          := rat.mul_one,
  one_mul          := rat.one_mul,
  mul_comm         := rat.mul_comm,
  mul_assoc        := rat.mul_assoc,
  left_distrib     := rat.mul_add,
  right_distrib    := rat.add_mul,
  zero_ne_one      := rat.zero_ne_one,
  mul_inv_cancel   := rat.mul_inv_cancel,
  inv_mul_cancel   := rat.inv_mul_cancel,
  has_decidable_eq := by apply_instance,
  inv_zero         := quotient.sound rfl }

private def nonneg' : rat.num_denum → Prop
| ⟨n₁, ⟨d₁, h₁⟩⟩ := 0 ≤ n₁

protected def nonneg : ℚ → Prop :=
quotient.lift nonneg' $ λ⟨n₁, ⟨d₁, h₁⟩⟩ ⟨n₂, ⟨d₂, h₂⟩⟩ (h : n₁ * d₂ = n₂ * d₁),
  propext $ calc (0 ≤ n₁) ↔ (0 ≤ n₁ * d₂) : (mul_nonneg_iff_right_nonneg_of_pos h₂).symm
                      ... ↔ (0 ≤ n₂ * d₁) : by rw h
                      ... ↔ (0 ≤ n₂) : mul_nonneg_iff_right_nonneg_of_pos h₁

protected def nonneg_add : rat.nonneg a → rat.nonneg b → rat.nonneg (a + b) :=
quotient.induction_on₂ a b $ λ⟨n₁, ⟨d₁, h₁⟩⟩ ⟨n₂, ⟨d₂, h₂⟩⟩ _ _,
  add_nonneg (mul_nonneg ‹0 ≤ n₁› (le_of_lt ‹0 < d₂›)) (mul_nonneg ‹0 ≤ n₂› (le_of_lt ‹0 < d₁›))

protected def nonneg_mul : rat.nonneg a → rat.nonneg b → rat.nonneg (a * b) :=
quotient.induction_on₂ a b $ λ⟨n₁, ⟨d₁, h₁⟩⟩ ⟨n₂, ⟨d₂, h₂⟩⟩ _ _,
  mul_nonneg ‹0 ≤ n₁› ‹0 ≤ n₂›

protected def nonneg_antisymm : rat.nonneg a → rat.nonneg (-a) → a = 0 :=
quotient.induction_on a $ λ⟨n₁, ⟨d₁, h₁⟩⟩ (h₂ : 0 ≤ n₁) (h₃ : 0 ≤ -n₁), quotient.sound $
  le_antisymm (by simp; exact le_neg_of_le_neg h₃) (by simp; exact h₂)

protected def nonneg_total : rat.nonneg a ∨ rat.nonneg (-a) :=
quotient.induction_on a $ λ⟨n₁, ⟨d₁, h₁⟩⟩,
  show 0 ≤ n₁ ∨ 0 ≤ -n₁,
    from or.imp_right neg_nonneg_of_nonpos (le_total 0 n₁)

instance decidable_nonneg : decidable (rat.nonneg a)  :=
quotient.rec_on_subsingleton a
  (λ⟨n, ⟨d, h⟩⟩, if h : 0 ≤ n then is_true h else is_false h)

protected def le (a b : ℚ) := rat.nonneg (b - a)

instance : has_le ℚ := ⟨rat.le⟩

protected theorem le_refl : a ≤ a :=
show rat.nonneg (a - a), begin rw [sub_self], exact le_refl (0 : int) end

instance : linear_strong_order_pair ℚ :=
{ le              := rat.le,
  lt              := λa b, a ≤ b ∧ a ≠ b,
  le_iff_lt_or_eq := assume a b,
    ⟨assume : a ≤ b, if h : a = b then or.inr h else or.inl ⟨this, h⟩,
      or.rec and.left (assume : a = b, show a ≤ b, from this ▸ rat.le_refl _)⟩,
  lt_irrefl       := assume a ⟨_, h⟩, h rfl,
  le_refl         := rat.le_refl,
  le_trans        := assume a b c h_ab h_bc,
    have rat.nonneg (b - a + (c - b)),
      from rat.nonneg_add _ _ h_ab h_bc,
    show rat.nonneg (c - a),
      by simp at this; assumption,
  le_antisymm     := assume a b h_ab h_ba,
    have a = - - b,
    from eq_neg_of_add_eq_zero $ rat.nonneg_antisymm _ h_ba (by simp; assumption),
    by rw neg_neg at this; assumption,
  le_total        := assume a b,
    have rat.nonneg (b - a) ∨ rat.nonneg (- (b - a)),
      from rat.nonneg_total _,
    by rw neg_sub at this; assumption }

protected def zero_le_of_nonneg : rat.nonneg a → 0 ≤ a :=
quotient.induction_on a $ assume ⟨n, ⟨d, h⟩⟩ _, show 0 ≤ n * 1 + (- 0) * d,
  by simp; assumption

protected def nonneg_of_zero_le : 0 ≤ a → rat.nonneg a :=
quotient.induction_on a $ assume ⟨n, ⟨d, h⟩⟩, assume : 0 ≤ n * 1 + (- 0) * d,
  by simp at this; assumption

instance : discrete_linear_ordered_field ℚ :=
{ rat.field_rat with
  le              := (≤),
  lt              := (<),
  le_refl         := le_refl,
  le_trans        := assume a b c, le_trans,
  le_antisymm     := assume a b, le_antisymm,
  le_total        := le_total,
  le_iff_lt_or_eq := assume a b, le_iff_lt_or_eq,
  lt_irrefl       := lt_irrefl,
  le_of_lt        := assume a b, le_of_lt,
  lt_of_lt_of_le  := assume a b c, lt_of_lt_of_le,
  lt_of_le_of_lt  := assume a b c, lt_of_le_of_lt,
  zero_lt_one     := ⟨rat.zero_le_of_nonneg _ (@zero_le_one int _), zero_ne_one⟩,
  add_le_add_left := assume a b (h_ab : rat.nonneg (b - a)) c,
    show rat.nonneg ((c + b) - (c + a)), by rw add_sub_add_left_eq_sub; assumption,
  add_lt_add_left := assume a b ⟨a_le_b, a_ne_b⟩ c,
    show rat.nonneg ((c + b) - (c + a)) ∧ c + a ≠ c + b,
      by rw [add_sub_add_left_eq_sub]; exact ⟨a_le_b, not_antimono a_ne_b add_left_cancel⟩,
  mul_nonneg      := assume a b ha hb, rat.zero_le_of_nonneg _ $
    rat.nonneg_mul _ _ (rat.nonneg_of_zero_le a ha) (rat.nonneg_of_zero_le b hb),
  mul_pos         := assume a b ⟨nn_a, a_ne_zero⟩ ⟨nn_b, b_ne_zero⟩,
    ⟨rat.zero_le_of_nonneg _ $ rat.nonneg_mul _ _
      (rat.nonneg_of_zero_le a nn_a) (rat.nonneg_of_zero_le b nn_b),
      (mul_ne_zero a_ne_zero.symm b_ne_zero.symm).symm⟩,
  decidable_eq    := by apply_instance,
  decidable_le    := assume a b, rat.decidable_nonneg (b - a),
  decidable_lt    := assume a b, show decidable (rat.nonneg (b - a) ∧ a ≠ b), by apply_instance }

end rat
