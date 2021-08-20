import ring_theory.valuation.basic

open_locale classical
noncomputable theory

universe u

class valuation_ring (R : Type u) [integral_domain R] : Prop :=
(cond : ∀ (a b : R), ∃ c : R, a * c = b ∨ b * c = a)

namespace valuation_ring

variables (R : Type u) [integral_domain R] [valuation_ring R]

instance : local_ring R :=
{ exists_pair_ne := ⟨0, 1, zero_ne_one⟩,
  is_local := begin
    intros a,
    rcases cond a (1-a) with ⟨c,h|h⟩,
    { left,
      apply is_unit_of_mul_eq_one a (c+1),
      simp [mul_add, h] },
    { right,
      apply is_unit_of_mul_eq_one (1-a) (c+1),
      simp [mul_add, h] }
  end }

instance : linear_order (ideal R) :=
{ le_total := begin
    intros α β,
    by_contra h,
    change ¬((∀ a (ha : a ∈ α), a ∈ β) ∨ (∀ b (hb : b ∈ β), b ∈ α)) at h,
    push_neg at h,
    obtain ⟨⟨a,ha1,ha2⟩,⟨b,hb1,hb2⟩⟩ := h,
    rcases cond a b with ⟨c,hc|hc⟩,
    { apply hb2,
      rw ← hc,
      exact α.mul_mem_right c ha1 },
    { apply ha2,
      rw ← hc,
      exact β.mul_mem_right c hb1 }
  end,
  decidable_le := infer_instance,
  ..(infer_instance : bounded_lattice _) } .

def Γ.setoid : setoid R := setoid.ker (λ r : R, R ∙ r)

def Γ := quotient (Γ.setoid R)

instance : linear_ordered_comm_monoid_with_zero (Γ R) :=
{ le := λ a b, quotient.lift_on₂' a b (λ x y, (R ∙ x) ≤ (R ∙ y)) begin
    intros a₁ a₂ b₁ b₂ h₁ h₂,
    change _ = _ at h₁,
    change _ = _ at h₂,
    dsimp at *,
    rw [h₁, h₂],
  end,
  le_refl := by { rintro ⟨a⟩, exact le_refl _ },
  le_trans := by { rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h₁ h₂, exact le_trans h₁ h₂ },
  le_antisymm := begin
    rintros ⟨a⟩ ⟨b⟩ h1 h2,
    apply quotient.sound',
    exact le_antisymm h1 h2,
  end,
  le_total := by { rintros ⟨a⟩ ⟨b⟩, apply le_total },
  decidable_le := by apply_instance,
  mul := λ a b, quotient.lift_on₂' a b (λ x y, quotient.mk' (x * y)) begin
    intros a₁ a₂ b₁ b₂ h₁ h₂,
    change _ = _ at h₁,
    change _ = _ at h₂,
    apply quotient.sound',
    change _ = _,
    dsimp at *,
    simp_rw [← set.singleton_mul_singleton],
    rw [← submodule.span_mul_span, ← submodule.span_mul_span, h₁, h₂],
  end,
  mul_assoc := by { rintro ⟨a⟩ ⟨b⟩ ⟨c⟩, apply quotient.sound', rw [mul_assoc, ← quotient.eq'] },
  one := quotient.mk' 1,
  one_mul := by { rintro ⟨a⟩, apply quotient.sound', rw [one_mul, ← quotient.eq'] },
  mul_one := by { rintro ⟨a⟩, apply quotient.sound', rw [mul_one, ← quotient.eq'] },
  --npow := _,
  --npow_zero' := _,
  --npow_succ' := _,
  mul_comm := by { rintro ⟨a⟩ ⟨b⟩, apply quotient.sound', rw [mul_comm, ← quotient.eq' ] },
  mul_le_mul_left := begin
    rintro ⟨a⟩ ⟨b⟩ (h : (R ∙ a) ≤ R ∙ b) ⟨c⟩,
    change (R ∙ _) ≤ R ∙ _,
    simp_rw [← set.singleton_mul_singleton, ← submodule.span_mul_span],
    exact submodule.mul_le_mul (le_refl _) h,
  end,
  lt_of_mul_lt_mul_left := begin
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ (h : (R ∙ (a * b)) < R ∙ (a * c)),
    change (R ∙ b) < (R ∙ c),
    have ha : a ≠ 0,
    { rintro rfl,
      refine h.2 _,
      simp },
    apply lt_of_le_of_ne,
    { rw submodule.span_singleton_le_iff_mem,
      have : a * b ∈ R ∙ (a * c), by { apply h.1, apply submodule.mem_span_singleton_self },
      rw submodule.mem_span_singleton at this ⊢,
      obtain ⟨d,hd⟩ := this,
      use d,
      erw (show d • (a * c) = a * (d * c), by { change _ * _ = _, ring }) at hd,
      apply mul_left_cancel' ha hd },
    { replace h := ne_of_lt h,
      intro c,
      apply h,
      simp only [← set.singleton_mul_singleton, ← submodule.span_mul_span, c] }
  end,
  zero := quotient.mk' 0,
  zero_mul := by { rintro ⟨a⟩, apply quotient.sound', simp [← quotient.eq'] },
  mul_zero := by { rintro ⟨a⟩, apply quotient.sound', simp [← quotient.eq'] },
  zero_le_one := λ a ha, by { simp only [ideal.mem_bot, submodule.span_zero_singleton] at ha,
    simp [ha] } } .

def v : valuation R (Γ R) :=
{ to_fun := quotient.mk',
  map_zero' := rfl,
  map_one' := rfl,
  map_mul' := λ x y, rfl,
  map_add' := begin
    intros x y,
    rcases cond x y with ⟨c,rfl|rfl⟩,
    { refine le_trans _ (le_max_left _ _),
      erw [submodule.span_singleton_le_iff_mem, submodule.mem_span_singleton],
      use (1 + c),
      rw mul_comm,
      simp [add_mul] },
    { refine le_trans _ (le_max_right _ _),
      erw [submodule.span_singleton_le_iff_mem, submodule.mem_span_singleton],
      use (1 + c),
      simp only [add_mul, algebra.id.smul_eq_mul, one_mul],
      ring }
  end }

end valuation_ring
