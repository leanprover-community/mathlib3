/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import tactic.field_simp
import tactic.polyrith

/-!
# Edwards elliptic curves

cf Hales, https://arxiv.org/abs/1610.05278

-/

noncomputable theory

variables {R : Type*} [field R]
variables (c d : R)

local notation `f` := λ x y, x ^ 2 + c * y ^ 2 - 1 - d * x ^ 2 * y ^ 2

include c d

/-- The curve `x ^ 2 + c * y ^ 2 - 1 - d * x ^ 2 * y ^ 2 = 0` in `R × R`. -/
def edwards_curve : Type* := {p : R × R // f p.1 p.2 = 0}

local notation `C` := edwards_curve c d

instance edwards_curve.has_add : has_add C :=
{ add := begin
    rintros ⟨⟨x₁, y₁⟩, h₁⟩ ⟨⟨x₂, y₂⟩, h₂⟩,
    refine ⟨((x₁ * x₂ - c * y₁ * y₂) / (1 - d * x₁ * x₂ * y₁ * y₂),
      (x₁ * y₂ + y₁ * x₂) / (1 + d * x₁ * x₂ * y₁ * y₂)), _⟩,
    dsimp at *,
    have : 1 - d * x₁ * x₂ * y₁ * y₂ ≠ 0 := sorry,
    have : 1 + d * x₁ * x₂ * y₁ * y₂ ≠ 0 := sorry,
    field_simp,
    have H : (x₁ * x₂ - c * y₁ * y₂) ^ 2 * (1 + d * x₁ * x₂ * y₁ * y₂) ^ 2
      + c * (x₁ * y₂ + y₁ * x₂) ^ 2 * (1 - d * x₁ * x₂ * y₁ * y₂) ^ 2
      - (1 - d * x₁ * x₂ * y₁ * y₂) ^ 2 * (1 + d * x₁ * x₂ * y₁ * y₂) ^ 2
      - d * (x₁ * x₂ - c * y₁ * y₂) ^ 2 * (x₁ * y₂ + y₁ * x₂) ^ 2 = 0,
    -- { polyrith },
    { sorry },
    linear_combination (1 - d * x₁ * x₂ * y₁ * y₂) ^ 2 *
      (1 + d * x₁ * x₂ * y₁ * y₂) ^ 2 * H
  end }

instance edwards_curve.has_zero : has_zero C :=
{ zero := ⟨(1, 0), begin
    dsimp,
    ring
  end⟩ }

instance edwards_curve.has_neg : has_neg C :=
{ neg := begin
    rintros ⟨⟨x, y⟩, h⟩,
    refine ⟨⟨x, -y⟩, _⟩,
    dsimp at *,
    linear_combination h,
  end }

lemma edwards_curve.add_assoc' (a b k : edwards_curve c d) : a + b + k = a + (b + k) :=
begin
  obtain ⟨⟨x₁, y₁⟩, h₁⟩ := a,
  obtain ⟨⟨x₂, y₂⟩, h₂⟩ := b,
  obtain ⟨⟨x₃, y₃⟩, h₃⟩ := k,
  have : 1 - d * x₁ * x₂ * y₁ * y₂ ≠ 0 := sorry,
  have : 1 + d * x₁ * x₂ * y₁ * y₂ ≠ 0 := sorry,
  have : 1 - d * x₂ * x₃ * y₂ * y₃ ≠ 0 := sorry,
  have : 1 + d * x₂ * x₃ * y₂ * y₃ ≠ 0 := sorry,
  ext,
  { have : (1 - d * x₁ * x₂ * y₁ * y₂) * (1 + d * x₁ * x₂ * y₁ * y₂)
      - d * (x₁ * x₂ - c * y₁ * y₂) * x₃ * (x₁ * y₂ + y₁ * x₂) * y₃ ≠ 0 := sorry,
    have : (1 - d * x₂ * x₃ * y₂ * y₃) * (1 + d * x₂ * x₃ * y₂ * y₃)
      - d * x₁ * (x₂ * x₃ - c * y₂ * y₃) * y₁ * (x₂ * y₃ + y₂ * x₃) ≠ 0 := sorry,
    dsimp [edwards_curve.has_add] at *,
    field_simp,
    -- polyrith,
    sorry },
  { have : (1 - d * x₁ * x₂ * y₁ * y₂) * (1 + d * x₁ * x₂ * y₁ * y₂)
      + d * (x₁ * x₂ - c * y₁ * y₂) * x₃ * (x₁ * y₂ + y₁ * x₂) * y₃ ≠ 0 := sorry,
    have : ((1 - d * x₂ * x₃ * y₂ * y₃) * (1 + d * x₂ * x₃ * y₂ * y₃)
      + d * x₁ * (x₂ * x₃ - c * y₂ * y₃) * y₁ * (x₂ * y₃ + y₂ * x₃)) ≠ 0 := sorry,
    dsimp [edwards_curve.has_add] at *,
    field_simp,
    -- polyrith,
    sorry }
end

lemma edwards_curve.add_comm' (a b : edwards_curve c d) : a + b = b + a :=
begin
  obtain ⟨⟨x₁, y₁⟩, h₁⟩ := a,
  obtain ⟨⟨x₂, y₂⟩, h₂⟩ := b,
  ext,
  { have : 1 - d * x₁ * x₂ * y₁ * y₂ ≠ 0 := sorry,
    have : 1 - d * x₂ * x₁ * y₂ * y₁ ≠ 0 := sorry,
    dsimp [edwards_curve.has_add] at *,
    field_simp,
    ring },
  { have : 1 + d * x₁ * x₂ * y₁ * y₂ ≠ 0 := sorry,
    have : 1 + d * x₂ * x₁ * y₂ * y₁ ≠ 0 := sorry,
    dsimp [edwards_curve.has_add] at *,
    field_simp,
    ring },
end

lemma edwards_curve.add_left_neg' (a : edwards_curve c d) : -a + a = 0 :=
begin
  obtain ⟨⟨x, y⟩, h⟩ := a,
  ext,
  { dsimp [edwards_curve.has_add, edwards_curve.has_zero, edwards_curve.has_neg] at *,
    have : 1 + d * x * x * y * y ≠ 0 := sorry,
    field_simp,
    linear_combination h },
  { dsimp [edwards_curve.has_add, edwards_curve.has_zero, edwards_curve.has_neg] at *,
    have : 1 + - (d * x * x * y * y) ≠ 0 := sorry,
    field_simp,
    ring }
end

instance edwards_curve.add_comm_group : add_comm_group C :=
{ add_assoc := edwards_curve.add_assoc' c d,
  add_comm := edwards_curve.add_comm' c d,
  zero_add := begin
    rintros ⟨⟨x, y⟩, h⟩,
    ext,
    { dsimp [edwards_curve.has_add, edwards_curve.has_zero] at *,
      field_simp },
    { dsimp [edwards_curve.has_add, edwards_curve.has_zero] at *,
      field_simp, },
  end,
  add_zero := begin
    rintros ⟨⟨x, y⟩, h⟩,
    ext,
    { dsimp [edwards_curve.has_add, edwards_curve.has_zero] at *,
      field_simp },
    { dsimp [edwards_curve.has_add, edwards_curve.has_zero] at *,
      field_simp, },
  end,
  add_left_neg := edwards_curve.add_left_neg' c d,
  .. edwards_curve.has_add c d,
  .. edwards_curve.has_zero c d,
  .. edwards_curve.has_neg c d  }
