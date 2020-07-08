

import category_theory.limits.shapes.zero

universes v u

open category_theory
open category_theory.limits

variables (V : Type u) [category.{v} V]
variables [has_zero_morphisms V] [has_zero_object V]

local attribute [instance] has_zero_object.has_zero

inductive composable_morphisms'
  (V : Type u) [category.{v} V] : V → Type (max u v)
| zero [] : Π X, composable_morphisms' X
| cons : Π {X Y : V} (f : X ⟶ Y) (C : composable_morphisms' Y), composable_morphisms' X

def composable_morphisms := Σ (X : V), (composable_morphisms' V X)

variables {V}

namespace composable_morphisms

open composable_morphisms'

def length_aux : Π X, composable_morphisms' V X → ℕ
| _ (zero _) := 0
| _ (cons f c) := length_aux _ c + 1

/-- The length of a string of composable morphisms is the number of morphisms in the string. -/
def length (c : composable_morphisms V) : ℕ := length_aux c.1 c.2

@[simp]
lemma length_cons {X Y : V} {f : X ⟶ Y} {c} : length ⟨X, cons f c⟩ = length ⟨_, c⟩ + 1 := rfl

def X' : ℕ → composable_morphisms V → V
| 0 c := c.1
| (n+1) ⟨_, zero _⟩ := 0
| (n+1) ⟨_, cons f c⟩ := X' n ⟨_, c⟩

def X'_bounded (c : composable_morphisms V) {i : ℕ} (h : c.length < i) : c.X' i ≅ 0 :=
begin
  cases c with X c,
  induction i generalizing X c,
  { exfalso, cases h, },
  { cases c,
    { refl, },
    { dsimp [X'],
      simp only [nat.succ_eq_add_one, length_cons, add_lt_add_iff_right] at h,
      exact i_ih _ _ h, }, }
end

def d' : Π (n : ℕ) (c : composable_morphisms V), X' n c ⟶ X' (n+1) c
| 0 ⟨_, zero _⟩ := 0
| 0 ⟨_, cons f c⟩ := f
| (n+1) ⟨_, zero _⟩ := 0
| (n+1) ⟨_, cons f c⟩ := d' n ⟨_, c⟩

def X (c : composable_morphisms V) (i : ℤ) : V :=
if 0 ≤ i then c.X' i.to_nat else 0

def X_nonneg (c : composable_morphisms V) {i : ℤ} (h : i < 0) : c.X i ≅ 0 :=
by { rw [X, if_neg], simpa using h, }

def X_bounded (c : composable_morphisms V) {i : ℤ} (h : (c.length : ℤ) < i) : c.X i ≅ 0 :=
begin
  dsimp [X],
  rw [if_pos],
  apply X'_bounded,
  { exact int.lt_to_nat.mpr h, },
  { exact le_of_lt (lt_of_le_of_lt (int.coe_zero_le (length c)) h) },
end

def d (c : composable_morphisms V) (i : ℤ) : c.X i ⟶ c.X (i+1) :=
if h : 0 ≤ i then
  eq_to_hom (by simp [X, h]) ≫ c.d' i.to_nat ≫ eq_to_hom (by simp [X, h, int.le_add_one, int.to_nat_add_one])
else
  0

lemma d_nonneg (c : composable_morphisms V) {i : ℤ} (h : i < 0) : c.d i = 0 :=
by { rw [d, dif_neg], simpa using h, }

inductive d_squared : composable_morphisms V → Prop
| zero : Π X, d_squared ⟨_, zero X⟩
| single : Π {X Y : V} (f : X ⟶ Y), d_squared ⟨_, cons f (zero Y)⟩
| d_squared : Π {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
    {c : composable_morphisms' V Z} (h : d_squared ⟨Y, cons g c⟩), d_squared ⟨X, cons f (cons g c)⟩

end composable_morphisms
