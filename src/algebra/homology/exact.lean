import algebra.homology.homology
import category_theory.preadditive
import tactic.suggest
import tactic.omega
import tactic.interval_cases

universes v u

-- I want this locatable by library_search.
lemma foo {a b : ℤ} (h : a ≤ b) : a ≤ b + 1 := by omega

@[simp] lemma quux' {n : ℕ} : ((n : ℤ) + 1).to_nat = n + 1 := rfl

lemma bar {a : ℤ} (h : 0 ≤ a) : a.to_nat + 1 = (a + 1).to_nat :=
begin
  lift a to ℕ using h,
  simp,
end

@[simp]
lemma turkle : (0 : ℤ).to_nat = 0 := rfl

@[simp]
lemma turkle' : (1 : ℤ).to_nat = 1 := rfl

open category_theory
open category_theory.limits

variables {V : Type u} [category.{v} V]
variables [has_images V] [has_equalizers V]
variables {β : Type} [add_comm_group β] {b : β}

local attribute [instance] has_zero_object.has_zero

namespace complex
variables [has_zero_morphisms V] (C : complex V b)

/--
We say a complex `C` is exact at `i` if
the inclusion map from `image (C.d (i-b))` to `kernel (C.d i)`
is an epimorphism.

(We say epimorphism rather than isomorphism because, at least for preadditive categories,
this is exactly equivalent to the homology at `i` vanishing.
In an abelian category, this is the same as being an isomorphism,
because the inclusion map is always a monomorphism.)
-/
def exact_at (i : β) : Prop := epi (C.image_to_kernel_map (i-b))

/--
A complex is exact if it is exact at every point.
-/
def exact : Prop := Π i, C.exact_at i

/-- If a complex is zero at some point, then it is automatically exact there. -/
lemma exact_at_of_zero [has_zero_object V] {i : β} (h : C.X i ≅ 0) : C.exact_at i :=
begin
  -- In fact we show something slightly stronger:
  haveI : is_iso (C.image_to_kernel_map (i-b)) := by
  { dsimp [complex.image_to_kernel_map, category_theory.image_to_kernel_map],
    have t := zero_of_target_iso_zero (C.d (i - b)) (by { convert h, simp, }),
    simp [t],
    refine (is_iso_zero_equiv_iso_zero _ _).symm (_, _),
    { exact image_zero' t, },
    { haveI := mono_of_source_iso_zero (C.d (i - b + b)) (by { convert h, simp }),
      apply kernel.of_mono, } },
  dsimp [exact_at],
  apply_instance,
end

end complex

namespace complex
variables [has_zero_object V]

section

variables [has_zero_morphisms V] [has_cokernels V]

/-- If a complex is exact at a point, the homology vanishes there. -/
def homology_zero_of_exact {C : complex V b} {i : β} (x : C.exact_at i) : C.homology i ≅ 0 :=
begin
  unfreezingI { dsimp [exact_at] at x },
  apply cokernel.of_epi,
end

end

section

variables [preadditive V] [has_cokernels V]

/-- In a preadditive category, a complex is exact at a point if the homology vanishes there. -/
lemma exact_of_homology_zero {C : complex V b} {i : β} (h : C.homology i ≅ 0) : C.exact_at i :=
preadditive.epi_of_cokernel_zero _ (zero_of_target_iso_zero _ h)

end

end complex

variables (V) [has_zero_morphisms V]

structure short_exact_sequence :=
(A B C : V)
(f : A ⟶ B)
(g : B ⟶ C)
[is_mono : mono f]
[is_epi : epi g]
(d_squared : f ≫ g = 0)
(exact : epi (image_to_kernel_map f g d_squared))

attribute [instance] short_exact_sequence.is_mono short_exact_sequence.is_epi

local attribute [instance] has_zero_object.has_zero

inductive composable_morphisms'
  (V : Type u) [category.{v} V] : V → Type (max u v)
| zero [] : Π X, composable_morphisms' X
| cons : Π {X Y : V} (f : X ⟶ Y) (C : composable_morphisms' Y), composable_morphisms' X

variables [has_zero_object V]

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
  eq_to_hom (by simp [X, h]) ≫ c.d' i.to_nat ≫ eq_to_hom (by simp [X, h, foo, bar])
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

section

variables (V)

def inductive_complex := Σ' (c : composable_morphisms V), c.d_squared

end

namespace inductive_complex

open composable_morphisms

@[simps]
def to_cochain_complex (c : inductive_complex V) : cochain_complex V :=
{ X := c.1.X,
  d := c.1.d,
  d_squared' :=
  begin
    cases c with c h,
    ext i,
    simp [d],
    by_cases p : 0 ≤ i,
    lift i to ℕ using p,
    { rw [dif_pos, dif_pos],
      { simp, dsimp,
        induction i with i ih generalizing c,
        { rcases h with X|⟨X,Y,f⟩|⟨X,Y,Z,f,g,w,c,h'⟩,
          { simp [d'], },
          { simp [d'], },
          { simp [d', w], }, },
        { rcases h with X|⟨X,Y,f⟩|⟨X,Y,Z,f,g,w,c,h'⟩,
          { simp [d'], },
          { simp [d'], },
          { specialize ih _ h', simp only [d'] at ih, simp [d', ih], }, }, },
      { exact foo (int.coe_zero_le i), },
      { exact int.coe_zero_le i, }, },
    { simp [p], }
  end }

def to_chain_complex_X_nonneg (c : inductive_complex V) {i : ℤ} (h : i < 0) :
  c.to_cochain_complex.X i ≅ 0 :=
c.1.X_nonneg h

lemma to_chain_complex_d_nonneg (c : inductive_complex V) {i : ℤ} (h : i < 0) :
  c.to_cochain_complex.d i = 0 :=
c.1.d_nonneg h

end inductive_complex

namespace short_exact_sequence
variables [has_zero_object V]
local attribute [instance] has_zero_object.has_zero

def to_composable_morphisms (S : short_exact_sequence V) : composable_morphisms V :=
⟨S.A, composable_morphisms'.cons S.f (composable_morphisms'.cons S.g (composable_morphisms'.zero S.C))⟩

lemma to_composable_morphisms_d_squared (S : short_exact_sequence V) : S.to_composable_morphisms.d_squared :=
begin
  constructor,
  exact S.d_squared,
  constructor,
end

def to_inductive_complex (S : short_exact_sequence V) : inductive_complex V :=
⟨S.to_composable_morphisms, S.to_composable_morphisms_d_squared⟩

def to_cochain_complex (S : short_exact_sequence V) : cochain_complex V :=
S.to_inductive_complex.to_cochain_complex

@[simp]
lemma to_cochain_complex_d_zero (S : short_exact_sequence V) : S.to_cochain_complex.d 0 = S.f :=
begin
  dsimp [to_cochain_complex, composable_morphisms.d, to_inductive_complex, to_composable_morphisms],
  simp [composable_morphisms.d'],
end

@[simp]
lemma to_cochain_complex_d_zero' (S : short_exact_sequence V) : S.to_cochain_complex.d (1 - 1) = S.f :=
S.to_cochain_complex_d_zero

@[simp]
lemma to_cochain_complex_d_zero'' (S : short_exact_sequence V) : S.to_cochain_complex.d (0 - 1 + 1) = S.f :=
S.to_cochain_complex_d_zero

@[simp]
lemma to_cochain_complex_d_one (S : short_exact_sequence V) : S.to_cochain_complex.d 1 = S.g :=
begin
  dsimp [to_cochain_complex, composable_morphisms.d, to_inductive_complex, to_composable_morphisms],
  rw [dif_pos zero_le_one],
  simp [composable_morphisms.d'],
end

@[simp]
lemma to_cochain_complex_d_one' (S : short_exact_sequence V) : S.to_cochain_complex.d (1 - 1 + 1) = S.g :=
S.to_cochain_complex_d_one

@[simp]
lemma to_cochain_complex_d_one'' (S : short_exact_sequence V) : S.to_cochain_complex.d (2 - 1) = S.g :=
S.to_cochain_complex_d_one

def to_cochain_complex_short (S : short_exact_sequence V) {i : ℤ} (h : 2 < i) : S.to_cochain_complex.X i ≅ 0 :=
begin
  dsimp [to_cochain_complex, to_inductive_complex, to_composable_morphisms],
  apply composable_morphisms.X_bounded,
  exact h,
end

lemma to_cochain_complex_exact (S : short_exact_sequence V) : S.to_cochain_complex.exact :=
begin
  intro i,
  by_cases h₁ : i < 0,
  { apply complex.exact_at_of_zero, exact inductive_complex.to_chain_complex_X_nonneg _ h₁, },
  { simp at h₁,
    by_cases h₂ : 2 < i,
    { apply complex.exact_at_of_zero,
      apply S.to_cochain_complex_short h₂, },
    simp at h₂,
    interval_cases i; clear h₁ h₂; dsimp only [complex.exact_at, complex.image_to_kernel_map],
    { -- exactness at A
      haveI : mono (S.to_cochain_complex.d (0 - 1 + 1)) := by { convert S.is_mono, simp, },
      apply @image_to_kernel_map_epi_of_zero_of_mono _ _ _ _ _ _ _ _ _ _ _,
      assumption, },
    { -- exactness at B
      convert S.exact; simp, },
    { -- exactness at C
      have E : epi (S.to_cochain_complex.d (2 - 1)) := by { convert S.is_epi, simp, },
      convert @image_to_kernel_map_epi_of_epi_of_zero _ _ _ _ _ _ _ _ _ E _,
      sorry,
      sorry,
      sorry,
      sorry, }, }
end

end short_exact_sequence
