import data.set.basic data.set.lattice data.nat.parity
import tactic.linarith

open set nat function

open_locale classical

variables {α : Type*} {β : Type*} {γ : Type*} {I : Type*}

/-!
## Set exercises

These are collected from *Mathematics in Lean*.

We will go over the examples together, and then let you
work on the exercises.

There is more material here than can fit in the sessions,
but we will pick and choose as we go.
-/

section set_variables

variable  x : α
variables s t u : set α

/-!
### Notation
-/

#check s ⊆ t        -- \sub
#check x ∈ s        -- \in or \mem
#check x ∉ s        -- \notin
#check s ∩ t        -- \i or \cap
#check s ∪ t        -- \un or \cup
#check (∅ : set α)  -- \empty

/-!
### Examples
-/

-- Three proofs of the same fact.
-- The first two expand definitions explicitly,
-- while the third forces Lean to do the unfolding.

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  rw [subset_def, inter_def, inter_def],
  rw subset_def at h,
  dsimp,
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  simp only [subset_def, mem_inter_eq] at *,
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  intros x xsu,
  exact ⟨h xsu.1, xsu.2⟩
end

-- Use `cases` or `rcases` or `rintros` with union.
-- Two proofs of the same fact, one longer and one shorter.

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  intros x hx,
  have xs : x ∈ s := hx.1,
  have xtu : x ∈ t ∪ u := hx.2,
  cases xtu with xt xu,
  { left,
    show x ∈ s ∩ t,
    exact ⟨xs, xt⟩ },
  right,
  show x ∈ s ∩ u,
  exact ⟨xs, xu⟩
end

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  rintros x ⟨xs, xt | xu⟩,
  { left, exact ⟨xs, xt⟩ },
  right, exact ⟨xs, xu⟩
end

-- Two examples with set difference.
-- Type it as ``\\``.
-- ``x ∈ s \ t`` expands to ``x ∈ s ∧ x ∉ t``.

example : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  have xs : x ∈ s := xstu.1.1,
  have xnt : x ∉ t := xstu.1.2,
  have xnu : x ∉ u := xstu.2,
  split,
  { exact xs }, dsimp,
  intro xtu, -- x ∈ t ∨ x ∈ u
  cases xtu with xt xu,
  { show false, from xnt xt },
  show false, from xnu xu
end

example : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨xs, xnt⟩, xnu⟩,
  use xs,
  rintros (xt | xu); contradiction
end

/-!
### Exercises
-/

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
sorry

example : s \ (t ∪ u) ⊆ s \ t \ u :=
sorry

/-!
### Proving two sets are equal
-/

-- the ext tactic

example : s ∩ t = t ∩ s :=
begin
  ext x,
  -- simp only [mem_inter_eq],  -- optional.
  split,
  { rintros ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
  rintros ⟨xt, xs⟩, exact ⟨xs, xt⟩
end

example : s ∩ t = t ∩ s :=
by ext x; simp [and.comm]

/-!
### Exercises
-/

example : s ∩ (s ∪ t) = s :=
sorry

example : s ∪ (s ∩ t) = s :=
sorry

example : (s \ t) ∪ t = s ∪ t :=
sorry

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
sorry

/-!
### Set-builder notation
-/

def evens : set ℕ := {n | even n}
def odds :  set ℕ := {n | ¬ even n}

example : evens ∪ odds = univ :=
begin
  rw [evens, odds],
  ext n,
  simp,
  apply classical.em
end

example : s ∩ t = {x | x ∈ s ∧ x ∈ t} := rfl
example : s ∪ t = {x | x ∈ s ∨ x ∈ t} := rfl
example : (∅ : set α) = {x | false} := rfl
example : (univ : set α) = {x | true} := rfl

example (x : ℕ) (h : x ∈ (∅ : set ℕ)) : false :=
h

example (x : ℕ) : x ∈ (univ : set ℕ) :=
trivial

/-!
### Exercise
-/

-- Use `intro n` to unfold the definition of subset,
-- and use the simplifier to reduce the
-- set-theoretic constructions to logic.
-- We also recommend using the theorems
-- ``prime.eq_two_or_odd`` and ``even_iff``.

example : { n | prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } :=
sorry

/-!
Indexed unions
-/

-- See *Mathematics in Lean* for a discussion of
-- bounded quantifiers, which we will skip here.

section

-- We can use any index type in place of ℕ
variables A B : ℕ → set α

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Union],
  split,
  { rintros ⟨xs, ⟨i, xAi⟩⟩,
    exact ⟨i, xAi, xs⟩ },
  rintros ⟨i, xAi, xs⟩,
  exact ⟨xs, ⟨i, xAi⟩⟩
end

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Inter],
  split,
  { intro h,
    split,
    { intro i,
      exact (h i).1 },
    intro i,
    exact (h i).2 },
  rintros ⟨h1, h2⟩ i,
  split,
  { exact h1 i },
  exact h2 i
end

end

/-!
### Exercise
-/

-- One direction requires classical logic!
-- We recommend using ``by_cases xs : x ∈ s``
-- at an appropriate point in the proof.

section

variables A B : ℕ → set α

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
sorry

end

/-
Mathlib also has bounded unions and intersections,
`⋃ x ∈ s, f x` and `⋂ x ∈ s, f x`,
and set unions and intersections, `⋃₀ s` and `⋂₀ s`,
where `s : set α`.

See *Mathematics in Lean* for details.
-/

end set_variables

/-!
### Functions
-/

section function_variables

variable  f : α → β
variables s t : set α
variables u v : set β
variable  A : I → set α
variable  B : I → set β

#check f '' s
#check image f s
#check f ⁻¹' u    -- type as \inv' and then hit space or tab
#check preimage f u

example : f '' s = {y | ∃ x, x ∈ s ∧ f x = y} := rfl
example : f ⁻¹' u = {x | f x ∈ u } := rfl

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by { ext, refl }

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y, split,
  { rintros ⟨x, xs | xt, rfl⟩,
    { left, use [x, xs] },
    right, use [x, xt] },
  rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
  { use [x, or.inl xs] },
  use [x, or.inr xt]
end

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  show f x ∈ f '' s,
  use [x, xs]
end

/-!
### Exercises
-/

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
sorry

example (h : injective f) : f ⁻¹' (f '' s) ⊆ s :=
sorry

example : f '' (f⁻¹' u) ⊆ u :=
sorry

example (h : surjective f) : u ⊆ f '' (f⁻¹' u) :=
sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t :=
sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
sorry

example (h : injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u :=
sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
sorry

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
sorry

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
sorry

example (i : I) (injf : injective f) : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
sorry

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
sorry

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
sorry

/-
There is a lot more in *Mathematics in Lean* that we will not have time for!
There is a discussion of injectivity, more exercises on images and ranges,
and a discussion of inverses.

But we will close with on last exercise. Remember that `surjective f`
says `∀ y, ∃ x, f x = y`.

See if you can understand the proof of Cantor's famous theorem that there is no
surjective function from its set to its powerset, and
fill in the two lines that are missing.
-/

theorem Cantor : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := { i | i ∉ f i},
  rcases surjf S with j,
  have h₁ : j ∉ f j,
  { intro h',
    have : j ∉ f j,
      { by rwa h at h' },
    contradiction },
  have h₂ : j ∈ S,
sorry
    ,
  have h₃ : j ∉ S,
sorry
    ,
  contradiction
end

end function_variables

