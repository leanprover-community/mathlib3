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
-- sorry
begin
  rintros x (⟨xs, xt⟩ | ⟨xs, xu⟩),
  { use xs, left, exact xt },
  use xs, right, exact xu
end
-- sorry

example : s \ (t ∪ u) ⊆ s \ t \ u :=
-- sorry
begin
  rintros x ⟨xs, xntu⟩,
  use xs,
  { intro xt, exact xntu (or.inl xt) },
  intro xu, exact xntu (or.inr xu)
end
-- sorry

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
-- sorry
begin
  ext x, split,
  { rintros ⟨xs, _⟩, exact xs },
  intro xs,
  use xs, left, exact xs
end
-- sorry

example : s ∪ (s ∩ t) = s :=
-- sorry
begin
  ext x, split,
  { rintros (xs | ⟨xs, xt⟩); exact xs },
  intro xs, left, exact xs
end
-- sorry

example : (s \ t) ∪ t = s ∪ t :=
-- sorry
begin
  ext x, split,
  { rintros (⟨xs, nxt⟩ | xt),
    { left, exact xs},
    right, exact xt },
  by_cases h : x ∈ t,
  { intro _, right, exact h },
  rintros (xs | xt),
  { left, use [xs, h] },
  right, use xt
end
-- sorry

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
-- sorry
begin
  ext x, split,
  { rintros (⟨xs, xnt⟩ | ⟨xt, xns⟩),
    { split, left, exact xs,
      rintros ⟨_, xt⟩, contradiction },
    split , right, exact xt,
    rintros ⟨xs, _⟩, contradiction },
  rintros ⟨xs | xt, nxst⟩,
  { left, use xs, intro xt,
    apply nxst,
    split; assumption },
  right, use xt, intro xs,
  apply nxst,
  split; assumption
end
-- sorry

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
-- sorry
begin
  intro n,
  simp,
  intro nprime,
  cases prime.eq_two_or_odd nprime with h h,
  { rw h, intro, linarith },
  rw [even_iff, h],
  norm_num
end
-- sorry

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
-- sorry
begin
  ext x,
  simp only [mem_union, mem_Inter],
  split,
  { rintros (xs | xI),
    { intro i, right, exact xs },
    intro i, left, exact xI i },
  intro h,
  by_cases xs : x ∈ s,
  { left, exact xs },
  right,
  intro i,
  cases h i,
  { assumption },
  contradiction
end
-- sorry

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
-- sorry
begin
  split,
  { intros h x xs,
    have : f x ∈ f '' s,
    from mem_image_of_mem _ xs,
    exact h this },
  intros h y ymem,
  rcases ymem with ⟨x, xs, fxeq⟩,
  rw ← fxeq,
  apply h xs
end
-- sorry

example (h : injective f) : f ⁻¹' (f '' s) ⊆ s :=
-- sorry
begin
  rintros x ⟨y, ys, fxeq⟩,
  rw ← h fxeq,
  exact ys
end
-- sorry

example : f '' (f⁻¹' u) ⊆ u :=
-- sorry
begin
  rintros y ⟨x, xmem, rfl⟩,
  exact xmem
end
-- sorry

example (h : surjective f) : u ⊆ f '' (f⁻¹' u) :=
-- sorry
begin
  intros y yu,
  rcases h y with ⟨x, fxeq⟩,
  use x,
  split,
  { show f x ∈ u,
    rw fxeq, exact yu },
  exact fxeq
end
-- sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t :=
-- sorry
begin
  rintros y ⟨x, xs, fxeq⟩,
  use [x, h xs, fxeq]
end
-- sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
-- sorry
by intro x; apply h
-- sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
-- sorry
by ext x; refl
-- sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
-- sorry
sorry
-- sorry

example (h : injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
-- sorry
sorry
-- sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
-- sorry
sorry
-- sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
-- sorry
sorry
-- sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
-- sorry
sorry
-- sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u :=
-- sorry
sorry
-- sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
-- sorry
sorry
-- sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
-- sorry
sorry
-- sorry

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
-- sorry
begin
  ext y, simp,
  split,
  { rintros ⟨x, ⟨i, xAi⟩, fxeq⟩,
    use [i, x, xAi, fxeq] },
  rintros ⟨i, x, xAi, fxeq⟩,
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩
end
-- sorry

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
-- sorry
begin
  intro y, simp,
  intros x h fxeq i,
  use [x, h i, fxeq],
end
-- sorry

example (i : I) (injf : injective f) : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
-- sorry
begin
  intro y, simp,
  intro h,
  rcases h i with ⟨x, xAi, fxeq⟩,
  use x, split,
  { intro i',
    rcases h i' with ⟨x', x'Ai, fx'eq⟩,
    have : f x = f x', by rw [fxeq, fx'eq],
    have : x = x', from injf this,
    rw this,
    exact x'Ai },
  exact fxeq
end
-- sorry

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
-- sorry
by { ext x, simp }
-- sorry

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
-- sorry
by { ext x, simp }
-- sorry

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
-- sorry
    from h₁
-- sorry
    ,
  have h₃ : j ∉ S,
-- sorry
    by rwa h at h₁
-- sorry
    ,
  contradiction
end

end function_variables
