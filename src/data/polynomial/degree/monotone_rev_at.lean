import data.polynomial.degree.basic
import data.polynomial.degree.to_basic
import data.polynomial.degree.erase_lead
import data.polynomial.degree.reverse
import data.polynomial.degree.to_trailing_degree
import data.polynomial.degree.trailing_degree

open polynomial finsupp finset

namespace polynomial

variables {R : Type*} [semiring R] {f : polynomial R}

open erase_lead

def mon {α β : Type*} [linear_order α] [linear_order β] (f : α → β) := ∀ ⦃x y : α⦄, x ≤ y → f y ≤ f x

lemma min_max_mon {α β : Type*} [decidable_linear_order α] [decidable_linear_order β]
  {s : finset α} (hs : s.nonempty) {f : α → β} (mf : mon f) :
  max' (image f s) (hs.image f) = f (min' s hs) :=
begin
  apply le_antisymm,
    { refine (image f s).max'_le (nonempty.image hs f) (f (min' s hs)) _,
      intros x hx,
      rw mem_image at hx,
      rcases hx with ⟨ b , bs , rfl⟩,
      apply mf,
      apply min'_le,
      assumption, },
    { apply le_max',
      refine mem_image_of_mem f _,
      exact min'_mem s hs, },
end

def monotone_rev_at (N : ℕ) : ℕ → ℕ := λ i : ℕ , (N-i)

lemma min_max {s : finset ℕ} {hs : s.nonempty} : max' (image (monotone_rev_at (max' s hs)) s) (by exact nonempty.image hs (monotone_rev_at (max' s hs))) = monotone_rev_at (max' s hs) (min' s hs) :=
begin
  refine min_max_mon hs _,
  intros x y hxy,
  unfold monotone_rev_at,
  rw nat.sub_le_iff,
  by_cases xle : x ≤ (s.max' hs),
    { rwa nat.sub_sub_self xle, },
    { rw not_le at xle,
      apply le_of_lt,
      convert gt_of_ge_of_gt hxy xle,
      convert nat.sub_zero (s.max' hs),
      rw nat.sub_eq_zero_iff_le,
      exact le_of_lt xle, },
end

lemma monotone_rev_at_eq_rev_at_small {N n : ℕ} (n ≤ N) : monotone_rev_at N n = rev.rev_at N n :=
begin
  unfold monotone_rev_at,
  unfold rev.rev_at,
  split_ifs,
  refl,
end


lemma xxx {α β : Type*} {s : finset α} {hs : s.nonempty} {f : α → β} : (f '' ↑s).nonempty :=
set.nonempty_image_iff.mpr hs

lemma min'_rev_at_eq_max' {N : ℕ} {s : finset ℕ} {hs : s.nonempty} (H : s.max' hs ≤ N) : min' (image (rev.rev_at N) s) (hs.image (rev.rev_at N)) = max' s hs :=
begin
  unfold rev.rev_at,

  sorry,
end

#exit
