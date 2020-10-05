import data.polynomial.degree.basic
import data.polynomial.degree.to_basic
import data.polynomial.degree.erase_lead
import data.polynomial.degree.reverse
import data.polynomial.degree.to_trailing_degree
import data.polynomial.degree.trailing_degree

open polynomial finsupp finset polynomial.erase_lead polynomial.rev

namespace polynomial

variables {R : Type*} [semiring R] {f : polynomial R}


/-- mon is the property of being monotone non-increasing. -/
def mon {α β : Type*} [linear_order α] [linear_order β] (f : α → β) := ∀ ⦃x y : α⦄, x ≤ y → f y ≤ f x

lemma monotone_max'_min' {α β : Type*} [decidable_linear_order α] [decidable_linear_order β]
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

/-- monotone_rev_at N _ coincides with rev_at N _ in the range [0,..,N].  I use monotone_rev_at just to show that rev_at exchanges mins and maxs.  If you can find an alternative proof that does not use this definition, then it can be removed! -/
def monotone_rev_at (N : ℕ) : ℕ → ℕ := λ i : ℕ , (N-i)

lemma rev_at_max'_min' {N : ℕ} {s : finset ℕ} {hs : s.nonempty} (H : s.max' hs ≤ N) : max' (image (monotone_rev_at N) s) (nonempty.image hs (monotone_rev_at N)) = monotone_rev_at N (min' s hs) :=
begin
  refine monotone_min_max hs _,
  intros x y hxy,
  unfold monotone_rev_at,
  rw nat.sub_le_iff,
  by_cases xle : x ≤ N,
    { rwa nat.sub_sub_self xle, },
    { rw not_le at xle,
      apply le_of_lt,
      convert gt_of_ge_of_gt hxy xle,
      convert nat.sub_zero N,
      rw nat.sub_eq_zero_iff_le,
      exact le_of_lt xle, },
end

@[simp] lemma monotone_rev_at_eq_rev_at_small {N n : ℕ} : (n ≤ N) → monotone_rev_at N n = rev_at N n :=
begin
  intro H,
  rw rev_at_small H,
  refl,
end



lemma rev_at_small_min_max {N : ℕ} {s : finset ℕ} {hs : s.nonempty} {sm : s.max' hs ≤ N} : max' (image (rev_at N) s) ((nonempty.image hs (rev_at N))) = rev_at N (min' s hs) :=
begin
  rwa [← monotone_rev_at_eq_rev_at_small, ← min_max sm],
  have : (image (rev_at N) s) = (image (monotone_rev_at N) s) →
    (image (rev_at N) s).max' ((nonempty.image hs (rev_at N))) = (image (monotone_rev_at N) s).max' ((nonempty.image hs (monotone_rev_at N))),
    { intro,
      simp only [a], },
  apply this,
  ext1,
  repeat { rw mem_image },
  split;
    { intro,
      rcases a_1 with ⟨ a , ha , rfl ⟩ ,
      use a,
      refine ⟨ ha , _ ⟩,
      rw monotone_rev_at_eq_rev_at_small,
      apply le_trans _ sm,
      apply le_max',
      assumption, },
  apply le_trans _ sm,
  apply le_max',
  exact min'_mem s hs,
end






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



--


lemma leading_eq_trailing {N : ℕ} (H : f.nat_degree ≤ N) :
 leading_coeff (reflect N f) = trailing_coeff f :=
begin
  by_cases f0 : f=0,
    { rw [f0, reflect_zero, leading_coeff, trailing_coeff, coeff_zero, coeff_zero], },
    { have c : (reflect N f).leading_coeff = (reflect N f).coeff (reflect N f).nat_degree, by congr,
      have d : f.trailing_coeff = f.coeff f.nat_trailing_degree, by congr,
      have rfn0 : reflect N f ≠ 0:=(not_congr reflect_zero_iff).mpr f0,
      rw [c, d, nat_degree_eq_support_min'_trailing (f0), nat_degree_eq_support_max' rfn0],
      convert @rev_at_small_min_max N f.support (nonempty_support_iff.mpr f0) (by rwa ← nat_degree_eq_support_max'),
      unfold reflect,
      simp only [coeff_mk, eq_iff_iff],
      split,
        { intros a,
          rw ← (monotone_rev_at_eq_rev_at_small ),
            { rw @rev_at_small_min_max N f.support _ (_ ),
              { rw monotone_rev_at_eq_rev_at_small,
                exact le_trans (min'_le _ _ (nat_degree_mem_support_of_nonzero f0)) H, },
              { apply le_trans _ H,
                convert le_refl f.nat_degree,
                rw nat_degree_eq_support_max', }, },
              { exact le_trans (min'_le _ _ (nat_degree_mem_support_of_nonzero f0)) H, }, },
        { intro,
          congr,
          simp only [*, rev_at_invol], }, },
end
