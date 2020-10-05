import data.polynomial.degree.reverse

open finset

namespace polynomial

namespace rev

variables {R : Type*} [semiring R] {f : polynomial R}

@[simp] lemma rev_at_large {N n : ℕ} (H : N < n) : rev_at N n = n :=
begin
  unfold rev_at,
  split_ifs,
    { exfalso,
      exact nat.lt_le_antisymm H h, },
  { refl, },
end

lemma reflect_support (N : ℕ) : (reflect N f).support = (image (rev_at N) f.support) :=
rfl

@[simp] lemma reflect_invol (N : ℕ) : reflect N (reflect N f) = f :=
begin
  unfold reflect,
  simp_rw [coeff_mk, rev_at_invol],
  ext1,
  refl,
end

/-- mon is the property of being monotone non-increasing. -/
def mon {α β : Type*} [linear_order α] [linear_order β] (f : α → β) := ∀ ⦃x y : α⦄, x ≤ y → f y ≤ f x

lemma monotone_max'_min' {α β : Type*} [decidable_linear_order α] [decidable_linear_order β]
  {s : finset α} (hs : s.nonempty) {f : α → β} (mf : mon f) :
  max' (image f s) (hs.image f) = f (min' s hs) :=
begin
  apply le_antisymm _ (le_max' _ _ (mem_image_of_mem f (min'_mem s hs))),
  refine (image f s).max'_le (nonempty.image hs f) (f (min' s hs)) _,
  intros x hx,
  rw mem_image at hx,
  rcases hx with ⟨ b , bs , rfl⟩,
  exact mf (min'_le _ _ bs),
end

/-- monotone_rev_at N _ coincides with rev_at N _ in the range [0,..,N].  I use monotone_rev_at just to show that rev_at exchanges mins and maxs.  If you can find an alternative proof that does not use this definition, then it can be removed! -/
def monotone_rev_at (N : ℕ) : ℕ → ℕ := λ i : ℕ , (N-i)

lemma monotone_rev_at_monotone (N : ℕ) : mon (monotone_rev_at N) :=
begin
  intros x y hxy,
  unfold monotone_rev_at,
  rw nat.sub_le_iff,
  by_cases xle : x ≤ N,
    { rwa nat.sub_sub_self xle, },
    { rw not_le at xle,
      apply le_of_lt,
      convert gt_of_ge_of_gt hxy xle,
      convert nat.sub_zero N,
      exact nat.sub_eq_zero_iff_le.mpr (le_of_lt xle), },
end

lemma rev_at_max'_min' {N : ℕ} {s : finset ℕ} {hs : s.nonempty} (H : s.max' hs ≤ N) : max' (image (monotone_rev_at N) s) (nonempty.image hs (monotone_rev_at N)) = monotone_rev_at N (min' s hs) :=
monotone_max'_min' hs (monotone_rev_at_monotone N)

@[simp] lemma monotone_rev_at_eq_rev_at_small {N n : ℕ} : (n ≤ N) → rev_at N n = monotone_rev_at N n :=
begin
  intro H,
  rw rev_at_small H,
  refl,
end

lemma rev_at_small_min_max {N : ℕ} {s : finset ℕ} {hs : s.nonempty} {sm : s.max' hs ≤ N} : max' (image (rev_at N) s) ((nonempty.image hs (rev_at N))) = rev_at N (min' s hs) :=
begin
  rwa [monotone_rev_at_eq_rev_at_small, ← rev_at_max'_min' sm],
  have : (image (rev_at N) s) = (image (monotone_rev_at N) s) →
    (image (rev_at N) s).max' ((nonempty.image hs (rev_at N))) =
     (image (monotone_rev_at N) s).max' ((nonempty.image hs (monotone_rev_at N))),
    { intro,
      simp only [a], },
  apply this,
  ext1,
  repeat { rw mem_image },
  split;
    { intro,
      rcases a_1 with ⟨ a , ha , rfl ⟩ ,
      use a,
      refine ⟨ ha , by rw (monotone_rev_at_eq_rev_at_small (le_trans (le_max' _ _ ha) sm)) ⟩, },
  exact le_trans (le_max' _ _ (min'_mem s hs)) sm,
end

lemma nat_degree_reflect_le {N : ℕ} : (reflect N f).nat_degree ≤ max N f.nat_degree :=
begin
  by_cases f0 : f=0,
    { subst f0,
      rw [reflect_zero, nat_degree_zero],
      exact zero_le (max N 0), },
    { by_cases dsm : f.nat_degree ≤ N,
        { rw [max_eq_left dsm],
          rw (@nat_degree_eq_support_max' R _ (reflect N f)) (by rwa [ne.def, reflect_zero_iff]),
          apply max'_le,
          intros y hy,
          rw [reflect_support, mem_image] at hy,
          rcases hy with ⟨ y , hy , rfl⟩,
          rw rev_at_small (le_trans (le_nat_degree_of_mem_supp y hy) dsm),
          exact nat.sub_le N y, },
        { rw not_le at dsm,
          rw [max_eq_right  (le_of_lt dsm), nat_degree_eq_support_max', nat_degree_eq_support_max' f0],
            { apply max'_le,
              rw ← nat_degree_eq_support_max',
              intros y hy,
              rw [reflect_support, mem_image] at hy,
              rcases hy with ⟨ y , hy , rfl ⟩,
              by_cases ys : y ≤ N,
                { rw rev_at_small ys,
                  apply le_of_lt,
                  apply gt_of_gt_of_ge dsm,
                  exact nat.sub_le N y, },
                { rw not_le at ys,
                  rw rev_at_large ys,
                  apply le_nat_degree_of_mem_supp _ hy, }, },
          rwa [ne.def, (@reflect_zero_iff R _ N f)], }, },

end


lemma lead_reflect_eq_trailing {N : ℕ} (H : f.nat_degree ≤ N) :
 leading_coeff (reflect N f) = trailing_coeff f :=
begin
  by_cases f0 : f=0,
    { rw [f0, reflect_zero, leading_coeff, trailing_coeff, coeff_zero, coeff_zero], },
    { have c : (reflect N f).leading_coeff = (reflect N f).coeff (reflect N f).nat_degree, by congr,
      have d : f.trailing_coeff = f.coeff f.nat_trailing_degree, by congr,
      have rfn0 : reflect N f ≠ 0:=(not_congr (reflect_zero_iff f)).mpr f0,
      rw [c, d, nat_degree_eq_support_min'_trailing (f0), nat_degree_eq_support_max' rfn0],
      convert @rev_at_small_min_max N f.support (nonempty_support_iff.mpr f0) (by rwa ← nat_degree_eq_support_max'),
      unfold reflect,
      simp only [coeff_mk, eq_iff_iff],
      split,
        { intros a,
          rw (monotone_rev_at_eq_rev_at_small ),
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

lemma trailing_reflect_eq_lead {N : ℕ} (H : f.nat_degree ≤ N) :
 trailing_coeff (reflect N f) = leading_coeff f :=
begin
  conv_rhs {rw ← @reflect_invol R _ f N},
  rw lead_reflect_eq_trailing,
  convert @nat_degree_reflect_le R _ f N,
  rwa max_eq_left,
end

end rev

end polynomial
