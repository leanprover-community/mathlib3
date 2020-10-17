import data.polynomial.reverse
import data.polynomial.degree.trailing_degree

open finset

namespace polynomial

namespace rev

variables {R : Type*} [semiring R] {f : polynomial R}

@[simp] lemma reflect_ne_zero_iff {N : ℕ} {f : polynomial R} :
  reflect N (f : polynomial R) ≠ 0 ↔ f ≠ 0 :=
not_congr reflect_eq_zero_iff

@[simp] lemma rev_at_gt {N n : ℕ} (H : N < n) : rev_at N n = n :=
begin
  rw [rev_at, function.embedding.coe_fn_mk],
  split_ifs,
    { exfalso,
      exact nat.lt_le_antisymm H h, },
  { refl, },
end

@[simp] lemma reflect_invol (N : ℕ) : reflect N (reflect N f) = f :=
begin
  ext,
  rw [coeff_reflect, coeff_reflect, rev_at_invol],
end

/-- `mon` is the property of being monotone non-increasing. -/
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

/-- `monotone_rev_at N _` coincides with `rev_at N _` in the range [0,..,N].  I use
`monotone_rev_at` just to show that `rev_at` exchanges `min`s and `max`s.  With an alternative
proof of the exchange property that does not use this definition, it can be removed! -/
def monotone_rev_at (N : ℕ) : ℕ → ℕ := λ i : ℕ , (N-i)

lemma monotone_rev_at_monotone (N : ℕ) : mon (monotone_rev_at N) :=
begin
  intros x y hxy,
  rw [monotone_rev_at, nat.sub_le_iff],
  by_cases xle : x ≤ N,
  { rwa nat.sub_sub_self xle, },
  { rw not_le at xle,
    apply le_of_lt,
    convert gt_of_ge_of_gt hxy xle,
    convert nat.sub_zero N,
    exact nat.sub_eq_zero_iff_le.mpr (le_of_lt xle), },
end

lemma monotone_rev_at_max'_min' {N : ℕ} {s : finset ℕ} {hs : s.nonempty} (H : s.max' hs ≤ N) :
  max' (image (monotone_rev_at N) s) (nonempty.image hs (monotone_rev_at N)) =
  monotone_rev_at N (min' s hs) :=
monotone_max'_min' hs (monotone_rev_at_monotone N)

@[simp] lemma monotone_rev_at_eq_rev_at_small {N n : ℕ} :
  (n ≤ N) → rev_at N n = monotone_rev_at N n :=
begin
  intro H,
  rw rev_at_le H,
  refl,
end

lemma rev_at_small_min_max {N : ℕ} {s : finset ℕ} {hs : s.nonempty} {sm : s.max' hs ≤ N} :
  max' (image (rev_at N) s) ((nonempty.image hs (rev_at N))) = rev_at N (min' s hs) :=
begin
  rwa [monotone_rev_at_eq_rev_at_small, ← monotone_rev_at_max'_min' sm],
  have im : (image (rev_at N) s) = (image (monotone_rev_at N) s) →
    (image (rev_at N) s).max' ((nonempty.image hs (rev_at N))) =
    (image (monotone_rev_at N) s).max' ((nonempty.image hs (monotone_rev_at N))),
  { intro a,
    simp only [a], },
  apply im,
  ext1 a,
  repeat { rw mem_image },
  split;
  { rintro ⟨ a, ha, rfl⟩ ,
    use a,
    refine ⟨ ha , by rw (monotone_rev_at_eq_rev_at_small (le_trans (le_max' _ _ ha) sm)) ⟩, },
  { exact le_trans (le_max' _ _ (min'_mem s hs)) sm, },
end

lemma nat_degree_reflect_le {N : ℕ} : (reflect N f).nat_degree ≤ max N f.nat_degree :=
begin
  by_cases f0 : f=0,
  { rw [f0, reflect_zero, nat_degree_zero], exact zero_le (max N 0), },
  by_cases dsm : f.nat_degree ≤ N,
  { rw [max_eq_left dsm, nat_degree_eq_support_max' (reflect_ne_zero_iff.mpr f0)],
    apply max'_le,
    intros y hy,
    rw [reflect_support, mem_image] at hy,
    rcases hy with ⟨ y , hy , rfl⟩,
    rw rev_at_le (le_trans (le_nat_degree_of_mem_supp y hy) dsm),
    exact nat.sub_le N y, },
  { rw not_le at dsm,
    rw [max_eq_right  (le_of_lt dsm), nat_degree_eq_support_max', nat_degree_eq_support_max' f0],
    { apply max'_le,
      rw ← nat_degree_eq_support_max',
      intros y hy,
      rw [reflect_support, mem_image] at hy,
      rcases hy with ⟨ y , hy , rfl ⟩,
      by_cases ys : y ≤ N,
      { rw rev_at_le ys, exact le_of_lt (gt_of_gt_of_ge dsm (nat.sub_le N y)), },
      { rw rev_at_gt (not_le.mp ys), exact le_nat_degree_of_mem_supp _ hy, }, },
    { rwa [ne.def, (@reflect_eq_zero_iff R _ N f)], }, },
end


lemma lead_reflect_eq_trailing {N : ℕ} (H : f.nat_degree ≤ N) :
  leading_coeff (reflect N f) = trailing_coeff f :=
begin
  by_cases f0 : f = 0,
  { rw [f0, reflect_zero, leading_coeff, trailing_coeff, coeff_zero, coeff_zero], },
  have c : (reflect N f).leading_coeff = (reflect N f).coeff (reflect N f).nat_degree, by congr,
  have d : f.trailing_coeff = f.coeff f.nat_trailing_degree, by congr,
  have rfn0 : reflect N f ≠ 0 := reflect_ne_zero_iff.mpr f0,
  rw [c, d, nat_trailing_degree_eq_support_min' f0, nat_degree_eq_support_max' rfn0],
  simp_rw [coeff_reflect, reflect_support],
  rw [rev_at_small_min_max, rev_at_invol],
  convert H,
  rw nat_degree_eq_support_max',
end

lemma trailing_reflect_eq_lead {N : ℕ} (H : f.nat_degree ≤ N) :
  trailing_coeff (reflect N f) = leading_coeff f :=
begin
  conv_rhs { rw ← @reflect_invol R _ f N },
  rw lead_reflect_eq_trailing,
  convert @nat_degree_reflect_le R _ f N,
  rwa max_eq_left,
end

lemma lead_reverse_eq_trailing (f : polynomial R) : leading_coeff (reverse f) = trailing_coeff f :=
lead_reflect_eq_trailing rfl.le

lemma trailing_reverse_eq_lead (f : polynomial R) : trailing_coeff (reverse f) = leading_coeff f :=
trailing_reflect_eq_lead rfl.le

lemma trailing_degree_add_le (p q : polynomial R) : min (nat_trailing_degree p) (nat_trailing_degree q) ≤ nat_trailing_degree (p + q) :=
begin
  rw @nat_trailing_degree_eq_support_min' R _ (p+q) _,
  rw @nat_trailing_degree_eq_support_min' R _ p _,
  rw @nat_trailing_degree_eq_support_min' R _ q _,
  let N : ℕ := (max p.nat_degree q.nat_degree),
  conv_lhs { congr,
    congr,
    congr,
    rw ← @reflect_invol R _ p N,
    congr,
    skip,
    skip,
    congr,
    congr,
    rw ← @reflect_invol R _ q N },
  simp_rw reflect_support,
  simp_rw ← rev_at_le_min_max,
  simp_rw (@lead_reflect_eq_trailing R _ (reflect N p) N),

  rw ← @reflect_invol R _ q N,
  sorry,
--calc trailing_degree (p + q) = ((p + q).support).inf some : rfl
--  ... ≤ (p.support ∪ q.support).inf some : by convert sup_mono support_add
--  ... = p.support.inf some ⊔ q.support.inf some : by convert sup_union
--  ... = _ : with_top.sup_eq_max _ _
end

end rev

end polynomial
