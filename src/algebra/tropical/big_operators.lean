import algebra.tropical.lattice
import algebra.big_operators.basic
import data.list.min_max

open_locale big_operators

variables {R S : Type*}

open tropical

lemma list.trop_sum [add_monoid R] (l : list R) : trop l.sum = list.prod (l.map trop) :=
begin
  induction l with hd tl IH,
  { simp },
  { simp [←IH] }
end

lemma multiset.trop_sum [add_comm_monoid R] (s : multiset R) :
  trop s.sum = multiset.prod (s.map trop) :=
quotient.induction_on s (by simpa using list.trop_sum)

lemma trop_sum [add_comm_monoid R] (s : finset S) (f : S → R) :
  trop (∑ i in s, f i) = ∏ i in s, trop (f i) :=
begin
  cases s,
  convert multiset.trop_sum _,
  simp
end

lemma fintype.trop_sum [add_comm_monoid R] [fintype S] (f : S → R) :
  trop (∑ i : S, f i) = ∏ i : S, trop (f i) :=
trop_sum _ _

lemma list.untrop_prod [add_monoid R] (l : list (tropical R)) :
  untrop l.prod = list.sum (l.map untrop) :=
begin
  induction l with hd tl IH,
  { simp },
  { simp [←IH] }
end

lemma multiset.untrop_prod [add_comm_monoid R] (s : multiset (tropical R)) :
  untrop s.prod = multiset.sum (s.map untrop) :=
quotient.induction_on s (by simpa using list.untrop_prod)

lemma untrop_prod [add_comm_monoid R] (s : finset S) (f : S → tropical R) :
  untrop (∏ i in s, f i) = ∑ i in s, untrop (f i) :=
begin
  cases s,
  convert multiset.untrop_prod _,
  simp
end

lemma fintype.untrop_prod [add_comm_monoid R] [fintype S] (f : S → tropical R) :
  untrop (∏ i : S, f i) = ∑ i : S, untrop (f i) :=
untrop_prod _ _

lemma list.trop_minimum [linear_order R] (l : list R) :
  trop l.minimum = list.sum (l.map (trop ∘ coe)) :=
begin
  induction l with hd tl IH,
  { simp },
  { simp [list.minimum_cons, ←IH] }
end

lemma multiset.trop_inf [h : linear_order R] [h' : order_top R] (s : multiset R) :
  trop s.inf = multiset.sum (s.map trop) :=
begin
  induction s using multiset.induction with s x IH,
  { simp },
  { simp [←IH] }
end

lemma finset.trop_inf [h : linear_order R] [h' : order_top R] (s : finset S) (f : S → R) :
  trop (s.inf f) = ∑ i in s, trop (f i) :=
begin
  cases s,
  convert multiset.trop_inf _,
  simp
end

lemma trop_Inf_image [conditionally_complete_linear_order R] (s : finset S)
  (f : S → with_top R) : trop (Inf (f '' s)) = ∑ i in s, trop (f i) :=
begin
  rcases s.eq_empty_or_nonempty with rfl|h,
  { simp only [set.image_empty, finset.coe_empty, finset.sum_empty, with_top.cInf_empty, trop_top] },
  rw [←finset.inf'_eq_cInf_image _ h, finset.inf'_eq_inf],
  convert s.trop_inf f,
  refine lattice.ext _,
  intros,
  exact iff.rfl
end

lemma trop_infi [conditionally_complete_linear_order R] [fintype S] (f : S → with_top R) :
  trop (⨅ (i : S), f i) = ∑ (i : S), trop (f i) :=
by rw [infi, ←set.image_univ, ←finset.coe_univ, trop_Inf_image]

lemma multiset.untrop_sum [h : linear_order R] [h' : order_top R] (s : multiset (tropical R)) :
  untrop s.sum = multiset.inf (s.map untrop) :=
begin
  induction s using multiset.induction with s x IH,
  { simp },
  { simpa [←IH] }
end

lemma finset.untrop_sum [h : linear_order R] [h' : order_top R] (s : finset S)
  (f : S → tropical R) : untrop (∑ i in s, f i) = s.inf (untrop ∘ f) :=
begin
  cases s,
  convert multiset.untrop_sum _,
  simpa
end

lemma untrop_sum_eq_Inf_image [conditionally_complete_linear_order R] (s : finset S)
  (f : S → tropical (with_top R)) :
  untrop (∑ i in s, f i) = Inf (untrop ∘ f '' s) :=
begin
  rcases s.eq_empty_or_nonempty with rfl|h,
  { simp only [set.image_empty, finset.coe_empty, finset.sum_empty,
               with_top.cInf_empty, untrop_zero] },
  rw [←finset.inf'_eq_cInf_image _ h, finset.inf'_eq_inf],
  convert s.untrop_sum f,
  refine lattice.ext _,
  intros,
  exact iff.rfl
end

lemma untrop_sum [conditionally_complete_linear_order R] [fintype S]
  (f : S → tropical (with_top R)) :
  untrop (∑ i : S, f i) = ⨅ i : S, untrop (f i) :=
by rw [infi, ←set.image_univ, ←finset.coe_univ, untrop_sum_eq_Inf_image]
