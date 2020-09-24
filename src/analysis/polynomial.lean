import data.real.basic
import data.polynomial.default
import data.set.intervals.infinite

section real
variables (f : polynomial ℝ)
open set polynomial

lemma f_zero_on_interval_f_zero {a b : ℝ} (h : a < b) (f_zero: ∀ x ∈ Icc a b, f.eval x = 0) : f = 0 :=
begin
    by_contra absurd,
    set roots := roots f with hroots,
    have absurd2 : ∀ x ∈ Icc a b, x ∈ roots,
    { intros a ha, rw hroots,
      rw [mem_roots absurd, is_root.def], exact f_zero a ha },
    have absurd3 : finite (Icc a b),
    { refine @finite.subset _ (↑roots.to_finset) (multiset.to_finset roots).finite_to_set _ _,
      { intros x h, simp only [multiset.mem_to_finset, finset.mem_coe], exact absurd2 _ h } },

    suffices : set.infinite (Icc a b),
    { exact this absurd3 },
    { rw ←infinite_coe_iff, exact infinite_Icc h }
end

end real
