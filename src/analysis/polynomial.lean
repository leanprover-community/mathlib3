import data.real.basic
import data.polynomial.default
import data.set.intervals.infinite

section real
variables {a : ℝ} (f : polynomial ℝ)
open set polynomial

lemma f_zero_on_interval_f_zero (f_zero: ∀ x ∈ Icc (a-1) (a+1), f.eval x = 0) : f = 0 :=
begin
    by_contra absurd,
    set roots := roots f with hroots,
    have absurd2 : ∀ x ∈ (Icc (a-1) (a+1)), x ∈ roots,
    { intros a ha, rw hroots,
      rw [mem_roots absurd, is_root.def], exact f_zero a ha },
    have absurd3 : finite (Icc (a-1) (a+1)),
    { refine @finite.subset _ (↑roots.to_finset) (multiset.to_finset roots).finite_to_set _ _,
      { intros x h, simp only [multiset.mem_to_finset, finset.mem_coe], exact absurd2 _ h } },

    suffices : set.infinite (Icc (a-1) (a+1)),
    { exact this absurd3 },
    { rw ←infinite_coe_iff, refine infinite_Icc _, linarith }
end

end real
