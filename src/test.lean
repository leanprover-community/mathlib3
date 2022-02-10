import analysis.calculus.inverse

lemma Pi.complete_nondep {ι : Type*} (α : Type*) [uniform_space α]
[complete_space α] : complete_space (ι → α) :=
Pi.complete _

lemma zou (ι : Type*) [h : fintype ι] :
@complete_space (ι → ℝ)
  (@metric_space.to_uniform_space' (ι → ℝ)
     (@semi_normed_group.to_pseudo_metric_space (ι → ℝ)
        (@normed_group.to_semi_normed_group (ι → ℝ)
           (@pi.normed_group ι (λ (ᾰ : ι), ℝ) h (λ (i : ι), real.normed_group))))) :=
begin
  apply Pi.complete_nondep ℝ
end
