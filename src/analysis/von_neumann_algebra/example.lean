import analysis.inner_product_space.pi_L2

noncomputable theory

variables (𝕜 : Type*) [is_R_or_C 𝕜] (H : Type*)

example [inner_product_space 𝕜 H] (ι : Type*) [fintype ι] :
  inner_product_space 𝕜 (pi_Lp 2 (λ i : ι, H)) := by apply_instance
example [inner_product_space 𝕜 H] [complete_space H] (ι : Type*) [fintype ι] :
  complete_space (pi_Lp 2 (λ i : ι, H)) := by apply_instance
