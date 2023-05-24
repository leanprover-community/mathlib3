import analysis.calculus.deriv

/-! ### Support of derivatives -/

section support

open function
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F] {f : 𝕜 → F}

lemma support_deriv_subset : support (deriv f) ⊆ tsupport f :=
begin
  intros x,
  rw [← not_imp_not],
  intro h2x,
  rw [not_mem_tsupport_iff_eventually_eq] at h2x,
  exact nmem_support.mpr (h2x.deriv_eq.trans (deriv_const x 0))
end

lemma has_compact_support.deriv (hf : has_compact_support f) : has_compact_support (deriv f) :=
hf.mono' support_deriv_subset

end support
