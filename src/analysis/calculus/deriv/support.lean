import analysis.calculus.deriv.basic

universes u v w
noncomputable theory
open_locale classical topology big_operators filter ennreal
open filter asymptotics set
open continuous_linear_map (smul_right smul_right_one_eq_iff)


variables {𝕜 : Type u} [nontrivially_normed_field 𝕜]
variables {F : Type v} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {E : Type w} [normed_add_comm_group E] [normed_space 𝕜 E]

variables {f f₀ f₁ g : 𝕜 → F}
variables {f' f₀' f₁' g' : F}
variables {x : 𝕜}
variables {s t : set 𝕜}
variables {L L₁ L₂ : filter 𝕜}

/-! ### Support of derivatives -/

section support

open function

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
