import .exact_seq
import .abelian_category

noncomputable theory

open category_theory
open category_theory.limits

universes v u

variables {𝒜 : Type u} [category.{v} 𝒜] [abelian 𝒜]
variables {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C}

namespace category_theory

namespace exact_seq

lemma drop : ∀ {L : list (arrow 𝒜)} (h : exact_seq 𝒜 L) (n : ℕ),
  exact_seq 𝒜 (L.drop n)
| _ nil               0     := nil
| _ nil               (n+1) := nil
| _ (single f)        0     := single f
| _ (single f)        (n+1) := drop nil n
| _ (cons f g h L hL) 0     := cons f g h L hL
| _ (cons f g h L hL) (n+1) := hL.drop n

lemma pair : ∀ {L : list (arrow 𝒜)} (h : exact_seq 𝒜 (f :: g :: L)),
  exact f g
| L (cons _ _ h _ _) := h

end exact_seq

namespace exact

lemma mono_of_eq_zero (h : exact f g) (hf : f = 0) : mono g :=
by rwa [(abelian.tfae_mono A g).out 0 2, ← hf]

lemma eq_zero_of_mono (h : exact f g) (hg : mono g) : f = 0 :=
by rw [← cancel_mono g, h.w, zero_comp]

lemma mono_iff_eq_zero (h : exact f g) : mono g ↔ f = 0 :=
⟨h.eq_zero_of_mono, h.mono_of_eq_zero⟩

lemma epi_of_eq_zero (h : exact f g) (hg : g = 0) : category_theory.epi f :=
by rwa [(abelian.tfae_epi C f).out 0 2, ← hg]

lemma eq_zero_of_epi (h : exact f g) (hf : category_theory.epi f) : g = 0 :=
by rw [← cancel_epi f, h.w, comp_zero]

lemma epi_iff_eq_zero (h : exact f g) : category_theory.epi f ↔ g = 0 :=
⟨h.eq_zero_of_epi, h.epi_of_eq_zero⟩

lemma mono_of_is_zero (h : exact f g) (hA : is_zero A) : mono g :=
by { rw h.mono_iff_eq_zero, exact hA.eq_of_src f _ }

lemma epi_of_is_zero (h : exact f g) (hA : is_zero C) : category_theory.epi f :=
by { rw h.epi_iff_eq_zero, exact hA.eq_of_tgt g _ }

lemma is_zero_of_eq_zero_eq_zero (h : exact f g) (hf : f = 0) (hg : g = 0) : is_zero B :=
is_zero_of_exact_zero_zero' _ _ h hf hg

lemma is_zero_of_is_zero_is_zero (h : exact f g) (hA : is_zero A) (hC : is_zero C) : is_zero B :=
is_zero_of_exact_is_zero_is_zero _ _ h hA hC

protected lemma exact_seq (h : exact f g) : exact_seq 𝒜 [f, g] :=
(exact_iff_exact_seq _ _).mp h

lemma cons (h : exact f g) {L : list (arrow 𝒜)} (hL : exact_seq 𝒜 (g :: L)) :
  exact_seq 𝒜 (f :: g :: L) :=
exact_seq.cons f g h L hL

end exact

end category_theory
