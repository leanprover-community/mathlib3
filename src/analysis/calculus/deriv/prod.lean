import analysis.calculus.deriv.basic
import analysis.calculus.fderiv.prod

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

section cartesian_product
/-! ### Derivative of the cartesian product of two functions -/

variables {G : Type w} [normed_add_comm_group G] [normed_space 𝕜 G]
variables {f₂ : 𝕜 → G} {f₂' : G}

lemma has_deriv_at_filter.prod
  (hf₁ : has_deriv_at_filter f₁ f₁' x L) (hf₂ : has_deriv_at_filter f₂ f₂' x L) :
  has_deriv_at_filter (λ x, (f₁ x, f₂ x)) (f₁', f₂') x L :=
hf₁.prod hf₂

lemma has_deriv_within_at.prod
  (hf₁ : has_deriv_within_at f₁ f₁' s x) (hf₂ : has_deriv_within_at f₂ f₂' s x) :
  has_deriv_within_at (λ x, (f₁ x, f₂ x)) (f₁', f₂') s x :=
hf₁.prod hf₂

lemma has_deriv_at.prod (hf₁ : has_deriv_at f₁ f₁' x) (hf₂ : has_deriv_at f₂ f₂' x) :
  has_deriv_at (λ x, (f₁ x, f₂ x)) (f₁', f₂') x :=
hf₁.prod hf₂

lemma has_strict_deriv_at.prod (hf₁ : has_strict_deriv_at f₁ f₁' x)
  (hf₂ : has_strict_deriv_at f₂ f₂' x) :
  has_strict_deriv_at (λ x, (f₁ x, f₂ x)) (f₁', f₂') x :=
hf₁.prod hf₂

end cartesian_product

section pi

/-! ### Derivatives of functions `f : 𝕜 → Π i, E i` -/

variables {ι : Type*} [fintype ι] {E' : ι → Type*} [Π i, normed_add_comm_group (E' i)]
  [Π i, normed_space 𝕜 (E' i)] {φ : 𝕜 → Π i, E' i} {φ' : Π i, E' i}

@[simp] lemma has_strict_deriv_at_pi :
  has_strict_deriv_at φ φ' x ↔ ∀ i, has_strict_deriv_at (λ x, φ x i) (φ' i) x :=
has_strict_fderiv_at_pi'

@[simp] lemma has_deriv_at_filter_pi :
  has_deriv_at_filter φ φ' x L ↔
    ∀ i, has_deriv_at_filter (λ x, φ x i) (φ' i) x L :=
has_fderiv_at_filter_pi'

lemma has_deriv_at_pi :
  has_deriv_at φ φ' x ↔ ∀ i, has_deriv_at (λ x, φ x i) (φ' i) x:=
has_deriv_at_filter_pi

lemma has_deriv_within_at_pi :
  has_deriv_within_at φ φ' s x ↔ ∀ i, has_deriv_within_at (λ x, φ x i) (φ' i) s x:=
has_deriv_at_filter_pi

lemma deriv_within_pi (h : ∀ i, differentiable_within_at 𝕜 (λ x, φ x i) s x)
  (hs : unique_diff_within_at 𝕜 s x) :
  deriv_within φ s x = λ i, deriv_within (λ x, φ x i) s x :=
(has_deriv_within_at_pi.2 (λ i, (h i).has_deriv_within_at)).deriv_within hs

lemma deriv_pi (h : ∀ i, differentiable_at 𝕜 (λ x, φ x i) x) :
  deriv φ x = λ i, deriv (λ x, φ x i) x :=
(has_deriv_at_pi.2 (λ i, (h i).has_deriv_at)).deriv

end pi

