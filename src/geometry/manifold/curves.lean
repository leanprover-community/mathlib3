import geometry.manifold.tangent_bundle_derivation
import geometry.manifold.instances.real

noncomputable theory

open set

def is_maximal {α : Type*} [partial_order α] (a : α) : Prop := ∀ b : α, b ≥ a → b = a

open_locale manifold

section

structure curve {E : Type*} [normed_group E] [normed_space ℝ E]
  {H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
  (M : Type*) [inhabited M] [topological_space M] [charted_space H M]
  [smooth_manifold_with_corners I M] (n : with_top ℕ) extends Cₗ[n](Isf(ℝ), ℝ; I, M) :=
(connected_source    : is_connected source)
(default_value       : ∀ x ∉ source, to_fun x = default M)

variables {E : Type*} [normed_group E] [normed_space ℝ E]
{H : Type*} [topological_space H] {I : model_with_corners ℝ E H}
{M : Type*} [inhabited M] [topological_space M] [charted_space H M]
[smooth_manifold_with_corners I M] (n : with_top ℕ)

namespace curve

instance : has_coe_to_fun (curve I M n) := ⟨_, λ γ, γ.to_fun⟩

protected lemma times_cont_mdiff_on (γ : curve I M n) :
  times_cont_mdiff_on Isf(ℝ) I n γ γ.source := γ.times_cont_mdiff_on_to_fun

protected lemma smooth (γ : curve I M ∞) :
  smooth_on Isf(ℝ) I γ γ.source := γ.times_cont_mdiff_on_to_fun

@[ext] protected lemma ext {γ σ : curve I M n} (h_src : γ.source = σ.source)
  (h : ∀ x ∈ γ.source, γ x = σ x) : γ = σ :=
begin
  cases γ, cases σ, congr', ext,
  exact iff_of_eq (congr_arg (has_mem.mem x) h_src),
  intro x,
  by_cases h1 : (x ∈ γ__to_times_cont_mdiff_on_map.source),
  exact (h x) h1,
  have h2 := γ_default_value x h1,
  rw h_src at h1,
  have h3 := σ_default_value x h1,
  dsimp at h2 h3, /- dsimp only does not work... -/
  rw [h2, h3],
end

variables {I} {M} {n}

def speed (γ : curve I M n) (t : ℝ) : tangent_space I (γ t) :=
(deriv_within ((ext_chart_at I (γ t)) ∘ γ) γ.source t : E)

def speed_der (γ : curve I M n) (t : ℝ) : point_derivation I (γ t) :=
{ to_fun := λ f, deriv (f ∘ γ) t,
  map_add' := λ f g, by { sorry },
  map_smul' := λ c f, by { sorry },
  leibniz' := λ f g, by {dsimp only, sorry, } }

instance : has_lt (curve I M n) :=
⟨λ γ₁ γ₂, γ₁.source ⊂ γ₂.source ∧ ∀ x ∈ γ₁.source, γ₁ x = γ₂ x⟩

instance : has_le (curve I M n) :=
⟨λ γ₁ γ₂, γ₁.source ⊆ γ₂.source ∧ ∀ x ∈ γ₁.source, γ₁ x = γ₂ x⟩

instance : partial_order (curve I M n) :=
{ le_refl := λ γ, ⟨subset.rfl, λ x h, by refl⟩,
  le_trans := λ γ σ ρ, λ h1 h2, ⟨subset.trans h1.1 h2.1, λ x h, by rw [h1.2 x h, h2.2 x (h1.1 h)]⟩,
  le_antisymm := λ γ σ, λ h1 h2, by { ext1, exacts [subset.antisymm h1.1 h2.1, λ x hx, h1.2 x hx] },
  ..curve.has_le }

end curve

structure integral_curve {E : Type*} [normed_group E] [normed_space ℝ E]
  {H : Type*} [topological_space H] {I : model_with_corners ℝ E H}
  {M : Type*} [inhabited M] [topological_space M] [charted_space H M]
  [smooth_manifold_with_corners I M] (X : vector_field_derivation I M)
  extends curve I M ∞ :=
(integral : ∀ t ∈ source, to_curve.speed_der t = X.eval (to_fun t))

variables {X : vector_field_derivation I M}

namespace integral_curve

instance : has_coe_to_fun (integral_curve X) := ⟨_, λ γ, γ.to_fun⟩
instance : has_coe (integral_curve X) (curve I M ∞) := ⟨to_curve⟩

protected lemma smooth (γ : integral_curve X) :
  smooth_on Isf(ℝ) I γ γ.source := γ.times_cont_mdiff_on_to_fun

@[ext] protected lemma ext {γ σ : integral_curve X} (h : (γ : curve I M ∞) = σ) : γ = σ :=
by { cases γ, cases σ, congr' }

lemma injective.to_curve : function.injective (λ γ : integral_curve X, γ.to_curve) :=
λ γ σ h, by { ext1, exact h }

instance : partial_order (integral_curve X) := partial_order.lift to_curve injective.to_curve

end integral_curve

def vector_field_derivation.is_complete (X : vector_field_derivation I M) : Prop :=
∀ γ : integral_curve X, is_maximal γ → γ.source = univ

theorem exists_maximal_curve (X : vector_field_derivation I M) (x : M) :
  ∃ γ : integral_curve X, γ 0 = x ∧ is_maximal γ :=
sorry /- need some more advanced ODE theory -/

lemma unique_maximal_curve (γ σ : integral_curve X) (h : γ 0 = σ 0) (hg : is_maximal γ)
(hs : is_maximal σ) : γ = σ := sorry

def maximal_curve (X : vector_field_derivation I M) (x : M) : integral_curve X :=
classical.some (exists_maximal_curve X x)

lemma maximal_curve_zero (X : vector_field_derivation I M) (x : M) : maximal_curve X x 0 = x :=
(classical.some_spec (exists_maximal_curve X x)).1

lemma maximal_curve_maximal (X : vector_field_derivation I M) (x : M) :
  is_maximal (maximal_curve X x) :=
(classical.some_spec (exists_maximal_curve X x)).2

def flow (X : vector_field_derivation I M) : M × ℝ → M := λ x, maximal_curve X x.1 x.2

def flow.source (X : vector_field_derivation I M) : set (M × ℝ) :=
λ x : M × ℝ, x.2 ∈ (maximal_curve X x.1).source

lemma flow.smooth_on : smooth_on (I.prod Isf(ℝ)) I (flow X) (flow.source X) := sorry

lemma complete_iff_maximal_source : vector_field_derivation.is_complete X ↔ flow.source X = univ :=
sorry

end
