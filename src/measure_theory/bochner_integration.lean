import measure_theory.simple_func_dense

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

set_option class.instance_max_depth 100

namespace measure_theory
open set lattice filter topological_space ennreal emetric

universes u v
variables {α : Type u} {β : Type v} [measure_space α]
          {γ : Type*} [normed_group γ] [second_countable_topology γ]

namespace l1

variables (α γ)
def simple_func : Type* :=
{ f : α →₁ γ // ∃ (s : simple_func α γ) (hs : integrable s), mk s s.measurable hs = f}
variables {α γ}

local infixr ` →ₛ `:25 := simple_func

namespace simple_func
open ae_eq_fun

def mk (f : measure_theory.simple_func α γ) : integrable f → (α →ₛ γ) :=
assume h,  ⟨l1.mk f f.measurable h , ⟨f, ⟨h, rfl⟩⟩⟩

instance :  has_coe (α →ₛ γ) (α →₁ γ) := ⟨subtype.val⟩

instance : metric_space (α →ₛ γ) :=
  metric_space.induced (coe : (α →ₛ γ) → (α →₁ γ)) subtype.val_injective l1.metric_space

lemma exists_simple_func_near (f : α →₁ γ) {ε : ℝ} (ε0 : ε > 0) :
  ∃ s : α →ₛ γ, dist f s < ε :=
begin
  rcases f with ⟨⟨f, hfm⟩, hfi⟩,
  simp only [integrable_mk, quot_mk_eq_mk] at hfi,
  rcases simple_func_sequence_tendsto' hfm hfi with ⟨F, ⟨h₁, h₂⟩⟩,
  rw ennreal.tendsto_at_top at h₂,
  rcases h₂ (ennreal.of_real (ε/2)) (of_real_pos.2 $ half_pos ε0) with ⟨N, hN⟩,
  have : (∫⁻ (x : α), nndist (F N x) (f x)) < ennreal.of_real ε :=
  calc
    (∫⁻ (x : α), nndist (F N x) (f x)) ≤ 0 + ennreal.of_real (ε/2) : (hN N (le_refl _)).2
    ... < ennreal.of_real ε :
      by { simp only [zero_add, of_real_lt_of_real_iff ε0], exact half_lt_self ε0 },
  { refine ⟨mk (F N) (h₁ N), _⟩, rw dist_comm,
    rw ← lt_of_real_iff_to_real_lt at this, simpa [edist, comp_nndist, ae_eq_fun.edist, mk, l1.mk] },
  { exact zero_ne_top }
end

lemma uniform_continuous_of_simple_func : uniform_continuous (coe : (α →ₛ γ) → (α →₁ γ)) :=
uniform_continuous_comap

lemma uniform_embedding_of_simple_func : uniform_embedding (coe : (α →ₛ γ) → (α →₁ γ)) :=
uniform_embedding_comap subtype.val_injective

lemma dense_embedding_of_simple_func : dense_embedding (coe : (α →ₛ γ) → (α →₁ γ)) :=
uniform_embedding_of_simple_func.dense_embedding $
λ f, mem_closure_iff_nhds.2 $ λ t ht,
let ⟨ε,ε0, hε⟩ := metric.mem_nhds_iff.1 ht in
let ⟨s, h⟩ := exists_simple_func_near f ε0 in
ne_empty_iff_exists_mem.2 ⟨_, hε (metric.mem_ball'.2 h), s, rfl⟩

end simple_func

end l1

end measure_theory
