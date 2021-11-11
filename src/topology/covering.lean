import topology.connected
import topology.continuous_function.basic

section for_mathlib

/-lemma open_embedding_of_open_embedding_compose_injective {A B C : Type*}
  [topological_space A] [topological_space B] [topological_space C]
  {f : A → B} {g : B → C} (hf : continuous f) (hg : continuous g) (h : open_embedding (g ∘ f))
  (hg' : function.injective g) : open_embedding f :=
begin
  refine ⟨embedding_of_embedding_compose hf hg h.1, _⟩,
  rw [←set.preimage_image_eq (set.range f) hg', ←set.range_comp],
  exact is_open.preimage hg h.2,
end

@[continuity] lemma set.maps_to.restrict.continuous {A B : Type*} [topological_space A] [topological_space B]
  {f : A → B} (hf' : continuous f) {s : set A} {t : set B} (hf : set.maps_to f s t) :
  continuous (set.maps_to.restrict f s t hf) :=
begin
  refine ⟨λ U hU, _⟩,
  obtain ⟨U, hU, rfl⟩ := hU,
  exact ⟨f ⁻¹' U, is_open.preimage hf' hU, rfl⟩,
end-/

end for_mathlib

universes u

variables {E E' X : Type u} [topological_space E] [topological_space E'] [topological_space X]

def evenly_covered (f : E → X) (U : set X) : Prop :=
∃ (α : Type u) (ι : (Σ (a : α), U) → E), embedding ι ∧ set.range ι = f ⁻¹' U ∧ ∀ s, f (ι s) = s.2

-- not sure if we'll end up needing this lemma
lemma evenly_covered.comp {f : E' → X} {g : E → E'} {U : set X}
  (hf : evenly_covered f U) (hg : evenly_covered g (f ⁻¹' U)) : evenly_covered (f ∘ g) U :=
begin
  obtain ⟨α, ι, hι1, hι2, hι3⟩ := hf,
  obtain ⟨β, κ, hκ1, hκ2, hκ3⟩ := hg,
  let γ := α × β,
  let μ : (Σ (c : γ), U) → E :=
  λ s, κ ⟨s.1.2, ⟨ι ⟨s.1.1, s.2⟩, (congr_arg (∈ U) (hι3 ⟨s.1.1, s.2⟩)).mpr s.2.2⟩⟩,
  have h3 : ∀ s, f (g (μ s)) = s.2 := λ s, by rw [hκ3, subtype.coe_mk, hι3],
  have h2 : set.range μ = (f ∘ g) ⁻¹' U,
  { refine set.subset.antisymm _ _,
    { rintros _ ⟨s, rfl⟩,
      exact (congr_arg (∈ U) (h3 s)).mpr s.2.2 },
    { intros e he,
      obtain ⟨s, hs⟩ := hι2.symm.subset he,
      obtain ⟨t, rfl⟩ := hκ2.symm.subset he,
      exact ⟨⟨⟨s.1, t.1⟩, s.2⟩, by simp_rw [μ, sigma.eta, hs, hκ3, subtype.coe_eta, sigma.eta]⟩ } },
  have h1 : embedding μ,
  { sorry },
  exact ⟨γ, μ, h1, h2, h3⟩,
end

variables (E E' X)

structure covering_map extends continuous_map E X :=
(surjective : function.surjective to_fun)
(evenly_covered : ∀ x : X, ∃ U ∈ nhds x, evenly_covered to_fun U)

variables {E E' X}

namespace covering_map

infixr ` ↠ `:25 := covering_map -- shortcut: type `\rr-` or just type `\rr `

instance : has_coe_to_fun (E ↠ X) (λ _, E → X) := ⟨λ q, q.to_fun⟩

@[continuity] lemma continuous (q : E ↠ X) : continuous q := q.continuous_to_fun

end covering_map
