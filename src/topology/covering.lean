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

universes u v w

variables (E : Type u) (E' : Type v) (X : Type w)
  [topological_space E] [topological_space E'] [topological_space X]

variables {E E' X}

def evenly_covered (f : E → X) (U : set X) : Prop :=
∃ (α : Type u) (g : (Σ (a : α), U) → E), embedding g ∧ set.range g = f ⁻¹' U ∧ f ∘ g = λ x, x.2

variables (E E' X)

structure covering_map extends continuous_map E X :=
(surjective : function.surjective to_fun)
(evenly_covered : ∀ x : X, ∃ U ∈ nhds x, evenly_covered to_fun U)

variables {E E' X}

namespace covering_map

infixr ` ↠ `:25 := covering_map -- shortcut: type `\rr-` or just type `\rr `

instance : has_coe_to_fun (E ↠ X) (λ _, E → X) := ⟨λ q, q.to_fun⟩

@[continuity] lemma continuous (q : E ↠ X) : continuous q := q.continuous_to_fun

def comp (p : E' ↠ X) (q : E ↠ E') : E ↠ X :=
{ to_fun := p ∘ q,
  surjective := p.surjective.comp q.surjective,
  evenly_covered := sorry }

end covering_map
