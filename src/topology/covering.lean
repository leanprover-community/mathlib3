import topology.connected
import topology.continuous_function.basic

section for_mathlib

lemma open_embedding_of_open_embedding_compose_injective {A B C : Type*}
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
end

end for_mathlib

variables (E E' X : Type*) [topological_space E] [topological_space E'] [topological_space X]

structure covering_map extends continuous_map E X :=
(surjective : function.surjective to_fun)
(evenly_covered : ∀ e : E, open_embedding (to_fun ∘ coe : connected_component e → X))

infixr ` ↠ `:25 := covering_map -- shortcut: type `\rr-` or just type `\rr `

instance : has_coe_to_fun (E ↠ X) (λ _, E → X) := ⟨λ q, q.to_fun⟩

variables {E E' X}

def covering_map.comp
  (p : E' ↠ X) (q : E ↠ E') : E ↠ X :=
{ to_fun := p ∘ q,
  continuous_to_fun := continuous.comp p.continuous_to_fun q.continuous_to_fun, -- seems like there might be a fancy way to get the continuity tactic to do this automatically?
  surjective := function.surjective.comp p.surjective q.surjective,
  evenly_covered := λ e, by
  { have key : set.maps_to q (connected_component e) (connected_component (q e)) :=
    (λ x hx, continuous.image_connected_component_subset q.continuous_to_fun e ⟨x, hx, rfl⟩),
    change open_embedding ((p ∘ coe) ∘ (set.maps_to.restrict _ _ _ key)),
    exact open_embedding.comp (p.evenly_covered (q e))
      (open_embedding_of_open_embedding_compose_injective
      (set.maps_to.restrict.continuous q.continuous_to_fun key)
      continuous_subtype_coe (q.evenly_covered e) subtype.coe_injective) } }
