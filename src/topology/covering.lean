import topology.connected
import topology.continuous_function.basic
import topology.homotopy.fundamental_groupoid
import category_theory.full_subcategory

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

variables (E E' X : Type*) [topological_space E] [topological_space E'] [topological_space X]

structure covering_map extends continuous_map E X :=
(surjective : function.surjective to_fun)
(discrete_fibers : ∀ x : X, discrete_topology (to_fun ⁻¹' {x}))
(evenly_covered : ∀ x : X, ∃ U : set X, is_open U ∧ ∃ hx : x ∈ U,
  ∃ ι : to_fun ⁻¹' {x} × U ≃ₜ to_fun ⁻¹' U, (∀ s, to_fun (ι s) = s.2) ∧
    ∀ s, ι ⟨s, x, hx⟩ = ⟨s, (congr_arg (∈ U) s.2).mpr hx⟩)

variables {E E' X}

def fundamental_group (x : X) :=
let y : fundamental_groupoid X := x in y ⟶ y

noncomputable instance (x : X) : group (fundamental_group x) :=
{ mul := category_theory.category_struct.comp,
  mul_assoc := category_theory.category.assoc,
  one := category_theory.category_struct.id _,
  one_mul := category_theory.category.id_comp,
  mul_one := category_theory.category.comp_id,
  inv := category_theory.groupoid.inv,
  mul_left_inv := category_theory.groupoid.inv_comp }

namespace covering_map

infixr ` ↠ `:25 := covering_map -- shortcut: type `\rr-` or just type `\rr `

instance : has_coe_to_fun (E ↠ X) (λ _, E → X) := ⟨λ q, q.to_fun⟩

@[continuity] lemma continuous (q : E ↠ X) : continuous q := q.continuous_to_fun

end covering_map
