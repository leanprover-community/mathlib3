import topology.connected
import topology.continuous_function.basic
import topology.homotopy.fundamental_groupoid
import category_theory.full_subcategory
<<<<<<< HEAD
import topology.maps
=======

>>>>>>> b4fea6719d0a3e8c2cc0bed8143b4c0786554659
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

<<<<<<< HEAD
universes u

variables {E E' X : Type u} [topological_space E] [topological_space E'] [topological_space X]

def evenly_covered (f : E → X) (U : set X) : Prop :=
∃ (α : Type u) (ι : (Σ a : α, U) → E), embedding ι ∧ set.range ι = f ⁻¹' U ∧ ∀ s, f (ι s) = s.2

lemma evenly_covered_sub_evenly_covered (f : E → X) (U : set X) (V : set X)[V⊂U]
 [evenly_covered f U]: evenly_covered f V:=
 begin
   cases _inst_5 with r hr,
   cases hr with z hz,
   --have t:(Σ (a : r), ↥V) → E:= λ x, z x,
   sorry,
 end

-- not sure if we'll end up needing this lemma
lemma evenly_covered.comp {f : E' → X} {g : E → E'} {U : set X}
  (hf : evenly_covered f U) (hg : evenly_covered g (f ⁻¹' U)) : evenly_covered (f ∘ g) U :=
begin
  obtain ⟨α, ι, hι1, hι2, hι3⟩ := hf,
  obtain ⟨β, κ, hκ1, hκ2, hκ3⟩ := hg,
  --let ϕ : (Σ a : α, U) ≃ₜ set.range ι := homeomorph.of_embedding ι hι1,
  let ψ : (Σ c : α × β, U) ≃ₜ (Σ b : β, f ⁻¹' U) :=
  { to_fun := λ s, ⟨s.1.2, ⟨ι ⟨s.1.1, s.2⟩, (congr_arg (∈ U) (hι3 ⟨s.1.1, s.2⟩)).mpr s.2.2⟩⟩,
    inv_fun := sorry,
    left_inv := sorry,
    right_inv := sorry,
    continuous_to_fun := sorry,
    continuous_inv_fun := sorry },
  refine ⟨α × β, κ ∘ ψ, embedding.comp hκ1 ψ.embedding,
    (function.surjective.range_comp ψ.surjective κ).trans hκ2, λ s, _⟩,
  rw [function.comp_apply, hκ3],
  apply hι3,
end

def singleton_subtype (x:X):= {y: X//y=x}
def singleton_inclusion (x:X):(singleton_subtype x)→ X:=λ s,x

--noncomputable def fundamental_group (x:X) := @category_theory.induced_category.category _
--  X (category_theory.category.{u} X) (singleton_inclusion x),

variables (E E' X)
=======
variables (E E' X : Type*) [topological_space E] [topological_space E'] [topological_space X]
>>>>>>> b4fea6719d0a3e8c2cc0bed8143b4c0786554659

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

lemma covering_map_open (q:E↠ X): is_open_map q:=
begin
  intros U hU,
  sorry,
end
lemma covering_map_quotient (q:E↠ X): quotient_map q :=
 is_open_map.to_quotient_map (covering_map_open q) (continuous q) (q.surjective)

end covering_map
