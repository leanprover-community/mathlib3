
import logic.equiv.defs
import order.directed
import order.upper_lower

-- Other references to Scott
--import topology.omega_complete_partial_order
--#check Scott
--import order.omega_complete_partial_order -- Scott continuity
--#check omega_complete_partial_order.continuous

variables (α : Type*)

/-
-- A complete lattice is a omega complete partial order
variables [complete_lattice α]

#check Scott.topological_space α

lemma Scott_upper (u : set α) (h: Scott.is_open α u) : is_upper_set u :=
begin
  intros a b hab ha,

end

lemma scott_open :
  Scott.is_open α = λ u, is_upper_set u ∧ ∀ (d : set α), directed_on (≤) d → Sup d ∈ u → d∩u ≠ ∅ :=
begin
  ext u,
  split,
  { intro h,
    split,
     },
  { intro h,

  sorry, }
end
-/
open set --topological_space

/--
Type synonym for a preorder equipped with the Scott topology
-/
def with_scott_topology := α

variables {α}

namespace with_scott_topology

/-- `to_scott` is the identity function to the `with_scott_topology` of a type.  -/
@[pattern] def to_scott : α ≃ with_scott_topology α := equiv.refl _

/-- `of_scott` is the identity function from the `with_scott_topology` of a type.  -/
@[pattern] def of_scott : with_scott_topology α ≃ α := equiv.refl _

@[simp] lemma to_with_scott_topology_symm_eq : (@to_scott α).symm = of_scott := rfl
@[simp] lemma of_with_scott_topology_symm_eq : (@of_scott α).symm = to_scott := rfl
@[simp] lemma to_scott_of_scott (a : with_scott_topology α) : to_scott (of_scott a) = a := rfl
@[simp] lemma of_scott_to_scott (a : α) : of_scott (to_scott a) = a := rfl
@[simp] lemma to_scott_inj {a b : α} : to_scott a = to_scott b ↔ a = b := iff.rfl
@[simp] lemma of_scott_inj {a b : with_scott_topology α} : of_scott a = of_scott b ↔ a = b :=
iff.rfl

/-- A recursor for `with_scott_topology`. Use as `induction x using with_scott_topology.rec`. -/
protected def rec {β : with_scott_topology α → Sort*}
  (h : Π a, β (to_scott a)) : Π a, β a := λ a, h (of_scott a)

instance [nonempty α] : nonempty (with_scott_topology α) := ‹nonempty α›
instance [inhabited α] : inhabited (with_scott_topology α) := ‹inhabited α›
instance [complete_lattice α] : complete_lattice (with_scott_topology α) := ‹complete_lattice α›

--variables [partial_order α]



/-
instance : topological_space (with_scott_topology α) := generate_from {s | ∃ a, (Ici a)ᶜ = s}

lemma is_open_preimage_of_scott (S : set α) :
  is_open (with_scott_topology.of_scott ⁻¹' S) ↔
    (generate_from {s : set α | ∃ (a : α), (Ici a)ᶜ = s}).is_open S := iff.rfl

lemma is_open_def (T : set (with_scott_topology α)) :
  is_open T ↔ (generate_from {s : set α | ∃ (a : α), (Ici a)ᶜ = s}).is_open
    (with_scott_topology.to_scott ⁻¹' T) := iff.rfl
-/

section preorder

variable [preorder α]

def is_scott_open (u : set α) : Prop := is_upper_set u ∧
  ∀ (d : set α) (a : α), d.nonempty → directed_on (≤) d → is_lub d a → a ∈ u → d∩u ≠ ∅

lemma is_open_univ : is_scott_open (univ : set α) :=
begin
  rw is_scott_open,
  split,
  { exact is_upper_set_univ, },
  { intros d a hd₁ hd₂ hd₃ ha,
    rw inter_univ,
    exact nonempty.ne_empty hd₁ }
end

end preorder

section complete_lattice

lemma complete_scott_open [complete_lattice α] :
  is_scott_open = λ u, is_upper_set u ∧
    ∀ (d : set α), d.nonempty → directed_on (≤) d → Sup d ∈ u → d∩u ≠ ∅ :=
begin
  ext u,
  rw is_scott_open,
  split,
  { intro h,
    split,
    { exact h.1, },
    { intros d hd₁ hd₂ hd₃,
      exact h.2 d (Sup d) hd₁ hd₂ (is_lub_Sup d) hd₃ } },
  { intro h,
    split,
    { exact h.1, },
    { intros d a hd₁ hd₂ hd₃ ha,
      apply h.2 d hd₁ hd₂,
      { rw (is_lub.Sup_eq hd₃), exact ha, } } }
end

end complete_lattice

end with_scott_topology
