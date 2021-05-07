import representation_theory.main2
import representation_theory.pi_map

open_locale direct_sum classical big_operators
open classical linear_map finite_dimensional
noncomputable theory
/-!
# Simple Modules



-/

variables {F A M : Type*} [field F] [ring A] [add_comm_monoid M]
variables [algebra F A] [module A M]
variables [finite_dimensional F A]

variables (A)

instance submodule.setoid : setoid (submodule A A) :=
{ r := λ n m, nonempty (n ≃ₗ[A] m),
  iseqv := ⟨λ x, ⟨linear_equiv.refl A x⟩, λ x y h, ⟨h.some.symm⟩,
    λ x y z hxy hyz, ⟨hxy.some.trans hyz.some⟩⟩ }

def atom_setoid := subtype.setoid (λ s : submodule A A, is_atom s)
def atom_quot := quotient $ atom_setoid A

def setoid.class {α : Type*} (r : setoid α) (y : α) := {x : α | r.rel x y}



lemma exist_mem_of_mem_Sup {R M : Type*}
  [semiring R] [add_comm_monoid M] [module R M]
  {S : set (submodule R M)} {x : M} :
  x ∈ Sup S ↔ ∃ s ∈ S, x ∈ s :=
begin
  split,
  contrapose!,
end

lemma decompose [is_complemented (submodule A A)] [fintype {a : submodule A A | is_atom a}]
  [fintype (atom_quot A)] : ⊤ =
  ⨆ s : atom_quot A, (⨆ i : (atom_setoid A).class s.out, i.val : submodule A A) :=
begin
  refine le_antisymm _ le_top,
  rw ← Sup_atoms_eq_top,
  intros x hx,
  rw submodule.mem_supr',
  rw Sup_eq_supr' at hx,
  rw submodule.mem_supr' at hx,
  rcases hx with ⟨a, b, c⟩,
end
