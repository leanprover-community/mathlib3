import analysis.special_functions.log
import topology.algebra.order.intermediate_value

/-! automata groups.
-/

--!! I don't think we want this here
--noncomputable theory
open set function real

namespace automata_group

variables {S : Type} {X : Type}

--!! does the following structuring sound reasonable to you?
-- notation machine := S×X → X×S
-- structure transducer := ⟨machine : S×X→X×S,s : S⟩

-- we could implement in lean the composition of transducers -- it's again given by a transducer, with stateset S the product of the states of the factors.
-- more precisely, ⟨machine1,s1⟩∘⟨machine2,s2⟩ := ⟨machine1∘machine2,(s1,s2)⟩,
-- with (machine1∘machine2) ((t1,t2),x) := let ⟨y,u2⟩ := machine2 (t2,x) in let ⟨z,u1⟩ := machine1 (t1,y) in (z,(u1,u2))

def isinvertible_machine (machine : S×X → X×S) := ∀ s x, ∃! y, (machine (s,y)).1 = x
-- we could also implement the inverse, for invertible machines: they would be the machine S×X→X×S given by
-- (invmachine machine) (s,x) := ("the y such that machine (s,y).1=x",machine (s,x).2).
-- then ⟨machine,s⟩⁻¹ := ⟨invmachine machine,s⟩

-- transducer action: written in action notation?
def transducer_action (machine : S×X → X×S) : S → (list X) → (list X)
| _ [] := []
| state (head :: tail) := (machine (state,head)).1 :: transducer_action (machine (state,head)).2 tail

-- action of inverses of states
def transducer_invaction (machine : S×X → X×S) (inv : isinvertible_machine machine) : S → (list X) → (list X)
| _ [] := []
--!! extract a value from an existential quantifier, to form the head of a new list?
| state (head :: tail) := (exists_of_exists_unique (inv state head)).1 :: transducer_invaction (machine (state,head)).2 tail

def transducer_perm (machine : S×X → X×S) [inv : isinvertible_machine machine] (state : S) : equiv.perm (list X) := {
  to_fun := transducer_action machine state,
  inv_fun := transducer_invaction machine inv state,
  left_inv := sorry,
  right_inv := sorry
}

--!! set syntax when going over a type ?
def automata_group (machine : S×X → X×S) [inv : isinvertible_machine machine] : subgroup (equiv.perm (list X)) :=
  subgroup.closure {transducer_perm machine s : s ∈ S}

end automata_group

namespace grigorchuk_example

open automata_group

notation `X` := fin 2
notation `S` := fin 5

def grigorchuk_machine : S×X → X×S := λ p,
-- perhaps would be nicer with a notation like | (0,0) := (1,4) etc.
  if p=(0,0) then (1,4) else if p=(1,0) then (0,4) else
  if p=(0,1) then (0,0) else if p=(1,1) then (1,2) else
  if p=(0,2) then (0,0) else if p=(1,2) then (1,3) else
  if p=(0,3) then (0,4) else if p=(1,3) then (1,1) else
  if p=(0,4) then (0,4) else                 (1,4)

instance inv : isinvertible_machine grigorchuk_machine := dec_trivial

def _root_.grigorchuk_group : subgroup (equiv.perm (list X)) := automata_group grigorchuk_machine

end grigorchuk_example

