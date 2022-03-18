import analysis.special_functions.log
import topology.algebra.order.intermediate_value

/-! automata groups.
-/

--!! I don't think we want this here
--noncomputable theory
open set function real

namespace automata_group

variables {S T : Type} {X : Type} [decidable_eq X] [fintype X]

--!! does the following structuring sound reasonable to you?
-- notation machine := S×X → X×S
-- structure transducer := ⟨machine : S×X→X×S,s : S⟩
structure machine (S X : Type*) :=
(out : S → X → X)
(next_state : S → X → S)

structure invertible_machine (S X : Type*) :=
(out : S → equiv.perm X)
(next_state : S → X → S)

namespace machine

variables (m : machine S X)

def is_invertible : Prop := ∀ s, bijective (m.out s)

end machine

-- we could implement in lean the composition of transducers -- it's again given by a transducer, with stateset S the product of the states of the factors.
-- more precisely, ⟨machine1,s1⟩∘⟨machine2,s2⟩ := ⟨machine1∘machine2,(s1,s2)⟩, as below
--!! also, let dec_trivial decide if two transducers are equal by testing if their quotient is 1, and test if a transducer is 1 by testing if all states reachable from the initial state induce trivial permutation X→X.

def isinvertible_machine (machine : S×X → X×S) := ∀ s, bijective (λ x, (machine (s,x)).1)

-- then ⟨machine,s⟩⁻¹ := ⟨invmachine machine,s⟩

-- transducer action: written in action notation?
def transducer_action (machine : S×X → X×S) : S → (list X) → (list X)
| _ [] := []
| state (head :: tail) := (machine (state,head)).1 :: transducer_action (machine (state,head)).2 tail

def machine_inverse {machine : S×X → X×S} (inv : isinvertible_machine machine) : S×X → X×S := λ p, let σ := fintype.bij_inv (inv p.1) in (σ p.2,(machine (p.1,σ p.2)).2)

--!! could (inv :...) be automatically deduced (in [])?
def transducer_perm (machine : S×X → X×S) (inv : isinvertible_machine machine) (state : S) : equiv.perm (list X) := {
  to_fun := transducer_action machine state,
  inv_fun := transducer_action (machine_inverse inv) state,
  left_inv := sorry,
  right_inv := sorry
}

--!! notation ∘ ?
def machine_composition (machine₁ : S×X → X×S) (machine₂ : T×X → X×T) : ((S×T)×X→X×(S×T)) := λ p, let q := machine₂ (p.1.2,p.2) in let r := machine₁ (p.1.1,q.1) in (r.1,(r.2,q.2))

--!! set syntax when going over a type ?
def automata_group (machine : S×X → X×S) (inv : isinvertible_machine machine) : subgroup (equiv.perm (list X)) :=
  subgroup.closure {transducer_perm machine s | s : S}

end automata_group

namespace grigorchuk_example

open automata_group


notation `X` := fin 2
notation `S` := fin 5

def grigorchuk_machine : S → X → X × S :=
![![_, _], _, _, _, _]
-- -- perhaps would be nicer with a notation like | (0,0) := (1,4) etc.
--   if p=(0,0) then (1,4) else if p=(1,0) then (0,4) else
--   if p=(0,1) then (0,0) else if p=(1,1) then (1,2) else
--   if p=(0,2) then (0,0) else if p=(1,2) then (1,3) else
--   if p=(0,3) then (0,4) else if p=(1,3) then (1,1) else
--   if p=(0,4) then (0,4) else                 (1,4)

#check isinvertible_machine grigorchuk_machine
-- this fails, though it should be easily decidable
def inv : isinvertible_machine grigorchuk_machine := dec_trivial

def _root_.grigorchuk_group : subgroup (equiv.perm (list X)) := automata_group grigorchuk_machine inv

def grigorchuk_group.a : equiv.perm (list X) := transducer_perm grigorchuk_machine inv 0
def grigorchuk_group.b : equiv.perm (list X) := transducer_perm grigorchuk_machine inv 1
def grigorchuk_group.c : equiv.perm (list X) := transducer_perm grigorchuk_machine inv 2
def grigorchuk_group.d : equiv.perm (list X) := transducer_perm grigorchuk_machine inv 3

notation `𝔾` := grigorchuk_group
notation `a` := grigorchuk_group.a
notation `b` := grigorchuk_group.b
notation `c` := grigorchuk_group.c
notation `d` := grigorchuk_group.d

#check a*a = 1
#check b*b = 1
#check b*c*d = 1
#check (a*d)^4 = 1

end grigorchuk_example

