import analysis.special_functions.log
import topology.algebra.order.intermediate_value

/-! automata groups.
-/

--!! I don't think we want this here
--noncomputable theory
open set function real

namespace automata_group

--!! put later the decidable_eq, fintype restrictions
variables {S T : Type} {X Y Z : Type} [decidable_eq X] [decidable_eq Y] [fintype X]

structure machine (S X Y : Type*) :=
(out : S → X → Y)
(step : S → X → S)

structure invertible_machine (S X : Type*) :=
(out : S → equiv.perm X)
(step : S → X → S)

def invertible_machine.to_machine (m : invertible_machine S X) : machine S X X := {
   out := λ s, m.out s, step := m.step }

structure transducer (S X Y : Type*) extends machine S X Y :=
(init : S)

structure invertible_transducer (S X : Type*) extends invertible_machine S X :=
(init : S)

instance : has_coe (invertible_transducer S X) (transducer S X X) :=
   ⟨λ m, { out := λ s, m.out s, step := m.step, init := m.init }⟩

-- the minimal set R of states containing init and closed under step(R,X)
def reachable (t : transducer S X Y) : set S := ⋂₀{R | t.init∈R ∧ ∀(s∈R) x, t.step s x∈R}

def transducer.is_trivial (t : transducer S X X) : Prop :=
    ∀ s : S, s ∈ reachable t → t.out s = id

def invertible_transducer.is_trivial (t : invertible_transducer S X) : Prop :=
    (t : transducer S X X).is_trivial

namespace machine

variables (m : machine S X Y)

def is_invertible : Prop := ∀ s, bijective (m.out s)

def machine_inverse (inv : is_invertible m) : machine S Y X := {
    out := λ s, fintype.bij_inv (inv s),
    step := λ s y, m.step s ((fintype.bij_inv (inv s)) y)
}

--!! how to convert automatically a machine with is_invertible to an invertible_machine?

#check function.End

--!! notation ⬝?
def machine_action : S → (list X) → (list Y)
| _ [] := []
| state (head :: tail) := m.out state head :: machine_action (m.step state head) tail

--!! notation ∘ ? and... which order do we do composition?
def machine_composition (m₁ : machine S X Y) (m₂ : machine T Y Z) : machine (S×T) X Z := {
    out := λ st x, m₂.out st.2 (m₁.out st.1 x),
    step := λ st x, ((m₁.step st.1 x),(m₂.step st.2 (m₁.out st.1 x)))
}

--!! semigroups?
def automata_semigroup (m : machine S X X) : subsemigroup ((list X) → (list X)) :=
  semigroup.closure (set.range (machine_action m))

--!! do we need this?
def invertible_machine_action (m : invertible_machine S X) : S → equiv.perm (list X) := sorry

def automata_group (m : invertible_machine S X) : subgroup (equiv.perm (list X)) :=
  subgroup.closure (set.range (machine_permaction m))

end machine

namespace transducer

open machine

variables (t : transducer S X Y)

--!! how do I tell lean that t is also a machine?
def transducer_action : (list X) → (list Y) := machine_action t.to_machine t.init

def transducer_composition (t₁ : transducer S X Y) (t₂ : transducer T Y Z) : transducer (S×T) X Z := {
    init := (t₁.init,t₂.init),
    ..machine_composition t₁.to_machine t₂.to_machine
}

def transducer_mk (m : machine S X Y) (i : S) : transducer S X Y := { init := i, ..m }

end transducer

end automata_group

namespace grigorchuk_example

open automata_group

notation `X` := fin 2
notation `S` := fin 5

def grigorchuk_machine : machine S X X := {
   out := ![![1,0], ![0,1], ![0,1], ![0,1], ![0,1]],
   step := ![![4,4], ![0,2], ![0,3], ![0,1], ![4,4]]
}

-- this fails, though it should be easily decidable
def inv : isinvertible_machine grigorchuk_machine := begin
  rw isinvertible_machine, dec_trivial,
end

--! do automatically? a tactic replacing the maps in out with fintype.bij_inv
def grigorchuk_invmachine : invertible_machine S X := {
   out := ![equiv.swap 0 1, equiv.refl _, equiv.refl _, equiv.refl _, equiv.refl _],
   step := ![![4,4], ![0,2], ![0,3], ![0,1], ![4,4]]
}

def grigorchuk_a : invertible_transducer S X := { init := 0, ..grigorchuk_invmachine }
def grigorchuk_b : invertible_transducer S X := { init := 1, ..grigorchuk_invmachine }
def grigorchuk_c : invertible_transducer S X := { init := 2, ..grigorchuk_invmachine }
def grigorchuk_d : invertible_transducer S X := { init := 3, ..grigorchuk_invmachine }
def grigorchuk_e : invertible_transducer S X := { init := 4, ..grigorchuk_invmachine }

example : grigorchuk_e.is_trivial := begin
-- set reachable = {4}, check that all outputs are trivial 
end

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

