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

structure transducer (S X Y : Type*) extends machine S X Y :=
(init : S)

--!! notation self_transducer S X := transducer S X X

structure invertible_transducer (S X : Type*) extends invertible_machine S X :=
(init : S)

def reachable (t : transducer S X Y) : set S := "minimal set R such that init ∈ R and step(R,X)⊆R"

def is_trivial (t : transducer S X X) : Prop :=
    ∀ s : S, s ∈ reachable t → t.out s = id

--!!later: example is_trivial ⟨grigorchuk_machine,4⟩ := dec_trivial

namespace machine

variables (m : machine S X Y)

def is_invertible : Prop := ∀ s, bijective (m.out s)

def machine_inverse (inv : is_invertible m) : machine S Y X := {
    out := λ s, fintype.bij_inv (inv s),
    step := λ s y, m.step s ((fintype.bij_inv (inv s)) y)
}

--!! how to convert automatically a machine with is_invertible to an invertible_machine?

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
def transducer_action : (list X) → (list Y) := machine_action t t.init

def transducer_composition (t₁ : transducer S X Y) (t₂ : transducer T Y Z) : transducer (S×T) X Z := {
    init := (t₁.init,t₂.init),
    .. machine_composition t₁ t₂
}

def transducer_mk (m : machine S X Y) (i : S) := { init := i, ..m }

end transducer

end automata_group

namespace grigorchuk_example

open automata_group

notation `X` := fin 2
notation `S` := fin 5

def grigorchuk_machine : S → X → X × S :=
![![(1,4), (0,4)], ![(0,0),(1,2)], ![(0,0),(1,3)], ![(0,4),(1,1)], ![(0,4),(1,4)]]

-- this fails, though it should be easily decidable
def inv : isinvertible_machine grigorchuk_machine := begin
  rw isinvertible_machine, dec_trivial,
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

