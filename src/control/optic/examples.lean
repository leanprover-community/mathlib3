/-
Copyright (c) 2020 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers
-/
import .profunctor_optic
import .prod

/-!
Examples of optics.
-/

open control.optic
open control.profunctor

variables {A B S T : Type}

variable {n: ℕ}
open vector

def vector.grate : grate A B (vector A n) (vector B n) :=
grate.mk $ λ f, vector.of_fn $ λ i, f $ λ va, vector.nth va i
instance [has_repr A] : has_repr (vector A n) := ⟨λ x, repr $ x.to_list⟩

def vector.iota (n : ℕ) : vector ℕ n := @vector.of_fn nat n $ λ i, i.val

#eval zip_with2 vector.grate (+) (vector.iota 100) (vector.iota _)

namespace widget
open control

meta instance : profunctor widget.component :=
{ dimap := λ A B C D ba cd, component.map_action cd ∘ component.map_props ba
}

meta instance : strong widget.component :=
{ first  := λ A B C ab, component.filter_map_action (λ ⟨a,c⟩ b, some (b,c))
                        $ component.map_props prod.fst $ ab
, second := λ A B C ab, component.filter_map_action (λ ⟨c,a⟩ b, some (c,b))
                        $ component.map_props prod.snd $ ab
}

/-- Note that this is not _technically_ an isomorphism. `P → list (html A)`
will _always_ rerender, but a component can optionally re-render depending on whether
the props have changed, so can result in different behaviour. -/
meta instance : representable widget.component :=
{ Rep := list ∘ html
, tabulate := λ A B ab, component.pure ab
, sieve := λ A B c a, singleton $ html.of_component a $ c
}

end widget
