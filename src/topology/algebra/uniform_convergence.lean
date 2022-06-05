/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.uniform_space.uniform_convergence_topology
import topology.algebra.uniform_group

/-!
# Algebraic facts about the topology of uniform convergence

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

section group

variables {α G : Type*} [group G] [uniform_space G] [uniform_group G]

local attribute [-instance] Pi.uniform_space
local attribute [-instance] Pi.topological_space
local attribute [instance] uniform_convergence.uniform_space

#check uniform_inducing.uniform_continuous

@[to_additive]
protected lemma uniform_convergence.uniform_group :
uniform_group (α → G) :=
⟨begin
  suffices : uniform_continuous (uniform_convergence.uniform_equiv_Pi_comm (/))
end⟩

end group
