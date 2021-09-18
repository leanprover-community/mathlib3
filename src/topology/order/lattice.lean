-- Topological lattices
-- Modeled on topology.algebra.monoid

import topology.basic
import topology.constructions
import topology.algebra.ordered.basic

class has_continuous_inf (L : Type*) [topological_space L] [has_inf L] : Prop :=
(continuous_inf : continuous (λ p : L × L, p.1 ⊓ p.2))

class has_continuous_sup (L : Type*) [topological_space L] [has_sup L] : Prop :=
(continuous_sup : continuous (λ p : L × L, p.1 ⊔ p.2))

instance has_continuous_inf_dual_has_continuous_sup
(L : Type*) [topological_space L] [has_sup L] [h: has_continuous_inf (order_dual L)] :
  has_continuous_sup  L :=
{
  continuous_sup :=
    @has_continuous_inf.continuous_inf  (order_dual L) _ _ h
}

-- The equivalent definition of a topological_monoid doesn't appear to exist
class topological_lattice (L : Type*) [topological_space L] [lattice L]
  extends has_continuous_inf L, has_continuous_sup L
