import algebra.char_zero.defs
import data.fintype.lattice

open set
variables (M : Type*) [add_monoid_with_one M] [char_zero M]

@[priority 100] -- see Note [lower instance priority]
instance char_zero.infinite : infinite M :=
infinite.of_injective coe nat.cast_injective
