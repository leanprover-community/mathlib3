#exit
import algebra.monoid_algebra.basic
import representation_theory.basic

variables {k : Type*} [comm_ring k] {G : Type*} [group G]

instance yeahh : has_scalar G G := by apply_instance
noncomputable def yeah (g : G) : monoid_algebra k G → monoid_algebra k G :=
finsupp.lmap_domain k k ((•) g)

example (x )
