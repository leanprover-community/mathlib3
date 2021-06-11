import ring_theory.ideal.basic

/-- Typeclass instances on ideal quotients transfer to submodule quotients.

This is useful if you want to apply results that hold for general submodules
to ideals specifically.

The instance will not be found if `ideal.quotient` is not reducible,
e.g. after you uncomment the following line:
```
local attribute [semireducible] ideal.quotient
```
-/
example {R : Type*} [comm_ring R] (I : ideal R)
  [fintype (ideal.quotient I)] : fintype (submodule.quotient I) :=
infer_instance
