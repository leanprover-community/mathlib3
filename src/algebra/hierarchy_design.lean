import tactic.doc_commands

/--
# The algebraic hierarchy

[[ Summarize the design principles of the algebraic hierarchy,
without necessarily giving a tour. ]]

## Adding new typeclasses

When adding new typeclasses `Z` to the algebraic hierarchy
(either new leaves, or new intermediate classes)
one should attempt to add the following constructions and results,
when applicable:

* `instance prod.Z [Z M] [Z N] : Z (M × N) := ...` (see examples in `algebra.group.prod`)
* `instance pi.Z [∀ i, Z $ f i] : Z (Π i : I, f i) := ...` (see examples in `algebra.group.pi`)
*
```
def injective.Z [Z M₂] (f : M₁ → M₂) (hf : Z f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) : Z M₁ := ...

def surjective.Z [Z M₁] (f : M₁ → M₂) (hf : surjective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) : Z M₂ :=
```
(see examples in `algebra.group.inj_surj`)
* `instance finsupp.Z [Z β] : Z (α →₀ β) := ...` (see examples in `data.finsupp.pointwise`)
* `instance set.Z [Z α] : Z (set α) := ...` (see examples in `algebra.pointwise`)
* `def equiv.Z (e : α ≃ β) [Z β] : Z α := ...` and
  `def equiv.Z_equiv (e : α ≃ β) [Z β] : by { letI := equiv.Z e, exact α ≃Z β } := ...`
  (when there is a new notion of `Z`-equiv) (see examples in `data.equiv.transfer_instance`)

[[ Notes about stuff that is currently missing: e.g. all of `algebra.ring.inj_surj`. ]]

[[ Talk about morphisms? ]]
[[ Talk about equivalences? ]]
[[ Talk about subobjects? ]]

### Interactions with topology

[[ Mention here all the `topological_Z` infrastructure you might want. ]]

### Interactions with order

[[ Complicated! ]]

-/
library_note "the algebraic hierarchy"
