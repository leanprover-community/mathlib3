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

* Instances tranferred elementwise to products, like `prod.monoid`.
  See `algebra.group.prod` for more examples.
  ```
  instance prod.Z [Z M] [Z N] : Z (M × N) := ...
  ```
* Instances tranferred elementwise to pi types, like `pi.monoid`.
  See `algebra.group.pi` for more examples.
  ```
  instance pi.Z [∀ i, Z $ f i] : Z (Π i : I, f i) := ...`
  ```
* Definitions for transferring the proof fields of instances along injective and surjective functions that agree
  on the data fields, like `function.injective.monoid` and `function.surjective.monoid`.
  See ``algebra.group.inj_surj` for more examples
  ```
  def function.injective.Z [Z M₂] (f : M₁ → M₂) (hf : injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) : Z M₁ := ...

  def function.surjective.Z [Z M₁] (f : M₁ → M₂) (hf : surjective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) : Z M₂ :=
  ```
* Instances tranferred elementwise to `finsupp`s, like `finsupp.semigroup`.
  See `data.finsupp.pointwise` for more examples.
  ```
  instance finsupp.Z [Z β] : Z (α →₀ β) := ...
  ```
* Instances tranferred elementwise to `set`s, like `set.monoid`.
  See `algebra.pointwise` for more examples.
  ```
  instance set.Z [Z α] : Z (set α) := ...
  ```
* Definitions for transferring the entire structure across an equivalence, like `equiv.monoid`.
  See `data.equiv.transfer_instance` for more examples.
  ```
  def equiv.Z (e : α ≃ β) [Z β] : Z α := ...` and
  /- when there is a new notion of `Z`-equiv -/
  def equiv.Z_equiv (e : α ≃ β) [Z β] : by { letI := equiv.Z e, exact α ≃Z β } := ...
  ```
* When `Z` adds only new proof fields to an existing structure `Y`, instances transferring
  `Z α` to `Z (sub_Y α)`, like `submonoid.to_comm_monoid`.
  Typically this is done using the `function.injective.Z` definition mentioned above.
  ```
  instance sub_Y.to_Z [Z α] : Z (sub_Y α) :=
  coe_injective.Z coe ...
  ```
* When `Z` adds new data fields too, a new `sub_Z` `structure` with a `carrier` field.
  If `Z` extends `Y`, then `sub_Z` should usually extend `sub_Y`.

[[ Talk about morphisms? ]]
[[ Talk about equivalences? ]]
[[ Talk about subobjects? ]]

### Interactions with topology

[[ Mention here all the `topological_Z` infrastructure you might want. ]]

### Interactions with order

[[ Complicated! ]]

-/
library_note "the algebraic hierarchy"
