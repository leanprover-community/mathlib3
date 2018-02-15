# Maths in Lean : functions

The file `init/function.lean` in the core library has basic defintions
and facts about functions between general types.

### Basic definitions.

`comp` (function composition), `id` (the identity function), `const` (a
constant function), `injective`,`surjective`,`bijective`. Note that many
of these things live in the `function` namespace, which has to be opened
first.

### Usage examples.

```
universes u variables (X Y Z : Type u)
variables (f : X → Y) (g : Y → Z) (h : Y → X)

open function 

example : bijective g → bijective f → bijective (g ∘ f) := bijective_comp 

example : has_left_inverse f → injective f := injective_of_has_left_inverse 

example : left_inverse h f → h ∘ f = id := id_of_left_inverse
```
