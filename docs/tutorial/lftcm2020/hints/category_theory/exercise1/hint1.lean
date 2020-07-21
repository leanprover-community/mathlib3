import category_theory.isomorphism
import category_theory.yoneda

open category_theory
open opposite

variables {C : Type*} [category C]

def iso_of_hom_iso_attempt_1 (X Y : C) (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y :=
-- We're trying to construct an isomorphism, so our first task is to write a stub for the structure:
-- { }
sorry

/-
This says:

```
invalid structure value { ... }, field 'hom' was not provided
invalid structure value { ... }, field 'inv' was not provided
```

so let's try again:
-/

def iso_of_hom_iso_attempt_2 (X Y : C) (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y :=
{ hom := sorry,
  inv := sorry, }

/-
It's time to think about the maths, but lets do that in the next hint file.
-/
