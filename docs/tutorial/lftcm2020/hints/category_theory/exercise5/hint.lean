/-!

Try:

```
def functor.preadditive.preserves_biproducts (F : C ⥤ D) (P : F.preadditive) (X Y : C) :
  F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y :=
{ hom := biprod.lift (F.map biprod.fst) (F.map biprod.snd),
  inv := biprod.desc (F.map biprod.inl) (F.map biprod.inr), }
```

Observing:
1. Lean is happy with the definitions `hom` and `inv`,
   so at least you've defined maps in the right places!
2. The unsolved goals all look very plausible using preadditivity of `F`,
   so it's time to add the fields `hom_inv_id'` and `inv_hom_id'` back in,
  and work on those!

-/
