# How to use calc

`calc` appears to be something called an `environment`. I don't really
know what an environment is. 

calc will work with any relation tagged [refl], and if they're also tagged
[trans] then calc is a bit more powerful.


Here's an example of a proof which uses `calc`. When I start it looks like this:

```
open nat
theorem zero_add_induction_step (d : ℕ) (H : 0 + d = d) : 0 + succ d = succ d :=
calc 0 + succ d = _      : _
--- ABOVE HERE write more ... lines
...             = succ d : _
```

When I have finished it looks like this:

```
open nat
theorem zero_add_induction_step (d : ℕ) (H : 0 + d = d) : 0 + succ d = succ d :=
calc 0 + succ d = succ (0 + d) : rfl
...             = succ d : by rw [H]
```



