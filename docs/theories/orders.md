# Maths in Lean : Orderings

The basic order typeclasses are in the core lean library in
`init/algebra/order.lean` .

### Basic typeclasses.

* `partial_order`
* `decidable_linear_order` (a total order)

### Usage examples.

```lean
variable (P₁ : Type*)
variable [partial_order P₁]
variables a b : P₁
example : a = b ↔ a ≤ b ∧ b ≤ a := le_antisymm_iff
example : a ≤ b → a < b ∨ a = b := lt_or_eq_of_le

variable (P₂ : Type*)
variable [decidable_linear_order P₂]
variables (c d e : P₂)
example : c < d ∨ c ≥ d := lt_or_ge c d
example (h₁ : c ≤ e) (h₂ : d ≤ e) : max c d ≤ e := max_le h₁ h₂
example : min (min c d) e = min c (min d e) := min_assoc c d e
```
                                                    

### Related typeclasses.

`preorder`, `linear_order` (a “non-decidable” linear order so you can’t
use max or min!), `ordered_cancel_comm_monoid`, `ordered_semiring` (the
naturals!) and so on. Note also the `well_founded` inductive type in
`init/wf.lean` in the core library.
