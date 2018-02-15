# Maths in lean : Groups.

The group typeclass is defined in the core library, in `init/algebra/group.lean`. 
Related typeclasses are also defined in the `init/algebra` directory.

### Basic typeclasses.

* `group` (a group with * as the group law)
* `comm_group` (an abelian group with * as the group law)
* `add_group` (a group with + as the group law)
* `comm_add_group` (an abelian group with + as the group law)

### Usage examples:

```lean
variable (G₁ : Type*)
variable [group G₁]
example : ∀ (g h : G₁), g * h⁻¹ * h = g := inv_mul_cancel_right

variable (G₂ : Type*)
variable [comm_group G₂]
example : ∀ (g h : G₂), (g * h)⁻¹ = g⁻¹ * h⁻¹ := mul_inv

variable (G₃ : Type*)
variable [add_group G₃]
example : ∀ g h : G₃, g - h = g + (-h) := sub_eq_add_neg

variable (G₄ : Type*)
variable [add_comm_group G₄]
example : ∀ g h : G₄, -(-g - (-h)) = g - h := neg_neg_sub_neg
```

### Other related typeclasses.

`semigroup`, `monoid`, `ordered_comm_group`, `ordered_cancel_comm_monoid`,
`left_cancel_semigroup` and many other variants, as you might imagine.
