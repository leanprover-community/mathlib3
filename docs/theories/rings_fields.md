# Maths in Lean : rings and fields

The `ring` typeclass is defined in the core library, in
`init/algebra/ring`. Related typeclasses are also defined in the
`init/algebra` directory.

### Basic typeclasses.

-   `ring` (note that in Lean a ring automatically has a 1)
-   `comm_ring` (a commutative ring)
-   `integral_domain`
-   `division_ring`
-   `discrete_field` (note that mathematicians will probably want to use
    this typeclass for fields, rather than the `field` typeclass; the
    `field` typeclass is a constructive mathematics version of
    `discrete_field`).

### Usage examples.

```
    variable (R₁ : Type*)
    variable [ring R₁]
    example : ∀ r : R₁, r+1=1+r := λ r, add_comm r 1
    example : ∀ r : R₁, r * 1 = r := mul_one

    variable (R₂ : Type*)
    variable [comm_ring R₂]
    example : ∀ (a b : R₂), a * a - b * b = (a + b) * (a - b) :=
    mul_self_sub_mul_self_eq
    example (a b c : R₂) (h : a ∣ b) :  a ∣ c ↔ a ∣ b + c :=
    dvd_add_iff_right h

    variable (R₃ : Type*)
    variable [integral_domain R₃]
    example (a b : R₃) : a * b = 0 ↔ a = 0 ∨ b = 0 :=
    mul_eq_zero_iff_eq_zero_or_eq_zero
    example  (a b : R₃) : b ≠ 1 → a * b = a → a = 0 :=
    eq_zero_of_mul_eq_self_right

    variable (F : Type*)
    variable [field F]
    example (a b c : F) : (a / c) - (b / c) = (a - b) / c :=
    div_sub_div_same a b c
    example (a b : F) (hb : b ≠ 0) : a / b = 1 ↔ a = b := div_eq_one_iff_eq
    a hb
```

 

### Related typeclasses.

`discrete_linear_ordered_field` etc.
