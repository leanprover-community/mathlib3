# Variables #

There are different ways to declare a variable `a` of type `α` in Lean.

## () vs {}
Consider the following two ways to define the projection of a length 2 vector onto its first component.

```lean
import data.vector

variable {α : Type}

def p₁: vector α 2 → α
| v := vector.head v
#check p₁ -- p₁ : vector ?M_1 2 → ?M_1
#check @p₁ -- p₁ : Π {α : Type}, vector α 2 → α

def v : vector nat 2 := 1 :: 2 :: vector.nil
#eval p₁ v -- 1

variable (β : Type) -- or equivalently variable β : Type

def π₁: vector β 2 → β
| v := vector.head v
#check π₁ -- π₁ : Π (β : Type), vector β 2 → β
#check @π₁ -- π₁ : Π (β : Type), vector β 2 → β

#eval π₁ nat v -- 1
```

Curly braces tell Lean that the following variable may be inferred. Whenever one calls `p₁ v` with `v : vector nat 2` it is clear that `α` in the definition of `p₁` is `nat`. Use the `@` operator to check for those "hidden" variables. Hence `#check @p₁` and `#check @π₁` yield almost the same result. If one wants to make an implicit variable like `{α : Type}` explicit later on in the same file one can use `variable (α)`.

The `variables` keyword is shorthand notation and can be circumvented as follows:

```lean
def p₁ {α : Type}: vector α 2 → α := sorry
#check p₁ -- p₁ : vector ?M_1 2 → ?M_1
#check @p₁ -- p₁ : Π {α : Type}, vector α 2 → α

def π₁ (β : Type): vector β 2 → β := sorry
#check π₁ -- π₁ : Π (β : Type), vector β 2 → β
#check @π₁ -- π₁ : Π (β : Type), vector β 2 → β
```

Nevertheless using `variables` may improve code clarity. Note that `variables` are somewhat "smart" in that definitions which do not depend on a previously introduced variable do not carry them in their signature: In the first example `π₁` does not depend on `α` at all.

## []
Square brackets refer to the [type class mechanism](https://leanprover.github.io/theorem_proving_in_lean/type_classes.html)

## Pattern matching
Consider the following code snippet recursively defining vector addition on length n vectors of some type `α` for which addition is defined.

```lean
import data.vector

variables {α : Type}

def vec_add [has_add α] : Π n : nat, vector α n → vector α n → vector α n
| 0 _ _ := vector.nil
| (n+1) v w :=
vector.cons (vector.head(v)+vector.head(w)) (vec_add n (vector.tail v) (vector.tail w))
#check vec_add -- vec_add : Π (n : ℕ), vector ?M_1 n → vector ?M_1 n → vector ?M_1 n
#check @vec_add -- vec_add : Π {α : Type} [_inst_1 : has_add α] (n : ℕ), vector α n → vector α n → vector α n

def vec_add_2 [has_add α](n:nat) : vector α n → vector α n → vector α n
| 0 _ _ := vector.nil
| (n+1) v w :=
vector.cons (vector.head(v)+vector.head(w)) (vec_add_2 n (vector.tail v) (vector.tail w))
#check vec_add_2 -- vec_add_2 : Π (n : ℕ), vector ?M_1 n → vector ?M_1 n → vector ?M_1 n
#check @vec_add_2 -- vec_add_2 : Π {α : Type} [_inst_1 : has_add α] (n : ℕ), vector α n → vector α n → vector α n
```

Both `vec_add` and `vec_add_2` have exactly the same type but the first definition type checks and the second does not. After `def vec_add_2 [has_add α](n:nat) :` the function `vec_add_2` is of fixed type `vector α n → vector α n → vector α n` and hence the recursion will not work out. This is important to remember for any kind of recursive definition.