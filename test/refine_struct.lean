import tactic.interactive

section refine_struct

variables {α : Type} [_inst : monoid α]
include _inst

example : true :=
begin
  have : group α,
  { refine_struct { .._inst },
    guard_tags _field inv group, admit,
    guard_tags _field mul_left_inv group, admit, },
  trivial
end

end refine_struct

def my_foo {α} (x : semigroup α) (y : group α) : true := trivial

example {α : Type} : true :=
begin
  have : true,
  { refine_struct (@my_foo α { .. } { .. } ),
      -- 9 goals
    guard_tags _field mul semigroup, admit,
      -- case semigroup, mul
      -- α : Type
      -- ⊢ α → α → α

    guard_tags _field mul_assoc semigroup, admit,
      -- case semigroup, mul_assoc
      -- α : Type
      -- ⊢ ∀ (a b c : α), a * b * c = a * (b * c)

    guard_tags _field mul group, admit,
      -- case group, mul
      -- α : Type
      -- ⊢ α → α → α

    guard_tags _field mul_assoc group, admit,
      -- case group, mul_assoc
      -- α : Type
      -- ⊢ ∀ (a b c : α), a * b * c = a * (b * c)

    guard_tags _field one group, admit,
      -- case group, one
      -- α : Type
      -- ⊢ α

    guard_tags _field one_mul group, admit,
      -- case group, one_mul
      -- α : Type
      -- ⊢ ∀ (a : α), 1 * a = a

    guard_tags _field mul_one group, admit,
      -- case group, mul_one
      -- α : Type
      -- ⊢ ∀ (a : α), a * 1 = a

    guard_tags _field inv group, admit,
      -- case group, inv
      -- α : Type
      -- ⊢ α → α

    guard_tags _field mul_left_inv group, admit,
      -- case group, mul_left_inv
      -- α : Type
      -- ⊢ ∀ (a : α), a⁻¹ * a = 1
  },
  trivial
end

def my_bar {α} (x : semigroup α) (y : group α) (i j : α) : α := i

example {α : Type} : true :=
begin
  have : monoid α,
  { refine_struct { mul := my_bar { .. } { .. } },
    guard_tags _field mul semigroup, admit,
    guard_tags _field mul_assoc semigroup, admit,
    guard_tags _field mul group, admit,
    guard_tags _field mul_assoc group, admit,
    guard_tags _field one group, admit,
    guard_tags _field one_mul group, admit,
    guard_tags _field mul_one group, admit,
    guard_tags _field inv group, admit,
    guard_tags _field mul_left_inv group, admit,
    guard_tags _field mul_assoc monoid, admit,
    guard_tags _field one monoid, admit,
    guard_tags _field one_mul monoid, admit,
    guard_tags _field mul_one monoid, admit, },
  trivial
end
