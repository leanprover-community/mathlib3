import data.W.basic

universe u

namespace W_type

section nat

/-- The constructors for the naturals -/
inductive nat_α : Type
| zero : nat_α
| succ : nat_α

instance : inhabited nat_α := ⟨ nat_α.zero ⟩

/-- The arity of the constructors for the naturals, `zero` takes no arguments, `succ` takes one -/
def nat_β : nat_α → Type
| nat_α.zero := empty
| nat_α.succ := unit

instance : inhabited (nat_β nat_α.succ) := ⟨ () ⟩

/-- The isomorphism from the naturals to its corresponding `W_type` -/
@[simp] def nat_to_W_type : ℕ → W_type nat_β
| nat.zero := ⟨ nat_α.zero , empty.elim ⟩
| (nat.succ n) := ⟨ nat_α.succ , λ _ , nat_to_W_type n ⟩

/-- The isomorphism from the `W_type` of the naturals to the naturals -/
@[simp] def W_type_to_nat : W_type nat_β → ℕ
| (W_type.mk nat_α.zero f) := 0
| (W_type.mk nat_α.succ f) := (W_type_to_nat (f ())).succ

lemma left_inv_W_type_to_nat : function.left_inverse W_type_to_nat nat_to_W_type
| nat.zero := rfl
| (nat.succ n) := by rw [nat_to_W_type, W_type_to_nat, left_inv_W_type_to_nat n]

lemma right_inv_W_type_to_nat : function.right_inverse W_type_to_nat nat_to_W_type
| (W_type.mk nat_α.zero f) := by { simp, tidy }
| (W_type.mk nat_α.succ f) := by { simp, tidy }

/-- The naturals are equivalent to their associated `W_type` -/
def nat_equiv_W_type : ℕ ≃ W_type nat_β :=
{ to_fun := nat_to_W_type,
  inv_fun := W_type_to_nat,
  left_inv := left_inv_W_type_to_nat,
  right_inv := right_inv_W_type_to_nat }

end nat

section list

variable (γ : Type u)

/--
The constructors for lists.
There is "one constructor `cons x` for each `x : γ`",
since we view `list γ` as
| nil : list γ
| cons x₀ : list γ → list γ
| cons x₁ : list γ → list γ
|   ⋮      γ many times
-/
inductive list_α : Type u
| nil : list_α
| cons : γ → list_α

instance : inhabited (list_α γ) := ⟨ list_α.nil ⟩

/-- The arities of each constructor for lists, `nil` takes no arguments, `cons hd` takes one -/
def list_β : list_α γ → Type u
| list_α.nil := pempty
| (list_α.cons hd) := punit

instance (hd : γ) : inhabited (list_β γ (list_α.cons hd)) := ⟨ punit.star ⟩

/-- The isomorphism from lists to W_types -/
@[simp] def list_to_W_type : list γ → W_type (list_β γ)
| list.nil := ⟨ list_α.nil, pempty.elim ⟩
| (list.cons hd tl) := ⟨ list_α.cons hd, λ _ , list_to_W_type tl ⟩

/-- The isomorphism from W_types to lists -/
@[simp] def W_type_to_list : W_type (list_β γ) → list γ
| (W_type.mk list_α.nil f) := []
| (W_type.mk (list_α.cons hd) f) := hd :: W_type_to_list (f punit.star)

lemma left_inv_W_type_to_list : function.left_inverse (W_type_to_list _) (list_to_W_type γ)
| list.nil := rfl
| (list.cons hd tl) := by simp [left_inv_W_type_to_list tl]

lemma right_inv_W_type_to_list : function.right_inverse (W_type_to_list _) (list_to_W_type γ)
| (W_type.mk list_α.nil f) := by { simp, tidy }
| (W_type.mk (list_α.cons x) f) := by { simp, tidy }

/-- The naturals are equivalent to their associated `W_type` -/
def list_equiv_W_type : list γ ≃ W_type (list_β γ) :=
{ to_fun := list_to_W_type _,
  inv_fun := W_type_to_list _,
  left_inv := left_inv_W_type_to_list _,
  right_inv := right_inv_W_type_to_list _ }

end list

section int

end int

end W_type
