-- TODO: does it make sense to go directly into src/?
import .defs

open nat

inductive triv_group : Sort*
| e : triv_group

lemma triv_group.ext (a b : triv_group) : a = b := begin
  cases a,
  cases b,
  refl,
end

instance : group triv_group :=
{
  one := triv_group.e,
  mul := (λ a b, triv_group.e),
  inv := (λ a, triv_group.e),
  mul_assoc := (λ a b c, triv_group.ext _ _),
  one_mul := (λ a, triv_group.ext _ _),
  mul_one := (λ a, triv_group.ext _ _),
  mul_left_inv := (λ a, triv_group.ext _ _),
}

def iterated_wreath_product (G : Type*) : ℕ → Type*
| zero := triv_group
| (succ n) := iterated_wreath_product n ≀[G] G

lemma iterated_wreath_product_zero (G : Type*) : iterated_wreath_product G zero = triv_group := rfl

lemma iterated_wreath_product_succ (G : Type*) (n : ℕ) : iterated_wreath_product G (succ n) = (iterated_wreath_product G n ≀[G] G) := rfl


instance (G : Type*) [group G] (n : ℕ) : group (iterated_wreath_product G n) :=
begin
  induction n with n ih,
  {
    rw iterated_wreath_product_zero,
    apply_instance
  },
  {
    rw iterated_wreath_product_succ,
    apply wreath_product_group_explicit,
    exact ih,
  }
end
