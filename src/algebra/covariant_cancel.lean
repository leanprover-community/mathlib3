#exit
import algebra.ordered_monoid_lemmas

variables {α : Type*} {a b c d : α}

@[to_additive]
def contravariant.to_left_cancel_semigroup [semigroup α] [partial_order α]
  [contravariant_class α α (*) (≤)] :
  left_cancel_semigroup α :=
{ mul_left_cancel := λ a b c bc, (contravariant_class.covtc _ bc.le).antisymm
    (contravariant_class.covtc _ bc.ge),
  ..(infer_instance : semigroup α) }

@[to_additive]
def contravariant.to_right_cancel_semigroup [semigroup α] [partial_order α]
  [contravariant_class α α (function.swap (*)) (≤)] :
  right_cancel_semigroup α :=
{ mul_right_cancel := λ a b c bc,
le_antisymm (contravariant_class.covtc b bc.le) (contravariant_class.covtc b bc.ge)
  ..(infer_instance : semigroup α) }
