import algebra.group.units
import algebra.field.defs
import algebra.char_zero.defs
import algebra.group_with_zero.units.basic
import algebra.hom.group
import data.int.char_zero

example {R : Type*} (x : ℤ) [division_ring R] [char_zero R] :
  is_unit (x : R) ↔ x ≠ 0:=
by rw [is_unit_iff_ne_zero, int.cast_ne_zero]

-- Don't forget to rebase
