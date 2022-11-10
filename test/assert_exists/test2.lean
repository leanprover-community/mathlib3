import tactic.assert_exists
import algebra.order.ring.defs
import data.int.basic

assert_exists int
assert_not_exists rat

assert_instance ring ℤ
assert_no_instance ordered_ring ℤ
