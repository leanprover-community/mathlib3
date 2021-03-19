import algebra.module.basic

example : @add_comm_group.int_module.{0} int (@ring.to_add_comm_group _ int.ring) =
  @semiring.to_semimodule.{0} int
    (@comm_semiring.to_semiring.{0} int (@comm_ring.to_comm_semiring.{0} int int.comm_ring)) := rfl
