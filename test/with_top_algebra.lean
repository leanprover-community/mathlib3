import algebra.ordered_ring
variables {R : Type*} [h : ordered_semiring R]

lemma diamond :
  (@with_top.add_comm_monoid R
    (@non_unital_non_assoc_semiring.to_add_comm_monoid R
      (@non_assoc_semiring.to_non_unital_non_assoc_semiring R
        (@semiring.to_non_assoc_semiring R
          (@ordered_semiring.to_semiring R h)))))
        =
  (@ordered_add_comm_monoid.to_add_comm_monoid (with_top R)
    (@with_top.ordered_add_comm_monoid R
      (@ordered_cancel_add_comm_monoid.to_ordered_add_comm_monoid R
        (@ordered_semiring.to_ordered_cancel_add_comm_monoid R h)))) :=
rfl
