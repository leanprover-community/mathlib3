import algebra.order.floor
import algebra.ring.prod

variables {α β : Type*}

attribute [simp] int.le_floor int.ceil_le

instance [ordered_semiring α] [ordered_semiring β] [floor_semiring α] [floor_semiring β] :
  floor_semiring (α × β) :=
{ floor := λ x, min ⌊x.1⌋₊ ⌊x.2⌋₊,
  ceil := λ x, max ⌈x.1⌉₊ ⌈x.2⌉₊,
  floor_of_neg := λ x hx,
    by rw [nat.floor_of_nonpos hx.le.1, nat.floor_of_nonpos hx.le.2, min_self],
  gc_floor := λ x n hx, by simp only [prod.le_def, le_min_iff, nat.le_floor_iff hx.1,
    nat.le_floor_iff hx.2, prod.fst_nat_cast, prod.snd_nat_cast],
  gc_ceil := λ x n, by simp [prod.le_def] }

instance [ordered_ring α] [ordered_ring β] [floor_ring α] [floor_ring β] : floor_ring (α × β) :=
{ floor := λ x, min ⌊x.1⌋ ⌊x.2⌋,
  ceil := λ x, max ⌈x.1⌉ ⌈x.2⌉,
  gc_coe_floor := λ n x, by simp [prod.le_def, int.le_floor],
  gc_ceil_coe := λ x n, by simp [prod.le_def, int.ceil_le] }
