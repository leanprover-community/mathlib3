import algebra.order.archimedean
import algebra.order.nonneg.ring

instance archimedean [ordered_add_comm_monoid α] [archimedean α] : archimedean {x : α // 0 ≤ x} :=
⟨λ x y hy,
  let ⟨n, hr⟩ := archimedean.arch (x : α) (hy : (0 : α) < y) in
  ⟨n, show (x : α) ≤ (n • y : {x : α // 0 ≤ x}), by simp [*, -nsmul_eq_mul, nsmul_coe]⟩⟩

instance floor_semiring [ordered_semiring α] [floor_semiring α] : floor_semiring {r : α // 0 ≤ r} :=
{ floor := λ a, ⌊(a : α)⌋₊,
  ceil := λ a, ⌈(a : α)⌉₊,
  floor_of_neg := λ a ha, floor_semiring.floor_of_neg ha,
  gc_floor := λ a n ha, begin
    refine (floor_semiring.gc_floor (show 0 ≤ (a : α), from ha)).trans _,
    rw [←subtype.coe_le_coe, nonneg.coe_nat_cast]
  end,
  gc_ceil := λ a n, begin
    refine (floor_semiring.gc_ceil (a : α) n).trans _,
    rw [←subtype.coe_le_coe, nonneg.coe_nat_cast]
  end}

@[norm_cast] lemma nat_floor_coe [ordered_semiring α] [floor_semiring α] (a : {r : α // 0 ≤ r}) :
  ⌊(a : α)⌋₊ = ⌊a⌋₊ := rfl

@[norm_cast] lemma nat_ceil_coe [ordered_semiring α] [floor_semiring α] (a : {r : α // 0 ≤ r}) :
  ⌈(a : α)⌉₊ = ⌈a⌉₊  := rfl
