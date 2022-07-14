/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import data.int.cast
import data.nat.cast_field

/-!
# Cast of integers into fields

This file concerns the canonical homomorphism `ℤ → F`, where `F` is a field.

## Main results

 * `int.cast_div`: if `n` divides `m`, then `↑(m / n) = ↑m / ↑n`
-/

namespace int

open nat
variables {α : Type*}

@[simp] theorem cast_div [field α] {m n : ℤ} (n_dvd : n ∣ m) (n_nonzero : (n : α) ≠ 0) :
  ((m / n : ℤ) : α) = m / n :=
begin
  rcases n_dvd with ⟨k, rfl⟩,
  have : n ≠ 0, { rintro rfl, simpa using n_nonzero },
  rw [int.mul_div_cancel_left _ this, int.cast_mul, mul_div_cancel_left _ n_nonzero],
end

end int
