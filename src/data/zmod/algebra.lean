/-
Copyleft. No rights reserved.
Authors: Johan Commelin
-/

import data.zmod.basic
import ring_theory.algebra


namespace zmod
variables (R : Type*) [ring R]


section
variables {n : ℕ} (m : ℕ) [char_p R m]

def algebra' (h : m ∣ n) : algebra (zmod n) R :=
{ smul := λ a r, a * r,
  commutes' := λ a r, show (a * r : R) = r * a,
  begin
    rcases zmod.int_cast_surjective a with ⟨k, rfl⟩,
    show zmod.cast_hom h R k * r = r * zmod.cast_hom h R k,
    rw ring_hom.map_int_cast,
    exact commute.cast_int_left r k,
  end,
  smul_def' := λ a r, rfl,
  .. zmod.cast_hom h R }

end

section
variables (n : ℕ) [char_p R n]

instance : algebra (zmod n) R := algebra' R n (dvd_refl n)

end

end zmod
