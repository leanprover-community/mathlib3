/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.zmod.basic
import algebra.algebra.basic

/-!
# The `zmod n`-algebra structure on rings whose characteristic divides `n`
-/

namespace zmod

variables (R : Type*) [ring R]

instance (p : ℕ) : subsingleton (algebra (zmod p) R) :=
⟨λ x y, algebra.algebra_ext _ _ $ ring_hom.congr_fun $ subsingleton.elim _ _⟩

section
variables {n : ℕ} (m : ℕ) [char_p R m]

/-- The `zmod n`-algebra structure on rings whose characteristic `m` divides `n` -/
def algebra' (h : m ∣ n) : algebra (zmod n) R :=
{ smul := λ a r, a * r,
  commutes' := λ a r, show (a * r : R) = r * a,
  begin
    rcases zmod.int_cast_surjective a with ⟨k, rfl⟩,
    show zmod.cast_hom h R k * r = r * zmod.cast_hom h R k,
    rw map_int_cast,
    exact commute.cast_int_left r k,
  end,
  smul_def' := λ a r, rfl,
  .. zmod.cast_hom h R }

end

instance (p : ℕ) [char_p R p] : algebra (zmod p) R := algebra' R p dvd_rfl

end zmod
