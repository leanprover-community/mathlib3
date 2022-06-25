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
⟨λ x y, begin
  casesI p,
  { exact @@subsingleton.elim int_algebra_subsingleton x y },
  refine x.algebra_ext y (λ r, _),
  convert_to (@algebra_map _ _ _ _ x) ((coe : zmod p.succ → zmod p.succ) r) =
             (@algebra_map _ _ _ _ y) ((coe : zmod p.succ → zmod p.succ) r),
  { rw [cast_id] },
  { rw [cast_id] },
  rw [←nat_cast_val r, ←nat.smul_one_eq_coe, map_nsmul, map_nsmul, map_one, map_one]
end⟩

section
variables {n : ℕ} (m : ℕ) [char_p R m]

/-- The `zmod n`-algebra structure on rings whose characteristic `m` divides `n` -/
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

instance (p : ℕ) [char_p R p] : algebra (zmod p) R := algebra' R p dvd_rfl

end

end zmod
