/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.char_p.basic
import algebra.ring.pi

/-!
# Characteristic of semirings of functions
-/

universes u v

namespace char_p

instance pi (ι : Type u) [hi : nonempty ι] (R : Type v) [semiring R] (p : ℕ) [char_p R p] :
  char_p (ι → R) p :=
⟨λ x, let ⟨i⟩ := hi in iff.symm $ (char_p.cast_eq_zero_iff R p x).symm.trans
⟨λ h, funext $ λ j, show pi.eval_ring_hom (λ _, R) j (↑x : ι → R) = 0,
    by rw [ring_hom.map_nat_cast, h],
  λ h, (pi.eval_ring_hom (λ _: ι, R) i).map_nat_cast x ▸ by rw [h, ring_hom.map_zero]⟩⟩

-- diamonds
instance pi' (ι : Type u) [hi : nonempty ι] (R : Type v) [comm_ring R] (p : ℕ) [char_p R p] :
  char_p (ι → R) p :=
char_p.pi ι R p

end char_p
