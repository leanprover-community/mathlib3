/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.char_p.basic
import ring_theory.subring

/-!
# Characteristic of subrings
-/

universes u v

namespace char_p

instance subsemiring (R : Type u) [semiring R] (p : ℕ) [char_p R p] (S : subsemiring R) :
  char_p S p :=
⟨λ x, iff.symm $ (char_p.cast_eq_zero_iff R p x).symm.trans
⟨λ h, subtype.eq $ show S.subtype x = 0, by rw [ring_hom.map_nat_cast, h],
  λ h, S.subtype.map_nat_cast x ▸ by rw [h, ring_hom.map_zero]⟩⟩

instance subring (R : Type u) [ring R] (p : ℕ) [char_p R p] (S : subring R) :
  char_p S p :=
⟨λ x, iff.symm $ (char_p.cast_eq_zero_iff R p x).symm.trans
⟨λ h, subtype.eq $ show S.subtype x = 0, by rw [ring_hom.map_nat_cast, h],
  λ h, S.subtype.map_nat_cast x ▸ by rw [h, ring_hom.map_zero]⟩⟩

instance subring' (R : Type u) [comm_ring R] (p : ℕ) [char_p R p] (S : subring R) :
  char_p S p :=
char_p.subring R p S

end char_p
