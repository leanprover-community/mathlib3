/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa
-/

import tactic.basic
import data.zmod.basic


/-!
# IMO 1959 Q1

Prove that the fraction `(21n+4)/(14n+3)` is irreducible for every natural number `n`.

Since Lean doesn't have a concept of "irreducible fractions" per se, we just formalize this
as saying the numerator and denominator are relatively prime.
-/

lemma modfact1 (n : ℕ): ((2^(3+n)) : zmod 7).val = (2^n : zmod 7).val :=
begin
  have h2 : (2^3 : zmod 7) = 1 := by refl,
  have h4 : (2^(3+n) : zmod 7).val = (2^3*2^n : zmod 7).val := congr_arg zmod.val (pow_add 2 3 n),
  rwa [h2,one_mul] at h4,
end

lemma modfact2 (n : ℕ) : (2^n : zmod 7) = 2^(n : zmod 3).val :=
begin
  norm_cast at *,

  sorry,

end

example (n : ℕ) : ((2^n -1) : zmod 7).val = 0 ↔ (n : zmod 3).val = 0 :=
begin
  split,
  { rw modfact2,
    have h1 := zmod.val_lt (n : zmod 3),
    intro hn,
    rw zmod.val_eq_zero _ at hn,
    have h2 : (n : zmod 3).val = 0 ∨ (n : zmod 3).val = 1 ∨ (n : zmod 3).val = 2 := by omega,
    cases h2,
    assumption,
    cases h2;
    rw h2 at hn;
    exfalso;
    norm_num at hn,
    contrapose! hn,
    dec_trivial },
  { intro hn,
    rw [(zmod.val_eq_zero (2^n - 1)), modfact2, hn],
    norm_num }
end

example (n : ℕ) : ¬((2^n + 1) : zmod 7).val = 0 :=
begin
  intro hn,
  have h1 := zmod.val_lt (n : zmod 3),
  have h2 : (n : zmod 3).val = 0 ∨ (n : zmod 3).val = 1 ∨ (n : zmod 3).val = 2 := by omega,
  rw [zmod.val_eq_zero,modfact2] at hn,
  repeat {cases h2};
  rw h2 at hn; ring at hn; contrapose! hn; dec_trivial,
end
