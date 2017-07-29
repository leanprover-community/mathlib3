/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro

Basic operations on the natural numbers.
-/
import logic.basic

universe u

open tactic

namespace nat

protected theorem eq_mul_of_div_eq_right {a b c : ℕ} (H1 : b ∣ a) (H2 : a / b = c) : 
  a = b * c := 
by rw [← H2, nat.mul_div_cancel' H1] 
 
protected theorem div_eq_iff_eq_mul_right {a b c : ℕ} (H : b > 0) (H' : b ∣ a) : 
  a / b = c ↔ a = b * c := 
⟨nat.eq_mul_of_div_eq_right H', nat.div_eq_of_eq_mul_right H⟩ 
 
protected theorem div_eq_iff_eq_mul_left {a b c : ℕ} (H : b > 0) (H' : b ∣ a) : 
  a / b = c ↔ a = c * b := 
by rw mul_comm; exact nat.div_eq_iff_eq_mul_right H H' 
 
protected theorem eq_mul_of_div_eq_left {a b c : ℕ} (H1 : b ∣ a) (H2 : a / b = c) : 
  a = c * b := 
by rw [mul_comm, nat.eq_mul_of_div_eq_right H1 H2] 

end nat
