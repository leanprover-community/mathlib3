/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

Define the p-adic integers ℤ_p as a subtype of ℚ_p. Show ℤ_p is a ring.
-/

import data.padics.padic_rationals
open nat padic
noncomputable theory

section padic_int
variables {p : ℕ} (hp : prime p)

def padic_int := {x : ℚ_[hp] // padic_norm_e x ≤ 1}
notation `ℤ_[`hp`]` := padic_int hp
end padic_int 

namespace padic_int 
variables {p : ℕ} {hp : prime p}

def add : ℤ_[hp] → ℤ_[hp] → ℤ_[hp]
| ⟨x, hx⟩ ⟨y, hy⟩ := ⟨x+y, 
    le_trans (padic_norm_e.nonarchimedean _ _) (max_le_iff.2 ⟨hx,hy⟩)⟩

def mul : ℤ_[hp] → ℤ_[hp] → ℤ_[hp]
| ⟨x, hx⟩ ⟨y, hy⟩ := ⟨x*y, 
    begin rw padic_norm_e.mul, apply mul_le_one; {assumption <|> apply padic_norm_e.nonneg} end⟩

def neg : ℤ_[hp] → ℤ_[hp]
| ⟨x, hx⟩ := ⟨-x, by simpa⟩

instance : ring ℤ_[hp] :=
begin 
  refine { add := add,
           mul := mul,
           neg := neg,
           zero := ⟨0, by simp⟩,
           one := ⟨1, by simp⟩,
           .. };
  {repeat {rintro ⟨_, _⟩}, simp [mul_assoc, left_distrib, right_distrib, add, mul, neg]}
end 

end padic_int 