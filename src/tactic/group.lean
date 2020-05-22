/-
Copyright (c) 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Thomas Browning, Jalex Stark
-/
import tactic

/-!

## Tags

group_theory
-/

namespace tactic.interactive
setup_tactic_parser
open tactic.simp_arg_type

meta def group (locat : parse location) : tactic unit :=
simp_core {} skip tt [
  expr ``(mul_inv_self),
  symm_expr ``(mul_assoc),
  expr ``(mul_inv_self),
  expr ``(mul_inv_rev),
  expr ``(inv_inv),
  expr ``(inv_mul_self),
  expr ``(mul_inv_cancel_right),
  expr ``(mul_inv_cancel_left),
  expr ``(inv_mul_cancel_right),
  expr ``(inv_mul_cancel_left)]
  [] locat
end tactic.interactive

example {G : Type} [group G] (a b c d : G) : c *(a*b)*(b⁻¹*a⁻¹)*c = c*c :=
by group

example {G : Type} [group G] (a b c d : G) : (b*c⁻¹)*c *(a*b)*(b⁻¹*a⁻¹)*c = b*c :=
by group

example {G : Type} [group G] (a b c d : G) : c⁻¹*(b*c⁻¹)*c *(a*b)*(b⁻¹*a⁻¹*b⁻¹)*c = 1 :=
by group


def commutator {G} [group G] : G → (G → G) := λ g h, g * h * g⁻¹ * h⁻¹

def commutator3 {G} [group G] : G → (G → (G → G)) := λ g h k, commutator (commutator g h) k

-- The following is known as the Hall-Witt identity, see e.g. https://en.wikipedia.org/wiki/Three_subgroups_lemma#Proof_and_the_Hall%E2%80%93Witt_identity
example {G} [group G] (g h k : G) : g * (commutator3 g⁻¹ h k) * g⁻¹ * k * (commutator3 k⁻¹ g h) * k⁻¹ * h * (commutator3 h⁻¹ k g) * h⁻¹ = 1 :=
begin
repeat {unfold commutator3},
repeat {unfold commutator},
group,
end
