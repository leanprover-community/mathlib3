/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.group_action.defs
import data.set_like

/-!
# Typeclasses for set-like objects with membership closed under an operation
-/

/-- Objects which contain a constant. -/
class op₀_closed (S : Type*) {A : Type*} [has_mem A S] (op : A) :=
(mem : ∀ (s : S), op ∈ s)

/-- Objects which are closed under a unary operation. -/
class op₁_closed (S : Type*) {A : Type*} [has_mem A S] (op : A → A) :=
(mem : ∀ (s : S) {x}, x ∈ s → op x ∈ s)

/-- Objects which are closed under a binary operation. -/
class op₂_closed (S : Type*) {A : Type*} [has_mem A S] (op : A → A → A) :=
(mem : ∀ (s : S) {x y}, x ∈ s → y ∈ s → op x y ∈ s)

/-! ### Aliases -/
section

variables (S : Type*) (R : Type*) (A : Type*) [has_mem A S]

/-- Objects which contain `1`. -/
@[to_additive "Objects which contain `0`"]
abbreviation one_closed [has_one A] := op₀_closed S (1 : A)

/-- Objects which are closed under `⁻¹`. -/
@[to_additive "Objects which are closed under `-`"]
abbreviation inv_closed [has_inv A] := op₁_closed S (has_inv.inv : A → A)

/-- Objects which are closed under `*`. -/
@[to_additive "Objects which are closed under `+`."]
abbreviation mul_closed [has_mul A] := op₂_closed S ((*) : A → A → A)

/-- Objects which are closed under `/`. -/
@[to_additive "Objects which are closed under `-`."]
abbreviation div_closed [has_div A] := op₂_closed S ((/) : A → A → A)

/-- Objects which are closed under `•`. -/
@[to_additive "Objects which are closed under `+ᵥ`."]
abbreviation smul_closed [has_scalar R A] := Π r : R, op₁_closed S ((•) r : A → A)

end


/-! ### Lemmas -/

section

variables {S : Type*} {R : Type*} {A : Type*} [has_mem A S]

@[simp, to_additive] lemma one_mem [has_one A] [one_closed S A]
  (s : S) :
  (1 : A) ∈ s := op₀_closed.mem s
@[simp, to_additive] lemma inv_mem [has_inv A] [inv_closed S A]
  (s : S) {x : A} (hx : x ∈ s) :
  x⁻¹ ∈ s := op₁_closed.mem s hx
@[simp, to_additive] lemma mul_mem [has_mul A] [mul_closed S A]
  (s : S) {x y : A} (hx : x ∈ s) (hy : y ∈ s) :
  x * y ∈ s := op₂_closed.mem s hx hy
@[simp, to_additive] lemma div_mem [has_div A] [div_closed S A]
  (s : S) {x y : A} (hx : x ∈ s) (hy : y ∈ s) :
  x / y ∈ s := op₂_closed.mem s hx hy
@[simp, to_additive] lemma smul_mem [has_scalar R A] [smul_closed S R A]
  (s : S) (r : R) {x : A} (hx : x ∈ s):
  r • x ∈ s := op₁_closed.mem s hx

end

/-! ### Derived instances on `set_like` -/

namespace set_like

variables {S : Type*} {R : Type*} {A : Type*} [set_like S A] (s : S)

@[to_additive]
instance [has_one A] [one_closed S A] : has_one s := ⟨⟨(1 : A), one_mem s⟩⟩
@[to_additive]
instance [has_mul A] [mul_closed S A] : has_mul s := ⟨λ a b, ⟨(a * b : A), mul_mem s a.prop b.prop⟩⟩
@[to_additive]
instance [has_div A] [div_closed S A] : has_div s := ⟨λ a b, ⟨(a / b : A), div_mem s a.prop b.prop⟩⟩
@[to_additive]
instance [has_inv A] [inv_closed S A] : has_inv s := ⟨λ a, ⟨(a⁻¹ : A), inv_mem s a.prop⟩⟩
instance [has_vadd R A] [vadd_closed S R A] : has_vadd R s :=
⟨λ r a, ⟨(r +ᵥ a : A), vadd_mem s r a.prop⟩⟩
@[to_additive set_like.has_vadd]
instance [has_scalar R A] [smul_closed S R A] : has_scalar R s :=
⟨λ r a, ⟨(r • a : A), smul_mem s r a.prop⟩⟩

end set_like
