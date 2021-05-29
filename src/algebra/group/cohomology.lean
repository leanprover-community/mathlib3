/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import algebra.group_action_hom

/-!
# Group cohomology

We describe an explicit model for the group cohomology groups `Hⁿ(G,M)`,
as certain homogeneous cocycles over coboundaries.

## TODO

Write down map from usual n-cocycles to group cohomology and prove
that it's surjective with kernel precisely the classical n-coboundaries
-/

namespace add_comm_group
-- a sensible add_comm_group constructor

universe uA

variables (A : Type uA) [has_add A] [has_zero A] [has_neg A]

class add_comm_group_aux  : Prop :=
(add_assoc : ∀ (a b c : A), (a + b) + c = a + (b + c))
(zero_add : ∀ (a : A), 0 + a = a)
(add_left_neg : ∀ (a : A), -a + a = 0)
(add_comm : ∀ (a b : A), a + b = b + a)

open add_comm_group_aux

instance foo [add_comm_group_aux A] : add_comm_group A :=
{ add := (+),
  zero := 0,
  neg := has_neg.neg,
  add_zero := λ a, (add_comm_group_aux.add_comm 0 a) ▸ (zero_add a),
  ..‹add_comm_group_aux A›}

end add_comm_group

namespace group_cohomology

universes uG uM uA

variables (G : Type uG) [group G] (M : Type uM) [add_comm_group M]
  [distrib_mul_action G M] (n : ℕ)

-- need the homogeneous cochains, cocycles and coboundaries
/-- `cochain G M n.succ` is homogeneous `n`-cochains, namely functions
$$c:G^{n+1}\to M$$ which are homogeneous in the sense that $$c(s(g_i)_i)=s\bub c((g_i)_i)$$.

-/
@[ext] structure cochain_succ :=
(to_fun : (fin n → G) → M)
(smul_apply' : ∀ (s : G) (g : fin n → G), s • to_fun g = to_fun (λ i, s * g i))

namespace cochain_succ

instance : has_coe_to_fun (cochain_succ G M n) :=
{ F := _,
  coe := to_fun }

@[ext] theorem ext' (c₁ c₂ : cochain_succ G M n) (h : ∀ g : fin n → G, c₁ g = c₂ g) : c₁ = c₂ :=
ext c₁ c₂ (funext (λ (x : fin n → G), h x))

def zero : cochain_succ G M n :=
{ to_fun := λ _, 0,
  smul_apply' := λ s g, smul_zero s }

instance : has_zero (cochain_succ G M n) := ⟨zero G M n⟩

@[simp] lemma zero_apply (g : fin n → G) : (0 : cochain_succ G M n) g = 0 := rfl

variables {G M n}

@[simp] lemma smul_apply (c : cochain_succ G M n) (s : G) (g : fin n → G) : s • c g = c (λ i, s * g i) :=
c.smul_apply' s g

def neg (c₁ : cochain_succ G M n): cochain_succ G M n :=
{ to_fun := λ g, -c₁ g,
  smul_apply' := λ s g, by {rw ← smul_apply, apply smul_neg }, }

instance : has_neg (cochain_succ G M n) := ⟨neg⟩

@[simp] lemma neg_apply (c : cochain_succ G M n) (g : fin n → G) : (-c : cochain_succ G M n) g = -(c g) := rfl

def add (c₁ c₂ : cochain_succ G M n) : cochain_succ G M n :=
{ to_fun := λ g, c₁ g + c₂ g,
  smul_apply' := by {intros, simp * at *}, }

instance : has_add (cochain_succ G M n) := ⟨add⟩

@[simp] lemma add_apply (c₁ c₂ : cochain_succ G M n) (g : fin n → G) : (c₁ + c₂) g = c₁ g + c₂ g :=
rfl

instance : add_comm_group.add_comm_group_aux (cochain_succ G M n) :=
{ add_assoc := by { intros, ext, simp [add_assoc] },
  zero_add := by {intros, ext, simp },
  add_left_neg := by { intros, ext, simp },
  add_comm := by {intros, ext, simp [add_comm] },
}

end cochain_succ

def d {i j : ℕ} (hij : j = i + 1) : cochain_succ G M i →+ cochain_succ G M j :=
{ to_fun := λ c,
  { to_fun := λ g, (finset.range j).sum (λ k, if hk : k < j then (-1 : ℤ)^k • c sorry else 0),
    smul_apply' := sorry },
  map_zero' := sorry,
  map_add' := sorry }

--def H (n : ℕ) (G : Type uG) [group G] (M : Type uM) [add_comm_group M]
--  [distrib_mul_action G M] := sorry

end group_cohomology
