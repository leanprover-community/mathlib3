/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.ordinal_arithmetic

/-!
### Principal ordinals

We define principal or indecomposable ordinals, and we prove the standard properties about them.

### Todo
* Prove the characterization of additive principal ordinals.
* Prove the characterization of multiplicative principal ordinals.
* Refactor any related theorems from `ordinal_arithmetic` into this file.
-/

universe u

noncomputable theory

namespace ordinal

/-! ### Principal ordinals -/

/-- An ordinal `o` is said to be principal or indecomposable under an operation when the set of
ordinals less than it is closed under that operation. In standard mathematical usage, this term is
almost exclusively used for additive and multiplicative principal ordinals.

For simplicity, we break usual convention and regard 0 as principal. -/
def principal (op : ordinal → ordinal → ordinal) (o : ordinal) : Prop :=
∀ ⦃a b⦄, a < o → b < o → op a b < o

theorem principal_iff_principal_swap {op : ordinal → ordinal → ordinal} {o : ordinal} :
  principal op o ↔ principal (function.swap op) o :=
by split; exact λ h a b ha hb, h hb ha

theorem principal_zero {op : ordinal → ordinal → ordinal} : principal op 0 :=
λ a _ h, (ordinal.not_lt_zero a h).elim

@[simp] theorem principal_one_iff {op : ordinal → ordinal → ordinal} :
  principal op 1 ↔ op 0 0 = 0 :=
begin
  refine ⟨λ h, _, λ h a b ha hb, _⟩,
  { rwa ←lt_one_iff_zero,
    exact h zero_lt_one zero_lt_one },
  { rwa [lt_one_iff_zero, ha, hb] at * }
end

theorem principal.iterate_lt {op : ordinal → ordinal → ordinal} {a o : ordinal} (hao : a < o)
  (ho : principal op o) (n : ℕ) : (op a)^[n] a < o :=
begin
  induction n with n hn,
  { rwa function.iterate_zero },
  { rw function.iterate_succ', exact ho hao hn }
end

theorem op_eq_self_of_principal {op : ordinal → ordinal → ordinal} {a o : ordinal.{u}}
  (hao : a < o) (H : is_normal (op a)) (ho : principal op o) (ho' : is_limit o) : op a o = o :=
begin
  refine le_antisymm _ (H.self_le _),
  rw [←is_normal.bsup_eq.{u u} H ho', bsup_le],
  exact λ b hbo, le_of_lt (ho hao hbo)
end

theorem nfp_le_of_principal {op : ordinal → ordinal → ordinal}
  {a o : ordinal} (hao : a < o) (ho : principal op o) : nfp (op a) a ≤ o :=
nfp_le.2 $ λ n, le_of_lt (ho.iterate_lt hao n)

/-! ### Principal ordinals are unbounded -/

/-- The least strict upper bound of `op` applied to all pairs of ordinals less than `o`. This is
essentially a two-argument version of `ordinal.blsub`. -/
def blsub₂ (op : ordinal → ordinal → ordinal) (o : ordinal) : ordinal :=
lsub (λ x : o.out.α × o.out.α, op (typein o.out.r x.1) (typein o.out.r x.2))

theorem lt_blsub₂ (op : ordinal → ordinal → ordinal) {o : ordinal} {a b : ordinal} (ha : a < o)
  (hb : b < o) : op a b < blsub₂ op o :=
begin
  convert lt_lsub _ (prod.mk (enum o.out.r a (by rwa type_out)) (enum o.out.r b (by rwa type_out))),
  simp only [typein_enum]
end

theorem principal_nfp_blsub₂ (op : ordinal → ordinal → ordinal) (o : ordinal) :
  principal op (nfp (blsub₂.{u u} op) o) :=
begin
  intros a b ha hb,
  rw lt_nfp at *,
  cases ha with m hm,
  cases hb with n hn,
  cases le_total ((blsub₂.{u u} op)^[m] o) ((blsub₂.{u u} op)^[n] o) with h h,
  { use n + 1,
    rw function.iterate_succ',
    exact lt_blsub₂ op (hm.trans_le h) hn },
  { use m + 1,
    rw function.iterate_succ',
    exact lt_blsub₂ op hm (hn.trans_le h) },
end

theorem unbounded_principal (op : ordinal → ordinal → ordinal) :
  set.unbounded (<) {o | principal op o} :=
λ o, ⟨_, principal_nfp_blsub₂ op o, (le_nfp_self _ o).not_lt⟩

end ordinal
