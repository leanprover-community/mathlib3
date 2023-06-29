/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Floris van Doorn
-/
import data.pnat.basic

/-!
# Explicit least witnesses to existentials on positive natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Implemented via calling out to `nat.find`.

-/

namespace pnat

variables {p q : ℕ+ → Prop} [decidable_pred p] [decidable_pred q] (h : ∃ n, p n)

instance decidable_pred_exists_nat :
  decidable_pred (λ n' : ℕ, ∃ (n : ℕ+) (hn : n' = n), p n) := λ n',
decidable_of_iff' (∃ (h : 0 < n'), p ⟨n', h⟩) $ subtype.exists.trans $
  by simp_rw [subtype.coe_mk, @exists_comm (_ < _) (_ = _), exists_prop, exists_eq_left']


include h

/-- The `pnat` version of `nat.find_x` -/
protected def find_x : {n // p n ∧ ∀ m : ℕ+, m < n → ¬p m} :=
begin
  have : ∃ (n' : ℕ) (n : ℕ+) (hn' : n' = n), p n, from exists.elim h (λ n hn, ⟨n, n, rfl, hn⟩),
  have n := nat.find_x this,
  refine ⟨⟨n, _⟩, _, λ m hm pm, _⟩,
  { obtain ⟨n', hn', -⟩ := n.prop.1,
    rw hn',
    exact n'.prop },
  { obtain ⟨n', hn', pn'⟩ := n.prop.1,
    simpa [hn', subtype.coe_eta] using pn' },
  { exact n.prop.2 m hm ⟨m, rfl, pm⟩ }
end

/--
If `p` is a (decidable) predicate on `ℕ+` and `hp : ∃ (n : ℕ+), p n` is a proof that
there exists some positive natural number satisfying `p`, then `pnat.find hp` is the
smallest positive natural number satisfying `p`. Note that `pnat.find` is protected,
meaning that you can't just write `find`, even if the `pnat` namespace is open.

The API for `pnat.find` is:

* `pnat.find_spec` is the proof that `pnat.find hp` satisfies `p`.
* `pnat.find_min` is the proof that if `m < pnat.find hp` then `m` does not satisfy `p`.
* `pnat.find_min'` is the proof that if `m` does satisfy `p` then `pnat.find hp ≤ m`.
-/
protected def find : ℕ+ :=
pnat.find_x h

protected theorem find_spec : p (pnat.find h) :=
(pnat.find_x h).prop.left

protected theorem find_min : ∀ {m : ℕ+}, m < pnat.find h → ¬p m :=
(pnat.find_x h).prop.right

protected theorem find_min' {m : ℕ+} (hm : p m) : pnat.find h ≤ m :=
le_of_not_lt (λ l, pnat.find_min h l hm)

variables {n m : ℕ+}

lemma find_eq_iff : pnat.find h = m ↔ p m ∧ ∀ n < m, ¬ p n :=
begin
  split,
  { rintro rfl, exact ⟨pnat.find_spec h, λ _, pnat.find_min h⟩ },
  { rintro ⟨hm, hlt⟩,
    exact le_antisymm (pnat.find_min' h hm) (not_lt.1 $ imp_not_comm.1 (hlt _) $ pnat.find_spec h) }
end

@[simp] lemma find_lt_iff (n : ℕ+) : pnat.find h < n ↔ ∃ m < n, p m :=
⟨λ h2, ⟨pnat.find h, h2, pnat.find_spec h⟩, λ ⟨m, hmn, hm⟩, (pnat.find_min' h hm).trans_lt hmn⟩

@[simp] lemma find_le_iff (n : ℕ+) : pnat.find h ≤ n ↔ ∃ m ≤ n, p m :=
by simp only [exists_prop, ← lt_add_one_iff, find_lt_iff]

@[simp] lemma le_find_iff (n : ℕ+) : n ≤ pnat.find h ↔ ∀ m < n, ¬ p m :=
by simp_rw [← not_lt, find_lt_iff, not_exists]

@[simp] lemma lt_find_iff (n : ℕ+) : n < pnat.find h ↔ ∀ m ≤ n, ¬ p m :=
by simp only [← add_one_le_iff, le_find_iff, add_le_add_iff_right]

@[simp] lemma find_eq_one : pnat.find h = 1 ↔ p 1 :=
by simp [find_eq_iff]

@[simp] lemma one_le_find : 1 < pnat.find h ↔ ¬ p 1 :=
not_iff_not.mp $ by simp

theorem find_mono (h : ∀ n, q n → p n)
  {hp : ∃ n, p n} {hq : ∃ n, q n} :
  pnat.find hp ≤ pnat.find hq :=
pnat.find_min' _ (h _ (pnat.find_spec hq))

lemma find_le {h : ∃ n, p n} (hn : p n) : pnat.find h ≤ n :=
(pnat.find_le_iff _ _).2 ⟨n, le_rfl, hn⟩

lemma find_comp_succ (h : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h1 : ¬ p 1) :
  pnat.find h = pnat.find h₂ + 1 :=
begin
  refine (find_eq_iff _).2 ⟨pnat.find_spec h₂, λ n, pnat.rec_on n _ _⟩,
  { simp [h1] },
  intros m IH hm,
  simp only [add_lt_add_iff_right, lt_find_iff] at hm,
  exact hm _ le_rfl
end

end pnat
