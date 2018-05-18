/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

The partial recursive functions are defined similarly to the primitive
recursive functions, but now all functions are partial, implemented
using the `roption` monad, and there is an additional operation, called
μ-recursion, which performs unbounded minimization.
-/
import data.computability.primrec data.pfun

namespace nat

section rfind
parameter (p : ℕ →. bool)

private def lbp (m n : ℕ) : Prop := m = n + 1 ∧ ∀ k ≤ n, ff ∈ p k

parameter (H : ∃ n, tt ∈ p n ∧ ∀ k < n, (p k).dom)

private def wf_lbp : well_founded lbp :=
⟨let ⟨n, pn⟩ := H in begin
  suffices : ∀m k, n ≤ k + m → acc (lbp p) k,
  { from λa, this _ _ (nat.le_add_left _ _) },
  intros m k kn,
  induction m with m IH generalizing k;
    refine ⟨_, λ y r, _⟩; rcases r with ⟨rfl, a⟩,
  { injection roption.mem_unique pn.1 (a _ kn) },
  { exact IH _ (by rw nat.add_right_comm; exact kn) }
end⟩

protected def rfind_x : {n // tt ∈ p n ∧ ∀m < n, ff ∈ p m} :=
suffices ∀ k, (∀n < k, ff ∈ p n) → {n // tt ∈ p n ∧ ∀m < n, ff ∈ p m},
from this 0 (λ n, (nat.not_lt_zero _).elim),
@well_founded.fix _ _ lbp wf_lbp begin
  intros m IH al,
  have pm : (p m).dom,
  { rcases H with ⟨n, h₁, h₂⟩,
    rcases lt_trichotomy m n with h₃|h₃|h₃,
    { exact h₂ _ h₃ },
    { rw h₃, exact h₁.fst },
    { injection roption.mem_unique h₁ (al _ h₃) } },
  cases e : (p m).get pm,
  { suffices,
    exact IH _ ⟨rfl, this⟩ (λ n h, this _ (le_of_lt_succ h)),
    intros n h, cases lt_or_eq_of_le h with h h,
    { exact al _ h },
    { rw h, exact ⟨_, e⟩ } },
  { exact ⟨m, ⟨_, e⟩, al⟩ }
end

protected def rfind : ℕ := nat.rfind_x.1

protected theorem rfind_spec : tt ∈ p rfind := nat.rfind_x.2.1

protected theorem rfind_min : ∀ {m : ℕ}, m < rfind → ff ∈ p m := nat.rfind_x.2.right

protected theorem rfind_min' {m : ℕ} (h : tt ∈ p m) : rfind ≤ m :=
le_of_not_gt $ λ l, bool.no_confusion $
roption.mem_unique (rfind_min l) h

end rfind

inductive partrec : (ℕ →. ℕ) → Prop
| zero : partrec (pure 0)
| succ : partrec succ
| left : partrec (λ n, n.unpair.1)
| right : partrec (λ n, n.unpair.2)
| pair {f g} : partrec f → partrec g → partrec (λ n, mkpair <$> f n <*> g n)
| comp {f g} : partrec f → partrec g → partrec (λ n, g n >>= f)
| prec {f g} : partrec f → partrec g → partrec (unpaired (λ z n,
   n.elim (f z) (λ y IH, (mkpair z ∘ mkpair y) <$> IH >>= g)))
| rfind {f} : partrec f → partrec (unpaired (λ z n,
   ⟨_, nat.rfind (λ n, (λ m, m = 0) <$> f (mkpair z n))⟩))

namespace partrec

theorem of_eq {f g : ℕ →. ℕ} (hg : partrec g) (H : ∀ n, f n = g n) : partrec f :=
(funext H : f = g).symm ▸ hg

theorem prim {f : ℕ → ℕ} (hf : primrec f) : partrec f :=
begin
  induction hf,
  case nat.primrec.zero { exact zero },
  case nat.primrec.succ { exact succ },
  case nat.primrec.left { exact left },
  case nat.primrec.right { exact right },
  case nat.primrec.pair : f g hf hg pf pg {
    refine (pf.pair pg).of_eq (λ n, (roption.eq_some_of_mem _).symm),
    simp [has_seq.seq] },
  case nat.primrec.comp : f g hf hg pf pg {
    refine (pf.comp pg).of_eq (λ n, (roption.eq_some_of_mem _).symm),
    simp [has_seq.seq] },
  case nat.primrec.prec : f g hf hg pf pg {
    refine (pf.prec pg).of_eq (λ n, (roption.eq_some_of_mem _).symm),
    simp,
    induction n.unpair.2 with m IH, {simp},
    simp, exact ⟨_, ⟨_, IH, rfl⟩, rfl⟩ },
end

end partrec

end nat
