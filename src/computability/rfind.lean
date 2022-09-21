import data.pfun

open part


local attribute [-simp] not_forall

namespace nat

section rfind
parameter (p : ℕ →. bool)

private def lbp (m n : ℕ) : Prop := m = n + 1 ∧ ∀ k ≤ n, ff ∈ p k

parameter (H : ∃ n, tt ∈ p n ∧ ∀ k < n, (p k).dom)

private def wf_lbp : well_founded lbp :=
⟨let ⟨n, pn⟩ := H in begin
  suffices : ∀m k, n ≤ k + m → acc (lbp p) k,
  { from λ a, this _ _ (nat.le_add_left _ _) },
  intros m k kn,
  induction m with m IH generalizing k;
    refine ⟨_, λ y r, _⟩; rcases r with ⟨rfl, a⟩,
  { injection mem_unique pn.1 (a _ kn) },
  { exact IH _ (by rw nat.add_right_comm; exact kn) }
end⟩

def rfind_x : {n // tt ∈ p n ∧ ∀m < n, ff ∈ p m} :=
suffices ∀ k, (∀n < k, ff ∈ p n) → {n // tt ∈ p n ∧ ∀m < n, ff ∈ p m},
from this 0 (λ n, (nat.not_lt_zero _).elim),
@well_founded.fix _ _ lbp wf_lbp begin
  intros m IH al,
  have pm : (p m).dom,
  { rcases H with ⟨n, h₁, h₂⟩,
    rcases lt_trichotomy m n with h₃|h₃|h₃,
    { exact h₂ _ h₃ },
    { rw h₃, exact h₁.fst },
    { injection mem_unique h₁ (al _ h₃) } },
  cases e : (p m).get pm,
  { suffices,
    exact IH _ ⟨rfl, this⟩ (λ n h, this _ (le_of_lt_succ h)),
    intros n h, cases h.lt_or_eq_dec with h h,
    { exact al _ h },
    { rw h, exact ⟨_, e⟩ } },
  { exact ⟨m, ⟨_, e⟩, al⟩ }
end

end rfind

def rfind (p : ℕ →. bool) : part ℕ :=
⟨_, λ h, (rfind_x p h).1⟩

theorem rfind_spec {p : ℕ →. bool} {n : ℕ} (h : n ∈ rfind p) : tt ∈ p n :=
h.snd ▸ (rfind_x p h.fst).2.1

theorem rfind_min {p : ℕ →. bool} {n : ℕ} (h : n ∈ rfind p) :
  ∀ {m : ℕ}, m < n → ff ∈ p m :=
h.snd ▸ (rfind_x p h.fst).2.2

@[simp] theorem rfind_dom {p : ℕ →. bool} :
  (rfind p).dom ↔ ∃ n, tt ∈ p n ∧ ∀ {m : ℕ}, m < n → (p m).dom :=
iff.rfl

theorem rfind_dom' {p : ℕ →. bool} :
  (rfind p).dom ↔ ∃ n, tt ∈ p n ∧ ∀ {m : ℕ}, m ≤ n → (p m).dom :=
exists_congr $ λ n, and_congr_right $ λ pn,
⟨λ H m h, (decidable.eq_or_lt_of_le h).elim (λ e, e.symm ▸ pn.fst) (H _),
 λ H m h, H (le_of_lt h)⟩

@[simp] theorem mem_rfind {p : ℕ →. bool} {n : ℕ} :
  n ∈ rfind p ↔ tt ∈ p n ∧ ∀ {m : ℕ}, m < n → ff ∈ p m :=
⟨λ h, ⟨rfind_spec h, @rfind_min _ _ h⟩,
  λ ⟨h₁, h₂⟩, let ⟨m, hm⟩ := dom_iff_mem.1 $
    (@rfind_dom p).2 ⟨_, h₁, λ m mn, (h₂ mn).fst⟩ in
  begin
    rcases lt_trichotomy m n with h|h|h,
    { injection mem_unique (h₂ h) (rfind_spec hm) },
    { rwa ← h },
    { injection mem_unique h₁ (rfind_min hm h) },
  end⟩

theorem rfind_min' {p : ℕ → bool} {m : ℕ} (pm : p m) :
  ∃ n ∈ rfind p, n ≤ m :=
have tt ∈ (p : ℕ →. bool) m, from ⟨trivial, pm⟩,
let ⟨n, hn⟩ := dom_iff_mem.1 $
  (@rfind_dom p).2 ⟨m, this, λ k h, ⟨⟩⟩ in
⟨n, hn, not_lt.1 $ λ h,
  by injection mem_unique this (rfind_min hn h)⟩

theorem rfind_zero_none
  (p : ℕ →. bool) (p0 : p 0 = none) : rfind p = none :=
eq_none_iff.2 $ λ a h,
let ⟨n, h₁, h₂⟩ := rfind_dom'.1 h.fst in
(p0 ▸ h₂ (zero_le _) : (@part.none bool).dom)

def rfind_opt {α} (f : ℕ → option α) : part α :=
(rfind (λ n, (f n).is_some)).bind (λ n, f n)

theorem rfind_opt_spec {α} {f : ℕ → option α} {a}
 (h : a ∈ rfind_opt f) : ∃ n, a ∈ f n :=
let ⟨n, h₁, h₂⟩ := mem_bind_iff.1 h in ⟨n, mem_coe.1 h₂⟩

theorem rfind_opt_dom {α} {f : ℕ → option α} :
  (rfind_opt f).dom ↔ ∃ n a, a ∈ f n :=
⟨λ h, (rfind_opt_spec ⟨h, rfl⟩).imp (λ n h, ⟨_, h⟩),
 λ h, begin
  have h' : ∃ n, (f n).is_some :=
    h.imp (λ n, option.is_some_iff_exists.2),
  have s := nat.find_spec h',
  have fd : (rfind (λ n, (f n).is_some)).dom :=
    ⟨nat.find h', by simpa using s.symm, λ _ _, trivial⟩,
  refine ⟨fd, _⟩,
  have := rfind_spec (get_mem fd),
  simp at this ⊢,
  cases option.is_some_iff_exists.1 this.symm with a e,
  rw e, trivial
end⟩

theorem rfind_opt_mono {α} {f : ℕ → option α}
  (H : ∀ {a m n}, m ≤ n → a ∈ f m → a ∈ f n)
  {a} : a ∈ rfind_opt f ↔ ∃ n, a ∈ f n :=
⟨rfind_opt_spec, λ ⟨n, h⟩, begin
  have h' := rfind_opt_dom.2 ⟨_, _, h⟩,
  cases rfind_opt_spec ⟨h', rfl⟩ with k hk,
  have := (H (le_max_left _ _) h).symm.trans
          (H (le_max_right _ _) hk),
  simp at this, simp [this, get_mem],
end⟩

end nat
