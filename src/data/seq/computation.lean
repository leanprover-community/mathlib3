/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.stream.init
import tactic.basic

/-!
# Unbounded computations


-/

open function
universes u v w

/-
coinductive computation (α : Type u) : Type u
| return : α → computation α
| think : computation α → computation α
-/

/-- `computation α` is the type of unbounded computations returning `α`.
  An element of `computation α` is an infinite sequence of `option α` such
  that if `f n = some a` for some `n` then it is constantly `some a` after that. -/
structure computation (α : Type u) extends stream (option α) : Type u :=
(nth_succ_eq_some : ∀ {n a}, nth n = some a → nth (n + 1) = some a)

namespace computation
variables {α : Type u} {β : Type v} {γ : Type w}

/-- `run_for c n` evaluates `c` for `n` steps and returns the result, or `none`
  if it did not terminate after `n` steps. -/
def run_for (c : computation α) (n : ℕ) : option α := c.nth n

@[simp] lemma nth_to_stream (c : computation α) : c.to_stream.nth = c.run_for := rfl

/-- See Note [custom simps projection]. -/
def simps.run_for (c : computation α) : ℕ → option α := c.run_for

initialize_simps_projections computation (to_stream_nth → run_for as_prefix)

theorem le_stable (s : computation α) {a m n} (h : m ≤ n) (hm : s.run_for m = some a) :
  s.run_for n = some a :=
nat.le_induction hm (λ _ _ h, s.2 h) n h

lemma to_stream_injective : injective (@to_stream α) :=
by { rintro ⟨s, _⟩ ⟨s', _⟩ (rfl : s = s'), refl }

@[simp] lemma to_stream_inj {c₁ c₂ : computation α} : c₁.to_stream = c₂.to_stream ↔ c₁ = c₂ :=
to_stream_injective.eq_iff

@[ext] lemma ext {c₁ c₂ : computation α} (h : ∀ n, c₁.run_for n = c₂.run_for n) : c₁ = c₂ :=
to_stream_injective $ stream.ext h

/-! ### Constructors -/

/-- `computation.return a` is the computation that immediately terminates with result `a`. -/
@[simps] def return (a : α) : computation α := ⟨pure (some a), λ n a', id⟩

instance : has_coe_t α (computation α) := ⟨return⟩ -- note [use has_coe_t]

/-- `computation.think c` is the computation that delays for one "tick" and then performs
computation `c`. -/
@[simps to_stream] def think (c : computation α) : computation α :=
⟨none :: c.1, λ n a h, by {cases n with n, contradiction, exact c.2 h}⟩

/-- `computation.thinkN c n` is the computation that delays for `n` ticks and then performs
  computation `c`. -/
def thinkN (c : computation α) : ℕ → computation α
| 0 := c
| (n+1) := think (thinkN n)

/-- `computation.head c` is the first step of computation, either `some a` if `c = return a`
  or `none` if `c = think c'`. -/
def head (c : computation α) : option α := c.1.head

@[simp] lemma head_return (a : α) : head (return a) = some a := rfl

@[simp] lemma head_eq_some {a : α} {c : computation α} : c.head = some a ↔ c = return a :=
⟨λ h, by { ext1 n, rw [run_for_return, c.le_stable (zero_le _) h] }, λ h, h.symm ▸ rfl⟩

@[simp] lemma head_think (c : computation α) : c.think.head = none := rfl

/-- `tail c` is the remainder of computation, either `c` if `c = return a`
  or `c'` if `c = think c'`. -/
@[simps] def tail (c : computation α) : computation α := ⟨c.1.tail, λ n a h, c.2 h⟩

lemma ext_head_tail {c₁ c₂ : computation α} (h₁ : c₁.head = c₂.head) (h₂ : c₁.tail = c₂.tail) :
  c₁ = c₂ :=
to_stream_injective $ stream.ext_head_tail h₁ $ by convert congr_arg to_stream h₂

@[simp] lemma tail_think (c : computation α) : c.think.tail = c := ext $ λ _, rfl

/-- `empty α` is the computation that never returns, an infinite sequence of
  `think`s. -/
@[simps] def empty (α) : computation α := ⟨pure none, λ n a', id⟩

instance : inhabited (computation α) := ⟨empty _⟩

/-- `destruct c` is the destructor for `computation α` as a coinductive type.
  It returns `inl a` if `c = return a` and `inr c'` if `c = think c'`. -/
def destruct : computation α ≃ α ⊕ computation α :=
{ to_fun := λ c, c.head.elim (sum.inr (tail c)) sum.inl,
  inv_fun := λ c, c.elim return think,
  left_inv := λ c,
    begin
      cases h : c.head,
      { have : c.tail.think = c, from ext_head_tail h.symm rfl,
        simp * },
      { simp * at * }
    end,
  right_inv := λ c, by cases c; simp }

/-- `run c` is an unsound meta function that runs `c` to completion, possibly
  resulting in an infinite loop in the VM. -/
meta def run : computation α → α | c :=
match destruct c with
| sum.inl a := a
| sum.inr ca := run ca
end

@[simp] theorem destruct_return (a : α) : destruct (return a) = sum.inl a := rfl
@[simp] theorem destruct_symm_inl (a : α) : destruct.symm (sum.inl a) = return a := rfl
@[simp] theorem destruct_symm_inr (c : computation α) : destruct.symm (sum.inr c) = think c := rfl
@[simp] theorem destruct_empty : destruct (empty α) = sum.inr (empty α) := rfl

@[simp] theorem destruct_eq_inl {c : computation α} {a : α} :
  destruct c = sum.inl a ↔ c = return a :=
destruct.eq_symm_apply.symm

@[simp] theorem destruct_eq_inr {c : computation α} {c'} :
  destruct c = sum.inr c' ↔ c = think c' :=
destruct.eq_symm_apply.symm

@[simp] theorem destruct_think (c : computation α) : destruct (think c) = sum.inr c :=
destruct_eq_inr.2 rfl

@[simp] theorem head_empty : head (empty α) = none := rfl
@[simp] theorem tail_return (a : α) : tail (return a) = return a := rfl
@[simp] theorem tail_empty : tail (empty α) = empty α := rfl

@[simp] theorem think_empty : think (empty α) = empty α :=
(destruct_eq_inr.1 destruct_empty).symm

/-- Recursion principle for computations, compare with `list.rec_on`. -/
def cases_return_think {C : computation α → Sort v} (c : computation α)
  (h1 : ∀ a, C (return a)) (h2 : ∀ c, C (think c)) : C c :=
by { rw [← destruct.symm_apply_apply c], exact sum.rec_on (destruct c) h1 h2 }

/-- `computation.corec f b` is the corecursor for `computation α` as a coinductive type. If
  `f b = sum.inl a` then `computation.corec f b = computation.return a`, and if `f b = sum.inr b'`
  then `computation.corec f b = computation.think (computation.corec f b')`. -/
@[simps to_stream] def corec (f : β → α ⊕ β) (b : β) : computation α :=
begin
  refine ⟨stream.corec sum.get_left (sum.elim sum.inl f) (f b), λ n a' h, _⟩,
  rw [stream.corec, stream.nth_map, sum.get_left_eq_some_iff] at h ⊢,
  rw [stream.nth_iterate_succ', h, sum.elim_inl]
end

@[simp] lemma head_corec (f : β → α ⊕ β) (b : β) : (corec f b).head = (f b).get_left := rfl

lemma corec_eq (f : β → α ⊕ β) (b : β) :
  corec f b = (f b).elim return (think ∘ corec f) :=
begin
  apply to_stream_injective,
  cases h : f b; simp only [h, sum.elim_inl, sum.elim_inr, corec_to_stream],
  { exact stream.corec_fixed _ rfl },
  { exact stream.corec_eq _ _ _ }
end

@[simp] lemma destruct_corec (f : β → α ⊕ β) (b : β) :
  destruct (corec f b) = sum.map id (corec f) (f b) :=
begin
  rw [corec_eq, ← destruct.eq_symm_apply],
  simp [destruct, equiv.symm, sum.elim_map]
end

@[simp] lemma corec_eq_return {f : β → α ⊕ β} {b : β} {a : α} :
  corec f b = return a ↔ f b = sum.inl a :=
by { rw [← destruct_eq_inl, destruct_corec], cases h : f b; simp }

section bisim
variable (R : computation α → computation α → Prop)

local infix ` ~ `:50 := R

@[simp] def bisim_o : α ⊕ computation α → α ⊕ computation α → Prop
| (sum.inl a) (sum.inl a') := a = a'
| (sum.inr s) (sum.inr s') := R s s'
| _           _            := false

def is_bisimulation := ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → bisim_o R (destruct s₁) (destruct s₂)

-- If two computations are bisimilar, then they are equal
theorem eq_of_bisim (bisim : is_bisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂ :=
begin
  apply to_stream_injective,
  refine stream.eq_of_bisim (λ x y, ∃ s s' : computation α, s.1 = x ∧ s'.1 = y ∧ R s s') _
    ⟨s₁, s₂, rfl, rfl, r⟩,
  rintros t₁ t₂ ⟨s, s', rfl, rfl, r⟩,
  suffices : head s = head s' ∧ R (tail s) (tail s'),
    from this.imp_right (λ r, ⟨tail s, tail s', by cases s; refl, by cases s'; refl, r⟩),
  have := bisim r, revert r this,
  apply cases_return_think s _ _; intros;
    apply cases_return_think s' _ _; intros; intros r this,
  { constructor, dsimp at this, rw this, assumption },
  { rw [destruct_return, destruct_think] at this,
    exact false.elim this },
  { rw [destruct_return, destruct_think] at this,
    exact false.elim this },
  { simp at this, simp [*] },
end

end bisim

-- It's more of a stretch to use ∈ for this relation, but it
-- asserts that the computation limits to the given value.
instance : has_mem α (computation α) := ⟨λ a s, some a ∈ s.1⟩

lemma mem_def {a : α} {c : computation α} : a ∈ c ↔ ∃ n, some a = c.run_for n := iff.rfl

theorem mem_unique {s : computation α} {a b : α} : a ∈ s → b ∈ s → a = b
| ⟨m, ha⟩ ⟨n, hb⟩ := option.some.inj $
  (le_stable s (le_max_left m n) ha.symm).symm.trans (le_stable s (le_max_right m n) hb.symm)

theorem mem.left_unique : relator.left_unique ((∈) : α → computation α → Prop) :=
λ a s b, mem_unique

theorem self_mem_return (a : α) : a ∈ return a := ⟨0, rfl⟩

@[simp] theorem mem_return {a b : α} : a ∈ return b ↔ a = b :=
⟨λ h, mem_unique h (self_mem_return b), λ h, h ▸ self_mem_return a⟩

@[simp] theorem mem_think {c : computation α} {a : α} : a ∈ think c ↔ a ∈ c :=
⟨λ ⟨n, hn⟩, ⟨n, (le_stable (think c) n.le_succ hn.symm).symm⟩, λ ⟨n, hn⟩, ⟨n + 1, hn⟩⟩

/-- `terminates s` asserts that the computation `s` eventually terminates with some value. -/
@[mk_iff] class terminates (s : computation α) : Prop := (term : ∃ a, a ∈ s)

theorem terminates_of_mem {s : computation α} {a : α} (h : a ∈ s) : terminates s :=
⟨⟨a, h⟩⟩

theorem terminates_def (s : computation α) : terminates s ↔ ∃ n, (s.run_for n).is_some :=
by simp only [option.is_some_iff_exists, terminates_iff, mem_def, eq_comm, @exists_swap ℕ]

instance return_terminates (a : α) : terminates (return a) := terminates_of_mem (self_mem_return a)

theorem think_terminates {c : computation α} : terminates (think c) ↔ terminates c :=
by simp only [terminates_iff, mem_think]

instance think.terminates (s : computation α) [terminates s] : terminates (think s) :=
think_terminates.mpr ‹_›

@[simp] theorem not_mem_empty (a : α) : a ∉ empty α := λ ⟨n, h⟩, option.some_ne_none _ h

@[simp] theorem not_terminates_empty : ¬ terminates (empty α) := λ ⟨⟨a, h⟩⟩, not_mem_empty a h

@[simp] theorem not_terminates {c} : ¬terminates c ↔ c = empty α :=
begin
  refine ⟨λ h, ext $ λ n, _, λ h, h.symm ▸ not_terminates_empty⟩,
  contrapose! h,
  exact c.terminates_def.2 ⟨n, option.not_is_some_iff_eq_none.not_right.2 h⟩
end

@[simp] theorem mem_thinkN {s : computation α} {a} : ∀ n, a ∈ thinkN s n ↔ a ∈ s
| 0 := iff.rfl
| (n+1) := iff.trans mem_think (mem_thinkN n)

@[simp] theorem thinkN_terminates {c : computation α} {n : ℕ} :
  (thinkN c n).terminates ↔ c.terminates :=
by simp only [terminates_iff, mem_thinkN]

instance thinkN.terminates (s : computation α) [terminates s] (n) : terminates (thinkN s n) :=
thinkN_terminates.2 ‹_›

/-- `computation.promises s a`, or `s ~> a`, asserts that although the computation `s`
  may not terminate, if it does, then the result is `a`. -/
def promises (s : computation α) (a : α) : Prop := ∀ ⦃a'⦄, a' ∈ s → a = a'

infix ` ~> `:50 := promises

theorem mem_promises {s : computation α} {a : α} : a ∈ s → s ~> a :=
λ h a', mem_unique h

theorem empty_promises (a : α) : empty α ~> a :=
λ a' h, absurd h (not_mem_empty _)

section get
variables (s : computation α) [h : terminates s]
include s h

/-- `length s` gets the number of steps of a terminating computation -/
def length : ℕ := nat.find (s.terminates_def.1 h)

/-- `get s` returns the result of a terminating computation -/
def get : α := option.get (nat.find_spec $ (terminates_def _).1 h)

@[simp] theorem run_for_length : s.run_for s.length = some s.get := option.eq_some_of_is_some _

theorem get_mem : get s ∈ s := ⟨length s, s.run_for_length.symm⟩

theorem get_eq_of_mem {a} : a ∈ s → get s = a := mem_unique (get_mem _)

theorem mem_of_get_eq {a} : get s = a → a ∈ s := λ h, h ▸ get_mem _

@[simp] theorem get_think : get (think s) = get s :=
get_eq_of_mem _ $ mem_think.2 s.get_mem

@[simp] theorem get_thinkN (n) : get (thinkN s n) = get s :=
get_eq_of_mem _ $ (mem_thinkN _).2 (get_mem _)

theorem get_promises : s ~> get s := λ a, get_eq_of_mem _

theorem promises.mem {a} (p : s ~> a) : a ∈ s :=
by { casesI h, cases h with a' h, rw p h, exact h }

theorem get_eq_of_promises {a} : s ~> a → get s = a := get_eq_of_mem _ ∘ promises.mem _

end get

/-- `results s a n` completely characterizes a terminating computation:
  it asserts that `s` terminates after exactly `n` steps, with result `a`. -/
def results (s : computation α) (a : α) (n : ℕ) :=
∃ (h : a ∈ s), @length _ s (terminates_of_mem h) = n

theorem results_get_length (s : computation α) [terminates s] :
  results s (get s) (length s) :=
⟨get_mem _, rfl⟩

theorem results_length_of_mem (s : computation α) {a} (h : a ∈ s) :
  results s a (@length _ s $ terminates_of_mem h) :=
by { generalize_proofs, resetI, rw [← get_eq_of_mem _ h], apply results_get_length }

protected theorem results.mem {s : computation α} {a n} : results s a n → a ∈ s
| ⟨m, _⟩ := m

protected theorem results.terminates {s : computation α} {a n} (h : results s a n) : terminates s :=
terminates_of_mem h.mem

protected theorem results.get_eq {s : computation α} {a n} (h : results s a n) [terminates s] :
  get s = a :=
get_eq_of_mem _ h.mem

theorem results.length_eq {s : computation α} {a n} [T : terminates s] :
  results s a n → length s = n
| ⟨_, h⟩ := h

theorem results.run_for_eq {c : computation α} {a n} (h : results c a n) : c.run_for n = some a :=
by { haveI := h.terminates, rw [← h.length_eq, run_for_length, h.get_eq] }

theorem results.val_unique {s : computation α} {a b m n} (h1 : results s a m) (h2 : results s b n) :
  a = b :=
mem_unique h1.mem h2.mem

theorem results.length_unique {s : computation α} {a b m n}
  (h1 : results s a m) (h2 : results s b n) : m = n :=
by haveI := h1.terminates; haveI := h2.terminates; rw [←h1.length_eq, h2.length_eq]

theorem exists_results_of_mem {s : computation α} {a} (h : a ∈ s) : ∃ n, results s a n :=
by haveI := terminates_of_mem h; exact ⟨_, results_length_of_mem s h⟩

@[simp] theorem get_return (a : α) : get (return a) = a := get_eq_of_mem _ ⟨0, rfl⟩

@[simp] theorem length_return (a : α) : length (return a) = 0 :=
(nat.find_eq_zero _).2 option.is_some_some

theorem results_return (a : α) : results (return a) a 0 := ⟨_, length_return _⟩

@[simp] theorem length_think (s : computation α) [terminates s] :
  length (think s) = length s + 1 :=
begin
  apply le_antisymm,
  { exact nat.find_min' _ (nat.find_spec ((terminates_def _).1 ‹_›)) },
  { have : (option.is_some ((think s).run_for (length (think s))) : Prop) :=
      nat.find_spec ((terminates_def _).1 (think.terminates _)),
    cases length (think s) with n,
    { contradiction },
    { apply nat.succ_le_succ, apply nat.find_min', apply this } }
end

theorem results.think {s : computation α} {a n} (h : results s a n) :
  results (think s) a (n + 1) :=
by haveI := h.terminates; exact ⟨mem_think.2 h.mem, by rw [length_think, h.length_eq]⟩

theorem of_results_think {s : computation α} {a n}
  (h : results (think s) a n) : ∃ m, results s a m ∧ n = m + 1 :=
begin
  haveI := think_terminates.1 h.terminates,
  have := results_length_of_mem _ (mem_think.1 h.mem),
  exact ⟨_, this, h.length_unique this.think⟩,
end

@[simp] theorem results_think {s : computation α} {a n} :
  results (think s) a (n + 1) ↔ results s a n :=
⟨λ h, let ⟨n', r, e⟩ := of_results_think h in by injection e with h'; rwa h', results.think⟩

theorem results.thinkN {s : computation α} {a m} :
  results s a m → ∀ n, results (thinkN s n) a (m + n)
| h 0       := h
| h (n + 1) := (results.thinkN h n).think

theorem results_thinkN_return (a : α) (n) : results (thinkN (return a) n) a n :=
by simpa only [nat.zero_add] using (results_return a).thinkN n

@[simp] theorem length_thinkN (s : computation α) [h : terminates s] (n) :
  length (thinkN s n) = length s + n :=
((results_get_length _).thinkN _).length_eq

theorem results.eq_thinkN {s : computation α} {a n} (h : results s a n) :
  s = thinkN (return a) n :=
begin
  induction n with n IH generalizing s,
  { rw [thinkN, ← head_eq_some],
    exact h.run_for_eq },
  { induction s using computation.cases_return_think,
    { exact absurd (h.length_unique $ results_return _) n.succ_ne_zero },
    { rw [thinkN, IH (results_think.1 h)] } },
end

theorem eq_thinkN (s : computation α) [h : terminates s] :
  s = thinkN (return (get s)) (length s) :=
s.results_get_length.eq_thinkN

def rec_on_mem {C : computation α → Sort v} {a s} (M : a ∈ s)
  (h1 : C (return a)) (h2 : ∀ s, C s → C (think s)) : C s :=
begin
  haveI := terminates_of_mem M,
  rw [(s.results_length_of_mem M).eq_thinkN],
  induction s.length with n IH, exacts [h1, h2 _ IH]
end

def rec_on_terminates {C : computation α → Sort v} (s) [terminates s]
  (h1 : ∀ a, C (return a)) (h2 : ∀ s, C s → C (think s)) : C s :=
rec_on_mem (get_mem _) (h1 _) h2

/-- Map a function on the result of a computation. -/
@[simps] def map (f : α → β) (c : computation α) : computation β :=
⟨c.1.map (option.map f), λ n b h, let ⟨a, ha, hb⟩ := option.map_eq_some'.1 h in
  by rw [stream.nth_map, c.2 ha, option.map_some', hb]⟩

/-- One step of computation of `computation.bind`. -/
def bind.F (f : α → computation β) :
  computation α ⊕ computation β → β ⊕ computation α ⊕ computation β
| (sum.inl ca) :=
  match destruct ca with
  | sum.inl a := (destruct (f a)).map id sum.inr
  | sum.inr ca' := sum.inr $ sum.inl ca'
  end
| (sum.inr cb) := (destruct cb).map id sum.inr

/-- Compose two computations into a monadic `bind` operation. -/
def bind (c : computation α) (f : α → computation β) : computation β :=
corec (bind.F f) (sum.inl c)

instance : has_bind computation := ⟨@bind⟩

@[simp] theorem has_bind_eq_bind {β} (c : computation α) (f : α → computation β) :
  c >>= f = bind c f := rfl

/-- Flatten a computation of computations into a single computation. -/
def join (c : computation (computation α)) : computation α := c >>= id

@[simp] theorem map_return (f : α → β) (a) : map f (return a) = return (f a) := rfl

@[simp] theorem map_think (f : α → β) (s) : map f (think s) = think (map f s) :=
to_stream_injective $ stream.map_cons _ _ _

@[simp] theorem destruct_map (f : α → β) (s) :
  destruct (map f s) = sum.map f id ((destruct s).map id (map f)) :=
by apply s.cases_return_think; intro; simp

@[simp] theorem map_id (s : computation α) : map id s = s :=
ext $ λ n, by simp

theorem map_comp (f : α → β) (g : β → γ) (s : computation α) : map (g ∘ f) s = map g (map f s) :=
by { ext n, simp }

@[simp] theorem return_bind (a) (f : α → computation β) :
  bind (return a) f = f a :=
begin
  apply eq_of_bisim
    (λ c₁ c₂, c₁ = bind (return a) f ∧ c₂ = f a ∨ c₁ = corec (bind.F f) (sum.inr c₂)),
  { rintros c₁ c₂ (⟨rfl, rfl⟩ | rfl),
    { simp only [bind, bind.F, destruct_corec, destruct_return, sum.map_map, comp.right_id],
      cases destruct (f a); simp },
    { simp only [bind.F, destruct_corec, sum.map_map, comp.right_id],
      cases destruct c₂; simp } },
  { simp }
end

@[simp] theorem think_bind (c) (f : α → computation β) :
  bind (think c) f = think (bind c f) :=
destruct_eq_inr.1 $ by simp [bind, bind.F]

@[simp] theorem thinkN_bind (c) (f : α → computation β) :
  ∀ n, bind (thinkN c n) f = thinkN (bind c f) n
| 0 := rfl
| (n + 1) := by rw [thinkN, thinkN, think_bind, thinkN_bind]

@[simp] theorem bind_return_comp (f : α → β) (s) : bind s (return ∘ f) = map f s :=
begin
  apply eq_of_bisim (λ c₁ c₂, c₁ = c₂ ∨ ∃ s, c₁ = bind s (return ∘ f) ∧ c₂ = map f s),
  { rintros c₁ c₂ (rfl | ⟨s, rfl, rfl⟩),
    { cases destruct c₁; simp },
    { apply cases_return_think s,
      { simp },
      exact λ s, or.inr ⟨s, rfl, rfl⟩ } },
  { exact or.inr ⟨s, rfl, rfl⟩ }
end

@[simp] theorem bind_return (s : computation α) : bind s return = s :=
by { rw bind_return_comp, apply map_id }

@[simp] theorem bind_assoc (s : computation α) (f : α → computation β) (g : β → computation γ) :
  bind (bind s f) g = bind s (λ (x : α), bind (f x) g) :=
begin
  set r := λ c₁ c₂ : computation γ, c₁ = c₂ ∨
    ∃ s, c₁ = bind (bind s f) g ∧ c₂ = bind s (λ (x : α), bind (f x) g),
  have hr : ∀ c, bisim_o r c c := λ c, sum.rec_on c (λ _, rfl) (λ _, or.inl rfl),
  refine eq_of_bisim r _ (or.inr ⟨s, rfl, rfl⟩),
  rintro c₁ c₂ (rfl | ⟨s, rfl, rfl⟩),
  { apply hr },
  { induction s using computation.cases_return_think with a s,
    { simpa only [return_bind] using hr _ },
    { simp only [think_bind, destruct_think, bisim_o],
      exact or.inr ⟨_, rfl, rfl⟩ } }
end

theorem results.bind {s : computation α} {f : α → computation β} {a b m n}
  (h1 : results s a m) (h2 : results (f a) b n) : results (bind s f) b (n + m) :=
begin
  rcases h1.eq_thinkN with rfl,
  rw [thinkN_bind, return_bind],
  exact h2.thinkN _
end

theorem mem_bind_of_mem {s : computation α} {f : α → computation β} {a b}
  (h1 : a ∈ s) (h2 : b ∈ f a) : b ∈ bind s f :=
let ⟨m, h1⟩ := exists_results_of_mem h1,
    ⟨n, h2⟩ := exists_results_of_mem h2 in (h1.bind h2).mem

instance terminates_bind (s : computation α) (f : α → computation β)
  [terminates s] [terminates (f (get s))] :
  terminates (bind s f) :=
terminates_of_mem (mem_bind_of_mem (get_mem s) (get_mem (f (get s))))

@[simp] theorem get_bind (s : computation α) (f : α → computation β)
  [terminates s] [terminates (f (get s))] :
  get (bind s f) = get (f (get s)) :=
get_eq_of_mem _ (mem_bind_of_mem (get_mem s) (get_mem (f (get s))))

@[simp] theorem length_bind (s : computation α) (f : α → computation β)
  [terminates s] [terminates (f (get s))] :
  length (bind s f) = length (f (get s)) + length s :=
(results_get_length _).length_unique $ (results_get_length _).bind (results_get_length _)

theorem results_bind {s : computation α} {f : α → computation β} {b k} :
  results (bind s f) b k ↔
    ∃ a m n, results s a m ∧ results (f a) b n ∧ k = n + m :=
begin
  refine ⟨λ h, _, _⟩,
  { induction k with n IH generalizing s;
      induction s using computation.cases_return_think with a s,
    { rw [return_bind] at h,
      exact ⟨a, 0, 0, results_return _, h, rfl⟩ },
    { exact absurd (congr_arg head h.eq_thinkN) (option.some_ne_none _).symm },
    { rw [return_bind] at h,
      exact ⟨a, _, n + 1, results_return _, h, rfl⟩ },
    { rw [think_bind, results_think] at h,
      rcases IH h with ⟨a, m, n, hm, hn, rfl⟩,
      exact ⟨a, m + 1, n, hm.think, hn, rfl⟩ } },
  { rintro ⟨a, m, n, hm, hn, rfl⟩,
    exact hm.bind hn }
end

theorem mem_bind {s : computation α} {f : α → computation β} {b} :
  b ∈ bind s f ↔ ∃ a ∈ s, b ∈ f a :=
⟨λ h, let ⟨k, h⟩ := exists_results_of_mem h,
    ⟨a, m, n, h1, h2, e⟩ := results_bind.1 h in ⟨a, h1.mem, h2.mem⟩,
  λ ⟨a, ha, hb⟩, mem_bind_of_mem ha hb⟩

theorem promises.bind {s : computation α} {f : α → computation β} {a b}
  (h1 : s ~> a) (h2 : f a ~> b) : bind s f ~> b :=
λ b' bB, let ⟨a', a's, ba'⟩ := mem_bind.1 bB in @h2 b' ((h1 a's).symm ▸ ba')

instance : monad computation :=
{ map  := @map,
  pure := @return,
  bind := @bind }

instance : is_lawful_monad computation :=
{ id_map := @map_id,
  bind_pure_comp_eq_map := @bind_return_comp,
  pure_bind := @return_bind,
  bind_assoc := @bind_assoc }

@[simp] theorem has_map_eq_map {β} (f : α → β) (c : computation α) : f <$> c = map f c := rfl

@[simp] theorem return_def (a) : (_root_.return a : computation α) = return a := rfl

theorem mem_map {f : α → β} {b : β} {s : computation α} :
  b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b :=
by simp only [← bind_return_comp, mem_bind, exists_prop, comp_app, mem_return, eq_comm]

theorem mem_map_of_mem (f : α → β) {a} {s : computation α} (ha : a ∈ s) : f a ∈ map f s :=
mem_map.2 ⟨_, ha, rfl⟩

instance terminates_map (f : α → β) (s : computation α) [terminates s] : terminates (map f s) :=
bind_return_comp f s ▸ infer_instance

theorem terminates_map_iff (f : α → β) (s : computation α) :
  terminates (map f s) ↔ terminates s :=
⟨λ ⟨⟨a, h⟩⟩, let ⟨b, h1, _⟩ := mem_map.1 h in ⟨⟨_, h1⟩⟩, @computation.terminates_map _ _ _ _⟩


/-- `c₁ <|> c₂` calculates `c₁` and `c₂` simultaneously, returning the first one that gives a
result. If both computations terminate at the same time, the result of the first one is used. -/
def orelse (c₁ c₂ : computation α) : computation α :=
@computation.corec α (computation α × computation α)
  (λ ⟨c₁, c₂⟩, match destruct c₁ with
  | sum.inl a := sum.inl a
  | sum.inr c₁' := match destruct c₂ with
    | sum.inl a := sum.inl a
    | sum.inr c₂' := sum.inr (c₁', c₂')
    end
  end) (c₁, c₂)

instance : alternative computation :=
{ orelse := @orelse, failure := @empty, ..computation.monad }

@[simp] theorem return_orelse (a : α) (c₂ : computation α) :
  (return a <|> c₂) = return a :=
head_eq_some.1 rfl

@[simp] theorem orelse_return (c₁ : computation α) (a : α) :
  (think c₁ <|> return a) = return a :=
head_eq_some.1 rfl

@[simp] theorem orelse_think (c₁ c₂ : computation α) :
  (think c₁ <|> think c₂) = think (c₁ <|> c₂) :=
destruct_eq_inr.1 $ by unfold has_orelse.orelse; simp [orelse]

@[simp] theorem empty_orelse (c) : (empty α <|> c) = c :=
begin
  apply eq_of_bisim (λ c₁ c₂, (empty α <|> c₂) = c₁) _ rfl,
  rintros s' s rfl,
  induction s using computation.cases_return_think,
  { rw [← think_empty, orelse_return, destruct_return], exact rfl },
  { rw [← think_empty, orelse_think, destruct_think, destruct_think, bisim_o, think_empty] }
end

@[simp] theorem orelse_empty (c : computation α) : (c <|> empty α) = c :=
begin
  apply eq_of_bisim (λ c₁ c₂, (c₂ <|> empty α) = c₁) _ rfl,
  rintros s' s rfl,
  induction s using computation.cases_return_think,
  { simp },
  { rw [← think_empty, orelse_think], simp }
end

/-- `c₁ ~ c₂` asserts that `c₁` and `c₂` either both terminate with the same result,
  or both loop forever. -/
def equiv (c₁ c₂ : computation α) : Prop := ∀ a, a ∈ c₁ ↔ a ∈ c₂

infix ` ~ `:50 := equiv

@[refl] theorem equiv.refl (s : computation α) : s ~ s := λ _, iff.rfl

@[symm] theorem equiv.symm {s t : computation α} : s ~ t → t ~ s :=
λ h a, (h a).symm

@[trans] theorem equiv.trans {s t u : computation α} : s ~ t → t ~ u → s ~ u :=
λ h1 h2 a, (h1 a).trans (h2 a)

theorem equiv.equivalence : equivalence (@equiv α) :=
⟨@equiv.refl _, @equiv.symm _, @equiv.trans _⟩

theorem equiv_of_mem {s t : computation α} {a} (h1 : a ∈ s) (h2 : a ∈ t) : s ~ t :=
λ a', ⟨λ ma, by rw mem_unique ma h1; exact h2,
      λ ma, by rw mem_unique ma h2; exact h1⟩

theorem terminates_congr {c₁ c₂ : computation α}
  (h : c₁ ~ c₂) : terminates c₁ ↔ terminates c₂ :=
by simp only [terminates_iff, exists_congr h]

theorem promises_congr {c₁ c₂ : computation α}
  (h : c₁ ~ c₂) (a) : c₁ ~> a ↔ c₂ ~> a :=
forall_congr (λ a', imp_congr (h a') iff.rfl)

theorem get_equiv {c₁ c₂ : computation α} (h : c₁ ~ c₂)
  [terminates c₁] [terminates c₂] : get c₁ = get c₂ :=
get_eq_of_mem _ $ (h _).2 $ get_mem _

theorem think_equiv (s : computation α) : think s ~ s := λ a, mem_think

theorem thinkN_equiv (s : computation α) (n) : thinkN s n ~ s := λ a, mem_thinkN _

theorem bind_congr {s1 s2 : computation α} {f1 f2 : α → computation β}
  (h1 : s1 ~ s2) (h2 : ∀ a, f1 a ~ f2 a) : bind s1 f1 ~ bind s2 f2 :=
λ a, by simp only [mem_bind, exists_prop, h1 _, h2 _ _]

theorem equiv_return_of_mem {s : computation α} {a} (h : a ∈ s) : s ~ return a :=
equiv_of_mem h (self_mem_return _)

/-- `lift_rel R ca cb` is a generalization of `equiv` to relations other than
  equality. It asserts that if `ca` terminates with `a`, then `cb` terminates with
  some `b` such that `R a b`, and if `cb` terminates with `b` then `ca` terminates
  with some `a` such that `R a b`. -/
def lift_rel (R : α → β → Prop) (ca : computation α) (cb : computation β) : Prop :=
(∀ {a}, a ∈ ca → ∃ {b}, b ∈ cb ∧ R a b) ∧
 ∀ {b}, b ∈ cb → ∃ {a}, a ∈ ca ∧ R a b

theorem lift_rel.swap (R : α → β → Prop) (ca : computation α) (cb : computation β) :
  lift_rel (swap R) cb ca ↔ lift_rel R ca cb :=
and_comm _ _

theorem lift_eq_iff_equiv (c₁ c₂ : computation α) : lift_rel (=) c₁ c₂ ↔ c₁ ~ c₂ :=
⟨λ ⟨h1, h2⟩ a,
  ⟨λ a1, let ⟨b, b2, ab⟩ := h1 a1 in by rwa ab,
   λ a2, let ⟨b, b1, ab⟩ := h2 a2 in by rwa ←ab⟩,
λ e, ⟨λ a a1, ⟨a, (e _).1 a1, rfl⟩, λ a a2, ⟨a, (e _).2 a2, rfl⟩⟩⟩

theorem lift_rel.refl (R : α → α → Prop) (H : reflexive R) : reflexive (lift_rel R) :=
λ s, ⟨λ a as, ⟨a, as, H a⟩, λ b bs, ⟨b, bs, H b⟩⟩

theorem lift_rel.symm (R : α → α → Prop) (H : symmetric R) : symmetric (lift_rel R) :=
λ s1 s2 ⟨l, r⟩,
 ⟨λ a a2, let ⟨b, b1, ab⟩ := r a2 in ⟨b, b1, H ab⟩,
  λ a a1, let ⟨b, b2, ab⟩ := l a1 in ⟨b, b2, H ab⟩⟩

theorem lift_rel.trans (R : α → α → Prop) (H : transitive R) : transitive (lift_rel R) :=
λ s1 s2 s3 ⟨l1, r1⟩ ⟨l2, r2⟩,
 ⟨λ a a1, let ⟨b, b2, ab⟩ := l1 a1, ⟨c, c3, bc⟩ := l2 b2 in ⟨c, c3, H ab bc⟩,
  λ c c3, let ⟨b, b2, bc⟩ := r2 c3, ⟨a, a1, ab⟩ := r1 b2 in ⟨a, a1, H ab bc⟩⟩

theorem lift_rel.equiv (R : α → α → Prop) : equivalence R → equivalence (lift_rel R)
| ⟨refl, symm, trans⟩ :=
  ⟨lift_rel.refl R refl, lift_rel.symm R symm, lift_rel.trans R trans⟩

theorem lift_rel.imp {R S : α → β → Prop} (H : ∀ {a b}, R a b → S a b) (s t) :
  lift_rel R s t → lift_rel S s t | ⟨l, r⟩ :=
⟨λ a as, let ⟨b, bt, ab⟩ := l as in ⟨b, bt, H ab⟩,
 λ b bt, let ⟨a, as, ab⟩ := r bt in ⟨a, as, H ab⟩⟩

theorem terminates_of_lift_rel {R : α → β → Prop} {s t} :
 lift_rel R s t → (terminates s ↔ terminates t) | ⟨l, r⟩ :=
⟨λ ⟨⟨a, as⟩⟩, let ⟨b, bt, ab⟩ := l as in ⟨⟨b, bt⟩⟩,
 λ ⟨⟨b, bt⟩⟩, let ⟨a, as, ab⟩ := r bt in ⟨⟨a, as⟩⟩⟩

theorem rel_of_lift_rel {R : α → β → Prop} {ca cb} :
 lift_rel R ca cb → ∀ {a b}, a ∈ ca → b ∈ cb → R a b
| ⟨l, r⟩ a b ma mb :=
  let ⟨b', mb', ab'⟩ := l ma in by rw mem_unique mb mb'; exact ab'

theorem lift_rel_of_mem {R : α → β → Prop} {a b ca cb}
  (ma : a ∈ ca) (mb : b ∈ cb) (ab : R a b) : lift_rel R ca cb :=
⟨λ a' ma', by rw mem_unique ma' ma; exact ⟨b, mb, ab⟩,
 λ b' mb', by rw mem_unique mb' mb; exact ⟨a, ma, ab⟩⟩

theorem exists_of_lift_rel_left {R : α → β → Prop} {ca cb}
  (H : lift_rel R ca cb) {a} (h : a ∈ ca) : ∃ {b}, b ∈ cb ∧ R a b :=
H.left h

theorem exists_of_lift_rel_right {R : α → β → Prop} {ca cb}
  (H : lift_rel R ca cb) {b} (h : b ∈ cb) : ∃ {a}, a ∈ ca ∧ R a b :=
H.right h

theorem lift_rel_def {R : α → β → Prop} {ca cb} : lift_rel R ca cb ↔
  (terminates ca ↔ terminates cb) ∧ ∀ {a b}, a ∈ ca → b ∈ cb → R a b :=
⟨λ h, ⟨terminates_of_lift_rel h, λ a b ma mb,
  let ⟨b', mb', ab⟩ := h.left ma in by rwa mem_unique mb mb'⟩,
λ ⟨l, r⟩,
 ⟨λ a ma, let ⟨⟨b, mb⟩⟩ := l.1 ⟨⟨_, ma⟩⟩ in ⟨b, mb, r ma mb⟩,
  λ b mb, let ⟨⟨a, ma⟩⟩ := l.2 ⟨⟨_, mb⟩⟩ in ⟨a, ma, r ma mb⟩⟩⟩

theorem lift_rel_bind {δ} (R : α → β → Prop) (S : γ → δ → Prop)
  {s1 : computation α} {s2 : computation β}
  {f1 : α → computation γ} {f2 : β → computation δ}
  (h1 : lift_rel R s1 s2) (h2 : ∀ {a b}, R a b → lift_rel S (f1 a) (f2 b))
  : lift_rel S (bind s1 f1) (bind s2 f2) :=
let ⟨l1, r1⟩ := h1 in
⟨λ c cB,
  let ⟨a, a1, c₁⟩ := mem_bind.1 cB,
      ⟨b, b2, ab⟩ := l1 a1,
      ⟨l2, r2⟩ := h2 ab,
      ⟨d, d2, cd⟩ := l2 c₁ in
  ⟨_, mem_bind_of_mem b2 d2, cd⟩,
λ d dB,
  let ⟨b, b1, d1⟩ := mem_bind.1 dB,
      ⟨a, a2, ab⟩ := r1 b1,
      ⟨l2, r2⟩ := h2 ab,
      ⟨c, c₂, cd⟩ := r2 d1 in
  ⟨_, mem_bind_of_mem a2 c₂, cd⟩⟩

@[simp] theorem lift_rel_return_left (R : α → β → Prop) (a : α) (cb : computation β) :
  lift_rel R (return a) cb ↔ ∃ {b}, b ∈ cb ∧ R a b :=
⟨λ ⟨l, r⟩, l (self_mem_return _),
 λ ⟨b, mb, ab⟩,
  ⟨λ a' ma', by rw mem_return.1 ma'; exact ⟨b, mb, ab⟩,
   λ b' mb', ⟨_, self_mem_return _, by rw mem_unique mb' mb; exact ab⟩⟩⟩

@[simp] theorem lift_rel_return_right (R : α → β → Prop) (ca : computation α) (b : β) :
  lift_rel R ca (return b) ↔ ∃ {a}, a ∈ ca ∧ R a b :=
by rw [lift_rel.swap, lift_rel_return_left]

@[simp] theorem lift_rel_return (R : α → β → Prop) (a : α) (b : β) :
  lift_rel R (return a) (return b) ↔ R a b :=
by rw [lift_rel_return_left]; exact
⟨λ ⟨b', mb', ab'⟩, by rwa mem_return.1 mb' at ab',
 λ ab, ⟨_, self_mem_return _, ab⟩⟩

@[simp] theorem lift_rel_think_left (R : α → β → Prop) (ca : computation α) (cb : computation β) :
  lift_rel R (think ca) cb ↔ lift_rel R ca cb :=
and_congr (forall_congr $ λ b, mem_think.imp iff.rfl)
 (forall_congr $ λ b, imp_congr iff.rfl $ exists_congr $ λ b, mem_think.and iff.rfl)

@[simp] theorem lift_rel_think_right (R : α → β → Prop) (ca : computation α) (cb : computation β) :
  lift_rel R ca (think cb) ↔ lift_rel R ca cb :=
by rw [←lift_rel.swap R, ←lift_rel.swap R]; apply lift_rel_think_left

theorem lift_rel_mem_cases {R : α → β → Prop} {ca cb}
  (Ha : ∀ a ∈ ca, lift_rel R ca cb)
  (Hb : ∀ b ∈ cb, lift_rel R ca cb) : lift_rel R ca cb :=
⟨λ a ma, (Ha _ ma).left ma, λ b mb, (Hb _ mb).right mb⟩

theorem lift_rel_congr {R : α → β → Prop} {ca ca' : computation α} {cb cb' : computation β}
  (ha : ca ~ ca') (hb : cb ~ cb') : lift_rel R ca cb ↔ lift_rel R ca' cb' :=
and_congr
  (forall_congr $ λ a, imp_congr (ha _) $ exists_congr $ λ b, and_congr (hb _) iff.rfl)
  (forall_congr $ λ b, imp_congr (hb _) $ exists_congr $ λ a, and_congr (ha _) iff.rfl)

theorem lift_rel_map {δ} (R : α → β → Prop) (S : γ → δ → Prop)
  {s1 : computation α} {s2 : computation β}
  {f1 : α → γ} {f2 : β → δ}
  (h1 : lift_rel R s1 s2) (h2 : ∀ {a b}, R a b → S (f1 a) (f2 b))
  : lift_rel S (map f1 s1) (map f2 s2) :=
by rw [←bind_return_comp, ←bind_return_comp]; apply lift_rel_bind _ _ h1; simp; exact @h2

theorem map_congr (R : α → α → Prop) (S : β → β → Prop)
  {s1 s2 : computation α} {f : α → β}
  (h1 : s1 ~ s2) : map f s1 ~ map f s2 :=
by rw [←lift_eq_iff_equiv];
   exact lift_rel_map eq _ ((lift_eq_iff_equiv _ _).2 h1) (λ a b, congr_arg _)

def lift_rel_aux (R : α → β → Prop)
  (C : computation α → computation β → Prop) :
  α ⊕ computation α → β ⊕ computation β → Prop
| (sum.inl a)  (sum.inl b)  := R a b
| (sum.inl a)  (sum.inr cb) := ∃ {b}, b ∈ cb ∧ R a b
| (sum.inr ca) (sum.inl b)  := ∃ {a}, a ∈ ca ∧ R a b
| (sum.inr ca) (sum.inr cb) := C ca cb
attribute [simp] lift_rel_aux

@[simp] lemma lift_rel_aux.return_left (R : α → β → Prop)
  (C : computation α → computation β → Prop) (a cb) :
  lift_rel_aux R C (sum.inl a) (destruct cb) ↔ ∃ {b}, b ∈ cb ∧ R a b :=
begin
  induction cb using computation.cases_return_think with b cb,
  { simp only [lift_rel_aux, destruct_return, mem_return, exists_eq_left] },
  { simp only [destruct_think, mem_think, lift_rel_aux] }
end

theorem lift_rel_aux.swap (R : α → β → Prop) (C) (a b) :
  lift_rel_aux (swap R) (swap C) b a = lift_rel_aux R C a b :=
by cases a with a ca; cases b with b cb; simp only [lift_rel_aux]

@[simp] lemma lift_rel_aux.return_right (R : α → β → Prop)
  (C : computation α → computation β → Prop) (b ca) :
  lift_rel_aux R C (destruct ca) (sum.inl b) ↔ ∃ {a}, a ∈ ca ∧ R a b :=
by rw [←lift_rel_aux.swap, lift_rel_aux.return_left]

theorem lift_rel_rec.lem {R : α → β → Prop} (C : computation α → computation β → Prop)
  (H : ∀ {ca cb}, C ca cb → lift_rel_aux R C (destruct ca) (destruct cb))
  (ca cb) (Hc : C ca cb) (a) (ha : a ∈ ca) : lift_rel R ca cb :=
begin
  revert cb, refine rec_on_mem ha _ (λ ca' IH, _); intros cb Hc; have h := H Hc,
  { simpa using h },
  { rw [lift_rel_think_left],
    induction cb using computation.cases_return_think; simp at h; simp [h],
    exact IH _ h }
end

theorem lift_rel_rec {R : α → β → Prop} (C : computation α → computation β → Prop)
  (H : ∀ {ca cb}, C ca cb → lift_rel_aux R C (destruct ca) (destruct cb))
  (ca cb) (Hc : C ca cb) : lift_rel R ca cb :=
lift_rel_mem_cases (lift_rel_rec.lem C @H ca cb Hc) (λ b hb,
 (lift_rel.swap _ _ _).2 $
 lift_rel_rec.lem (swap C)
   (λ cb ca h, cast (lift_rel_aux.swap _ _ _ _).symm $ H h)
   cb ca Hc b hb)

end computation
