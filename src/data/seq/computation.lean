/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Coinductive formalization of unbounded computations.
-/
import data.stream
import tactic.basic

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
def computation (α : Type u) : Type u :=
{ f : stream (option α) // ∀ {n a}, f n = some a → f (n+1) = some a }

namespace computation
variables {α : Type u} {β : Type v} {γ : Type w}

-- constructors
/-- `return a` is the computation that immediately terminates with result `a`. -/
def return (a : α) : computation α := ⟨stream.const (some a), λn a', id⟩

instance : has_coe_t α (computation α) := ⟨return⟩ -- note [use has_coe_t]

/-- `think c` is the computation that delays for one "tick" and then performs
  computation `c`. -/
def think (c : computation α) : computation α :=
⟨none :: c.1, λn a h, by {cases n with n, contradiction, exact c.2 h}⟩

/-- `thinkN c n` is the computation that delays for `n` ticks and then performs
  computation `c`. -/
def thinkN (c : computation α) : ℕ → computation α
| 0 := c
| (n+1) := think (thinkN n)

-- check for immediate result
/-- `head c` is the first step of computation, either `some a` if `c = return a`
  or `none` if `c = think c'`. -/
def head (c : computation α) : option α := c.1.head

-- one step of computation
/-- `tail c` is the remainder of computation, either `c` if `c = return a`
  or `c'` if `c = think c'`. -/
def tail (c : computation α) : computation α :=
⟨c.1.tail, λ n a, let t := c.2 in t⟩

/-- `empty α` is the computation that never returns, an infinite sequence of
  `think`s. -/
def empty (α) : computation α := ⟨stream.const none, λn a', id⟩

instance : inhabited (computation α) := ⟨empty _⟩

/-- `run_for c n` evaluates `c` for `n` steps and returns the result, or `none`
  if it did not terminate after `n` steps. -/
def run_for : computation α → ℕ → option α := subtype.val

/-- `destruct c` is the destructor for `computation α` as a coinductive type.
  It returns `inl a` if `c = return a` and `inr c'` if `c = think c'`. -/
def destruct (c : computation α) : α ⊕ computation α :=
match c.1 0 with
| none := sum.inr (tail c)
| some a := sum.inl a
end

/-- `run c` is an unsound meta function that runs `c` to completion, possibly
  resulting in an infinite loop in the VM. -/
meta def run : computation α → α | c :=
match destruct c with
| sum.inl a := a
| sum.inr ca := run ca
end

theorem destruct_eq_ret {s : computation α} {a : α} :
  destruct s = sum.inl a → s = return a :=
begin
  dsimp [destruct],
  induction f0 : s.1 0; intro h,
  { contradiction },
  { apply subtype.eq, funext n,
    induction n with n IH,
    { injection h with h', rwa h' at f0 },
    { exact s.2 IH } }
end

theorem destruct_eq_think {s : computation α} {s'} :
  destruct s = sum.inr s' → s = think s' :=
begin
  dsimp [destruct],
  induction f0 : s.1 0 with a'; intro h,
  { injection h with h', rw ←h',
    cases s with f al,
    apply subtype.eq, dsimp [think, tail],
    rw ←f0, exact (stream.eta f).symm },
  { contradiction }
end

@[simp] theorem destruct_ret (a : α) : destruct (return a) = sum.inl a := rfl

@[simp] theorem destruct_think : ∀ s : computation α, destruct (think s) = sum.inr s
| ⟨f, al⟩ := rfl

@[simp] theorem destruct_empty : destruct (empty α) = sum.inr (empty α) := rfl

@[simp] theorem head_ret (a : α) : head (return a) = some a := rfl

@[simp] theorem head_think (s : computation α) : head (think s) = none := rfl

@[simp] theorem head_empty : head (empty α) = none := rfl

@[simp] theorem tail_ret (a : α) : tail (return a) = return a := rfl

@[simp] theorem tail_think (s : computation α) : tail (think s) = s :=
by cases s with f al; apply subtype.eq; dsimp [tail, think]; rw [stream.tail_cons]

@[simp] theorem tail_empty : tail (empty α) = empty α := rfl

theorem think_empty : empty α = think (empty α) :=
destruct_eq_think destruct_empty

def cases_on {C : computation α → Sort v} (s : computation α)
  (h1 : ∀ a, C (return a)) (h2 : ∀ s, C (think s)) : C s := begin
  induction H : destruct s with v v,
  { rw destruct_eq_ret H, apply h1 },
  { cases v with a s', rw destruct_eq_think H, apply h2 }
end

def corec.F (f : β → α ⊕ β) : α ⊕ β → option α × (α ⊕ β)
| (sum.inl a) := (some a, sum.inl a)
| (sum.inr b) := (match f b with
  | sum.inl a := some a
  | sum.inr b' := none
  end, f b)

/-- `corec f b` is the corecursor for `computation α` as a coinductive type.
  If `f b = inl a` then `corec f b = return a`, and if `f b = inl b'` then
  `corec f b = think (corec f b')`. -/
def corec (f : β → α ⊕ β) (b : β) : computation α :=
begin
  refine ⟨stream.corec' (corec.F f) (sum.inr b), λn a' h, _⟩,
  rw stream.corec'_eq,
  change stream.corec' (corec.F f) (corec.F f (sum.inr b)).2 n = some a',
  revert h, generalize : sum.inr b = o, revert o,
  induction n with n IH; intro o,
  { change (corec.F f o).1 = some a' → (corec.F f (corec.F f o).2).1 = some a',
    cases o with a b; intro h, { exact h },
    dsimp [corec.F] at h, dsimp [corec.F],
    cases f b with a b', { exact h },
    { contradiction } },
  { rw [stream.corec'_eq (corec.F f) (corec.F f o).2,
        stream.corec'_eq (corec.F f) o],
    exact IH (corec.F f o).2 }
end

/-- left map of `⊕` -/
def lmap (f : α → β) : α ⊕ γ → β ⊕ γ
| (sum.inl a) := sum.inl (f a)
| (sum.inr b) := sum.inr b

/-- right map of `⊕` -/
def rmap (f : β → γ) : α ⊕ β → α ⊕ γ
| (sum.inl a) := sum.inl a
| (sum.inr b) := sum.inr (f b)
attribute [simp] lmap rmap

@[simp] lemma corec_eq (f : β → α ⊕ β) (b : β) :
  destruct (corec f b) = rmap (corec f) (f b) :=
begin
  dsimp [corec, destruct],
  change stream.corec' (corec.F f) (sum.inr b) 0 with corec.F._match_1 (f b),
  induction h : f b with a b', { refl },
  dsimp [corec.F, destruct],
  apply congr_arg, apply subtype.eq,
  dsimp [corec, tail],
  rw [stream.corec'_eq, stream.tail_cons],
  dsimp [corec.F], rw h
end

section bisim
  variable (R : computation α → computation α → Prop)

  local infix ` ~ `:50 := R

  def bisim_o : α ⊕ computation α → α ⊕ computation α → Prop
  | (sum.inl a) (sum.inl a') := a = a'
  | (sum.inr s) (sum.inr s') := R s s'
  | _           _            := false
  attribute [simp] bisim_o

  def is_bisimulation := ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → bisim_o R (destruct s₁) (destruct s₂)

  -- If two computations are bisimilar, then they are equal
  theorem eq_of_bisim (bisim : is_bisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂ :=
  begin
    apply subtype.eq,
    apply stream.eq_of_bisim (λx y, ∃ s s' : computation α, s.1 = x ∧ s'.1 = y ∧ R s s'),
    dsimp [stream.is_bisimulation],
    intros t₁ t₂ e,
    exact match t₁, t₂, e with ._, ._, ⟨s, s', rfl, rfl, r⟩ :=
      suffices head s = head s' ∧ R (tail s) (tail s'), from
      and.imp id (λr, ⟨tail s, tail s',
        by cases s; refl, by cases s'; refl, r⟩) this,
      begin
        have := bisim r, revert r this,
        apply cases_on s _ _; intros; apply cases_on s' _ _; intros; intros r this,
        { constructor, dsimp at this, rw this, assumption },
        { rw [destruct_ret, destruct_think] at this,
          exact false.elim this },
        { rw [destruct_ret, destruct_think] at this,
          exact false.elim this },
        { simp at this, simp [*] }
      end
    end,
    exact ⟨s₁, s₂, rfl, rfl, r⟩
  end
end bisim

-- It's more of a stretch to use ∈ for this relation, but it
-- asserts that the computation limits to the given value.
protected def mem (a : α) (s : computation α) := some a ∈ s.1

instance : has_mem α (computation α) := ⟨computation.mem⟩

theorem le_stable (s : computation α) {a m n} (h : m ≤ n) :
  s.1 m = some a → s.1 n = some a :=
by {cases s with f al, induction h with n h IH, exacts [id, λ h2, al (IH h2)]}

theorem mem_unique {s : computation α} {a b : α} : a ∈ s → b ∈ s → a = b
| ⟨m, ha⟩ ⟨n, hb⟩ := by injection
  (le_stable s (le_max_left m n) ha.symm).symm.trans
  (le_stable s (le_max_right m n) hb.symm)

theorem mem.left_unique : relator.left_unique ((∈) : α → computation α → Prop) :=
⟨λ a s b, mem_unique⟩

/-- `terminates s` asserts that the computation `s` eventually terminates with some value. -/
class terminates (s : computation α) : Prop := (term : ∃ a, a ∈ s)

theorem terminates_iff (s : computation α) : terminates s ↔ ∃ a, a ∈ s :=
⟨λ h, h.1, terminates.mk⟩

theorem terminates_of_mem {s : computation α} {a : α} (h : a ∈ s) : terminates s :=
⟨⟨a, h⟩⟩

theorem terminates_def (s : computation α) : terminates s ↔ ∃ n, (s.1 n).is_some :=
⟨λ ⟨⟨a, n, h⟩⟩, ⟨n, by {dsimp [stream.nth] at h, rw ←h, exact rfl}⟩,
 λ ⟨n, h⟩, ⟨⟨option.get h, n, (option.eq_some_of_is_some h).symm⟩⟩⟩

theorem ret_mem (a : α) : a ∈ return a :=
exists.intro 0 rfl

theorem eq_of_ret_mem {a a' : α} (h : a' ∈ return a) : a' = a :=
mem_unique h (ret_mem _)

instance ret_terminates (a : α) : terminates (return a) :=
terminates_of_mem (ret_mem _)

theorem think_mem {s : computation α} {a} : a ∈ s → a ∈ think s
| ⟨n, h⟩ := ⟨n+1, h⟩

instance think_terminates (s : computation α) :
  ∀ [terminates s], terminates (think s)
| ⟨⟨a, n, h⟩⟩ := ⟨⟨a, n+1, h⟩⟩

theorem of_think_mem {s : computation α} {a} : a ∈ think s → a ∈ s
| ⟨n, h⟩ := by {cases n with n', contradiction, exact ⟨n', h⟩}

theorem of_think_terminates {s : computation α} :
  terminates (think s) → terminates s
| ⟨⟨a, h⟩⟩ := ⟨⟨a, of_think_mem h⟩⟩

theorem not_mem_empty (a : α) : a ∉ empty α :=
λ ⟨n, h⟩, by clear _fun_match; contradiction

theorem not_terminates_empty : ¬ terminates (empty α) :=
λ ⟨⟨a, h⟩⟩, not_mem_empty a h

theorem eq_empty_of_not_terminates {s} (H : ¬ terminates s) : s = empty α :=
begin
  apply subtype.eq, funext n,
  induction h : s.val n, {refl},
  refine absurd _ H, exact ⟨⟨_, _, h.symm⟩⟩
end

theorem thinkN_mem {s : computation α} {a} : ∀ n, a ∈ thinkN s n ↔ a ∈ s
| 0 := iff.rfl
| (n+1) := iff.trans ⟨of_think_mem, think_mem⟩ (thinkN_mem n)

instance thinkN_terminates (s : computation α) :
  ∀ [terminates s] n, terminates (thinkN s n)
| ⟨⟨a, h⟩⟩ n := ⟨⟨a, (thinkN_mem n).2 h⟩⟩

theorem of_thinkN_terminates (s : computation α) (n) :
  terminates (thinkN s n) → terminates s
| ⟨⟨a, h⟩⟩ := ⟨⟨a, (thinkN_mem _).1 h⟩⟩

/-- `promises s a`, or `s ~> a`, asserts that although the computation `s`
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
def length : ℕ := nat.find ((terminates_def _).1 h)

/-- `get s` returns the result of a terminating computation -/
def get : α := option.get (nat.find_spec $ (terminates_def _).1 h)

theorem get_mem : get s ∈ s :=
exists.intro (length s) (option.eq_some_of_is_some _).symm

theorem get_eq_of_mem {a} : a ∈ s → get s = a :=
mem_unique (get_mem _)

theorem mem_of_get_eq {a} : get s = a → a ∈ s :=
by intro h; rw ←h; apply get_mem

@[simp] theorem get_think : get (think s) = get s :=
get_eq_of_mem _ $ let ⟨n, h⟩ := get_mem s in ⟨n+1, h⟩

@[simp] theorem get_thinkN (n) : get (thinkN s n) = get s :=
get_eq_of_mem _ $ (thinkN_mem _).2 (get_mem _)

theorem get_promises : s ~> get s := λ a, get_eq_of_mem _

theorem mem_of_promises {a} (p : s ~> a) : a ∈ s :=
by { casesI h, cases h with a' h, rw p h, exact h }

theorem get_eq_of_promises {a} : s ~> a → get s = a :=
get_eq_of_mem _ ∘ mem_of_promises _

end get

/-- `results s a n` completely characterizes a terminating computation:
  it asserts that `s` terminates after exactly `n` steps, with result `a`. -/
def results (s : computation α) (a : α) (n : ℕ) :=
∃ (h : a ∈ s), @length _ s (terminates_of_mem h) = n

theorem results_of_terminates (s : computation α) [T : terminates s] :
  results s (get s) (length s) :=
⟨get_mem _, rfl⟩

theorem results_of_terminates' (s : computation α) [T : terminates s] {a} (h : a ∈ s) :
  results s a (length s) :=
by rw ←get_eq_of_mem _ h; apply results_of_terminates

theorem results.mem {s : computation α} {a n} : results s a n → a ∈ s
| ⟨m, _⟩ := m

theorem results.terminates {s : computation α} {a n} (h : results s a n) : terminates s :=
terminates_of_mem h.mem

theorem results.length {s : computation α} {a n} [T : terminates s] :
  results s a n → length s = n
| ⟨_, h⟩ := h

theorem results.val_unique {s : computation α} {a b m n}
  (h1 : results s a m) (h2 : results s b n) : a = b :=
mem_unique h1.mem h2.mem

theorem results.len_unique {s : computation α} {a b m n}
  (h1 : results s a m) (h2 : results s b n) : m = n :=
by haveI := h1.terminates; haveI := h2.terminates; rw [←h1.length, h2.length]

theorem exists_results_of_mem {s : computation α} {a} (h : a ∈ s) : ∃ n, results s a n :=
by haveI := terminates_of_mem h; exact ⟨_, results_of_terminates' s h⟩

@[simp] theorem get_ret (a : α) : get (return a) = a :=
get_eq_of_mem _ ⟨0, rfl⟩

@[simp] theorem length_ret (a : α) : length (return a) = 0 :=
let h := computation.ret_terminates a in
nat.eq_zero_of_le_zero $ nat.find_min' ((terminates_def (return a)).1 h) rfl

theorem results_ret (a : α) : results (return a) a 0 :=
⟨_, length_ret _⟩

@[simp] theorem length_think (s : computation α) [h : terminates s] :
  length (think s) = length s + 1 :=
begin
  apply le_antisymm,
  { exact nat.find_min' _ (nat.find_spec ((terminates_def _).1 h)) },
  { have : (option.is_some ((think s).val (length (think s))) : Prop) :=
      nat.find_spec ((terminates_def _).1 s.think_terminates),
    cases length (think s) with n,
    { contradiction },
    { apply nat.succ_le_succ, apply nat.find_min', apply this } }
end

theorem results_think {s : computation α} {a n}
  (h : results s a n) : results (think s) a (n + 1) :=
by haveI := h.terminates; exact ⟨think_mem h.mem, by rw [length_think, h.length]⟩

theorem of_results_think {s : computation α} {a n}
  (h : results (think s) a n) : ∃ m, results s a m ∧ n = m + 1 :=
begin
  haveI := of_think_terminates h.terminates,
  have := results_of_terminates' _ (of_think_mem h.mem),
  exact ⟨_, this, results.len_unique h (results_think this)⟩,
end

@[simp] theorem results_think_iff {s : computation α} {a n} :
  results (think s) a (n + 1) ↔ results s a n :=
⟨λ h, let ⟨n', r, e⟩ := of_results_think h in by injection e with h'; rwa h',
results_think⟩

theorem results_thinkN {s : computation α} {a m} :
  ∀ n, results s a m → results (thinkN s n) a (m + n)
| 0     h := h
| (n+1) h := results_think (results_thinkN n h)

theorem results_thinkN_ret (a : α) (n) : results (thinkN (return a) n) a n :=
by have := results_thinkN n (results_ret a); rwa nat.zero_add at this

@[simp] theorem length_thinkN (s : computation α) [h : terminates s] (n) :
  length (thinkN s n) = length s + n :=
(results_thinkN n (results_of_terminates _)).length

theorem eq_thinkN {s : computation α} {a n} (h : results s a n) :
  s = thinkN (return a) n :=
begin
  revert s,
  induction n with n IH; intro s;
  apply cases_on s (λ a', _) (λ s, _); intro h,
  { rw ←eq_of_ret_mem h.mem, refl },
  { cases of_results_think h with n h, cases h, contradiction },
  { have := h.len_unique (results_ret _), contradiction },
  { rw IH (results_think_iff.1 h), refl }
end

theorem eq_thinkN' (s : computation α) [h : terminates s] :
  s = thinkN (return (get s)) (length s) :=
eq_thinkN (results_of_terminates _)

def mem_rec_on {C : computation α → Sort v} {a s} (M : a ∈ s)
  (h1 : C (return a)) (h2 : ∀ s, C s → C (think s)) : C s :=
begin
  haveI T := terminates_of_mem M,
  rw [eq_thinkN' s, get_eq_of_mem s M],
  generalize : length s = n,
  induction n with n IH, exacts [h1, h2 _ IH]
end

def terminates_rec_on {C : computation α → Sort v} (s) [terminates s]
  (h1 : ∀ a, C (return a)) (h2 : ∀ s, C s → C (think s)) : C s :=
mem_rec_on (get_mem s) (h1 _) h2

/-- Map a function on the result of a computation. -/
def map (f : α → β) : computation α → computation β
| ⟨s, al⟩ := ⟨s.map (λo, option.cases_on o none (some ∘ f)),
λn b, begin
  dsimp [stream.map, stream.nth],
  induction e : s n with a; intro h,
  { contradiction }, { rw [al e, ←h] }
end⟩

def bind.G : β ⊕ computation β → β ⊕ computation α ⊕ computation β
| (sum.inl b)   := sum.inl b
| (sum.inr cb') := sum.inr $ sum.inr cb'

def bind.F (f : α → computation β) :
  computation α ⊕ computation β → β ⊕ computation α ⊕ computation β
| (sum.inl ca) :=
  match destruct ca with
  | sum.inl a := bind.G $ destruct (f a)
  | sum.inr ca' := sum.inr $ sum.inl ca'
  end
| (sum.inr cb) := bind.G $ destruct cb

/-- Compose two computations into a monadic `bind` operation. -/
def bind (c : computation α) (f : α → computation β) : computation β :=
corec (bind.F f) (sum.inl c)

instance : has_bind computation := ⟨@bind⟩

theorem has_bind_eq_bind {β} (c : computation α) (f : α → computation β) :
  c >>= f = bind c f := rfl

/-- Flatten a computation of computations into a single computation. -/
def join (c : computation (computation α)) : computation α := c >>= id

@[simp] theorem map_ret (f : α → β) (a) : map f (return a) = return (f a) := rfl

@[simp] theorem map_think (f : α → β) : ∀ s, map f (think s) = think (map f s)
| ⟨s, al⟩ := by apply subtype.eq; dsimp [think, map]; rw stream.map_cons

@[simp]
theorem destruct_map (f : α → β) (s) : destruct (map f s) = lmap f (rmap (map f) (destruct s)) :=
by apply s.cases_on; intro; simp

@[simp] theorem map_id : ∀ (s : computation α), map id s = s
| ⟨f, al⟩ := begin
  apply subtype.eq; simp [map, function.comp],
  have e : (@option.rec α (λ_, option α) none some) = id,
  { ext ⟨⟩; refl },
  simp [e, stream.map_id]
end

theorem map_comp (f : α → β) (g : β → γ) :
  ∀ (s : computation α), map (g ∘ f) s = map g (map f s)
| ⟨s, al⟩ := begin
  apply subtype.eq; dsimp [map],
  rw stream.map_map,
  apply congr_arg (λ f : _ → option γ, stream.map f s),
  ext ⟨⟩; refl
end

@[simp] theorem ret_bind (a) (f : α → computation β) :
  bind (return a) f = f a :=
begin
  apply eq_of_bisim (λc₁ c₂,
         c₁ = bind (return a) f ∧ c₂ = f a ∨
         c₁ = corec (bind.F f) (sum.inr c₂)),
  { intros c₁ c₂ h,
    exact match c₁, c₂, h with
    | ._, ._, or.inl ⟨rfl, rfl⟩ := begin
      simp [bind, bind.F],
      cases destruct (f a) with b cb; simp [bind.G]
    end
    | ._, c, or.inr rfl := begin
      simp [bind.F],
      cases destruct c with b cb; simp [bind.G]
    end end },
  { simp }
end

@[simp] theorem think_bind (c) (f : α → computation β) :
  bind (think c) f = think (bind c f) :=
destruct_eq_think $ by simp [bind, bind.F]

@[simp] theorem bind_ret (f : α → β) (s) : bind s (return ∘ f) = map f s :=
begin
  apply eq_of_bisim (λc₁ c₂, c₁ = c₂ ∨
         ∃ s, c₁ = bind s (return ∘ f) ∧ c₂ = map f s),
  { intros c₁ c₂ h,
    exact match c₁, c₂, h with
    | _, _, or.inl (eq.refl c) := begin cases destruct c with b cb; simp end
    | _, _, or.inr ⟨s, rfl, rfl⟩ := begin
      apply cases_on s; intros s; simp,
      exact or.inr ⟨s, rfl, rfl⟩
    end end },
  { exact or.inr ⟨s, rfl, rfl⟩ }
end

@[simp] theorem bind_ret' (s : computation α) : bind s return = s :=
by rw bind_ret; change (λ x : α, x) with @id α; rw map_id

@[simp] theorem bind_assoc (s : computation α) (f : α → computation β) (g : β → computation γ) :
  bind (bind s f) g = bind s (λ (x : α), bind (f x) g) :=
begin
  apply eq_of_bisim (λc₁ c₂, c₁ = c₂ ∨
         ∃ s, c₁ = bind (bind s f) g ∧ c₂ = bind s (λ (x : α), bind (f x) g)),
  { intros c₁ c₂ h,
    exact match c₁, c₂, h with
    | _, _, or.inl (eq.refl c) := by cases destruct c with b cb; simp
    | ._, ._, or.inr ⟨s, rfl, rfl⟩ := begin
      apply cases_on s; intros s; simp,
      { generalize : f s = fs,
        apply cases_on fs; intros t; simp,
        { cases destruct (g t) with b cb; simp } },
      { exact or.inr ⟨s, rfl, rfl⟩ }
    end end },
  { exact or.inr ⟨s, rfl, rfl⟩ }
end

theorem results_bind {s : computation α} {f : α → computation β} {a b m n}
  (h1 : results s a m) (h2 : results (f a) b n) : results (bind s f) b (n + m) :=
begin
  have := h1.mem, revert m,
  apply mem_rec_on this _ (λ s IH, _); intros m h1,
  { rw [ret_bind], rw h1.len_unique (results_ret _), exact h2 },
  { rw [think_bind], cases of_results_think h1 with m' h, cases h with h1 e,
    rw e, exact results_think (IH h1) }
end

theorem mem_bind {s : computation α} {f : α → computation β} {a b}
  (h1 : a ∈ s) (h2 : b ∈ f a) : b ∈ bind s f :=
let ⟨m, h1⟩ := exists_results_of_mem h1,
    ⟨n, h2⟩ := exists_results_of_mem h2 in (results_bind h1 h2).mem

instance terminates_bind (s : computation α) (f : α → computation β)
  [terminates s] [terminates (f (get s))] :
  terminates (bind s f) :=
terminates_of_mem (mem_bind (get_mem s) (get_mem (f (get s))))

@[simp] theorem get_bind (s : computation α) (f : α → computation β)
  [terminates s] [terminates (f (get s))] :
  get (bind s f) = get (f (get s)) :=
get_eq_of_mem _ (mem_bind (get_mem s) (get_mem (f (get s))))

@[simp] theorem length_bind (s : computation α) (f : α → computation β)
  [T1 : terminates s] [T2 : terminates (f (get s))] :
  length (bind s f) = length (f (get s)) + length s :=
(results_of_terminates _).len_unique $
results_bind (results_of_terminates _) (results_of_terminates _)

theorem of_results_bind {s : computation α} {f : α → computation β} {b k} :
  results (bind s f) b k →
  ∃ a m n, results s a m ∧ results (f a) b n ∧ k = n + m :=
begin
  induction k with n IH generalizing s;
  apply cases_on s (λ a, _) (λ s', _); intro e,
  { simp [thinkN] at e, refine ⟨a, _, _, results_ret _, e, rfl⟩ },
  { have := congr_arg head (eq_thinkN e), contradiction },
  { simp at e, refine ⟨a, _, n+1, results_ret _, e, rfl⟩ },
  { simp at e, exact let ⟨a, m, n', h1, h2, e'⟩ := IH e in
    by rw e'; exact ⟨a, m.succ, n', results_think h1, h2, rfl⟩ }
end

theorem exists_of_mem_bind {s : computation α} {f : α → computation β} {b}
  (h : b ∈ bind s f) : ∃ a ∈ s, b ∈ f a :=
let ⟨k, h⟩ := exists_results_of_mem h,
    ⟨a, m, n, h1, h2, e⟩ := of_results_bind h in ⟨a, h1.mem, h2.mem⟩

theorem bind_promises {s : computation α} {f : α → computation β} {a b}
  (h1 : s ~> a) (h2 : f a ~> b) : bind s f ~> b :=
λ b' bB, begin
  rcases exists_of_mem_bind bB with ⟨a', a's, ba'⟩,
  rw ←h1 a's at ba', exact h2 ba'
end

instance : monad computation :=
{ map  := @map,
  pure := @return,
  bind := @bind }

instance : is_lawful_monad computation :=
{ id_map := @map_id,
  bind_pure_comp_eq_map := @bind_ret,
  pure_bind := @ret_bind,
  bind_assoc := @bind_assoc }

theorem has_map_eq_map {β} (f : α → β) (c : computation α) : f <$> c = map f c := rfl

@[simp] theorem return_def (a) : (_root_.return a : computation α) = return a := rfl

@[simp] theorem map_ret' {α β} : ∀ (f : α → β) (a), f <$> return a = return (f a) := map_ret
@[simp] theorem map_think' {α β} : ∀ (f : α → β) s, f <$> think s = think (f <$> s) := map_think

theorem mem_map (f : α → β) {a} {s : computation α} (m : a ∈ s) : f a ∈ map f s :=
by rw ←bind_ret; apply mem_bind m; apply ret_mem

theorem exists_of_mem_map {f : α → β} {b : β} {s : computation α} (h : b ∈ map f s) :
   ∃ a, a ∈ s ∧ f a = b :=
by rw ←bind_ret at h; exact
let ⟨a, as, fb⟩ := exists_of_mem_bind h in ⟨a, as, mem_unique (ret_mem _) fb⟩

instance terminates_map (f : α → β) (s : computation α) [terminates s] : terminates (map f s) :=
by rw ←bind_ret; apply_instance

theorem terminates_map_iff (f : α → β) (s : computation α) :
  terminates (map f s) ↔ terminates s :=
⟨λ ⟨⟨a, h⟩⟩, let ⟨b, h1, _⟩ := exists_of_mem_map h in ⟨⟨_, h1⟩⟩,
 @computation.terminates_map _ _ _ _⟩

-- Parallel computation
/-- `c₁ <|> c₂` calculates `c₁` and `c₂` simultaneously, returning
  the first one that gives a result. -/
def orelse (c₁ c₂ : computation α) : computation α :=
@computation.corec α (computation α × computation α)
  (λ⟨c₁, c₂⟩, match destruct c₁ with
  | sum.inl a := sum.inl a
  | sum.inr c₁' := match destruct c₂ with
    | sum.inl a := sum.inl a
    | sum.inr c₂' := sum.inr (c₁', c₂')
    end
  end) (c₁, c₂)

instance : alternative computation :=
{ orelse := @orelse, failure := @empty, ..computation.monad }

@[simp] theorem ret_orelse (a : α) (c₂ : computation α) :
  (return a <|> c₂) = return a :=
destruct_eq_ret $ by unfold has_orelse.orelse; simp [orelse]

@[simp] theorem orelse_ret (c₁ : computation α) (a : α) :
  (think c₁ <|> return a) = return a :=
destruct_eq_ret $ by unfold has_orelse.orelse; simp [orelse]

@[simp] theorem orelse_think (c₁ c₂ : computation α) :
  (think c₁ <|> think c₂) = think (c₁ <|> c₂) :=
destruct_eq_think $ by unfold has_orelse.orelse; simp [orelse]

@[simp] theorem empty_orelse (c) : (empty α <|> c) = c :=
begin
  apply eq_of_bisim (λc₁ c₂, (empty α <|> c₂) = c₁) _ rfl,
  intros s' s h, rw ←h,
  apply cases_on s; intros s; rw think_empty; simp,
  rw ←think_empty,
end

@[simp] theorem orelse_empty (c : computation α) : (c <|> empty α) = c :=
begin
  apply eq_of_bisim (λc₁ c₂, (c₂ <|> empty α) = c₁) _ rfl,
  intros s' s h, rw ←h,
  apply cases_on s; intros s; rw think_empty; simp,
  rw←think_empty,
end

/-- `c₁ ~ c₂` asserts that `c₁` and `c₂` either both terminate with the same result,
  or both loop forever. -/
def equiv (c₁ c₂ : computation α) : Prop := ∀ a, a ∈ c₁ ↔ a ∈ c₂

infix ` ~ `:50 := equiv

@[refl] theorem equiv.refl (s : computation α) : s ~ s := λ_, iff.rfl

@[symm] theorem equiv.symm {s t : computation α} : s ~ t → t ~ s :=
λh a, (h a).symm

@[trans] theorem equiv.trans {s t u : computation α} : s ~ t → t ~ u → s ~ u :=
λh1 h2 a, (h1 a).trans (h2 a)

theorem equiv.equivalence : equivalence (@equiv α) :=
⟨@equiv.refl _, @equiv.symm _, @equiv.trans _⟩

theorem equiv_of_mem {s t : computation α} {a} (h1 : a ∈ s) (h2 : a ∈ t) : s ~ t :=
λa', ⟨λma, by rw mem_unique ma h1; exact h2,
      λma, by rw mem_unique ma h2; exact h1⟩

theorem terminates_congr {c₁ c₂ : computation α}
  (h : c₁ ~ c₂) : terminates c₁ ↔ terminates c₂ :=
by simp only [terminates_iff, exists_congr h]

theorem promises_congr {c₁ c₂ : computation α}
  (h : c₁ ~ c₂) (a) : c₁ ~> a ↔ c₂ ~> a :=
forall_congr (λa', imp_congr (h a') iff.rfl)

theorem get_equiv {c₁ c₂ : computation α} (h : c₁ ~ c₂)
  [terminates c₁] [terminates c₂] : get c₁ = get c₂ :=
get_eq_of_mem _ $ (h _).2 $ get_mem _

theorem think_equiv (s : computation α) : think s ~ s :=
λ a, ⟨of_think_mem, think_mem⟩

theorem thinkN_equiv (s : computation α) (n) : thinkN s n ~ s :=
λ a, thinkN_mem n

theorem bind_congr {s1 s2 : computation α} {f1 f2 : α → computation β}
  (h1 : s1 ~ s2) (h2 : ∀ a, f1 a ~ f2 a) : bind s1 f1 ~ bind s2 f2 :=
λ b, ⟨λh, let ⟨a, ha, hb⟩ := exists_of_mem_bind h in
        mem_bind ((h1 a).1 ha) ((h2 a b).1 hb),
      λh, let ⟨a, ha, hb⟩ := exists_of_mem_bind h in
        mem_bind ((h1 a).2 ha) ((h2 a b).2 hb)⟩

theorem equiv_ret_of_mem {s : computation α} {a} (h : a ∈ s) : s ~ return a :=
equiv_of_mem h (ret_mem _)

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
⟨λ⟨h1, h2⟩ a,
  ⟨λ a1, let ⟨b, b2, ab⟩ := h1 a1 in by rwa ab,
   λ a2, let ⟨b, b1, ab⟩ := h2 a2 in by rwa ←ab⟩,
λe, ⟨λ a a1, ⟨a, (e _).1 a1, rfl⟩, λ a a2, ⟨a, (e _).2 a2, rfl⟩⟩⟩

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
⟨λh, ⟨terminates_of_lift_rel h, λ a b ma mb,
  let ⟨b', mb', ab⟩ := h.left ma in by rwa mem_unique mb mb'⟩,
λ⟨l, r⟩,
 ⟨λ a ma, let ⟨⟨b, mb⟩⟩ := l.1 ⟨⟨_, ma⟩⟩ in ⟨b, mb, r ma mb⟩,
  λ b mb, let ⟨⟨a, ma⟩⟩ := l.2 ⟨⟨_, mb⟩⟩ in ⟨a, ma, r ma mb⟩⟩⟩

theorem lift_rel_bind {δ} (R : α → β → Prop) (S : γ → δ → Prop)
  {s1 : computation α} {s2 : computation β}
  {f1 : α → computation γ} {f2 : β → computation δ}
  (h1 : lift_rel R s1 s2) (h2 : ∀ {a b}, R a b → lift_rel S (f1 a) (f2 b))
  : lift_rel S (bind s1 f1) (bind s2 f2) :=
let ⟨l1, r1⟩ := h1 in
⟨λ c cB,
  let ⟨a, a1, c₁⟩ := exists_of_mem_bind cB,
      ⟨b, b2, ab⟩ := l1 a1,
      ⟨l2, r2⟩ := h2 ab,
      ⟨d, d2, cd⟩ := l2 c₁ in
  ⟨_, mem_bind b2 d2, cd⟩,
λ d dB,
  let ⟨b, b1, d1⟩ := exists_of_mem_bind dB,
      ⟨a, a2, ab⟩ := r1 b1,
      ⟨l2, r2⟩ := h2 ab,
      ⟨c, c₂, cd⟩ := r2 d1 in
  ⟨_, mem_bind a2 c₂, cd⟩⟩

@[simp] theorem lift_rel_return_left (R : α → β → Prop) (a : α) (cb : computation β) :
  lift_rel R (return a) cb ↔ ∃ {b}, b ∈ cb ∧ R a b :=
⟨λ⟨l, r⟩, l (ret_mem _),
 λ⟨b, mb, ab⟩,
  ⟨λ a' ma', by rw eq_of_ret_mem ma'; exact ⟨b, mb, ab⟩,
   λ b' mb', ⟨_, ret_mem _, by rw mem_unique mb' mb; exact ab⟩⟩⟩

@[simp] theorem lift_rel_return_right (R : α → β → Prop) (ca : computation α) (b : β) :
  lift_rel R ca (return b) ↔ ∃ {a}, a ∈ ca ∧ R a b :=
by rw [lift_rel.swap, lift_rel_return_left]

@[simp] theorem lift_rel_return (R : α → β → Prop) (a : α) (b : β) :
  lift_rel R (return a) (return b) ↔ R a b :=
by rw [lift_rel_return_left]; exact
⟨λ⟨b', mb', ab'⟩, by rwa eq_of_ret_mem mb' at ab',
 λab, ⟨_, ret_mem _, ab⟩⟩

@[simp] theorem lift_rel_think_left (R : α → β → Prop) (ca : computation α) (cb : computation β) :
  lift_rel R (think ca) cb ↔ lift_rel R ca cb :=
and_congr (forall_congr $ λb, imp_congr ⟨of_think_mem, think_mem⟩ iff.rfl)
 (forall_congr $ λb, imp_congr iff.rfl $
    exists_congr $ λ b, and_congr ⟨of_think_mem, think_mem⟩ iff.rfl)

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
by rw [←bind_ret, ←bind_ret]; apply lift_rel_bind _ _ h1; simp; exact @h2

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

@[simp] lemma lift_rel_aux.ret_left (R : α → β → Prop)
  (C : computation α → computation β → Prop) (a cb) :
  lift_rel_aux R C (sum.inl a) (destruct cb) ↔ ∃ {b}, b ∈ cb ∧ R a b :=
begin
  apply cb.cases_on (λ b, _) (λ cb, _),
  { exact ⟨λ h, ⟨_, ret_mem _, h⟩, λ ⟨b', mb, h⟩,
    by rw [mem_unique (ret_mem _) mb]; exact h⟩ },
  { rw [destruct_think],
    exact ⟨λ ⟨b, h, r⟩, ⟨b, think_mem h, r⟩,
           λ ⟨b, h, r⟩, ⟨b, of_think_mem h, r⟩⟩ }
end

theorem lift_rel_aux.swap (R : α → β → Prop) (C) (a b) :
  lift_rel_aux (swap R) (swap C) b a = lift_rel_aux R C a b :=
by cases a with a ca; cases b with b cb; simp only [lift_rel_aux]

@[simp] lemma lift_rel_aux.ret_right (R : α → β → Prop)
  (C : computation α → computation β → Prop) (b ca) :
  lift_rel_aux R C (destruct ca) (sum.inl b) ↔ ∃ {a}, a ∈ ca ∧ R a b :=
by rw [←lift_rel_aux.swap, lift_rel_aux.ret_left]

theorem lift_rel_rec.lem {R : α → β → Prop} (C : computation α → computation β → Prop)
  (H : ∀ {ca cb}, C ca cb → lift_rel_aux R C (destruct ca) (destruct cb))
  (ca cb) (Hc : C ca cb) (a) (ha : a ∈ ca) : lift_rel R ca cb :=
begin
  revert cb, refine mem_rec_on ha _ (λ ca' IH, _);
  intros cb Hc; have h := H Hc,
  { simp at h, simp [h] },
  { have h := H Hc, simp, revert h, apply cb.cases_on (λ b, _) (λ cb', _);
    intro h; simp at h; simp [h], exact IH _ h }
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
