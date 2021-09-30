/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.seq.seq
import data.dlist

open function
universes u v w

/-
coinductive wseq (α : Type u) : Type u
| nil : wseq α
| cons : α → wseq α → wseq α
| think : wseq α → wseq α
-/

/-- Weak sequences.

  While the `seq` structure allows for lists which may not be finite,
  a weak sequence also allows the computation of each element to
  involve an indeterminate amount of computation, including possibly
  an infinite loop. This is represented as a regular `seq` interspersed
  with `none` elements to indicate that computation is ongoing.

  This model is appropriate for Haskell style lazy lists, and is closed
  under most interesting computation patterns on infinite lists,
  but conversely it is difficult to extract elements from it. -/
def wseq (α) := seq (option α)

namespace wseq
variables {α : Type u} {β : Type v} {γ : Type w}

/-- Turn a sequence into a weak sequence -/
def of_seq : seq α → wseq α := (<$>) some

/-- Turn a list into a weak sequence -/
def of_list (l : list α) : wseq α := of_seq l

/-- Turn a stream into a weak sequence -/
def of_stream (l : stream α) : wseq α := of_seq l

instance coe_seq : has_coe (seq α) (wseq α) := ⟨of_seq⟩
instance coe_list : has_coe (list α) (wseq α) := ⟨of_list⟩
instance coe_stream : has_coe (stream α) (wseq α) := ⟨of_stream⟩

/-- The empty weak sequence -/
def nil : wseq α := seq.nil

instance : inhabited (wseq α) := ⟨nil⟩

/-- Prepend an element to a weak sequence -/
def cons (a : α) : wseq α → wseq α := seq.cons (some a)

/-- Compute for one tick, without producing any elements -/
def think : wseq α → wseq α := seq.cons none

/-- Destruct a weak sequence, to (eventually possibly) produce either
  `none` for `nil` or `some (a, s)` if an element is produced. -/
def destruct : wseq α → computation (option (α × wseq α)) :=
computation.corec (λs, match seq.destruct s with
  | none              := sum.inl none
  | some (none, s')   := sum.inr s'
  | some (some a, s') := sum.inl (some (a, s'))
  end)

def cases_on {C : wseq α → Sort v} (s : wseq α) (h1 : C nil)
  (h2 : ∀ x s, C (cons x s)) (h3 : ∀ s, C (think s)) : C s :=
seq.cases_on s h1 (λ o, option.cases_on o h3 h2)

protected def mem (a : α) (s : wseq α) := seq.mem (some a) s

instance : has_mem α (wseq α) :=
⟨wseq.mem⟩

theorem not_mem_nil (a : α) : a ∉ @nil α := seq.not_mem_nil a

/-- Get the head of a weak sequence. This involves a possibly
  infinite computation. -/
def head (s : wseq α) : computation (option α) :=
computation.map ((<$>) prod.fst) (destruct s)

/-- Encode a computation yielding a weak sequence into additional
  `think` constructors in a weak sequence -/
def flatten : computation (wseq α) → wseq α :=
seq.corec (λc, match computation.destruct c with
  | sum.inl s := seq.omap return (seq.destruct s)
  | sum.inr c' := some (none, c')
  end)

/-- Get the tail of a weak sequence. This doesn't need a `computation`
  wrapper, unlike `head`, because `flatten` allows us to hide this
  in the construction of the weak sequence itself. -/
def tail (s : wseq α) : wseq α :=
flatten $ (λo, option.rec_on o nil prod.snd) <$> destruct s

/-- drop the first `n` elements from `s`. -/
def drop (s : wseq α) : ℕ → wseq α
| 0     := s
| (n+1) := tail (drop n)
attribute [simp] drop

/-- Get the nth element of `s`. -/
def nth (s : wseq α) (n : ℕ) : computation (option α) := head (drop s n)

/-- Convert `s` to a list (if it is finite and completes in finite time). -/
def to_list (s : wseq α) : computation (list α) :=
@computation.corec (list α) (list α × wseq α) (λ⟨l, s⟩,
  match seq.destruct s with
  | none              := sum.inl l.reverse
  | some (none, s')   := sum.inr (l, s')
  | some (some a, s') := sum.inr (a::l, s')
  end) ([], s)

/-- Get the length of `s` (if it is finite and completes in finite time). -/
def length (s : wseq α) : computation ℕ :=
@computation.corec ℕ (ℕ × wseq α) (λ⟨n, s⟩,
  match seq.destruct s with
  | none              := sum.inl n
  | some (none, s')   := sum.inr (n, s')
  | some (some a, s') := sum.inr (n+1, s')
  end) (0, s)

/-- A weak sequence is finite if `to_list s` terminates. Equivalently,
  it is a finite number of `think` and `cons` applied to `nil`. -/
class is_finite (s : wseq α) : Prop := (out : (to_list s).terminates)

instance to_list_terminates (s : wseq α) [h : is_finite s] : (to_list s).terminates := h.out

/-- Get the list corresponding to a finite weak sequence. -/
def get (s : wseq α) [is_finite s] : list α := (to_list s).get

/-- A weak sequence is *productive* if it never stalls forever - there are
 always a finite number of `think`s between `cons` constructors.
 The sequence itself is allowed to be infinite though. -/
class productive (s : wseq α) : Prop := (nth_terminates : ∀ n, (nth s n).terminates)

theorem productive_iff (s : wseq α) : productive s ↔ ∀ n, (nth s n).terminates :=
⟨λ h, h.1, λ h, ⟨h⟩⟩

instance nth_terminates (s : wseq α) [h : productive s] :
  ∀ n, (nth s n).terminates := h.nth_terminates

instance head_terminates (s : wseq α) [productive s] :
  (head s).terminates := s.nth_terminates 0

/-- Replace the `n`th element of `s` with `a`. -/
def update_nth (s : wseq α) (n : ℕ) (a : α) : wseq α :=
@seq.corec (option α) (ℕ × wseq α) (λ⟨n, s⟩,
  match seq.destruct s, n with
  | none,               n     := none
  | some (none, s'),    n     := some (none, n, s')
  | some (some a', s'), 0     := some (some a', 0, s')
  | some (some a', s'), 1     := some (some a, 0, s')
  | some (some a', s'), (n+2) := some (some a', n+1, s')
  end) (n+1, s)

/-- Remove the `n`th element of `s`. -/
def remove_nth (s : wseq α) (n : ℕ) : wseq α :=
@seq.corec (option α) (ℕ × wseq α) (λ⟨n, s⟩,
  match seq.destruct s, n with
  | none,               n     := none
  | some (none, s'),    n     := some (none, n, s')
  | some (some a', s'), 0     := some (some a', 0, s')
  | some (some a', s'), 1     := some (none, 0, s')
  | some (some a', s'), (n+2) := some (some a', n+1, s')
  end) (n+1, s)

/-- Map the elements of `s` over `f`, removing any values that yield `none`. -/
def filter_map (f : α → option β) : wseq α → wseq β :=
seq.corec (λs, match seq.destruct s with
  | none              := none
  | some (none, s')   := some (none, s')
  | some (some a, s') := some (f a, s')
  end)

/-- Select the elements of `s` that satisfy `p`. -/
def filter (p : α → Prop) [decidable_pred p] : wseq α → wseq α :=
filter_map (λa, if p a then some a else none)

-- example of infinite list manipulations
/-- Get the first element of `s` satisfying `p`. -/
def find (p : α → Prop) [decidable_pred p] (s : wseq α) : computation (option α) :=
head $ filter p s

/-- Zip a function over two weak sequences -/
def zip_with (f : α → β → γ) (s1 : wseq α) (s2 : wseq β) : wseq γ :=
@seq.corec (option γ) (wseq α × wseq β) (λ⟨s1, s2⟩,
  match seq.destruct s1, seq.destruct s2 with
  | some (none, s1'),    some (none, s2')    := some (none, s1', s2')
  | some (some a1, s1'), some (none, s2')    := some (none, s1, s2')
  | some (none, s1'),    some (some a2, s2') := some (none, s1', s2)
  | some (some a1, s1'), some (some a2, s2') := some (some (f a1 a2), s1', s2')
  | _,                   _                   := none
  end) (s1, s2)

/-- Zip two weak sequences into a single sequence of pairs -/
def zip : wseq α → wseq β → wseq (α × β) := zip_with prod.mk

/-- Get the list of indexes of elements of `s` satisfying `p` -/
def find_indexes (p : α → Prop) [decidable_pred p] (s : wseq α) : wseq ℕ :=
(zip s (stream.nats : wseq ℕ)).filter_map
  (λ ⟨a, n⟩, if p a then some n else none)

/-- Get the index of the first element of `s` satisfying `p` -/
def find_index (p : α → Prop) [decidable_pred p] (s : wseq α) : computation ℕ :=
(λ o, option.get_or_else o 0) <$> head (find_indexes p s)

/-- Get the index of the first occurrence of `a` in `s` -/
def index_of [decidable_eq α] (a : α) : wseq α → computation ℕ := find_index (eq a)

/-- Get the indexes of occurrences of `a` in `s` -/
def indexes_of [decidable_eq α] (a : α) : wseq α → wseq ℕ := find_indexes (eq a)

/-- `union s1 s2` is a weak sequence which interleaves `s1` and `s2` in
  some order (nondeterministically). -/
def union (s1 s2 : wseq α) : wseq α :=
@seq.corec (option α) (wseq α × wseq α) (λ⟨s1, s2⟩,
  match seq.destruct s1, seq.destruct s2 with
  | none,                none                := none
  | some (a1, s1'),      none                := some (a1, s1', nil)
  | none,                some (a2, s2')      := some (a2, nil, s2')
  | some (none, s1'),    some (none, s2')    := some (none, s1', s2')
  | some (some a1, s1'), some (none, s2')    := some (some a1, s1', s2')
  | some (none, s1'),    some (some a2, s2') := some (some a2, s1', s2')
  | some (some a1, s1'), some (some a2, s2') := some (some a1, cons a2 s1', s2')
  end) (s1, s2)

/-- Returns `tt` if `s` is `nil` and `ff` if `s` has an element -/
def is_empty (s : wseq α) : computation bool :=
computation.map option.is_none $ head s

/-- Calculate one step of computation -/
def compute (s : wseq α) : wseq α :=
match seq.destruct s with
| some (none, s') := s'
| _               := s
end

/-- Get the first `n` elements of a weak sequence -/
def take (s : wseq α) (n : ℕ) : wseq α :=
@seq.corec (option α) (ℕ × wseq α) (λ⟨n, s⟩,
  match n, seq.destruct s with
  | 0,   _                 := none
  | m+1, none              := none
  | m+1, some (none, s')   := some (none, m+1, s')
  | m+1, some (some a, s') := some (some a, m, s')
  end) (n, s)

/-- Split the sequence at position `n` into a finite initial segment
  and the weak sequence tail -/
def split_at (s : wseq α) (n : ℕ) : computation (list α × wseq α) :=
@computation.corec (list α × wseq α) (ℕ × list α × wseq α) (λ⟨n, l, s⟩,
  match n, seq.destruct s with
  | 0,   _                 := sum.inl (l.reverse, s)
  | m+1, none              := sum.inl (l.reverse, s)
  | m+1, some (none, s')   := sum.inr (n, l, s')
  | m+1, some (some a, s') := sum.inr (m, a::l, s')
  end) (n, [], s)

/-- Returns `tt` if any element of `s` satisfies `p` -/
def any (s : wseq α) (p : α → bool) : computation bool :=
computation.corec (λs : wseq α,
  match seq.destruct s with
  | none              := sum.inl ff
  | some (none, s')   := sum.inr s'
  | some (some a, s') := if p a then sum.inl tt else sum.inr s'
  end) s

/-- Returns `tt` if every element of `s` satisfies `p` -/
def all (s : wseq α) (p : α → bool) : computation bool :=
computation.corec (λs : wseq α,
  match seq.destruct s with
  | none              := sum.inl tt
  | some (none, s')   := sum.inr s'
  | some (some a, s') := if p a then sum.inr s' else sum.inl ff
  end) s

/-- Apply a function to the elements of the sequence to produce a sequence
  of partial results. (There is no `scanr` because this would require
  working from the end of the sequence, which may not exist.) -/
def scanl (f : α → β → α) (a : α) (s : wseq β) : wseq α :=
cons a $ @seq.corec (option α) (α × wseq β) (λ⟨a, s⟩,
  match seq.destruct s with
  | none              := none
  | some (none, s')   := some (none, a, s')
  | some (some b, s') := let a' := f a b in some (some a', a', s')
  end) (a, s)

/-- Get the weak sequence of initial segments of the input sequence -/
def inits (s : wseq α) : wseq (list α) :=
cons [] $ @seq.corec (option (list α)) (dlist α × wseq α) (λ ⟨l, s⟩,
  match seq.destruct s with
  | none              := none
  | some (none, s')   := some (none, l, s')
  | some (some a, s') := let l' := l.concat a in
                         some (some l'.to_list, l', s')
  end) (dlist.empty, s)

/-- Like take, but does not wait for a result. Calculates `n` steps of
  computation and returns the sequence computed so far -/
def collect (s : wseq α) (n : ℕ) : list α :=
(seq.take n s).filter_map id

/-- Append two weak sequences. As with `seq.append`, this may not use
  the second sequence if the first one takes forever to compute -/
def append : wseq α → wseq α → wseq α := seq.append

/-- Map a function over a weak sequence -/
def map (f : α → β) : wseq α → wseq β := seq.map (option.map f)

/-- Flatten a sequence of weak sequences. (Note that this allows
  empty sequences, unlike `seq.join`.) -/
def join (S : wseq (wseq α)) : wseq α :=
seq.join ((λo : option (wseq α), match o with
  | none := seq1.ret none
  | some s := (none, s)
  end) <$> S)

/-- Monadic bind operator for weak sequences -/
def bind (s : wseq α) (f : α → wseq β) : wseq β :=
join (map f s)

@[simp] def lift_rel_o (R : α → β → Prop) (C : wseq α → wseq β → Prop) :
  option (α × wseq α) → option (β × wseq β) → Prop
| none          none          := true
| (some (a, s)) (some (b, t)) := R a b ∧ C s t
| _             _             := false

theorem lift_rel_o.imp {R S : α → β → Prop} {C D : wseq α → wseq β → Prop}
  (H1 : ∀ a b, R a b → S a b) (H2 : ∀ s t, C s t → D s t) :
  ∀ {o p}, lift_rel_o R C o p → lift_rel_o S D o p
| none          none          h := trivial
| (some (a, s)) (some (b, t)) h := and.imp (H1 _ _) (H2 _ _) h
| none          (some _)      h := false.elim h
| (some (_, _)) none          h := false.elim h

theorem lift_rel_o.imp_right (R : α → β → Prop) {C D : wseq α → wseq β → Prop}
  (H : ∀ s t, C s t → D s t) {o p} : lift_rel_o R C o p → lift_rel_o R D o p :=
lift_rel_o.imp (λ _ _, id) H

@[simp] def bisim_o (R : wseq α → wseq α → Prop) :
  option (α × wseq α) → option (α × wseq α) → Prop := lift_rel_o (=) R

theorem bisim_o.imp {R S : wseq α → wseq α → Prop} (H : ∀ s t, R s t → S s t) {o p} :
  bisim_o R o p → bisim_o S o p :=
lift_rel_o.imp_right _ H

/-- Two weak sequences are `lift_rel R` related if they are either both empty,
  or they are both nonempty and the heads are `R` related and the tails are
  `lift_rel R` related. (This is a coinductive definition.) -/
def lift_rel (R : α → β → Prop) (s : wseq α) (t : wseq β) : Prop :=
∃ C : wseq α → wseq β → Prop, C s t ∧
∀ {s t}, C s t → computation.lift_rel (lift_rel_o R C) (destruct s) (destruct t)

/-- If two sequences are equivalent, then they have the same values and
  the same computational behavior (i.e. if one loops forever then so does
  the other), although they may differ in the number of `think`s needed to
  arrive at the answer. -/
def equiv : wseq α → wseq α → Prop := lift_rel (=)

theorem lift_rel_destruct {R : α → β → Prop} {s : wseq α} {t : wseq β} :
  lift_rel R s t →
    computation.lift_rel (lift_rel_o R (lift_rel R)) (destruct s) (destruct t)
| ⟨R, h1, h2⟩ :=
  by refine computation.lift_rel.imp _ _ _ (h2 h1);
     apply lift_rel_o.imp_right; exact λ s' t' h', ⟨R, h', @h2⟩

theorem lift_rel_destruct_iff {R : α → β → Prop} {s : wseq α} {t : wseq β} :
  lift_rel R s t ↔
    computation.lift_rel (lift_rel_o R (lift_rel R)) (destruct s) (destruct t) :=
⟨lift_rel_destruct, λ h, ⟨λ s t, lift_rel R s t ∨
  computation.lift_rel (lift_rel_o R (lift_rel R)) (destruct s) (destruct t),
  or.inr h, λ s t h, begin
    have h : computation.lift_rel (lift_rel_o R (lift_rel R)) (destruct s) (destruct t),
    { cases h with h h, exact lift_rel_destruct h, assumption },
    apply computation.lift_rel.imp _ _ _ h,
    intros a b, apply lift_rel_o.imp_right,
    intros s t, apply or.inl
  end⟩⟩

infix ` ~ `:50 := equiv

theorem destruct_congr {s t : wseq α} :
  s ~ t → computation.lift_rel (bisim_o (~)) (destruct s) (destruct t) :=
lift_rel_destruct

theorem destruct_congr_iff {s t : wseq α} :
  s ~ t ↔ computation.lift_rel (bisim_o (~)) (destruct s) (destruct t) :=
lift_rel_destruct_iff

theorem lift_rel.refl (R : α → α → Prop) (H : reflexive R) : reflexive (lift_rel R) :=
λ s, begin
  refine ⟨(=), rfl, λ s t (h : s = t), _⟩,
  rw ←h, apply computation.lift_rel.refl,
  intro a, cases a with a, simp, cases a; simp, apply H
end

theorem lift_rel_o.swap (R : α → β → Prop) (C) :
  swap (lift_rel_o R C) = lift_rel_o (swap R) (swap C) :=
by funext x y; cases x with x; [skip, cases x]; { cases y with y; [skip, cases y]; refl }

theorem lift_rel.swap_lem {R : α → β → Prop} {s1 s2} (h : lift_rel R s1 s2) :
  lift_rel (swap R) s2 s1 :=
begin
  refine ⟨swap (lift_rel R), h, λ s t (h : lift_rel R t s), _⟩,
  rw [←lift_rel_o.swap, computation.lift_rel.swap],
  apply lift_rel_destruct h
end

theorem lift_rel.swap (R : α → β → Prop) :
  swap (lift_rel R) = lift_rel (swap R) :=
funext $ λ x, funext $ λ y, propext ⟨lift_rel.swap_lem, lift_rel.swap_lem⟩

theorem lift_rel.symm (R : α → α → Prop) (H : symmetric R) : symmetric (lift_rel R) :=
λ s1 s2 (h : swap (lift_rel R) s2 s1),
by rwa [lift_rel.swap, show swap R = R, from
        funext $ λ a, funext $ λ b, propext $ by constructor; apply H] at h

theorem lift_rel.trans (R : α → α → Prop) (H : transitive R) : transitive (lift_rel R) :=
λ s t u h1 h2, begin
  refine ⟨λ s u, ∃ t, lift_rel R s t ∧ lift_rel R t u, ⟨t, h1, h2⟩, λ s u h, _⟩,
  rcases h with ⟨t, h1, h2⟩,
  have h1 := lift_rel_destruct h1,
  have h2 := lift_rel_destruct h2,
  refine computation.lift_rel_def.2
    ⟨(computation.terminates_of_lift_rel h1).trans
     (computation.terminates_of_lift_rel h2), λ a c ha hc, _⟩,
  rcases h1.left ha with ⟨b, hb, t1⟩,
  have t2 := computation.rel_of_lift_rel h2 hb hc,
  cases a with a; cases c with c,
  { trivial },
  { cases b, {cases t2}, {cases t1} },
  { cases a, cases b with b, {cases t1}, {cases b, cases t2} },
  { cases a with a s, cases b with b, {cases t1},
    cases b with b t, cases c with c u,
    cases t1 with ab st, cases t2 with bc tu,
    exact ⟨H ab bc, t, st, tu⟩ }
end

theorem lift_rel.equiv (R : α → α → Prop) : equivalence R → equivalence (lift_rel R)
| ⟨refl, symm, trans⟩ :=
  ⟨lift_rel.refl R refl, lift_rel.symm R symm, lift_rel.trans R trans⟩

@[refl] theorem equiv.refl : ∀ (s : wseq α), s ~ s :=
lift_rel.refl (=) eq.refl

@[symm] theorem equiv.symm : ∀ {s t : wseq α}, s ~ t → t ~ s :=
lift_rel.symm (=) (@eq.symm _)

@[trans] theorem equiv.trans : ∀ {s t u : wseq α}, s ~ t → t ~ u → s ~ u :=
lift_rel.trans (=) (@eq.trans _)

theorem equiv.equivalence : equivalence (@equiv α) :=
⟨@equiv.refl _, @equiv.symm _, @equiv.trans _⟩

open computation
local notation `return` := computation.return

@[simp] theorem destruct_nil : destruct (nil : wseq α) = return none :=
computation.destruct_eq_ret rfl

@[simp] theorem destruct_cons (a : α) (s) : destruct (cons a s) = return (some (a, s)) :=
computation.destruct_eq_ret $ by simp [destruct, cons, computation.rmap]

@[simp] theorem destruct_think (s : wseq α) : destruct (think s) = (destruct s).think :=
computation.destruct_eq_think $ by simp [destruct, think, computation.rmap]

@[simp] theorem seq_destruct_nil : seq.destruct (nil : wseq α) = none :=
seq.destruct_nil

@[simp] theorem seq_destruct_cons (a : α) (s) : seq.destruct (cons a s) = some (some a, s) :=
seq.destruct_cons _ _

@[simp] theorem seq_destruct_think (s : wseq α) : seq.destruct (think s) = some (none, s) :=
seq.destruct_cons _ _

@[simp] theorem head_nil : head (nil : wseq α) = return none := by simp [head]; refl
@[simp] theorem head_cons (a : α) (s) : head (cons a s) = return (some a) := by simp [head]; refl
@[simp] theorem head_think (s : wseq α) : head (think s) = (head s).think := by simp [head]; refl

@[simp] theorem flatten_ret (s : wseq α) : flatten (return s) = s :=
begin
  refine seq.eq_of_bisim (λs1 s2, flatten (return s2) = s1) _ rfl,
  intros s' s h, rw ←h, simp [flatten],
  cases seq.destruct s, { simp },
  { cases val with o s', simp }
end

@[simp] theorem flatten_think (c : computation (wseq α)) : flatten c.think = think (flatten c) :=
seq.destruct_eq_cons $ by simp [flatten, think]

@[simp]
theorem destruct_flatten (c : computation (wseq α)) : destruct (flatten c) = c >>= destruct :=
begin
  refine computation.eq_of_bisim (λc1 c2, c1 = c2 ∨
    ∃ c, c1 = destruct (flatten c) ∧ c2 = computation.bind c destruct) _ (or.inr ⟨c, rfl, rfl⟩),
  intros c1 c2 h, exact match c1, c2, h with
  | _, _, (or.inl $ eq.refl c) := by cases c.destruct; simp
  | _, _, (or.inr ⟨c, rfl, rfl⟩) := begin
    apply c.cases_on (λa, _) (λc', _); repeat {simp},
    { cases (destruct a).destruct; simp },
    { exact or.inr ⟨c', rfl, rfl⟩ }
  end end
end

theorem head_terminates_iff (s : wseq α) : terminates (head s) ↔ terminates (destruct s) :=
terminates_map_iff _ (destruct s)

@[simp] theorem tail_nil : tail (nil : wseq α) = nil := by simp [tail]
@[simp] theorem tail_cons (a : α) (s) : tail (cons a s) = s := by simp [tail]
@[simp] theorem tail_think (s : wseq α) : tail (think s) = (tail s).think := by simp [tail]

@[simp] theorem dropn_nil (n) :
  drop (nil : wseq α) n = nil := by induction n; simp [*, drop]
@[simp] theorem dropn_cons (a : α) (s) (n) :
  drop (cons a s) (n+1) = drop s n := by induction n; simp [*, drop]
@[simp] theorem dropn_think (s : wseq α) (n) :
  drop (think s) n = (drop s n).think := by induction n; simp [*, drop]

theorem dropn_add (s : wseq α) (m) : ∀ n, drop s (m + n) = drop (drop s m) n
| 0     := rfl
| (n+1) := congr_arg tail (dropn_add n)

theorem dropn_tail (s : wseq α) (n) : drop (tail s) n = drop s (n + 1) :=
by rw add_comm; symmetry; apply dropn_add

theorem nth_add (s : wseq α) (m n) : nth s (m + n) = nth (drop s m) n :=
congr_arg head (dropn_add _ _ _)

theorem nth_tail (s : wseq α) (n) : nth (tail s) n = nth s (n + 1) :=
congr_arg head (dropn_tail _ _)

@[simp] theorem join_nil : join nil = (nil : wseq α) := seq.join_nil

@[simp] theorem join_think (S : wseq (wseq α)) :
  join (think S) = think (join S) :=
by { simp [think, join], unfold functor.map, simp [join, seq1.ret] }

@[simp] theorem join_cons (s : wseq α) (S) :
  join (cons s S) = think (append s (join S)) :=
by { simp [think, join], unfold functor.map, simp [join, cons, append] }

@[simp] theorem nil_append (s : wseq α) : append nil s = s := seq.nil_append _

@[simp] theorem cons_append (a : α) (s t) :
  append (cons a s) t = cons a (append s t) := seq.cons_append _ _ _

@[simp] theorem think_append (s t : wseq α) :
  append (think s) t = think (append s t) := seq.cons_append _ _ _

@[simp] theorem append_nil (s : wseq α) : append s nil = s := seq.append_nil _

@[simp] theorem append_assoc (s t u : wseq α) :
  append (append s t) u = append s (append t u) := seq.append_assoc _ _ _

@[simp] def tail.aux : option (α × wseq α) → computation (option (α × wseq α))
| none          := return none
| (some (a, s)) := destruct s

theorem destruct_tail (s : wseq α) :
  destruct (tail s) = destruct s >>= tail.aux :=
begin
  simp [tail], rw [← bind_pure_comp_eq_map, is_lawful_monad.bind_assoc],
  apply congr_arg, ext1 (_|⟨a, s⟩);
  apply (@pure_bind computation _ _ _ _ _ _).trans _; simp
end

@[simp] def drop.aux : ℕ → option (α × wseq α) → computation (option (α × wseq α))
| 0     := return
| (n+1) := λ a, tail.aux a >>= drop.aux n

theorem drop.aux_none : ∀ n, @drop.aux α n none = return none
| 0     := rfl
| (n+1) := show computation.bind (return none) (drop.aux n) = return none,
           by rw [ret_bind, drop.aux_none]

theorem destruct_dropn :
  ∀ (s : wseq α) n, destruct (drop s n) = destruct s >>= drop.aux n
| s 0     := (bind_ret' _).symm
| s (n+1) := by rw [← dropn_tail, destruct_dropn _ n,
  destruct_tail, is_lawful_monad.bind_assoc]; refl

theorem head_terminates_of_head_tail_terminates (s : wseq α) [T : terminates (head (tail s))] :
  terminates (head s) :=
(head_terminates_iff _).2 $ begin
  rcases (head_terminates_iff _).1 T with ⟨⟨a, h⟩⟩,
  simp [tail] at h,
  rcases exists_of_mem_bind h with ⟨s', h1, h2⟩,
  unfold functor.map at h1,
  exact let ⟨t, h3, h4⟩ := exists_of_mem_map h1 in terminates_of_mem h3
end

theorem destruct_some_of_destruct_tail_some {s : wseq α} {a}
  (h : some a ∈ destruct (tail s)) : ∃ a', some a' ∈ destruct s :=
begin
  unfold tail functor.map at h, simp at h,
  rcases exists_of_mem_bind h with ⟨t, tm, td⟩, clear h,
  rcases exists_of_mem_map tm with ⟨t', ht', ht2⟩, clear tm,
  cases t' with t'; rw ←ht2 at td; simp at td,
  { have := mem_unique td (ret_mem _), contradiction },
  { exact ⟨_, ht'⟩ }
end

theorem head_some_of_head_tail_some {s : wseq α} {a}
  (h : some a ∈ head (tail s)) : ∃ a', some a' ∈ head s :=
begin
  unfold head at h,
  rcases exists_of_mem_map h with ⟨o, md, e⟩, clear h,
  cases o with o; injection e with h', clear e h',
  cases destruct_some_of_destruct_tail_some md with a am,
  exact ⟨_, mem_map ((<$>) (@prod.fst α (wseq α))) am⟩
end

theorem head_some_of_nth_some {s : wseq α} {a n}
  (h : some a ∈ nth s n) : ∃ a', some a' ∈ head s :=
begin
  revert a, induction n with n IH; intros,
  exacts [⟨_, h⟩, let ⟨a', h'⟩ := head_some_of_head_tail_some h in IH h']
end

instance productive_tail (s : wseq α) [productive s] : productive (tail s) :=
⟨λ n, by rw [nth_tail]; apply_instance⟩

instance productive_dropn (s : wseq α) [productive s] (n) : productive (drop s n) :=
⟨λ m, by rw [←nth_add]; apply_instance⟩

/-- Given a productive weak sequence, we can collapse all the `think`s to
  produce a sequence. -/
def to_seq (s : wseq α) [productive s] : seq α :=
⟨λ n, (nth s n).get, λn h,
begin
  cases e : computation.get (nth s (n + 1)), {assumption},
  have := mem_of_get_eq _ e,
  simp [nth] at this h, cases head_some_of_head_tail_some this with a' h',
  have := mem_unique h' (@mem_of_get_eq _ _ _ _ h),
  contradiction
end⟩

theorem nth_terminates_le {s : wseq α} {m n} (h : m ≤ n) :
  terminates (nth s n) → terminates (nth s m) :=
by induction h with m' h IH; [exact id,
  exact λ T, IH (@head_terminates_of_head_tail_terminates _ _ T)]

theorem head_terminates_of_nth_terminates {s : wseq α} {n} :
  terminates (nth s n) → terminates (head s) :=
nth_terminates_le (nat.zero_le n)

theorem destruct_terminates_of_nth_terminates {s : wseq α} {n} (T : terminates (nth s n)) :
  terminates (destruct s) :=
(head_terminates_iff _).1 $ head_terminates_of_nth_terminates T

theorem mem_rec_on {C : wseq α → Prop} {a s} (M : a ∈ s)
  (h1 : ∀ b s', (a = b ∨ C s') → C (cons b s'))
  (h2 : ∀ s, C s → C (think s)) : C s :=
begin
  apply seq.mem_rec_on M,
  intros o s' h, cases o with b,
  { apply h2, cases h, {contradiction}, {assumption} },
  { apply h1, apply or.imp_left _ h, intro h, injection h }
end

@[simp] theorem mem_think (s : wseq α) (a) : a ∈ think s ↔ a ∈ s :=
begin
  cases s with f al,
  change some (some a) ∈ some none :: f ↔ some (some a) ∈ f,
  constructor; intro h,
  { apply (stream.eq_or_mem_of_mem_cons h).resolve_left,
    intro, injections },
  { apply stream.mem_cons_of_mem _ h }
end

theorem eq_or_mem_iff_mem {s : wseq α} {a a' s'} :
  some (a', s') ∈ destruct s → (a ∈ s ↔ a = a' ∨ a ∈ s') :=
begin
  generalize e : destruct s = c, intro h,
  revert s, apply computation.mem_rec_on h _ (λ c IH, _); intro s;
  apply s.cases_on _ (λ x s, _) (λ s, _); intros m;
  have := congr_arg computation.destruct m; simp at this;
  cases this with i1 i2,
  { rw [i1, i2],
    cases s' with f al,
    unfold cons has_mem.mem wseq.mem seq.mem seq.cons, simp,
    have h_a_eq_a' : a = a' ↔ some (some a) = some (some a'), {simp},
    rw [h_a_eq_a'],
    refine ⟨stream.eq_or_mem_of_mem_cons, λo, _⟩,
    { cases o with e m,
      { rw e, apply stream.mem_cons },
      { exact stream.mem_cons_of_mem _ m } } },
  { simp, exact IH this }
end

@[simp] theorem mem_cons_iff (s : wseq α) (b) {a} : a ∈ cons b s ↔ a = b ∨ a ∈ s :=
eq_or_mem_iff_mem $ by simp [ret_mem]

theorem mem_cons_of_mem {s : wseq α} (b) {a} (h : a ∈ s) : a ∈ cons b s :=
(mem_cons_iff _ _).2 (or.inr h)

theorem mem_cons (s : wseq α) (a) : a ∈ cons a s :=
(mem_cons_iff _ _).2 (or.inl rfl)

theorem mem_of_mem_tail {s : wseq α} {a} : a ∈ tail s → a ∈ s :=
begin
  intro h, have := h, cases h with n e, revert s, simp [stream.nth],
  induction n with n IH; intro s; apply s.cases_on _ (λx s, _) (λ s, _);
    repeat{simp}; intros m e; injections,
  { exact or.inr m },
  { exact or.inr m },
  { apply IH m, rw e, cases tail s, refl }
end

theorem mem_of_mem_dropn {s : wseq α} {a} : ∀ {n}, a ∈ drop s n → a ∈ s
| 0     h := h
| (n+1) h := @mem_of_mem_dropn n (mem_of_mem_tail h)

theorem nth_mem {s : wseq α} {a n} : some a ∈ nth s n → a ∈ s :=
begin
  revert s, induction n with n IH; intros s h,
  { rcases exists_of_mem_map h with ⟨o, h1, h2⟩,
    cases o with o; injection h2 with h',
    cases o with a' s',
    exact (eq_or_mem_iff_mem h1).2 (or.inl h'.symm) },
  { have := @IH (tail s), rw nth_tail at this,
    exact mem_of_mem_tail (this h) }
end

theorem exists_nth_of_mem {s : wseq α} {a} (h : a ∈ s) : ∃ n, some a ∈ nth s n :=
begin
  apply mem_rec_on h,
  { intros a' s' h, cases h with h h,
    { existsi 0, simp [nth], rw h, apply ret_mem },
    { cases h with n h, existsi n+1,
      simp [nth], exact h } },
  { intros s' h, cases h with n h,
    existsi n, simp [nth], apply think_mem h }
end

theorem exists_dropn_of_mem {s : wseq α} {a} (h : a ∈ s) :
  ∃ n s', some (a, s') ∈ destruct (drop s n) :=
let ⟨n, h⟩ := exists_nth_of_mem h in ⟨n, begin
  rcases (head_terminates_iff _).1 ⟨⟨_, h⟩⟩ with ⟨⟨o, om⟩⟩,
  have := mem_unique (mem_map _ om) h,
  cases o with o; injection this with i,
  cases o with a' s', dsimp at i,
  rw i at om, exact ⟨_, om⟩
end⟩

theorem lift_rel_dropn_destruct {R : α → β → Prop} {s t} (H : lift_rel R s t) :
  ∀ n, computation.lift_rel (lift_rel_o R (lift_rel R))
    (destruct (drop s n)) (destruct (drop t n))
| 0     := lift_rel_destruct H
| (n+1) := begin
  simp [destruct_tail],
  apply lift_rel_bind,
  apply lift_rel_dropn_destruct n,
  exact λ a b o, match a, b, o with
  | none,       none,         _        := by simp
  | some (a, s), some (b, t), ⟨h1, h2⟩ := by simp [tail.aux]; apply lift_rel_destruct h2
  end
end

theorem exists_of_lift_rel_left {R : α → β → Prop} {s t}
  (H : lift_rel R s t) {a} (h : a ∈ s) : ∃ {b}, b ∈ t ∧ R a b :=
let ⟨n, h⟩ := exists_nth_of_mem h,
    ⟨some (._, s'), sd, rfl⟩ := exists_of_mem_map h,
    ⟨some (b, t'), td, ⟨ab, _⟩⟩ := (lift_rel_dropn_destruct H n).left sd in
⟨b, nth_mem (mem_map ((<$>) prod.fst.{v v}) td), ab⟩

theorem exists_of_lift_rel_right {R : α → β → Prop} {s t}
  (H : lift_rel R s t) {b} (h : b ∈ t) : ∃ {a}, a ∈ s ∧ R a b :=
by rw ←lift_rel.swap at H; exact exists_of_lift_rel_left H h

theorem head_terminates_of_mem {s : wseq α} {a} (h : a ∈ s) : terminates (head s) :=
let ⟨n, h⟩ := exists_nth_of_mem h in head_terminates_of_nth_terminates ⟨⟨_, h⟩⟩

theorem of_mem_append {s₁ s₂ : wseq α} {a : α} : a ∈ append s₁ s₂ → a ∈ s₁ ∨ a ∈ s₂ :=
seq.of_mem_append

theorem mem_append_left {s₁ s₂ : wseq α} {a : α} : a ∈ s₁ → a ∈ append s₁ s₂ :=
seq.mem_append_left

theorem exists_of_mem_map {f} {b : β} : ∀ {s : wseq α}, b ∈ map f s → ∃ a, a ∈ s ∧ f a = b
| ⟨g, al⟩ h := let ⟨o, om, oe⟩ := seq.exists_of_mem_map h in
  by cases o with a; injection oe with h'; exact ⟨a, om, h'⟩

@[simp] theorem lift_rel_nil (R : α → β → Prop) : lift_rel R nil nil :=
by rw [lift_rel_destruct_iff]; simp

@[simp] theorem lift_rel_cons (R : α → β → Prop) (a b s t) :
  lift_rel R (cons a s) (cons b t) ↔ R a b ∧ lift_rel R s t :=
by rw [lift_rel_destruct_iff]; simp

@[simp] theorem lift_rel_think_left (R : α → β → Prop) (s t) :
  lift_rel R (think s) t ↔ lift_rel R s t :=
by rw [lift_rel_destruct_iff, lift_rel_destruct_iff]; simp

@[simp] theorem lift_rel_think_right (R : α → β → Prop) (s t) :
  lift_rel R s (think t) ↔ lift_rel R s t :=
by rw [lift_rel_destruct_iff, lift_rel_destruct_iff]; simp

theorem cons_congr {s t : wseq α} (a : α) (h : s ~ t) : cons a s ~ cons a t :=
by unfold equiv; simp; exact h

theorem think_equiv (s : wseq α) : think s ~ s :=
by unfold equiv; simp; apply equiv.refl

theorem think_congr {s t : wseq α} (a : α) (h : s ~ t) : think s ~ think t :=
by unfold equiv; simp; exact h

theorem head_congr : ∀ {s t : wseq α}, s ~ t → head s ~ head t :=
suffices ∀ {s t : wseq α}, s ~ t → ∀ {o}, o ∈ head s → o ∈ head t, from
λ s t h o, ⟨this h, this h.symm⟩,
begin
  intros s t h o ho,
  rcases @computation.exists_of_mem_map _ _ _ _ (destruct s) ho with ⟨ds, dsm, dse⟩,
  rw ←dse,
  cases destruct_congr h with l r,
  rcases l dsm with ⟨dt, dtm, dst⟩,
  cases ds with a; cases dt with b,
  { apply mem_map _ dtm },
  { cases b, cases dst },
  { cases a, cases dst },
  { cases a with a s', cases b with b t', rw dst.left,
    exact @mem_map _ _ (@functor.map _ _ (α × wseq α) _ prod.fst)
      _ (destruct t) dtm }
end

theorem flatten_equiv {c : computation (wseq α)} {s} (h : s ∈ c) : flatten c ~ s :=
begin
  apply computation.mem_rec_on h, { simp },
  { intro s', apply equiv.trans, simp [think_equiv] }
end

theorem lift_rel_flatten {R : α → β → Prop} {c1 : computation (wseq α)} {c2 : computation (wseq β)}
  (h : c1.lift_rel (lift_rel R) c2) : lift_rel R (flatten c1) (flatten c2) :=
let S := λ s t,
  ∃ c1 c2, s = flatten c1 ∧ t = flatten c2 ∧ computation.lift_rel (lift_rel R) c1 c2 in
⟨S, ⟨c1, c2, rfl, rfl, h⟩, λ s t h,
  match s, t, h with ._, ._, ⟨c1, c2, rfl, rfl, h⟩ := begin
    simp, apply lift_rel_bind _ _ h,
    intros a b ab, apply computation.lift_rel.imp _ _ _ (lift_rel_destruct ab),
    intros a b, apply lift_rel_o.imp_right,
    intros s t h, refine ⟨return s, return t, _, _, _⟩; simp [h]
  end end⟩

theorem flatten_congr {c1 c2 : computation (wseq α)} :
  computation.lift_rel equiv c1 c2 → flatten c1 ~ flatten c2 := lift_rel_flatten

theorem tail_congr {s t : wseq α} (h : s ~ t) : tail s ~ tail t :=
begin
  apply flatten_congr,
  unfold functor.map, rw [←bind_ret, ←bind_ret],
  apply lift_rel_bind _ _ (destruct_congr h),
  intros a b h, simp,
  cases a with a; cases b with b,
  { trivial },
  { cases h },
  { cases a, cases h },
  { cases a with a s', cases b with b t', exact h.right }
end

theorem dropn_congr {s t : wseq α} (h : s ~ t) (n) : drop s n ~ drop t n :=
by induction n; simp [*, tail_congr]

theorem nth_congr {s t : wseq α} (h : s ~ t) (n) : nth s n ~ nth t n :=
head_congr (dropn_congr h _)

theorem mem_congr {s t : wseq α} (h : s ~ t) (a) : a ∈ s ↔ a ∈ t :=
suffices ∀ {s t : wseq α}, s ~ t → a ∈ s → a ∈ t, from ⟨this h, this h.symm⟩,
λ s t h as, let ⟨n, hn⟩ := exists_nth_of_mem as in
nth_mem ((nth_congr h _ _).1 hn)

theorem productive_congr {s t : wseq α} (h : s ~ t) : productive s ↔ productive t :=
by simp only [productive_iff]; exact
  forall_congr (λ n, terminates_congr $ nth_congr h _)

theorem equiv.ext {s t : wseq α} (h : ∀ n, nth s n ~ nth t n) : s ~ t :=
⟨λ s t, ∀ n, nth s n ~ nth t n, h, λs t h, begin
  refine lift_rel_def.2 ⟨_, _⟩,
  { rw [←head_terminates_iff, ←head_terminates_iff],
    exact terminates_congr (h 0) },
  { intros a b ma mb,
    cases a with a; cases b with b,
    { trivial },
    { injection mem_unique (mem_map _ ma) ((h 0 _).2 (mem_map _ mb)) },
    { injection mem_unique (mem_map _ ma) ((h 0 _).2 (mem_map _ mb)) },
    { cases a with a s', cases b with b t',
      injection mem_unique (mem_map _ ma) ((h 0 _).2 (mem_map _ mb)) with ab,
      refine ⟨ab, λ n, _⟩,
      refine (nth_congr (flatten_equiv (mem_map _ ma)) n).symm.trans
        ((_ : nth (tail s) n ~ nth (tail t) n).trans
        (nth_congr (flatten_equiv (mem_map _ mb)) n)),
      rw [nth_tail, nth_tail], apply h } }
end⟩

theorem length_eq_map (s : wseq α) : length s = computation.map list.length (to_list s) :=
begin
  refine eq_of_bisim
    (λ c1 c2, ∃ (l : list α) (s : wseq α),
      c1 = corec length._match_2 (l.length, s) ∧
      c2 = computation.map list.length (corec to_list._match_2 (l, s)))
    _ ⟨[], s, rfl, rfl⟩,
  intros s1 s2 h, rcases h with ⟨l, s, h⟩, rw [h.left, h.right],
  apply s.cases_on _ (λ a s, _) (λ s, _);
    repeat {simp [to_list, nil, cons, think, length]},
  { refine ⟨a::l, s, _, _⟩; simp },
  { refine ⟨l, s, _, _⟩; simp }
end

@[simp] theorem of_list_nil : of_list [] = (nil : wseq α) := rfl

@[simp] theorem of_list_cons (a : α) (l) :
  of_list (a :: l) = cons a (of_list l) :=
show seq.map some (seq.of_list (a :: l)) =
     seq.cons (some a) (seq.map some (seq.of_list l)), by simp

@[simp] theorem to_list'_nil (l : list α) :
  corec to_list._match_2 (l, nil) = return l.reverse :=
destruct_eq_ret rfl

@[simp] theorem to_list'_cons (l : list α) (s : wseq α) (a : α) :
  corec to_list._match_2 (l, cons a s) =
  (corec to_list._match_2 (a::l, s)).think :=
destruct_eq_think $ by simp [to_list, cons]

@[simp] theorem to_list'_think (l : list α) (s : wseq α) :
  corec to_list._match_2 (l, think s) =
  (corec to_list._match_2 (l, s)).think :=
destruct_eq_think $ by simp [to_list, think]

theorem to_list'_map (l : list α) (s : wseq α) :
  corec to_list._match_2 (l, s) =
  ((++) l.reverse) <$> to_list s :=
begin
  refine eq_of_bisim
    (λ c1 c2, ∃ (l' : list α) (s : wseq α),
      c1 = corec to_list._match_2 (l' ++ l, s) ∧
      c2 = computation.map ((++) l.reverse) (corec to_list._match_2 (l', s)))
    _ ⟨[], s, rfl, rfl⟩,
  intros s1 s2 h, rcases h with ⟨l', s, h⟩, rw [h.left, h.right],
  apply s.cases_on _ (λ a s, _) (λ s, _);
    repeat {simp [to_list, nil, cons, think, length]},
  { refine ⟨a::l', s, _, _⟩; simp },
  { refine ⟨l', s, _, _⟩; simp }
end

@[simp] theorem to_list_cons (a : α) (s) :
  to_list (cons a s) = (list.cons a <$> to_list s).think :=
destruct_eq_think $ by unfold to_list; simp; rw to_list'_map; simp; refl

@[simp] theorem to_list_nil : to_list (nil : wseq α) = return [] :=
destruct_eq_ret rfl

theorem to_list_of_list (l : list α) : l ∈ to_list (of_list l) :=
by induction l with a l IH; simp [ret_mem]; exact think_mem (mem_map _ IH)

@[simp] theorem destruct_of_seq (s : seq α) :
  destruct (of_seq s) = return (s.head.map $ λ a, (a, of_seq s.tail)) :=
destruct_eq_ret $ begin
  simp [of_seq, head, destruct, seq.destruct, seq.head],
  rw [show seq.nth (some <$> s) 0 = some <$> seq.nth s 0, by apply seq.map_nth],
  cases seq.nth s 0 with a, { refl },
  unfold functor.map,
  simp [destruct]
end

@[simp] theorem head_of_seq (s : seq α) : head (of_seq s) = return s.head :=
by simp [head]; cases seq.head s; refl

@[simp] theorem tail_of_seq (s : seq α) : tail (of_seq s) = of_seq s.tail :=
begin
  simp [tail], apply s.cases_on _ (λ x s, _); simp [of_seq], {refl},
  rw [seq.head_cons, seq.tail_cons], refl
end

@[simp] theorem dropn_of_seq (s : seq α) : ∀ n, drop (of_seq s) n = of_seq (s.drop n)
| 0 := rfl
| (n+1) := by dsimp [drop]; rw [dropn_of_seq, tail_of_seq]

theorem nth_of_seq (s : seq α) (n) : nth (of_seq s) n = return (seq.nth s n) :=
by dsimp [nth]; rw [dropn_of_seq, head_of_seq, seq.head_dropn]

instance productive_of_seq (s : seq α) : productive (of_seq s) :=
⟨λ n, by rw nth_of_seq; apply_instance⟩

theorem to_seq_of_seq (s : seq α) : to_seq (of_seq s) = s :=
begin
  apply subtype.eq, funext n,
  dsimp [to_seq], apply get_eq_of_mem,
  rw nth_of_seq, apply ret_mem
end

/-- The monadic `return a` is a singleton list containing `a`. -/
def ret (a : α) : wseq α := of_list [a]

@[simp] theorem map_nil (f : α → β) : map f nil = nil := rfl

@[simp] theorem map_cons (f : α → β) (a s) :
  map f (cons a s) = cons (f a) (map f s) := seq.map_cons _ _ _

@[simp] theorem map_think (f : α → β) (s) :
  map f (think s) = think (map f s) := seq.map_cons _ _ _

@[simp] theorem map_id (s : wseq α) : map id s = s := by simp [map]

@[simp] theorem map_ret (f : α → β) (a) : map f (ret a) = ret (f a) := by simp [ret]

@[simp] theorem map_append (f : α → β) (s t) : map f (append s t) = append (map f s) (map f t) :=
seq.map_append _ _ _

theorem map_comp (f : α → β) (g : β → γ) (s : wseq α) :
  map (g ∘ f) s = map g (map f s) :=
begin
  dsimp [map], rw ←seq.map_comp,
  apply congr_fun, apply congr_arg,
  ext ⟨⟩; refl
end

theorem mem_map (f : α → β) {a : α} {s : wseq α} : a ∈ s → f a ∈ map f s :=
seq.mem_map (option.map f)

-- The converse is not true without additional assumptions
theorem exists_of_mem_join {a : α} : ∀ {S : wseq (wseq α)}, a ∈ join S → ∃ s, s ∈ S ∧ a ∈ s :=
suffices ∀ ss : wseq α, a ∈ ss → ∀ s S, append s (join S) = ss →
  a ∈ append s (join S) → a ∈ s ∨ ∃ s, s ∈ S ∧ a ∈ s, from λ S h,
  (this _ h nil S (by simp) (by simp [h])).resolve_left (not_mem_nil _),
begin
  intros ss h, apply mem_rec_on h (λ b ss o, _) (λ ss IH, _); intros s S,
  { refine s.cases_on (S.cases_on _ (λ s S, _) (λ S, _)) (λ b' s, _) (λ s, _);
    intros ej m; simp at ej;
    have := congr_arg seq.destruct ej; simp at this;
    try {cases this}; try {contradiction},
    substs b' ss,
    simp at m ⊢,
    cases o with e IH, { simp [e] },
    cases m with e m, { simp [e] },
    exact or.imp_left or.inr (IH _ _ rfl m) },
  { refine s.cases_on (S.cases_on _ (λ s S, _) (λ S, _)) (λ b' s, _) (λ s, _);
    intros ej m; simp at ej;
    have := congr_arg seq.destruct ej; simp at this;
    try { try {have := this.1}, contradiction }; subst ss,
    { apply or.inr, simp at m ⊢,
      cases IH s S rfl m with as ex,
      { exact ⟨s, or.inl rfl, as⟩ },
      { rcases ex with ⟨s', sS, as⟩,
        exact ⟨s', or.inr sS, as⟩ } },
    { apply or.inr, simp at m,
      rcases (IH nil S (by simp) (by simp [m])).resolve_left (not_mem_nil _) with ⟨s, sS, as⟩,
      exact ⟨s, by simp [sS], as⟩ },
    { simp at m IH ⊢, apply IH _ _ rfl m } }
end

theorem exists_of_mem_bind {s : wseq α} {f : α → wseq β} {b}
  (h : b ∈ bind s f) : ∃ a ∈ s, b ∈ f a :=
let ⟨t, tm, bt⟩ := exists_of_mem_join h,
    ⟨a, as, e⟩ := exists_of_mem_map tm in ⟨a, as, by rwa e⟩

theorem destruct_map (f : α → β) (s : wseq α) :
  destruct (map f s) = computation.map (option.map (prod.map f (map f))) (destruct s) :=
begin
  apply eq_of_bisim (λ c1 c2, ∃ s, c1 = destruct (map f s) ∧
    c2 = computation.map (option.map (prod.map f (map f))) (destruct s)),
  { intros c1 c2 h, cases h with s h, rw [h.left, h.right],
    apply s.cases_on _ (λ a s, _) (λ s, _); simp,
    exact ⟨s, rfl, rfl⟩ },
  { exact ⟨s, rfl, rfl⟩ }
end

theorem lift_rel_map {δ} (R : α → β → Prop) (S : γ → δ → Prop)
  {s1 : wseq α} {s2 : wseq β}
  {f1 : α → γ} {f2 : β → δ}
  (h1 : lift_rel R s1 s2) (h2 : ∀ {a b}, R a b → S (f1 a) (f2 b))
  : lift_rel S (map f1 s1) (map f2 s2) :=
⟨λ s1 s2, ∃ s t, s1 = map f1 s ∧ s2 = map f2 t ∧ lift_rel R s t,
⟨s1, s2, rfl, rfl, h1⟩,
λ s1 s2 h, match s1, s2, h with ._, ._, ⟨s, t, rfl, rfl, h⟩ := begin
  simp [destruct_map], apply computation.lift_rel_map _ _ (lift_rel_destruct h),
  intros o p h,
  cases o with a; cases p with b; simp,
  { cases b; cases h },
  { cases a; cases h },
  { cases a with a s; cases b with b t, cases h with r h,
    exact ⟨h2 r, s, rfl, t, rfl, h⟩ }
end end⟩

theorem map_congr (f : α → β) {s t : wseq α} (h : s ~ t) : map f s ~ map f t :=
lift_rel_map _ _ h (λ _ _, congr_arg _)

@[simp] def destruct_append.aux (t : wseq α) :
  option (α × wseq α) → computation (option (α × wseq α))
| none          := destruct t
| (some (a, s)) := return (some (a, append s t))

theorem destruct_append (s t : wseq α) :
  destruct (append s t) = (destruct s).bind (destruct_append.aux t) :=
begin
  apply eq_of_bisim (λ c1 c2, ∃ s t, c1 = destruct (append s t) ∧
    c2 = (destruct s).bind (destruct_append.aux t)) _ ⟨s, t, rfl, rfl⟩,
  intros c1 c2 h, rcases h with ⟨s, t, h⟩, rw [h.left, h.right],
  apply s.cases_on _ (λ a s, _) (λ s, _); simp,
  { apply t.cases_on _ (λ b t, _) (λ t, _); simp,
    { refine ⟨nil, t, _, _⟩; simp } },
  { exact ⟨s, t, rfl, rfl⟩ }
end

@[simp] def destruct_join.aux : option (wseq α × wseq (wseq α)) → computation (option (α × wseq α))
| none          := return none
| (some (s, S)) := (destruct (append s (join S))).think

theorem destruct_join (S : wseq (wseq α)) :
  destruct (join S) = (destruct S).bind destruct_join.aux :=
begin
  apply eq_of_bisim (λ c1 c2, c1 = c2 ∨ ∃ S, c1 = destruct (join S) ∧
    c2 = (destruct S).bind destruct_join.aux) _ (or.inr ⟨S, rfl, rfl⟩),
  intros c1 c2 h, exact match c1, c2, h with
  | _, _, (or.inl $ eq.refl c) := by cases c.destruct; simp
  | _, _, or.inr ⟨S, rfl, rfl⟩ := begin
    apply S.cases_on _ (λ s S, _) (λ S, _); simp,
    { refine or.inr ⟨S, rfl, rfl⟩ }
  end end
end

theorem lift_rel_append (R : α → β → Prop) {s1 s2 : wseq α} {t1 t2 : wseq β}
  (h1 : lift_rel R s1 t1) (h2 : lift_rel R s2 t2) :
  lift_rel R (append s1 s2) (append t1 t2) :=
⟨λ s t, lift_rel R s t ∨ ∃ s1 t1, s = append s1 s2 ∧ t = append t1 t2 ∧ lift_rel R s1 t1,
or.inr ⟨s1, t1, rfl, rfl, h1⟩,
λ s t h, match s, t, h with
| s, t, or.inl h := begin
    apply computation.lift_rel.imp _ _ _ (lift_rel_destruct h),
    intros a b, apply lift_rel_o.imp_right,
    intros s t, apply or.inl
  end
| ._, ._, or.inr ⟨s1, t1, rfl, rfl, h⟩ := begin
    simp [destruct_append],
    apply computation.lift_rel_bind _ _ (lift_rel_destruct h),
    intros o p h,
    cases o with a; cases p with b,
    { simp, apply computation.lift_rel.imp _ _ _ (lift_rel_destruct h2),
      intros a b, apply lift_rel_o.imp_right,
      intros s t, apply or.inl },
    { cases b; cases h },
    { cases a; cases h },
    { cases a with a s; cases b with b t, cases h with r h,
      simp, exact ⟨r, or.inr ⟨s, rfl, t, rfl, h⟩⟩ }
  end
end⟩

theorem lift_rel_join.lem (R : α → β → Prop) {S T} {U : wseq α → wseq β → Prop}
  (ST : lift_rel (lift_rel R) S T) (HU : ∀ s1 s2, (∃ s t S T,
      s1 = append s (join S) ∧ s2 = append t (join T) ∧
      lift_rel R s t ∧ lift_rel (lift_rel R) S T) → U s1 s2) {a} (ma : a ∈ destruct (join S)) :
  ∃ {b}, b ∈ destruct (join T) ∧ lift_rel_o R U a b :=
begin
  cases exists_results_of_mem ma with n h, clear ma, revert a S T,
  apply nat.strong_induction_on n _,
  intros n IH a S T ST ra, simp [destruct_join] at ra, exact
  let ⟨o, m, k, rs1, rs2, en⟩ := of_results_bind ra,
      ⟨p, mT, rop⟩ := computation.exists_of_lift_rel_left (lift_rel_destruct ST) rs1.mem in
  by exact match o, p, rop, rs1, rs2, mT with
  | none, none, _, rs1, rs2, mT := by simp only [destruct_join]; exact
    ⟨none, mem_bind mT (ret_mem _), by rw eq_of_ret_mem rs2.mem; trivial⟩
  | some (s, S'), some (t, T'), ⟨st, ST'⟩, rs1, rs2, mT :=
    by simp [destruct_append] at rs2; exact
    let ⟨k1, rs3, ek⟩ := of_results_think rs2,
        ⟨o', m1, n1, rs4, rs5, ek1⟩ := of_results_bind rs3,
        ⟨p', mt, rop'⟩ := computation.exists_of_lift_rel_left (lift_rel_destruct st) rs4.mem in
    by exact match o', p', rop', rs4, rs5, mt with
    | none, none, _, rs4, rs5', mt :=
      have n1 < n, begin
        rw [en, ek, ek1],
        apply lt_of_lt_of_le _ (nat.le_add_right _ _),
        apply nat.lt_succ_of_le (nat.le_add_right _ _)
      end,
      let ⟨ob, mb, rob⟩ := IH _ this ST' rs5' in by refine ⟨ob, _, rob⟩;
      { simp [destruct_join], apply mem_bind mT, simp [destruct_append],
        apply think_mem, apply mem_bind mt, exact mb }
    | some (a, s'), some (b, t'), ⟨ab, st'⟩, rs4, rs5, mt := begin
      simp at rs5,
      refine ⟨some (b, append t' (join T')), _, _⟩,
      { simp [destruct_join], apply mem_bind mT, simp [destruct_append],
        apply think_mem, apply mem_bind mt, apply ret_mem },
      rw eq_of_ret_mem rs5.mem,
      exact ⟨ab, HU _ _ ⟨s', t', S', T', rfl, rfl, st', ST'⟩⟩
    end end
  end
end

theorem lift_rel_join (R : α → β → Prop) {S : wseq (wseq α)} {T : wseq (wseq β)}
  (h : lift_rel (lift_rel R) S T) : lift_rel R (join S) (join T) :=
⟨λ s1 s2, ∃ s t S T,
  s1 = append s (join S) ∧ s2 = append t (join T) ∧
  lift_rel R s t ∧ lift_rel (lift_rel R) S T,
  ⟨nil, nil, S, T, by simp, by simp, by simp, h⟩,
λs1 s2 ⟨s, t, S, T, h1, h2, st, ST⟩, begin
  clear _fun_match _x,
  rw [h1, h2], rw [destruct_append, destruct_append],
  apply computation.lift_rel_bind _ _ (lift_rel_destruct st),
  exact λ o p h, match o, p, h with
  | some (a, s), some (b, t), ⟨h1, h2⟩ :=
    by simp; exact ⟨h1, s, t, S, rfl, T, rfl, h2, ST⟩
  | none, none, _ := begin
    dsimp [destruct_append.aux, computation.lift_rel], constructor,
    { intro, apply lift_rel_join.lem _ ST (λ _ _, id) },
    { intros b mb,
      rw [←lift_rel_o.swap], apply lift_rel_join.lem (swap R),
      { rw [←lift_rel.swap R, ←lift_rel.swap], apply ST },
      { rw [←lift_rel.swap R, ←lift_rel.swap (lift_rel R)],
        exact λ s1 s2 ⟨s, t, S, T, h1, h2, st, ST⟩,
                      ⟨t, s, T, S, h2, h1, st, ST⟩ },
      { exact mb } }
  end end
end⟩

theorem join_congr {S T : wseq (wseq α)} (h : lift_rel equiv S T) : join S ~ join T :=
lift_rel_join _ h

theorem lift_rel_bind {δ} (R : α → β → Prop) (S : γ → δ → Prop)
  {s1 : wseq α} {s2 : wseq β}
  {f1 : α → wseq γ} {f2 : β → wseq δ}
  (h1 : lift_rel R s1 s2) (h2 : ∀ {a b}, R a b → lift_rel S (f1 a) (f2 b))
  : lift_rel S (bind s1 f1) (bind s2 f2) :=
lift_rel_join _ (lift_rel_map _ _ h1 @h2)

theorem bind_congr {s1 s2 : wseq α} {f1 f2 : α → wseq β}
  (h1 : s1 ~ s2) (h2 : ∀ a, f1 a ~ f2 a) : bind s1 f1 ~ bind s2 f2 :=
lift_rel_bind _ _ h1 (λ a b h, by rw h; apply h2)

@[simp] theorem join_ret (s : wseq α) : join (ret s) ~ s :=
by simp [ret]; apply think_equiv

@[simp] theorem join_map_ret (s : wseq α) : join (map ret s) ~ s :=
begin
  refine ⟨λ s1 s2, join (map ret s2) = s1, rfl, _⟩,
  intros s' s h, rw ←h,
  apply lift_rel_rec
    (λ c1 c2, ∃ s,
      c1 = destruct (join (map ret s)) ∧ c2 = destruct s),
  { exact λ c1 c2 h, match c1, c2, h with
    | ._, ._, ⟨s, rfl, rfl⟩ := begin
      clear h _match,
      have : ∀ s, ∃ s' : wseq α, (map ret s).join.destruct = (map ret s').join.destruct ∧
        destruct s = s'.destruct, from λ s, ⟨s, rfl, rfl⟩,
      apply s.cases_on _ (λ a s, _) (λ s, _); simp [ret, ret_mem, this, option.exists]
    end end },
  { exact ⟨s, rfl, rfl⟩ }
end

@[simp] theorem join_append (S T : wseq (wseq α)) :
  join (append S T) ~ append (join S) (join T) :=
begin
  refine ⟨λ s1 s2, ∃ s S T,
    s1 = append s (join (append S T)) ∧
    s2 = append s (append (join S) (join T)), ⟨nil, S, T, by simp, by simp⟩, _⟩,
  intros s1 s2 h,
  apply lift_rel_rec (λ c1 c2, ∃ (s : wseq α) S T,
    c1 = destruct (append s (join (append S T))) ∧
    c2 = destruct (append s (append (join S) (join T)))) _ _ _
    (let ⟨s, S, T, h1, h2⟩ := h in
         ⟨s, S, T, congr_arg destruct h1, congr_arg destruct h2⟩),
  intros c1 c2 h,
  exact match c1, c2, h with ._, ._, ⟨s, S, T, rfl, rfl⟩ := begin
    clear _match h h,
    apply wseq.cases_on s _ (λ a s, _) (λ s, _); simp,
    { apply wseq.cases_on S _ (λ s S, _) (λ S, _); simp,
      { apply wseq.cases_on T _ (λ s T, _) (λ T, _); simp,
        { refine ⟨s, nil, T, _, _⟩; simp },
        { refine ⟨nil, nil, T, _, _⟩; simp } },
      { exact ⟨s, S, T, rfl, rfl⟩ },
      { refine ⟨nil, S, T, _, _⟩; simp } },
    { exact ⟨s, S, T, rfl, rfl⟩ },
    { exact ⟨s, S, T, rfl, rfl⟩ }
  end end
end

@[simp] theorem bind_ret (f : α → β) (s) : bind s (ret ∘ f) ~ map f s :=
begin
  dsimp [bind], change (λx, ret (f x)) with (ret ∘ f),
  rw [map_comp], apply join_map_ret
end

@[simp] theorem ret_bind (a : α) (f : α → wseq β) :
  bind (ret a) f ~ f a := by simp [bind]

@[simp] theorem map_join (f : α → β) (S) :
  map f (join S) = join (map (map f) S) :=
begin
  apply seq.eq_of_bisim (λs1 s2,
    ∃ s S, s1 = append s (map f (join S)) ∧
      s2 = append s (join (map (map f) S))),
  { intros s1 s2 h,
    exact match s1, s2, h with ._, ._, ⟨s, S, rfl, rfl⟩ := begin
      apply wseq.cases_on s _ (λ a s, _) (λ s, _); simp,
      { apply wseq.cases_on S _ (λ s S, _) (λ S, _); simp,
        { exact ⟨map f s, S, rfl, rfl⟩ },
        { refine ⟨nil, S, _, _⟩; simp } },
      { exact ⟨_, _, rfl, rfl⟩ },
      { exact ⟨_, _, rfl, rfl⟩ }
    end end },
  { refine ⟨nil, S, _, _⟩; simp }
end

@[simp] theorem join_join (SS : wseq (wseq (wseq α))) :
  join (join SS) ~ join (map join SS) :=
begin
  refine ⟨λ s1 s2, ∃ s S SS,
    s1 = append s (join (append S (join SS))) ∧
    s2 = append s (append (join S) (join (map join SS))),
    ⟨nil, nil, SS, by simp, by simp⟩, _⟩,
  intros s1 s2 h,
  apply lift_rel_rec (λ c1 c2, ∃ s S SS,
      c1 = destruct (append s (join (append S (join SS)))) ∧
      c2 = destruct (append s (append (join S) (join (map join SS)))))
    _ (destruct s1) (destruct s2)
    (let ⟨s, S, SS, h1, h2⟩ := h in ⟨s, S, SS, by simp [h1], by simp [h2]⟩),
  intros c1 c2 h,
  exact match c1, c2, h with ._, ._, ⟨s, S, SS, rfl, rfl⟩ := begin
    clear _match h h,
    apply wseq.cases_on s _ (λ a s, _) (λ s, _); simp,
    { apply wseq.cases_on S _ (λ s S, _) (λ S, _); simp,
      { apply wseq.cases_on SS _ (λ S SS, _) (λ SS, _); simp,
        { refine ⟨nil, S, SS, _, _⟩; simp },
        { refine ⟨nil, nil, SS, _, _⟩; simp } },
      { exact ⟨s, S, SS, rfl, rfl⟩ },
      { refine ⟨nil, S, SS, _, _⟩; simp } },
    { exact ⟨s, S, SS, rfl, rfl⟩ },
    { exact ⟨s, S, SS, rfl, rfl⟩ }
  end end
end

@[simp] theorem bind_assoc (s : wseq α) (f : α → wseq β) (g : β → wseq γ) :
  bind (bind s f) g ~ bind s (λ (x : α), bind (f x) g) :=
begin
  simp [bind], rw [← map_comp f (map g), map_comp (map g ∘ f) join],
  apply join_join
end

instance : monad wseq :=
{ map  := @map,
  pure := @ret,
  bind := @bind }

/-
  Unfortunately, wseq is not a lawful monad, because it does not satisfy
  the monad laws exactly, only up to sequence equivalence.
  Furthermore, even quotienting by the equivalence is not sufficient,
  because the join operation involves lists of quotient elements,
  with a lifted equivalence relation, and pure quotients cannot handle
  this type of construction.

instance : is_lawful_monad wseq :=
{ id_map := @map_id,
  bind_pure_comp_eq_map := @bind_ret,
  pure_bind := @ret_bind,
  bind_assoc := @bind_assoc }
-/

end wseq
