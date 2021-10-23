/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.list.basic
import data.stream
import data.lazy_list
import data.seq.computation

universes u v w

/-
coinductive seq (α : Type u) : Type u
| nil : seq α
| cons : α → seq α → seq α
-/

/--
A stream `s : option α` is a sequence if `s.nth n = none` implies `s.nth (n + 1) = none`.
-/
def stream.is_seq {α : Type u} (s : stream (option α)) : Prop :=
∀ {n : ℕ}, s n = none → s (n + 1) = none

/-- `seq α` is the type of possibly infinite lists (referred here as sequences).
  It is encoded as an infinite stream of options such that if `f n = none`, then
  `f m = none` for all `m ≥ n`. -/
def seq (α : Type u) : Type u := { f : stream (option α) // f.is_seq }

/-- `seq1 α` is the type of nonempty sequences. -/
def seq1 (α) := α × seq α

namespace seq
variables {α : Type u} {β : Type v} {γ : Type w}

/-- The empty sequence -/
def nil : seq α := ⟨stream.const none, λn h, rfl⟩

instance : inhabited (seq α) := ⟨nil⟩

/-- Prepend an element to a sequence -/
def cons (a : α) : seq α → seq α
| ⟨f, al⟩ := ⟨some a :: f, λn h, by {cases n with n, contradiction, exact al h}⟩

/-- Get the nth element of a sequence (if it exists) -/
def nth : seq α → ℕ → option α := subtype.val

/-- A sequence has terminated at position `n` if the value at position `n` equals `none`. -/
def terminated_at (s : seq α) (n : ℕ) : Prop := s.nth n = none

/-- It is decidable whether a sequence terminates at a given position. -/
instance terminated_at_decidable (s : seq α) (n : ℕ) : decidable (s.terminated_at n) :=
decidable_of_iff' (s.nth n).is_none $ by unfold terminated_at; cases s.nth n; simp

/-- A sequence terminates if there is some position `n` at which it has terminated. -/
def terminates (s : seq α) : Prop := ∃ (n : ℕ), s.terminated_at n

/-- Functorial action of the functor `option (α × _)` -/
@[simp] def omap (f : β → γ) : option (α × β) → option (α × γ)
| none          := none
| (some (a, b)) := some (a, f b)

/-- Get the first element of a sequence -/
def head (s : seq α) : option α := nth s 0

/-- Get the tail of a sequence (or `nil` if the sequence is `nil`) -/
def tail : seq α → seq α
| ⟨f, al⟩ := ⟨f.tail, λ n, al⟩

protected def mem (a : α) (s : seq α) := some a ∈ s.1

instance : has_mem α (seq α) :=
⟨seq.mem⟩

theorem le_stable (s : seq α) {m n} (h : m ≤ n) :
  s.nth m = none → s.nth n = none :=
by {cases s with f al, induction h with n h IH, exacts [id, λ h2, al (IH h2)]}

/-- If a sequence terminated at position `n`, it also terminated at `m ≥ n `. -/
lemma terminated_stable (s : seq α) {m n : ℕ} (m_le_n : m ≤ n)
(terminated_at_m : s.terminated_at m) :
  s.terminated_at n :=
le_stable s m_le_n terminated_at_m

/--
If `s.nth n = some aₙ` for some value `aₙ`, then there is also some value `aₘ` such
that `s.nth = some aₘ` for `m ≤ n`.
-/
lemma ge_stable (s : seq α) {aₙ : α} {n m : ℕ} (m_le_n : m ≤ n)
(s_nth_eq_some : s.nth n = some aₙ) :
  ∃ (aₘ : α), s.nth m = some aₘ :=
have s.nth n ≠ none, by simp [s_nth_eq_some],
have s.nth m ≠ none, from mt (s.le_stable m_le_n) this,
option.ne_none_iff_exists'.mp this

theorem not_mem_nil (a : α) : a ∉ @nil α :=
λ ⟨n, (h : some a = none)⟩, by injection h

theorem mem_cons (a : α) : ∀ (s : seq α), a ∈ cons a s
| ⟨f, al⟩ := stream.mem_cons (some a) _

theorem mem_cons_of_mem (y : α) {a : α} : ∀ {s : seq α}, a ∈ s → a ∈ cons y s
| ⟨f, al⟩ := stream.mem_cons_of_mem (some y)

theorem eq_or_mem_of_mem_cons {a b : α} : ∀ {s : seq α}, a ∈ cons b s → a = b ∨ a ∈ s
| ⟨f, al⟩ h := (stream.eq_or_mem_of_mem_cons h).imp_left (λh, by injection h)

@[simp] theorem mem_cons_iff {a b : α} {s : seq α} : a ∈ cons b s ↔ a = b ∨ a ∈ s :=
⟨eq_or_mem_of_mem_cons, λo, by cases o with e m;
  [{rw e, apply mem_cons}, exact mem_cons_of_mem _ m]⟩

/-- Destructor for a sequence, resulting in either `none` (for `nil`) or
  `some (a, s)` (for `cons a s`). -/
def destruct (s : seq α) : option (seq1 α) :=
(λa', (a', s.tail)) <$> nth s 0

theorem destruct_eq_nil {s : seq α} : destruct s = none → s = nil :=
begin
  dsimp [destruct],
  induction f0 : nth s 0; intro h,
  { apply subtype.eq,
    funext n,
    induction n with n IH, exacts [f0, s.2 IH] },
  { contradiction }
end

theorem destruct_eq_cons {s : seq α} {a s'} : destruct s = some (a, s') → s = cons a s' :=
begin
  dsimp [destruct],
  induction f0 : nth s 0 with a'; intro h,
  { contradiction },
  { cases s with f al,
    injections with _ h1 h2,
    rw ←h2, apply subtype.eq, dsimp [tail, cons],
    rw h1 at f0, rw ←f0,
    exact (stream.eta f).symm }
end

@[simp] theorem destruct_nil : destruct (nil : seq α) = none := rfl

@[simp] theorem destruct_cons (a : α) : ∀ s, destruct (cons a s) = some (a, s)
| ⟨f, al⟩ := begin
  unfold cons destruct functor.map,
  apply congr_arg (λ s, some (a, s)),
  apply subtype.eq, dsimp [tail], rw [stream.tail_cons]
end

theorem head_eq_destruct (s : seq α) : head s = prod.fst <$> destruct s :=
by unfold destruct head; cases nth s 0; refl

@[simp] theorem head_nil : head (nil : seq α) = none := rfl

@[simp] theorem head_cons (a : α) (s) : head (cons a s) = some a :=
by rw [head_eq_destruct, destruct_cons]; refl

@[simp] theorem tail_nil : tail (nil : seq α) = nil := rfl

@[simp] theorem tail_cons (a : α) (s) : tail (cons a s) = s :=
by cases s with f al; apply subtype.eq; dsimp [tail, cons]; rw [stream.tail_cons]

def cases_on {C : seq α → Sort v} (s : seq α)
  (h1 : C nil) (h2 : ∀ x s, C (cons x s)) : C s := begin
  induction H : destruct s with v v,
  { rw destruct_eq_nil H, apply h1 },
  { cases v with a s', rw destruct_eq_cons H, apply h2 }
end

theorem mem_rec_on {C : seq α → Prop} {a s} (M : a ∈ s)
  (h1 : ∀ b s', (a = b ∨ C s') → C (cons b s')) : C s :=
begin
  cases M with k e, unfold stream.nth at e,
  induction k with k IH generalizing s,
  { have TH : s = cons a (tail s),
    { apply destruct_eq_cons,
      unfold destruct nth functor.map, rw ←e, refl },
    rw TH, apply h1 _ _ (or.inl rfl) },
  revert e, apply s.cases_on _ (λ b s', _); intro e,
  { injection e },
  { have h_eq : (cons b s').val (nat.succ k) = s'.val k, { cases s'; refl },
    rw [h_eq] at e,
    apply h1 _ _ (or.inr (IH e)) }
end

def corec.F (f : β → option (α × β)) : option β → option α × option β
| none     := (none, none)
| (some b) := match f b with none := (none, none) | some (a, b') := (some a, some b') end

/-- Corecursor for `seq α` as a coinductive type. Iterates `f` to produce new elements
  of the sequence until `none` is obtained. -/
def corec (f : β → option (α × β)) (b : β) : seq α :=
begin
  refine ⟨stream.corec' (corec.F f) (some b), λn h, _⟩,
  rw stream.corec'_eq,
  change stream.corec' (corec.F f) (corec.F f (some b)).2 n = none,
  revert h, generalize : some b = o, revert o,
  induction n with n IH; intro o,
  { change (corec.F f o).1 = none → (corec.F f (corec.F f o).2).1 = none,
    cases o with b; intro h, { refl },
    dsimp [corec.F] at h, dsimp [corec.F],
    cases f b with s, { refl },
    { cases s with a b', contradiction } },
  { rw [stream.corec'_eq (corec.F f) (corec.F f o).2,
        stream.corec'_eq (corec.F f) o],
    exact IH (corec.F f o).2 }
end

@[simp] theorem corec_eq (f : β → option (α × β)) (b : β) :
  destruct (corec f b) = omap (corec f) (f b) :=
begin
  dsimp [corec, destruct, nth],
  change stream.corec' (corec.F f) (some b) 0 with (corec.F f (some b)).1,
  dsimp [corec.F],
  induction h : f b with s, { refl },
  cases s with a b', dsimp [corec.F],
  apply congr_arg (λ b', some (a, b')),
  apply subtype.eq,
  dsimp [corec, tail],
  rw [stream.corec'_eq, stream.tail_cons],
  dsimp [corec.F], rw h, refl
end

/-- Embed a list as a sequence -/
def of_list (l : list α) : seq α :=
⟨list.nth l, λn h, begin
  induction l with a l IH generalizing n, refl,
  dsimp [list.nth], cases n with n; dsimp [list.nth] at h,
  { contradiction },
  { apply IH _ h }
end⟩

instance coe_list : has_coe (list α) (seq α) := ⟨of_list⟩

section bisim
  variable (R : seq α → seq α → Prop)

  local infix ` ~ `:50 := R

  def bisim_o : option (seq1 α) → option (seq1 α) → Prop
  | none          none            := true
  | (some (a, s)) (some (a', s')) := a = a' ∧ R s s'
  | _             _               := false
  attribute [simp] bisim_o

  def is_bisimulation := ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → bisim_o R (destruct s₁) (destruct s₂)

  -- If two streams are bisimilar, then they are equal
  theorem eq_of_bisim (bisim : is_bisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂ :=
  begin
    apply subtype.eq,
    apply stream.eq_of_bisim (λx y, ∃ s s' : seq α, s.1 = x ∧ s'.1 = y ∧ R s s'),
    dsimp [stream.is_bisimulation],
    intros t₁ t₂ e,
    exact match t₁, t₂, e with ._, ._, ⟨s, s', rfl, rfl, r⟩ :=
      suffices head s = head s' ∧ R (tail s) (tail s'), from
      and.imp id (λr, ⟨tail s, tail s',
        by cases s; refl, by cases s'; refl, r⟩) this,
      begin
        have := bisim r, revert r this,
        apply cases_on s _ _; intros; apply cases_on s' _ _; intros; intros r this,
        { constructor, refl, assumption },
        { rw [destruct_nil, destruct_cons] at this,
          exact false.elim this },
        { rw [destruct_nil, destruct_cons] at this,
          exact false.elim this },
        { rw [destruct_cons, destruct_cons] at this,
          rw [head_cons, head_cons, tail_cons, tail_cons],
          cases this with h1 h2,
          constructor, rw h1, exact h2 }
      end
    end,
    exact ⟨s₁, s₂, rfl, rfl, r⟩
  end
end bisim

theorem coinduction : ∀ {s₁ s₂ : seq α}, head s₁ = head s₂ →
  (∀ (β : Type u) (fr : seq α → β),
    fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂
| ⟨f₁, a₁⟩ ⟨f₂, a₂⟩ hh ht :=
  subtype.eq (stream.coinduction hh (λ β fr, ht β (λs, fr s.1)))

theorem coinduction2 (s) (f g : seq α → seq β)
  (H : ∀ s, bisim_o (λ (s1 s2 : seq β), ∃ (s : seq α), s1 = f s ∧ s2 = g s)
    (destruct (f s)) (destruct (g s)))
  : f s = g s :=
begin
  refine eq_of_bisim (λ s1 s2, ∃ s, s1 = f s ∧ s2 = g s) _ ⟨s, rfl, rfl⟩,
  intros s1 s2 h, rcases h with ⟨s, h1, h2⟩,
  rw [h1, h2], apply H
end

/-- Embed an infinite stream as a sequence -/
def of_stream (s : stream α) : seq α :=
⟨s.map some, λn h, by contradiction⟩

instance coe_stream : has_coe (stream α) (seq α) := ⟨of_stream⟩

/-- Embed a `lazy_list α` as a sequence. Note that even though this
  is non-meta, it will produce infinite sequences if used with
  cyclic `lazy_list`s created by meta constructions. -/
def of_lazy_list : lazy_list α → seq α :=
corec (λl, match l with
  | lazy_list.nil := none
  | lazy_list.cons a l' := some (a, l' ())
  end)

instance coe_lazy_list : has_coe (lazy_list α) (seq α) := ⟨of_lazy_list⟩

/-- Translate a sequence into a `lazy_list`. Since `lazy_list` and `list`
  are isomorphic as non-meta types, this function is necessarily meta. -/
meta def to_lazy_list : seq α → lazy_list α | s :=
match destruct s with
| none := lazy_list.nil
| some (a, s') := lazy_list.cons a (to_lazy_list s')
end

/-- Translate a sequence to a list. This function will run forever if
  run on an infinite sequence. -/
meta def force_to_list (s : seq α) : list α := (to_lazy_list s).to_list

/-- The sequence of natural numbers some 0, some 1, ... -/
def nats : seq ℕ := stream.nats

@[simp]
lemma nats_nth (n : ℕ) : nats.nth n = some n := rfl

/-- Append two sequences. If `s₁` is infinite, then `s₁ ++ s₂ = s₁`,
  otherwise it puts `s₂` at the location of the `nil` in `s₁`. -/
def append (s₁ s₂ : seq α) : seq α :=
@corec α (seq α × seq α) (λ⟨s₁, s₂⟩,
  match destruct s₁ with
  | none := omap (λs₂, (nil, s₂)) (destruct s₂)
  | some (a, s₁') := some (a, s₁', s₂)
  end) (s₁, s₂)

/-- Map a function over a sequence. -/
def map (f : α → β) : seq α → seq β | ⟨s, al⟩ :=
⟨s.map (option.map f),
λn, begin
  dsimp [stream.map, stream.nth],
  induction e : s n; intro,
  { rw al e, assumption }, { contradiction }
end⟩

/-- Flatten a sequence of sequences. (It is required that the
  sequences be nonempty to ensure productivity; in the case
  of an infinite sequence of `nil`, the first element is never
  generated.) -/
def join : seq (seq1 α) → seq α :=
corec (λS, match destruct S with
  | none := none
  | some ((a, s), S') := some (a, match destruct s with
    | none := S'
    | some s' := cons s' S'
    end)
  end)

/-- Remove the first `n` elements from the sequence. -/
def drop (s : seq α) : ℕ → seq α
| 0     := s
| (n+1) := tail (drop n)
attribute [simp] drop

/-- Take the first `n` elements of the sequence (producing a list) -/
def take : ℕ → seq α → list α
| 0     s := []
| (n+1) s := match destruct s with
  | none := []
  | some (x, r) := list.cons x (take n r)
  end

/-- Split a sequence at `n`, producing a finite initial segment
  and an infinite tail. -/
def split_at : ℕ → seq α → list α × seq α
| 0     s := ([], s)
| (n+1) s := match destruct s with
  | none := ([], nil)
  | some (x, s') := let (l, r) := split_at n s' in (list.cons x l, r)
  end

section zip_with

/-- Combine two sequences with a function -/
def zip_with (f : α → β → γ) : seq α → seq β → seq γ
| ⟨f₁, a₁⟩ ⟨f₂, a₂⟩ := ⟨λn,
    match f₁ n, f₂ n with
    | some a, some b := some (f a b)
    | _, _ := none
    end,
  λn, begin
    induction h1 : f₁ n,
    { intro H, simp only [(a₁ h1)], refl },
    induction h2 : f₂ n; dsimp [seq.zip_with._match_1]; intro H,
    { rw (a₂ h2), cases f₁ (n + 1); refl },
    { rw [h1, h2] at H, contradiction }
  end⟩

variables {s : seq α} {s' : seq β} {n : ℕ}

lemma zip_with_nth_some {a : α} {b : β} (s_nth_eq_some : s.nth n = some a)
(s_nth_eq_some' : s'.nth n = some b) (f : α → β → γ) :
  (zip_with f s s').nth n = some (f a b) :=
begin
  cases s with st,
  have : st n = some a, from s_nth_eq_some,
  cases s' with st',
  have : st' n = some b, from s_nth_eq_some',
  simp only [zip_with, seq.nth, *]
end

lemma zip_with_nth_none (s_nth_eq_none : s.nth n = none) (f : α → β → γ) :
  (zip_with f s s').nth n = none :=
begin
  cases s with st,
  have : st n = none, from s_nth_eq_none,
  cases s' with st',
  cases st'_nth_eq : st' n;
  simp only [zip_with, seq.nth, *]
end

lemma zip_with_nth_none' (s'_nth_eq_none : s'.nth n = none) (f : α → β → γ) :
  (zip_with f s s').nth n = none :=
begin
  cases s' with st',
  have : st' n = none, from s'_nth_eq_none,
  cases s with st,
  cases st_nth_eq : st n;
  simp only [zip_with, seq.nth, *]
end

end zip_with

/-- Pair two sequences into a sequence of pairs -/
def zip : seq α → seq β → seq (α × β) := zip_with prod.mk

/-- Separate a sequence of pairs into two sequences -/
def unzip (s : seq (α × β)) : seq α × seq β := (map prod.fst s, map prod.snd s)

/-- Convert a sequence which is known to terminate into a list -/
def to_list (s : seq α) (h : ∃ n, ¬ (nth s n).is_some) : list α :=
take (nat.find h) s

/-- Convert a sequence which is known not to terminate into a stream -/
def to_stream (s : seq α) (h : ∀ n, (nth s n).is_some) : stream α :=
λn, option.get (h n)

/-- Convert a sequence into either a list or a stream depending on whether
  it is finite or infinite. (Without decidability of the infiniteness predicate,
  this is not constructively possible.) -/
def to_list_or_stream (s : seq α) [decidable (∃ n, ¬ (nth s n).is_some)] :
  list α ⊕ stream α :=
if h : ∃ n, ¬ (nth s n).is_some
then sum.inl (to_list s h)
else sum.inr (to_stream s (λn, decidable.by_contradiction (λ hn, h ⟨n, hn⟩)))

@[simp] theorem nil_append (s : seq α) : append nil s = s :=
begin
  apply coinduction2, intro s,
  dsimp [append], rw [corec_eq],
  dsimp [append], apply cases_on s _ _,
  { trivial },
  { intros x s,
    rw [destruct_cons], dsimp,
    exact ⟨rfl, s, rfl, rfl⟩ }
end

@[simp] theorem cons_append (a : α) (s t) : append (cons a s) t = cons a (append s t) :=
destruct_eq_cons $ begin
  dsimp [append], rw [corec_eq],
  dsimp [append], rw [destruct_cons],
  dsimp [append], refl
end

@[simp] theorem append_nil (s : seq α) : append s nil = s :=
begin
  apply coinduction2 s, intro s,
  apply cases_on s _ _,
  { trivial },
  { intros x s,
    rw [cons_append, destruct_cons, destruct_cons], dsimp,
    exact ⟨rfl, s, rfl, rfl⟩ }
end

@[simp] theorem append_assoc (s t u : seq α) :
  append (append s t) u = append s (append t u) :=
begin
  apply eq_of_bisim (λs1 s2, ∃ s t u,
    s1 = append (append s t) u ∧ s2 = append s (append t u)),
  { intros s1 s2 h, exact match s1, s2, h with ._, ._, ⟨s, t, u, rfl, rfl⟩ := begin
      apply cases_on s; simp,
      { apply cases_on t; simp,
        { apply cases_on u; simp,
          { intros x u, refine ⟨nil, nil, u, _, _⟩; simp } },
        { intros x t, refine ⟨nil, t, u, _, _⟩; simp } },
      { intros x s, exact ⟨s, t, u, rfl, rfl⟩ }
    end end },
  { exact ⟨s, t, u, rfl, rfl⟩ }
end

@[simp] theorem map_nil (f : α → β) : map f nil = nil := rfl

@[simp] theorem map_cons (f : α → β) (a) : ∀ s, map f (cons a s) = cons (f a) (map f s)
| ⟨s, al⟩ := by apply subtype.eq; dsimp [cons, map]; rw stream.map_cons; refl

@[simp] theorem map_id : ∀ (s : seq α), map id s = s
| ⟨s, al⟩ := begin
  apply subtype.eq; dsimp [map],
  rw [option.map_id, stream.map_id]; refl
end

@[simp] theorem map_tail (f : α → β) : ∀ s, map f (tail s) = tail (map f s)
| ⟨s, al⟩ := by apply subtype.eq; dsimp [tail, map]; rw stream.map_tail; refl

theorem map_comp (f : α → β) (g : β → γ) : ∀ (s : seq α), map (g ∘ f) s = map g (map f s)
| ⟨s, al⟩ := begin
  apply subtype.eq; dsimp [map],
  rw stream.map_map,
  apply congr_arg (λ f : _ → option γ, stream.map f s),
  ext ⟨⟩; refl
end

@[simp] theorem map_append (f : α → β) (s t) : map f (append s t) = append (map f s) (map f t) :=
begin
  apply eq_of_bisim (λs1 s2, ∃ s t,
    s1 = map f (append s t) ∧ s2 = append (map f s) (map f t)) _ ⟨s, t, rfl, rfl⟩,
  intros s1 s2 h, exact match s1, s2, h with ._, ._, ⟨s, t, rfl, rfl⟩ := begin
    apply cases_on s; simp,
    { apply cases_on t; simp,
      { intros x t, refine ⟨nil, t, _, _⟩; simp } },
    { intros x s, refine ⟨s, t, rfl, rfl⟩ }
  end end
end

@[simp] theorem map_nth (f : α → β) : ∀ s n, nth (map f s) n = (nth s n).map f
| ⟨s, al⟩ n := rfl

instance : functor seq := {map := @map}

instance : is_lawful_functor seq :=
{ id_map := @map_id, comp_map := @map_comp }

@[simp] theorem join_nil : join nil = (nil : seq α) := destruct_eq_nil rfl

@[simp] theorem join_cons_nil (a : α) (S) :
  join (cons (a, nil) S) = cons a (join S) :=
destruct_eq_cons $ by simp [join]

@[simp] theorem join_cons_cons (a b : α) (s S) :
  join (cons (a, cons b s) S) = cons a (join (cons (b, s) S)) :=
destruct_eq_cons $ by simp [join]

@[simp, priority 990] theorem join_cons (a : α) (s S) :
  join (cons (a, s) S) = cons a (append s (join S)) :=
begin
  apply eq_of_bisim (λs1 s2, s1 = s2 ∨
    ∃ a s S, s1 = join (cons (a, s) S) ∧
      s2 = cons a (append s (join S))) _ (or.inr ⟨a, s, S, rfl, rfl⟩),
  intros s1 s2 h,
  exact match s1, s2, h with
  | _, _, (or.inl $ eq.refl s) := begin
      apply cases_on s, { trivial },
      { intros x s, rw [destruct_cons], exact ⟨rfl, or.inl rfl⟩ }
    end
  | ._, ._, (or.inr ⟨a, s, S, rfl, rfl⟩) := begin
      apply cases_on s,
      { simp },
      { intros x s, simp, refine or.inr ⟨x, s, S, rfl, rfl⟩ }
    end
  end
end

@[simp] theorem join_append (S T : seq (seq1 α)) :
  join (append S T) = append (join S) (join T) :=
begin
  apply eq_of_bisim (λs1 s2, ∃ s S T,
    s1 = append s (join (append S T)) ∧
    s2 = append s (append (join S) (join T))),
  { intros s1 s2 h, exact match s1, s2, h with ._, ._, ⟨s, S, T, rfl, rfl⟩ := begin
      apply cases_on s; simp,
      { apply cases_on S; simp,
        { apply cases_on T, { simp },
          { intros s T, cases s with a s; simp,
            refine ⟨s, nil, T, _, _⟩; simp } },
        { intros s S, cases s with a s; simp,
          exact ⟨s, S, T, rfl, rfl⟩ } },
      { intros x s, exact ⟨s, S, T, rfl, rfl⟩ }
    end end },
  { refine ⟨nil, S, T, _, _⟩; simp }
end

@[simp] theorem of_list_nil : of_list [] = (nil : seq α) := rfl

@[simp] theorem of_list_cons (a : α) (l) :
  of_list (a :: l) = cons a (of_list l) :=
begin
  apply subtype.eq, simp [of_list, cons],
  ext ⟨⟩; simp [list.nth, stream.cons]
end

@[simp] theorem of_stream_cons (a : α) (s) :
  of_stream (a :: s) = cons a (of_stream s) :=
by apply subtype.eq; simp [of_stream, cons]; rw stream.map_cons

@[simp] theorem of_list_append (l l' : list α) :
  of_list (l ++ l') = append (of_list l) (of_list l') :=
by induction l; simp [*]

@[simp] theorem of_stream_append (l : list α) (s : stream α) :
  of_stream (l ++ₛ s) = append (of_list l) (of_stream s) :=
by induction l; simp [*, stream.nil_append_stream, stream.cons_append_stream]

/-- Convert a sequence into a list, embedded in a computation to allow for
  the possibility of infinite sequences (in which case the computation
  never returns anything). -/
def to_list' {α} (s : seq α) : computation (list α) :=
@computation.corec (list α) (list α × seq α) (λ⟨l, s⟩,
  match destruct s with
  | none         := sum.inl l.reverse
  | some (a, s') := sum.inr (a::l, s')
  end) ([], s)

theorem dropn_add (s : seq α) (m) : ∀ n, drop s (m + n) = drop (drop s m) n
| 0     := rfl
| (n+1) := congr_arg tail (dropn_add n)

theorem dropn_tail (s : seq α) (n) : drop (tail s) n = drop s (n + 1) :=
by rw add_comm; symmetry; apply dropn_add

theorem nth_tail : ∀ (s : seq α) n, nth (tail s) n = nth s (n + 1)
| ⟨f, al⟩ n := rfl

@[ext]
protected lemma ext (s s': seq α) (hyp : ∀ (n : ℕ), s.nth n = s'.nth n) : s = s' :=
begin
  let ext := (λ (s s' : seq α), ∀ n, s.nth n = s'.nth n),
  apply seq.eq_of_bisim ext _ hyp,
  -- we have to show that ext is a bisimulation
  clear hyp s s',
  assume s s' (hyp : ext s s'),
  unfold seq.destruct,
  rw (hyp 0),
  cases (s'.nth 0),
  { simp [seq.bisim_o] }, -- option.none
  { -- option.some
    suffices : ext s.tail s'.tail, by simpa,
    assume n,
    simp only [seq.nth_tail _ n, (hyp $ n + 1)] }
end

@[simp] theorem head_dropn (s : seq α) (n) : head (drop s n) = nth s n :=
begin
  induction n with n IH generalizing s, { refl },
  rw [nat.succ_eq_add_one, ←nth_tail, ←dropn_tail], apply IH
end

theorem mem_map (f : α → β) {a : α} : ∀ {s : seq α}, a ∈ s → f a ∈ map f s
| ⟨g, al⟩ := stream.mem_map (option.map f)

theorem exists_of_mem_map {f} {b : β} : ∀ {s : seq α}, b ∈ map f s → ∃ a, a ∈ s ∧ f a = b
| ⟨g, al⟩ h := let ⟨o, om, oe⟩ := stream.exists_of_mem_map h in
  by cases o with a; injection oe with h'; exact ⟨a, om, h'⟩

theorem of_mem_append {s₁ s₂ : seq α} {a : α} (h : a ∈ append s₁ s₂) : a ∈ s₁ ∨ a ∈ s₂ :=
begin
  have := h, revert this,
  generalize e : append s₁ s₂ = ss, intro h, revert s₁,
  apply mem_rec_on h _,
  intros b s' o s₁,
  apply s₁.cases_on _ (λ c t₁, _); intros m e;
  have := congr_arg destruct e,
  { apply or.inr, simpa using m },
  { cases (show a = c ∨ a ∈ append t₁ s₂, by simpa using m) with e' m,
    { rw e', exact or.inl (mem_cons _ _) },
    { cases (show c = b ∧ append t₁ s₂ = s', by simpa) with i1 i2,
      cases o with e' IH,
      { simp [i1, e'] },
      { exact or.imp_left (mem_cons_of_mem _) (IH m i2) } } }
end

theorem mem_append_left {s₁ s₂ : seq α} {a : α} (h : a ∈ s₁) : a ∈ append s₁ s₂ :=
by apply mem_rec_on h; intros; simp [*]

end seq

namespace seq1
variables {α : Type u} {β : Type v} {γ : Type w}
open seq

/-- Convert a `seq1` to a sequence. -/
def to_seq : seq1 α → seq α
| (a, s) := cons a s

instance coe_seq : has_coe (seq1 α) (seq α) := ⟨to_seq⟩

/-- Map a function on a `seq1` -/
def map (f : α → β) : seq1 α → seq1 β
| (a, s) := (f a, seq.map f s)

theorem map_id : ∀ (s : seq1 α), map id s = s | ⟨a, s⟩ := by simp [map]

/-- Flatten a nonempty sequence of nonempty sequences -/
def join : seq1 (seq1 α) → seq1 α
| ((a, s), S) := match destruct s with
  | none := (a, seq.join S)
  | some s' := (a, seq.join (cons s' S))
  end

@[simp] theorem join_nil (a : α) (S) : join ((a, nil), S) = (a, seq.join S) := rfl

@[simp] theorem join_cons (a b : α) (s S) :
  join ((a, cons b s), S) = (a, seq.join (cons (b, s) S)) :=
by dsimp [join]; rw [destruct_cons]; refl

/-- The `return` operator for the `seq1` monad,
  which produces a singleton sequence. -/
def ret (a : α) : seq1 α := (a, nil)

instance [inhabited α] : inhabited (seq1 α) := ⟨ret (default _)⟩

/-- The `bind` operator for the `seq1` monad,
  which maps `f` on each element of `s` and appends the results together.
  (Not all of `s` may be evaluated, because the first few elements of `s`
  may already produce an infinite result.) -/
def bind (s : seq1 α) (f : α → seq1 β) : seq1 β :=
join (map f s)

@[simp] theorem join_map_ret (s : seq α) : seq.join (seq.map ret s) = s :=
by apply coinduction2 s; intro s; apply cases_on s; simp [ret]

@[simp] theorem bind_ret (f : α → β) : ∀ s, bind s (ret ∘ f) = map f s
| ⟨a, s⟩ := begin
  dsimp [bind, map], change (λx, ret (f x)) with (ret ∘ f),
  rw [map_comp], simp [function.comp, ret]
end

@[simp] theorem ret_bind (a : α) (f : α → seq1 β) : bind (ret a) f = f a :=
begin
  simp [ret, bind, map],
  cases f a with a s,
  apply cases_on s; intros; simp
end

@[simp] theorem map_join' (f : α → β) (S) :
  seq.map f (seq.join S) = seq.join (seq.map (map f) S) :=
begin
  apply eq_of_bisim (λs1 s2,
    ∃ s S, s1 = append s (seq.map f (seq.join S)) ∧
      s2 = append s (seq.join (seq.map (map f) S))),
  { intros s1 s2 h, exact match s1, s2, h with ._, ._, ⟨s, S, rfl, rfl⟩ := begin
      apply cases_on s; simp,
      { apply cases_on S; simp,
        { intros x S, cases x with a s; simp [map],
          exact ⟨_, _, rfl, rfl⟩ } },
      { intros x s, refine ⟨s, S, rfl, rfl⟩ }
    end end },
  { refine ⟨nil, S, _, _⟩; simp }
end

@[simp] theorem map_join (f : α → β) : ∀ S, map f (join S) = join (map (map f) S)
| ((a, s), S) := by apply cases_on s; intros; simp [map]

@[simp] theorem join_join (SS : seq (seq1 (seq1 α))) :
  seq.join (seq.join SS) = seq.join (seq.map join SS) :=
begin
  apply eq_of_bisim (λs1 s2,
    ∃ s SS, s1 = seq.append s (seq.join (seq.join SS)) ∧
      s2 = seq.append s (seq.join (seq.map join SS))),
  { intros s1 s2 h, exact match s1, s2, h with ._, ._, ⟨s, SS, rfl, rfl⟩ := begin
      apply cases_on s; simp,
      { apply cases_on SS; simp,
        { intros S SS, cases S with s S; cases s with x s; simp [map],
          apply cases_on s; simp,
          { exact ⟨_, _, rfl, rfl⟩ },
          { intros x s,
            refine ⟨cons x (append s (seq.join S)), SS, _, _⟩; simp } } },
      { intros x s, exact ⟨s, SS, rfl, rfl⟩ }
    end end },
  { refine ⟨nil, SS, _, _⟩; simp }
end

@[simp] theorem bind_assoc (s : seq1 α) (f : α → seq1 β) (g : β → seq1 γ) :
  bind (bind s f) g = bind s (λ (x : α), bind (f x) g) :=
begin
  cases s with a s,
  simp [bind, map],
  rw [←map_comp],
  change (λ x, join (map g (f x))) with (join ∘ ((map g) ∘ f)),
  rw [map_comp _ join],
  generalize : seq.map (map g ∘ f) s = SS,
  rcases map g (f a) with ⟨⟨a, s⟩, S⟩,
  apply cases_on s; intros; apply cases_on S; intros; simp,
  { cases x with x t, apply cases_on t; intros; simp },
  { cases x_1 with y t; simp }
end

instance : monad seq1 :=
{ map  := @map,
  pure := @ret,
  bind := @bind }

instance : is_lawful_monad seq1 :=
{ id_map := @map_id,
  bind_pure_comp_eq_map := @bind_ret,
  pure_bind := @ret_bind,
  bind_assoc := @bind_assoc }

end seq1
