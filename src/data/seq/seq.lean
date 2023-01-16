/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.list.basic
import data.lazy_list
import data.nat.basic
import data.stream.init
import data.seq.computation

universes u v w
open function
variables {α : Type u} {β : Type v} {γ : Type w}


/-
coinductive seq (α : Type u) : Type u
| nil : seq α
| cons : α → seq α → seq α
-/

/-- `seq α` is the type of possibly infinite lists (referred here as sequences). It is encoded as
an infinite stream of `option`s such that if `f n = none`, then `f m = none` for all `m ≥ n`. -/
structure seq (α : Type u) extends val : stream (option α) : Type u :=
(nth_succ_eq_none : ∀ ⦃n⦄, nth n = none → nth (n + 1) = none)

/-- `seq1 α` is the type of nonempty sequences. -/
structure seq1 (α : Type u) := (head : α) (tail : seq α)

namespace seq

lemma val_injective : injective (@val α) :=
by { rintro ⟨s, _⟩ ⟨s', _⟩ (rfl : s = s'), refl }

@[simp] lemma val_inj {s s' : seq α} : s.val = s'.val ↔ s = s' :=
val_injective.eq_iff

@[ext] lemma ext {s s' : seq α} (h : ∀ n, s.nth n = s'.nth n) : s = s' :=
val_injective $ stream.ext h

lemma ext_iff {s s' : seq α} : s = s' ↔ ∀ n, s.nth n = s'.nth n := ⟨λ h n, h ▸ rfl, ext⟩

/-- The empty sequence -/
@[simps] def nil : seq α := ⟨pure none, λ n h, rfl⟩
lemma nth_nil (n) : (@nil α).nth n = none := rfl

instance : inhabited (seq α) := ⟨nil⟩

@[simp] lemma mk_val (s h) : (mk s h : seq α).1 = s := rfl

/-- Prepend an element to a sequence -/
@[simps val] def cons (a : α) (s : seq α) : seq α :=
⟨some a :: s.1, nat.and_forall_succ.1 ⟨λ h, absurd h (option.some_ne_none _), λ n h, s.2 h⟩⟩

@[simp] theorem nth_cons_succ (a : α) (s : seq α) (n : ℕ) : (cons a s).nth (n + 1) = s.nth n := rfl

/-- Get the first element of a sequence -/
def head (s : seq α) : option α := s.nth 0

@[simp] lemma nth_zero (s : seq α) : s.nth 0 = s.head := rfl
@[simp] lemma head_cons (a : α) (s : seq α) : head (cons a s) = some a := rfl
@[simp] theorem head_nil : head (nil : seq α) = none := rfl

/-- Remove the first `n` elements from the sequence. -/
@[simps val] def drop (s : seq α) (n : ℕ) : seq α :=
⟨s.1.drop n, λ m hm, by simpa only [stream.nth_drop, add_right_comm] using s.2 hm⟩

@[simp] lemma head_drop (s : seq α) (n : ℕ) : (s.drop n).head = s.nth n := s.1.head_drop n
lemma nth_drop (s : seq α) (n i : ℕ) : (s.drop n).nth i = s.nth (i + n) := rfl

/-- Get the tail of a sequence (or `seq.nil` if the sequence is `seq.nil`) -/
def tail (s : seq α) : seq α := s.drop 1

@[simp] lemma tail_val (s : seq α) : s.tail.val = s.val.tail := rfl
@[simp] lemma head_tail (s : seq α) : s.tail.head = s.nth 1 := rfl
lemma nth_tail (s : seq α) (n : ℕ) : s.tail.nth n = s.nth (n + 1) := rfl

@[simp] lemma tail_cons (a : α) (s : seq α) : (cons a s).tail = s :=
val_injective $ stream.tail_cons _ _

@[simp] lemma tail_nil : tail (@nil α) = nil := rfl

lemma ext_head_tail {s₁ s₂ : seq α} (h₁ : s₁.head = s₂.head) (h₂ : s₁.tail = s₂.tail) : s₁ = s₂ :=
ext $ nat.and_forall_succ.1 ⟨h₁, ext_iff.1 h₂⟩

lemma cons_injective2 : function.injective2 (cons : α → seq α → seq α) :=
λ x y s t h, ⟨by rw [← option.some_inj, ← head_cons, h, head_cons],
  by rw [← tail_cons x s, h, tail_cons]⟩

lemma cons_left_injective (s : seq α) : function.injective (λ x, cons x s) :=
cons_injective2.left _

lemma cons_right_injective (x : α) : function.injective (cons x) :=
cons_injective2.right _

/-- A sequence has terminated at position `n` if the value at position `n` equals `none`. -/
def terminated_at (s : seq α) (n : ℕ) : Prop := s.nth n = none

lemma terminated_at.eq {s : seq α} {n : ℕ} (h : terminated_at s n) : s.nth n = none := h

/-- It is decidable whether a sequence terminates at a given position. -/
instance terminated_at_decidable (s : seq α) (n : ℕ) : decidable (s.terminated_at n) :=
option.decidable_eq_none

lemma terminated_at_nil (n : ℕ) : (@nil α).terminated_at n := refl none

@[simp] lemma terminated_at_cons_succ {s : seq α} {a n} :
  terminated_at (cons a s) (n + 1) ↔ terminated_at s n :=
iff.rfl

lemma terminated_at.cons {s : seq α} {n} (h : terminated_at s n) (a) :
  terminated_at (cons a s) (n + 1) :=
h

lemma terminated_at.tail {s : seq α} : ∀ {n}, terminated_at s n → terminated_at s.tail (n - 1)
| 0 h := s.2 h
| (n + 1) h := h

@[simp] lemma terminated_at_tail {s : seq α} {n} :
  terminated_at (tail s) n ↔ terminated_at s (n + 1) :=
iff.rfl

alias terminated_at_tail ↔ terminated_at.of_tail _

theorem le_stable (s : seq α) {m n} (h : m ≤ n) : s.nth m = none → s.nth n = none :=
nat.le_induction id (λ k hmk hk hm, s.2 (hk hm)) n h

/-- If a sequence terminated at position `n`, it also terminated at `m ≥ n `. -/
lemma terminated_at.mono {s : seq α} {m n : ℕ} : m ≤ n → s.terminated_at m →
  s.terminated_at n :=
s.le_stable

@[simp] lemma head_eq_none {s : seq α} : s.head = none ↔ s = nil :=
⟨λ h, ext $ λ n, s.le_stable (zero_le _) h, λ h, h.symm ▸ rfl⟩

lemma head_eq_some {s : seq α} {a} : s.head = some a ↔ s = cons a s.tail :=
⟨λ h, ext_head_tail h (tail_cons _ _).symm, λ h, h.symm ▸ rfl⟩

/-- A sequence terminates if there is some position `n` at which it has terminated. -/
def terminates (s : seq α) : Prop := ∃ (n : ℕ), s.terminated_at n

lemma terminated_at.terminates {s : seq α} {n} (h : terminated_at s n) : terminates s := ⟨n, h⟩

theorem not_terminates_iff {s : seq α} : ¬ s.terminates ↔ ∀ n, (s.nth n).is_some :=
by simp only [terminates, terminated_at, not_exists, ← ne.def, option.ne_none_iff_is_some]

@[simp] lemma terminates_nil : (@nil α).terminates := ⟨0, terminated_at_nil _⟩

lemma terminates.cons {s : seq α} (h : terminates s) (a) : terminates (cons a s) :=
let ⟨n, hn⟩ := h in ⟨_, hn.cons a⟩

@[simp] lemma terminates_tail {s : seq α} : terminates (tail s) ↔ terminates s :=
⟨λ ⟨n, hn⟩, ⟨_, hn.of_tail⟩, λ ⟨n, hn⟩, ⟨_, hn.tail⟩⟩

alias terminates_tail ↔ terminates.of_tail terminates.tail

@[simp] lemma terminates_cons {a : α} {s} : terminates (cons a s) ↔ terminates s :=
⟨λ h, tail_cons a s ▸ h.tail, λ h, h.cons a⟩

/-- Length of a finite sequence. -/
def length (s : seq α) (h : terminates s) : ℕ := nat.find h

lemma terminates.terminated_at {s : seq α} (h : terminates s) : terminated_at s (length s h) :=
nat.find_spec h

lemma length_le {s : seq α} (h : terminates s) {n} : length s h ≤ n ↔ s.terminated_at n :=
⟨λ hn, h.terminated_at.mono hn, nat.find_min' h⟩

lemma terminated_at.length_le {s : seq α} {n} (h : terminated_at s n) :
  length s h.terminates ≤ n :=
(length_le _).2 h

@[simp] lemma length_nil : length (@nil α) terminates_nil = 0 :=
(nat.find_eq_zero _).2 (terminated_at_nil _)

@[simp] lemma length_cons {s : seq α} (h : terminates s) (a : α) :
  length (cons a s) (h.cons _) = length s h + 1 :=
begin
  refine eq_of_forall_ge_iff (nat.and_forall_succ.1 ⟨_, λ n, _⟩),
  { simp only [length_le, terminated_at, nth_zero, head_cons, (nat.succ_pos _).not_le] },
  { simp only [nat.succ_le_succ_iff, length_le, terminated_at_cons_succ] }
end

instance : has_mem α (seq α) := ⟨λ a s, some a ∈ s.1⟩

theorem mem_def {a : α} {s : seq α} : a ∈ s ↔ some a ∈ s.1 := iff.rfl

/--
If `s.nth n = some aₙ` for some value `aₙ`, then there is also some value `aₘ` such
that `s.nth = some aₘ` for `m ≤ n`.
-/
lemma ge_stable (s : seq α) {aₙ : α} {n m : ℕ} (m_le_n : m ≤ n)
  (s_nth_eq_some : s.nth n = some aₙ) :
  ∃ (aₘ : α), s.nth m = some aₘ :=
have s.nth n ≠ none, from s_nth_eq_some.symm ▸ option.some_ne_none _,
have s.nth m ≠ none, from mt (s.le_stable m_le_n) this,
option.ne_none_iff_exists'.mp this

@[simp] theorem not_mem_nil (a : α) : a ∉ @nil α := λ ⟨n, h⟩, option.some_ne_none a h

end seq

namespace seq1

instance : has_coe_t (seq1 α) (seq α) := ⟨λ s, seq.cons s.1 s.2⟩

@[simp] lemma head_coe (s : seq1 α) : (s : seq α).head = some s.head := rfl
@[simp] lemma tail_coe (s : seq1 α) : (s : seq α).tail = s.tail := seq.tail_cons _ _
@[simp] lemma coe_mk (a : α) (s : seq α) : (mk a s : seq α) = s.cons a := rfl

@[simp] lemma mk_head_tail (s : seq1 α) : mk s.1 s.2 = s := by { cases s, refl }

end seq1

namespace seq

theorem mem_cons (a : α) (s : seq α) : a ∈ cons a s := stream.mem_cons _ _

theorem mem_cons_of_mem (y : α) {a : α} {s : seq α} (h : a ∈ s) : a ∈ cons y s :=
stream.mem_cons_of_mem (some y) h

@[simp] theorem mem_cons_iff {a b : α} {s : seq α} : a ∈ cons b s ↔ a = b ∨ a ∈ s :=
stream.mem_cons_iff.trans $ option.some_inj.or iff.rfl

/-- Destructor for a sequence, resulting in either `none` (for `nil`) or
  `some (a, s)` (for `cons a s`). -/
@[simps symm_apply] def destruct : seq α ≃ option (seq1 α) :=
{ to_fun := λ s, s.head.map $ λ a', ⟨a', s.tail⟩,
  inv_fun := λ o, o.elim nil coe,
  left_inv := λ s,
    begin
      cases h : head s,
      { simpa only [h] using (head_eq_none.1 h).symm },
      { simpa only [h] using (head_eq_some.1 h).symm }
    end,
  right_inv := λ o, by cases o; simp }

@[simp] theorem destruct_eq_none {s : seq α} : destruct s = none ↔ s = nil :=
destruct.eq_symm_apply.symm

@[simp] theorem destruct_eq_some {s : seq α} {s'} : destruct s = some s' ↔ s = s' :=
destruct.eq_symm_apply.symm

theorem destruct_eq_some' {s : seq α} {a s'} : destruct s = some ⟨a, s'⟩ ↔ s = cons a s' :=
destruct.eq_symm_apply.symm

@[simp] theorem destruct_nil : destruct (nil : seq α) = none := rfl

@[simp] theorem destruct_cons (a : α) (s) : destruct (cons a s) = some ⟨a, s⟩ :=
destruct_eq_some.2 rfl

@[simp] theorem _root_.seq1.destruct_coe (s : seq1 α) : destruct ↑s = some s :=
destruct_eq_some.2 rfl

/-- Recursion principle for sequences, compare with `list.rec_on`. -/
@[elab_as_eliminator] def cases_nil_cons {C : seq α → Sort v} (s : seq α)
  (h1 : C nil) (h2 : ∀ x s, C (cons x s)) : C s :=
(equiv.Pi_congr_left' C destruct).symm (λ o, option.rec_on o h1 (λ _, h2 _ _)) s

theorem head_eq_destruct (s : seq α) : head s = seq1.head <$> destruct s :=
cases_nil_cons s rfl $ λ _ _, rfl

theorem tail_eq_destruct (s : seq α) : tail s = (destruct s).elim nil seq1.tail :=
cases_nil_cons s rfl $ λ _ _, rfl

theorem rec_on_mem {C : seq α → Prop} {a s} (ha : a ∈ s)
  (h1 : ∀ b s', (a = b ∨ C s') → C (cons b s')) : C s :=
begin
  cases ha with k hk,
  induction k with k ihk generalizing s,
  { rw [head_eq_some.1 hk.symm], exact h1 a s.tail (or.inl rfl) },
  { rcases ge_stable s (zero_le _) hk.symm with ⟨b, hb⟩,
    rw [head_eq_some.1 hb],
    exact h1 _ _ (or.inr $ @ihk s.tail hk) }
end

/-- Map a function over a sequence. -/
def map (f : α → β) (s : seq α) : seq β :=
⟨s.1.map (option.map f), by simpa only [stream.nth_map, option.map_eq_none'] using s.2⟩

theorem map_val (f : α → β) (s) : (map f s).1 = s.1.map (option.map f) := rfl
@[simp] lemma nth_map (f : α → β) (s : seq α) (n : ℕ) : (s.map f).nth n = (s.nth n).map f := rfl

@[simp] theorem map_nil (f : α → β) : map f nil = nil := rfl

@[simp] theorem map_cons (f : α → β) (a s) : map f (cons a s) = cons (f a) (map f s) :=
ext_head_tail rfl rfl

@[simp] theorem map_id (s : seq α) : map id s = s :=
ext $ λ n, by simp only [nth_map, option.map_id, id]

@[simp] theorem map_tail (f : α → β) (s) : map f (tail s) = tail (map f s) := rfl

theorem map_comp (f : α → β) (g : β → γ) (s : seq α) : map (g ∘ f) s = map g (map f s) :=
ext $ λ n, (option.map_map _ _ _).symm

theorem mem_map {f : α → β} {b : β} {s : seq α} : b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b :=
by simp only [mem_def, stream.mem_map, map_val, option.exists, option.map_none', and_false,
  false_or, option.map_some']

theorem mem_map_of_mem (f : α → β) {a : α} {s : seq α} : a ∈ s → f a ∈ map f s :=
stream.mem_map_of_mem (option.map f)

@[simp] lemma terminated_at_map {f : α → β} {s n} : (map f s).terminated_at n ↔ s.terminated_at n :=
option.map_eq_none'

lemma terminated_at.map {s n} (h : terminated_at s n) (f : α → β) : terminated_at (map f s) n :=
terminated_at_map.2 h

@[simp] lemma terminates_map {f : α → β} {s} : (map f s).terminates ↔ s.terminates :=
exists_congr $ λ n, terminated_at_map

lemma terminates.map {s} (h : terminates s) (f : α → β) : (map f s).terminates :=
terminates_map.2 h

@[simp] lemma length_map {s} {f : α → β} (h : terminates (map f s)) :
  length (map f s) h = length s (terminates_map.1 h) :=
by { simp only [length, terminated_at_map], congr }

instance : functor seq := {map := @map}

@[simp] lemma has_map_eq_map {β} (f : α → β) (s : seq α) : f <$> s = map f s := rfl

instance : is_lawful_functor seq :=
{ id_map := @map_id, comp_map := @map_comp }

/-- Corecursor for `seq α` as a coinductive type. Iterates `f` to produce new elements
  of the sequence until `none` is obtained. -/
def corec (f : β → option (α × β)) (b : β) : seq α :=
begin
  refine ⟨stream.corec (λ x, (option.bind x f).map prod.fst)
    (λ x, (option.bind x f).map prod.snd) (some b), λ n h, _⟩,
  rw [stream.corec, stream.nth_map, option.map_eq_none'] at h ⊢,
  rw [stream.nth_iterate_succ', h, option.map_none', option.bind]
end

@[simp] lemma head_corec (f : β → option (α × β)) (b : β) :
  head (corec f b) = (f b).map prod.fst :=
rfl

@[simp] theorem destruct_corec (f : β → option (α × β)) (b : β) :
  destruct (corec f b) = (f b).map (λ x, ⟨x.1, corec f x.2⟩)  :=
begin
  cases h : f b,
  { rw [option.map_none', destruct_eq_none, ← head_eq_none, head_corec, h, option.map_none'] },
  { simp_rw [option.map_some', destruct_eq_some, seq1.coe_mk, ← val_inj,
      cons_val, corec],
    rw [stream.corec_eq, option.bind, h, option.map_some', option.map_some'] }
end

theorem tail_corec (f : β → option (α × β)) (b : β) :
  tail (corec f b) = (f b).elim nil (corec f ∘ prod.snd) :=
by { rw [tail_eq_destruct, destruct_corec], cases f b; refl }

section bisim
  variable (R : seq α → seq α → Prop)

  local infix (name := R) ` ~ `:50 := R

  /-- An auxiliary definition for `seq.is_bisimulation`. -/
  def bisim_o : option (seq1 α) → option (seq1 α) → Prop
  | none          none            := true
  | (some ⟨a, s⟩) (some ⟨a', s'⟩) := a = a' ∧ R s s'
  | _             _               := false
  attribute [simp] bisim_o

  def is_bisimulation := ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → bisim_o R (destruct s₁) (destruct s₂)

  /-- If two streams are bisimilar, then they are equal. -/
  theorem eq_of_bisim (bisim : is_bisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂ :=
  begin
    apply val_injective,
    refine stream.eq_of_bisim (λ x y, ∃ s s' : seq α, s.1 = x ∧ s'.1 = y ∧ R s s') _
      ⟨s₁, s₂, rfl, rfl, r⟩,
    clear r s₁ s₂,
    rintros _ _ ⟨s, s', rfl, rfl, r⟩,
    suffices : head s = head s' ∧ R (tail s) (tail s'),
      from this.imp_right (λ r, ⟨tail s, tail s', rfl, rfl, r⟩),
    induction s using seq.cases_nil_cons; induction s' using seq.cases_nil_cons,
    exacts [⟨rfl, r⟩, (bisim r).elim, (bisim r).elim, by simpa using bisim r]
  end

end bisim

theorem coinduction {s₁ s₂ : seq α} (hh : head s₁ = head s₂)
  (ht : ∀ (β : Type u) (f : seq α → β), f s₁ = f s₂ → f (tail s₁) = f (tail s₂)) : s₁ = s₂ :=
val_injective (stream.coinduction hh (λ β fr, ht β (λ s, fr s.1)))

theorem coinduction2 (s) (f g : seq α → seq β)
  (H : ∀ s, bisim_o (λ s1 s2, ∃ s, s1 = f s ∧ s2 = g s) (destruct (f s)) (destruct (g s))) :
  f s = g s :=
begin
  refine eq_of_bisim (λ s1 s2, ∃ s, s1 = f s ∧ s2 = g s) _ ⟨s, rfl, rfl⟩,
  intros s1 s2 h, rcases h with ⟨s, h1, h2⟩,
  rw [h1, h2], apply H
end

/-- Embed a list as a sequence. -/
instance coe_list : has_coe (list α) (seq α) :=
⟨λ l, ⟨⟨list.nth l⟩, λ n h, begin
  rw list.nth_eq_none_iff at h ⊢,
  exact h.trans (nat.le_succ n)
end⟩⟩

@[simp] theorem of_list_nil : ↑([] : list α) = (nil : seq α) := rfl
@[simp] theorem nth_of_list (l : list α) (n : ℕ) : (l : seq α).nth n = l.nth n := rfl

@[simp] theorem of_list_cons (a : α) (l : list α) : ↑(a :: l) = cons a l :=
by ext1 (_|n); refl

/-- Embed an infinite stream as a sequence -/
instance coe_stream : has_coe (stream α) (seq α) :=
⟨λ s, ⟨s.map some, λ n h, by contradiction⟩⟩

/-- Embed a `lazy_list α` as a sequence. Note that even though this
  is non-meta, it will produce infinite sequences if used with
  cyclic `lazy_list`s created by meta constructions. -/
def of_lazy_list : lazy_list α → seq α :=
corec (λ l, match l with
  | lazy_list.nil := none
  | lazy_list.cons a l' := some (a, l' ())
  end)

instance coe_lazy_list : has_coe (lazy_list α) (seq α) := ⟨of_lazy_list⟩

/-- Translate a sequence into a `lazy_list`. Since `lazy_list` and `list`
  are isomorphic as non-meta types, this function is necessarily meta. -/
meta def to_lazy_list : seq α → lazy_list α | s :=
match destruct s with
| none := lazy_list.nil
| some ⟨a, s'⟩ := lazy_list.cons a (to_lazy_list s')
end

/-- Translate a sequence to a list. This function will run forever if
  run on an infinite sequence. -/
meta def force_to_list (s : seq α) : list α := (to_lazy_list s).to_list

/-- The sequence of natural numbers some 0, some 1, ... -/
def nats : seq ℕ := stream.nats

@[simp] lemma nats_nth (n : ℕ) : nats.nth n = some n := rfl

/-- Append two sequences. If `s₁` is infinite, then `s₁ ++ s₂ = s₁`,
  otherwise it puts `s₂` at the location of the `nil` in `s₁`. -/
@[simps val_nth { attrs := [] }]
def append (s₁ s₂ : seq α) : seq α :=
begin
  refine ⟨⟨λ n, if h : s₁.terminated_at n then s₂.nth (n - length s₁ h.terminates) else s₁.nth n⟩,
    λ n hn, _⟩,
  dsimp only at hn ⊢,
  by_cases h : s₁.terminated_at n,
  { simp only [dif_pos h, dif_pos (h.mono n.le_succ)] at hn ⊢,
    exact le_stable _ (tsub_le_tsub_right n.le_succ _) hn },
  { rw [dif_neg h] at hn,
    exact absurd hn h }
end

lemma head_append (s₁ s₂ : seq α) : (append s₁ s₂).head = s₁.head.orelse s₂.head :=
begin
  cases h : s₁.head,
  { refine (dif_pos h).trans _,
    rw [nat.zero_sub, nth_zero, option.none_orelse'] },
  { exact (dif_neg $ ne_of_eq_of_ne h (option.some_ne_none _)).trans h }
end

/-- Flatten a sequence of sequences. (It is required that the
  sequences be nonempty to ensure productivity; in the case
  of an infinite sequence of `nil`, the first element is never
  generated.) -/
def join : seq (seq1 α) → seq α :=
corec $ λ S, (destruct S).map $ λ S', (S'.1.1, (destruct S'.1.2).elim S'.2 $ λ s', cons s' S'.2)

/-- Take the first `n` elements of the sequence (producing a list) -/
def take : ℕ → seq α → list α
| 0     s := []
| (n+1) s := (destruct s).elim [] (λ s, s.1 :: take n s.2)

@[simp] lemma take_nil : ∀ n, take n (@nil α) = []
| 0       := rfl
| (n + 1) := by rw [take, destruct_nil, option.elim]

@[simp] lemma take_succ_cons (s : seq α) (a) (n : ℕ) : take (n + 1) (cons a s) = a :: take n s :=
by rw [take, destruct_cons, option.elim]

@[simp] lemma nth_take (s : seq α) (n k : ℕ) :
  (s.take n).nth k = if k < n then s.nth k else none :=
begin
  induction n with n ihn generalizing k s,
  { rw [if_neg k.not_lt_zero, take, list.nth] },
  { induction s using seq.cases_nil_cons with x s,
    { rw [take_nil, nth_nil, if_t_t, list.nth] },
    { rw [take_succ_cons],
      cases k,
      { rw [list.nth, if_pos n.succ_pos, nth_zero, head_cons] },
      { simp only [list.nth, nat.succ_lt_succ_iff, ihn, nth_cons_succ] } } }
end

/-- Split a sequence at `n`, producing a finite initial segment
  and an infinite tail. -/
def split_at : ℕ → seq α → list α × seq α
| 0     s := ([], s)
| (n+1) s := match destruct s with
  | none := ([], nil)
  | some ⟨x, s'⟩ := let (l, r) := split_at n s' in (list.cons x l, r)
  end

section zip_with

/-- Combine two sequences with a function -/
def zip_with (f : α → β → γ) (s₁ : seq α) (s₂ : seq β) : seq γ :=
⟨⟨λ n, option.map₂ f (s₁.nth n) (s₂.nth n)⟩, λ n hn,
  option.map₂_eq_none_iff.2 $ (option.map₂_eq_none_iff.1 hn).imp (λ h, s₁.2 h) (λ h, s₂.2 h)⟩

variables {s : seq α} {s' : seq β} {n : ℕ}

@[simp] lemma nth_zip_with (f : α → β → γ) (s s' n) :
  (zip_with f s s').nth n = option.map₂ f (s.nth n) (s'.nth n) :=
rfl

end zip_with

/-- Pair two sequences into a sequence of pairs -/
def zip : seq α → seq β → seq (α × β) := zip_with prod.mk

lemma nth_zip (s : seq α) (t : seq β) (n : ℕ) :
  (zip s t).nth n = option.map₂ prod.mk (s.nth n) (t.nth n) :=
nth_zip_with _ _ _ _

/-- Separate a sequence of pairs into two sequences -/
def unzip (s : seq (α × β)) : seq α × seq β := (map prod.fst s, map prod.snd s)

/-- Enumerate a sequence by tagging each element with its index. -/
def enum (s : seq α) : seq (ℕ × α) := seq.zip nats s

@[simp] lemma nth_enum (s : seq α) (n : ℕ) : (enum s).nth n = (s.nth n).map (prod.mk n) := rfl

@[simp] lemma enum_nil : enum (nil : seq α) = nil := rfl

/-- Convert a sequence which is known to terminate into a list -/
def to_list (s : seq α) (h : s.terminates) : list α :=
take (length s h) s

@[simp] lemma nth_to_list {s : seq α} (h : s.terminates) (k : ℕ) : (s.to_list h).nth k = s.nth k :=
by { rw [to_list, nth_take, ite_eq_left_iff, not_lt, length_le], exact eq.symm }

@[simp] lemma of_list_to_list {s : seq α} (h : s.terminates) : ↑(to_list s h) = s :=
ext $ nth_to_list h

/-- Convert a sequence which is known not to terminate into a stream -/
def to_stream (s : seq α) (h : ¬ s.terminates) : stream α :=
⟨λ n, option.get $ not_terminates_iff.1 h n⟩

/-- Convert a sequence into either a list or a stream depending on whether
  it is finite or infinite. (Without decidability of the infiniteness predicate,
  this is not constructively possible.) -/
def to_list_or_stream (s : seq α) [decidable s.terminates] : list α ⊕ stream α :=
if h : s.terminates
then sum.inl (to_list s h)
else sum.inr (to_stream s h)

@[simp] theorem nil_append (s : seq α) : append nil s = s :=
begin
  ext1 n,
  rw [nth_append_val, dif_pos (terminated_at_nil _), length_nil, nat.sub_zero]
end

theorem append_of_not_terminates (s t : seq α) (h : ¬terminates s) : append s t = s :=
ext $ λ n, dif_neg $ mt terminated_at.terminates h

theorem terminated_at.append {s t : seq α} {m n} (hs : s.terminated_at m)
  (ht : t.terminated_at n) : (append s t).terminated_at (m + n) :=
begin
  rw [terminated_at, nth_append_val, dif_pos (hs.mono $ nat.le_add_right _ _)],
  refine ht.mono _, generalize_proofs,
  rw [add_comm, nat.add_sub_assoc hs.length_le],
  exact nat.le_add_right _ _
end

theorem terminates.append {s t : seq α} :
  s.terminates → t.terminates → (append s t).terminates
| ⟨m, hm⟩ ⟨n, hn⟩ := ⟨_, hm.append hn⟩

theorem terminated_at.left_of_append {s t : seq α} {m} (hs : terminated_at (append s t) m) :
  terminated_at s m :=
begin
  rw [terminated_at, nth_append_val] at hs,
  split_ifs at hs; assumption
end

theorem terminated_at.right_of_append' {s t : seq α} {m} (hs : terminated_at (append s t) m) :
  terminated_at t (m - s.length hs.left_of_append.terminates) :=
begin
  have := hs,
  rwa [terminated_at, nth_append_val, dif_pos hs.left_of_append] at this
end

theorem terminated_at.right_of_append {s t : seq α} {m} (hs : terminated_at (append s t) m) :
  terminated_at t m :=
hs.right_of_append'.mono $ nat.sub_le _ _

lemma terminates.left_of_append {s t : seq α} : terminates (append s t) → terminates s
| ⟨m, hm⟩ := ⟨m, hm.left_of_append⟩

lemma terminates.right_of_append {s t : seq α} : terminates (append s t) → terminates t
| ⟨m, hm⟩ := ⟨m, hm.right_of_append⟩

@[simp] lemma terminates_append {s t : seq α} :
  terminates (append s t) ↔ terminates s ∧ terminates t :=
⟨λ h, ⟨h.left_of_append, h.right_of_append⟩, λ h, h.1.append h.2⟩

@[simp] theorem cons_append (a : α) (s t) : append (cons a s) t = cons a (append s t) :=
begin
  refine ext_head_tail (head_append _ _) (ext $ λ n, _),
  simp only [nth_tail, nth_append_val, nth_cons_succ],
  dsimp only [terminated_at, nth_cons_succ],
  split_ifs; [refine congr_arg _ _, refl],
  rw [length_cons, nat.succ_sub_succ]
end

@[simp] theorem append_nil (s : seq α) : append s nil = s :=
begin
  ext1 n,
  rw [nth_append_val, dite_eq_right_iff],
  exact λ h, h.symm
end

@[simp] theorem append_assoc (s t u : seq α) :
  append (append s t) u = append s (append t u) :=
begin
  set r := λ s₁ s₂ : seq α, ∃ s t u, s₁ = append (append s t) u ∧ s₂ = append s (append t u),
  have hr : ∀ o, bisim_o r o o,
  { rintro (_|⟨_, s⟩), exacts [trivial, ⟨rfl, nil, nil, s, by simp⟩] },
  refine eq_of_bisim r _ ⟨s, t, u, rfl, rfl⟩,
  rintros _ _ ⟨s, t, u, rfl, rfl⟩,
  induction s using seq.cases_nil_cons with x s,
  { simp [hr] },
  { simp only [bisim_o, cons_append, destruct_cons],
    exact ⟨rfl, s, t, u, rfl, rfl⟩ },
end

@[simp] theorem map_append (f : α → β) (s t) : map f (append s t) = append (map f s) (map f t) :=
begin
  ext1 n,
  simp only [nth_map, nth_append_val, terminated_at_map, length_map],
  split_ifs; refl
end

@[simp] theorem join_nil : join nil = (nil : seq α) := destruct_eq_none.1 rfl

@[simp] theorem join_cons_nil (a : α) (S) :
  join (cons ⟨a, nil⟩ S) = cons a (join S) :=
destruct_eq_some'.1 $ by simp [join]

@[simp] theorem join_cons_cons (a b : α) (s S) :
  join (cons ⟨a, cons b s⟩ S) = cons a (join (cons ⟨b, s⟩ S)) :=
destruct_eq_some'.1 $ by simp [join]

@[simp, priority 990] theorem join_cons (a : α) (s S) :
  join (cons ⟨a, s⟩ S) = cons a (append s (join S)) :=
begin
  refine eq_of_bisim (λ s1 s2, s1 = s2 ∨
    ∃ a s S, s1 = join (cons ⟨a, s⟩ S) ∧ s2 = cons a (append s (join S))) _
    (or.inr ⟨a, s, S, rfl, rfl⟩),
  rintro s₁ s₂ (rfl | ⟨a, s, S, rfl, rfl⟩),
  { induction s₁ using seq.cases_nil_cons with x s,
    exacts [trivial, ⟨rfl, or.inl rfl⟩] },
  { induction s using seq.cases_nil_cons with x s,
    { simp },
    { simp only [bisim_o, join_cons_cons, destruct_cons, cons_append],
      exact ⟨rfl, or.inr ⟨x, s, S, rfl, rfl⟩⟩ } }
end

@[simp] theorem join_append (S T : seq (seq1 α)) :
  join (append S T) = append (join S) (join T) :=
begin
  refine eq_of_bisim (λ s1 s2, ∃ s S T,
    s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T))) _
    ⟨nil, S, T, (nil_append _).symm, (nil_append _).symm⟩, clear S T,
  rintros _ _ ⟨s, S, T, rfl, rfl⟩,
  induction s using seq.cases_nil_cons with x s,
  { induction S using seq.cases_nil_cons with s S,
    { induction T using seq.cases_nil_cons with s T,
      { simp },
      { cases s with a s,
        simp only [bisim_o, nil_append, join_cons, destruct_cons, join_nil],
        refine ⟨rfl, s, nil, T, _, _⟩; simp only [nil_append, join_nil] } },
    { cases s with a s,
      simp only [bisim_o, cons_append, join_cons, nil_append, destruct_cons, append_assoc],
      exact ⟨rfl, s, S, T, rfl, rfl⟩ } },
  { simp only [bisim_o, cons_append, destruct_cons],
    exact ⟨rfl, s, S, T, rfl, rfl⟩ }
end

@[simp] theorem of_stream_cons (a : α) (s) :
  ↑(a :: s : stream α) = cons a s :=
val_injective $ stream.map_cons _ _ _

@[simp] theorem of_list_append (l l' : list α) : (↑(l ++ l') : seq α) = append l l' :=
by induction l; simp [*]

@[simp] theorem of_stream_append (l : list α) (s : stream α) :
  (↑(l ++ₛ s) : seq α) = append l s :=
by induction l; simp [*, list.cons_append_stream]

/-- Convert a sequence into a list, embedded in a computation to allow for
  the possibility of infinite sequences (in which case the computation
  never returns anything). -/
def to_list' {α} (s : seq α) : computation (list α) :=
computation.corec (λ L : list α × seq α,
  (destruct L.2).elim (sum.inl L.1.reverse) (λ s', sum.inr (s'.1::L.1, s'.2))) ([], s)

theorem drop_add (s : seq α) (m n) : drop s (m + n) = drop (drop s m) n :=
val_injective $ add_comm n m ▸ (stream.drop_drop _ _ _).symm

theorem drop_tail (s : seq α) (n) : drop (tail s) n = drop s (n + 1) := rfl

theorem tail_drop (s : seq α) (n) : tail (drop s n) = drop s (n + 1) :=
(drop_add _ _ _).symm

@[simp] lemma mem_append {s t : seq α} {a : α} :
  a ∈ append s t ↔ a ∈ s ∨ s.terminates ∧ a ∈ t :=
begin
  split,
  { rintro ⟨n, hn⟩,
    rw [nth_append_val, eq_comm, dite_eq_iff] at hn,
    exact hn.symm.imp (λ h, ⟨_, h.snd.symm⟩) (λ h, ⟨⟨_, h.fst⟩, _, h.snd.symm⟩) },
  { rintro (⟨n, hn⟩ | ⟨hs, n, hn⟩),
    { use n,
      rw [hn, nth_append_val, dif_neg],
      exact ne_of_eq_of_ne hn.symm (option.some_ne_none _) },
    { refine ⟨s.length hs + n, hn.trans _⟩,
      rw [nth_append_val, dif_pos (hs.terminated_at.mono $ nat.le_add_right _ _),
        nat.add_sub_cancel_left] } }
end

theorem mem_append_left {s₁ s₂ : seq α} {a : α} (h : a ∈ s₁) : a ∈ append s₁ s₂ :=
mem_append.2 $ or.inl h

@[simp] lemma enum_cons (s : seq α) (x : α) :
  enum (cons x s) = cons (0, x) (map (prod.map nat.succ id) (enum s)) :=
begin
  ext ⟨n⟩ : 1,
  { refl },
  { simp only [nth_enum, nth_cons_succ, nth_map, option.map_map], refl }
end

end seq

namespace seq1

/-- Map a function on a `seq1` -/
@[simps] def map (f : α → β) (s : seq1 α) : seq1 β := ⟨f s.1, seq.map f s.2⟩

@[simp] lemma map_mk (f : α → β) (a s) : map f ⟨a, s⟩ = ⟨f a, seq.map f s⟩ := rfl
@[simp] theorem map_id : ∀ (s : seq1 α), map id s = s | ⟨a, s⟩ := by simp [map]

@[simp] lemma coe_map (f : α → β) (s : seq1 α) : ↑(map f s) = (seq.map f s : seq β) :=
seq.ext_head_tail rfl rfl

/-- Flatten a nonempty sequence of nonempty sequences -/
def join (s : seq1 (seq1 α)) : seq1 α :=
⟨s.1.1, seq.join $ (seq.destruct s.1.2).elim s.2 (λ s', seq.cons s' s.2)⟩

@[simp] theorem join_nil (a : α) (S) : join ⟨⟨a, seq.nil⟩, S⟩ = ⟨a, seq.join S⟩ := rfl

@[simp] theorem join_cons (a b : α) (s S) :
  join ⟨⟨a, seq.cons b s⟩, S⟩ = ⟨a, seq.join (seq.cons ⟨b, s⟩ S)⟩ :=
by { dsimp [join], rw [seq.destruct_cons], refl }

/-- The `return` operator for the `seq1` monad,
  which produces a singleton sequence. -/
def return (a : α) : seq1 α := ⟨a, seq.nil⟩

@[simp] lemma map_return (f : α → β) (a : α) : map f (return a) = return (f a) := rfl

@[simp] theorem join_return (s : seq1 α) : join (return s) = s :=
begin
  cases s with x s,
  induction s using seq.cases_nil_cons; simp [return, join]
end

instance [inhabited α] : inhabited (seq1 α) := ⟨return default⟩

/-- The `bind` operator for the `seq1` monad,
  which maps `f` on each element of `s` and appends the results together.
  (Not all of `s` may be evaluated, because the first few elements of `s`
  may already produce an infinite result.) -/
def bind (s : seq1 α) (f : α → seq1 β) : seq1 β :=
join (map f s)

@[simp] theorem join_map_return (s : seq α) : seq.join (seq.map return s) = s :=
by apply seq.coinduction2 s; intro s; apply seq.cases_nil_cons s; simp [return]

@[simp] theorem bind_return (f : α → β) : ∀ s, bind s (return ∘ f) = map f s
| ⟨a, s⟩ := begin
  dsimp [bind, map], change (λ x, return (f x)) with (return ∘ f),
  rw [seq.map_comp], simp [function.comp, return]
end

@[simp] theorem return_bind (a : α) (f : α → seq1 β) : bind (return a) f = f a :=
begin
  rw [bind, map_return],
  cases f a with a s,
  induction s using seq.cases_nil_cons; simp
end

@[simp] theorem map_join' (f : α → β) (S) :
  seq.map f (seq.join S) = seq.join (seq.map (map f) S) :=
begin
  refine seq.eq_of_bisim (λ s1 s2,
    ∃ s S, s1 = seq.append s (seq.map f (seq.join S)) ∧
      s2 = seq.append s (seq.join (seq.map (map f) S))) _ ⟨seq.nil, S, by simp⟩,
  rintros _ _ ⟨s, S, rfl, rfl⟩,
  induction s using seq.cases_nil_cons with x s,
  { induction S using seq.cases_nil_cons with x S,
    { simp },
    { cases x,
      simp only [map, seq.bisim_o, seq.join_cons, seq.map_cons, seq.map_append, seq.nil_append,
        seq.destruct_cons],
      exact ⟨rfl, _, _, rfl, rfl⟩ } },
  { simp only [seq.bisim_o, seq.cons_append, seq.destruct_cons],
    exact ⟨rfl, s, S, rfl, rfl⟩ }
end

@[simp] theorem map_join (f : α → β) : ∀ S, map f (join S) = join (map (map f) S)
| ⟨⟨a, s⟩, S⟩ := by induction s using seq.cases_nil_cons; simp [map]

@[simp] theorem join_join (SS : seq (seq1 (seq1 α))) :
  seq.join (seq.join SS) = seq.join (seq.map join SS) :=
begin
  refine seq.eq_of_bisim
    (λ s1 s2, ∃ s SS, s1 = seq.append s (seq.join (seq.join SS)) ∧
      s2 = seq.append s (seq.join (seq.map join SS)))
    _ ⟨seq.nil, SS, by simp⟩,
  rintros _ _ ⟨s, SS, rfl, rfl⟩,
  induction s using seq.cases_nil_cons with x s,
  { induction SS using seq.cases_nil_cons with S SS,
    { simp },
    { rcases S with ⟨⟨x, s⟩, S⟩,
      induction s using seq.cases_nil_cons with x s,
       { simp only [seq.bisim_o, seq.join_cons, seq.join_append, seq.nil_append, seq.destruct_cons,
           seq.map_cons, join_nil],
         exact ⟨rfl, _, _, rfl, rfl⟩ },
        { simp only [seq.bisim_o, seq.join_cons, seq.join_cons_cons, seq.join_append,
            seq.nil_append, seq.destruct_cons, seq.map_cons, join_cons, seq.append_assoc],
          refine ⟨rfl, seq.cons x (seq.append s (seq.join S)), SS, _, _⟩; simp } } },
  { simp only [seq.bisim_o, seq.cons_append, seq.destruct_cons],
    exact ⟨rfl, s, SS, rfl, rfl⟩ }
end

@[simp] theorem bind_assoc (s : seq1 α) (f : α → seq1 β) (g : β → seq1 γ) :
  bind (bind s f) g = bind s (λ (x : α), bind (f x) g) :=
begin
  cases s with a s,
  simp [bind, map_mk],
  rw [← seq.map_comp f, seq.map_comp _ join, (∘)],
  generalize : seq.map (λ x, map g (f x)) s = SS,
  rcases map g (f a) with ⟨⟨a, s⟩, S⟩,
  apply seq.cases_nil_cons s; intros; apply seq.cases_nil_cons S; intros; simp,
  { cases x with x t, apply seq.cases_nil_cons t; intros; simp },
  { cases x_1 with y t; simp }
end

instance : monad seq1 :=
{ map  := @map,
  pure := @return,
  bind := @bind }

instance : is_lawful_monad seq1 :=
{ id_map := @map_id,
  bind_pure_comp_eq_map := @bind_return,
  pure_bind := @return_bind,
  bind_assoc := @bind_assoc }

end seq1
