/-
Copyright (c) 2020 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import data.string.basic

/-!
# Parsers

`parser α` is the type that describes a computation that can ingest a `char_buffer`
and output, if successful, a term of type `α`.
This file expands on the definitions in the core library, proving that all the core library
parsers are `valid`. There are also lemmas on the composability of parsers.

## Main definitions

* 'parse_result.pos` : The position of a `char_buffer` at which a `parser α` has finished.
* `parser.valid` : The property that a parser only moves forward within a buffer,
  in both cases of success or failure.

## Implementation details

Lemmas about how parsers are valid are in the `valid` namespace. That allows using projection
notation for shorter term proofs that are parallel to the definitions of the parsers in structure.

-/

open parser parse_result

/--
For some `parse_result α`, give the position at which the result was provided, in either the
`done` or the `fail` case.
-/
@[simp] def parse_result.pos {α} : parse_result α → ℕ
| (done n _) := n
| (fail n _) := n

namespace parser

section defn_lemmas

variables {α β : Type} (msgs : thunk (list string)) (msg : thunk string)
variables (p q : parser α) (cb : char_buffer) (n n' : ℕ) {err : dlist string}
variables {a : α} {b : β}

/--
A `parser α` is defined to be `valid` if the result `p cb n` it gives,
for some `cb : char_buffer` and `n : ℕ`, (whether `done` or `fail`),
is always at a `parse_result.pos` that is at least `n`. Additionally, if the position of the result
of the parser was within the size of the `cb`, then the input to the parser must have been within
`cb.size` too.
-/
def valid : Prop :=
∀ (cb : char_buffer) (n : ℕ), n ≤ (p cb n).pos ∧ ((p cb n).pos ≤ cb.size → n ≤ cb.size)

lemma fail_iff :
  (∀ pos' result, p cb n ≠ done pos' result) ↔
    ∃ (pos' : ℕ) (err : dlist string), p cb n = fail pos' err :=
by cases p cb n; simp

lemma success_iff :
  (∀ pos' err, p cb n ≠ fail pos' err) ↔ ∃ (pos' : ℕ) (result : α), p cb n = done pos' result :=
by cases p cb n; simp

variables {p q cb n n' msgs msg}

lemma decorate_errors_fail (h : p cb n = fail n' err) :
  @decorate_errors α msgs p cb n = fail n ((dlist.lazy_of_list (msgs ()))) :=
by simp [decorate_errors, h]

lemma decorate_errors_success (h : p cb n = done n' a) :
  @decorate_errors α msgs p cb n = done n' a :=
by simp [decorate_errors, h]

lemma decorate_error_fail (h : p cb n = fail n' err) :
  @decorate_error α msg p cb n = fail n ((dlist.lazy_of_list ([msg ()]))) :=
decorate_errors_fail h

lemma decorate_error_success (h : p cb n = done n' a) :
  @decorate_error α msg p cb n = done n' a :=
decorate_errors_success h

@[simp] lemma decorate_errors_eq_done :
  @decorate_errors α msgs p cb n = done n' a ↔ p cb n = done n' a :=
by cases h : p cb n; simp [decorate_errors, h]

@[simp] lemma decorate_error_eq_done :
  @decorate_error α msg p cb n = done n' a ↔ p cb n = done n' a :=
decorate_errors_eq_done

@[simp] lemma decorate_errors_eq_fail :
  @decorate_errors α msgs p cb n = fail n err ↔
    err = dlist.lazy_of_list (msgs ()) ∧ ∃ np err', p cb n = fail np err' :=
by cases h : p cb n; simp [decorate_errors, h, eq_comm]

@[simp] lemma decorate_error_eq_fail :
  @decorate_error α msg p cb n = fail n err ↔
    err = dlist.lazy_of_list ([msg ()]) ∧ ∃ np err', p cb n = fail np err' :=
decorate_errors_eq_fail

@[simp] lemma return_eq_pure : (@return parser _ _ a) = pure a := rfl

lemma pure_eq_done : (@pure parser _ _ a) = λ _ n, done n a := rfl

@[simp] lemma pure_ne_fail : (pure a : parser α) cb n ≠ fail n' err := by simp [pure_eq_done]

section bind

variable (f : α → parser β)

@[simp] lemma bind_eq_bind : p.bind f = p >>= f := rfl

variable {f}

@[simp] lemma bind_eq_done :
  (p >>= f) cb n = done n' b ↔
  ∃ (np : ℕ) (a : α), p cb n = done np a ∧ f a cb np = done n' b :=
by cases hp : p cb n; simp [hp, ←bind_eq_bind, parser.bind, and_assoc]

@[simp] lemma bind_eq_fail :
  (p >>= f) cb n = fail n' err ↔
  (p cb n = fail n' err) ∨ (∃ (np : ℕ) (a : α), p cb n = done np a ∧ f a cb np = fail n' err) :=
by cases hp : p cb n; simp [hp, ←bind_eq_bind, parser.bind, and_assoc]

@[simp] lemma and_then_eq_bind {α β : Type} {m : Type → Type} [monad m] (a : m α) (b : m β) :
  a >> b = a >>= (λ _, b) := rfl

lemma and_then_fail :
  (p >> return ()) cb n = parse_result.fail n' err ↔ p cb n = fail n' err :=
by simp [pure_eq_done]

lemma and_then_success :
  (p >> return ()) cb n = parse_result.done n' () ↔ ∃ a, p cb n = done n' a:=
by simp [pure_eq_done]

end bind

section map

variable {f : α → β}

@[simp] lemma map_eq_done : (f <$> p) cb n = done n' b ↔
  ∃ (a : α), p cb n = done n' a ∧ f a = b :=
by cases hp : p cb n; simp [←is_lawful_monad.bind_pure_comp_eq_map, hp, and_assoc, pure_eq_done]

@[simp] lemma map_eq_fail : (f <$> p) cb n = fail n' err ↔ p cb n = fail n' err :=
by simp [←bind_pure_comp_eq_map, pure_eq_done]

@[simp] lemma map_const_eq_done {b'} : (b <$ p) cb n = done n' b' ↔
  ∃ (a : α), p cb n = done n' a ∧ b = b' :=
by simp [map_const_eq]

@[simp] lemma map_const_eq_fail : (b <$ p) cb n = fail n' err ↔ p cb n = fail n' err :=
by simp only [map_const_eq, map_eq_fail]

lemma map_const_rev_eq_done {b'} : (p $> b) cb n = done n' b' ↔
  ∃ (a : α), p cb n = done n' a ∧ b = b' :=
map_const_eq_done

lemma map_rev_const_eq_fail : (p $> b) cb n = fail n' err ↔ p cb n = fail n' err :=
map_const_eq_fail

end map

@[simp] lemma orelse_eq_orelse : p.orelse q = (p <|> q) := rfl

@[simp] lemma orelse_eq_done : (p <|> q) cb n = done n' a ↔
  (p cb n = done n' a ∨ (q cb n = done n' a ∧ ∃ err, p cb n = fail n err)) :=
begin
  cases hp : p cb n with np resp np errp,
  { simp [hp, ←orelse_eq_orelse, parser.orelse] },
  { by_cases hn : np = n,
    { cases hq : q cb n with nq resq nq errq,
      { simp [hp, hn, hq, ←orelse_eq_orelse, parser.orelse] },
      { rcases lt_trichotomy nq n with H|rfl|H;
        simp [hp, hn, hq, H, not_lt_of_lt H, lt_irrefl, ←orelse_eq_orelse, parser.orelse] <|>
          simp [hp, hn, hq, lt_irrefl, ←orelse_eq_orelse, parser.orelse] } },
    { simp [hp, hn, ←orelse_eq_orelse, parser.orelse] } }
end

@[simp] lemma orelse_eq_fail_eq : (p <|> q) cb n = fail n err ↔
  (p cb n = fail n err ∧ ∃ (nq errq), n < nq ∧ q cb n = fail nq errq) ∨
  (∃ (errp errq), p cb n = fail n errp ∧ q cb n = fail n errq ∧ errp ++ errq = err)
 :=
begin
  cases hp : p cb n with np resp np errp,
  { simp [hp, ←orelse_eq_orelse, parser.orelse] },
  { by_cases hn : np = n,
    { cases hq : q cb n with nq resq nq errq,
      { simp [hp, hn, hq, ←orelse_eq_orelse, parser.orelse] },
      { rcases lt_trichotomy nq n with H|rfl|H;
        simp [hp, hq, hn, ←orelse_eq_orelse, parser.orelse, H,
              ne_of_gt H, ne_of_lt H, not_lt_of_lt H] <|>
          simp [hp, hq, hn, ←orelse_eq_orelse, parser.orelse, lt_irrefl] } },
    { simp [hp, hn, ←orelse_eq_orelse, parser.orelse] } }
end

lemma orelse_eq_fail_invalid_lt (hn : n' < n) : (p <|> q) cb n = fail n' err ↔
  (p cb n = fail n' err) ∨
  (q cb n = fail n' err ∧ (∃ (errp), p cb n = fail n errp)) :=
begin
  cases hp : p cb n with np resp np errp,
  { simp [hp, ←orelse_eq_orelse, parser.orelse] },
  { by_cases h : np = n,
    { cases hq : q cb n with nq resq nq errq,
      { simp [hp, h, hn, hq, ne_of_gt hn, ←orelse_eq_orelse, parser.orelse] },
      { rcases lt_trichotomy nq n with H|H|H,
        { simp [hp, hq, h, H, ne_of_gt hn, not_lt_of_lt H, ←orelse_eq_orelse, parser.orelse] },
        { simp [hp, hq, h, H, ne_of_gt hn, lt_irrefl, ←orelse_eq_orelse, parser.orelse] },
        { simp [hp, hq, h, H, ne_of_gt (hn.trans H), ←orelse_eq_orelse, parser.orelse] } } },
    { simp [hp, h, ←orelse_eq_orelse, parser.orelse] } }
end

lemma orelse_eq_fail_of_valid_ne (hv : q.valid) (hn : n ≠ n') :
  (p <|> q) cb n = fail n' err ↔ p cb n = fail n' err :=
begin
  cases hp : p cb n with np resp np errp,
  { simp [hp, ←orelse_eq_orelse, parser.orelse] },
  { by_cases h : np = n,
    { cases hq : q cb n with nq resq nq errq,
      { simp [hp, h, hn, hq, hn, ←orelse_eq_orelse, parser.orelse] },
      { have : n ≤ nq := by { convert (hv cb n).left, simp [hq] },
        rcases eq_or_lt_of_le this with rfl|H,
        { simp [hp, hq, h, hn, lt_irrefl, ←orelse_eq_orelse, parser.orelse] },
        { simp [hp, hq, h, hn, H, ←orelse_eq_orelse, parser.orelse] } } },
    { simp [hp, h, ←orelse_eq_orelse, parser.orelse] } },
end

@[simp] lemma failure_eq_failure : @parser.failure α = failure := rfl

@[simp] lemma failure_def : (failure : parser α) cb n = fail n dlist.empty := rfl

lemma not_failure_eq_done : ¬ (failure : parser α) cb n = done n' a :=
by simp

lemma failure_eq_fail : (failure : parser α) cb n = fail n' err ↔ n = n' ∧ err = dlist.empty :=
by simp [eq_comm]

lemma seq_eq_done {f : parser (α → β)} {p : parser α} : (f <*> p) cb n = done n' b ↔
  ∃ (nf : ℕ) (f' : α → β) (a : α), f cb n = done nf f' ∧ p cb nf = done n' a ∧ f' a = b :=
by simp [seq_eq_bind_map]

lemma seq_eq_fail {f : parser (α → β)} {p : parser α} : (f <*> p) cb n = fail n' err ↔
  (f cb n = fail n' err) ∨ (∃ (nf : ℕ) (f' : α → β), f cb n = done nf f' ∧ p cb nf = fail n' err) :=
by simp [seq_eq_bind_map]

lemma seq_left_eq_done {p : parser α} {q : parser β} : (p <* q) cb n = done n' a ↔
  ∃ (np : ℕ) (b : β), p cb n = done np a ∧ q cb np = done n' b :=
begin
  have : ∀ (p q : ℕ → α → Prop),
    (∃ (np : ℕ) (x : α), p np x ∧ q np x ∧ x = a) ↔ ∃ (np : ℕ), p np a ∧ q np a :=
    λ _ _, ⟨λ ⟨np, x, hp, hq, rfl⟩, ⟨np, hp, hq⟩, λ ⟨np, hp, hq⟩, ⟨np, a, hp, hq, rfl⟩⟩,
  simp [seq_left_eq, seq_eq_done, map_eq_done, this]
end

lemma seq_left_eq_fail {p : parser α} {q : parser β} : (p <* q) cb n = fail n' err ↔
  (p cb n = fail n' err) ∨ (∃ (np : ℕ) (a : α), p cb n = done np a ∧ q cb np = fail n' err) :=
by simp [seq_left_eq, seq_eq_fail]

lemma seq_right_eq_done {p : parser α} {q : parser β} : (p *> q) cb n = done n' b ↔
  ∃ (np : ℕ) (a : α), p cb n = done np a ∧ q cb np = done n' b :=
by simp [seq_right_eq, seq_eq_done, map_eq_done, and.comm, and.assoc]

lemma seq_right_eq_fail {p : parser α} {q : parser β} : (p *> q) cb n = fail n' err ↔
  (p cb n = fail n' err) ∨ (∃ (np : ℕ) (a : α), p cb n = done np a ∧ q cb np = fail n' err) :=
by simp [seq_right_eq, seq_eq_fail]

lemma mmap_eq_done {f : α → parser β} {a : α} {l : list α} {b : β} {l' : list β} :
  (a :: l).mmap f cb n = done n' (b :: l') ↔
  ∃ (np : ℕ), f a cb n = done np b ∧ l.mmap f cb np = done n' l' :=
by simp [mmap, and.comm, and.assoc, and.left_comm, pure_eq_done]

lemma mmap'_eq_done {f : α → parser β} {a : α} {l : list α} :
  (a :: l).mmap' f cb n = done n' () ↔
  ∃ (np : ℕ) (b : β), f a cb n = done np b ∧ l.mmap' f cb np = done n' () :=
by simp [mmap']

lemma guard_eq_done {p : Prop} [decidable p] :
  @guard parser _ p _ cb n = done n' () ↔ p ∧ n = n' :=
by { by_cases hp : p; simp [guard, hp, pure_eq_done] }

lemma guard_eq_fail {p : Prop} [decidable p] :
  @guard parser _ p _ cb n = fail n' err ↔ (¬ p) ∧ n = n' ∧ err = dlist.empty :=
by { by_cases hp : p; simp [guard, hp, eq_comm, pure_eq_done] }

section valid

variables {sep : parser unit}

namespace valid

lemma mono_done (hp : p.valid) (h : p cb n = done n' a) : n ≤ n' :=
by simpa [h] using (hp cb n).left

lemma mono_fail (hp : p.valid) (h : p cb n = fail n' err) : n ≤ n' :=
by simpa [h] using (hp cb n).left

lemma pure : valid (pure a) :=
λ _ _, by simp [pure_eq_done]

@[simp] lemma bind {f : α → parser β} (hp : p.valid) (hf : ∀ a, (f a).valid) :
  (p >>= f).valid :=
begin
  intros cb n,
  cases hx : (p >>= f) cb n,
  { obtain ⟨n', a, h, h'⟩ := bind_eq_done.mp hx,
    refine ⟨le_trans (hp cb n).left (h' ▸ _), λ hn, (hp cb n).right _⟩,
    { simp [h, hf a cb n'] },
    { simp [h, (hf a cb n').right (h'.symm ▸ hn)] } },
  { obtain h | ⟨n', a, h, h'⟩ := bind_eq_fail.mp hx,
    { simpa only [h] using hp cb n },
    { refine ⟨le_trans (hp cb n).left (h' ▸ _), λ hn, (hp cb n).right _⟩,
      { simp [h, hf a cb n'] },
      { simp [h, (hf a cb n').right (h'.symm ▸ hn)] } } }
end

lemma and_then {q : parser β} (hp : p.valid) (hq : q.valid) : (p >> q).valid :=
hp.bind (λ _, hq)

@[simp] lemma map (hp : p.valid) {f : α → β} : (f <$> p).valid :=
hp.bind (λ _, pure)

@[simp] lemma seq {f : parser (α → β)} (hf : f.valid) (hp : p.valid) : (f <*> p).valid :=
hf.bind (λ _, hp.map)

@[simp] lemma mmap {l : list α} {f : α → parser β} (h : ∀ a ∈ l, (f a).valid) :
  (l.mmap f).valid :=
begin
  induction l with hd tl hl generalizing h,
  { exact pure },
  { exact bind (h _ (list.mem_cons_self _ _))
      (λ b, map (hl (λ _ ha, h _ (list.mem_cons_of_mem _ ha)))) }
end

@[simp] lemma mmap' {l : list α} {f : α → parser β} (h : ∀ a ∈ l, (f a).valid) :
  (l.mmap' f).valid :=
begin
  induction l with hd tl hl generalizing h,
  { exact pure },
  { exact and_then (h _ (list.mem_cons_self _ _)) (hl (λ _ ha, h _ (list.mem_cons_of_mem _ ha))) }
end

@[simp] lemma failure : @parser.valid α failure :=
by simp [valid, le_refl]

@[simp] lemma guard {p : Prop} [decidable p] : valid (guard p) :=
by simp only [guard, apply_ite valid, pure, failure, or_true, if_true_left_eq_or]

@[simp] lemma orelse (hp : p.valid) (hq : q.valid) : (p <|> q).valid :=
begin
  intros cb n,
  cases hx : (p <|> q) cb n with posx resx posx errx,
  { obtain h | ⟨h, -, -⟩ := orelse_eq_done.mp hx,
    { simpa [h] using hp cb n },
    { simpa [h] using hq cb n } },
  { by_cases h : n = posx,
    { simp [hx, h] },
    { simpa [(orelse_eq_fail_of_valid_ne hq h).mp hx] using hp cb n } }
end

@[simp] lemma decorate_errors (hp : p.valid) :
  (@decorate_errors α msgs p).valid :=
begin
  intros cb n,
  cases h : p cb n,
  { simpa [decorate_errors, h] using hp cb n },
  { simp [decorate_errors, h] }
end

@[simp] lemma decorate_error (hp : p.valid) : (@decorate_error α msg p).valid :=
decorate_errors hp

@[simp] lemma any_char : valid any_char :=
begin
  intros cb n,
  by_cases h : n < cb.size,
  { simpa [any_char, h] using nat.le_of_succ_le },
  { simp [any_char, h] }
end

@[simp] lemma sat {p : char → Prop} [decidable_pred p] : valid (sat p) :=
begin
  intros cb n,
  simp only [sat],
  split_ifs,
  { simpa using nat.le_of_succ_le },
  { simp },
  { simp }
end

@[simp] lemma eps : valid eps := pure

lemma ch {c : char} : valid (ch c) := decorate_error (sat.and_then eps)

lemma char_buf {s : char_buffer} : valid (char_buf s) :=
decorate_error (mmap' (λ _ _, ch))

lemma one_of {cs : list char} : (one_of cs).valid :=
decorate_errors sat

lemma one_of' {cs : list char} : (one_of' cs).valid :=
one_of.and_then eps

lemma str {s : string} : (str s).valid :=
decorate_error (mmap' (λ _ _, ch))

lemma remaining : remaining.valid :=
λ _ _, ⟨le_refl _, λ h, h⟩

lemma eof : eof.valid :=
decorate_error (remaining.bind (λ _, guard))

lemma foldr_core_zero {f : α → β → β} {b : β} : (foldr_core f p b 0).valid :=
failure

lemma foldr_core {f : α → β → β} {b : β} (hp : p.valid) :
  ∀ {reps : ℕ}, (foldr_core f p b reps).valid
| 0          := failure
| (reps + 1) := orelse (hp.bind (λ _, foldr_core.bind (λ _, pure))) pure

lemma foldr {f : α → β → β} (hp : p.valid) : valid (foldr f p b) :=
λ _ _, foldr_core hp _ _

lemma foldl_core_zero {f : β → α → β} {b : β} : (foldl_core f b p 0).valid :=
failure

lemma foldl_core {f : α → β → α} {p : parser β} (hp : p.valid) :
  ∀ {a : α} {reps : ℕ}, (foldl_core f a p reps).valid
| _ 0          := failure
| _ (reps + 1) := orelse (hp.bind (λ _, foldl_core)) pure

lemma foldl {f : α → β → α} {p : parser β} (hp : p.valid) : valid (foldl f a p) :=
λ _ _, foldl_core hp _ _

lemma many (hp : p.valid) : p.many.valid :=
hp.foldr

lemma many_char {p : parser char} (hp : p.valid) : p.many_char.valid :=
hp.many.map

lemma many' (hp : p.valid) : p.many'.valid :=
hp.many.and_then eps

lemma many1 (hp : p.valid) : p.many1.valid :=
hp.map.seq hp.many

lemma many_char1 {p : parser char} (hp : p.valid) : p.many_char1.valid :=
hp.many1.map

lemma sep_by1 {sep : parser unit} (hp : p.valid) (hs : sep.valid) : valid (sep_by1 sep p) :=
hp.map.seq (hs.and_then hp).many

lemma sep_by {sep : parser unit} (hp : p.valid) (hs : sep.valid) : valid (sep_by sep p) :=
(hp.sep_by1 hs).orelse pure

lemma fix_core {F : parser α → parser α} (hF : ∀ (p : parser α), p.valid → (F p).valid) :
  ∀ (max_depth : ℕ), valid (fix_core F max_depth)
| 0               := failure
| (max_depth + 1) := hF _ (fix_core _)

lemma digit : digit.valid :=
decorate_error (sat.bind (λ _, pure))

lemma nat : nat.valid :=
decorate_error (digit.many1.bind (λ _, pure))

lemma fix {F : parser α → parser α} (hF : ∀ (p : parser α), p.valid → (F p).valid) :
  valid (fix F) :=
λ _ _, fix_core hF _ _ _

end valid

end valid

@[simp] lemma orelse_pure_eq_fail : (p <|> pure a) cb n = fail n' err ↔
  p cb n = fail n' err ∧ n ≠ n' :=
begin
  by_cases hn : n = n',
  { simp [hn, pure_eq_done] },
  { rw [orelse_eq_fail_of_valid_ne valid.pure hn],
    simp [hn] }
end

end defn_lemmas

section done

variables {α β : Type}
  {cb : char_buffer} {n n' : ℕ} (hn : n < cb.size) {a a' : α} {b : β} {c : char}
include hn

lemma any_char_eq_done : any_char cb n = done n' c ↔ n' = n + 1 ∧ cb.read ⟨n, hn⟩ = c :=
by simp [any_char, hn, eq_comm]

lemma sat_eq_done {p : char → Prop} [decidable_pred p] : sat p cb n = done n' c ↔
  p c ∧ n' = n + 1 ∧ cb.read ⟨n, hn⟩ = c :=
begin
  by_cases hp : p (cb.read ⟨n, hn⟩),
  { simp only [sat, hp, hn, dif_pos, if_true],
    split,
    { rintro ⟨rfl, rfl⟩, simp [hp] },
    { rintro ⟨-, rfl, rfl⟩, simp } },
  { simp [sat, hp, hn, dif_pos, false_iff, not_and, if_false],
    rintro hc rfl rfl,
    exact hp hc }
end

omit hn
lemma eps_eq_done : eps cb n = done n' () ↔ n = n' := by simp [eps, pure_eq_done]

include hn

lemma ch_eq_done : ch c cb n = done n' () ↔ n' = n + 1 ∧ cb.read ⟨n, hn⟩ = c :=
by simp [ch, hn, eps_eq_done, sat_eq_done, and.comm, @eq_comm _ n']

-- TODO: add char_buf_eq_done, needs lemmas about matching buffers

lemma one_of_eq_done {cs : list char} : one_of cs cb n = done n' c ↔
  c ∈ cs ∧ n' = n + 1 ∧ cb.read ⟨n, hn⟩ = c :=
by simp [one_of, hn, sat_eq_done]

lemma one_of'_eq_done {cs : list char} : one_of' cs cb n = done n' () ↔
  cb.read ⟨n, hn⟩ ∈ cs ∧ n' = n + 1 :=
begin
  have : ∀ {x : char} {p : Prop},
    (∃ (z : char), z ∈ cs ∧ p ∧ x = z) ↔ x ∈ cs ∧ p,
    { intros x p,
      exact ⟨λ ⟨z, hz, hp, rfl⟩, ⟨hz, hp⟩, λ ⟨hx, hp⟩, ⟨x, hx, hp, rfl⟩⟩ },
  simp [one_of', hn, one_of_eq_done, sat_eq_done, eps_eq_done, this]
end

omit hn
lemma remaining_eq_done {r : ℕ} : remaining cb n = done n' r ↔ n = n' ∧ cb.size - n = r :=
by simp [remaining]

lemma eof_eq_done : eof cb n = done n' () ↔ n = n' ∧ cb.size ≤ n :=
by simp [eof, guard_eq_done, remaining_eq_done, nat.sub_eq_zero_iff_le, and_comm, and_assoc]

@[simp] lemma foldr_core_zero_eq_done {f : α → β → β} {p : parser α} {b' : β} :
  foldr_core f p b 0 cb n ≠ done n' b' :=
by simp [foldr_core]

lemma foldr_core_eq_done {f : α → β → β} {p : parser α} {reps : ℕ} {b' : β} :
  foldr_core f p b (reps + 1) cb n = done n' b' ↔
  (∃ (np : ℕ) (a : α) (xs : β), p cb n = done np a ∧ foldr_core f p b reps cb np = done n' xs
    ∧ f a xs = b') ∨
  (n = n' ∧ b = b' ∧ ∃ (err), (p cb n = fail n err) ∨
    (∃ (np : ℕ) (a : α), p cb n = done np a ∧ foldr_core f p b reps cb np = fail n err)) :=
by simp [foldr_core, and.comm, and.assoc, pure_eq_done]

@[simp] lemma foldr_core_zero_eq_fail {f : α → β → β} {p : parser α} {err : dlist string} :
  foldr_core f p b 0 cb n = fail n' err ↔ n = n' ∧ err = dlist.empty :=
by simp [foldr_core, eq_comm]

lemma foldr_core_succ_eq_fail {f : α → β → β} {p : parser α} {reps : ℕ} {err : dlist string} :
  foldr_core f p b (reps + 1) cb n = fail n' err ↔ n ≠ n' ∧
  (p cb n = fail n' err ∨
    ∃ (np : ℕ) (a : α), p cb n = done np a ∧ foldr_core f p b reps cb np = fail n' err) :=
by simp [foldr_core, and_comm]

lemma foldr_eq_done {f : α → β → β} {p : parser α} {b' : β} :
  foldr f p b cb n = done n' b' ↔
  ((∃ (np : ℕ) (a : α) (x : β), p cb n = done np a ∧
    foldr_core f p b (cb.size - n) cb np = done n' x ∧ f a x = b') ∨
  (n = n' ∧ b = b' ∧ (∃ (err), p cb n = parse_result.fail n err ∨
    ∃ (np : ℕ) (x : α), p cb n = done np x ∧ foldr_core f p b (cb.size - n) cb np = fail n err))) :=
by simp [foldr, foldr_core_eq_done]

lemma foldr_eq_fail_of_valid_at_end {f : α → β → β} {p : parser α} {err : dlist string}
  (hp : p.valid) (hc : cb.size ≤ n) : foldr f p b cb n = fail n' err ↔
    n < n' ∧ (p cb n = fail n' err ∨ ∃ (a : α), p cb n = done n' a ∧ err = dlist.empty) :=
begin
  have : cb.size - n = 0 := nat.sub_eq_zero_of_le hc,
  simp only [foldr, foldr_core_succ_eq_fail, this, and.left_comm, foldr_core_zero_eq_fail,
            ne_iff_lt_iff_le, exists_and_distrib_right, exists_eq_left, and.congr_left_iff,
            exists_and_distrib_left],
  rintro (h | ⟨⟨a, h⟩, rfl⟩),
  { exact hp.mono_fail h },
  { exact hp.mono_done h }
end

lemma foldr_eq_fail {f : α → β → β} {p : parser α} {err : dlist string} :
  foldr f p b cb n = fail n' err ↔ n ≠ n' ∧ (p cb n = fail n' err ∨
    ∃ (np : ℕ) (a : α), p cb n = done np a ∧ foldr_core f p b (cb.size - n) cb np = fail n' err) :=
by simp [foldr, foldr_core_succ_eq_fail]

@[simp] lemma foldl_core_zero_eq_done {f : β → α → β} {p : parser α} {b' : β} :
  foldl_core f b p 0 cb n = done n' b' ↔ false :=
by simp [foldl_core]

lemma foldl_core_eq_done {f : β → α → β} {p : parser α} {reps : ℕ} {b' : β} :
  foldl_core f b p (reps + 1) cb n = done n' b' ↔
  (∃ (np : ℕ) (a : α), p cb n = done np a ∧ foldl_core f (f b a) p reps cb np = done n' b') ∨
  (n = n' ∧ b = b' ∧ ∃ (err), (p cb n = fail n err) ∨
    (∃ (np : ℕ) (a : α), p cb n = done np a ∧ foldl_core f (f b a) p reps cb np = fail n err)) :=
by simp [foldl_core, and.assoc, pure_eq_done]

@[simp] lemma foldl_core_zero_eq_fail {f : β → α → β} {p : parser α} {err : dlist string} :
  foldl_core f b p 0 cb n = fail n' err ↔ n = n' ∧ err = dlist.empty :=
by simp [foldl_core, eq_comm]

lemma foldl_core_succ_eq_fail {f : β → α → β} {p : parser α} {reps : ℕ} {err : dlist string} :
  foldl_core f b p (reps + 1) cb n = fail n' err ↔ n ≠ n' ∧
  (p cb n = fail n' err ∨
    ∃ (np : ℕ) (a : α), p cb n = done np a ∧ foldl_core f (f b a) p reps cb np = fail n' err) :=
by  simp [foldl_core, and_comm]

lemma foldl_eq_done {f : β → α → β} {p : parser α} {b' : β} :
  foldl f b p cb n = done n' b' ↔
  (∃ (np : ℕ) (a : α), p cb n = done np a ∧
    foldl_core f (f b a) p (cb.size - n) cb np = done n' b') ∨
  (n = n' ∧ b = b' ∧ ∃ (err), (p cb n = fail n err) ∨
    (∃ (np : ℕ) (a : α), p cb n = done np a ∧
      foldl_core f (f b a) p (cb.size - n) cb np = fail n err)) :=
by simp [foldl, foldl_core_eq_done]

lemma foldl_eq_fail {f : β → α → β} {p : parser α} {err : dlist string} :
  foldl f b p cb n = fail n' err ↔ n ≠ n' ∧ (p cb n = fail n' err ∨
    ∃ (np : ℕ) (a : α), p cb n = done np a ∧
    foldl_core f (f b a) p (cb.size - n) cb np = fail n' err) :=
by simp [foldl, foldl_core_succ_eq_fail]

lemma many_eq_done_nil {p : parser α} : many p cb n = done n' (@list.nil α) ↔ n = n' ∧
  ∃ (err), p cb n = fail n err ∨ ∃ (np : ℕ) (a : α), p cb n = done np a ∧
    foldr_core list.cons p [] (cb.size - n) cb np = fail n err :=
by simp [many, foldr_eq_done]

lemma many_eq_done {p : parser α} {x : α} {xs : list α} :
  many p cb n = done n' (x :: xs) ↔ ∃ (np : ℕ), p cb n = done np x
    ∧ foldr_core list.cons p [] (cb.size - n) cb np = done n' xs :=
by simp [many, foldr_eq_done, and.comm, and.assoc, and.left_comm]

lemma many_eq_fail {p : parser α} {err : dlist string} :
  many p cb n = fail n' err ↔ n ≠ n' ∧ (p cb n = fail n' err ∨
    ∃ (np : ℕ) (a : α), p cb n = done np a ∧
      foldr_core list.cons p [] (cb.size - n) cb np = fail n' err) :=
by simp [many, foldr_eq_fail]

lemma many_char_eq_done_empty {p : parser char} : many_char p cb n = done n' string.empty ↔ n = n' ∧
  ∃ (err), p cb n = fail n err ∨ ∃ (np : ℕ) (c : char), p cb n = done np c ∧
    foldr_core list.cons p [] (cb.size - n) cb np = fail n err :=
by simp [many_char, many_eq_done_nil, map_eq_done, list.as_string_eq]

lemma many_char_eq_done_not_empty {p : parser char} {s : string} (h : s ≠ "") :
  many_char p cb n = done n' s ↔ ∃ (np : ℕ), p cb n = done np s.head ∧
    foldr_core list.cons p list.nil (buffer.size cb - n) cb np = done n' (s.popn 1).to_list :=
by simp [many_char, list.as_string_eq, string.to_list_nonempty h, many_eq_done]

lemma many_char_eq_many_of_to_list {p : parser char} {s : string} :
  many_char p cb n = done n' s ↔ many p cb n = done n' s.to_list :=
by simp [many_char, list.as_string_eq]

lemma many'_eq_done {p : parser α} : many' p cb n = done n' () ↔
  many p cb n = done n' [] ∨ ∃ (np : ℕ) (a : α) (l : list α), many p cb n = done n' (a :: l)
    ∧ p cb n = done np a ∧ foldr_core list.cons p [] (buffer.size cb - n) cb np = done n' l :=
begin
  simp only [many', eps_eq_done, many, foldr, and_then_eq_bind, exists_and_distrib_right,
             bind_eq_done, exists_eq_right],
  split,
  { rintro ⟨_ | ⟨hd, tl⟩, hl⟩,
    { exact or.inl hl },
    { have hl2 := hl,
      simp only [foldr_core_eq_done, or_false, exists_and_distrib_left, and_false, false_and,
                 exists_eq_right_right] at hl,
      obtain ⟨np, hp, h⟩ := hl,
      refine or.inr ⟨np, _, _, hl2, hp, h⟩ } },
  { rintro (h | ⟨np, a, l, hp, h⟩),
    { exact ⟨[], h⟩ },
    { refine ⟨a :: l, hp⟩ } }
end

@[simp] lemma many1_ne_done_nil {p : parser α} : many1 p cb n ≠ done n' [] :=
by simp [many1, seq_eq_done]

lemma many1_eq_done {p : parser α} {l : list α} : many1 p cb n = done n' (a :: l) ↔
  ∃ (np : ℕ), p cb n = done np a ∧ many p cb np = done n' l :=
by simp [many1, seq_eq_done, map_eq_done]

lemma many1_eq_fail {p : parser α} {err : dlist string} : many1 p cb n = fail n' err ↔
  p cb n = fail n' err ∨ (∃ (np : ℕ) (a : α), p cb n = done np a ∧ many p cb np = fail n' err) :=
by simp [many1, seq_eq_fail]

@[simp] lemma many_char1_ne_empty {p : parser char} : many_char1 p cb n ≠ done n' "" :=
by simp [many_char1, ←string.nil_as_string_eq_empty]

lemma many_char1_eq_done {p : parser char} {s : string} (h : s ≠ "") :
  many_char1 p cb n = done n' s ↔
  ∃ (np : ℕ), p cb n = done np s.head ∧ many_char p cb np = done n' (s.popn 1) :=
by simp [many_char1, list.as_string_eq, string.to_list_nonempty h, many1_eq_done,
         many_char_eq_many_of_to_list]

@[simp] lemma sep_by1_ne_done_nil {sep : parser unit} {p : parser α} :
  sep_by1 sep p cb n ≠ done n' [] :=
by simp [sep_by1, seq_eq_done]

lemma sep_by1_eq_done {sep : parser unit} {p : parser α} {l : list α} :
  sep_by1 sep p cb n = done n' (a :: l) ↔ ∃ (np : ℕ), p cb n = done np a ∧
    (sep >> p).many cb np  = done n' l :=
by simp [sep_by1, seq_eq_done]

lemma sep_by_eq_done_nil {sep : parser unit} {p : parser α} :
  sep_by sep p cb n = done n' [] ↔ n = n' ∧ ∃ (err), sep_by1 sep p cb n = fail n err :=
by simp [sep_by, pure_eq_done]

@[simp] lemma fix_core_ne_done_zero {F : parser α → parser α} :
  fix_core F 0 cb n ≠ done n' a :=
by simp [fix_core]

lemma fix_core_eq_done {F : parser α → parser α} {max_depth : ℕ} :
  fix_core F (max_depth + 1) cb n = done n' a ↔ F (fix_core F max_depth) cb n = done n' a :=
by simp [fix_core]

include hn

lemma digit_eq_done {k : ℕ} : digit cb n = done n' k ↔ n' = n + 1 ∧ k ≤ 9 ∧
  (cb.read ⟨n, hn⟩).to_nat - '0'.to_nat = k ∧ '0' ≤ cb.read ⟨n, hn⟩ ∧ cb.read ⟨n, hn⟩ ≤ '9' :=
begin
  have c9 : '9'.to_nat - '0'.to_nat = 9 := rfl,
  have l09 : '0'.to_nat ≤ '9'.to_nat := dec_trivial,
  have le_iff_le : ∀ {c c' : char}, c ≤ c' ↔ c.to_nat ≤ c'.to_nat := λ _ _, iff.rfl,
  simp only [digit, pure_eq_done, sat_eq_done, hn, and.left_comm, exists_eq_left, bind_eq_done,
             and.congr_right_iff, @eq_comm _ n', decorate_error_eq_done, and.comm,
             exists_and_distrib_left],
  simp only [←and.assoc, exists_eq_right', le_iff_le, and.congr_left_iff, ←c9],
  rintro hn rfl hl,
  simp [l09, nat.sub_le_sub_right_iff, hl],
end

end done

end parser
