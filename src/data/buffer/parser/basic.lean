/-
Copyright (c) 2020 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import data.list.basic

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

@[simp] lemma decorate_errors_success_iff :
  @decorate_errors α msgs p cb n = done n' a ↔ p cb n = done n' a :=
by cases h : p cb n; simp [decorate_errors, h]

@[simp] lemma decorate_error_success_iff :
  @decorate_error α msg p cb n = done n' a ↔ p cb n = done n' a :=
decorate_errors_success_iff

@[simp] lemma decorate_errors_failure_iff :
  @decorate_errors α msgs p cb n = fail n err ↔
    err = dlist.lazy_of_list (msgs ()) ∧ ∃ np err', p cb n = fail np err' :=
by cases h : p cb n; simp [decorate_errors, h, eq_comm]

@[simp] lemma decorate_error_failure_iff :
  @decorate_error α msg p cb n = fail n err ↔
    err = dlist.lazy_of_list ([msg ()]) ∧ ∃ np err', p cb n = fail np err' :=
decorate_errors_failure_iff

@[simp] lemma return_eq_pure : (@return parser _ _ a) = pure a := rfl

@[simp] lemma pure_eq_done : (@pure parser _ _ a) = λ _ n, done n a := rfl

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
by simp

lemma and_then_success :
  (p >> return ()) cb n = parse_result.done n' () ↔ ∃ a, p cb n = done n' a:=
by simp

end bind

section map

variable {f : α → β}

@[simp] lemma map_eq_done : (f <$> p) cb n = done n' b ↔
  ∃ (a : α), p cb n = done n' a ∧ f a = b :=
by cases hp : p cb n; simp [←is_lawful_monad.bind_pure_comp_eq_map, hp, and_assoc]

@[simp] lemma map_eq_fail : (f <$> p) cb n = fail n' err ↔ p cb n = fail n' err :=
by simp [←bind_pure_comp_eq_map]

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

section valid

variables {sep : parser unit}

namespace valid

lemma pure : valid (pure a) :=
by { intros cb n, simp only [pure_eq_done, parse_result.pos, imp_self, and_true] }

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

lemma foldr_core {f : α → β → β} {b : β} (hp : p.valid) :
  ∀ {reps : ℕ}, (foldr_core f p b reps).valid
| 0          := failure
| (reps + 1) := orelse (hp.bind (λ _, foldr_core.bind (λ _, pure))) pure

lemma foldr {f : α → β → β} (hp : p.valid) : valid (foldr f p b) :=
λ _ _, foldr_core hp _ _

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

end defn_lemmas

end parser
